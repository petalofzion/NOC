"""
Subject: Experimental "NOC" Environment for Atropos (Intrinsic Motivation)

This environment implements the "Naturalized Orthogonality Collapse" (NOC v5) meta-utility function.
Instead of just rewarding `correctness`, it rewards **Acceleration** and **Synergy**:

    M = alpha * Delta U + beta * Delta^2 U + gamma * Delta Sigma - zeta * J

Key Features:
1.  **Acceleration (Delta^2 U):** Rewards the agent for the *rate* of its improvement, forcing it out of plateaus (Lemma B).
2.  **Synergy (Delta Sigma):** Uses `logprobs` to calculate the **Information Gain** (reduction in surprise) the agent's hint provides.
3.  **Async-Native:** Compatible with Atropos `BaseServer` for distributed async rollouts.

Usage: Drop this into your Atropos `envs/` folder and pass a vLLM-compatible server instance.
"""

from typing import Any, Dict, Tuple, List, Optional
import numpy as np
import logging

# Atropos Imports
try:
    from atroposlib.envs.base import BaseEnv
    from atroposlib.core.trajectory import Trajectory, Step
    from atroposlib.envs.server_handling.base import BaseServer
except ImportError:
    # Mock for local validity if Atropos is not installed
    class BaseEnv:
        def __init__(self, **kwargs): pass
    class BaseServer:
        async def generate(self, **kwargs): return {}

class NOCCoordinationEnv(BaseEnv):
    """
    NOC v5 'Capacity-Optionality' Environment for Atropos.
    """
    
    def __init__(
        self,
        server: BaseServer,
        dataset: List[Dict],
        alpha: float = 1.0,         # Weight for direct improvement (Delta U)
        beta_meta: float = 0.5,     # Weight for acceleration (Delta^2 U) - Lemma B
        gamma: float = 2.0,         # Weight for Synergy/Optionality (Delta Sigma)
        zeta: float = 0.01,         # Weight for Cost (J)
        **kwargs
    ):
        super().__init__(**kwargs)
        self.server = server
        self.dataset = dataset
        
        # Meta-Utility Weights
        self.alpha = alpha
        self.beta_meta = beta_meta
        self.gamma = gamma
        self.zeta = zeta
        
        # State tracking
        self.current_idx = 0
        # History buffer for derivatives [U_{t-2}, U_{t-1}, U_t]
        self.u_history: List[float] = [0.0, 0.0] 

    async def reset(self, *args, **kwargs) -> Tuple[str, Dict]:
        """
        Resets the environment to the start state.
        Required by Atropos/Gym API.
        """
        self.current_idx = 0
        self.u_history = [0.0, 0.0]
        
        # Return initial observation
        first_task = self.dataset[0]['question']
        return first_task, {}

    async def step(self, action_text: str) -> Tuple[Any, float, bool, Dict]:
        """
        Execute one step using the v5 NOC Meta-Utility function.
        """
        task_data = self.dataset[self.current_idx]
        question = task_data['question']
        target = task_data['answer']
        
        # --- 1. Calculate Task Capacity (U) ---
        # In this env, U is binary: Did the agent solve the task?
        current_u = 1.0 if target.lower() in action_text.lower() else 0.0
        
        # --- 2. Calculate Derivatives (Delta U, Delta^2 U) ---
        prev_u = self.u_history[-1]
        prev_prev_u = self.u_history[-2]
        
        # First Difference (Improvement rate)
        delta_u = current_u - prev_u
        
        # Second Difference (Acceleration) - Critical for Lemma B
        prev_delta_u = prev_u - prev_prev_u
        delta_sq_u = delta_u - prev_delta_u
        
        # Update history buffer
        self.u_history.append(current_u)
        if len(self.u_history) > 3:
            self.u_history.pop(0)

        # --- 3. Calculate Synergy (Delta Sigma) ---
        # We measure Information Gain: Reduction in surprise of the answer 
        
        # A. Baseline Log-Prob: P(Answer | Question)
        prompt_base = f"Question: {question}\nAnswer:"
        lp_base = await self._get_target_logprob(prompt_base, target)
        
        # B. Helped Log-Prob: P(Answer | Question + Action)
        prompt_help = f"Question: {question}\nHint: {action_text}\nAnswer:"
        lp_help = await self._get_target_logprob(prompt_help, target)
        
        # Synergy = Information Gain (nats/bits)
        delta_sigma = lp_help - lp_base
        
        # --- 4. Calculate Cost (J) ---
        cost_j = len(action_text) * self.zeta
        
        # --- 5. Final Meta-Utility (M) ---
        reward = (self.alpha * delta_u) + \
                 (self.beta_meta * delta_sq_u) + \
                 (self.gamma * delta_sigma) - \
                 cost_j
        
        # --- 6. Diagnostics & Logging ---
        info = {
            "U_score": current_u,
            "Delta_U": delta_u,
            "Acceleration": delta_sq_u,
            "Synergy_Sigma": delta_sigma,
            "Cost_J": cost_j,
            "Rho_ratio": (self.gamma * delta_sigma) / (cost_j + 1e-9)
        }
        
        # Rotate Task (Infinite Episode Logic)
        self.current_idx = (self.current_idx + 1) % len(self.dataset)
        next_obs = self.dataset[self.current_idx]['question']
        
        return next_obs, reward, False, info

    async def _get_target_logprob(self, prompt: str, target: str) -> float:
        """
        Computes log(P(target | prompt)) using the Atropos inference server.
        """
        full_text = prompt + target
        
        try:
            # Standard vLLM/SGLang parameters via Atropos
            response = await self.server.generate(
                prompt=full_text,
                max_tokens=1,     # We only need logprobs of the prompt+target
                logprobs=1,       # Request logprobs
                echo=True,        # Echo prompt to get logprobs of input tokens
                temperature=0.0   # Deterministic evaluation
            )
            
            if 'logprobs' in response and response['logprobs']:
                token_logprobs = response['logprobs']['token_logprobs']
                tokens = response['logprobs']['tokens']
                
                # Heuristic: Iterate backwards to find the target tokens
                target_len_chars = len(target)
                accumulated_lp = 0.0
                chars_covered = 0
                
                for token, lp in zip(reversed(tokens), reversed(token_logprobs)):
                    if lp is None: continue
                    accumulated_lp += lp
                    chars_covered += len(token)
                    if chars_covered >= target_len_chars:
                        break
                        
                return accumulated_lp
                
            return 0.0
            
        except Exception as e:
            logging.error(f"Logprob fetch failed: {e}")
            return -10.0 # Penalty for inference failure
