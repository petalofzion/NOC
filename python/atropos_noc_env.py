"""
Title: NOC (Naturalized Orthogonality Collapse) Environment for Atropos
Description: Implements Intrinsic Motivation via Acceleration and Synergy rewards.
Compatibility: Atropos v1.0+ (BaseEnv architecture)
"""

import logging
import numpy as np
from typing import List, Dict, Any, Tuple, Optional
from dataclasses import dataclass

# Atropos Imports
from atroposlib.envs.base import BaseEnv, BaseEnvConfig
from atroposlib.core.trajectory import ScoredDataGroup
from atroposlib.server.config import OpenaiConfig

@dataclass
class NOCEnvConfig(BaseEnvConfig):
    # Standard Atropos defaults
    max_token_length: int = 2048
    group_size: int = 16  
    
    # NOC Specific Hyperparameters
    alpha: float = 1.0      # Weight for Direct Improvement (Delta U)
    beta_meta: float = 0.5  # Weight for Acceleration/Variance proxy
    gamma: float = 2.0      # Weight for Synergy (Delta Sigma)
    zeta: float = 0.001     # Weight for Cost (J)
    
    # Dataset config
    dataset_name: str = "gsm8k" 
    dataset_split: str = "train"
    tokenizer_name: str = "gpt2" 

class NOCEnv(BaseEnv):
    """
    Atropos Environment implementing NOC Meta-Utility.
    """

    @classmethod
    def config_init(cls):
        """Injects configuration for the environment and the LLM server."""
        return NOCEnvConfig, [OpenaiConfig]

    def setup(self):
        """
        Initializes the dataset. 
        """
        try:
            import datasets
            ds = datasets.load_dataset(self.config.dataset_name, "main")
            self.train_ds = ds['train']
            self.dataset = self.train_ds 
            logging.info(f"NOCEnv: Loaded {self.config.dataset_name} with {len(self.dataset)} samples.")
        except ImportError:
            raise RuntimeError("The 'datasets' library is missing. Please install it to run NOCEnv.")

    async def collect_trajectories(self, item: Dict) -> ScoredDataGroup:
        """
        Phase 1 & 2: Generation AND Scoring.
        Returns the final ScoredDataGroup for the Trainer.
        """
        question = item['question']
        target = item['answer']
        
        prompt = (
            f"Question: {question}\n"
            "Please think step by step to find the answer.\n"
            "Response:"
        )

        # Managed Server Context
        if hasattr(self.server, 'managed_server'):
            async with self.server.managed_server(self.tokenizer) as managed:
                rollouts = await managed.chat_completion(
                    messages=[{"role": "user", "content": prompt}],
                    max_tokens=self.config.max_token_length,
                    n=self.config.group_size,
                    temperature=1.0 
                )
        else:
            rollouts = await self.server.chat_completion(
                messages=[{"role": "user", "content": prompt}],
                max_tokens=self.config.max_token_length,
                n=self.config.group_size,
                temperature=1.0
            )

        group_data = {
            "item": item,
            "prompt": prompt,
            "rollouts": rollouts, 
            "ground_truth": target
        }
        
        return await self.score(group_data)

    async def score(self, group_data: Any) -> ScoredDataGroup:
        """
        Phase 2: Evaluation.
        Calculates Meta-Utility M and packs data manually for safety.
        """
        target = group_data['ground_truth']
        rollouts = group_data['rollouts']
        prompt = group_data['prompt']
        
        # Initialize output container explicitely 
        scored_data = ScoredDataGroup(
            tokens=[], masks=[], rewards=[], prompts=[], texts=[]
        )
        
        # --- 1. Calculate Batch Statistics ---
        correctness_vector = []
        texts = []
        
        # Extract texts and basic stats first
        for completion in rollouts:
            if hasattr(completion.choices[0].message, 'content'):
                text = completion.choices[0].message.content
            else:
                text = ""
            texts.append(text)
            
            is_correct = 1.0 if target.strip() in text else 0.0
            correctness_vector.append(is_correct)
            
        # Batch Variance (Acceleration Proxy)
        if not correctness_vector:
            batch_accel_proxy = 0.0
        else:
            batch_accel_proxy = np.var(correctness_vector)

        # --- 2. Scoring & Manual Tokenization ---
        for i, text in enumerate(texts):
            # --- Reward Calculation ---
            # A. Utility
            u_val = correctness_vector[i] if i < len(correctness_vector) else 0.0
            
            # B. Cost
            cost_j = len(text) * self.config.zeta
            
            # C. Synergy
            synergy_val = await self._calculate_synergy(prompt, text, target)
            
            # D. Final Reward
            reward = (self.config.alpha * u_val) + \
                     (self.config.beta_meta * batch_accel_proxy) + \
                     (self.config.gamma * synergy_val) - \
                     cost_j
            
            # --- Manual Tokenization & Packing ---
            conversation = [
                {"role": "user", "content": prompt},
                {"role": "assistant", "content": text}
            ]
            
            try:
                # FIX: Check for chat template availability
                if getattr(self.tokenizer, 'chat_template', None):
                    formatted_text = self.tokenizer.apply_chat_template(
                        conversation, 
                        tokenize=False, 
                        add_generation_prompt=False
                    )
                else:
                    # Fallback for GPT-2 or models without chat templates
                    formatted_text = f"{prompt}\n{text}"

                # Tokenize
                encoding = self.tokenizer(
                    formatted_text,
                    truncation=True,
                    max_length=self.config.max_token_length,
                    padding=False, 
                    return_tensors=None 
                )
                
                tokens = encoding['input_ids']
                mask = encoding['attention_mask']
                
                # Append to ScoredDataGroup
                if hasattr(scored_data, 'tokens'): scored_data.tokens.append(tokens)
                if hasattr(scored_data, 'masks'): scored_data.masks.append(mask)
                if hasattr(scored_data, 'rewards'): scored_data.rewards.append(reward)
                if hasattr(scored_data, 'prompts'): scored_data.prompts.append(prompt)
                if hasattr(scored_data, 'texts'): scored_data.texts.append(text)
                
            except Exception as e:
                logging.warning(f"Tokenization failed for sample {i}: {e}")
                
        return scored_data

    async def _calculate_synergy(self, prompt: str, generated_thought: str, target: str) -> float:
        """
        Calculates Information Gain (Delta Sigma).
        """
        try:
            # 1. Baseline: P(Answer | Prompt)
            base_req = f"{prompt}\nAnswer: {target}"
            base_logprob = await self._fetch_sequence_logprob(base_req, target)
            
            # 2. Helped: P(Answer | Prompt + Thought)
            help_req = f"{prompt}\n{generated_thought}\nAnswer: {target}"
            help_logprob = await self._fetch_sequence_logprob(help_req, target)
            
            return max(help_logprob - base_logprob, -5.0) 
            
        except Exception as e:
            logging.warning(f"Synergy calc failed: {e}")
            return 0.0

    async def _fetch_sequence_logprob(self, full_text: str, target_suffix: str) -> float:
        """
        Extracts the log-probability of the target_suffix given the prefix.
        Uses Completions API to support echo=True.
        """
        try:
            # FIX: Use raw completion endpoint for echo=True support
            # vLLM Chat Endpoint DOES NOT support echo.
            if hasattr(self.server, 'managed_server'):
                async with self.server.managed_server(self.tokenizer) as managed:
                    # We access the raw OpenAI client inside the managed wrapper
                    # Note: This assumes 'managed' exposes 'client' or we call directly
                    if hasattr(managed, 'client'):
                        response = await managed.client.completions.create(
                            model=self.config.tokenizer_name, # Use config model name
                            prompt=full_text,
                            max_tokens=0, # vLLM supports 0 for pure echo
                            logprobs=1, 
                            echo=True, 
                            temperature=0.0
                        )
                    else:
                         # Fallback if managed wrapper hides client
                         # This path might fail on Chat-Only servers
                         return 0.0
            else:
                # Fallback for mock/legacy
                return 0.0
            
            # Parse Standard OpenAI Completion Object
            if not response or not response.choices: return 0.0
            
            choice = response.choices[0]
            if not hasattr(choice, 'logprobs') or not choice.logprobs: return 0.0
            
            logprobs_data = choice.logprobs
            tokens = logprobs_data.tokens
            token_logprobs = logprobs_data.token_logprobs
            
            # Reverse Matcher
            accumulated_logprob = 0.0
            matched_str = ""
            target_clean = target_suffix.strip()
            lookback_limit = min(len(tokens), 50) 
            found_match = False
            
            for i in range(1, lookback_limit + 1):
                idx = -i
                tok = tokens[idx]
                val = token_logprobs[idx]
                if val is not None: accumulated_logprob += val
                matched_str = tok + matched_str
                if target_clean in matched_str:
                    found_match = True
                    break
            
            return accumulated_logprob if found_match else 0.0
            
        except Exception as e:
            # logging.warning(f"Logprob fetch failed: {e}")
            return 0.0