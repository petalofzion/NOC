import sys
import asyncio
import types
import unittest.mock as mock
import os
import numpy as np
from dataclasses import dataclass

# --- 1. MOCK INJECTION ---
class MockBaseEnv:
    def __init__(self, server, tokenizer, config):
        self.server = server
        self.tokenizer = tokenizer
        self.config = config
    def setup(self): pass

@dataclass
class MockBaseEnvConfig:
    max_token_length: int = 100
    group_size: int = 2
    alpha: float = 1.0
    beta_meta: float = 0.5
    gamma: float = 2.0
    zeta: float = 0.01
    dataset_name: str = "mock_dataset"
    tokenizer_name: str = "mock_gpt"

m_base = types.ModuleType("atroposlib.envs.base")
m_base.BaseEnv = MockBaseEnv
m_base.BaseEnvConfig = MockBaseEnvConfig
sys.modules["atroposlib.envs.base"] = m_base

m_traj = types.ModuleType("atroposlib.core.trajectory")
class ScoredDataGroup:
    def __init__(self, rewards): self.rewards = rewards
m_traj.ScoredDataGroup = ScoredDataGroup
sys.modules["atroposlib.core.trajectory"] = m_traj

m_utils = types.ModuleType("atroposlib.core.utils")
async def mock_tokenize(**kwargs):
    return ScoredDataGroup(kwargs['rewards'])
m_utils.tokenize_for_trainer = mock_tokenize
sys.modules["atroposlib.core.utils"] = m_utils

m_cfg = types.ModuleType("atroposlib.server.config")
class OpenaiConfig: pass
m_cfg.OpenaiConfig = OpenaiConfig
sys.modules["atroposlib.server.config"] = m_cfg

mock_ds = {'train': [{'question': '2+2', 'answer': '4'}], 'test': []}
sys.modules["datasets"] = mock.MagicMock()
sys.modules["datasets"].load_dataset.return_value = mock_ds

# --- 2. IMPORT ENV ---
sys.path.append(os.path.join(os.getcwd(), 'python'))
from atropos_noc_env1 import NOCEnv, NOCEnvConfig

# --- 3. ADVANCED MOCK SERVER ---
class MockServer:
    def __init__(self):
        self.mode = "idiot" 

    def set_mode(self, mode):
        self.mode = mode

    async def chat_completion(self, messages, n, **kwargs):
        prompt = messages[0]['content']
        if self.mode == "idiot": text = "I dont know."
        elif self.mode == "genius": text = "The answer is 4."
        elif self.mode == "teacher": text = "Hint: Think about adding."
        
        class Message:
            def __init__(self, content): self.content = content
        class Choice:
            def __init__(self, content): self.message = Message(content)
        class Completion:
            def __init__(self, content): self.choices = [Choice(content)]
        return [Completion(text) for _ in range(n)]

    async def generate(self, prompt, **kwargs):
        base_lp = -10.0
        help_lp = -10.0
        
        if "Hint:" in prompt: help_lp = -2.0 
        elif "The answer is 4" in prompt: help_lp = -0.1 
            
        current_val = base_lp
        if "Hint:" in prompt or "The answer is" in prompt:
            current_val = help_lp
            
        # CRITICAL FIX: Return tokens that actually contain the answer "4"
        return {
            "logprobs": {
                # The last token " 4" has the logprob we care about
                "token_logprobs": [-0.1, -0.1, -0.1, current_val],
                "tokens": [" The", " answer", " is", " 4"]
            }
        }

# --- 4. RUN TEST ---
async def run_math_verification():
    print("\n=== STARTING NOC MATH VERIFICATION ===\n")
    
    server = MockServer()
    config = NOCEnvConfig(
        alpha=1.0, 
        beta_meta=1.0, 
        gamma=1.0, 
        zeta=0.0 
    )
    
    class MockTok: pass
    env = NOCEnv(server, MockTok(), config)
    env.setup()
    item = {'question': '2+2?', 'answer': '4'}
    
    print(">>> TEST 1: Mode 'Idiot' (Expect 0.0)")
    server.set_mode("idiot")
    group_data, _ = await env.collect_trajectories(item)
    scored = await env.score(group_data)
    print(f"    Avg Reward: {np.mean(scored.rewards):.4f}")
    
    print("\n>>> TEST 2: Mode 'Teacher' (Expect ~8.0 Synergy)")
    server.set_mode("teacher")
    group_data, _ = await env.collect_trajectories(item)
    scored = await env.score(group_data)
    print(f"    Avg Reward: {np.mean(scored.rewards):.4f}")
    
    print("\n>>> TEST 3: Mode 'Genius' (Expect ~10.0 [U=1 + Synergy=9])")
    server.set_mode("genius")
    group_data, _ = await env.collect_trajectories(item)
    scored = await env.score(group_data)
    print(f"    Avg Reward: {np.mean(scored.rewards):.4f}")

    print("\n=== VERIFICATION COMPLETE ===")

if __name__ == "__main__":
    asyncio.run(run_math_verification())