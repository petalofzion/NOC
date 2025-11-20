
import sys
import asyncio
import types
import unittest.mock as mock
import os
from dataclasses import dataclass
import numpy as np
import inspect

# --- MOCK ATROPOS LIBRARY ---
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
    dataset_name: str = "gsm8k"
    dataset_split: str = "train"
    tokenizer_name: str = "mock_gpt"
    model_name: str = "mock_gpt" # Added model_name
    alpha: float = 1.0
    beta_meta: float = 0.5
    gamma: float = 2.0
    zeta: float = 0.01

class MockAPIServerConfig:
    def __init__(self, **kwargs): pass

class MockOpenaiConfig: pass

class MockScoredDataGroup:
    def __init__(self, tokens=None, masks=None, rewards=None, prompts=None, texts=None):
        self.tokens = tokens or []
        self.rewards = rewards or []
        self.texts = texts or []

m_base = types.ModuleType("atroposlib.envs.base")
m_base.BaseEnv = MockBaseEnv
m_base.BaseEnvConfig = MockBaseEnvConfig
sys.modules["atroposlib.envs.base"] = m_base

m_traj = types.ModuleType("atroposlib.core.trajectory")
m_traj.ScoredDataGroup = MockScoredDataGroup
sys.modules["atroposlib.core.trajectory"] = m_traj

m_cfg = types.ModuleType("atroposlib.server.config")
m_cfg.APIServerConfig = MockAPIServerConfig
m_cfg.OpenaiConfig = MockOpenaiConfig
sys.modules["atroposlib.server.config"] = m_cfg

mock_ds = {'train': [{'question': '2+2', 'answer': '4'}]}
sys.modules["datasets"] = mock.MagicMock()
sys.modules["datasets"].load_dataset.return_value = mock_ds

class MockTokenizer:
    def __init__(self):
        self.pad_token = None
        self.eos_token = "</s>"
        self.chat_template = "exists"
    def apply_chat_template(self, conv, **kwargs): return "MOCK PROMPT"
    # Simulate HF returning nested lists sometimes
    def __call__(self, text, **kwargs): 
        return {'input_ids': [[1, 2, 3]], 'attention_mask': [[1, 1, 1]]}
    def decode(self, tokens): return "decoded text"
    @classmethod
    def from_pretrained(cls, *args, **kwargs): return cls()

sys.modules["transformers"] = mock.MagicMock()
sys.modules["transformers"].AutoTokenizer.from_pretrained = MockTokenizer.from_pretrained

# --- IMPORT ENV ---
sys.path.append(os.path.join(os.getcwd(), 'python'))
try:
    from atropos_noc_env import NOCEnv, NOCEnvConfig
except ImportError as e:
    print(f"[FAIL] Import: {e}")
    sys.exit(1)

# --- RUNTIME SIMULATION ---
class MockManagedServer:
    def __init__(self, client): self.client = client
    async def __aenter__(self): return self
    async def __aexit__(self, exc_type, exc, tb): pass
    async def chat_completion(self, **kwargs):
        class Msg: 
            def __init__(self): self.content = "The answer is 4"
        class Choice:
            def __init__(self): self.message = Msg()
        class Comp:
            def __init__(self): self.choices = [Choice()]
        return [Comp(), {"choices": [{"message": {"content": "Dict Response"}}]}]

class MockClient:
    def __init__(self): self.completions = self
    async def create(self, **kwargs):
        class LPData:
            def __init__(self):
                self.tokens = [1, 2, 3] # Use Ints to test decode path
                self.token_logprobs = [-0.1, -0.1, -0.1]
        class Choice:
            def __init__(self): self.logprobs = LPData()
        class Resp:
            def __init__(self): self.choices = [Choice()]
        return Resp()

class MockServer:
    def __init__(self): self.client = MockClient()
    def managed_server(self, tokenizer): return MockManagedServer(self.client)

async def run_test():
    print("--- Starting Final Integrity Check ---")
    
    # TEST 1: CONFIG INIT
    cfg, srv = NOCEnv.config_init()
    if not isinstance(cfg, NOCEnvConfig):
        print(f"[FAIL] config_init returned class not instance: {type(cfg)}")
        sys.exit(1)
    print("[SUCCESS] config_init instance check")
    
    # TEST 2: SETUP
    tokenizer = MockTokenizer()
    server = MockServer()
    env = NOCEnv(server, tokenizer, cfg)
    env.setup()
    print("[SUCCESS] setup")
    
    # TEST 3: COLLECT & NORMALIZE & FLATTEN
    item = {'question': '2+2', 'answer': '4'}
    result = await env.collect_trajectories(item)
    
    # Check Flattening
    if len(result.tokens) > 0:
        first_sample = result.tokens[0]
        if isinstance(first_sample[0], list):
            print(f"[FAIL] Token flattening failed. Got nested list: {first_sample}")
            sys.exit(1)
        else:
            print(f"[SUCCESS] Tokens flattened correctly: {first_sample}")
            
    print("[SUCCESS] Full Integrity Check Passed")

if __name__ == "__main__":
    asyncio.run(run_test())
