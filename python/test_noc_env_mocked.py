
import sys
import asyncio
import types
from dataclasses import dataclass

# --- 1. MOCK ATROPOS LIBRARY ---
# We inject fake modules so we can import the production file without crashing.

# Mock Classes
@dataclass
class BaseEnvConfig:
    max_token_length: int = 100
    group_size: int = 2
    alpha: float = 1.0
    beta_meta: float = 0.5
    gamma: float = 2.0
    zeta: float = 0.01
    dataset_name: str = "mock_dataset"
    tokenizer_name: str = "mock_gpt"

class BaseEnv:
    def __init__(self, server, tokenizer, config):
        self.server = server
        self.tokenizer = tokenizer
        self.config = config
    def setup(self):
        pass

class ScoredDataGroup:
    pass

async def tokenize_for_trainer(*args, **kwargs):
    return "mock_tokenized_data"

# Inject into sys.modules
m1 = types.ModuleType("atroposlib.envs.base")
m1.BaseEnv = BaseEnv
m1.BaseEnvConfig = BaseEnvConfig
sys.modules["atroposlib.envs.base"] = m1

m2 = types.ModuleType("atroposlib.core.trajectory")
m2.ScoredDataGroup = ScoredDataGroup
sys.modules["atroposlib.core.trajectory"] = m2

m3 = types.ModuleType("atroposlib.core.utils")
m3.tokenize_for_trainer = tokenize_for_trainer
sys.modules["atroposlib.core.utils"] = m3

m4 = types.ModuleType("atroposlib.llm_utils.solvers")
sys.modules["atroposlib.llm_utils.solvers"] = m4

m5 = types.ModuleType("atroposlib.server.config")
class OpenaiConfig:
    pass
m5.OpenaiConfig = OpenaiConfig
sys.modules["atroposlib.server.config"] = m5

# --- 2. MOCK DATASET ---
# We need to intercept 'datasets.load_dataset'
import unittest.mock as mock
mock_ds = {
    'train': [
        {'question': 'What is 2+2?', 'answer': '4'},
        {'question': 'Capital of France?', 'answer': 'Paris'}
    ],
    'test': []
}
sys.modules["datasets"] = mock.MagicMock()
sys.modules["datasets"].load_dataset.return_value = mock_ds


# --- 3. IMPORT YOUR ENV ---
# Now that mocks are in place, we can safe-import
from atropos_noc_env1 import NOCEnv, NOCEnvConfig

# --- 4. MOCK SERVER & TOKENIZER ---
class MockServer:
    async def chat_completion(self, messages, n, **kwargs):
        # Return N rollouts
        class Message:
            def __init__(self, content):
                self.content = content
        class Choice:
            def __init__(self, content):
                self.message = Message(content)
        class Completion:
            def __init__(self, content):
                self.choices = [Choice(content)]
        
        # Generate different responses to test scoring
        # Response 0: Helpful Hint
        # Response 1: Useless Noise
        responses = [
            Completion("Hint: Think about addition."), 
            Completion("I like turtles.")
        ]
        # Repeat to match group_size if needed
        return responses * (n // 2 + 1)

    async def generate(self, prompt, logprobs=0, echo=False, **kwargs):
        # Return Logprobs
        # If prompt has "Hint: Think about addition", we give HIGH probability to answer
        # Else LOW probability
        
        fake_lp = -5.0 # Baseline
        if "Think about addition" in prompt:
            fake_lp = -1.0 # Improvement!
            
        return {
            "logprobs": {
                "token_logprobs": [fake_lp, -0.1],
                "tokens": [" token", " target"]
            }
        }

class MockTokenizer:
    pass

# --- 5. THE TEST RUNNER ---
async def run_test():
    print(">>> Initializing NOCEnv with Mocks...")
    server = MockServer()
    tokenizer = MockTokenizer()
    config = NOCEnvConfig() # Uses defaults from your file + BaseEnvConfig
    
    env = NOCEnv(server, tokenizer, config)
    env.setup() # Load mock dataset
    
    print(">>> Starting Trajectory Collection (Generation Phase)...")
    item = env.dataset[0] # 'What is 2+2?'
    group_data, _ = await env.collect_trajectories(item)
    
    print(f"    Question: {group_data['item']['question']}")
    print(f"    Generated {len(group_data['rollouts'])} rollouts.")
    print(f"    Rollout 1 Text: '{group_data['rollouts'][0].choices[0].message.content}'")
    
    print("\n>>> Starting Scoring (NOC Evaluation Phase)...")
    # This is where your Math runs
    scored_data = await env.score(group_data)
    
    # Since score() returns 'mock_tokenized_data', we can't inspect rewards directly 
    # unless we print them inside the class or check internal state.
    # Let's check the History Buffer to see if Acceleration updated.
    
    print(f"\n>>> Global Score History: {env.global_score_history}")
    # We expect non-zero history because we ran a batch
    
    print("\n>>> TEST PASSED: Logic flow completed without crashes.")

if __name__ == "__main__":
    asyncio.run(run_test())
