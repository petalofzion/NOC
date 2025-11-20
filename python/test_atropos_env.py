import asyncio
import sys
import os

# Ensure python directory is in path
sys.path.append(os.path.join(os.getcwd(), 'python'))

from atropos_noc_env1 import NOCCoordinationEnv

# 1. Mock the Atropos Server
class MockServer:
    async def generate(self, prompt, **kwargs):
        fake_logprob = -5.0
        if "Hint:" in prompt:
            fake_logprob = -1.0
        return {
            "logprobs": {
                "token_logprobs": [fake_logprob, -0.1, -0.1],
                "tokens": [" The", " answer", " is"]
            }
        }

# 2. Mock Dataset
dataset = [
    {"question": "Q1", "answer": "4"},
    {"question": "Q2", "answer": "Paris"},
    {"question": "Q3", "answer": "Shakespeare"}
]

async def main():
    print("Initializing NOC Environment...")
    server = MockServer()
    env = NOCCoordinationEnv(server=server, dataset=dataset)
    
    obs, _ = await env.reset()
    print(f"Initial Observation: {obs}")
    
    actions = [
        "Hint: It is a number.",
        "Just guessing.",
        "Hint: It is a city in Europe."
    ]
    
    for i, action in enumerate(actions):
        print(f"\n--- Step {i+1}: Agent says '{action}' ---")
        obs, reward, done, info = await env.step(action)
        print(f"  -> Reward: {reward:.4f}")
        print(f"  -> Synergy: {info['Synergy_Sigma']:.4f}")
        print(f"  -> Acceleration: {info['Acceleration']:.4f}")

if __name__ == "__main__":
    asyncio.run(main())
