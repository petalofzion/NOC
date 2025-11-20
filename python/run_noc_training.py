
import asyncio
import os
import sys

# Mock imports if on Mac (so you can see the code structure)
# On your CUDA Laptop, these imports will work natively.
try:
    from atropos_noc_env1 import NOCEnv, NOCEnvConfig
    from atroposlib.server.vllm_server import VLLMServer
    from atroposlib.trainer import AtroposTrainer
    from atroposlib.server.config import VllmConfig
except ImportError:
    print("Atropos not installed. This script is a TEMPLATE for your CUDA laptop.")
    sys.exit(0)

async def main():
    # 1. Configure the GPU Server (vLLM)
    # This will load the model onto your Laptop's GPU
    server_config = VllmConfig(
        model_name="Qwen/Qwen2.5-1.5B-Instruct", # Fits on 6GB VRAM
        gpu_memory_utilization=0.7,              # Leave room for overhead
        tensor_parallel_size=1                   # Single GPU
    )
    
    # Initialize the server wrapper
    server = VLLMServer(server_config)
    
    try:
        # 2. Start the Server
        print(">>> Starting vLLM Server on GPU...")
        await server.start()
        
        # 3. Initialize YOUR Custom NOC Environment
        # This connects the NOC math to the vLLM server
        env_config = NOCEnvConfig(
            dataset_name="gsm8k",
            group_size=4,   # Small batch for laptop testing
            gamma=2.0,      # Synergy Weight
            beta_meta=0.5   # Acceleration Weight
        )
        
        # Note: We pass None for tokenizer here as vLLM handles it, 
        # but real Atropos might need a tokenizer object.
        env = NOCEnv(server=server, tokenizer=None, config=env_config)
        env.setup() # Loads dataset
        
        # 4. Run the Loop (Collection -> Scoring)
        print(">>> Starting NOC Data Collection...")
        
        # Iterate through a few items
        for i in range(3):
            item = env.dataset[i]
            print(f"\n--- Processing Question {i+1}: {item['question']} ---")
            
            # A. Collect (Generate Hints)
            group_data, _ = await env.collect_trajectories(item)
            print(f"    Generated {len(group_data['rollouts'])} rollouts.")
            print(f"    Sample: {group_data['rollouts'][0].choices[0].message.content[:50]}...")
            
            # B. Score (Calculate Acceleration & Synergy)
            print("    Calculating Synergy & Acceleration...")
            scored_data = await env.score(group_data)
            
            avg_reward = sum(scored_data.rewards) / len(scored_data.rewards)
            print(f"    > Average NOC Reward: {avg_reward:.4f}")
            print(f"    > Global Acceleration History: {env.global_score_history}")

    finally:
        # Cleanup
        print(">>> Stopping Server...")
        await server.stop()

if __name__ == "__main__":
    asyncio.run(main())
