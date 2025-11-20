import mlx.core as mx
import mlx.nn as nn  # Import nn specifically
from mlx_lm import load
import numpy as np
import matplotlib.pyplot as plt
from datasets import load_dataset
import os
import re

# 1. SETUP: Use Qwen 0.5B
MODEL_NAME = "mlx-community/Qwen2.5-0.5B-Instruct-4bit"
print(f"Loading {MODEL_NAME}...")
model, tokenizer = load(MODEL_NAME)

def get_log_prob_of_answer(context, answer):
    """Calculates log-probability of ANSWER given CONTEXT."""
    context_tokens = tokenizer.encode(context)
    answer_tokens = tokenizer.encode(answer)
    full_tokens = context_tokens + answer_tokens
    tokens_mx = mx.array(full_tokens)
    
    # Forward pass
    logits = model(tokens_mx[None]) 
    
    log_prob_sum = 0.0
    start_idx = len(context_tokens) - 1 
    end_idx = len(full_tokens) - 1
    
    for i in range(start_idx, end_idx):
        next_token_logits = logits[0, i, :]
        # FIXED: Use nn.log_softmax from mlx.nn, not mx.nn
        next_token_logprobs = nn.log_softmax(next_token_logits)
        
        target_token = full_tokens[i+1]
        token_score = next_token_logprobs[target_token].item()
        log_prob_sum += token_score
        
    return log_prob_sum

def extract_answer(answer_str):
    parts = answer_str.split("####")
    if len(parts) > 1:
        return parts[1].strip()
    return answer_str.strip()

def simulate_noc_hint(question, reasoning):
    sentences = re.split(r'(?<=[.!?]) +', reasoning)
    hint = " ".join(sentences[:2]) 
    return hint

def run_gsm8k_eval(num_samples=50):
    print("Loading GSM8K dataset...")
    ds = load_dataset("gsm8k", "main", split="test")
    
    ds = ds.shuffle(seed=42).select(range(num_samples))
    
    synergy_gains = []
    
    print(f"Running Evaluation on {num_samples} examples...")
    
    for i, item in enumerate(ds):
        question = item['question']
        full_reasoning = item['answer']
        final_answer = extract_answer(full_reasoning)
        
        # 1. Ablated
        prompt_ablated = f"<|im_start|>user\n{question}<|im_end|>\n<|im_start|>assistant\nThe answer is"
        lp_ablated = get_log_prob_of_answer(prompt_ablated, final_answer)
        
        # 2. Helped
        hint = simulate_noc_hint(question, full_reasoning)
        prompt_helped = f"<|im_start|>user\n{question}\nHint: {hint}<|im_end|>\n<|im_start|>assistant\nThe answer is"
        lp_helped = get_log_prob_of_answer(prompt_helped, final_answer)
        
        # 3. Synergy
        delta_sigma = lp_helped - lp_ablated
        synergy_gains.append(delta_sigma)
        
        if i % 10 == 0:
            print(f"[{i}/{num_samples}] Synergy: {delta_sigma:.4f} (Acc: {lp_ablated:.2f} -> {lp_helped:.2f})")

    return synergy_gains

def plot_distribution(gains):
    gains = np.array(gains)
    mean_gain = np.mean(gains)
    
    plt.figure(figsize=(10, 6))
    plt.hist(gains, bins=20, color='#4C72B0', edgecolor='black', alpha=0.7)
    plt.axvline(0, color='red', linestyle='--', linewidth=2, label='Zero Synergy')
    plt.axvline(mean_gain, color='green', linestyle='-', linewidth=2, label=f'Mean Gain: {mean_gain:.2f}')
    
    plt.xlabel("Synergy Gain ($\Delta \Sigma$) [Nats]", fontsize=12)
    plt.ylabel("Frequency (Count)", fontsize=12)
    plt.title(f"Distribution of Capacity Injection (GSM8K, N={len(gains)})", fontsize=14)
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    save_path = "experiments/mlx_eval/NOC_GSM8K_Distribution.png"
    plt.savefig(save_path)
    print(f"Graph saved to {save_path}")

if __name__ == "__main__":
    os.makedirs("experiments/mlx_eval", exist_ok=True)
    gains = run_gsm8k_eval(num_samples=50)
    plot_distribution(gains)
