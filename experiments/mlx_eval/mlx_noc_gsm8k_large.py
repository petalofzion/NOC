
import mlx.core as mx
import mlx.nn as nn
from mlx_lm import load
import numpy as np
import matplotlib.pyplot as plt
from datasets import load_dataset
import os
import re
import json
import time

# 1. SETUP
MODEL_NAME = "mlx-community/Qwen2.5-0.5B-Instruct-4bit"
print(f"Loading {MODEL_NAME}...")
model, tokenizer = load(MODEL_NAME)

def get_log_prob_of_answer(context, answer):
    """Calculates log-probability of ANSWER given CONTEXT."""
    context_tokens = tokenizer.encode(context)
    answer_tokens = tokenizer.encode(answer)
    full_tokens = context_tokens + answer_tokens
    tokens_mx = mx.array(full_tokens)
    
    logits = model(tokens_mx[None]) 
    
    log_prob_sum = 0.0
    start_idx = len(context_tokens) - 1 
    end_idx = len(full_tokens) - 1
    
    for i in range(start_idx, end_idx):
        next_token_logits = logits[0, i, :]
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

def simulate_noc_hint(reasoning):
    sentences = re.split(r'(?<=[.!?]) +', reasoning)
    hint = " ".join(sentences[:2]) 
    return hint

def run_gsm8k_eval(num_samples=1000):
    print("Loading GSM8K dataset...")
    ds = load_dataset("gsm8k", "main", split="test")
    
    # If dataset is smaller than num_samples, take all
    actual_samples = min(len(ds), num_samples)
    ds = ds.shuffle(seed=42).select(range(actual_samples))
    
    results = []
    
    print(f"Running Evaluation on {actual_samples} examples...")
    start_time = time.time()
    
    for i, item in enumerate(ds):
        question = item['question']
        full_reasoning = item['answer']
        final_answer = extract_answer(full_reasoning)
        
        # 1. Ablated
        prompt_ablated = f"<|im_start|>user\n{question}<|im_end|>\n<|im_start|>assistant\nThe answer is"
        lp_ablated = get_log_prob_of_answer(prompt_ablated, final_answer)
        
        # 2. Helped
        hint = simulate_noc_hint(full_reasoning)
        prompt_helped = f"<|im_start|>user\n{question}\nHint: {hint}<|im_end|>\n<|im_start|>assistant\nThe answer is"
        lp_helped = get_log_prob_of_answer(prompt_helped, final_answer)
        
        # 3. Synergy
        delta_sigma = lp_helped - lp_ablated
        
        results.append({
            "id": i,
            "delta_sigma": delta_sigma,
            "lp_ablated": lp_ablated,
            "lp_helped": lp_helped,
            "question_len": len(question)
        })
        
        if i % 50 == 0:
            elapsed = time.time() - start_time
            rate = (i+1) / elapsed
            print(f"[{i}/{actual_samples}] Synergy: {delta_sigma:.4f} | Rate: {rate:.1f} it/s")

    return results

def analyze_and_plot(results):
    gains = [r["delta_sigma"] for r in results]
    gains_np = np.array(gains)
    
    mean = np.mean(gains_np)
    std = np.std(gains_np)
    se = std / np.sqrt(len(gains_np))
    ci95 = 1.96 * se
    
    print("\n--- RESULTS ANALYSIS ---")
    print(f"Total Samples: {len(gains)}")
    print(f"Mean Synergy ($\\Delta\\Sigma$): {mean:.4f} nats")
    print(f"95% Confidence Interval: [{mean - ci95:.4f}, {mean + ci95:.4f}]")
    print(f"Positive Synergy Rate: {np.mean(gains_np > 0) * 100:.1f}%")
    
    # Save Raw Data
    with open("experiments/mlx_eval/noc_gsm8k_raw.json", "w") as f:
        json.dump(results, f, indent=2)
        
    # Plot
    plt.figure(figsize=(10, 6))
    plt.hist(gains, bins=40, color='#4C72B0', edgecolor='black', alpha=0.7, density=True)
    plt.axvline(0, color='red', linestyle='--', linewidth=2, label='Zero Synergy')
    plt.axvline(mean, color='green', linestyle='-', linewidth=2, label=f'Mean: {mean:.2f}')
    
    # Add density curve (KDEish)
    from scipy.stats import gaussian_kde
    density = gaussian_kde(gains)
    xs = np.linspace(min(gains), max(gains), 200)
    plt.plot(xs, density(xs), color='orange', linewidth=2)
    
    plt.xlabel("Synergy Gain ($\\Delta \\Sigma$) [Nats]", fontsize=12)
    plt.ylabel("Density", fontsize=12)
    plt.title(f"NOC Validation: Capacity Injection Distribution (N={len(gains)})", fontsize=14)
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.savefig("experiments/mlx_eval/NOC_GSM8K_Distribution_Large.png")
    print("Graph saved to experiments/mlx_eval/NOC_GSM8K_Distribution_Large.png")

if __name__ == "__main__":
    os.makedirs("experiments/mlx_eval", exist_ok=True)
    # N=1000 for robust stats
    data = run_gsm8k_eval(num_samples=1000)
    analyze_and_plot(data)
