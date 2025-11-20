"""
Title: NOC (Naturalized Orthogonality Collapse) Environment for Atropos
Description: Implements Intrinsic Motivation via Acceleration and Synergy rewards.
Compatibility: Atropos v1.0+ (BaseEnv architecture)
"""

import logging
import os
import numpy as np
import inspect
from typing import List, Dict, Any, Tuple, Optional
from dataclasses import dataclass

# Atropos Imports
from atroposlib.envs.base import BaseEnv, BaseEnvConfig
from atroposlib.core.trajectory import ScoredDataGroup

# Canonical Server Config
try:
    from atroposlib.server.config import APIServerConfig
except ImportError:
    from atroposlib.server.config import OpenaiConfig as APIServerConfig

@dataclass
class NOCEnvConfig(BaseEnvConfig):
    # Standard Atropos defaults
    max_token_length: int = 2048
    group_size: int = 16  
    
    # NOC Specific Hyperparameters
    alpha: float = 1.0      
    beta_meta: float = 0.5  
    gamma: float = 2.0      
    zeta: float = 0.001     
    
    # Data & Model
    dataset_name: str = "gsm8k" 
    dataset_split: str = "train"
    tokenizer_name: str = "gpt2" 
    model_name: str = "gpt2"

class NOCEnv(BaseEnv):
    """
    Atropos Environment implementing NOC Meta-Utility.
    """

    @classmethod
    def config_init(cls) -> Tuple[BaseEnvConfig, List[Any]]:
        """
        Injects configuration for the environment and the LLM server.
        Returns instantiated config objects.
        """
        env_config = NOCEnvConfig(
            max_token_length=2048,
            group_size=16,
            dataset_name="gsm8k",
            tokenizer_name="gpt2",
            model_name="gpt2"
        )

        server_config = APIServerConfig(
            model_name=env_config.model_name,
            base_url=None,     
            api_key=os.environ.get("OPENAI_API_KEY", None), # Safety: None instead of "EMPTY"
            num_requests_for_eval=env_config.group_size 
        )
        return env_config, [server_config]

    def setup(self):
        """
        Initializes the dataset and tokenizer.
        """
        # 1. Load Dataset Robustly
        try:
            import datasets
        except ImportError as e:
            raise RuntimeError("Please `pip install datasets` to run this environment.") from e

        try:
            if self.config.dataset_name == "gsm8k":
                ds = datasets.load_dataset(self.config.dataset_name, "main")
            else:
                ds = datasets.load_dataset(self.config.dataset_name)
                
            split = getattr(self.config, "dataset_split", "train")
            
            if split not in ds:
                if split == "train" and "training" in ds: split = "training"
                elif split == "test" and "validation" in ds: split = "validation"
                else:
                    raise RuntimeError(f"Dataset {self.config.dataset_name} does not contain split '{split}'. Available: {list(ds.keys())}")
            
            self.train_ds = ds[split]
            self.dataset = self.train_ds 
            logging.info(f"NOCEnv: Loaded {self.config.dataset_name} split={split} with {len(self.dataset)} samples.")
            
        except Exception as e:
            raise RuntimeError(f"Failed to load dataset: {e}")

        # 2. Ensure Tokenizer Exists
        if getattr(self, "tokenizer", None) is None:
            try:
                from transformers import AutoTokenizer
                self.tokenizer = AutoTokenizer.from_pretrained(self.config.tokenizer_name)
                if not self.tokenizer.pad_token:
                    self.tokenizer.pad_token = self.tokenizer.eos_token
                logging.info(f"NOCEnv: Built tokenizer from {self.config.tokenizer_name}")
            except Exception as e:
                logging.warning(f"Could not auto-load tokenizer: {e}. Expecting BaseEnv to handle it.")

    def _normalize_rollouts(self, raw_rollouts) -> List[str]:
        """
        Normalizes various server response shapes into a list of strings.
        """
        texts = []
        for r in raw_rollouts:
            text = ""
            try:
                # Case A: Object with choices
                if hasattr(r, "choices"):
                    c = r.choices[0]
                    if hasattr(c, "message") and getattr(c.message, "content", None):
                        text = c.message.content
                    elif getattr(c, "text", None):
                        text = c.text
                # Case B: Dictionary
                elif isinstance(r, dict):
                    if "choices" in r and r["choices"]:
                        c0 = r["choices"][0]
                        if isinstance(c0, dict):
                            text = c0.get("message", {}).get("content", "") or c0.get("text", "")
                        else:
                             if hasattr(c0, "message"): text = c0.message.content
                             elif hasattr(c0, "text"): text = c0.text
                    else:
                        text = r.get("text") or r.get("content", "")
            except Exception:
                text = ""
            texts.append(text or "")
        return texts

    def _make_scored_group(self) -> ScoredDataGroup:
        """
        Factory to create ScoredDataGroup robustly across versions.
        """
        try:
            sig = inspect.signature(ScoredDataGroup)
            if 'tokens' in sig.parameters:
                return ScoredDataGroup(tokens=[], masks=[], rewards=[], prompts=[], texts=[])
        except Exception:
            pass
        
        sd = ScoredDataGroup()
        sd.tokens = []; sd.masks = []; sd.rewards = []; sd.prompts = []; sd.texts = []
        return sd

    async def collect_trajectories(self, item: Dict) -> ScoredDataGroup:
        """
        Phase 1 & 2: Generation AND Scoring.
        """
        if not hasattr(self, "server") or self.server is None:
            raise RuntimeError("NOCEnv: No server object available. Ensure Atropos injects the server.")

        question = item['question']
        target = item['answer']
        
        prompt = (
            f"Question: {question}\n"
            "Please think step by step to find the answer.\n"
            "Response:"
        )

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

        texts = self._normalize_rollouts(rollouts)
        
        group_data = {
            "item": item,
            "prompt": prompt,
            "rollouts": rollouts, 
            "texts": texts,       
            "ground_truth": target
        }
        
        return await self.score(group_data)

    async def score(self, group_data: Any) -> ScoredDataGroup:
        """
        Phase 2: Evaluation.
        """
        target = group_data['ground_truth']
        texts = group_data['texts']
        prompt = group_data['prompt']
        
        scored_data = self._make_scored_group()

        # --- 1. Calculate Batch Statistics ---
        correctness_vector = []
        for text in texts:
            is_correct = 1.0 if target.strip() in text else 0.0
            correctness_vector.append(is_correct)
            
        if not correctness_vector:
            batch_accel_proxy = 0.0
        else:
            batch_accel_proxy = np.var(correctness_vector)

        # --- 2. Scoring & Manual Tokenization ---
        for i, text in enumerate(texts):
            u_val = correctness_vector[i] if i < len(correctness_vector) else 0.0
            cost_j = len(text) * self.config.zeta
            
            synergy_val = await self._calculate_synergy(prompt, text, target)
            
            reward = (self.config.alpha * u_val) + \
                     (self.config.beta_meta * batch_accel_proxy) + \
                     (self.config.gamma * synergy_val) - \
                     cost_j
            
            conversation = [
                {"role": "user", "content": prompt},
                {"role": "assistant", "content": text}
            ]
            
            try:
                if getattr(self.tokenizer, 'chat_template', None):
                    formatted_text = self.tokenizer.apply_chat_template(
                        conversation, 
                        tokenize=False, 
                        add_generation_prompt=False
                    )
                else:
                    formatted_text = f"{prompt}\n{text}"

                # Robust Tokenization
                encoding = self.tokenizer(
                    formatted_text,
                    truncation=True,
                    max_length=self.config.max_token_length,
                    padding=False, 
                    return_tensors=None,
                    return_attention_mask=True
                )
                
                # Flatten & Safely Extract
                tokens = encoding.get('input_ids', encoding)
                if isinstance(tokens, list) and len(tokens) > 0 and isinstance(tokens[0], list):
                     tokens = tokens[0]
                
                mask = encoding.get('attention_mask', None)
                if mask is None:
                    mask = [1] * len(tokens)
                elif isinstance(mask, list) and len(mask) > 0 and isinstance(mask[0], list):
                    mask = mask[0]
                
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
            def format_request(conversation):
                if getattr(self.tokenizer, 'chat_template', None):
                    return self.tokenizer.apply_chat_template(
                        conversation, 
                        tokenize=False, 
                        add_generation_prompt=False
                    )
                else:
                    return "\n".join([msg['content'] for msg in conversation])

            base_conv = [
                {"role": "user", "content": prompt},
                {"role": "assistant", "content": f"Answer: {target}"}
            ]
            base_req = format_request(base_conv)
            base_logprob = await self._fetch_sequence_logprob(base_req, target)
            
            help_conv = [
                {"role": "user", "content": prompt},
                {"role": "assistant", "content": f"{generated_thought}\nAnswer: {target}"}
            ]
            help_req = format_request(help_conv)
            help_logprob = await self._fetch_sequence_logprob(help_req, target)
            
            return max(help_logprob - base_logprob, -5.0) 
        except Exception as e:
            logging.warning(f"Synergy calc failed: {e}")
            return 0.0

    async def _fetch_sequence_logprob(self, full_text: str, target_suffix: str) -> float:
        """
        Extracts log-probability using Completions API.
        """
        try:
            if hasattr(self.server, 'managed_server'):
                async with self.server.managed_server(self.tokenizer) as managed:
                    # FIX: Guard against missing client/completions
                    if hasattr(managed, 'client') and hasattr(managed.client, 'completions'):
                        response = await managed.client.completions.create(
                            model=self.config.model_name, 
                            prompt=full_text,
                            max_tokens=0, 
                            logprobs=1, 
                            echo=True, 
                            temperature=0.0
                        )
                    else:
                         return 0.0
            else:
                return 0.0
            
            if not response or not response.choices: return 0.0
            
            choice = response.choices[0]
            if not hasattr(choice, 'logprobs') or not choice.logprobs: return 0.0
            
            logprobs_data = choice.logprobs
            tokens = logprobs_data.tokens
            token_logprobs = logprobs_data.token_logprobs
            
            target_clean = target_suffix.strip().lower()
            lookback_limit = min(len(tokens), 50) 
            
            # Enhanced Decoding Strategy
            try:
                # Try to decode suffix to string if tokenizer allows
                suffix_tokens = tokens[-lookback_limit:]
                if hasattr(self.tokenizer, "decode") and all(isinstance(t, int) for t in suffix_tokens):
                    decoded_suffix = self.tokenizer.decode(suffix_tokens)
                else:
                    # Fallback: join token strings
                    decoded_suffix = "".join(map(str, suffix_tokens)).lower()
            except:
                decoded_suffix = "".join(map(str, tokens[-lookback_limit:])).lower()
            
            if target_clean in decoded_suffix:
                # Approximate: sum last N logprobs
                accumulated_logprob = sum(v for v in token_logprobs[-lookback_limit:] if v is not None)
                return accumulated_logprob
            
            return 0.0
            
        except Exception as e:
            return 0.0