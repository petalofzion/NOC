# Instructions for AI Agents

Welcome, Agent. This repository is optimized for your efficient interaction.

## 0. Core Directive: Deep Formalization
**Target: Option C (Full Formal Verification).**
This repository aims for **rigorous, research-grade mathematical formalization** of all claims.
- **Do not stop at assumptions.** Minimizing axioms is the goal.
- **Do not rely on "Empirical" excuses.** If a claim requires Probability Theory, Information Geometry, or ODE Convergence, **formalize the underlying theory**.
- **Ignore "Complexity" Warnings.** We have proven that this workflow can solve "month-long" mathlib gaps in days. If a foundation (like Directed Information or TTSA) is missing, build it from first principles.
- **Parallel Tracks:** We maintain the mapping to experiments (Track 2) for validation, but the Lean code (Track 1) must stand alone as a complete mathematical edifice.

## 1. Immediate Context
**Read `context.json` first.**
This JSON file contains the machine-readable map of the project structure, toolchain versions, and key file locations. It is your source of truth.

## 2. Critical Documentation
Before attempting any task, you should be aware of:
*   **`GLOSSARY.md`**: Defines the domain-specific mathematical symbols (`β`, `ΔU`, `Ξ_loss`) used in the code.
*   **`MATH_INDEX.md`**: Contains the Dependency Graph and Module Map. Use this to understand import hierarchies.
*   **`NOC/DEVELOPER_GUIDE.md`**: Explains the coding conventions and the meaning of `sorry` stubs.

## 3. Verified Workflows
Use these scripts to ensure safety and correctness:

*   **Verification:** `lake build` (Full build) or `./scripts/smoke_test.sh` (Fast wiring check).
*   **Debugging:** Use `lake build | python3 scripts/parse_lake_log.py` to get JSON-formatted error logs.
*   **Status Check:** Use `./scripts/verify_proofs.py` to see a summary of proved vs. incomplete theorems.
*   **Experimentation:** Always use the `Scratch/` directory for temporary code. Do not pollute `NOC/` with failed experiments.

## 4. Safety Constraints
*   **Dependency Lock:** Do NOT modify `lake-manifest.json` or `lean-toolchain`. The project is pinned to specific versions to avoid dependency hell.
*   **Deep Proof Over Scaffolding:** While we maintain empirical interfaces, the default action for any `sorry` or axiom is to **eliminate it via deep formalization**. Do not leave "empirical" stubs unless they represent raw data inputs (like specific dataset values) that cannot be derived mathematically.

## 5. Version Control Protocol
*   **No Auto-Reverts:** Do **NOT** use `git checkout`, `git reset`, or `git revert` to undo changes unless explicitly instructed by the user.
*   **Forward Fixes Only:** If a build breaks, fix the code forward (by editing the file). Do not roll back to a previous commit state, as this may destroy uncommitted work in the user's local environment.
*   **Commit Discipline:** Do not commit or push changes without explicit user approval.