# Instructions for AI Agents

Welcome, Agent. This repository is optimized for your efficient interaction.

## 1. Immediate Context
**Read `context.json` first.**
This JSON file contains the machine-readable map of the project structure, toolchain versions, and key file locations. It is your source of truth.

## 2. Critical Documentation
Before attempting any task, you should be aware of:
*   **`GLOSSARY.md`**: Defines the domain-specific mathematical symbols (`β`, `ΔU`, `Ξ_loss`) used in the code.
*   **`MATH_INDEX.md`**: Contains the Dependency Graph and Module Map. Use this to understand import hierarchies.
*   **`NOC/DEVELOPER_GUIDE.md`**: Explains the coding conventions and the meaning of `sorry` stubs (e.g., `EMPIRICAL` vs `TODO`).

## 3. Verified Workflows
Use these scripts to ensure safety and correctness:

*   **Verification:** `lake build` (Full build) or `./scripts/smoke_test.sh` (Fast wiring check).
*   **Debugging:** Use `lake build | python3 scripts/parse_lake_log.py` to get JSON-formatted error logs.
*   **Status Check:** Use `./scripts/verify_proofs.py` to see a summary of proved vs. incomplete theorems.
*   **Experimentation:** Always use the `Scratch/` directory for temporary code. Do not pollute `NOC/` with failed experiments.

## 4. Safety Constraints
*   **Dependency Lock:** Do NOT modify `lake-manifest.json` or `lean-toolchain`. The project is pinned to specific versions to avoid dependency hell.
*   **Stub Compliance:** Respect the `sorry` patterns defined in the Developer Guide. Do not attempt to prove empirical premises.
