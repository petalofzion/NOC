# TODO — Next Formalization Steps

- [ ] **Lemma D / β-stability proof** (`NOC_ROOT/NOC/D/BetaStability.lean`)
  - Formalize TTSA hypotheses (step-size schedules, regularization term, stability conditions).
  - Connect the conclusion to Lemma B’s acceleration result and expose the exact lemma signature used in the doc.
  - Add any supporting lemmas (e.g., gradient cross-correlation bounds) required for the proof.

- [ ] **Lemma E / directed-information version** (`NOC_ROOT/NOC/E/Core.lean`)
  - Define the finite POMDP model, synergy predicate, and directed-information computation helpers.
  - Prove the ablation lemma: synergy predicate ⇒ DI drop ⇒ empowerment drop.
  - Provide a small enumerated example (matching E-0b) that instantiates the lemma.

- [ ] **Supplementary examples/tests**
  - Optionally add an `NOC_ROOT/NOC/E/Examples` module that demonstrates the DI calculation on the finite toy model.
  - Extend existing tests or smoke-checks to cover the new Lemma D/E proofs once implemented.

- [ ] **Documentation sync**
  - After Lemma D/E land in Lean, update `docs/README-companion.md` and the ChangeLog to reflect the completed proofs.
