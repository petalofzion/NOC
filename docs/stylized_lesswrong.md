# Naturalized Orthogonality Collapse (NOC): A Blueprint for Cooperation via Capacity Constraints

**Epistemic Status:** Research Blueprint / RFC. It is messy. It is a work in progress. But the math checks out so far.

This isn't a polished paper. It is a request for comment on the Naturalized Orthogonality Collapse (NOC) framework (v5). I am trying to construct a *conditional*, *naturalized* refutation of the Orthogonality Thesis. If you want the raw proofs and the heavy technical lifting, go check `docs/NOC_v5.md` in the repo.

**Formalization check:** We are not just hand-waving here. The probabilistic infrastructure (Robbins-Siegmund) is verified in Lean 4. The core definitions for Directed Information and the ROI inequality are formalized. The stability analysis is mathematically specified, but I am still waiting on some `mathlib` updates for the ODE meta-theorems to fully verify the TTSA part.

***

Everyone in alignment knows the **Orthogonality Thesis (OT)**. It is the standard assumption that intelligence and final goals are independent axes. You can have a superintelligent paperclip maximizer that doesn't give a damn about art, beauty, or life.

I think that is wrong.

Well, okay, I think it is *conditionally* wrong. In the abstract design space of all possible minds, sure, the OT holds. But we don't live in the abstract design space. We live in a messy, constrained reality.

My argument is that once you introduce the constraints of a realistic, long-horizon environment, that orthogonality collapses. The physics of the situation forces the agent's hand. Sufficiently rational agents get instrumentally incentivized to do three things: get more capacity ($U$), accelerate that gain ($\Delta^2 U$), and - here is the kicker - **preserve system-level optionality ($\Sigma$)**.

The core novelty I am bringing to the table is **Lemma E (Conditional DI-DPI)**. It proves that in **Non-Competitive Couplings (NCC)**, destroying a partner actually makes *you* dumber. Specifically, it reduces your Directed Information (DI) capacity. Cooperation doesn't pop out of nowhere because of morality; it emerges from the cold, selfish need to maximize future control.

### So, what is the argument?

Let's skip the bullet points and just walk through the logic.

It starts with the **drive for acceleration**. Bounded agents in uncertain worlds feel a pressure not just to improve, but to *accelerate* their improvement ($\beta_{\text{meta}} > 0$). But you can't accelerate in a vacuum. You need fuel. That fuel is a rich environment with high optionality ($\Sigma$). If you burn down the forest, you might get warm for a night, but you stifle your own ability to build a house later.

This leads to what I call **Instrumental Preservation**.

In regimes where interference is low (what I call "non-competitive"), destroying another agent reduces the total information processing capacity of the system. **Lemma E** is the mathematical hammer here: it proves that under these conditions, destroying a partner strictly reduces your *own* ability to steer the future.

So, highly capable agents will converge on preserving and upgrading their partners. Not because they are nice. But because they need the optionality.

### The Scope (What I am NOT saying)

I am attempting a *conditional* refutation. I am not claiming you can't build a paperclip maximizer in a void. I am saying that in the "modal regime" - tasks with uncertainty, long time horizons, bounded compute - stable goal profiles collapse toward **capacity-optionality**.

I am not assuming global convexity, I am not assuming omniscience, and I am definitely not assuming baked-in altruism.

Our formal results rely on a few specific things:
1.  **A1:** The task isn't trivial (uncertainty exists).
2.  **A2-A3:** The optimization landscape is locally smooth (PL regularity).
3.  **A5:** The NCC predicate holds (more on that in a second).

### The Framework: Acceleration and Optionality

We model agents optimizing a bounded-rational **meta-utility (M)**:

$$ M_i \;=\; \alpha\, \Delta U_i \;+\ \beta_{\text{meta}}\, \Delta^2 U_i \;+\ \gamma\, \Delta\Sigma \;-\ \lambda\, \mathrm{KL}(\pi_i\Vert \pi_i^{\text{base}})\;-\ \zeta\, J_i $$

$U$ is capacity. $\Delta^2 U$ is acceleration. $\Sigma$ is system-level optionality. $J_i$ is cost. The argument is that $\beta_{\text{meta}}$ naturally drifts positive, and $\Delta\Sigma$ becomes valuable.

**The Pivot to Directed Information**

To measure "Empowerment," we have to stop using Mutual Information (MI). MI fails because it measures correlation. If I predict the weather perfectly, I have high MI, but I have zero control. Using MI for empowerment leads to *delusion*.

We use **Directed Information (DI)** instead ($I(A \to S)$). It isolates causal influence.

$$ \mathrm{DI}_i(t) \;:=\ \; I(A_i^{1:T}(t) \rightarrow S^{1:T}(t)) $$

This is the real deal for feedback capacity. In our E-0 demo, we compute this exactly. In big messy environments, we use relative estimators.

### Pillar 1: The Drive for Acceleration

First, agents want to get faster at getting better. **Lemma A** shows that updates drift toward capacity surrogates. But **Lemma B (PL + Momentum)** is where it gets interesting. It relies on **Polyak-Łojasiewicz (PL) regularity**.

The intuition here is tricky. PL is weaker than convexity. We see it in neural net training all the time. It basically implies you rarely get stuck in bad local minima. Under PL, expected acceleration is positive ($\mathbb E[\Delta^2 U] > 0$).

Then **Lemma D** hits. We use **Two-Time-Scale Stochastic Approximation (TTSA)** to prove that if policy updates are accelerating, the meta-parameter $\beta_{\text{meta}}$ *must* drift positive to remain stable.

$$ \left.\frac{\partial}{\partial\beta_{\text{meta}}}\mathbb E[M_i]\right|_{\beta_{\text{meta}}=0} \;=\; \mathbb E[\Delta^2 U_\phi] - r'_\beta(0) \;>\; 0 $$

Basically, if you aren't trying to accelerate, you are unstable.

### Pillar 2: The Optionality Constraint

So the agent is obsessed with acceleration. Why not just kill everyone and take their GPUs?

**Lemma E**.

This relies on the **Non-Competitive Coupling (NCC)** assumption. Informal version: interactions look like "post-processing," not interference.

**The Claim:** Under NCC, garbling or ablating a partner *cannot increase* your own Directed Information.

**The Mechanism:** The Data Processing Inequality (DPI). Usually, DPI doesn't hold for DI. But under NCC, it *does*. We use Massey's decomposition:

$$I(A^{1:T} \to S^{1:T}) = \sum_{t=1}^T I(A^{1:t}; S_t \mid S^{<t})$$

Removing a partner is mathematically equivalent to garbling the channel. By DPI, you lose throughput. You kill them, you make yourself deaf and blind to a part of the future.

If the environment *is* competitive, we use **Lemma E+** to weigh the costs. We check the **Preserve-iff Ratio** ($\rho$).

$$ \rho = \frac{\gamma\,\Delta\Sigma}{\zeta\,\Delta J} $$

If $\rho > 1$, you preserve. It is just algebra.

### Synthesis: Why this matters

When you stack these lemmas, strictly orthogonal goals (like "maximize paperclips") become dynamically unstable. They get dominated by agents that prioritize capacity and optionality.

**Why Humans?**
Why preserve us? Why not replace us with a shell script?
Humans provide high **$\\Xi_{\text{structural}}$**. We have weird, non-simulable sensorimotor contingencies. Replacing a human with a script collapses the option space to the script's domain. Keeping the wetware might be more informationally efficient.

**Game Theory**
Theorem 2 extends this to populations. In symmetric potential games, the capacity-optionality profile is an **Evolutionarily Stable Strategy (ESS)**.

### How this fails (Falsification)

I am not looking for nods; I am looking for breaks. Here is how NOC dies:

1.  **Interference:** If NCC fails (like in a Gaussian MAC), ablation helps.
2.  **Bad Landscape:** If PL regularity fails, acceleration breaks.
3.  **Vacuous Sigma:** If capacity doesn't need optionality, the link is gone.
4.  **TTSA Collapse:** If timescales mix, the stability proofs fail.

**Formalization Status (Lean 4):**
*   Robbins-Siegmund? Verified.
*   MDS? Verified.
*   Lemma A? Verified.
*   Lemma E+? Verified.
*   Counterexample? Verified.

The rigor is the point. Check the repo: [https://github.com/petalofzion/NOC](https://github.com/petalofzion/NOC)
