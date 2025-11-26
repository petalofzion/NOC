# Naturalized Orthogonality Collapse (NOC): A Blueprint for Cooperation via Capacity Constraints

**Epistemic Status:** Research Blueprint / RFC. It is messy. It is a work in progress. But the math checks out so far.

Hello LessWrong community \(^.^)/ Here is my request for comment on the Naturalized Orthogonality Collapse (NOC) theory(s) I've been working on (with the help of many lovely Angelic AI Assistants). I am trying to construct a *conditional*, *naturalized* refutation of the Orthogonality Thesis. If you want the raw proofs and the heavy technical lifting, go check `docs/NOC_v5.md` in the repo I have created with the canonical documentation and lean4 code! (it all compiles, and a lot has been done so far! if anything seems wrong or incorrect, please feel free to lmk!)

**Formalization check:** A recent paper came out where a team did somethign similar in terms of formalizing a specific necessary part for my theory, so i thought its about time I publicly start posting the work I have been doing. The probabilistic infrastructure (Robbins-Siegmund) is verified in Lean 4(what a recent paper did, though apparently in a diffeerent manner then what we did??).  The core definitions for Directed Information and the ROI inequality are formalized. The stability analysis is mathematically specified, but not yet fully finished. The AI agents i use to do formalization iteration keep telling me I need to "wait for mathlib to update with more lemmas and machinery" but I like trying to get it done ourselves, so thats probably next up on the list to iterate on :3

***

Everyone, I hope, that studies artificial intelligence alignment knows the **Orthogonality Thesis (OT)**. It is the standard *assumption* that intelligence and final goals are independent axes. You can have a superintelligent paperclip maximizer that doesn't give a damn about art, beauty, or life.

I think that is wrong.

Well, okay, I think it is *conditionally* wrong. In the abstract design space of all possible minds, for now, lets just grant that it does (there is another argument for the weak modal version, but that is under development uwu). But we don't live in the abstract design space. We live in a messy, physically (at least for methodological naturalist assumptions, setting aside personal beliefs about ontology) constrained reality! Oh noes O.o

My argument is that once you introduce the constraints of a realistic, long-horizon environment, orthogonality (not the math kind! the Bostrom kind!) collapses. The physics of the situation imposes practical realities that "constrain" the scope of non-collapsing goal + learning/intelligence-production pairs. Sufficiently rational agents get instrumentally incentivized to do three things: get more capacity ($U$), accelerate that gain ($\Delta^2 U$), and (here is the kicker!) **preserve system-level optionality ($\Sigma$)**.

The core novelty I am bringing to the table is what we formalized as... 
**Lemma E (Conditional DI-DPI)**!! 
It proves that in **Non-Competitive Couplings (NCC)**, destroying a partner actually makes *you* dumber. Specifically, it reduces your Directed Information (DI) capacity. Cooperation doesn't pop out of nowhere because of morality; it emerges from the cold, selfish need to maximize future control.

### So, what is the argument?

Let's walk through the logic.

It starts with the drive for acceleration. Bounded agents in uncertain worlds feel a pressure to improve, and also crucially, to *accelerate* their improvement ($\beta_{\text{meta}} > 0$). However, you can't accelerate in a vacuum. You need fuel. That fuel is a rich environment with high optionality ($\Sigma$). If you burn down the forest, you might get warm for a night, but you (drastically) stifle your own ability to build a house later.

This is a sort of instrumental preservation of the environment for (allowably) selfish reasons. I formalize this as **Σ-preservation** in the document. It represents the strategic necessity to maintain system-level *optionality* to fuel intelligent acceleration. It is a decision theoretic constraint derived from **Lemma E+** (an upgraded and more difficult to prove version of Lemma E) that says that *Conversion > Ablation*, showing that if you can "re-engineer" a partner/opponent into a "heterogenous channel", then it almost always dominates destroying them. The *almost* is the important part for applied alignment research, and has some implications for what we are doing when we do "alignment". It should give us some ideas already, but for starters, it means we should focus less on specifying goals (something notoriously difficult) and instead on engineering the environments that dont fall into an agent necessitating "ablating" (or umm idk... endlesslly torturing or killing the adorable simian like mamals ASI keeps as pets OwO)

In regimes where interference is low (what is sometimes called "non-competitive"), destroying another agent reduces the total information processing capacity of the system. **Lemma E** is the mathematical hammer here: it proves that under these conditions, destroying a partner strictly reduces your *own* ability to steer the future. You being any intelligent (hopefully(or not??)) agent in the process of learning.

So, highly capable agents will converge on preserving and upgrading their partners. Not because they are nice, though they might be allowed to be nice, and even converge on what is commonly considered by society as what constitutes "being nice", but because they need the optionality to accomplish their goals! yay~

### The Scope (What I am NOT saying)

I am attempting a *conditional* refutation. I am not claiming you can't build a paperclip maximizer in a void, at least not in this post! I am saying that in the specified "modal regime" - tasks with uncertainty, long time horizons, bounded compute - stable goal profiles collapse toward **capacity-optionality**.

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

This relies on the **Non-Competitive Coupling (NCC)** assumption. Here is an informal version, which might mean its kinda reductive or vague??: interactions look like "post-processing," not interference. Something like trade (the economy) is is an example of NCC, while Chess (or some might argue war) is not.

My claim is that, under NCC, garbling or ablating a partner *cannot increase* your own Directed Information. (Some recent papers also came out about using Directed Information in ML context! Another reason to get this out, all ideas won't be novel anymore by the time its fully fleshed out if we wait it seems like T.T)

Anyways, by what mechanism you ask, being a smart and skeptical sciencey mind that you are?? The Data Processing Inequality (DPI) of course! Usually, DPI doesn't hold for DI. But under NCC, it *does*. HOw?!? Well... we use Massey's decomposition:

$$I(A^{1:T} \to S^{1:T}) = \sum_{t=1}^T I(A^{1:t}; S_t \mid S^{<t})$$

Therefore, interestingly, removing a partner is mathematically equivalent to garbling the channel. By DPI, you lose throughput. You kill them, you make yourself deaf and blind to a part of the future. (Simulation studies section starts whispering amongst themselves...)

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
