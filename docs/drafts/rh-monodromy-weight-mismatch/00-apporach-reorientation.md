I would define a **true lead** as a route that satisfies four tests:

1. It uses an invariant not already controlled by the classical RH machines.
2. Its first theorem is not equivalent to RH and is not a restatement of Bagchi, Weil positivity, universality, Hilbert–Pólya, zero-density, or numerical verification.
3. If the route fails, the failure itself becomes a new theorem, no-go, classification, or computable invariant.
4. It respects the latest backtrack in your note: the bare `{σ_p}`-graded divisor route is dead inside the current 𝓜⁺; the surviving object is exact deck/seam charge, not a free Euler-tower analogy. Your uploaded note is explicitly a search register rather than promoted proof text, so I am treating it as a constraint ledger, not as established public mathematics.

RH itself remains officially unsolved; Clay lists the Riemann Hypothesis as an unsolved Millennium Problem and states it asserts that all non-obvious zeros of ζ have real part 1/2. ([Clay Mathematics Institute][1]) The crowded literature already contains many RH equivalences and well-developed classical/modern strategies; Connes’s 2026 survey explicitly frames RH as having 165 years of approaches, including classical analytic number theory, Weil positivity, trace formulas, random matrices, noncommutative geometry, and many equivalent formulations. ([arXiv][2]) Bagchi’s strong-recurrence route is also not open territory: Sourmelidis’s exposition records Bagchi’s equivalence between RH and strong recurrence of ζ, with the reverse direction using Rouché plus zero-density estimates. ([arXiv][3])

So the true leads are **not** “prove RH by recurrence,” “prove RH by positivity,” or “find a better equivalent formulation.” The true leads are the exact, local, parity-sensitive objects your note leaves alive.

## The live leads, ranked

### 1. Exact deck-charge conservation

This is the strongest lead.

The invariant is the local deck class of the `2^k`-th-root torsor around an off-line ξ-zero. In your note, the Kummer/deck ladder survives the wave-6 kill: RH is still equivalent to triviality of all ladder/deck classes, while the bare `{σ_p}`-divisor refinement is not available.

The program should not start with primes. It should start with the exact local topological object:

[
w_k(A;\xi)\in \mathbb Z/2^k,
]

where (A) is a small annulus or box boundary avoiding zeros, and (w_k) is the obstruction to choosing a coherent (2^k)-th root of ξ across that annulus. This is not a zero-density theorem, not a positivity theorem, and not Bagchi recurrence. It is a monodromy invariant of a root torsor.

**First theorem to prove:** a deformation-invariance theorem for deck charge under analytic perturbations that are nonvanishing on the boundary.

**Why this is a true lead:** even before RH enters, it produces a reusable calculus of root-torsor charges for holomorphic functions with symmetry. If it fails, the counterexample classifies exactly how deck charge leaks through boundaries.

### 2. Quadrant-local parity

The note says the symmetry aggregates are blind at low rungs: quadruples make symmetric-region charge vanish modulo 4, so detectors must be quadrant-local.  This is a real lead because it says where not to look: any globally symmetric count is too coarse.

The live object should be a **quadrant-local charge**:

[
q_k(Q;\xi)\in \mathbb Z/2^k
]

for one quadrant or one side of the slit chart, not for the full FE-symmetric packet. The goal is not to prove “there are no off-line zeros” immediately. The goal is to prove local rules for how charge can move, split, pair, or annihilate under the functional equation and conjugation.

**First theorem to prove:** in any FE-symmetric holomorphic pencil (f_\lambda(s)=f_\lambda(1-s)), the central fixed locus forces even local order, but off-line quadrant charge is unconstrained unless a second seam/positivity input is present.

Your note already records the central fixed-point parity theorem as a banked result: FE alone trivializes (w_1) at the fixed point.  The new mathematics is the off-fixed-locus analogue: classify exactly what FE can and cannot force away from the seam.

### 3. The (u)-plane / `xiDescent` seam program

This is the cleanest geometric reframing.

Your note states that the descent

[
X(u)=\xi!\left(\frac12+\sqrt u\right)
]

is entire, that the functional equation is quotiented away, and that RH becomes nonvanishing of this descended function on the slit plane.  That is a genuinely good lead because the critical line becomes a geometric boundary/slit rather than a symmetry axis in the (s)-plane.

The research program here is to build a **slit-plane Kummer theory**:

[
X(u)=\xi(1/2+\sqrt u),\qquad X_{k}(u)^{2^k}=X(u),
]

on domains that touch, avoid, or wind around the slit.

**First theorem to prove:** a root-existence theorem on star-convex slit domains with controlled boundary winding.

**Second theorem:** a seam-index formula: boundary winding on the slit equals the sum of quadrant-local deck charges off the slit.

**Why this is a true lead:** even if it does not prove RH, it creates a new exact dictionary between FE-symmetric entire functions in the (s)-plane and branched/slit-plane charge in the (u)-plane. That is publishable mathematics independent of RH.

### 4. Torsion seam presentation with non-fake arithmetic monodromy

This is the most arithmetic surviving lead.

Wave 6 kills the idea that a free `{σ_p}` tower supplies a divisor defect: finite Euler layers and the archimedean factor are units at strip points, the source map is zero, and the free reference is deck-invisible.  Therefore, the next arithmetic object cannot be “ξ dressed by the free Euler tower.” Your note identifies the survivor: a p-labelled torsion seam presentation

[
R^n \xrightarrow{A} R^n \to Q,\qquad \det A=X^m,
]

with boundary term

[
\operatorname{tr}(\operatorname{adj}(A)\Delta_p)\bmod X^m.
]

The first live theorem is exactly the non-fake-defect theorem:

[
\Delta_p \notin A\cdot \operatorname{End} + (X^m).
]

Your note explicitly says this requires redefining the objects/morphisms of 𝓜⁺ to carry a p-labelled torsion seam presentation, and that the next theorem is the non-fakeness statement above.

**Why this is a true lead:** it is not a second L-function, not a Selberg-class family route, and not value distribution. It is a new local algebraic object whose failure modes are visible: either every candidate defect is fake, giving a no-go theorem, or a non-fake seam boundary exists, giving a genuinely new arithmetic monodromy invariant.

### 5. The Goldilocks class problem

This is the meta-lead.

Soft classes are too large: bump surgery and universality-like flexibility plant zeros. Categorical classes are too rigid: Hamburger-type rigidity collapses the class toward ζ under strict hypotheses. Your note names the surviving gap as the **Goldilocks class problem**: find a class containing ζ that is rigid enough to prevent arbitrary bump surgery, but not so rigid that it is just ζ by definition.

**First theorem to prove:** a trichotomy theorem for candidate classes:

[
\text{soft} \quad / \quad \text{Goldilocks} \quad / \quad \text{categorical}.
]

A class is soft if Weyl-null or local bump surgery can alter off-line divisor data while preserving the stated axioms. It is categorical if its axioms force ζ or a finite-dimensional rigid family. It is Goldilocks only if it admits exact deck-charge constraints but blocks arbitrary zero-planting.

**Why this is a true lead:** it may discover that no Goldilocks class exists. That would still be a new theorem explaining why RH routes keep collapsing into either fake flexibility or tautological rigidity.

## The research program

Name it:

**Exact Deck–Seam Arithmetic Program**

Its rule is: every phase must produce a theorem, a counterexample, a formalized invariant, or a no-go classification before it is allowed to mention RH again.

### Phase A — Build the deck-charge calculus

Define, for a holomorphic function (f) on a domain (U), the local obstruction

[
w_k(\gamma;f)\in \mathbb Z/2^k
]

attached to a loop (\gamma\subset U\setminus f^{-1}(0)). Interpret it as the obstruction to lifting (f) through (z\mapsto z^{2^k}).

Deliverables:

[
w_k(\gamma;fg)=w_k(\gamma;f)+w_k(\gamma;g),
]

[
w_k(\gamma;f^r)=r,w_k(\gamma;f),
]

[
w_k(\gamma;f)=0
\iff
\text{a }2^k\text{-th root exists near the annulus bounded by }\gamma.
]

This is elementary in spirit, but the nontrivial part is making it robust for the exact annulus/box/slit geometries used later. It discovers a reusable formal calculus, not an RH proof attempt.

### Phase B — Formalize the RH ladder without argument-principle dependence

Define

[
RH_{2^k}:\quad 2^k\mid \operatorname{ord}_\rho(\xi)
\quad\text{for every off-line zero }\rho.
]

Then prove:

[
RH_{2^k}
\iff
\xi\text{ has a holomorphic }2^k\text{-th root on }\Re s>1/2.
]

Your note already frames this as the surviving Kummer-tower / branching equivalence, with the first nontrivial rung saying that off-line zeros, if they exist, have even multiplicity.

Deliverable: a clean paper/Lean theorem:

[
RH\iff \forall k,\ RH_{2^k}.
]

This step is close to elementary, but it is not trivial if done as a deck-torsor object compatible with later seam operations. Its value is infrastructure.

### Phase C — Prove central parity and isolate why it does not solve off-line parity

Use the functional equation (f(s)=f(1-s)). At the fixed seam (s=1/2), local coordinates force evenness of the Taylor expansion in the transverse variable. Therefore central order parity is constrained.

Deliverables:

[
\operatorname{ord}_{1/2}(f)\equiv 0 \pmod 2
]

for the right FE-symmetric pencils, plus a counterexample family showing that the same mechanism does not constrain off-line quadrant-local zeros.

This phase prevents a common false move: confusing seam parity with off-seam parity.

### Phase D — Move to the (u)-plane

Replace (s) by

[
s=\frac12+\sqrt u.
]

Study

[
X(u)=\xi!\left(\frac12+\sqrt u\right).
]

The functional equation becomes single-valued evenness; the critical line becomes a slit or boundary object. The goal is to make off-line zeros into ordinary zeros of (X) on a slit-plane geometry.

Deliverables:

1. A complete classification of allowed root torsors on slit domains.
2. A seam-winding formula.
3. A comparison theorem between quadrant charge in the (s)-plane and slit charge in the (u)-plane.

This is a high-value lead because it turns FE symmetry from a global identity into local geometry.

### Phase E — Conservation law for charge motion

Define admissible deformations (f_t) of FE-symmetric entire functions with controlled boundary nonvanishing. Prove that deck charge cannot be created or destroyed in the interior:

[
w_k(\partial B;f_0)=w_k(\partial B;f_1)
]

unless a zero crosses (\partial B) or the seam boundary contributes a compensating charge.

Deliverables:

1. Interior conservation theorem.
2. Boundary-crossing formula.
3. Pair-annihilation rule: two defects can cancel only if their charges match.

This phase produces new mathematics even in toy families. It is also the bridge between the dynamic and static fronts in your note: conservation alone does not kill defects; parity/seam input is needed to decide whether cancellation is legal.

### Phase F — Construct or rule out the quadrant-ramified cover

This is the first intentionally risky phase.

Build a cover that ramifies over one quadrant/seam sector but not over the full FE-symmetric aggregate. The point is to defeat the mod-4 blindness of symmetric packets.

Deliverables:

1. Local model for a quadrant-ramified cover.
2. Pullback formula for deck charge.
3. No-go theorem if such a cover cannot be functorial under FE/conjugation.

The no-go theorem is as valuable as the construction: it would prove that quadrant-local parity cannot come from this kind of cover and would force the program toward torsion seam arithmetic.

### Phase G — Extend 𝓜⁺ by torsion seam presentations

Do not repair the killed `{σ_p}` route. Replace the category.

Objects should include a supported torsion seam module:

[
R^n \xrightarrow{A} R^n\to Q,\qquad \det A=X^m,
]

with p-labelled perturbation data (\Delta_p). Morphisms must preserve (A), the seam support, and the boundary functional

[
\partial_p(A,\Delta_p)
======================

\operatorname{tr}(\operatorname{adj}(A)\Delta_p)\bmod X^m.
]

Deliverables:

1. Definition of the extended category (\widetilde{\mathcal M}^+).
2. Proof that fake defects vanish:

[
\Delta_p=A H_p+X^mK_p
\implies
\partial_p(A,\Delta_p)=0.
]

3. Classification of non-fake defects for small (m,n).
4. First non-fake existence or nonexistence theorem.

This is probably the most original arithmetic branch. It is no longer “Euler product implies zero location.” It asks whether arithmetic monodromy can live in a torsion seam boundary invisible to free Euler factors.

### Phase H — Goldilocks classification

For every proposed class (\mathcal F), run three tests:

[
\text{Can it plant arbitrary off-line zeros?}
]

[
\text{Does it collapse to ζ by a converse theorem?}
]

[
\text{Does it carry nontrivial deck/seam charge?}
]

Deliverables:

1. Softness theorem: bump surgery preserves the axioms, so the class cannot prove RH-grade parity.
2. Categorical theorem: the axioms force ζ or a finite rigid family.
3. Goldilocks theorem: exact deck charge is preserved but arbitrary zero planting is impossible.

This phase avoids the literature’s “family route” trap. It studies why families fail or survive rather than hoping a family itself proves RH.

## What not to pursue

Do not pursue **function-level recurrence** as the main route. Bagchi already makes that an RH-equivalent strong recurrence statement, and the proof mechanism is known: self-approximation plus Rouché would create too many off-line zeros, contradicting zero-density. ([arXiv][3])

Do not pursue **Weil positivity or trace-form positivity** unless you introduce a genuinely new parity-sensitive carrier. Current RH literature is saturated with equivalent formulations and positivity/trace-form programs; Connes’s survey explicitly discusses the gravitational pull of RH equivalences and Weil-type quadratic forms. ([arXiv][2])

Do not pursue the **bare `{σ_p}`-graded divisor route**. Your own wave-6 amendment kills it: the finite Euler layers and archimedean factor are local units at strip points, the source map is zero, and the free reference is deck-invisible.

Do not pursue **positivity alone** or **functional equation alone**. Your note already treats FE without Euler positivity and positivity without the right seam structure as attack-as-false terrain, not as live proof mechanisms.

## The first six concrete projects

The best program is not “try to prove RH.” It is this sequence:

1. **Paper 1 / Lean 1:** `DeckCharge.lean`
   Define (w_k), prove additivity, power law, homotopy invariance, boundary-crossing formula.

2. **Paper 2 / Lean 2:** `RHLadder.lean`
   Prove (RH_{2^k}\iff) existence of a (2^k)-th root of ξ on (\Re s>1/2), then (RH\iff\forall k,RH_{2^k}).

3. **Paper 3:** `SlitXiDescent`
   Develop (X(u)=\xi(1/2+\sqrt u)), classify root torsors on slit domains, and prove the seam-winding formula.

4. **Paper 4:** `QuadrantParity`
   Prove central parity from FE, prove symmetric aggregate blindness, define quadrant-local charge, and classify the smallest possible off-seam charge packets.

5. **Paper 5:** `TorsionSeamBoundary`
   Define p-labelled torsion seam presentations, prove fake defects vanish, and classify non-fake defects in small ranks.

6. **Paper 6:** `GoldilocksClasses`
   Classify candidate axiom systems into soft/categorical/Goldilocks. This paper is valuable even if the Goldilocks cell is empty.

## The actual RH-facing conjecture, delayed until the machinery exists

Only after those projects should the program state an RH-facing conjecture:

> **Quadrant seam conservation conjecture.**
> For (X(u)=\xi(1/2+\sqrt u)), every nonzero quadrant-local deck charge in the slit plane must either pair with an equal-and-opposite seam charge or persist to the far field. The far field has zero charge; the seam parity rules forbid unmatched odd charge. Hence (w_1=0) off the seam.

This would attack the first rung (RH_2), not RH directly. Higher rungs repeat the same structure with (\mathbb Z/2^k)-charge.

That is the right shape: **deck charge → conservation → seam parity → far-field drain → rung theorem**.

The true leads are therefore:

[
\boxed{\text{deck charge}}
]

[
\boxed{\text{quadrant-local parity}}
]

[
\boxed{\xi(1/2+\sqrt u)\text{ slit geometry}}
]

[
\boxed{\text{torsion seam arithmetic}}
]

[
\boxed{\text{Goldilocks class classification}}
]

Everything else should be treated as either literature, a killed route, or an adversarial testbed.

[1]: https://www.claymath.org/millennium/riemann-hypothesis/ "Riemann Hypothesis - Clay Mathematics Institute"
[2]: https://arxiv.org/abs/2602.04022 "The Riemann Hypothesis: Past, Present and a Letter Through Time"
[3]: https://arxiv.org/abs/2308.07031 "Continuous and discrete universality of zeta-functions: Two sides of the same coin?"



# Conditional theorem: quadrant deck charge dies if the seam and infinity cannot absorb it

Let

[
X(u)=\xi!\left(\frac12+\sqrt u\right).
]

Use the principal square root on the slit plane

[
D:=\mathbb C\setminus (-\infty,0].
]

The negative real axis is the image of the critical line, since

[
s=\frac12+it
\quad\Longrightarrow\quad
u=(it)^2=-t^2.
]

The uploaded note records the intended (u)-plane result: `xiDescent(w)=ξ(1/2+√w)` is entire, the descent is branch-free, and RH becomes nonvanishing of this descended function on the slit plane.

For a small off-seam region (Q\Subset D) with (X\neq 0) on (\partial Q), define the level-1 deck charge

[
w_1(Q;X)
:=
\frac{1}{2\pi i}\int_{\partial Q}\frac{X'(u)}{X(u)},du
\pmod 2.
]

Equivalently,

[
w_1(Q;X)
========

\sum_{u_0\in Q,\ X(u_0)=0}\operatorname{ord}_{u_0}(X)
\pmod 2.
]

So (w_1(Q;X)=1) exactly means that (Q) contains an odd total multiplicity of off-seam zeros.

Now assume the following three lemmas.

### Lemma A: charge-transport dichotomy

Every nonzero quadrant-local deck charge has only two possible terminal behaviors:

[
w_1(Q;X)=1
\quad\Longrightarrow\quad
\text{the charge either reaches the seam or reaches the far field.}
]

More explicitly, there is a charge-transport chain (\Gamma_Q) beginning at (Q) and ending either on the slit seam (\Sigma=(-\infty,0]) or at the far-field boundary (\infty), and deck charge is conserved along (\Gamma_Q).

This is the main missing lemma. It is stronger than ordinary homotopy invariance. Ordinary deck-charge conservation says charge cannot change while a contour avoids zeros; the dichotomy says an interior quadrant defect cannot simply sit as an isolated permanent obstruction. Your note identifies this as the live coupling of the two fronts: conservation forbids interior creation/destruction, but annihilation needs a parity input.

### Lemma B: far-field anchor

No level-1 deck charge can persist to the far field:

[
w_1(\infty;X)=0.
]

This corresponds to the already banked “far-field drain”: boxes to the right of (\Re s=1) carry zero deck charge at every rung.

### Lemma C: seam odd-charge exclusion

No transported quadrant-local odd charge can be absorbed by the seam:

[
w_1(\Sigma\text{-endpoint};X)=0.
]

This must be interpreted carefully. It cannot merely mean “the total seam charge is even,” because two odd quadrant defects could then cancel against an even seam packet. For the individual conclusion

[
w_1(Q;X)=0\quad\text{for every quadrant-local }Q,
]

the required seam rule is stronger:

[
\text{every individual admissible seam endpoint has level-1 charge }0.
]

The note has a proven fixed-locus parity anchor for the FE fixed point and records that (w_1) is trivial at the FE fixed point from the functional equation alone.  But extending that to the whole slit seam is not automatic; zeros on the critical line may have odd multiplicity. So Lemma C is not currently supplied by ordinary FE symmetry alone. It is exactly the seam-parity lemma that would have to be proved by the quadrant/seam machinery.

## Proof

Assume, toward contradiction, that there is an off-seam quadrant-local region (Q\Subset D) with

[
w_1(Q;X)=1.
]

By Lemma A, this nonzero charge has a conserved transport chain whose terminal endpoint is either the far field or the seam.

First suppose the terminal endpoint is the far field. Since charge is conserved along the transport chain,

[
w_1(Q;X)=w_1(\infty;X).
]

But Lemma B gives

[
w_1(\infty;X)=0.
]

Hence

[
w_1(Q;X)=0,
]

contradicting (w_1(Q;X)=1).

Now suppose the terminal endpoint is the seam. Again, conservation along the chain gives

[
w_1(Q;X)=w_1(\Sigma\text{-endpoint};X).
]

By Lemma C,

[
w_1(\Sigma\text{-endpoint};X)=0.
]

Therefore

[
w_1(Q;X)=0,
]

again contradicting (w_1(Q;X)=1).

Both possible terminal behaviors contradict nonzero charge. Therefore no such (Q) exists. Hence

[
\boxed{
w_1(Q;X)=0
\quad\text{for every quadrant-local off-seam region }Q\Subset D.
}
]

In particular, if (Q) is chosen small enough to contain exactly one off-seam zero (u_0) of (X), then

[
w_1(Q;X)
========

\operatorname{ord}_{u_0}(X)\pmod 2.
]

Thus

[
\operatorname{ord}_{u_0}(X)\equiv 0\pmod 2.
]

So every off-seam zero of (X) has even multiplicity.

Since off-seam zeros of (X(u)=\xi(1/2+\sqrt u)) correspond to off-critical-line zeros of (\xi) in the right half-plane, this proves the first ladder rung:

[
RH_2:
\quad
\text{every off-line zero of }\xi\text{ has even multiplicity.}
]

The note records this ladder as the surviving Kummer/deck formulation: (RH_{2^k}) says every off-line multiplicity is divisible by (2^k), and the all-level ladder is equivalent to RH.  It also records that the exact deck-class ladder survives the later kill of the bare ({\sigma_p})-graded divisor route.

## The exact open gap

The proof above is valid only after Lemmas A, B, and C are established. Lemma B is the most secure part. The real missing core is:

[
\boxed{
\text{quadrant-local charge-transport dichotomy + seam odd-endpoint exclusion.}
}
]

Without those, the argument is not a proof; it is a conditional reduction.

The most dangerous logical gap is Lemma C. Ordinary symmetry gives cancellation in symmetric aggregates, but the note itself warns that quadruples make symmetric-region charge vanish modulo (4), so symmetric detectors are blind and the detector must be quadrant-local.  Therefore the seam rule must be a **local endpoint rule**, not merely a global parity statement.

So the correct promoted statement is:

> **Proposition.**
> Let (X(u)=\xi(1/2+\sqrt u)). Assume the quadrant-local charge-transport dichotomy, the far-field zero-charge anchor, and the local seam odd-endpoint exclusion. Then (w_1(Q;X)=0) for every quadrant-local off-seam region (Q). Consequently every off-line zero of (\xi) has even multiplicity.

That is the proofable theorem. The unproved theorem you still need is the seam/transport lemma.

[1]: https://www.claymath.org/millennium/riemann-hypothesis/ "Riemann Hypothesis - Clay Mathematics Institute"
