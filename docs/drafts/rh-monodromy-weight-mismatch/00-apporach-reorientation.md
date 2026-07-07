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

I can reduce it, but not to zero. The honest state is:

[
\textbf{far-field zero charge and ordinary deck conservation are theorems;}
]

[
\textbf{the seam/terminal dichotomy is the real open core, and the naive seam-parity version is too weak.}
]

I will keep the proof strictly at level (w_1), so the target is only

[
RH_2:\quad \text{every off-line zero has even multiplicity,}
]

not full RH. RH itself remains listed by Clay as unsolved. ([Clay Mathematics Institute][1]) Your note is also explicit that the document is a search register, not promoted proof text.

## 1. What can be made unconditional

Put

[
Y(z):=\xi!\left(\frac12+z\right).
]

The functional equation gives

[
Y(-z)=Y(z),
]

so (Y) is even. Therefore there is a unique entire function (X) such that

[
Y(z)=X(z^2),
]

namely

[
X(u)=\xi!\left(\frac12+\sqrt u\right).
]

This is exactly the `xiDescent` object in your note: the functional equation is quotiented away, the descent is entire and branch-free, and RH becomes nonvanishing of this descended function on the slit plane.

Now let (u_0=z_0^2\neq 0), with (u_0) off the seam. Suppose (Y) has a zero of order (m) at (z_0). Since (Y) is even, it also has a zero of order (m) at (-z_0). Hence locally

[
Y(z)=(z-z_0)^m(z+z_0)^m H(z)
=(z^2-z_0^2)^m H(z).
]

Because the quotient is still even, (H(z)=K(z^2)) for some holomorphic (K). Therefore

[
X(u)=(u-u_0)^m K(u).
]

So the (u)-plane descent preserves the relevant multiplicity:

[
\operatorname{ord}_{u_0}X=m.
]

Thus, for a small loop (\gamma_{u_0}) around (u_0),

[
w_1(\gamma_{u_0};X)
===================

\frac{1}{2\pi i}\int_{\gamma_{u_0}}\frac{X'(u)}{X(u)},du
\pmod 2
=======

\operatorname{ord}_{u_0}X\pmod 2.
]

So

[
w_1(\gamma_{u_0};X)=1
]

is exactly the statement that the corresponding off-line zero of (\xi) has odd multiplicity.

That part is clean.

## 2. The far-field condition is not conditional

Define the principal slit-plane region

[
D=\mathbb C\setminus (-\infty,0].
]

In the part of (D) satisfying

[
\Re\sqrt u>\frac12,
]

we have

[
s=\frac12+\sqrt u
\quad\Longrightarrow\quad
\Re s>1.
]

But (\xi(s)) is zero-free for (\Re s>1). Therefore (X(u)\neq 0) there. Hence every loop (\gamma) contained in that far-field drain has

[
w_1(\gamma;X)=0.
]

So the statement

[
w_1(\infty;X)=0
]

can be promoted, provided “infinity” means the right-hand Euler-product drain, not an arbitrary large circle in the (u)-plane. Your note already records this as the far-field anchor: boxes right of (\Re s=1) carry zero deck charge at every rung.

So Lemma B is not the problem.

## 3. Ordinary conservation is also not conditional

If (\gamma_t) is a homotopy of loops avoiding (X^{-1}(0)), then

[
w_1(\gamma_t;X)
]

is constant in (t). Similarly, if (X_t) is a deformation and (X_t\neq 0) on a fixed contour, then the deck charge on that contour is constant. This is just homotopy invariance of the winding number.

Your note already has this in machine-checked form as `deckClass_step`, `deckClass_chain`, and `deckClass_deformation_invariant`.

So the real issue is not conservation. The issue is **where a nonzero local class is forced to go**.

## 4. The terminal dichotomy is not a topological theorem

The previous conditional proof assumed:

[
\text{every nonzero quadrant-local charge terminates at the seam or far field.}
]

That is not true from topology alone.

A small loop around an off-seam zero is a generator of the punctured-plane homology. It is not homotopic to a far-field loop unless one crosses the zero or supplies a deformation moving the zero. Conservation only says the charge cannot change while the contour avoids zeros; it does **not** say the charge must travel to the boundary.

A simple countermodel shows the danger:

[
P(u)=u^2+1.
]

Then (P) is real entire, (P(x)>0) for (x>0), and it has one upper-half-plane zero at (i) and one lower-half-plane zero at (-i). Around (i),

[
w_1=1.
]

The symmetric aggregate charge is

[
1+1=0\pmod 2,
]

but the upper quadrant-local charge is nonzero. It does not terminate at the negative real seam or at the positive far-field drain. It sits in a compact conjugate-pair island.

This is exactly the blindness your note warns about: FE/reality-symmetric aggregates can vanish modulo (4), so symmetric detectors miss the quadrant-local defect.

Therefore Lemma A cannot be replaced by ordinary homology or ordinary conservation. It needs an additional forcing principle.

The reduced obstruction is:

[
\boxed{
\text{rule out compact odd conjugate-pair islands.}
}
]

That is the real content.

## 5. The naive seam-parity rule is too weak

The statement

[
\text{“seam parity forbids unmatched odd charge”}
]

needs refinement, because at level (w_1) there is no distinction between equal and opposite:

[
-1=1\quad\text{in }\mathbb Z/2.
]

So “equal-and-opposite seam charge” cannot be expressed using ordinary (w_1) alone. One needs a lifted or relative invariant: a signed charge, a (\mathbb Z/4)-charge, or a half-seam boundary class.

There is also a local model showing why ordinary seam parity is insufficient. Consider the real-symmetric family

[
P_t(u)=(u-a)^2+t^2.
]

For (t>0), it has zeros

[
a+it,\qquad a-it.
]

The upper zero has quadrant-local charge

[
w_1=1.
]

At (t=0), the pair collides on the real seam and becomes

[
P_0(u)=(u-a)^2,
]

a double seam zero. The ordinary seam multiplicity is even, so ordinary seam (w_1) is zero. But the upper quadrant-local charge before collision was nonzero.

So an even seam zero does **not** forbid an odd upper charge. It can be exactly the endpoint of an upper/lower odd pair.

This means the seam statement must be upgraded from

[
\operatorname{ord}_{\Sigma}X\equiv 0\pmod 2
]

to something like

[
\frac12\operatorname{ord}_{\Sigma}^{\mathrm{collision}}X\equiv 0\pmod 2,
]

or, better, to a relative boundary class in a quadrant-ramified cover.

The central fixed-point parity theorem is real, but it only anchors the fixed locus. Your note records that (w_1) is trivial at the FE fixed point from FE alone, while also warning that off-line detectors must be quadrant-local.

So Lemma C reduces to a sharper missing theorem:

[
\boxed{
\text{the relevant half-seam / relative seam boundary class vanishes.}
}
]

Ordinary seam parity is not enough.

## 6. A cleaner reduction: replace seam transport by defect recurrence

The least conditional version I can honestly prove is this:

> **Reduced theorem.**
> Fix (\sigma_0>1/2), a height (H>0), and level (w_1). Suppose the following defect-recurrence property holds:
>
> If one box
>
> [
> B(T_0)=(\sigma_0,2)\times(T_0,T_0+H)
> ]
>
> has
>
> [
> w_1(B(T_0))=1,
> ]
>
> then boxes with (w_1=1) occur for a relatively dense set of heights (T).
>
> Then (w_1\equiv 0) for all such boxes. Consequently every zero of (\xi) with (\Re s>\sigma_0) has even multiplicity.

Here is the proof.

Assume some box has

[
w_1(B(T_0))=1.
]

Then that box contains at least one zero of (\xi) with (\Re s>\sigma_0).

By defect recurrence, there is (L>0) such that every interval of heights of length (L) contains some (T) with

[
w_1(B(T))=1.
]

Choose a separated subcollection of such boxes so that they are disjoint. Up to height (T), this gives

[
\gg T
]

disjoint boxes, each containing at least one zero with (\Re s>\sigma_0). Therefore

[
N(\sigma_0,T)\gg T.
]

But Ingham’s zero-density theorem gives, for every fixed (\sigma_0>1/2),

[
N(\sigma_0,T)
\ll
T^{3(1-\sigma_0)/(2-\sigma_0)}\log^C T.
]

Since

[
\frac{3(1-\sigma_0)}{2-\sigma_0}<1
\quad
\text{for }\sigma_0>1/2,
]

this is

[
o(T).
]

Contradiction.

Therefore no box has (w_1=1). Shrinking boxes around an isolated zero gives

[
\operatorname{ord}_\rho \xi\equiv 0\pmod 2
]

for every zero (\rho) with (\Re\rho>\sigma_0). Since (\sigma_0>1/2) was arbitrary, this proves (RH_2).

This is exactly the reduction your note states in §5: defect recurrence plus zero-density kills the cocycle.  The note also correctly says this is a rerouting of the burden, not a weakening, because all-level recurrence would be equivalent to RH; its value is that it grades the burden by (k) and starts with a coarse (\mathbb Z/2)-invariant.

## 7. What conditionality remains after the reduction

The old three conditions were:

[
A=\text{terminal dichotomy},
]

[
B=\text{far-field zero charge},
]

[
C=\text{seam odd-charge exclusion}.
]

After reduction:

[
B
]

is a theorem.

The conservation part of

[
A
]

is a theorem.

But the terminal part of

[
A
]

is not topological; it is equivalent to forbidding compact odd conjugate-pair islands.

And

[
C
]

must be replaced by a relative half-seam statement, because ordinary seam parity is blind to an upper/lower odd pair.

So the reduced open core is not three vague assumptions. It is one sharp missing mechanism:

[
\boxed{
\text{an odd quadrant-local deck defect must replicate, or else it must create a nonzero relative seam boundary class.}
}
]

Then one needs to prove that the relative seam boundary class is impossible for (\xi).

## 8. Why the free ({\sigma_p})-route cannot supply the missing mechanism

One tempting move would be:

[
\text{odd deck defect}
\quad\Rightarrow\quad
{\sigma_p}\text{-graded divisor defect}
\quad\Rightarrow\quad
\text{recurrence or mismatch}.
]

But your wave-6 amendment kills that inside bare (\mathcal M^+). The finite Euler layers and the archimedean factor are local units at strip points, the source map is zero, and the free reference is deck-invisible.

So the surviving path cannot be “dress (\xi) by the free Euler tower and compare deck classes.” Your note says the exact deck ladder survives, but the ({\sigma_p})-graded divisor refinement does not.

That means the only honest seam-based continuation is the torsion seam object:

[
R^n\xrightarrow{A}R^n\to Q,\qquad \det A=X^m,
]

with boundary

[
\operatorname{tr}(\operatorname{adj}(A)\Delta_p)\bmod X^m.
]

The first real theorem there is not RH and not recurrence. It is the non-fakeness theorem

[
\Delta_p\notin A\cdot \operatorname{End}+(X^m).
]

Your note identifies exactly this as the required next definition layer.

## Bottom line

The conditional proof can be reduced to this:

[
\boxed{
\text{Proved: descent, multiplicity preservation, local deck charge, conservation, far-field drain.}
}
]

[
\boxed{
\text{False/too weak: ordinary topology forcing every defect to the seam or infinity.}
}
]

[
\boxed{
\text{False/too weak: ordinary seam parity forbidding quadrant-local odd charge.}
}
]

[
\boxed{
\text{Remaining core: prove defect recurrence, or construct a relative half-seam invariant that an odd compact island cannot hide from.}
}
]

The cleanest reduced theorem is:

[
\boxed{
\text{defect recurrence of }w_1
\quad+\quad
\text{Ingham zero-density}
\quad\Longrightarrow\quad
RH_2.
}
]

That is a genuine reduction. It removes the vague seam/far-field story and leaves one precise target: **force recurrence or force a nonzero torsion seam boundary from a single odd quadrant-local deck defect.**

[1]: https://www.claymath.org/millennium/riemann-hypothesis/ "Riemann Hypothesis - Clay Mathematics Institute"
