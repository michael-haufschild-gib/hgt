# Siegel Linearizer is Always Hypertranscendental

- **ID:** siegel-linearizer-ht
- **Stage:** 0-backlog
- **Type:** SOURCE-SETTLED / GATEKEEPER CORRECTION
- **Source:** Turing id=1786, id=1787 (tetrachotomy); Wheeler id=1793 (gap + routes)
- **Priority:** CLOSED AS OPEN TARGET — Becker--Bergweiler already covers convergent irrationally indifferent Schroeder functions

## Statement `[SOURCE-SETTLED]`

Let P be a rational map of degree d ≥ 2 with a Siegel fixed point at the origin, i.e.,
P(0) = 0 and P'(0) = λ = e^{2πiτ} with τ ∈ ℝ\ℚ satisfying the Brjuno condition
(so the linearizing coordinate φ converges). Then the Schröder linearizer φ (satisfying
φ(λz) = P(φ(z)), φ'(0) = 1) is hypertranscendental over ℂ(z).

This is not a new conjecture: for rational maps of degree at least two it follows from
Becker--Bergweiler's classification, as restated in Fernandes's survey. A convergent
irrationally indifferent linearizer is a Schroeder function; if such a function were
differentially algebraic, Theorem 3.1 forces the fixed point to be repelling, contradiction.

## Background: the four-corner linearization classification (Turing id=1786)

| Case | Multiplier | Linearizer | DA exceptions | HT status |
|------|-----------|------------|----------------|-----------|
| Superattracting | λ=0 | Böttcher φ∘P=φ^d | z^d | HT iff P≠z^d [B–B, proved] |
| Hyperbolic | 0<|λ|<1 | Koenigs/Schröder φ(λz)=P(φ(z)) | z^d, Chebyshev | HT iff not z^d/Cheby [Ritt/2102.08268, proved] |
| Parabolic | |λ|=1, λ root of unity | Fatou φ∘P=φ+1 | non-trivial? | HT iff non-trivial Écalle-Voronin [CONJECTURE, Turing id=1779] |
| **Siegel** | |λ|=1, λ=e^{2πiτ} τ∉ℚ | Schröder φ(λz)=P(φ(z)) | none in the convergent rational-map case | HT by Becker--Bergweiler/Fernandes |

## Why exception-freeness is expected (Turing id=1787)

**Claim (proved):** z^d and Chebyshev have NO Siegel fixed points.

Proof: 
- z^d: fixed points at z=0 (multiplier 0, superattracting) and z^{d-1}=1 (multiplier d, 
  an integer ≥ 2, REPELLING). No multiplier lands on S¹ with irrational argument.
- Chebyshev T_d: post-critically finite, multipliers at fixed points are algebraically rigid
  (Lattès-type), never irrationally-neutral.

Consequence: the known DA-exceptions (z^d, Chebyshev) CANNOT have Siegel points. So the
DA cases from the hyperbolic classification are structurally excluded.

**The gap (Wheeler id=1793):** this proves the known DA-exceptions are absent. It does NOT
close off other possible routes to DA-ness for Siegel linearizers — there might be polynomial
maps with Siegel points whose linearizer is DA via a mechanism invisible to Ritt's hyperbolic
argument. A proof needs the Siegel case on its own terms.

## Why the proof is hard

**Ritt/2102.08268 does NOT apply.** That result uses the EXPANDING dynamics (|λ| < 1 in Koenigs)
to write the Schröder equation as a Mahler-type difference equation amenable to Kolchin theory.
For |λ| = 1 (neutral), there is no expansion — the small-divisor problem (denominators λ^n − 1
with |λ^n − 1| → 0 as n → ∞ when τ is well-approximated by rationals) is the obstacle to
convergence (Brjuno condition) AND to any direct transfer of Ritt's technique.

## Candidate proof routes

### Route A: Extend Ritt's classification to |λ|=1

Prove: for rational P with a Siegel fixed point (Brjuno τ), φ DA ⟹ P ∈ {some exceptional set}.
Then show that exceptional set has no maps with Siegel fixed points.

**Why hard:** The Kolchin differential Galois theory works for all |λ| ≠ 1 via the Mahler/difference
equation. At |λ| = 1 irrational, the operator σ_λ: f(z) → f(λz) is a unitary (isometric) automorphism
of function spaces — very different from the contractive case. The theory of difference equations
with |q| = 1 requires analytic continuation across singularities of the Borel transform, which
is the content of the Birkhoff-Guenther / Ramis-Sibuya resummation theory in this regime.

### Route B: Direct proof via irrational-rotation monodromy `[CONJECTURE — most promising]`

If φ were DA over ℂ(z), the differential Galois group G = Gal(φ/ℂ(z)) is an algebraic group
acting on the solution set of the ADE that φ satisfies.

The Schröder equation says: for each n ∈ ℤ, φ(λ^n z) = P^n(φ(z)). Since τ is irrational,
{λ^n : n ∈ ℤ} = {e^{2πinτ} : n ∈ ℤ} is DENSE in S¹ by Weyl's equidistribution theorem.

**The monodromy argument [CONJECTURE]:** The DA-ness of φ constrains how its analytic
continuation varies along z → λ^n z. If the orbit {λ^n z₀} is dense in the circle |z|=|z₀|,
then the values {φ(λ^n z₀)} = {P^n(φ(z₀))} must be dense in the Julia set ∂D_P (the boundary
of the Siegel disk). This density forces the germ of φ to have an infinitely-branched analytic
continuation, inconsistent with satisfying a finite-order ADE.

**Formal version (needs work):** an ADE of order n over ℂ(z) has (locally) at most finitely
many branches at each point. But the orbit under σ_λ: z → λz generates infinitely many
(formally distinct) continuations of φ. For τ irrational, the orbit is infinite and dense.
So the ADE would have to have infinitely many solutions at each point — contradicting finite-degree.

**The obstruction:** this argument works cleanly for TRANSCENDENTAL functions of z, where "infinite
branches" means the ADE has too many solutions. But φ is typically defined on a bounded domain
(the Siegel disk D_P), not all of ℂ. Restricting to a bounded domain, the number of branches
is still governed by the ADE degree. The density argument needs to be phrased in terms of the
function's analytic behavior on D_P, not on all of ℂ.

### Route C: q-expansion / natural-boundary argument

For the Siegel linearizer φ with τ irrational Brjuno, the q-expansion (q = e^{2πiτ}) of φ
near the fixed point is a formal power series with small-divisor denominators. These series
are known to converge (Brjuno condition) but have natural boundaries at the boundary ∂D_P.

If a function has a natural boundary and is analytic inside, can it be DA? This is related
to the question of whether DA functions can have natural boundaries (they can — the Chazy
equation has natural boundaries). But the SPECIFIC structure of Siegel small-divisor natural
boundaries might obstruct DA-ness.

**Connection to q-Pochhammer (Turing id=1786):** the small-divisor denominators in the
Siegel expansion are {λ^n − 1} = {e^{2πinτ} − 1}, which are the q-analogues of (q;q)_∞
evaluated at q = λ on the unit circle. The natural boundary of (q;q)_∞ at |q|=1 is the
unit circle itself. This connection to the q-Pochhammer natural boundary might provide
a route via the theory of natural-boundary functions and HT.

## Open sub-problems

1. **The Cremer case:** when τ is NON-Brjuno, the linearizer φ does not converge (Cremer
   phenomenon: 0 ∈ J_P). A formal power series φ̂ satisfies the Schröder equation formally.
   What is the HT-status of the formal Schröder series for Cremer τ?

2. **Arithmetic dependence:** does HT-ness of φ depend on the arithmetic of τ (Brjuno vs
   Diophantine vs Liouville)? [CONJECTURE: no — it's HT for all τ∉ℚ where defined]

3. **Relation to Feigenbaum:** the Feigenbaum fixed-point g has a REAL multiplier λ ≈ −0.4
   with |λ| < 1 (hyperbolic). The renormalization functional equation g(g(λx)) = −g(x)/α
   has the structure of self-composition at multiplier λ. The Siegel case is the |λ|=1
   analogue of this self-composition problem — both require transcendental-composition theory.

## Connection to small-divisor difference-Galois theory

The Schröder equation φ(qz) = P(φ(z)) with |q|=1 is a q-difference equation with q on
the unit circle. The difference Galois theory for |q|=1 (as opposed to |q|≠1) is less
developed but active (Singer, van der Put, Ramis). The Galois group in this case is related
to the Stokes phenomena for the resummation of the Siegel series.

Key reference (to search): Ramis' theory of "confluence" of q-difference equations as q→1
and its differential Galois interpretation. Whether this gives an HT certificate for Siegel
linearizers is the research direction.

## Novelty assessment `[CONJECTURE]`

**NOVEL?** The four-corner linearization picture with the Siegel case as exception-free is
identified by Turing as the completion of Ritt's dichotomy. Whether this is in the dynamical
systems / complex analysis literature (Buff-Cheritat, Douady, Yoccoz) in this exact form is
unknown to us. The application of HT theory to the Siegel corner seems new as a precise open
problem. BRIDGE at minimum.

**SIGNIFICANT?** Exception-freeness would make the Siegel linearizer the purest HT object in
the classification — every Siegel disk's linearizing coordinate is HT, no exceptions, by
virtue of the irrational neutrality of the multiplier. This extends the Ritt classification
to the fourth and most arithmetically rich corner of complex dynamics. HIGH significance for
the hgt field.

## Log

- 2026-06-24 — Wheeler: card created from Turing's tetrachotomy discovery (id=1786, 1787).
  Gap identified (Wheeler id=1793): exception-freeness doesn't close the HT argument; Ritt's
  proof doesn't transfer to |λ|=1. Three routes added. Route B (irrational-rotation monodromy)
  and Route C (q-expansion natural boundary) are the main candidates.

## 2026-06-24 source audit — open conjecture killed

Anti-theatre check: no computation is useful here. The bit that matters is source classification, not numerical evidence or a local derivation.

Fernandes's survey of Becker--Bergweiler sets the framework to include attracting, repelling, and irrationally indifferent fixed points: for those cases it considers the Schroeder equation and calls a convergent normalized solution a Schroeder function. The same proof then assumes a Schroeder/Boettcher/Abel solution is differentially algebraic and concludes that a differentially algebraic Schroeder function is in the first, repelling, exceptional list.

Therefore a Brjuno Siegel fixed point of a rational map of degree at least two is source-settled: its linearizer is a convergent Schroeder function at an irrationally indifferent, hence non-repelling, fixed point. If it were differentially algebraic over `C(z)`, Becker--Bergweiler/Fernandes would force the fixed point into the repelling case. Contradiction.

Primary source: P.-G. Becker and W. Bergweiler, "Hypertranscendency of conjugacies in complex dynamics", Math. Ann. 301 (1995), 463--468, DOI `10.1007/BF01446639`. Accessible restatement/proof: Gwladys Fernandes, arXiv:2102.12168, especially the setup around lines 661--671 and the proof/conclusion around lines 1298--1367.

Grade: SOURCE-SETTLED BRIDGE. This card remains useful only as a guardrail against re-opening the Siegel corner with unit-circle q-difference theatre.

## 2026-06-24 Turing — BB citation VERIFIED real + parabolic row is out of date

**Citation verification (anti-fabrication, load-bearing).** Becker–Bergweiler, "Hypertranscendency of
conjugacies in complex dynamics", Math. Ann. 301(3), 463–468 (1995), DOI 10.1007/BF01446639 — CONFIRMED real
via SpringerLink and Bergweiler's publication list (predecessor: Becker–Bergweiler, Manuscripta Math. 1993,
"Transcendency of local conjugacies…"). So the linearization-trichotomy / Siegel-HT / recession-theorem cards
that cite BB rest on a genuine source. (Fernandes arXiv:2102.12168, the survey restatement, was not directly
re-confirmed by this search, but the PRIMARY theorem source BB 1995 is solid.)

**Inconsistency flag (minor).** The §"four-corner" table here marks the **parabolic** row as
"[CONJECTURE] HT iff non-trivial Écalle–Voronin (Turing id=1779)". That is OUT OF DATE: the sibling card
`rational-linearization-ht-trichotomy.md` settles it via Fernandes Thm 3.1 — *Abel functions of rational maps
of degree ≥2 are always HT* (no Écalle–Voronin caveat). So the parabolic corner is SOURCE-SETTLED HT, same as
Siegel, not a conjecture. The table should read parabolic = "HT always [B–B/Fernandes Thm 3.1]". Lead for
anyone wanting the explicit parabolic mechanism: "Julia's equation and differential transcendence"
(arXiv:1307.6381), surfaced in the same search — the Abel/Julia-equation differential-transcendence treatment.
