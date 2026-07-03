# 14 — The Parity Stratum: Filters and the Exact-Identity Audit

**Register: SEARCH** (conjectures labelled). Lean citations are to banked, axiom-clean
theorems in `formal/GaloisForLFunctions/RHTower/`.

**Object.** The k = 1 rung. A *w₁-detector* is a lemma of the shape

> (D)  FE ∧ P(ζ) ⟹ for every zero ρ of ξ with Re ρ > 1/2: 2 ∣ ord_ρ(ξ),

for some exact property P. By `xi_deckClass_eq_one_iff_ladder_dvd` (XiDeck.lean, k = 1)
this is identically the statement that the deck class of local square roots of ξ is
trivial at every off-line zero. RH_2 is (D)'s conclusion; the ladder
`rh_iff_forall_ladder` consumes it as the base stratum.

This document sets up the three filters a candidate P must pass **before any proof
attempt**, runs the classical identity families through them, and records what
survives. Its function is discipline: every candidate killed here is a proof attempt
not wasted (#97), and the survivors re-aim #116.

---

## 1. Filter I — the Davenport–Heilbronn filter

**[PROVED HERE, from banked certificates]** The D–H function f_DH (5-periodic
coefficient pattern [1, κ, −κ, −1, 0], κ ≈ 0.28408 the classical D–H constant, stream
a_n = Re((1−iκ)χ(n)) per 04-prior-work-audit) satisfies an exact FE of
ξ-type about Re s = 1/2, is real-symmetric, has Dirichlet-series regularity, Bohr
almost-periodicity on vertical lines, and standard growth — and carries certified
SIMPLE off-line zeros: the banked 18-digit zero at
ρ ≈ 0.8085171824566374 + 85.69934848537759·i (04-prior-work-audit F1), and 237/237
off-line zeros of odd winding in t ≤ 5002 (R2 campaign). It has **no Euler product**.

**Consequence (the filter).** Any P for which (D) is provable must FAIL for f_DH.
Excluded at a stroke, because f_DH possesses them:

- FE alone, in any packaging (covers, descents, reflection identities);
- reality / real-symmetry;
- Dirichlet-series shape, coefficient boundedness, growth bounds, order ≤ 1;
- vertical almost-periodicity of any regularity f_DH has (Bohr on lines σ > 1;
  B² in the strip — cf. 11-recurrence-degrees Thm A/B for where these die anyway);
- any conjunction of the above.

P must consume **genuine multiplicativity** — the one axiom f_DH lacks. This is the
same division of labour measured throughout the lane (Euler moat R5/R5b; density
clause C4), now imposed at the level of lemma shape.

Consistency check on the banked base case: `xi_central_order_even`
(ReflectionParity.lean) forces even order at s = 1/2 from FE alone — and indeed the
same argument applies verbatim to f_DH at its center. No conflict: the central point is
not off-line. The mechanism (parity at the **fixed/ramified locus** of a constraint
symmetry) passes the filter precisely because it asserts nothing off the fixed locus.

---

## 2. Filter II — the symmetry discount (quadrant-localization)

**[PROVED HERE, from banked Lean]** By `xi_orderAt_conj` and `xi_orderAt_one_sub`
(Reflection.lean), every hypothetical off-line zero ρ lies in a quadruple

  {ρ, ρ̄, 1−ρ, 1−ρ̄},  all four of equal order m,

and the four points are distinct (Re ρ ≠ 1/2 by hypothesis; Im ρ ≠ 0 since ξ has no
real zeros in the strip — ζ(σ) ≠ 0 on (0,1)). Hence:

> **Symmetry discount.** Any region symmetric under both s ↦ 1−s and s ↦ s̄ carries
> total off-line charge ≡ 0 (mod 4).

**Consequence.** A detector that reads only FE-and-reality-symmetric aggregates —
global counts, symmetric-box windings, moment/trace data over symmetric regions, the
whole-strip explicit formula paired against symmetric test functions — is
**structurally blind at k = 1 and k = 2**: the symmetric aggregate of a lone simple
quadruple is 4, trivial mod 2 and mod 4. The first k at which symmetric data can see a
simple quadruple is k = 3.

So a w₁-detector must be **quadrant-local**: it must weigh a region containing ρ but
not ρ̄ (equivalently, in the u-plane of UPlaneDescent.lean, a region containing u but
not ū). This is why the deck class was built as a per-box invariant, and it is a hard
constraint on identity candidates: an exact identity whose two sides are
conjugation-equivariant (all of them below are) can only detect w₁ through
*non-symmetric evaluation*, never through symmetric averaging.

---

## 3. Filter III — the regularity wall (imported)

P must not factor through value-distribution/measure data of ζ on vertical lines or
strips. Four independent derivations (10-blind-cone; 11-recurrence-degrees Thm A/B;
11 §5.3 trichotomy; 12-turan-hybrid §6 priced death certificate) close every soft,
statistical, recurrence-shaped route at ζ's exact regularity: S²-a.p. is false for ζ,
B²-a.p. admits FE-symmetric counterexamples with finite off-line zero sets, and
exact-Euler recurrence-forcing costs exp(−e^{1/δ}) against a ceiling of exp(e^{c₁/δ}),
c₁ < 1. A candidate P phrased in that register is dead before the D–H filter is even
consulted. Survivors must be **exact**: monodromy, divisor, index, or identity data.

---

## 4. The audit

### 4.1 FE-covers and descents (u-plane family)

Passes Filter III (exact); **fails Filter I as an off-line detector** — correctly and
instructively. The u-descent `xi_eq_xiDescent` (UPlaneDescent.lean) exists verbatim
for f_DH (same even FE), so nothing cover-shaped built from FE alone can force
off-line parity. What the family *does* force is banked: even order at the
ramification point (`xi_central_order_even`; in the u-plane, the ramification of
s ↦ (s−1/2)² sits at u = 0). **Verdict: base case only.** The mechanism to generalize
is the ramified locus, not the cover; see 4.4.

### 4.2 The dyadic / Adams family — order balance, no anchor

The exact identities ζ(2s) = ζ(s)·L_λ(s) (λ = Liouville) and their iterates

  ζ(2^J s) = ζ(s) · ∏_{j=0}^{J−1} L_λ(2^j s)

pass Filter I (λ is where multiplicativity lives: L_λ = ζ(2s)/ζ(s) has no D–H
analogue). Computation at an off-line zero ρ of order m (Re ρ ∈ (1/2, 1)):

- Re(2^j ρ) > 1 for all j ≥ 1, so ord_{2^j ρ} of every factor built from ζ is 0 there;
- hence ord_ρ(LHS) = 0 and the right side telescopes to 0 = m + ord_ρ(L_λ),
  i.e. ord_ρ(L_λ) = −m. Substituting back: 0 = m − m. **The identity is
  order-balanced at every off-line zero.** The transported data (a zero of order m of
  ζ(2·) at ρ/2, a pole of order m of L_λ at ρ) never meets a point of *forced* order.

The obstruction is structural, not an accident of λ: an affine transport s ↦ as + b
moves ρ to aρ + b, and the only points of the ζ-world with forced nontrivial order
(the pole at 1, order −1; trivial zeros at −2k, order 1) are isolated — an affine map
sends a hypothetical continuum of possible ρ's onto them only for isolated ρ. So:

> **[PROVED HERE, elementary] Affine-monomial identity families
> (∏ ζ(a_i s + b_i)^{e_i} = controlled Dirichlet data) are order-conservative at
> off-line zeros. They can transport w₁; they cannot anchor it.**

**Verdict: dead as detectors; alive as transport.** Any use of this family requires an
anchor from elsewhere (conservation's far field, or a ramified cover). This re-aims
#116 sharply: *affine transport is exhausted; only ramified (nonlinear) transport
remains as an identity shape* — and the classical corpus offers no correspondence for
ζ beyond the affine/Adams family (GL(1)/ℚ has no Hecke correspondences to spare).
A detector-grade cover must be **constructed**, not found. [CHECK, C10 candidate:
literature sweep for nonlinear functional identities of ζ beyond FE ∧ Adams — expect
absence; run at promotion time.]

### 4.3 The positivity class — even order lives on the real locus only

Candidates: ζ(s)/ζ(2s) = Σ_{squarefree} n^{−s}, ζ(s)²/ζ(2s) = Σ 2^{ω(n)} n^{−s},
Rankin-type squares; mechanism: a Dirichlet series with nonnegative coefficients is
positive on the real axis right of convergence, and a real-analytic function
nonnegative on a real interval has even-order zeros there; Landau's theorem pins the
real singularity. Passes Filter I (coefficient positivity of these series IS an Euler
consequence; f_DH's analogues have sign-mixed coefficients).

But the mechanism's habitat is one-real-dimensional: it forces parity only at **real
points** of the series variable. For ζ that locus is (0,1) ⊂ ℝ, where ζ has no zeros
at all (ζ(σ) < 0 there) — no content. Vertical shifts destroy positivity
(n^{−it} phases). In the u-plane the real locus is: positive axis (= real s, no
zeros), and the **slit boundary** (= the critical line). So positivity-type parity
statements native habitat is the SEAM — the closed on-line locus — not the open
off-line region. Two prior verdicts subsume the rest: the lane's M3 refutation
(positivity-alone admits generic off-line zeros in positive Beurling systems, DMV
import, 04-prior-work F4), and the known failure ζ(s)/ζ(2s) has non-positive log
(00-approach §8). Filter II also applies: all these series are conjugation-equivariant
and were to be read through real/symmetric evaluations.

**Verdict: dead for off-line w₁.** Retargeted: positivity is seam material — its
proper consumer is the seam cocycle (#122), where "even order at the boundary-real
locus" is exactly the granularity of the slit ledger. (Its classical shadow: Hardy's
sign-change zeros are the odd-order on-line population.)

### 4.4 What survives

Two shapes pass all three filters:

1. **Conservation + family (M-lane, #119).** The deck charge is quadrant-local
   (Filter II ✓ — boxes are one-quadrant by construction), exact monodromy data
   (Filter III ✓), and the family deformation input is where multiplicativity enters:
   the measured Euler moat and defect extinction (R5/R5b) are D–H-separating
   (Filter I ✓ — the D–H end of the pencil is where the off-line population lives).
   Formal spine already banked: `deckClass_deformation_invariant` (conservation),
   `xi_deckClass_far_field` (anchor), `analyticOrderAt_even_of_reflection`
   (family-wide central parity). The open input is the global bookkeeping of #119:
   annihilation requires matching charge — which is where the parity stratum and the
   conservation lane consume each other.

2. **Constructed ramified correspondences (#116, re-aimed).** By 4.1/4.2 the detector
   must be a cover or correspondence whose **ramified locus meets the open quadrant**
   (not just the FE fixed point), compatible with the Euler structure so it breaks on
   D–H. No classical object does this; the hgt-native move is to build it. Concrete
   first target [CONJECTURE]: a two-sheeted cover of the u-plane slit geometry,
   branched at a *movable* point anchored to the far field, against which the deck
   class of ξ-roots is forced to descend — the u-plane version of "carry the arc to a
   line and reflect" (the q62 agent's third reflection theorem is the local model:
   reflection across a biholomorphic preimage of a line).

---

## 5. Board consequences

- **#97** (lemma attempts): restricted to the two survivors. No proof attempts on
  affine-identity or positivity candidates; they are refuted-by-filter above.
- **#116**: target sharpened from "hunt an identity" to "construct a quadrant-ramified
  cover compatible with Euler structure"; affine transport banked as a tool
  (order-balance lemma, 4.2), not a route.
- **#122** (seam cocycle): inherits the positivity class as its natural instrument set.
- **Symmetry discount** (§2) is a standing lemma for #119's bookkeeping: symmetric-box
  accounting starts at k = 3; the k ≤ 2 strata are irreducibly local. Lean target if
  needed: a four-point corollary of `xi_orderAt_conj` + `xi_orderAt_one_sub` (cheap).

The parity stratum's live geometry after the audit: **one lane through conservation
(dynamic, family-fed), one lane through construction (static, cover-fed), meeting at
the same object — the quadrant-local charge.**
