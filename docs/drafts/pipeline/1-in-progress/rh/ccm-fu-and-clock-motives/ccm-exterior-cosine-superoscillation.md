# Exterior cosine superoscillation and coefficient barrier

- **ID:** CCM-EXT-COS-SUPEROSC
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `CCMActualHeadExteriorGaugeCoerciveCompactReduction.lean` · compact corrected-symbol lifting open core
- **Statement:** High-frequency cosine atoms supported outside an aperture can reproduce every lower-frequency cosine on a compact interval, but the canonical packet pays an exact exponentially growing coefficient-variation cost.

## Goal

Determine whether the compact core left by corrected-symbol coercivity can be lifted by exterior
cosine gauges without importing RH. Separate two questions which earlier representation attempts
conflated:

1. local expressive power of exterior frequencies on a compact interval;
2. global tail damage measured by total variation of the representing signed measure.

This is source-pure: parameters are real frequencies, binomial coefficients, complex exponentials,
and finite sums. No zeta-zero or RH hypothesis enters the construction.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, explicit packet, hostile audit stated
- [ ] 1 → 2  fully-proven: exact expansion, exterior support, compact convergence, and coefficient law
- [ ] 2 → 3  formalized: Lean theorem(s), target-only `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Conjecture loop

### C1 — exterior packet

For `N ≥ 1`, exterior center `H`, bandwidth `δ ≥ 0`, and real `c`, define

`P_N(x) = exp(i H x) ((1-c) + c exp(-i δ x / N))^N`.

The binomial expansion has real coefficients and frequencies

`H - k δ / N`, `0 ≤ k ≤ N`.

If `H - δ ≥ H₀`, every atom lies in `[H₀, ∞)`.

### C2 — superoscillatory limit

For fixed `x`, `P_N(x) → exp(i (H-cδ) x)`. Hence choosing
`cδ = H-λ` makes the real part converge to `cos(λx)` although every frequency is exterior.
Strengthen pointwise convergence to uniform convergence on each compact interval.

### C3 — exact variation law

For `c ≥ 1`, total absolute coefficient mass is

`Σ_{k=0}^N |choose(N,k) (1-c)^(N-k) c^k| = (2c-1)^N`.

Thus genuine downshift `λ < H-δ` forces `c>1` and exponential variation growth in this canonical
packet. This is the exact quantity entering the global cosine-gauge bound proved in
`CCMActualHeadExteriorGaugeCoerciveCompactReduction.lean`.

### C4 — route decision

Either find a different exterior representation whose variation is controlled strongly enough by
the corrected-symbol coercive tail, or prove a lower bound showing every such compact approximation
must pay comparable variation. The first outcome opens a constructive RH route; the second gives a
sharp no-go and forces a pivot away from exterior-measure positivity.

## Approach

Formalize in increasing-risk order:

1. exact binomial frequency expansion;
2. exterior support inequality;
3. exact coefficient-variation identity;
4. pointwise, then compact-uniform convergence;
5. combine with the existing tail estimate and test whether any diagonal choice of compact radius,
   approximation error, and coefficient mass can preserve global nonnegativity.

Each failed strengthening must leave its strongest exact theorem in Lean before pivoting.

## Hostile audit

- Compact density alone does **not** imply a positive global representative.
- Coefficient mass can create new negative lobes outside compact core.
- Choosing a larger compact interval after seeing coefficient mass is potentially circular.
- A finite signed measure is not a positive measure; existing RH capstone needs pointwise positivity
  of corrected representative, not approximation in isolation.
- Success requires a simultaneous quantitative error/tail/variation estimate, not a qualitative
  Stone–Weierstrass statement.

## Novelty status

- **Internal:** corpus search found no exterior-frequency cosine superoscillation theorem and no
  coefficient-controlled compact lifting theorem.
- **External:** classical superoscillation mechanisms may cover qualitative convergence; no novelty
  claim is made for C1–C3 alone. Project-specific novelty target is exact interaction with CCM
  corrected-symbol coercive tail and resulting route decision C4.

## Log

- 2026-08-21 — promoted directly to 1-in-progress after corpus search isolated compact lifting as
  open core and an explicit source-pure superoscillation packet as first constructive attack.
- 2026-08-21 — C1, pointwise C2, and C3 formalized in
  `CCMActualHeadExteriorCosineSuperoscillation.lean`. Stronger than planned: each packet is exactly
  the cosine transform of a positive-minus-positive finite atomic exterior measure, is an exact
  Suzuki-aperture null gauge, and its combined measure mass equals coefficient total variation
  `(2c-1)^N`. Genuine downshift forces this mass to diverge. Qualitative packet construction is
  classical superoscillation; corpus/literature search found no CCM exterior-gauge/null-form/mass
  coupling. Uniform-on-compact convergence and C4 remain open.
- 2026-08-21 — hostile route decision: pointwise (or even compact-uniform) density cannot by itself
  close positivity. Existing coercive-tail theorem subtracts exactly the two measure masses now
  proved to diverge exponentially. Next conjecture must beat this mass/tail feedback, prove a lower
  bound showing no exterior representation can, or pivot to a gauge class with an unbounded
  positive tail contribution rather than bounded Fourier–Stieltjes perturbations.
