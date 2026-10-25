# Arithmetic Correlation Geometry (ACG)

- **ID:** acg-2026-10-25
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (programme card)
- **Source:** ../../../reports/review-2510/astra.md §3–§5
- **Statement:** Found the programme `formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/`:
  how additive relations constrain signed multiplicative correlations, and how those constraints
  reach spectral receivers with their boundary terms intact.

## Goal
Answer the report's three questions (signed coalescent surplus; prescribed additive–multiplicative
compatibility; relative amplification) and topics A–G with unconditional Lean theorems, and write
the foundational README.

## Gates
- [x] 0 → 1  in-progress: source read, sibling programmes surveyed (TTPC, SSA, BiarithmeticGeometry,
  AKT, ACS, APD, MPG, ADR, SquareRootThreshold, BSU)
- [ ] 1 → 2  paper proofs of each pillar (below)
- [ ] 2 → 3  Lean modules audited, umbrella wired, README written

## Approach (pillars)
1. Gauge group of multiplicative observation: twists `χ_x(n) = ∏ e(x_p v_p(n))` on the torus
   `UnitAddTorus ℕ`; Haar orthogonality; gauge moments of every order equal the multiplicative
   diagonal (no threshold); invariant monomials = multiplicative coincidences.
2. Successor correlations are pure gauge charge: mean zero, variance = magnitude energy,
   covariance across shifts = dilation correlation along `(h/g, h'/g)`; blindness corollary.
3. Threshold = price of the archimedean (Kronecker) line: window moment = `‖η‖²` gauge moment +
   near-incidence form; NI has gauge mean zero; nonnegative sources maximize PD-kernel NI.
4. Coalescent surplus (Q1) is pure gauge charge: twisted mean zero, variance = Σ weights².
5. Boundary geometry: escaped mass of `n ↦ an+b` at weight `n^{-2σ}` → `log a` iff `σ = ½`
   (→ 0 above, → ∞ below); composition cocycle.
6. Mixed Gram of an affine orbit = signed counts over `aj − ck = h` with escaped cells.
7. Successor phases of a gauge orbit have rank `π(N+1)` among `N`.
8. Multiplicative data determine a source up to gauge (character extension).
9. Persistence law (topic F): Lipschitz witness persistence vs exceptional measure.
10. Amplification comparison and loss laws (Q3); `𝔽_q` fixed-budget law; relative powers of ζ
    are idempotent.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** —
- **Strongest positive survivor:** —
- **New insight:** —
- **Status:** —

## Log
- 2026-10-25 — created; pillar list fixed after corpus survey.
