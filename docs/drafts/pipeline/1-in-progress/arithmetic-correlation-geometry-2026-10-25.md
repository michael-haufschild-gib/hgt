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
- [x] 1 → 2  paper proofs of each pillar (below)
- [x] 2 → 3  16 Lean modules checked with `lake --old env lean`, umbrella wired, README written;
  axiom audit of 53 key theorems: only `propext`, `Classical.choice`, `Quot.sound`

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
- **Exact killing theorem/mechanism:** multiplicative data are gauge invariant and determine a source
  only up to its gauge orbit (`agreeMultiplicatively_iff_exists_twist`); successor and coalescent
  statistics are gauge charged (`integral_succCorr_twisted`, `integral_twistedPrimeCoalSum`);
  gauge Jensen forces linear loss for multiplicative amplification
  (`pow_sum_normSq_le_sum_normSq_powCoeff`).
- **Strongest positive survivor:** every coalescent budget holds for Haar-almost every twist of
  the primes (`tendsto_gaugeHaar_large_twistedSurplus`); the boundary of a finite presentation
  separates gauge twins (`moebius_boundary_separates_twin`) at the unique horizon-uniform weight
  `σ = ½` (`exists_pos_tendsto_escapedMass_iff`); finite Dirichlet subgroups resolve the pairs the
  archimedean line freezes (`sum_twist_dirichletGauge_succ`); fixed budget ⇒ purity over `𝔽_q`
  (`unitary_of_bounded_powerSum`).
- **New insight:** the arithmetic content of a signed additive–multiplicative estimate is a property
  of one gauge point; the line, the finite subgroups and the boundary are the three ways to see it.
- **Status:** Lean, dependency-closed; README §6 records the open stabilizer-discrepancy target.

## Log
- 2026-10-25 — created; pillar list fixed after corpus survey.
- 2026-10-25 — Lean: gauge torus + orthogonality + all-order gauge moments; successor gauge charge;
  archimedean line vs gauge (threshold); coalescent surplus gauge variance o(N²); boundary = log a
  iff σ = ½; mixed Gram incidence + dilation covariance; sign gauge sees only square successor
  pairs; written: Möbius boundary vs Liouville twin, persistence law, amplification loss law,
  phase reconstruction (Baer extension). Pillars 7 (prime rank) dropped: content is the prime-value
  parametrisation already in SSA.
- 2026-10-26 — all 14 modules check clean; README final; umbrella + MainTheorems wired.
- 2026-10-26 — stabilizer decomposition of the actual coalescent statistic added; all oleans built; axiom audit clean.
- 2026-10-26 — Q3 first milestone formalized (relative square: gauge, trace, support, boundary, pole, golden test).
