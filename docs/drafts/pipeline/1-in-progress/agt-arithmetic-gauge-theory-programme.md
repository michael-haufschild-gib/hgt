# Arithmetic gauge theory of the ring ℤ (AGT programme)

- **ID:** agt-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2910/obstacles-summary.md §2.5–2.6
- **Statement:** Develop the programme: gauge points, special-point rigidity, approximate ring
  endomorphisms (Frobenius gap), coherent divisor collapse, shells as successor correlations,
  bounded multiplicity of classical producers, gauge exponents.

## Goal
A Lean programme `formal/GaloisForLFunctions/ArithmeticGaugeTheory/` with umbrella
`ArithmeticGaugeTheory.lean` and a foundational README. It builds on ACG's `GaugeTorus`,
`gaugeHaar`, `twist`.

## Gates
- [x] 0 → 1  in-progress: README draft written
- [ ] 1 → 2  paper proofs of each pillar (in module docstrings)
- [ ] 2 → 3  each pillar formalized, checked with `lake --old env lean`, wired into the umbrella

## Approach
Pillar modules (planned order):
1. `TheAdditivelyInvariantPoint`: a nonvanishing completely multiplicative function that is
   eventually periodic, or convergent, is identically one; twist versions.
2. `ApproximateRingEndomorphisms`: completely multiplicative maps with bounded additive defect
   are the identity or bounded by one. The gauge torus is exactly the unimodular ones. Exact
   endomorphisms are the identity and zero. Frobenius over 𝔽_p[X] multiplies degree by p.
3. `TheDivisorCollapse`: `Σ_{k∣ℓ} Λ(k)χ_x(k)` equals `log ℓ` at `0` and for every ℓ only at `0`.
   It has a closed form at the Liouville twin, gauge mean `0`, gauge mean square
   `Σ_{k∣ℓ} Λ(k)²`, and coherence bounds.
4. `ShellsAreSuccessorCorrelations`: the non-ratio pairs `n = km + j` of the prime form equal
   the shift-`j` successor correlation of `Λ * x` against `x`; gauge mean zero for `j ≠ 0`.
5. `FactorialRatiosHaveBoundedMultiplicity`: above the square root, `v_p` of a balanced factorial
   ratio is bounded by the number of factorials.
6. `GaugeExponents`: the precision exponent of a gauge point. Its almost-sure value is `≤ 1/2`,
   it equals `1` at twin tails, and it equals `Θ` at `0` (if available).

## Log
- 2026-10-29 — created; README draft written.
- 2026-10-30 — formalized and checked: TheAdditivelyInvariantPoint, ApproximateRingEndomorphisms,
  TheDivisorCollapse, TheShellDecomposition, TheGaugeExponent (exponent at 0 = Θ). Next: factorial-ratio
  multiplicity, coherence principle, exponent along the archimedean line.
- 2026-10-30 — also checked: FactorialRatiosHaveBoundedMultiplicity, TheCoherencePrinciple,
  TheArchimedeanLineCarriesTheExponent, TheGaugeExponentIsATailInvariant, TheAdamsOperations,
  TheMajorArcsOfTheShells, AffineInvariantKernelsAreTrivial, TheExponentIsNotGaugeInvariant.
  README v2 written. Open: growing-multiplicity producer, 0-1 law, a.e. exponent = 1/2,
  shell repayment, affine KL with boundary, index ceiling.
- 2026-10-30 — checked: TheLiouvillePointsHaveExponentOne (+ cylinder no-go), TheGaugeExponentZeroOneLaw
  (general tail-invariant sources), TheFiniteGaugePointsSampleHaar (large sieve on G),
  TheDirichletPointsCancelThroughPeriodicity, TheTypicalExponentIsOneHalf (a.e. exponent exactly 1/2 via
  top-prime block + Paley–Zygmund + PNT), TheSpecialPointsOfTheConstantSourceAreAtypical (special locus
  0 or 1; typical modulo the pole). Open: exponent floor (is 1/2 the minimum over G?), producer,
  BV for shells, shell repayment, affine KL with boundary, positive index ceiling.
- 2026-10-30 — checked: TheTrivialPointIsNeverBetterThanTypical (RH ⟺ exp(0) = θ_typ), TheSpecialLocusReadsGRH
  (Möbius exponent at primitive Dirichlet points = Θ_χ ≥ 1/2; GRH(χ) ⟺ typical), TheSpecialLocusIsTypicalOnAverage
  (large sieve: ≤ 2N^{1−2ε} atypical points up to conductor √N), TheLiouvillePointIsTheAntipode
  (S_N(ℓ) + S_N(0) = 2ψ(√N); pole ±1 separates the twins). Producer target as phrased in the review is
  excluded by the Bézout ledger for a single integer; the open form is AKLT's precision = size/multiplicity.

## Open-items goal (2026-10-30)
Targets: (1) typicality at an individual special point; (2) exponent floor on G; (3) growing-multiplicity
producer / precision = size/multiplicity; (4) BV for shells, shell repayment, positive affine KL, positive
index ceiling; (5) calibrations: sign at c = 2, derived 𝔽_q[T].
- (2) Paper proof (Liouville twin inequality): `μ(n)χ_{x+ℓ}(n) = μ(n)²χ_x(n)`, `μ² = Σ_{d²|n} μ(d)`, hyperbola
  at `D = (N+1)^κ` gives `exp_μ(x+ℓ) ≤ (1 + 2·exp_1(x) + exp_μ(2x)/2)/3`. At a real nonprincipal Dirichlet
  point `exp_1 = 0`, `2x` is a finite flip of `0`, so `exp_μ(x_χ+ℓ) ≤ (2+Θ)/6`. Hence floor on G ⟹ Θ = 1;
  RH ⟹ a point with exponent ≤ 5/12. Lean: `TheLiouvilleTwinInequality` (in progress).
- (1) GRH(χ) itself is out of reach; survivors: twin duality (x_χ ≥ 1/2 ≥ x_χ+ℓ).
- 2026-10-30 — checked and wired: TheLiouvilleTwinInequality (floor ⟹ Θ = 1; twin duality),
  FactorialRatiosHaveChebyshevPrecision (ghost windows, precision ≥ 2 log 2 · mass, binomial optimal),
  TheFunctionFieldCalibrationIsDerived (𝔽_q[T] degree sums 1, −q, 0 and squarefree count derived),
  TheShellsHaveLevelOfDistributionOneHalf (large sieve for the prime pair form and shells),
  AffinePositivityIsThePoleAndHaar (positive invariant forms = pole + Haar, index ≤ 1),
  TheShortShellsHaveNoConductor (overlap ≤ 2: shells |n − km| ≤ 2, level q ≥ 3 average zero).
  Still open: GRH(χ) itself; Siegel–Walfisz input; true floor of G; sign at c = 2 (a trivial-point
  question); non-invariant affine positivity; ceiling at 0; non-periodic producer.
