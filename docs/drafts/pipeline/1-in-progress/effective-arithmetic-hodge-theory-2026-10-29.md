# Effective arithmetic Hodge theory of 𝔾_m(ℚ) (EAHT)

- **ID:** eaht-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2910/fable2.md §7
- **Statement:** the effective chapter of the field whose chapters are HKT, AKL, ASRP, AET, AIT, ACS:
  finite sections of the Weil kernel (heights, lengths, overlaps), what they carry, and the
  topology in which they reach the index.

## Goal
Build `formal/GaloisForLFunctions/EffectiveArithmeticHodgeTheory/` with umbrella and README; prove the
accessible first theorems of fable2 §7.8 and answer the §7.7 topics with theorems or no-gos with
positive survivors. Do not duplicate HKT/AKL/ASRP modules.

## Gates
- [x] 0 → 1  scope fixed, README first draft
- [ ] modules below proved and wired into the umbrella

## Module plan
1. Effective completion: Gevrey/Denjoy–Carleman schedules `(log log N)^α/N` reach the whole index
   (HKT open). Route: Gram-matrix convergence of synthesized families (polarization + two-sided
   Lévy perturbation), linear Euler–Maclaurin weights, real negative subspace of the spline Grams,
   HKT receiver bound for the upper half.
2. Hasse principle with heights: towers `⟨u⟩` with `log u < π/T` certify height `T`
   (`deepSparse_tower_law` at general `ℓ`); explicit `u ∈ ⟨2,3⟩` by Dirichlet; among any
   `binom(κ_T,2)+1` primes one certifies; `κ_T ≤` zero count.
3. Bandwidth dictionary (Fourier side of atomic families).
4. Arithmetic Stepanov ceiling (integer Chebyshev barrier / multiplicity at controlled size).

## Proved (axiom audit clean, wired into the umbrella)
- `TheHassePrincipleWithHeights` (pillar B).
- `TheExplicitSchedulesReachTheIndex` (pillar A, Gevrey and Denjoy–Carleman schedules; generic
  `eventually_le_hermNegIndex_of_synthesis`).
- `IndexCarriersOfFiniteSpectra` (tower windows, two-element boxes, two-prime boxes).
- `TheBezoutTheoremOfTheMultiplicativeGroup` (zero estimate along Frobenius progressions, sharp).
- `TheRiemannRochTheoremOfTheMultiplicativeGroup` (`h⁰(N, m) = ⌊N/∏p^{m_p}⌋`).
- `ApproximateVanishingIsAlmostDivisibility` (ε-small values on `N²p log p` points ⇒ tower sums
  `√2 ε`-small).
- `SmallIntegerAuxiliariesAreDivisible` (integer auxiliaries: small on a stretch ⇒ divisible; zero estimate).
- `TheTwistTowerCollapsesOverTheIntegers` (levels `j ≥ 1` of the Liouville twist tower lie in `𝒬`).
- `TwinsAreSeenByEveryLargeSection` (SSHA gauge law upgraded from frequently to eventually).
- 𝔽_q calibration `finrank_divisibleLT_eulerFactor` (in the Riemann–Roch module).

## Open / blocked
- A′ Steklov schedules: `tendsto_dcLogSynthesis` and `abs_iteratedDeriv_mollify_le_dcLogWeight` are
  `private` in `TransMetzlerWeilPositivity/SuperGevreyCriticalGrowth.lean`; once public, the
  instance is `eventually_le_hermNegIndex_of_synthesis` + `exists_dcLogSynthesis`.
- Bandwidth dictionary (C): built in SSHA (`OverlapCoordinates`, `TheNormalizedAtomicTransform`).
- Shell symbol (E), flip threshold (F): being developed in CACT and TM/BoundedOverlap by other
  agents; do not duplicate.
- A′ export of the two TM lemmas requested from peer sessions (hgt-b7, hgt-3b), no reply yet.
- Open research cores (README §11): converse Krein–Langer on Γ, flatness identity / producer,
  quadratic Riemann–Roch on a surface, covariant regulators, Herglotz, infinite symmetry,
  depth-sensitive census, constrained inversion.

## Leads checked (exist; do not redo)
- `ArithmeticCastelnuovoSeveri.deepSparse_tower_law` holds for every `ℓ > 0`.
- `HeckeKreinToeplitz.hermNegIndex_weilGram_le_negIndex_zetaKernel` (upper half for any real test).
- `SpacingScaleHarmonicAnalysis.exists_gevreySynthesis`, `weilQuad_add_le`, `levyEnergy_add_le`.
- `ArithmeticCastelnuovoSeveri.hermQuad_weilGram`.
- `RHTower.exists_xiZeroCount_upper_bound` (`≤ c T log T`).

## Log
- 2026-10-29 — created; README first draft written; pillars A and B proved.
- 2026-10-30 — carriers, Bézout, Riemann–Roch, approximate Bézout, integer rigidity, twist tower, eventual gauge law.
