# Lattice Section Theory of the scaling surface (LST)

- **ID:** lst-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0111/obstacles-summary.md §2.7, Q1–Q3, B25, B39, B40
- **Statement:** sections of the scaling surface as Gaussian lattice counts; Serre duality as
  Poisson summation; `h¹ = Künneth part + ½ Weil defect`; definite counts are fakes; the split
  surface selects through boosts; the even Hodge defect is the primitive `h¹` index.

## Goal
Answer the 2.7 questions with Lean theorems; isolate the primitive `h¹` as the single missing count.
Lean folder `formal/GaloisForLFunctions/LatticeSectionTheory/`, umbrella `LatticeSectionTheory.lean`,
README in the folder.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proofs of the pillars (below)
- [x] 2 → 3  Lean modules for the pillars, each checked with `lake --old env lean`
- [ ] open core: primitive `h¹` as a count (stays in 1-in-progress)

## Formalized (module → content)
- `TheSlopeOfALatticeCountIsItsRank`: Poisson RR for every rank, Banaszczyk slope law, rank law.
- `TheKunnethRiemannRoch`: `h¹ = h¹_K + ½δ`; Künneth effectivity ⇔ Hodge index; ⇔ RH on ζ.
- `BidegreeCountsSeeNoPrimitiveClass`: bidegree blindness; prime-free effectivity (≤ 3/10 all tests;
  ample-orthogonal ≤ (log 2 + 1/50)/2).
- `RiemannRochOutsideAFiniteDivisorAtEveryDegree`: effectivity + coercive primitive `h¹` off `D_a`.
- `TheRectangularLatticeCount`, `DefiniteCountsHaveOffLineZeros`: Epstein FE-pair, Dirichlet
  series, real zero in (½,1) for `y > e²` and `y < e^{−2}`.
- `TheSiegelMajorantIsTheHodgeIndex`: majorant ⇔ HI; Siegel counts converge ⇔ RH; boosts `|u|>1`
  fake; Hecke = boost.
- `TheBoostTransformRestoresTheEulerProduct`: `∫Z⁺e^{2wu} = Kζ(s+w)ζ(s−w)`.
- `TheIsotropicConeCountsDivisors`: cone count `Γ(2π)^{−σ}ζ²`, double pole, not Poisson-dual,
  Siegel–Weil identity.
- `HeckeCorrespondencesAreSimilitudesOfThePrimitiveH1`, `TheIndexReadingsOfThePrimitiveH1`,
  `TheCalibrationOverFiniteFields`, `TheSelfDualPointHasNoRealZeros` (Λ_1 < 0 on (0,1)).
- `ThePrimitiveH1OfPrimeFreeCyclesIsAJumpCount`: on prime-free tests `W = Ω(0)‖f‖² + J(f) + 2·pole`;
  exterior jumps force `W ≥ ‖f‖²/4` for aperture `≤ 1/2000`.
- `TheExteriorJumpsOfAPrimeFreeCycle`: `A_f(x) ≤ ½‖f‖²` for gaps `x ≥ a`; count-derived positivity
  `W ≥ ‖f‖²/20` for aperture `≤ 1/64`.

## Open core
Primitive `h¹ = ½W(f,f)` as a nonnegative count. Prime-free: the jump-count identity is formalized
and forces positivity up to aperture `1/64`; exterior charge `½∫f²(W(a−x)+W(a+x))` would give
`≈ 0.03`; the window `½ log 2` needs interior jumps (Lévy Poincaré on an interval) and the pole
sign structure (`+2A²` even, `−2A²` odd). Beyond the window: the prime comb in the count.

## Log
- 2026-11-01 — created with README first draft; pillars formalized (15 modules).
