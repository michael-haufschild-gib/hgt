import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorCutoffReciprocity

/-!
# Exact compact-test Mellin limit of the cubic inversion defect

The actual arithmetic boundary pairing minus its reciprocal pairing tends
on `1 < re s < 2` to the primitive Mellin transform minus two holomorphic
upper tails. All estimates come from the original cubic datum. This identity
alone does not supply a function representative or pole-density rigidity.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
namespace RHTower.WeilHigherDenominator

/-- The reciprocal compact-test limit is paid entirely by the original cubic datum. -/
theorem degreeTwoQuotient_tendsto_reciprocal_head_pairing {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (A : ℂ) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun R : ℝ => fourierBoundaryPairing (degreeTwoQuotientCoeff g) A
      (coPoissonReciprocalSeed (mellinHeadTest mellinTailCutoff s R))) atTop
      (𝓝 (primitiveMellinTail (fourierBoundaryPrimitive (degreeTwoQuotientCoeff g)) A
        (mellinReciprocalCutoff mellinTailCutoff) (1 - s))) :=
  tendsto_fourierBoundaryPairing_reciprocal_head
    (degreeTwoQuotientCoeff_summable_shift_square hD) isMellinTailCutoff_mellinTailCutoff A hs

/-- The exact Mellin identity for the actual compact-test inversion defect. -/
theorem degreeTwoQuotient_tendsto_cutoff_defect {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (A : ℂ) {s : ℂ}
    (hs1 : 1 < s.re) (hs2 : s.re < 2) :
    Tendsto (fun R : ℝ =>
      fourierBoundaryPairing (degreeTwoQuotientCoeff g) A (mellinHeadTest mellinTailCutoff s R) -
      fourierBoundaryPairing (degreeTwoQuotientCoeff g) A
        (coPoissonReciprocalSeed (mellinHeadTest mellinTailCutoff s R))) atTop
      (𝓝 ((s - 1) * (s - 2) * ((LSeries g s / riemannZeta s) * primitiveMellinGammaFactor s) -
        primitiveMellinTail (fourierBoundaryPrimitive (degreeTwoQuotientCoeff g)) A mellinTailCutoff s -
        primitiveMellinTail (fourierBoundaryPrimitive (degreeTwoQuotientCoeff g)) A
          (mellinReciprocalCutoff mellinTailCutoff) (1 - s))) := by
  have ho := (degreeTwoQuotient_cutoff_overlap hD A hs1 hs2).2
  have hh : primitiveMellinHead (fourierBoundaryPrimitive (degreeTwoQuotientCoeff g)) A mellinTailCutoff s =
      (s - 1) * (s - 2) * ((LSeries g s / riemannZeta s) * primitiveMellinGammaFactor s) -
        primitiveMellinTail (fourierBoundaryPrimitive (degreeTwoQuotientCoeff g)) A mellinTailCutoff s := by
    linear_combination ho
  have H := (degreeTwoQuotient_tendsto_mellinHead_pairing hD A hs1 hs2).sub
    (degreeTwoQuotient_tendsto_reciprocal_head_pairing hD A hs1)
  rwa [hh] at H
end RHTower.WeilHigherDenominator
