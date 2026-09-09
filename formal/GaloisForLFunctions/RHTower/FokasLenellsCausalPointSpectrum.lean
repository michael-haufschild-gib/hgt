import GaloisForLFunctions.RHTower.FokasLenellsCausalNeutralGenerator

/-! Exact point spectrum of the actual maximal causal generator: the open left half-plane. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual point spectrum, requiring a nonzero vector in the maximal generator domain. -/
def causalGeneratorPointSpectrum : Set ℂ :=
  {z | ∃ u : causalGeneratorDomain, u ≠ 0 ∧ causalGenerator u = z • u.val}

/-- Every imaginary-axis generator shift is injective, although it has no bounded inverse. -/
theorem causalComplexGeneratorShift_imaginary_injective (ω : ℝ) :
    Function.Injective (causalComplexGeneratorShift ((ω : ℂ)*I)) :=
  LinearMap.ker_eq_bot.mp (causalImaginaryGeneratorKernel_eq_bot ω)

/-- The actual maximal causal generator has trivial kernel. -/
theorem causalGenerator_injective : Function.Injective causalGenerator := by
  intro u v h
  apply causalComplexGeneratorShift_imaginary_injective 0
  change ((0 : ℂ)*I) • u.val-causalGenerator u = ((0 : ℂ)*I) • v.val-causalGenerator v
  simp only [zero_mul, zero_smul, zero_sub, h]

/-- Actual nonzero maximal-generator eigenvectors exist exactly at strictly negative real part. -/
theorem causalGenerator_mem_pointSpectrum_iff (z : ℂ) :
    z ∈ causalGeneratorPointSpectrum ↔ z.re < 0 := by
  constructor
  · rintro ⟨u, hu, hG⟩
    have hs : causalComplexGeneratorShift z u = 0 := by
      change z • u.val-causalGenerator u = 0
      rw [hG, sub_self]
    by_contra hn
    have hz : 0 ≤ z.re := le_of_not_gt hn
    rcases lt_or_eq_of_le hz with hp | hz
    · apply hu
      apply causalComplexGeneratorShift_injective ⟨z, hp⟩
      rw [hs, map_zero]
    · have he : z = (z.im : ℂ)*I := by
        apply Complex.ext <;> simp [← hz]
      apply hu
      apply causalComplexGeneratorShift_imaginary_injective z.im
      rw [map_zero, ← he]
      exact hs
  · intro hz
    exact ⟨causalLeftEigenvector ⟨z, hz⟩, causalLeftEigenvector_ne_zero ⟨z, hz⟩,
      causalGenerator_leftEigenvector ⟨z, hz⟩⟩

/-- The point spectrum is the open left half-plane; the imaginary boundary has no eigenvectors. -/
theorem causalGeneratorPointSpectrum_eq_openLeftHalfPlane :
    causalGeneratorPointSpectrum = {z : ℂ | z.re < 0} := Set.ext causalGenerator_mem_pointSpectrum_iff

end
end RHTower.FokasLenells
