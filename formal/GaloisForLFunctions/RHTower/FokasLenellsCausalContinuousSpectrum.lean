import GaloisForLFunctions.RHTower.FokasLenellsCausalImaginaryRange
import GaloisForLFunctions.RHTower.FokasLenellsCausalGeneratorSpectrum

/-! Complete spectral partition of the actual causal generator: open-left point spectrum,
imaginary-axis continuous spectrum, open-right resolvent, and no residual spectrum. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem left_shift_not_injective (z : {z : ℂ // z.re < 0}) :
    ¬ Function.Injective (causalComplexGeneratorShift z.val) := by
  intro h
  apply causalLeftEigenvector_ne_zero z
  apply h
  have hs : causalComplexGeneratorShift z.val (causalLeftEigenvector z) = 0 := by
    change z.val • (causalLeftEigenvector z).val-causalGenerator (causalLeftEigenvector z) = 0
    rw [causalGenerator_leftEigenvector, sub_self]
  rw [hs, map_zero]

/-- The actual maximal-domain shift is injective exactly on the closed right half-plane. -/
theorem causalComplexGeneratorShift_injective_iff (z : ℂ) :
    Function.Injective (causalComplexGeneratorShift z) ↔ 0 ≤ z.re := by
  constructor
  · intro h
    by_contra hn
    exact left_shift_not_injective ⟨z, lt_of_not_ge hn⟩ h
  · intro hz
    rcases lt_or_eq_of_le hz with hp | hz
    · exact causalComplexGeneratorShift_injective ⟨z, hp⟩
    · have he : z = (z.im : ℂ)*I := by apply Complex.ext <;> simp [← hz]
      rw [he]
      exact causalComplexGeneratorShift_imaginary_injective z.im

/-- Continuous spectrum of the actual unbounded generator: injective shift with dense proper range. -/
def causalGeneratorContinuousSpectrum : Set ℂ :=
  {z | Function.Injective (causalComplexGeneratorShift z) ∧
    DenseRange (causalComplexGeneratorShift z) ∧
    ¬ Function.Surjective (causalComplexGeneratorShift z)}

/-- Residual spectrum of the actual unbounded generator: injective shift with nondense range. -/
def causalGeneratorResidualSpectrum : Set ℂ :=
  {z | Function.Injective (causalComplexGeneratorShift z) ∧
    ¬ DenseRange (causalComplexGeneratorShift z)}

/-- A complex value belongs to the actual continuous spectrum exactly when its real part vanishes. -/
theorem causalGenerator_mem_continuousSpectrum_iff (z : ℂ) :
    z ∈ causalGeneratorContinuousSpectrum ↔ z.re = 0 := by
  constructor
  · rintro ⟨hi, _, hs⟩
    have hz := (causalComplexGeneratorShift_injective_iff z).1 hi
    apply le_antisymm _ hz
    by_contra hn
    exact hs (causalComplexGeneratorShift_bijective ⟨z, lt_of_not_ge hn⟩).2
  · intro hz
    have he : z = (z.im : ℂ)*I := by apply Complex.ext <;> simp [hz]
    rw [he]
    exact ⟨causalComplexGeneratorShift_imaginary_injective z.im,
      causalComplexGeneratorShift_imaginary_denseRange z.im,
      causalComplexGeneratorShift_imaginary_not_surjective z.im⟩

/-- The whole imaginary axis is the actual continuous spectrum. -/
theorem causalGeneratorContinuousSpectrum_eq_imaginaryAxis :
    causalGeneratorContinuousSpectrum = {z : ℂ | z.re = 0} :=
  Set.ext causalGenerator_mem_continuousSpectrum_iff

/-- The actual causal generator has no residual spectrum anywhere in the complex plane. -/
theorem causalGeneratorResidualSpectrum_eq_empty : causalGeneratorResidualSpectrum = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hi, hd⟩ := hz
  have hz := (causalComplexGeneratorShift_injective_iff z).1 hi
  apply hd
  rcases lt_or_eq_of_le hz with hp | hz
  · intro u
    obtain ⟨v, hv⟩ := (causalComplexGeneratorShift_bijective ⟨z, hp⟩).2 u
    exact subset_closure ⟨v, hv⟩
  · have he : z = (z.im : ℂ)*I := by apply Complex.ext <;> simp [← hz]
    rw [he]
    exact causalComplexGeneratorShift_imaginary_denseRange z.im

/-- Every spectral value is either an actual eigenvalue or a continuous-spectrum boundary value. -/
theorem causalGeneratorSpectrum_eq_point_union_continuous :
    causalGeneratorSpectrum = causalGeneratorPointSpectrum ∪ causalGeneratorContinuousSpectrum := by
  apply Set.ext
  intro z
  simp only [Set.mem_union, causalGenerator_mem_spectrum_iff,
    causalGenerator_mem_pointSpectrum_iff, causalGenerator_mem_continuousSpectrum_iff]
  exact le_iff_lt_or_eq

end
end RHTower.FokasLenells
