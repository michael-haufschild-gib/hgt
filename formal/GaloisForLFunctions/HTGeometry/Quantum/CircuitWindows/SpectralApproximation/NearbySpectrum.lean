import GaloisForLFunctions.HTGeometry.NormalResolventDistance
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Spectral points detectable at fixed operator error -/
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation
noncomputable section

/-- If a normal approximant is within radius r of an operator, its
spectrum meets the open r-ball about each spectral point of the operator. -/
theorem nearby_spectral_point {A : Type*} [CStarAlgebra A] {U V : A} [IsStarNormal V]
    {z : ℂ} (hz : z ∈ spectrum ℂ U) {r : ℝ} (h : ‖U-V‖ < r) :
    ∃ w ∈ spectrum ℂ V, ‖z-w‖ < r := by
  have hr := (norm_nonneg _).trans_lt h
  by_contra! hfar
  have hn : z ∉ spectrum ℂ V := fun hz' => by simpa only [sub_self,norm_zero,not_le.mpr hr] using hfar z hz'
  let D := algebraMap ℂ A z-V
  have hu : IsUnit D := spectrum.notMem_iff.mp hn
  have hinv : ‖Ring.inverse D‖ ≤ 1/r := norm_inverse_le_of_spectrum_far hr hfar hu
  have hsmall : ‖Ring.inverse D*(U-V)‖ < 1 := by
    apply (norm_mul_le ..).trans_lt
    apply (mul_le_mul_of_nonneg_right hinv (norm_nonneg _)).trans_lt
    rw [one_div,inv_mul_lt_iff₀ hr,mul_one]
    exact h
  have he : D*(1-Ring.inverse D*(U-V))=algebraMap ℂ A z-U := by
    rw [mul_sub,mul_one,←mul_assoc,Ring.mul_inverse_cancel D hu,one_mul]
    dsimp only [D]
    abel
  exact (spectrum.mem_iff.mp hz) (he ▸ hu.mul (isUnit_one_sub_of_norm_lt_one hsmall))

/-- A separated finite family of spectral points needs distinct
approximating spectral points. The bound is invariant under a change of basis. -/
theorem separated_spectrum_count {A : Type*} [CStarAlgebra A] {U V : A} [IsStarNormal V]
    {m : ℕ} (z : Fin m → ℂ) (hz : ∀ i, z i ∈ spectrum ℂ U) {r : ℝ} (h : ‖U-V‖ < r)
    (hsep : ∀ i j, i ≠ j → 2*r ≤ ‖z i-z j‖) :
    ∃ f : Fin m → ℂ, Function.Injective f ∧ ∀ i, f i ∈ spectrum ℂ V := by
  choose f hf hd using fun i => nearby_spectral_point (hz i) h
  refine ⟨f,fun i j he => ?_,hf⟩
  by_contra hne
  have ht := norm_sub_le_norm_sub_add_norm_sub (z i) (f i) (z j)
  rw [he,norm_sub_rev (f j) (z j)] at ht
  have hi := hd i
  rw [he] at hi
  linarith only [ht,hi,hd j,hsep i j hne]

#print axioms separated_spectrum_count
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation
