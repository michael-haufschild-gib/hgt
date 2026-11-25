import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FirstReturnDates

/-! # Translating a short forecast window into finitely many spectral gap tests -/

open Real Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
noncomputable section

/-- A spectral gap of size at most L permits only finitely many closing
windings near T. For each winding the error in the forecast gap is at most
L/T times the error in the absolute date. -/
theorem winding_forecast {T L x : ℝ} (hT : 0<T) (hL : 0≤L) (hx : x∈Icc (0:ℝ) 1) :
    ∃ F : Finset ℤ, ∀ (v g : ℝ) (n : ℤ), 0<v → |v-T|≤1 → |g|≤L →
      g=(2*π)*((n:ℝ)+x)/v → n∈F ∧ |(2*π)*((n:ℝ)+x)/T-g|≤L/T*|v-T| := by
  let M := ⌈(T+1)*L+1⌉₊
  refine ⟨Finset.Icc (-(M:ℤ)) (M:ℤ),fun v g n hv ht hg he => ?_⟩
  have h₁ : (2*π)*((n:ℝ)+x)=g*v := ((eq_div_iff hv.ne').mp he).symm
  have h₂ : |(n:ℝ)+x|≤(T+1)*L := calc
    _ ≤ |2*π|*|(n:ℝ)+x| := le_mul_of_one_le_left (abs_nonneg _) (by
      rw [abs_of_pos two_pi_pos]; linarith only [pi_gt_three])
    _ = |g|*v := by rw [←abs_mul,h₁,abs_mul,abs_of_pos hv]
    _ ≤ L*(T+1) := mul_le_mul hg (by linarith only [(abs_le.mp ht).2]) hv.le hL
    _ = _ := mul_comm _ _
  have hM := Nat.le_ceil ((T+1)*L+1)
  have hn : |(n:ℝ)|≤(M:ℝ) := calc
    _ = |((n:ℝ)+x)-x| := by rw [add_sub_cancel_right]
    _ ≤ |(n:ℝ)+x|+|x| := abs_sub _ _
    _ ≤ (T+1)*L+1 := add_le_add h₂ ((abs_of_nonneg hx.1).trans_le hx.2)
    _ ≤ _ := hM
  have hl : -(M:ℤ)≤n := by exact_mod_cast (abs_le.mp hn).1
  have hu : n≤(M:ℤ) := by exact_mod_cast (abs_le.mp hn).2
  refine ⟨Finset.mem_Icc.mpr ⟨hl,hu⟩,?_⟩
  have hfrac : (2*π)*((n:ℝ)+x)/T-g=g/T*(v-T) := by rw [h₁]; field_simp; ring
  rw [hfrac,abs_mul,abs_div,abs_of_pos hT]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hg hT.le) (abs_nonneg _)

#print axioms winding_forecast
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
