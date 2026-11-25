import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FirstReturnDates

/-! # Translating a short forecast window into finitely many spectral gap tests -/

open Real Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
noncomputable section

/-- Integer turns allowed by the time and gap bounds, with one extra turn for the closing angle. -/
def windingBox (T L : ℝ) : Finset ℤ :=
  let m := ⌈(T+1)*L+1⌉₊
  Finset.Icc (-(m:ℤ)) (m:ℤ)

theorem windingBox_card {T L : ℝ} (hT : 0≤T) (hL : 0≤L) :
    ((windingBox T L).card:ℝ)≤2*(T+1)*L+5 := by
  let m := ⌈(T+1)*L+1⌉₊
  have hm : (windingBox T L).card=2*m+1 := by
    rw [windingBox,Int.card_Icc]
    change (↑m+1-(-↑m):ℤ).toNat=_
    omega
  rw [hm,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
  have h := Nat.ceil_lt_add_one (by positivity : 0≤(T+1)*L+1)
  change (m:ℝ)<_ at h
  linarith only [h]

/-- A spectral gap of size at most L permits only finitely many closing
windings near T. For each winding the error in the forecast gap is at most
L/T times the error in the absolute date. -/
theorem winding_forecast {T L x : ℝ} (hT : 0<T) (hL : 0≤L) (hx : x∈Icc (0:ℝ) 1) :
    ∀ (v g : ℝ) (n : ℤ), 0<v → |v-T|≤1 → |g|≤L →
      g=(2*π)*((n:ℝ)+x)/v → n∈windingBox T L ∧ |(2*π)*((n:ℝ)+x)/T-g|≤L/T*|v-T| := by
  let M := ⌈(T+1)*L+1⌉₊
  intro v g n hv ht hg he
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
  have hfrac : (2*π)*((n:ℝ)+x)/T-g=g/T*(v-T) := by rw [h₁]; field_simp [hT.ne'] <;> ring
  rw [hfrac,abs_mul,abs_div,abs_of_pos hT]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hg hT.le) (abs_nonneg _)

#print axioms winding_forecast
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
