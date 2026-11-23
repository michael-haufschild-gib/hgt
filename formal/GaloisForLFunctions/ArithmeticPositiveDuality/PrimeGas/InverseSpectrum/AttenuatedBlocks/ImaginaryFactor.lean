import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.AttenuatedBlocks.ChordFactors

/-! # Nonzero imaginary time increases the matched physical coefficient -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- Attenuation for a half turn of the complex clock. -/
def halfTurnFraction {z : ℂ} (ht : z.im ≠ 0) : Ioo (0:ℝ) 1 :=
  ⟨Real.exp (-Real.pi/|z.im|),Real.exp_pos _,Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) (abs_pos.mpr ht))⟩

private theorem halfTurn_power {z : ℂ} (ht : z.im ≠ 0) :
    ((halfTurnFraction ht).val:ℂ)^z = -(((halfTurnFraction ht).val^z.re:ℝ):ℂ) := by
  let u := -Real.pi/|z.im|
  have hx : 0 < Real.exp u := Real.exp_pos _
  change ((Real.exp u:ℝ):ℂ)^z = -(((Real.exp u)^z.re:ℝ):ℂ)
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),← Complex.ofReal_log hx.le,
    Real.rpow_def_of_pos hx,Real.log_exp]
  have he : (u:ℂ)*z = ((u*z.re:ℝ):ℂ)+((u*z.im:ℝ):ℂ)*Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  rw [he,Complex.exp_add,← Complex.ofReal_exp]
  have hi : u*z.im = Real.pi ∨ u*z.im = -Real.pi := by
    rcases lt_or_gt_of_ne ht with ht' | ht'
    · left
      dsimp only [u]
      rw [abs_of_neg ht',neg_div_neg_eq,div_mul_cancel₀ _ ht]
    · right
      dsimp only [u]
      rw [abs_of_pos ht',div_mul_cancel₀ _ ht]
  rcases hi with hi | hi
  · rw [hi,Complex.exp_pi_mul_I,mul_neg_one]
  · rw [hi,Complex.ofReal_neg,neg_mul,Complex.exp_neg,Complex.exp_pi_mul_I,inv_neg,inv_one,mul_neg_one]

/-- A half turn supplies an explicit coefficient bound at every nonzero clock height. -/
theorem halfTurn_trace_factor (r : ℕ) {z : ℂ} (hz : 0 < z.re) (ht : z.im ≠ 0) {p K : ℝ} (hp : 0 < p)
    (hm : z.re*p = 2) (h : traceControlsAt (r+1) z p K) :
    ((r+1:ℕ):ℝ)^(p-1)*(1+(halfTurnFraction ht).val^z.re)^p / (1-(halfTurnFraction ht).val^2) ≤ K := by
  let t := halfTurnFraction ht
  have hD : 0 < 1-t.val^2 := by
    rw [show 1-t.val^2 = (1-t.val)*(1+t.val) by ring]
    exact mul_pos (sub_pos.mpr t.property.2) (add_pos zero_lt_one t.property.1)
  have he := matched_chord_factor r hz hp hm h ⟨t.val,t.property.1,t.property.2.le⟩
  change _*‖1-(t.val:ℂ)^z‖^p ≤ K*(1-t.val^2) at he
  rw [halfTurn_power ht,sub_neg_eq_add,← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,
    Real.norm_of_nonneg (add_nonneg zero_le_one (Real.rpow_nonneg t.property.1.le _))] at he
  exact (div_le_iff₀ hD).mpr he

/-- Even at a fixed missing rank no nonzero clock height can have the real-temperature coefficient. -/
theorem imaginary_matched_factor_strict (r : ℕ) {z : ℂ} (hz : 0 < z.re) (ht : z.im ≠ 0) {p K : ℝ}
    (hp : 0 < p) (hm : z.re*p = 2) (h : traceControlsAt (r+1) z p K) : ((r+1:ℕ):ℝ)^(p-1) < K := by
  let t := halfTurnFraction ht
  let R := ((r+1:ℕ):ℝ)^(p-1)
  have hR : 0 < R := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos r)) _
  have hpow : 1 < (1+t.val^z.re)^p := Real.one_lt_rpow (lt_add_of_pos_right _ (Real.rpow_pos_of_pos t.property.1 _)) hp
  have hD : 0 < 1-t.val^2 := by
    rw [show 1-t.val^2 = (1-t.val)*(1+t.val) by ring]
    exact mul_pos (sub_pos.mpr t.property.2) (add_pos zero_lt_one t.property.1)
  apply lt_of_lt_of_le _ (halfTurn_trace_factor r hz ht hp hm h)
  apply (lt_div_iff₀ hD).mpr
  apply mul_lt_mul_of_pos_left _ hR
  exact (sub_lt_self 1 (sq_pos_of_pos t.property.1)).trans hpow


/-- At a matched power the physical coefficient grows at least linearly with the clock height. -/
theorem imaginary_factor_height_lower (r : ℕ) {z : ℂ} (hz : 0 < z.re) (ht : z.im ≠ 0) {p K : ℝ}
    (hp : 0 < p) (hm : z.re*p = 2) (h : traceControlsAt (r+1) z p K) :
    ((r+1:ℕ):ℝ)^(p-1)*|z.im| ≤ 2*Real.pi*K := by
  let t := halfTurnFraction ht
  let R := ((r+1:ℕ):ℝ)^(p-1)
  have hR : 0 < R := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos r)) _
  have hK : 0 < K := hR.trans (imaginary_matched_factor_strict r hz ht hp hm h)
  have hD : 0 < 1-t.val^2 := by
    rw [show 1-t.val^2 = (1-t.val)*(1+t.val) by ring]
    exact mul_pos (sub_pos.mpr t.property.2) (add_pos zero_lt_one t.property.1)
  have hpow : 1 < (1+t.val^z.re)^p := Real.one_lt_rpow (lt_add_of_pos_right _ (Real.rpow_pos_of_pos t.property.1 _)) hp
  have hb := (div_le_iff₀ hD).mp (halfTurn_trace_factor r hz ht hp hm h)
  have hc : R ≤ K*(1-t.val^2) := (le_mul_of_one_le_right hR.le hpow.le).trans hb
  let u := -Real.pi/|z.im|
  have he := Real.add_one_le_exp (u+u)
  rw [Real.exp_add,← sq] at he
  have hd : 1-t.val^2 ≤ (2*Real.pi)/|z.im| := by
    change 1-(Real.exp u)^2 ≤ _
    calc
      1-(Real.exp u)^2 ≤ -(u+u) := by linarith only [he]
      _ = _ := by dsimp only [u]; ring
  have hu := hc.trans (mul_le_mul_of_nonneg_left hd hK.le)
  rw [← mul_div_assoc] at hu
  exact ((le_div_iff₀ (abs_pos.mpr ht)).mp hu).trans_eq (mul_comm K _)

#print axioms imaginary_factor_height_lower
#print axioms halfTurn_trace_factor
#print axioms imaginary_matched_factor_strict

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
