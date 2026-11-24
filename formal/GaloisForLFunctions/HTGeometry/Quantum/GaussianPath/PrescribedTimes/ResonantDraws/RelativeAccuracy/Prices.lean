import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateReturnSpacing

/-! # Precision and confidence costs compared with a rare Haar mass -/
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.RelativeAccuracy
noncomputable section

private theorem dilation_chord {h : ℝ} (hh : 0≤h) (hh' : h≤1) (m : ℕ) :
    (1+h)^m ≤ 1+((2:ℝ)^m-1)*h := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ,pow_succ]
    have hp : 0≤(2:ℝ)^m-1 := sub_nonneg.mpr (one_le_pow₀ (by norm_num))
    have hh₂ : h*h≤h := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hh' hh
    have hc := mul_le_mul_of_nonneg_left hh₂ hp
    have hi := mul_le_mul_of_nonneg_right ih (add_nonneg zero_le_one hh)
    linarith only [hc,hi]

/-- Accuracy and exceptional probabilities can be prescribed with any
number M of bits at least D. Both costs are relative to the rare scalar mass. -/
theorem scalar_snapshot_prices (D m M : ℕ) (hD : 8≤D) (hM : D≤M) (hm : m≤12*D) {x : ℝ}
    (hx : 1/(2:ℝ)^M≤x) (hhalf : x≤1/2) :
    let v := 1/(2:ℝ)^M
    let δ := 1/(2:ℝ)^(M^2)
    let h := 1/(2:ℝ)^(M^3)
    let p := zeroGateArcDensity D x
    (D:ℝ)*δ≤v*x ∧ 0<p ∧ p≤1 ∧ 3*h+2*((1+h)^m-1)≤p*v := by
  intro v δ h p
  have hd : 1≤D := by omega
  have hDp : 0<(D:ℝ) := Nat.cast_pos.mpr (by omega)
  have hx₀ : 0<x := (one_div_pos.mpr (pow_pos (by norm_num) _)).trans_le hx
  have hM₈ : 8≤M := hD.trans hM
  have hs : 8*M≤M^2 := by simpa only [pow_two] using Nat.mul_le_mul_right M hM₈
  have hc : 8*M^2≤M^3 := by simpa only [pow_succ _ 2,Nat.mul_comm M] using Nat.mul_le_mul_right (M^2) hM₈
  have hbound : (D:ℝ) ≤ (2:ℝ)^M := by exact_mod_cast hM.trans (Nat.lt_two_pow_self (n:=M)).le
  have hv : 0<v := one_div_pos.mpr (pow_pos (by norm_num) _)
  have ha : (D:ℝ)*δ ≤ v*x := calc
    _ ≤ 1/(2:ℝ)^(M+M) := by
      change (D:ℝ)*(1/(2:ℝ)^(M^2))≤_
      rw [mul_one_div,div_le_div_iff₀ (by positivity) (by positivity),one_mul]
      apply (mul_le_mul_of_nonneg_right hbound (by positivity : 0≤(2:ℝ)^(M+M))).trans
      rw [←pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    _ = v*v := by dsimp only [v]; rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hx hv.le
  have hdim : D≤2^(D-1) := by
    have hh := Nat.lt_two_pow_self (n:=D-1)
    omega
  have hupper : p≤1 := by
    change (D:ℝ)*x^(D-1) ≤ 1
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx₀.le hhalf _) hDp.le).trans
    rw [_root_.one_div_pow,mul_one_div,div_le_one (by positivity)]
    exact_mod_cast hdim
  have hh₀ : 0≤h := by dsimp only [h]; positivity
  have hh₁ : h≤1 := (div_le_one (pow_pos (by norm_num) _)).mpr (one_le_pow₀ (by norm_num))
  have hres := dilation_chord hh₀ hh₁ m
  have hprice : 3*h+2*((1+h)^m-1)≤(2:ℝ)^(m+3)*h := by
    rw [pow_add]
    nlinarith only [hres,hh₀,mul_le_mul_of_nonneg_right (one_le_pow₀ (n:=m) (by norm_num : (1:ℝ)≤2)) hh₀]
  have hlow : δ≤p := calc
    _ ≤ v^(D-1) := by
      dsimp only [δ,v]
      rw [_root_.one_div_pow,←pow_mul]
      exact one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by rw [pow_two]; exact Nat.mul_le_mul_left M ((Nat.sub_le _ _).trans hM)))
    _ ≤ x^(D-1) := pow_le_pow_left₀ hv.le hx _
    _ ≤ p := le_mul_of_one_le_left (pow_nonneg hx₀.le _) (by exact_mod_cast hd)
  have hcoin : (2:ℝ)^(m+3)*h≤δ*v := by
    change (2:ℝ)^(m+3)*(1/(2:ℝ)^(M^3))≤(1/(2:ℝ)^(M^2))*(1/(2:ℝ)^M)
    rw [show (1/(2:ℝ)^(M^2))*(1/(2:ℝ)^M)=1/(2:ℝ)^(M^2+M) by rw [pow_add]; ring,
      mul_one_div,div_le_div_iff₀ (by positivity) (by positivity),one_mul,←pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  exact ⟨ha,mul_pos hDp (pow_pos hx₀ _),hupper,hprice.trans (hcoin.trans (mul_le_mul_of_nonneg_right hlow hv.le))⟩

#print axioms scalar_snapshot_prices
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.RelativeAccuracy
