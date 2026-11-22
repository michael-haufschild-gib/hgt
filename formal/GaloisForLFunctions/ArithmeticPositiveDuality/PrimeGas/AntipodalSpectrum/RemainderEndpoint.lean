import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RemainderDensity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RemainderSingularCount
import GaloisForLFunctions.RHTower.SchattenCriticalAsymptotic

/-!
# Critical singular values of the heat-weighted remainder

Inverting the occupation count determines each approximation number
asymptotically, including along degenerate shells. At critical temperature
the logarithmic trace and the thermal residue have the same coefficient.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks CopyExchange DyadicAperture.Binary Filter
open scoped Topology

/-- Inverting discrete reciprocal thresholds retains all jumps in the counting function. -/
private theorem inverse_count {A : ℕ → ℕ} {a : ℕ → ℝ} {D : ℝ}
    (hA : Monotone A) (hD : 0 < D) (hl : Tendsto (fun X : ℕ => (A X:ℝ)/X) atTop (𝓝 D))
    (hcut : ∀ X n : ℕ, 1/((X:ℝ)+1) < a n ↔ n < A X) :
    Tendsto (fun n : ℕ => a n*((n:ℝ)+1)) atTop (𝓝 D) := by
  classical
  have hnat : Tendsto (fun X : ℕ => (X:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hAr : Tendsto (fun X : ℕ => (A X:ℝ)) atTop atTop := by
    apply (hl.pos_mul_atTop hD hnat).congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with X hX
    exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hX.ne')
  have hex (n : ℕ) : ∃ X, n < A (X+1) := by
    obtain ⟨X,hX⟩ := (hAr.eventually_gt_atTop (n:ℝ)).exists
    exact ⟨X,(show n < A X by exact_mod_cast hX).trans_le (hA (Nat.le_succ _))⟩
  let K (n : ℕ) := Nat.find (hex n)
  have hi (n : ℕ) : n < A (K n+1) := Nat.find_spec (hex n)
  have hK : Tendsto K atTop atTop := by
    refine tendsto_atTop.2 fun R => (eventually_ge_atTop (A (R+1))).mono fun n hn => ?_
    by_contra! hk
    exact (hi n).not_ge ((hA (Nat.succ_le_succ hk.le)).trans hn)
  have hK' : Tendsto (fun n => K n+1) atTop atTop := tendsto_atTop_mono (fun n => Nat.le_succ (K n)) hK
  have hshift : Tendsto (fun X : ℕ => (A X:ℝ)/((X:ℝ)+2)) atTop (𝓝 D) := by
    have hden := tendsto_atTop_add_const_right _ (2:ℝ) hnat
    have hr := (tendsto_const_nhds (x := (2:ℝ))).div_atTop hden
    have ht := hl.mul ((tendsto_const_nhds (x := (1:ℝ))).sub hr)
    rw [sub_zero,mul_one] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with X hX
    change (A X:ℝ)/X*(1-2/((X:ℝ)+2)) = _
    field_simp [Nat.cast_ne_zero.mpr hX.ne']
    ring
  have hlo (n : ℕ) (hk : 0 < K n) : ¬n < A (K n) := by
    have hprev : K n-1 < K n := by omega
    have h := Nat.find_min (hex n) hprev
    change ¬n < A (K n-1+1) at h
    rwa [Nat.sub_add_cancel hk] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hshift.comp hK) (hl.comp hK')
  · filter_upwards [hK.eventually_gt_atTop 0] with n hk
    have ha := (hcut (K n+1) n).mpr (hi n)
    simp only [Nat.cast_add,Nat.cast_one] at ha
    rw [show (K n:ℝ)+1+1 = (K n:ℝ)+2 by ring] at ha
    change (A (K n):ℝ)/((K n:ℝ)+2) ≤ a n*((n:ℝ)+1)
    rw [div_eq_inv_mul,← one_div]
    exact mul_le_mul ha.le (by exact_mod_cast (Nat.le_of_not_gt (hlo n hk)).trans (Nat.le_succ n))
      (Nat.cast_nonneg _) ((by positivity : 0 < 1/((K n:ℝ)+2)).trans ha).le
  · filter_upwards [hK.eventually_gt_atTop 0] with n hk
    have ha := le_of_not_gt (fun he => hlo n hk ((hcut (K n) n).mp he))
    change a n*((n:ℝ)+1) ≤ (A (K n+1):ℝ)/(↑(K n+1):ℝ)
    rw [Nat.cast_add,Nat.cast_one,div_eq_inv_mul,← one_div]
    exact mul_le_mul ha (by exact_mod_cast hi n) (by positivity) (by positivity)

private theorem count_mono (t : ExceptionalTime) (j : ℕ) :
    Monotone (fun X => Nat.card (countingStates t j X)) := by
  intro X Y h
  exact Nat.card_le_card_of_injective
    (fun u : countingStates t j X => (⟨u.val,u.property.trans (Nat.pow_le_pow_left h 2)⟩ : countingStates t j Y))
    (fun _ _ he => Subtype.ext (congrArg (fun v : countingStates t j Y => v.val) he))

private theorem reciprocal_threshold (s : {z : ℂ // 0 < z.re}) (X : ℕ) :
    squareThreshold s.val X ^ (2*s.val.re)⁻¹ = 1/((X:ℝ)+1) := by
  rw [squareThreshold,norm_heat]
  change Real.exp (-s.val.re*Real.log (((X+1)^2:ℕ):ℝ)) ^ (2*s.val.re)⁻¹ = _
  rw [Nat.cast_pow,Real.log_pow,← Real.exp_mul]
  change Real.exp ((-s.val.re*(2*Real.log ((X+1:ℕ):ℝ)))*(2*s.val.re)⁻¹) = _
  rw [Nat.cast_add,Nat.cast_one,show (-s.val.re*(2*Real.log ((X:ℝ)+1)))*(2*s.val.re)⁻¹ = -Real.log ((X:ℝ)+1) by
    field_simp [s.property.ne'],Real.exp_neg,Real.exp_log (by positivity),one_div]

/-- At the reciprocal heat exponent the singular values, multiplied by their rank, tend to the shell density. -/
theorem remainder_endpoint_asymptotic (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 0 < z.re}) :
    Tendsto (fun n : ℕ => _root_.RHTower.approxNumber (dampedRemainder t j ⟨s.val,s.property.le⟩) n ^
      (2*s.val.re)⁻¹*((n:ℝ)+1)) atTop (𝓝 (2/((tailRadix t j).val-1:ℝ))) := by
  have hr : (1:ℝ) < (tailRadix t j).val := by exact_mod_cast radix_gt_one t j
  apply inverse_count (count_mono t j) (div_pos two_pos (sub_pos.mpr hr)) (remainder_count_density t j)
  intro X n
  rw [← reciprocal_threshold s X,Real.rpow_lt_rpow_iff (show 0 ≤ squareThreshold s.val X from norm_nonneg _) (_root_.RHTower.approxNumber_nonneg _ _)
    (inv_pos.mpr (mul_pos two_pos s.property))]
  exact threshold_lt_singular_iff t j s X n

/-- Individual singular values decay with exponent twice the real part of inverse temperature. -/
theorem remainder_singular_asymptotic (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 0 < z.re}) :
    Tendsto (fun n : ℕ => _root_.RHTower.approxNumber (dampedRemainder t j ⟨s.val,s.property.le⟩) n *
      ((n:ℝ)+1)^(2*s.val.re)) atTop (𝓝 ((2/((tailRadix t j).val-1:ℝ))^(2*s.val.re))) := by
  have hσ := mul_pos two_pos s.property
  have h := (remainder_endpoint_asymptotic t j s).rpow_const (p := 2*s.val.re) (Or.inr hσ.le)
  apply h.congr
  intro n
  rw [Real.mul_rpow (Real.rpow_nonneg (_root_.RHTower.approxNumber_nonneg _ _) _) (by positivity),
    ← Real.rpow_mul (_root_.RHTower.approxNumber_nonneg _ _),inv_mul_cancel₀ hσ.ne',Real.rpow_one]

theorem remainder_weak_endpoint (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 0 < z.re}) :
    _root_.RHTower.MemWeakSchattenClass (2*s.val.re)⁻¹ (dampedRemainder t j ⟨s.val,s.property.le⟩) :=
  _root_.RHTower.memWeakSchattenClass_of_tendsto_mul_succ (remainder_endpoint_asymptotic t j s)

theorem remainder_log_residue (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 0 < z.re}) :
    _root_.RHTower.HasSchattenLogResidue (2*s.val.re)⁻¹ (dampedRemainder t j ⟨s.val,s.property.le⟩)
      (2/((tailRadix t j).val-1:ℝ)) :=
  _root_.RHTower.hasSchattenLogResidue_of_tendsto_mul_succ (remainder_endpoint_asymptotic t j s)

/-- At every point of the critical line the ordinary logarithmic singular trace has the thermal residue. -/
theorem remainder_critical_log_trace (t : ExceptionalTime) (j : ℕ) (τ : ℝ) :
    let s : ℂ := ⟨1/2,τ⟩
    _root_.RHTower.HasSchattenLogResidue 1 (dampedRemainder t j ⟨s,by change (0:ℝ) ≤ 1/2; norm_num⟩)
      (2/((tailRadix t j).val-1:ℝ)) := by
  have h := remainder_log_residue t j ⟨⟨1/2,τ⟩,by change (0:ℝ) < 1/2; norm_num⟩
  convert h using 2
  norm_num

/-- Binary isometry is equivalent to weak trace membership with divergent singular-value sum. -/
theorem split_iff_weak_nontrace (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 0 < z.re}) :
    (∃ U : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, U f x = split s.val f x) ↔
      _root_.RHTower.MemWeakSchattenClass 1 (dampedRemainder t j ⟨s.val,s.property.le⟩) ∧
        ¬(dampedRemainder t j ⟨s.val,s.property.le⟩).IsTraceClass := by
  let p := (2*s.val.re)⁻¹
  have hp : 0 < p := inv_pos.mpr (mul_pos two_pos s.property)
  have hr : (1:ℝ) < (tailRadix t j).val := by exact_mod_cast radix_gt_one t j
  have hd := _root_.RHTower.exact_schattenDepth_of_tendsto_mul_succ hp (div_pos two_pos (sub_pos.mpr hr))
    (remainder_endpoint_asymptotic t j s)
  rw [split_isometric_iff]
  constructor
  · intro h
    have he : p = 1 := by simp [p,h]
    have hw := remainder_weak_endpoint t j s
    change _root_.RHTower.MemWeakSchattenClass p _ at hw
    rw [he] at hw
    exact ⟨hw,fun ht => hd.1 1 zero_lt_one he.ge (_root_.RHTower.IsTraceClass.memSchattenClass_one ht)⟩
  · rintro ⟨hw,ht⟩
    have he : p = 1 := le_antisymm
      (le_of_not_gt fun h => hd.1 p hp le_rfl (hw.memSchattenClass_of_lt zero_lt_one h))
      (le_of_not_gt fun h => ht (_root_.RHTower.MemSchattenClass.one_isTraceClass (hd.2 1 h)))
    have hh := inv_eq_one.mp he
    linarith only [hh]

#print axioms split_iff_weak_nontrace
#print axioms remainder_endpoint_asymptotic
#print axioms remainder_singular_asymptotic
#print axioms remainder_weak_endpoint
#print axioms remainder_log_residue
#print axioms remainder_critical_log_trace

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
