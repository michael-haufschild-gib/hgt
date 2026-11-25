import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints.Geometry

/-! # Asymptotic log partition function of a fixed occupation sector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints

open Filter Topology Set

private theorem negligible_log {u A : Ioi (0:ℝ) → ℝ} (hu : Tendsto u criticalApproach atTop)
    {a : ℝ} (ha : 0 < a) (hA : Tendsto A criticalApproach (𝓝 a)) :
    Tendsto (fun h => Real.log (A h)/u h) criticalApproach (𝓝 0) := by
  have H := ((Real.continuousAt_log ha.ne').tendsto.comp hA).mul (tendsto_inv_atTop_zero.comp hu)
  simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using H

private theorem log_multiplier {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (t : ℝ) :
    Real.log (Real.exp (u*t)*v)/u = t+Real.log v/u := by
  rw [Real.log_mul (Real.exp_pos _).ne' hv.ne',Real.log_exp,add_div,mul_div_cancel_left₀ _ hu.ne']

/-- Positive mass arbitrarily near the extremal exponent identifies the normalized logarithm. -/
private theorem logarithmic_limit {u A D : Ioi (0:ℝ) → ℝ} (hu : Tendsto u criticalApproach atTop)
    {a M : ℝ} (ha : 0 < a) (hA : Tendsto A criticalApproach (𝓝 a))
    (hU : ∀ᶠ h in criticalApproach, D h ≤ Real.exp (u h*M)*A h)
    (hL : ∀ z < M, ∃ t > z, ∃ (B : Ioi (0:ℝ) → ℝ) (v : ℝ), 0 < v ∧ Tendsto B criticalApproach (𝓝 v) ∧
      ∀ᶠ h in criticalApproach, Real.exp (u h*t)*B h ≤ D h) :
    Tendsto (fun h => Real.log (D h)/u h) criticalApproach (𝓝 M) := by
  have hup := hu.eventually_gt_atTop 0
  apply tendsto_order.mpr
  constructor
  · intro z hz
    obtain ⟨t,ht,B,v,hv,hB,hl⟩ := hL z hz
    have htend : Tendsto (fun h => t+Real.log (B h)/u h) criticalApproach (𝓝 t) := by
      simpa only [add_zero] using (negligible_log hu hv hB).const_add t
    filter_upwards [htend.eventually_const_lt ht,hB.eventually_const_lt hv,hup,hl] with h ht' hb hu' hl'
    apply ht'.trans_le
    rw [← log_multiplier hu' hb]
    exact div_le_div_of_nonneg_right (Real.log_le_log (mul_pos (Real.exp_pos _) hb) hl') hu'.le
  · intro z hz
    obtain ⟨t,_,B,v,hv,hB,hl⟩ := hL (M-1) (sub_lt_self M zero_lt_one)
    have htend : Tendsto (fun h => M+Real.log (A h)/u h) criticalApproach (𝓝 M) := by
      simpa only [add_zero] using (negligible_log hu ha hA).const_add M
    filter_upwards [htend.eventually_lt_const hz,hA.eventually_const_lt ha,hB.eventually_const_lt hv,hup,hl,hU]
      with h ht' ha' hb hu' hl' hU'
    apply lt_of_le_of_lt _ ht'
    rw [← log_multiplier hu' ha']
    exact div_le_div_of_nonneg_right (Real.log_le_log ((mul_pos (Real.exp_pos _) hb).trans_le hl') hU') hu'.le

/-- The lower endpoint determines the exponential cost of the count sector at positive diverging drift. -/
theorem cooling_log_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) {u : Ioi (0:ℝ) → ℝ}
    (hu : Tendsto u criticalApproach atTop) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun h => Real.log (coefficient (added c d h) (1+u h*h.val) k)/u h) criticalApproach (𝓝 (-(k*c))) := by
  apply logarithmic_limit hu (critical_limit_pos hc hcd k) (coefficient_limit hc hcd k)
  · exact (hu.eventually_ge_atTop 0).mono fun h hh => (cooling_bounds c d h hh k).2
  · intro z hz
    obtain ⟨w,hw,hwd,hwz⟩ := inner_width hcd (sub_pos.mpr hz) hk
    let b := c+w
    have hcb : c < b := lt_add_of_pos_right c hw
    have hbd : b ≤ d := by dsimp [b]; linarith only [hwd]
    refine ⟨-(k*b),by dsimp [b]; nlinarith only [hwz],_,_,critical_limit_pos hc hcb k,coefficient_limit hc hcb k,?_⟩
    filter_upwards [hu.eventually_ge_atTop 0] with h hh
    exact (cooling_bounds c b h hh k).1.trans (coefficient_mono (subband le_rfl hbd h) _ h k)

/-- Negative diverging drift gives the exponential gain at the upper band edge. -/
theorem heating_log_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) {u : Ioi (0:ℝ) → ℝ}
    (hu : Tendsto u criticalApproach atTop) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun h => Real.log (coefficient (added c d h) (1-u h*h.val) k)/u h) criticalApproach (𝓝 (k*d)) := by
  apply logarithmic_limit hu (critical_limit_pos hc hcd k) (coefficient_limit hc hcd k)
  · exact (hu.eventually_ge_atTop 0).mono fun h hh => (heating_bounds c d h hh k).2
  · intro z hz
    obtain ⟨w,hw,hwd,hwz⟩ := inner_width hcd (sub_pos.mpr hz) hk
    let b := d-w
    have hcb : c ≤ b := by dsimp [b]; linarith only [hwd]
    have hbd : b < d := sub_lt_self _ hw
    refine ⟨k*b,by dsimp [b]; nlinarith only [hwz],_,_,critical_limit_pos (hc.trans_le hcb) hbd k,
      coefficient_limit (hc.trans_le hcb) hbd k,?_⟩
    filter_upwards [hu.eventually_ge_atTop 0] with h hh
    exact (heating_bounds b d h hh k).1.trans (coefficient_mono (subband hcb le_rfl h) _ h k)

/-- Limiting pressure of the finite k-mode sector as a function of inverse temperature. -/
def pressure (c d : ℝ) (k : ℕ) (s : ℝ) := if s ≤ 1 then (1-s)*(k*d) else (1-s)*(k*c)

theorem pressure_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (s : ℝ) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun h : Ioi (0:ℝ) => h.val*Real.log (coefficient (added c d h) s k)) criticalApproach
      (𝓝 (pressure c d k s)) := by
  have hv : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  have hinv := tendsto_inv_nhdsGT_zero.comp hv
  rcases lt_trichotomy s 1 with hs | rfl | hs
  · have ht := sub_pos.mpr hs
    have H := (heating_log_limit hc hcd (hinv.const_mul_atTop ht) hk).const_mul (1-s)
    rw [pressure,if_pos hs.le]
    apply H.congr
    intro h
    change (1-s)*(Real.log (coefficient (added c d h) (1-(1-s)*h.val⁻¹*h.val) k)/((1-s)*h.val⁻¹)) = _
    rw [mul_assoc,inv_mul_cancel₀ (show 0 < h.val from h.property).ne',mul_one,sub_sub_cancel]
    field_simp [ht.ne',(show 0 < h.val from h.property).ne']
  · have H := (hv.mono_right nhdsWithin_le_nhds).mul
      ((Real.continuousAt_log (critical_limit_pos hc hcd k).ne').tendsto.comp (coefficient_limit hc hcd k))
    rw [pressure,if_pos le_rfl,sub_self,zero_mul]
    rw [zero_mul] at H
    exact H
  · have ht := sub_pos.mpr hs
    have H := (cooling_log_limit hc hcd (hinv.const_mul_atTop ht) hk).const_mul (s-1)
    rw [pressure,if_neg hs.not_ge,show (1-s)*(k*c) = (s-1)*(-(k*c)) by ring]
    apply H.congr
    intro h
    change (s-1)*(Real.log (coefficient (added c d h) (1+(s-1)*h.val⁻¹*h.val) k)/((s-1)*h.val⁻¹)) = _
    rw [show 1+(s-1)*h.val⁻¹*h.val = s by rw [mul_assoc,inv_mul_cancel₀ (show 0 < h.val from h.property).ne',mul_one]; ring]
    field_simp [ht.ne',(show 0 < h.val from h.property).ne']

#print axioms cooling_log_limit
#print axioms heating_log_limit
#print axioms pressure_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints
