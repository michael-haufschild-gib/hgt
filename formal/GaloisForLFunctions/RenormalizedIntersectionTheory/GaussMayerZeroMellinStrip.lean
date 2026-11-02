import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringCharge
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCoreMellin

/-!
# Exact Mellin strip of the scattering core

The incoming zeta charge controls the Mellin endpoints away from zeta zeros.
At a zero, the nonzero outgoing charge determines the larger convergence strip.
-/

open Complex Set Filter MeasureTheory Asymptotics
open scoped Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerScatteringCore MayerScatteringCharge
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerZeroMellinStrip

private theorem cpow_tendsto_zero {v : ℂ} (hv : v.re < 0) :
    Tendsto (fun a : ℝ => (a : ℂ)^v) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h : Tendsto (fun a : ℝ => a^v.re) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hv)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  exact (Complex.norm_cpow_eq_rpow_re_of_pos ha v).symm

/-- The incoming charge is recovered by the weight `a^w` throughout the critical strip. -/
theorem core_incoming_limit {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) :
    Tendsto (fun a : ℝ => (a : ℂ)^w*fieldCore w a) atTop (𝓝 (-riemannZeta w)) := by
  have hp := cpow_tendsto_zero (v := w-1) (by simpa only [Complex.sub_re,Complex.one_re] using sub_neg.mpr hw1)
  have h := ((hp.mul (scaledTail_tendsto_zero hw)).sub_const (riemannZeta w)).sub
    (hp.const_mul (scatteringCoefficient w))
  simp only [mul_zero,zero_sub,sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [fieldCore_eq_tail hw him ha,Complex.cpow_sub _ _ haC,Complex.cpow_one,
    Complex.cpow_neg,Complex.cpow_neg_one]
  have hpC : (a : ℂ)^w ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl haC)
  field_simp

/-- A nonzero power-scaled limit forces a strict upper bound on any absolute Mellin exponent. -/
private theorem mellin_re_lt_of_scaled_limit {f : ℝ → ℂ} {κ L : ℝ} {u : ℂ}
    (hL : 0 < L) (hl : Tendsto (fun a : ℝ => a^κ*‖f a‖) atTop (𝓝 L))
    (hf : MellinConvergent f u) : u.re < κ := by
  have he : ∀ᶠ a : ℝ in atTop, L/2 < a^κ*‖f a‖ :=
    hl.eventually (lt_mem_nhds (show L/2 < L from by linarith only [hL]))
  obtain ⟨A,hA⟩ := eventually_atTop.mp he
  let B : ℝ := max A 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hn : IntegrableOn (fun a : ℝ => ‖(a : ℂ)^(u-1) • f a‖) (Ioi 0) := hf.norm
  have hi : IntegrableOn (fun a : ℝ => (2/L)*‖(a : ℂ)^(u-1) • f a‖) (Ioi B) :=
    (hn.mono_set (Ioi_subset_Ioi hB.le)).const_mul (2/L)
  have hm : Measurable (fun a : ℝ => a^(u.re-κ-1)) := by fun_prop
  have hg : IntegrableOn (fun a : ℝ => a^(u.re-κ-1)) (Ioi B) := by
    apply hi.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have ha0 : 0 < a := hB.trans ha
    have haA : A ≤ a := (le_max_left _ _).trans ha.le
    have hlow := (hA a haA).le
    rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos ha0 _)]
    change a^(u.re-κ-1) ≤ 2/L*‖(a : ℂ)^(u-1) • f a‖
    rw [norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos ha0,Complex.sub_re,Complex.one_re]
    have heq : a^(u.re-1)=a^(u.re-κ-1)*a^κ := by
      rw [← Real.rpow_add ha0]
      congr 1
      ring
    rw [heq]
    have hpow := Real.rpow_pos_of_pos ha0 (u.re-κ-1)
    have hscaled : 1 ≤ 2/L*(a^κ*‖f a‖) := by
      rw [div_mul_eq_mul_div,le_div_iff₀ hL]
      nlinarith only [hlow]
    calc
      _ = a^(u.re-κ-1)*1 := (mul_one _).symm
      _ ≤ a^(u.re-κ-1)*(2/L*(a^κ*‖f a‖)) :=
        mul_le_mul_of_nonneg_left hscaled hpow.le
      _ = _ := by ring
  have hp := (integrableOn_Ioi_rpow_iff hB).mp hg
  linarith only [hp]

/-- Absolute convergence respects the exact reflection of the field. -/
theorem core_mellinConvergent_reflection {w u : ℂ} (hw : 0 < w.re) (him : 0 < w.im) :
    MellinConvergent (fieldCore w) u ↔ MellinConvergent (fieldCore w) (w-u) := by
  calc
    _ ↔ MellinConvergent (fun a : ℝ => (a : ℂ)^(-w) • fieldCore w a⁻¹) u := by
      apply integrableOn_congr_fun _ measurableSet_Ioi
      intro a ha
      dsimp only
      rw [fieldCore_reciprocity hw him ha]
      simp only [one_div,smul_eq_mul]
    _ ↔ MellinConvergent (fun a : ℝ => fieldCore w a⁻¹) (u + -w) :=
      MellinConvergent.cpow_smul
    _ ↔ MellinConvergent (fieldCore w) (w-u) := by
      simpa only [Real.rpow_neg_one,Complex.ofReal_neg,Complex.ofReal_one,div_neg,div_one,
        show -(u + -w)=w-u by ring] using
        (MellinConvergent.comp_rpow (f := fieldCore w) (s := u + -w)
          (a := -1) (by norm_num))

/-- The literal Mellin integral has reflection parameter `w-u`. -/
theorem core_mellin_reflection {w u : ℂ} (hw : 0 < w.re) (him : 0 < w.im) :
    mellin (fieldCore w) u = mellin (fieldCore w) (w-u) := by
  calc
    _ = mellin (fun a : ℝ => (a : ℂ)^(-w) • fieldCore w a⁻¹) u := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a ha
      dsimp only
      rw [fieldCore_reciprocity hw him ha]
      simp only [one_div,smul_eq_mul]
    _ = mellin (fun a : ℝ => fieldCore w a⁻¹) (u + -w) := mellin_cpow_smul _ _ _
    _ = mellin (fieldCore w) (w-u) := by
      rw [mellin_comp_inv]
      congr 1
      ring

/-- The actual field is locally integrable away from its height endpoints. -/
theorem core_locallyIntegrable {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) : LocallyIntegrableOn (fieldCore w) (Ioi 0) := by
  have hh0 : 0 < (w/2).re := by simp only [Complex.div_ofNat_re]; linarith only [hw]
  have hh1 : (w/2).re < 1 := by simp only [Complex.div_ofNat_re]; linarith only [hw1]
  have he : w-w/2=w/2 := by ring
  have hc := (MayerCoreMellin.core_hasMellin hh0 hh1 (by simpa only [he] using hh0)
    (by simpa only [he] using hh1) him).1
  have hi := hc.locallyIntegrableOn.continuousOn_smul isOpen_Ioi.isLocallyClosed
    (g := fun a : ℝ => (a : ℂ)^(1-w/2))
    (continuousOn_of_forall_continuousAt (fun a ha =>
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ha.ne')))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  rw [smul_smul,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne')]
  simp only [show 1-w/2+(w/2-1)=0 by ring,Complex.cpow_zero,one_smul]

private theorem tail_nonneg (w : ℂ) : 0 ≤ tailCoefficient w :=
  div_nonneg (_root_.RHTower.tailConst_nonneg _) (by positivity)

/-- Vanishing of the incoming charge gives decay `O(a⁻¹)` at infinity. -/
theorem core_zero_isBigO_top {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    (hz : riemannZeta w=0) : fieldCore w =O[atTop] (fun a : ℝ => a^(-1 : ℝ)) := by
  apply IsBigO.of_bound (‖scatteringCoefficient w‖+tailCoefficient w)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have h := core_large_bound hw him ha
  rw [hz,norm_zero,zero_mul,zero_add] at h
  rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos ha0 _),add_mul]
  apply h.trans
  have hp : a^(-w.re/2-1) ≤ a^(-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ha (by linarith only [hw])
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (tail_nonneg w))

/-- Reciprocity turns outgoing decay into `O(a^(1-Re w))` at zero. -/
theorem core_zero_isBigO_zero {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    (hz : riemannZeta w=0) :
    fieldCore w =O[𝓝[>] 0] (fun a : ℝ => a^(-(w.re-1))) := by
  apply IsBigO.of_bound (‖scatteringCoefficient w‖+tailCoefficient w)
  filter_upwards [eventually_mem_nhdsWithin,show ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 from
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with a ha ha1
  have h := core_small_bound hw him ha ha1.le
  rw [hz,norm_zero,zero_add] at h
  rw [show -(w.re-1)=1-w.re by ring,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ha _),add_mul]
  apply h.trans
  have hp : a^(1-w.re/2) ≤ a^(1-w.re) :=
    Real.rpow_le_rpow_of_exponent_ge ha ha1.le (by linarith only [hw])
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hp (tail_nonneg w))

/-- At a strip zeta zero, the ordinary Mellin integral converges on the enlarged strip. -/
theorem core_zero_mellinConvergent {w u : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w=0) (hu : w.re-1 < u.re) (hu1 : u.re < 1) :
    MellinConvergent (fieldCore w) u :=
  mellinConvergent_of_isBigO_rpow (core_locallyIntegrable hw hw1 him)
    (core_zero_isBigO_top hw him hz) hu1 (core_zero_isBigO_zero hw him hz) hu

private theorem core_nonzero_upper {w u : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w ≠ 0) (hf : MellinConvergent (fieldCore w) u) :
    u.re < w.re := by
  have hn : Tendsto (fun a : ℝ => a^w.re*‖fieldCore w a‖) atTop (𝓝 ‖riemannZeta w‖) := by
    have h := (core_incoming_limit hw hw1 him).norm
    simp only [norm_neg] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ha]
  exact mellin_re_lt_of_scaled_limit (norm_pos_iff.mpr hz) hn hf

private theorem core_zero_upper {w u : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w = 0) (hf : MellinConvergent (fieldCore w) u) :
    u.re < 1 := by
  have hn : Tendsto (fun a : ℝ => a^(1 : ℝ)*‖fieldCore w a‖) atTop (𝓝 ‖scatteringCoefficient w‖) := by
    have h := (core_charge_limit hw him hz).norm
    simp only [norm_neg] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,Real.rpow_one]
  exact mellin_re_lt_of_scaled_limit (norm_pos_iff.mpr (scatteringCoefficient_ne_zero hw1 him)) hn hf

/-- Away from a zeta zero, the two incoming charges give the exact open Mellin strip. -/
theorem core_mellinConvergent_iff_of_ne_zero {w u : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w ≠ 0) :
    MellinConvergent (fieldCore w) u ↔ 0 < u.re ∧ u.re < w.re := by
  constructor
  · intro hf
    have ht := core_nonzero_upper hw hw1 him hz hf
    have hr := core_nonzero_upper hw hw1 him hz ((core_mellinConvergent_reflection hw him).mp hf)
    simp only [Complex.sub_re] at hr
    exact ⟨by linarith only [hr],ht⟩
  · rintro ⟨hu,hu1⟩
    have hwu : 0 < (w-u).re := by simp only [Complex.sub_re]; linarith only [hu1]
    have hwu1 : (w-u).re < 1 := by simp only [Complex.sub_re]; linarith only [hu,hw1]
    exact (MayerCoreMellin.core_hasMellin hu (hu1.trans hw1) hwu hwu1 him).1

/-- A zeta zero enlarges the exact absolute-convergence strip by the missing incoming charges. -/
theorem core_mellinConvergent_iff_of_zero {w u : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) (hz : riemannZeta w = 0) :
    MellinConvergent (fieldCore w) u ↔ w.re-1 < u.re ∧ u.re < 1 := by
  constructor
  · intro hf
    have ht := core_zero_upper hw hw1 him hz hf
    have hr := core_zero_upper hw hw1 him hz ((core_mellinConvergent_reflection hw him).mp hf)
    simp only [Complex.sub_re] at hr
    exact ⟨by linarith only [hr],ht⟩
  · rintro ⟨hu,hu1⟩
    exact core_zero_mellinConvergent hw hw1 him hz hu hu1

/-- Absolute convergence of the unweighted multiplicative moment detects precisely the zeta zeros. -/
theorem core_mellinConvergent_zero_iff {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1)
    (him : 0 < w.im) : MellinConvergent (fieldCore w) 0 ↔ riemannZeta w=0 := by
  by_cases hz : riemannZeta w=0
  · simp only [hz,iff_true]
    exact core_zero_mellinConvergent hw hw1 him hz (by simp only [Complex.zero_re]; linarith only [hw1])
      (by norm_num)
  · rw [core_mellinConvergent_iff_of_ne_zero hw hw1 him hz]
    simp only [Complex.zero_re,lt_self_iff_false,false_and,hz]

#print axioms core_incoming_limit
#print axioms core_mellinConvergent_reflection
#print axioms core_mellin_reflection
#print axioms core_locallyIntegrable
#print axioms core_zero_isBigO_top
#print axioms core_zero_isBigO_zero
#print axioms core_zero_mellinConvergent
#print axioms core_mellinConvergent_iff_of_ne_zero
#print axioms core_mellinConvergent_iff_of_zero
#print axioms core_mellinConvergent_zero_iff

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerZeroMellinStrip
