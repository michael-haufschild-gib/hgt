import GaloisForLFunctions.RHTower.ThetaSeamCouplingFamily
import GaloisForLFunctions.RHTower.XiStripInverseDecay
import GaloisForLFunctions.RHTower.EntireConstantShiftZeroCount
import GaloisForLFunctions.HTGeometry.RealNonnegativeZeroEvenOrder
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeLevelSpecificity
import GaloisForLFunctions.HTGeometry.DivisorPairing

/-!
# Zeros of the coupled theta renewal family

`X_r(z) = C(1 - r) + r Ξ(2z)` tends to `C(1 - r)` as `|Re z| → ∞`, uniformly on every bounded
horizontal strip. Hence for `r ≠ 1` each strip `|Im z| ≤ B` holds only finitely many zeros and
there are finitely many real zeros; for `0 < r < 1` there are nevertheless infinitely many nonreal
zeros (the level `-C(1 - r)/r ≠ 0` of `Ξ`), whose imaginary parts are unbounded. At `r = 0` there
are no zeros, at `r = 1` infinitely many real ones.
-/

open Complex Filter Topology Set Metric HurwitzZeta

namespace RHTower

noncomputable section

/-! ## Zeros at a nonphysical coupling -/

/-- `X_r(z) → C(1 - r)` as `|Re z| → ∞`, uniformly on every bounded horizontal strip. -/
theorem exists_forall_norm_thetaCouplingXi_sub_lt (r B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : ℝ, ∀ z : ℂ, |z.im| ≤ B → U ≤ |z.re| →
      ‖thetaCouplingXi r z - thetaSeamConst * (1 - r)‖ < ε := by
  rcases eq_or_ne r 0 with hr | hr
  · refine ⟨0, fun z _ _ => ?_⟩
    rw [hr, thetaCouplingXi_zero]; simpa using hε
  have hr' : 0 < |r| := abs_pos.mpr hr
  obtain ⟨U, hU⟩ := exists_forall_norm_XiC_lt (2 * B) (div_pos hε hr')
  refine ⟨|U|, fun z hz hzU => ?_⟩
  rw [thetaCouplingXi_eq, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h := hU (2 * z) (by
      rw [show (2 * z).im = 2 * z.im by simp, abs_mul]; norm_num; linarith) (by
      rw [show (2 * z).re = 2 * z.re by simp, abs_mul]
      have := le_abs_self U; have := abs_nonneg z.re; norm_num; linarith)
  calc |r| * ‖XiC (2 * z)‖ < |r| * (ε / |r|) := mul_lt_mul_of_pos_left h hr'
    _ = ε := by field_simp

theorem norm_thetaSeamConst_mul (r : ℝ) :
    ‖(thetaSeamConst : ℂ) * (1 - r)‖ = |thetaSeamConst * (1 - r)| := by
  rw [show (thetaSeamConst : ℂ) * (1 - r) = ((thetaSeamConst * (1 - r) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]

theorem thetaCouplingXi_not_eventually_zero {r : ℝ} (hr : r ≠ 1) (z : ℂ) :
    ¬ ∀ᶠ w in 𝓝 z, thetaCouplingXi r w = 0 := by
  have hC : 0 < |thetaSeamConst * (1 - r)| :=
    abs_pos.mpr (mul_ne_zero thetaSeamConst_pos.ne' (sub_ne_zero.mpr (Ne.symm hr)))
  obtain ⟨U, hU⟩ := exists_forall_norm_thetaCouplingXi_sub_lt r 0 hC
  intro hev
  have han : AnalyticOnNhd ℂ (thetaCouplingXi r) univ := fun w _ =>
    (differentiable_thetaCouplingXi r).analyticAt w
  have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ z) hev
  have h0 := hzero (mem_univ ((|U| : ℝ) : ℂ))
  have h1 := hU ((|U| : ℝ) : ℂ) (by simp) (by simp [le_abs_self])
  simp only [Pi.zero_apply] at h0
  rw [h0, zero_sub, norm_neg, norm_thetaSeamConst_mul] at h1
  exact lt_irrefl _ h1

/-- For `r ≠ 1`, only finitely many zeros of `X_r` lie in each strip `|Im z| ≤ B`. -/
theorem finite_thetaCouplingXi_zeros_strip {r : ℝ} (hr : r ≠ 1) (B : ℝ) :
    {z : ℂ | |z.im| ≤ B ∧ thetaCouplingXi r z = 0}.Finite := by
  have hC : 0 < |thetaSeamConst * (1 - r)| :=
    abs_pos.mpr (mul_ne_zero thetaSeamConst_pos.ne' (sub_ne_zero.mpr (Ne.symm hr)))
  obtain ⟨U, hU⟩ := exists_forall_norm_thetaCouplingXi_sub_lt r B hC
  have hfin := GaloisForLFunctions.HTGeometry.finite_zeros_of_isCompact isOpen_univ
    (differentiable_thetaCouplingXi r).differentiableOn
    (fun z _ => thetaCouplingXi_not_eventually_zero hr z)
    (isCompact_closedBall (0 : ℂ) (|U| + |B|)) (subset_univ _)
  refine hfin.subset fun z ⟨hzB, hz⟩ => ⟨?_, hz⟩
  have hre : |z.re| < |U| := by
    by_contra hc
    push Not at hc
    have h := hU z hzB (le_trans (le_abs_self U) hc)
    rw [hz, zero_sub, norm_neg, norm_thetaSeamConst_mul] at h
    exact lt_irrefl _ h
  rw [mem_closedBall, dist_zero_right]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ |U| + |B| := by linarith [le_abs_self B]

/-- For `r ≠ 1`, `X_r` has only finitely many real zeros. -/
theorem finite_thetaCouplingXi_real_zeros {r : ℝ} (hr : r ≠ 1) :
    {y : ℝ | thetaCouplingXi r y = 0}.Finite := by
  refine ((finite_thetaCouplingXi_zeros_strip hr 0).preimage
    Complex.ofReal_injective.injOn).subset fun y hy => ?_
  simp only [mem_preimage, mem_setOf_eq, Complex.ofReal_im, abs_zero, le_refl, true_and]
  exact hy

/-- **Infinitely many nonreal zeros at every coupling `0 < r < 1`.** -/
theorem infinite_thetaCouplingXi_nonreal_zeros {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    {z : ℂ | thetaCouplingXi r z = 0 ∧ z.im ≠ 0}.Infinite := by
  set L : ℂ := -((thetaSeamConst * (1 - r) : ℝ) : ℂ) / r
  have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hL : L ≠ 0 := div_ne_zero (neg_ne_zero.mpr (by
    exact_mod_cast (mul_pos thetaSeamConst_pos (by linarith)).ne')) hr0'
  have hinf := (XiC_level_specificity hL).2
  refine (hinf.image (f := fun w : ℂ => w / 2) fun a _ b _ h => by
    simpa using h).mono ?_
  rintro _ ⟨w, ⟨hw, him⟩, rfl⟩
  refine ⟨?_, by simpa using him⟩
  rw [thetaCouplingXi_eq, show (2 : ℂ) * (w / 2) = w by ring, hw]
  simp only [L]
  push_cast
  field_simp
  ring

theorem infinite_thetaCouplingXi_zeros {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    {z : ℂ | thetaCouplingXi r z = 0}.Infinite :=
  (infinite_thetaCouplingXi_nonreal_zeros hr0 hr1).mono fun _ h => h.1

/-- The zeros of `X_r`, `0 < r < 1`, have unbounded imaginary parts. -/
theorem exists_thetaCouplingXi_zero_abs_im_gt {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (B : ℝ) :
    ∃ z : ℂ, thetaCouplingXi r z = 0 ∧ B < |z.im| := by
  obtain ⟨z, hz, hzB⟩ := ((infinite_thetaCouplingXi_zeros hr0 hr1).sdiff
    (finite_thetaCouplingXi_zeros_strip hr1.ne B)).nonempty
  refine ⟨z, hz, ?_⟩
  by_contra hc
  push Not at hc
  exact hzB ⟨hc, hz⟩

theorem thetaCouplingXi_zero_ne_zero (z : ℂ) : thetaCouplingXi 0 z ≠ 0 := by
  rw [thetaCouplingXi_zero]; exact_mod_cast thetaSeamConst_pos.ne'

/-- At the physical coupling `X_1(y) = Ξ(2y)` has infinitely many real zeros. -/
theorem infinite_thetaCouplingXi_one_real_zeros :
    {y : ℝ | thetaCouplingXi 1 y = 0}.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨M, hM⟩ => ?_
  obtain ⟨γ, hγ, hXi, -⟩ := exists_simpleCrossing_above 1 (Or.inl rfl) (2 * M)
  have hmem : γ / 2 ∈ {y : ℝ | thetaCouplingXi 1 y = 0} := by
    simp only [mem_setOf_eq, thetaCouplingXi_ofReal, show 2 * (γ / 2) = γ by ring, hXi]
    simp
  have := hM hmem
  linarith

/-- Conjugation and reflection symmetry of the zero set. -/
theorem thetaCouplingXi_eq_zero_conj {r : ℝ} {z : ℂ} (hz : thetaCouplingXi r z = 0) :
    thetaCouplingXi r ((starRingEnd ℂ) z) = 0 := by
  rw [thetaCouplingXi_conj, hz, map_zero]

theorem thetaCouplingXi_eq_zero_neg {r : ℝ} {z : ℂ} (hz : thetaCouplingXi r z = 0) :
    thetaCouplingXi r (-z) = 0 := by
  rw [thetaCouplingXi_neg, hz]

end

end RHTower
