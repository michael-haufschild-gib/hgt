import GaloisForLFunctions.RHTower.EulerShiftPairIncidenceCurrent
import GaloisForLFunctions.ConjugateDiagonalGeometry.FiniteThetaReadingError
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Gaussian readings of horizontal collisions

The nonnegative difference of the ordinate and planar Gaussians tends to the
indicator of distinct points sharing an ordinate. On a finite divisor the
multiplicity-weighted error is bounded by squared total mass times the Gaussian
of its least nonzero coordinate separation. Smooth height collars preserve the
half-open window, including height zero and excluding its upper endpoint.
-/

open Complex Filter Topology Set Metric
open scoped BigOperators Classical
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
noncomputable section

/-- A positive pair kernel that removes the diagonal and retains horizontal collisions. -/
def horizontalCollisionGaussian (q : ℝ) (z w : ℂ) : ℝ :=
  Real.exp (-q * (z.im - w.im)^2) * (1 - Real.exp (-q * (z.re - w.re)^2))

theorem horizontalCollisionGaussian_nonneg {q : ℝ} (hq : 0 ≤ q) (z w : ℂ) :
    0 ≤ horizontalCollisionGaussian q z w := by
  apply mul_nonneg (Real.exp_pos _).le
  apply sub_nonneg.mpr
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (sq_nonneg _)

theorem horizontalCollisionGaussian_le_exp {q : ℝ} (_hq : 0 ≤ q) (z w : ℂ) :
    horizontalCollisionGaussian q z w ≤ Real.exp (-q * (z.im - w.im)^2) := by
  exact mul_le_of_le_one_right (Real.exp_pos _).le (sub_le_self _ (Real.exp_pos _).le)

theorem horizontalCollisionGaussian_self (q : ℝ) (z : ℂ) :
    horizontalCollisionGaussian q z z = 0 := by
  simp only [horizontalCollisionGaussian, sub_self, zero_pow two_ne_zero,
    mul_zero, Real.exp_zero, sub_self, mul_zero]

theorem horizontalCollisionGaussian_eq_exp_difference (q : ℝ) (z w : ℂ) :
    horizontalCollisionGaussian q z w =
      Real.exp (-q * (z.im - w.im)^2) - Real.exp (-q * Complex.normSq (z - w)) := by
  have hn : Complex.normSq (z - w) = (z.re - w.re)^2 + (z.im - w.im)^2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have he : -q * ((z.re - w.re)^2 + (z.im - w.im)^2) =
      -q * (z.im - w.im)^2 + -q * (z.re - w.re)^2 := by ring
  rw [hn, he, Real.exp_add, horizontalCollisionGaussian]
  ring

/-- The least nonzero coordinate separation; one when every coordinate agrees. -/
def finiteCoordinateGap (S : Finset ℂ) (c : ℂ → ℝ) : ℝ :=
  let P := (S ×ˢ S).filter (fun p => c p.1 ≠ c p.2)
  if h : P.Nonempty then P.inf' h (fun p => |c p.1 - c p.2|) else 1

theorem finiteCoordinateGap_pos (S : Finset ℂ) (c : ℂ → ℝ) :
    0 < finiteCoordinateGap S c := by
  unfold finiteCoordinateGap
  dsimp only
  split_ifs with h
  · apply (Finset.lt_inf'_iff h).mpr
    intro p hp
    exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hp).2)
  · exact one_pos

theorem finiteCoordinateGap_le (S : Finset ℂ) (c : ℂ → ℝ)
    {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) (hzw : c z ≠ c w) :
    finiteCoordinateGap S c ≤ |c z - c w| := by
  have hm : (z, w) ∈ (S ×ˢ S).filter (fun p => c p.1 ≠ c p.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz, hw⟩, hzw⟩
  rw [finiteCoordinateGap, dif_pos ⟨(z, w), hm⟩]
  exact Finset.inf'_le (fun p : ℂ × ℂ => |c p.1 - c p.2|) hm

def finiteCollisionGap (S : Finset ℂ) : ℝ :=
  min (finiteCoordinateGap S Complex.re) (finiteCoordinateGap S Complex.im)

theorem finiteCollisionGap_pos (S : Finset ℂ) : 0 < finiteCollisionGap S :=
  lt_min (finiteCoordinateGap_pos S _) (finiteCoordinateGap_pos S _)

private theorem abs_horizontalCollisionGaussian_sub_indicator_le
    {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 ≤ δ) {z w : ℂ}
    (hre : z.re ≠ w.re → δ ≤ |z.re - w.re|)
    (him : z.im ≠ w.im → δ ≤ |z.im - w.im|) :
    |horizontalCollisionGaussian q z w - (if z.im = w.im ∧ z ≠ w then 1 else 0)| ≤
      Real.exp (-q * δ^2) := by
  have hdecay (d : ℝ) (hd : δ ≤ |d|) :
      Real.exp (-q * d^2) ≤ Real.exp (-q * δ^2) := by
    apply Real.exp_le_exp.mpr
    have hs : δ^2 ≤ d^2 := ((sq_le_sq₀ hδ (abs_nonneg d)).mpr hd).trans_eq (sq_abs d)
    exact mul_le_mul_of_nonpos_left hs (neg_nonpos.mpr hq)
  by_cases hi : z.im = w.im
  · by_cases hzw : z = w
    · subst w
      simp only [horizontalCollisionGaussian_self, ne_eq, not_true_eq_false, and_false,
        if_false, sub_zero, abs_zero]
      exact (Real.exp_pos _).le
    · have hr : z.re ≠ w.re := fun hr => hzw (Complex.ext hr hi)
      rw [if_pos ⟨hi, hzw⟩, horizontalCollisionGaussian, hi, sub_self,
        zero_pow two_ne_zero, mul_zero, Real.exp_zero, one_mul,
        sub_sub_cancel_left, abs_neg, abs_of_pos (Real.exp_pos _)]
      exact hdecay _ (hre hr)
  · rw [if_neg (fun h => hi h.1), sub_zero,
      abs_of_nonneg (horizontalCollisionGaussian_nonneg hq z w)]
    exact (horizontalCollisionGaussian_le_exp hq z w).trans (hdecay _ (him hi))

theorem abs_horizontalCollisionGaussian_pair_error
    (S : Finset ℂ) (m : ℂ → ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hre : ∀ z ∈ S, ∀ w ∈ S, z.re ≠ w.re → δ ≤ |z.re - w.re|)
    (him : ∀ z ∈ S, ∀ w ∈ S, z.im ≠ w.im → δ ≤ |z.im - w.im|)
    (q : ℝ) (hq : 0 ≤ q) :
      |(∑ z ∈ S, ∑ w ∈ S, (m z : ℝ) * (m w : ℝ) * horizontalCollisionGaussian q z w) -
        (∑ z ∈ S, ∑ w ∈ S,
          (m z : ℝ) * (m w : ℝ) * (if z.im = w.im ∧ z ≠ w then 1 else 0))| ≤
      (∑ z ∈ S, (m z : ℝ))^2 * Real.exp (-q * δ^2) := by
  classical
  have hpoint (z : ℂ) (hz : z ∈ S) (w : ℂ) (hw : w ∈ S) :
      |(m z : ℝ) * (m w : ℝ) * (horizontalCollisionGaussian q z w -
        (if z.im = w.im ∧ z ≠ w then 1 else 0))| ≤
      (m z : ℝ) * (m w : ℝ) * Real.exp (-q * δ^2) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    exact abs_horizontalCollisionGaussian_sub_indicator_le hq hδ
      (hre z hz w hw) (him z hz w hw)
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ z ∈ S, ∑ w ∈ S,
        |(m z : ℝ) * (m w : ℝ) * (horizontalCollisionGaussian q z w -
          (if z.im = w.im ∧ z ≠ w then 1 else 0))| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun z _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ z ∈ S, ∑ w ∈ S, (m z : ℝ) * (m w : ℝ) * Real.exp (-q * δ^2) :=
      Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun w hw => hpoint z hz w hw
    _ = _ := by
      rw [show (∑ z ∈ S, (m z : ℝ))^2 =
        (∑ z ∈ S, (m z : ℝ)) * (∑ z ∈ S, (m z : ℝ)) from pow_two _]
      simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]

theorem horizontalCollisionGaussian_error (S : Finset ℂ) (m : ℂ → ℕ) (q : ℝ)
    (hq : 0 ≤ q) :
    |(∑ z ∈ S, ∑ w ∈ S, (m z : ℝ) * (m w : ℝ) * horizontalCollisionGaussian q z w) -
      (∑ z ∈ S, ∑ w ∈ S,
        (m z : ℝ) * (m w : ℝ) * (if z.im = w.im ∧ z ≠ w then 1 else 0))| ≤
    (∑ z ∈ S, (m z : ℝ))^2 * Real.exp (-q * (finiteCollisionGap S)^2) :=
  abs_horizontalCollisionGaussian_pair_error S m (finiteCollisionGap_pos S).le
    (fun _ hz _ hw h => (min_le_left _ _).trans (finiteCoordinateGap_le S _ hz hw h))
    (fun _ hz _ hw h => (min_le_right _ _).trans (finiteCoordinateGap_le S _ hz hw h)) q hq

#print axioms horizontalCollisionGaussian_error

/-- Smooth collars retain the lower endpoint and exclude the upper endpoint. -/
def collisionHeightCutoff (T : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  Real.smoothTransition ((n : ℝ) * y + 1) *
    Real.smoothTransition ((n : ℝ) * (T - y))

theorem collisionHeightCutoff_nonneg (T : ℝ) (n : ℕ) (y : ℝ) :
    0 ≤ collisionHeightCutoff T n y :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem collisionHeightCutoff_le_one (T : ℝ) (n : ℕ) (y : ℝ) :
    collisionHeightCutoff T n y ≤ 1 := by
  apply (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _)).trans
  simpa only [one_mul] using Real.smoothTransition.le_one ((n : ℝ) * (T - y))

theorem eventually_collisionHeightCutoff_eq (T y : ℝ) :
    ∀ᶠ n : ℕ in atTop, collisionHeightCutoff T n y =
      if 0 ≤ y ∧ y < T then 1 else 0 := by
  by_cases hy : 0 ≤ y
  · by_cases hT : y < T
    · filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
        (1 / (T - y))] with n hn
      have hprod : 1 ≤ (n : ℝ) * (T - y) := (div_le_iff₀ (sub_pos.mpr hT)).mp hn
      rw [if_pos ⟨hy, hT⟩, collisionHeightCutoff,
        Real.smoothTransition.one_of_one_le (by nlinarith only [mul_nonneg (Nat.cast_nonneg n) hy]),
        Real.smoothTransition.one_of_one_le hprod, mul_one]
    · exact Eventually.of_forall fun n => by
        rw [if_neg (fun h => hT h.2), collisionHeightCutoff,
          Real.smoothTransition.zero_of_nonpos
            (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (sub_nonpos.mpr (le_of_not_gt hT))),
          mul_zero]
  · have hy0 : 0 < -y := neg_pos.mpr (lt_of_not_ge hy)
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (1 / -y)] with n hn
    have hprod : 1 ≤ (n : ℝ) * -y := (div_le_iff₀ hy0).mp hn
    rw [if_neg (fun h => hy h.1), collisionHeightCutoff,
      Real.smoothTransition.zero_of_nonpos (by nlinarith only [hprod]), zero_mul]

def collisionWindowCutoff (T : ℝ) (R n : ℕ) (z : ℂ) : ℝ :=
  sourceCutoff R z * collisionHeightCutoff T n z.im

def collisionWindowPairTest (T : ℝ) (R n : ℕ) (z w : ℂ) : ℝ :=
  collisionWindowCutoff T R n z * collisionWindowCutoff T R n w *
    horizontalCollisionGaussian ((n : ℝ)^2) z w

theorem contDiff_collisionWindowCutoff (T : ℝ) (R n : ℕ) :
    ContDiff ℝ 2 (collisionWindowCutoff T R n) := by
  have hs : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff
  have hi : ContDiff ℝ 2 Complex.im := Complex.imCLM.contDiff
  unfold collisionWindowCutoff collisionHeightCutoff
  exact (sourceCutoff R).contDiff.mul
    ((hs.comp ((contDiff_const.mul hi).add contDiff_const)).mul
      (hs.comp (contDiff_const.mul (contDiff_const.sub hi))))

theorem contDiff_horizontalCollisionGaussian (q : ℝ) :
    ContDiff ℝ 2 (Function.uncurry (horizontalCollisionGaussian q)) := by
  have hi : ContDiff ℝ 2 (fun p : ℂ × ℂ => p.1.im - p.2.im) :=
    (Complex.imCLM.contDiff.comp contDiff_fst).sub (Complex.imCLM.contDiff.comp contDiff_snd)
  have hr : ContDiff ℝ 2 (fun p : ℂ × ℂ => p.1.re - p.2.re) :=
    (Complex.reCLM.contDiff.comp contDiff_fst).sub (Complex.reCLM.contDiff.comp contDiff_snd)
  exact (Real.contDiff_exp.comp (contDiff_const.mul (hi.pow 2))).mul
    (contDiff_const.sub (Real.contDiff_exp.comp (contDiff_const.mul (hr.pow 2))))

theorem contDiff_collisionWindowPairTest (T : ℝ) (R n : ℕ) :
    ContDiff ℝ 2 (Function.uncurry (collisionWindowPairTest T R n)) :=
  (((contDiff_collisionWindowCutoff T R n).comp contDiff_fst).mul
    ((contDiff_collisionWindowCutoff T R n).comp contDiff_snd)).mul
      (contDiff_horizontalCollisionGaussian _)

theorem collisionWindowCutoff_nonneg (T : ℝ) (R n : ℕ) (z : ℂ) :
    0 ≤ collisionWindowCutoff T R n z :=
  mul_nonneg (sourceCutoff R).nonneg (collisionHeightCutoff_nonneg T n z.im)

theorem collisionWindowCutoff_le_one (T : ℝ) (R n : ℕ) (z : ℂ) :
    collisionWindowCutoff T R n z ≤ 1 := by
  apply (mul_le_mul_of_nonneg_right (sourceCutoff R).le_one
    (collisionHeightCutoff_nonneg T n z.im)).trans
  simpa only [one_mul] using collisionHeightCutoff_le_one T n z.im

theorem abs_collisionWindowPairTest_le_one (T : ℝ) (R n : ℕ) (z w : ℂ) :
    |collisionWindowPairTest T R n z w| ≤ 1 := by
  have hz0 := collisionWindowCutoff_nonneg T R n z
  have hw0 := collisionWindowCutoff_nonneg T R n w
  have hk0 := horizontalCollisionGaussian_nonneg (sq_nonneg (n : ℝ)) z w
  have hk1 : horizontalCollisionGaussian ((n : ℝ)^2) z w ≤ 1 :=
    (horizontalCollisionGaussian_le_exp (sq_nonneg (n : ℝ)) z w).trans
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg (n : ℝ))) (sq_nonneg _)))
  rw [collisionWindowPairTest, abs_of_nonneg (mul_nonneg (mul_nonneg hz0 hw0) hk0)]
  apply (mul_le_mul_of_nonneg_left hk1 (mul_nonneg hz0 hw0)).trans
  rw [mul_one]
  exact (mul_le_mul_of_nonneg_right (collisionWindowCutoff_le_one T R n z) hw0).trans
    (by simpa only [one_mul] using collisionWindowCutoff_le_one T R n w)

#print axioms eventually_collisionHeightCutoff_eq
#print axioms contDiff_collisionWindowPairTest

theorem collisionWindowPairTest_eq_zero_outside (T : ℝ) (R n : ℕ) (z w : ℂ)
    (h : z ∉ closedBall (0 : ℂ) ((R : ℝ) + 2) ∨
      w ∉ closedBall (0 : ℂ) ((R : ℝ) + 2)) : collisionWindowPairTest T R n z w = 0 := by
  have hz (u : ℂ) (hu : u ∉ closedBall (0 : ℂ) ((R : ℝ) + 2)) :
      collisionWindowCutoff T R n u = 0 := by
    have hc : sourceCutoff R u = 0 := (sourceCutoff R).zero_of_le_dist
      (le_of_lt (lt_of_not_ge hu))
    rw [collisionWindowCutoff, hc, zero_mul]
  rcases h with h | h
  · rw [collisionWindowPairTest, hz z h, zero_mul, zero_mul]
  · rw [collisionWindowPairTest, hz w h, mul_zero, zero_mul]

def collisionWindowRadius (T : ℝ) : ℕ := Nat.ceil |T| + 2

theorem sourceCutoff_collisionWindowRadius_eq_one {T : ℝ} {z : ℂ}
    (hz : z ∈ RHTower.stripWindow T) : sourceCutoff (collisionWindowRadius T) z = 1 := by
  have hn := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos hz.1, abs_of_nonneg hz.2.2.1] at hn
  have hT := Nat.le_ceil |T|
  apply (sourceCutoff (collisionWindowRadius T)).one_of_mem_closedBall
  rw [mem_closedBall, dist_zero_right]
  change ‖z‖ ≤ (collisionWindowRadius T : ℝ) + 1
  simp only [collisionWindowRadius, Nat.cast_add, Nat.cast_ofNat]
  linarith only [hn, hz.2.1, hz.2.2.2, le_abs_self T, hT]

theorem eventually_collisionWindowCutoff_eq_window (T : ℝ) {z : ℂ} (hz : RHTower.xi z = 0) :
    ∀ᶠ n : ℕ in atTop, collisionWindowCutoff T (collisionWindowRadius T) n z =
      if z ∈ RHTower.stripZeros T then 1 else 0 := by
  classical
  filter_upwards [eventually_collisionHeightCutoff_eq T z.im] with n hn
  rw [collisionWindowCutoff, hn]
  by_cases hw : z ∈ RHTower.stripZeros T
  · rw [if_pos hw, if_pos ⟨hw.1.2.2.1, hw.1.2.2.2⟩,
      sourceCutoff_collisionWindowRadius_eq_one hw.1, mul_one]
  · have hh : ¬ (0 ≤ z.im ∧ z.im < T) := by
      intro hh
      have hs := RHTower.xi_zero_re_mem_open_unit hz
      exact hw ⟨⟨hs.1, hs.2, hh.1, hh.2⟩, hz⟩
    rw [if_neg hw, if_neg hh, mul_zero]

#print axioms eventually_collisionWindowCutoff_eq_window

/-- The comparison sum on the actual finite Xi window retains both multiplicities. -/
def xiWindowGaussianPairSum (T q : ℝ) : ℝ :=
  ∑ z ∈ (RHTower.stripZeros_finite T).toFinset,
    ∑ w ∈ (RHTower.stripZeros_finite T).toFinset,
      (HTGeometry.zeroMult RHTower.xi z : ℝ) * (HTGeometry.zeroMult RHTower.xi w : ℝ) *
        horizontalCollisionGaussian q z w

theorem exists_xiWindowGaussianPairSum_error (T : ℝ) :
    ∃ δ > 0, ∀ q : ℝ, 0 ≤ q →
      |xiWindowGaussianPairSum T q - (RHTower.xiHorizontalCollisionCharge T : ℝ)| ≤
        (RHTower.xiStripWindowTotalOrder T : ℝ)^2 * Real.exp (-q * δ^2) := by
  classical
  let S := (RHTower.stripZeros_finite T).toFinset
  let m := HTGeometry.zeroMult RHTower.xi
  have hcharge : (RHTower.xiHorizontalCollisionCharge T : ℝ) =
      ∑ z ∈ S, ∑ w ∈ S, (m z : ℝ) * (m w : ℝ) *
        (if z.im = w.im ∧ z ≠ w then 1 else 0) := by
    rw [RHTower.xiHorizontalCollisionCharge_eq_sum_pairs,
      RHTower.xiHorizontalCollisionPairs, Finset.sum_filter, Finset.sum_product]
    push_cast
    simp only [S, m, HTGeometry.zeroMult, mul_ite, mul_one, mul_zero]
  refine ⟨finiteCollisionGap S, finiteCollisionGap_pos S, fun q hq => ?_⟩
  have h := horizontalCollisionGaussian_error S m q hq
  rw [← hcharge] at h
  simpa only [xiWindowGaussianPairSum, RHTower.xiStripWindowTotalOrder,
    Nat.cast_sum, m, HTGeometry.zeroMult] using h

#print axioms exists_xiWindowGaussianPairSum_error

theorem tendsto_collisionGaussian_error {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    Tendsto (fun n : ℕ => M^2 * Real.exp (-((n : ℝ)^2) * δ^2)) atTop (𝓝 0) := by
  have hk : Tendsto (fun n : ℕ => δ^2 * (n : ℝ)^2) atTop atTop :=
    (Filter.tendsto_const_mul_pow_atTop two_ne_zero (sq_pos_of_pos hδ)).comp
      tendsto_natCast_atTop_atTop
  have he := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hk
  simpa only [Function.comp_apply, pow_zero, one_mul, mul_zero, neg_mul, mul_neg, mul_comm] using
    he.const_mul (M^2)

#print axioms tendsto_collisionGaussian_error
end
end GaloisForLFunctions.ConjugateDiagonalGeometry
