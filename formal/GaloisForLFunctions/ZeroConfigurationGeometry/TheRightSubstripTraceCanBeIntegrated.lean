import GaloisForLFunctions.ZeroConfigurationGeometry.TheRightSubstripTraceIsContinuous
import GaloisForLFunctions.RHTower.ZetaUnitIntervalIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Power weighting and integration of the complete right-substrip trace

Reciprocal ordinate mass controls real shifts of every zero denominator.
It also bounds the Abel integrand uniformly on `[1,∞)`, so finite-interval
integration commutes with the full multiplicity-weighted trace.
-/

noncomputable section

open Complex Set MeasureTheory
open _root_.RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- Reciprocal ordinate mass in the retained right substrip. -/
def rightSubstripOrdinateWeight (σ : ℝ) (q : XiZeroCopy) : ℝ :=
  if σ ≤ (q.1 : ℂ).re then |xiCopyOrdinate q|⁻¹ else 0

theorem rightSubstripOrdinateWeight_nonneg (σ : ℝ) (q : XiZeroCopy) :
    0 ≤ rightSubstripOrdinateWeight σ q := by
  unfold rightSubstripOrdinateWeight
  split_ifs <;> positivity

theorem summable_rightSubstripOrdinateWeight {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (rightSubstripOrdinateWeight σ) := by
  change Summable ({q : XiZeroCopy | σ ≤ (q.1 : ℂ).re}.indicator
    (fun q => |xiCopyOrdinate q|⁻¹))
  exact summable_subtype_iff_indicator.mp (summable_rightSubstrip_inv_abs_ordinate hσ)

/-- A real denominator shift cannot reduce its norm below the ordinate. -/
theorem abs_ordinate_le_norm_zero_sub_real (q : XiZeroCopy) (b : ℝ) :
    |xiCopyOrdinate q| ≤ ‖(q.1 : ℂ) - (b : ℂ)‖ := by
  simpa only [xiCopyOrdinate, Complex.sub_im, Complex.ofReal_im, sub_zero] using
    Complex.abs_im_le_norm ((q.1 : ℂ) - (b : ℂ))

theorem zero_sub_real_ne_zero (q : XiZeroCopy) (b : ℝ) :
    (q.1 : ℂ) - (b : ℂ) ≠ 0 := by
  apply norm_pos_iff.mp
  have hγ := four_lt_abs_xiCopyOrdinate q
  exact (by linarith only [hγ] : 0 < |xiCopyOrdinate q|).trans_le
    (abs_ordinate_le_norm_zero_sub_real q b)

/-- Power shift `a` and denominator shift `b` of a retained zero. -/
def rightShiftedZeroTerm (σ a b x : ℝ) (q : XiZeroCopy) : ℂ :=
  if σ ≤ (q.1 : ℂ).re then
    (x : ℂ) ^ ((q.1 : ℂ) - (a : ℂ)) / ((q.1 : ℂ) - (b : ℂ)) else 0

/-- The complete shifted trace, retaining every multiplicity copy. -/
def rightShiftedZeroTrace (σ a b x : ℝ) : ℂ := ∑' q, rightShiftedZeroTerm σ a b x q

/-- A single ordinate majorant controls all real denominator shifts. -/
theorem norm_rightShiftedZeroTerm_le {σ a b x : ℝ} (hx : 1 ≤ x) (q : XiZeroCopy) :
    ‖rightShiftedZeroTerm σ a b x q‖ ≤ x ^ (1 - a) * rightSubstripOrdinateWeight σ q := by
  by_cases hq : σ ≤ (q.1 : ℂ).re
  · have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hγ : 0 < |xiCopyOrdinate q| := by
      have hh := four_lt_abs_xiCopyOrdinate q
      linarith only [hh]
    rw [rightShiftedZeroTerm, if_pos hq, norm_div,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.ofReal_re,
      rightSubstripOrdinateWeight, if_pos hq]
    calc
      _ ≤ x ^ (1 - a) / ‖(q.1 : ℂ) - (b : ℂ)‖ :=
        div_le_div_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hx
            (sub_le_sub_right (xiZeroCopy_re_lt_one q).le a)) (norm_nonneg _)
      _ ≤ x ^ (1 - a) / |xiCopyOrdinate q| :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) hγ
          (abs_ordinate_le_norm_zero_sub_real q b)
      _ = _ := div_eq_mul_inv _ _
  · simp only [rightShiftedZeroTerm, rightSubstripOrdinateWeight, if_neg hq,
      norm_zero, mul_zero, le_refl]

theorem summable_rightShiftedZeroTerm {σ a b x : ℝ} (hσ : 1 / 2 < σ) (hx : 1 ≤ x) :
    Summable (rightShiftedZeroTerm σ a b x) :=
  Summable.of_norm_bounded ((summable_rightSubstripOrdinateWeight hσ).mul_left _)
    (norm_rightShiftedZeroTerm_le hx)

/-- One power of damping makes the shifted trace uniformly dominated. -/
theorem norm_rightShiftedZeroTerm_le_weight {σ a b x : ℝ}
    (ha : 1 ≤ a) (hx : 1 ≤ x) (q : XiZeroCopy) :
    ‖rightShiftedZeroTerm σ a b x q‖ ≤ rightSubstripOrdinateWeight σ q := by
  apply (norm_rightShiftedZeroTerm_le hx q).trans
  calc
    _ ≤ 1 * rightSubstripOrdinateWeight σ q :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_one_of_one_le_of_nonpos hx (sub_nonpos.mpr ha))
        (rightSubstripOrdinateWeight_nonneg σ q)
    _ = _ := one_mul _

/-- Removing one power from the exponent factors out the real argument. -/
theorem rightShiftedZeroTerm_eq_mul {σ a b x : ℝ} (hx : 0 < x) (q : XiZeroCopy) :
    rightShiftedZeroTerm σ a b x q = (x : ℂ) * rightShiftedZeroTerm σ (a + 1) b x q := by
  by_cases hq : σ ≤ (q.1 : ℂ).re
  · have hxne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
    have hd := zero_sub_real_ne_zero q b
    rw [rightShiftedZeroTerm, rightShiftedZeroTerm, if_pos hq, if_pos hq,
      show (q.1 : ℂ) - ((a + 1 : ℝ) : ℂ) = (q.1 : ℂ) - (a : ℂ) - 1 by
        push_cast; ring,
      Complex.cpow_sub ((q.1 : ℂ) - (a : ℂ)) 1 hxne, Complex.cpow_one]
    field_simp <;> ring
  · simp only [rightShiftedZeroTerm, if_neg hq, mul_zero]

theorem rightShiftedZeroTrace_eq_mul {σ a b x : ℝ} (hx : 0 < x) :
    rightShiftedZeroTrace σ a b x = (x : ℂ) * rightShiftedZeroTrace σ (a + 1) b x := by
  unfold rightShiftedZeroTrace
  rw [tsum_congr (fun q => rightShiftedZeroTerm_eq_mul hx q), tsum_mul_left]

/-- The raw shifted trace is the actual normalized prime trace with its
normalizing power restored. -/
theorem rightShiftedZeroTrace_zero_eq_normalized {σ β x : ℝ} (hx : 0 < x) :
    rightShiftedZeroTrace σ 0 0 x = ((x ^ β : ℝ) : ℂ) * rightNormalizedZeroTrace σ β x := by
  have hxne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hp : ((x ^ β : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx β).ne'
  unfold rightShiftedZeroTrace rightNormalizedZeroTrace
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  by_cases hq : σ ≤ (q.1 : ℂ).re
  · have hd := xiZeroCopy_ne_zero q
    simp only [rightShiftedZeroTerm, rightNormalizedZeroTerm, if_pos hq,
      Complex.ofReal_zero, sub_zero]
    rw [Complex.cpow_sub _ _ hxne, ← Complex.ofReal_cpow hx.le β]
    field_simp <;> ring
  · simp only [rightShiftedZeroTerm, rightNormalizedZeroTerm, if_neg hq, mul_zero]

/-- A power weight can be moved outside the complete trace. -/
theorem rightShiftedZeroTrace_eq_power_mul {σ a b x : ℝ} (hx : 0 < x) :
    rightShiftedZeroTrace σ a b x =
      ((x ^ (-a) : ℝ) : ℂ) * rightShiftedZeroTrace σ 0 b x := by
  have hxne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hp : ((x ^ a : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx a).ne'
  unfold rightShiftedZeroTrace
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  by_cases hq : σ ≤ (q.1 : ℂ).re
  · have hd := zero_sub_real_ne_zero q b
    rw [rightShiftedZeroTerm, rightShiftedZeroTerm, if_pos hq, if_pos hq,
      Complex.ofReal_zero, sub_zero, Complex.cpow_sub _ _ hxne,
      ← Complex.ofReal_cpow hx.le a, Real.rpow_neg hx.le, Complex.ofReal_inv]
    field_simp <;> ring
  · simp only [rightShiftedZeroTerm, if_neg hq, mul_zero]

theorem continuousOn_rightShiftedZeroTerm (σ a b : ℝ) (q : XiZeroCopy) :
    ContinuousOn (fun x => rightShiftedZeroTerm σ a b x q) (Ici 1) := by
  by_cases hq : σ ≤ (q.1 : ℂ).re
  · simp only [rightShiftedZeroTerm, if_pos hq]
    exact ((continuousOn_Ioi_cpow ((q.1 : ℂ) - (a : ℂ))).mono
      (show Ici (1 : ℝ) ⊆ Ioi (0 : ℝ) by
        intro x hx
        change 0 < x
        have hh : (1 : ℝ) ≤ x := hx
        linarith only [hh])).div_const _
  · simp only [rightShiftedZeroTerm, if_neg hq]
    exact continuousOn_const

/-- Factoring one real power gives a uniformly convergent continuous trace. -/
theorem continuousOn_rightShiftedZeroTrace {σ a b : ℝ}
    (hσ : 1 / 2 < σ) (ha : 0 ≤ a) :
    ContinuousOn (rightShiftedZeroTrace σ a b) (Ici 1) := by
  have hd : ContinuousOn (rightShiftedZeroTrace σ (a + 1) b) (Ici 1) := by
    apply continuousOn_tsum
      (f := fun (q : XiZeroCopy) (x : ℝ) => rightShiftedZeroTerm σ (a + 1) b x q)
      (u := rightSubstripOrdinateWeight σ)
    · exact fun q => continuousOn_rightShiftedZeroTerm σ (a + 1) b q
    · exact summable_rightSubstripOrdinateWeight hσ
    · intro q x hx
      exact norm_rightShiftedZeroTerm_le_weight (by linarith only [ha]) hx q
  have hm := Complex.continuous_ofReal.continuousOn.mul hd
  exact hm.congr (fun x hx => (rightShiftedZeroTrace_eq_mul
    (zero_lt_one.trans_le hx)))

theorem intervalIntegrable_rightShiftedZeroTerm (σ a b : ℝ) (q : XiZeroCopy)
    {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (fun t => rightShiftedZeroTerm σ a b t q) volume 1 x :=
  ((continuousOn_rightShiftedZeroTerm σ a b q).mono
    (show Icc (1 : ℝ) x ⊆ Ici 1 from fun _ ht => ht.1)).intervalIntegrable_of_Icc hx

/-- Uniform reciprocal domination pays the integral of each term's norm. -/
theorem integral_norm_rightShiftedZeroTerm_le {σ a b x : ℝ}
    (ha : 1 ≤ a) (hx : 1 ≤ x) (q : XiZeroCopy) :
    (∫ t in Ioc (1 : ℝ) x, ‖rightShiftedZeroTerm σ a b t q‖) ≤
      (x - 1) * rightSubstripOrdinateWeight σ q := by
  rw [← intervalIntegral.integral_of_le hx]
  calc
    _ ≤ ∫ _t in (1 : ℝ)..x, rightSubstripOrdinateWeight σ q :=
      intervalIntegral.integral_mono_on hx
        (intervalIntegrable_rightShiftedZeroTerm σ a b q hx).norm
        intervalIntegrable_const (fun t ht => norm_rightShiftedZeroTerm_le_weight ha ht.1 q)
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]

theorem summable_integral_norm_rightShiftedZeroTerm {σ a b x : ℝ}
    (hσ : 1 / 2 < σ) (ha : 1 ≤ a) (hx : 1 ≤ x) :
    Summable (fun q => ∫ t in Ioc (1 : ℝ) x, ‖rightShiftedZeroTerm σ a b t q‖) :=
  ((summable_rightSubstripOrdinateWeight hσ).mul_left (x - 1)).of_nonneg_of_le
    (fun _ => integral_nonneg (fun _ => norm_nonneg _))
    (integral_norm_rightShiftedZeroTerm_le ha hx)

/-- Finite-interval integration commutes with the complete shifted trace. -/
theorem integral_rightShiftedZeroTrace {σ a b x : ℝ}
    (hσ : 1 / 2 < σ) (ha : 1 ≤ a) (hx : 1 ≤ x) :
    (∫ t in Ioc (1 : ℝ) x, rightShiftedZeroTrace σ a b t) =
      ∑' q, ∫ t in Ioc (1 : ℝ) x, rightShiftedZeroTerm σ a b t q := by
  exact (integral_tsum_of_summable_integral_norm
    (fun q => (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp
      (intervalIntegrable_rightShiftedZeroTerm σ a b q hx))
    (summable_integral_norm_rightShiftedZeroTerm hσ ha hx)).symm

/-- The exact primitive of the zero term appearing in weighted Abel summation. -/
theorem integral_rightShiftedZeroTerm_abel (σ a : ℝ) {x : ℝ}
    (hx : 1 ≤ x) (q : XiZeroCopy) :
    (∫ t in Ioc (1 : ℝ) x, rightShiftedZeroTerm σ (a + 1) 0 t q) =
      if σ ≤ (q.1 : ℂ).re then
        ((x : ℂ) ^ ((q.1 : ℂ) - (a : ℂ)) - 1) /
          ((q.1 : ℂ) * ((q.1 : ℂ) - (a : ℂ))) else 0 := by
  by_cases hq : σ ≤ (q.1 : ℂ).re
  · have hd := zero_sub_real_ne_zero q a
    have hρ := xiZeroCopy_ne_zero q
    have he : (q.1 : ℂ) - ((a + 1 : ℝ) : ℂ) + 1 = (q.1 : ℂ) - (a : ℂ) := by
      push_cast
      ring
    have hr : (q.1 : ℂ) - ((a + 1 : ℝ) : ℂ) ≠ -1 := by
      intro hh
      apply hd
      rw [← he, hh, neg_add_cancel]
    simp only [rightShiftedZeroTerm, if_pos hq, Complex.ofReal_zero, sub_zero,
      div_eq_mul_inv]
    rw [integral_mul_const, integral_Ioc_ofReal_cpow zero_lt_one hx hr, he,
      Complex.ofReal_one, Complex.one_cpow]
    field_simp <;> ring
  · simp only [rightShiftedZeroTerm, if_neg hq, integral_zero]

/-- Abel weighting shifts both the power and its zero denominator; the
endpoint at one supplies an explicit constant. -/
theorem rightShiftedZeroTerm_abel (σ a : ℝ) {x : ℝ} (hx : 1 ≤ x) (q : XiZeroCopy) :
    ((x ^ (-a) : ℝ) : ℂ) * rightShiftedZeroTerm σ 0 0 x q +
      (a : ℂ) * (∫ t in Ioc (1 : ℝ) x, rightShiftedZeroTerm σ (a + 1) 0 t q) =
      rightShiftedZeroTerm σ a a x q + rightShiftedZeroTerm σ 0 0 1 q -
        rightShiftedZeroTerm σ a a 1 q := by
  rw [integral_rightShiftedZeroTerm_abel σ a hx q]
  by_cases hq : σ ≤ (q.1 : ℂ).re
  · have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hxne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
    have hp : ((x ^ a : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx0 a).ne'
    have hd := zero_sub_real_ne_zero q a
    have hρ := xiZeroCopy_ne_zero q
    have hpow : (x : ℂ) ^ ((q.1 : ℂ) - (a : ℂ)) =
        (x : ℂ) ^ (q.1 : ℂ) / ((x ^ a : ℝ) : ℂ) := by
      rw [Complex.cpow_sub _ _ hxne, Complex.ofReal_cpow hx0.le a]
    simp only [rightShiftedZeroTerm, if_pos hq, Complex.ofReal_zero,
      sub_zero, Complex.ofReal_one, Complex.one_cpow, hpow]
    rw [Real.rpow_neg hx0.le, Complex.ofReal_inv]
    field_simp <;> ring
  · simp only [rightShiftedZeroTerm, if_neg hq, mul_zero, add_zero, sub_zero]

/-- The complete right-substrip trace obeys exact weighted Abel summation,
including its constant term at one. -/
theorem rightShiftedZeroTrace_abel {σ a x : ℝ}
    (hσ : 1 / 2 < σ) (ha : 0 ≤ a) (hx : 1 ≤ x) :
    ((x ^ (-a) : ℝ) : ℂ) * rightShiftedZeroTrace σ 0 0 x +
      (a : ℂ) * (∫ t in Ioc (1 : ℝ) x, rightShiftedZeroTrace σ (a + 1) 0 t) =
      rightShiftedZeroTrace σ a a x + rightShiftedZeroTrace σ 0 0 1 -
        rightShiftedZeroTrace σ a a 1 := by
  have ha1 : 1 ≤ a + 1 := by linarith only [ha]
  have hraw := summable_rightShiftedZeroTerm (a := 0) (b := 0) hσ hx
  have hQ := summable_rightShiftedZeroTerm (a := a) (b := a) hσ hx
  have hraw1 := summable_rightShiftedZeroTerm (a := 0) (b := 0) hσ (le_refl (1 : ℝ))
  have hQ1 := summable_rightShiftedZeroTerm (a := a) (b := a) hσ (le_refl (1 : ℝ))
  have hI : Summable (fun q => ∫ t in Ioc (1 : ℝ) x,
      rightShiftedZeroTerm σ (a + 1) 0 t q) :=
    Summable.of_norm_bounded (summable_integral_norm_rightShiftedZeroTerm hσ ha1 hx)
      (fun _ => norm_integral_le_integral_norm _)
  calc
    _ = ∑' q, (((x ^ (-a) : ℝ) : ℂ) * rightShiftedZeroTerm σ 0 0 x q +
        (a : ℂ) * (∫ t in Ioc (1 : ℝ) x, rightShiftedZeroTerm σ (a + 1) 0 t q)) := by
      rw [integral_rightShiftedZeroTrace hσ ha1 hx,
        (hraw.mul_left ((x ^ (-a) : ℝ) : ℂ)).tsum_add (hI.mul_left (a : ℂ)),
        tsum_mul_left, tsum_mul_left]
      rfl
    _ = ∑' q, (rightShiftedZeroTerm σ a a x q + rightShiftedZeroTerm σ 0 0 1 q -
        rightShiftedZeroTerm σ a a 1 q) :=
      tsum_congr (fun q => rightShiftedZeroTerm_abel σ a hx q)
    _ = _ := by
      rw [(hQ.add hraw1).tsum_sub hQ1, hQ.tsum_add hraw1]
      rfl

theorem integrableOn_rightShiftedZeroTrace {σ a b x : ℝ}
    (hσ : 1 / 2 < σ) (ha : 0 ≤ a) (hx : 1 ≤ x) :
    IntegrableOn (rightShiftedZeroTrace σ a b) (Ioc 1 x) := by
  have hi : IntervalIntegrable (rightShiftedZeroTrace σ a b) volume 1 x :=
    ((continuousOn_rightShiftedZeroTrace hσ ha).mono
      (show Icc (1 : ℝ) x ⊆ Ici 1 from fun _ ht => ht.1)).intervalIntegrable_of_Icc hx
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp hi

theorem rightShiftedZeroTrace_abelKernel_re {σ a t : ℝ} (ht : 1 ≤ t) :
    (rightShiftedZeroTrace σ (a + 1) 0 t).re =
      t ^ (-a - 1) * (rightShiftedZeroTrace σ 0 0 t).re := by
  rw [rightShiftedZeroTrace_eq_power_mul (zero_lt_one.trans_le ht)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    show -(a + 1) = -a - 1 by ring]

/-- The real weighted trace kernel is genuinely integrable, with its
integrability supplied by the complete complex trace. -/
theorem integrableOn_real_weightedRightZeroTrace {σ a x : ℝ}
    (hσ : 1 / 2 < σ) (ha : 0 ≤ a) (hx : 1 ≤ x) :
    IntegrableOn (fun t => t ^ (-a - 1) * (rightShiftedZeroTrace σ 0 0 t).re) (Ioc 1 x) := by
  have hi := integrableOn_rightShiftedZeroTrace (b := 0) hσ
    (by linarith only [ha] : 0 ≤ a + 1) hx
  have hir : IntegrableOn (fun t => (rightShiftedZeroTrace σ (a + 1) 0 t).re) (Ioc 1 x) := by
    simpa only [IntegrableOn, RCLike.re_to_complex] using hi.re
  exact hir.congr_fun (fun _ ht => rightShiftedZeroTrace_abelKernel_re ht.1.le) measurableSet_Ioc

/-- Real-part Abel summation for the actual full trace, with its endpoint constant. -/
theorem rightShiftedZeroTrace_abel_real {σ a x : ℝ}
    (hσ : 1 / 2 < σ) (ha : 0 ≤ a) (hx : 1 ≤ x) :
    x ^ (-a) * (rightShiftedZeroTrace σ 0 0 x).re +
      a * (∫ t in Ioc (1 : ℝ) x, t ^ (-a - 1) * (rightShiftedZeroTrace σ 0 0 t).re) =
      (rightShiftedZeroTrace σ a a x).re + (rightShiftedZeroTrace σ 0 0 1).re -
        (rightShiftedZeroTrace σ a a 1).re := by
  have hi := integrableOn_rightShiftedZeroTrace (b := 0) hσ
    (by linarith only [ha] : 0 ≤ a + 1) hx
  have hIr : (∫ t in Ioc (1 : ℝ) x, rightShiftedZeroTrace σ (a + 1) 0 t).re =
      ∫ t in Ioc (1 : ℝ) x, t ^ (-a - 1) * (rightShiftedZeroTrace σ 0 0 t).re := by
    calc
      _ = ∫ t in Ioc (1 : ℝ) x, (rightShiftedZeroTrace σ (a + 1) 0 t).re := by
        simpa only [RCLike.re_to_complex] using (integral_re hi).symm
      _ = _ := setIntegral_congr_fun measurableSet_Ioc
        (fun _ ht => rightShiftedZeroTrace_abelKernel_re ht.1.le)
  have hh := congrArg Complex.re (rightShiftedZeroTrace_abel hσ ha hx)
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hh
  rwa [hIr] at hh

end GaloisForLFunctions.ZeroConfigurationGeometry
