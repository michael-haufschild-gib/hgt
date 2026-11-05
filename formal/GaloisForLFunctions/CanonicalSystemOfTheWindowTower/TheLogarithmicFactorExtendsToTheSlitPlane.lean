import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFactorStartsAtOne
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import GaloisForLFunctions.HTGeometry.ComplexShiftLerch
import GaloisForLFunctions.HTGeometry.LogWeightedPoisson
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# The logarithmic factor on the slit plane

The nested logarithmic symbol maps each nonnegative slit ray into the slit plane.
Compact segment bounds control both logarithms and the resolvent uniformly.
An integrable logarithmic majorant then proves holomorphy of the literal factor.
Two positive dilations identify its real values with the Poisson factor;
conjugation preserves the defining integral.
-/

open MeasureTheory Set Filter Topology Complex Metric
open scoped ComplexOrder
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open GaloisForLFunctions.HTGeometry

/-- The analytic symbol whose restriction to a squared frequency is the positive reference. -/
def logarithmicLaplaceSymbol (z : ℂ) : ℂ :=
  1 + ((1 / 2 : ℝ) : ℂ) * Complex.log (1 + z)

private theorem one_add_slit_ray {z : ℂ} (hz : z ∈ slitPlane) {x : ℝ} (hx : 0 ≤ x) :
    1 + z * (x : ℂ) ∈ slitPlane := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp only [Complex.ofReal_zero, mul_zero, add_zero]
    exact Or.inl (by norm_num)
  · rcases mem_slitPlane_iff.mp hz with hr | hi
    · apply Or.inl
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      positivity
    · apply Or.inr
      simpa only [Complex.add_im, Complex.one_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] using mul_ne_zero hi hx.ne'

private theorem logarithmicLaplaceSymbol_slit_ray {z : ℂ} (hz : z ∈ slitPlane)
    {x : ℝ} (hx : 0 ≤ x) : logarithmicLaplaceSymbol (z * (x : ℂ)) ∈ slitPlane := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp only [Complex.ofReal_zero, mul_zero, logarithmicLaplaceSymbol,
      add_zero, Complex.log_one]
    exact Or.inl (by norm_num)
  · rcases mem_slitPlane_iff.mp hz with hr | hi
    · have hre : 1 ≤ (1 + z * (x : ℂ)).re := by
        simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        have hp := mul_nonneg hr.le hx.le
        linarith only [hp]
      have hn : 1 ≤ ‖1 + z * (x : ℂ)‖ := hre.trans (Complex.re_le_norm _)
      have hl := Real.log_nonneg hn
      apply Or.inl
      simp only [logarithmicLaplaceSymbol, Complex.add_re, Complex.one_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.log_re]
      linarith only [hl]
    · apply Or.inr
      have ha : (1 + z * (x : ℂ)).arg ≠ 0 := by
        intro h
        have him := (Complex.arg_eq_zero_iff.mp h).2
        simp only [Complex.add_im, Complex.one_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at him
        exact mul_ne_zero hi hx.ne' him
      have he : (logarithmicLaplaceSymbol (z * (x : ℂ))).im =
          (1 / 2 : ℝ) * (1 + z * (x : ℂ)).arg := by
        simp only [logarithmicLaplaceSymbol, Complex.add_im, Complex.one_im,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          zero_add, Complex.log_im]
      rw [he]
      exact mul_ne_zero (by norm_num) ha

theorem logarithmicLaplaceSymbol_ofReal_sq (t : ℝ) :
    logarithmicLaplaceSymbol ((t : ℂ) ^ 2) = (positiveLogarithmicSymbol t : ℂ) := by
  have he : (1 : ℂ) + (t : ℂ) ^ 2 = ((1 + t ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  unfold logarithmicLaplaceSymbol positiveLogarithmicSymbol
  rw [he, ← Complex.ofReal_log (by positivity : 0 ≤ 1 + t ^ 2)]
  push_cast
  rfl

private theorem differentiableAt_logarithmicLaplaceSymbol {z : ℂ}
    (hz : 1 + z ∈ slitPlane) : DifferentiableAt ℂ logarithmicLaplaceSymbol z := by
  have hlin : DifferentiableAt ℂ (fun w : ℂ => 1 + w) z := by fun_prop
  have hl : DifferentiableAt ℂ (fun w : ℂ => Complex.log (1 + w)) z := by
    simpa only [Function.comp_def] using!
      (Complex.hasDerivAt_log hz).differentiableAt.comp z hlin
  change DifferentiableAt ℂ (fun w : ℂ => 1 + ((1 / 2 : ℝ) : ℂ) * Complex.log (1 + w)) z
  simpa only using! (hl.const_mul ((1 / 2 : ℝ) : ℂ)).const_add (1 : ℂ)

private theorem differentiableAt_logarithmicLogSymbol {z : ℂ}
    (hz : 1 + z ∈ slitPlane) (hg : logarithmicLaplaceSymbol z ∈ slitPlane) :
    DifferentiableAt ℂ (fun w => Complex.log (logarithmicLaplaceSymbol w)) z :=
  (Complex.hasDerivAt_log hg).differentiableAt.comp z
    (differentiableAt_logarithmicLaplaceSymbol hz)

private theorem norm_complex_log_le (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  calc
    _ ≤ |(Complex.log z).re| + |(Complex.log z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by
      rw [Complex.log_re, Complex.log_im]
      exact add_le_add (le_refl _) (Complex.abs_arg_le_pi z)

private def slitSegment (p : ℂ × ℝ) : ℂ :=
  ((1 - p.2 : ℝ) : ℂ) + p.1 * (p.2 : ℂ)

private theorem slitSegment_mem {z : ℂ} (hz : z ∈ slitPlane) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : slitSegment (z, u) ∈ slitPlane := by
  rcases eq_or_lt_of_le hu.1 with rfl | hu0
  · simp only [slitSegment, sub_zero, Complex.ofReal_one, Complex.ofReal_zero,
      mul_zero, add_zero]
    exact Or.inl (by norm_num)
  · rcases mem_slitPlane_iff.mp hz with hr | hi
    · apply Or.inl
      simp only [slitSegment, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
      have hp := mul_pos hr hu0
      linarith only [hp, hu.2]
    · apply Or.inr
      simpa only [slitSegment, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, mul_zero, zero_add] using mul_ne_zero hi hu0.ne'

/-- A compact family of slit rays has uniform resolvent and logarithm bounds. -/
theorem compact_slit_ray_bounds {K : Set ℂ} (hK : IsCompact K)
    (hKs : K ⊆ slitPlane) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z ∈ K, ∀ x : ℝ, 0 ≤ x →
      c * (1 + x) ≤ ‖z + (x : ℂ)‖ ∧
      c * (1 + x) ≤ ‖1 + z * (x : ℂ)‖ ∧
      ‖Complex.log (1 + z * (x : ℂ))‖ ≤ Real.log (1 + x) + C := by
  let S : Set (ℂ × ℝ) := K ×ˢ Icc (0 : ℝ) 1
  have hS : IsCompact S := hK.prod isCompact_Icc
  have hq : ∀ p ∈ S, slitSegment p ∈ slitPlane :=
    fun p hp => slitSegment_mem (hKs hp.1) hp.2
  have hc : Continuous slitSegment := by unfold slitSegment; fun_prop
  obtain ⟨c, hc0, hc⟩ := hS.exists_forall_le' hc.norm.continuousOn
    (fun p hp => norm_pos_iff.mpr (slitPlane_ne_zero (hq p hp)))
  have hl : ContinuousOn (fun p => Complex.log (slitSegment p)) S := by
    intro p hp
    exact ((Complex.hasDerivAt_log (hq p hp)).continuousAt.comp
      (by unfold slitSegment; fun_prop)).continuousWithinAt
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hl
  refine ⟨c, |B| + 1, hc0, by positivity, fun z hz x hx => ?_⟩
  have hd : 0 < 1 + x := by linarith only [hx]
  have hu : x / (1 + x) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hx hd.le
    · exact (div_le_one hd).mpr (by linarith)
  have hv : 1 / (1 + x) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hd).mpr (by linarith)
  have he : ((1 + x : ℝ) : ℂ) * slitSegment (z, x / (1 + x)) = 1 + z * (x : ℂ) := by
    unfold slitSegment
    push_cast
    have hdC : (1 : ℂ) + (x : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp [hdC]
    ring
  have hf : ((1 + x : ℝ) : ℂ) * slitSegment (z, 1 / (1 + x)) = z + (x : ℂ) := by
    unfold slitSegment
    push_cast
    have hdC : (1 : ℂ) + (x : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp [hdC]
    ring
  have hn : ‖((1 + x : ℝ) : ℂ)‖ = 1 + x := Complex.norm_of_nonneg hd.le
  refine ⟨?_, ?_, ?_⟩
  · rw [← hf, norm_mul, hn]
    calc c * (1 + x) = (1 + x) * c := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc (z, 1 / (1 + x)) ⟨hz, hv⟩) hd.le
  · rw [← he, norm_mul, hn]
    calc c * (1 + x) = (1 + x) * c := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc (z, x / (1 + x)) ⟨hz, hu⟩) hd.le
  · rw [← he, Complex.log_ofReal_mul hd (slitPlane_ne_zero (hq _ ⟨hz, hu⟩))]
    calc
      _ ≤ ‖(Real.log (1 + x) : ℂ)‖ + ‖Complex.log (slitSegment (z, x / (1 + x)))‖ :=
        norm_add_le _ _
      _ = Real.log (1 + x) + ‖Complex.log (slitSegment (z, x / (1 + x)))‖ := by
        rw [Complex.norm_of_nonneg (Real.log_nonneg (by linarith))]
      _ ≤ Real.log (1 + x) + (|B| + 1) := by
        have hb := hB (z, x / (1 + x)) ⟨hz, hu⟩
        linarith only [hb, le_abs_self B]

private theorem logarithmicLaplaceSymbol_re (z : ℂ) :
    (logarithmicLaplaceSymbol z).re = 1 + (1 / 2 : ℝ) * Real.log ‖1 + z‖ := by
  simp only [logarithmicLaplaceSymbol, Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.log_re]

/-- The nested logarithm has logarithmic growth uniformly on compact families of slit rays. -/
private theorem compact_logarithmic_symbol_bound {K : Set ℂ} (hK : IsCompact K)
    (hKs : K ⊆ slitPlane) :
    ∃ D : ℝ, 0 < D ∧ ∀ z ∈ K, ∀ x : ℝ, 0 ≤ x →
      ‖Complex.log (logarithmicLaplaceSymbol (z * (x : ℂ)))‖ ≤ D + Real.log (1 + x) := by
  obtain ⟨c, C, hc, hC, hbase⟩ := compact_slit_ray_bounds hK hKs
  let T : ℝ := Real.exp (2 - Real.log c)
  have hT : 0 < T := Real.exp_pos _
  let S : Set (ℂ × ℝ) := K ×ˢ Icc (0 : ℝ) T
  have hS : IsCompact S := hK.prod isCompact_Icc
  have hgc : ContinuousOn (fun p : ℂ × ℝ => logarithmicLaplaceSymbol (p.1 * (p.2 : ℂ))) S := by
    intro p hp
    have hlin : ContinuousAt (fun q : ℂ × ℝ => 1 + q.1 * (q.2 : ℂ)) p := by fun_prop
    have hl : ContinuousAt (fun q : ℂ × ℝ => Complex.log (1 + q.1 * (q.2 : ℂ))) p :=
      ContinuousAt.comp (f := fun q : ℂ × ℝ => 1 + q.1 * (q.2 : ℂ)) (x := p)
        (Complex.hasDerivAt_log (one_add_slit_ray (hKs hp.1) hp.2.1)).continuousAt hlin
    exact (continuousAt_const.add (continuousAt_const.mul hl)).continuousWithinAt
  obtain ⟨b, hb, hblow⟩ := hS.exists_forall_le' hgc.norm
    (fun p hp => norm_pos_iff.mpr
      (slitPlane_ne_zero (logarithmicLaplaceSymbol_slit_ray (hKs hp.1) hp.2.1)))
  let m : ℝ := min b 1
  have hm : 0 < m := lt_min hb zero_lt_one
  have hlow : ∀ z ∈ K, ∀ x : ℝ, 0 ≤ x → m ≤ ‖logarithmicLaplaceSymbol (z * (x : ℂ))‖ := by
    intro z hz x hx
    by_cases hxt : x ≤ T
    · exact (min_le_left b 1).trans (hblow (z, x) ⟨hz, hx, hxt⟩)
    · have hTx : T < x := lt_of_not_ge hxt
      have hlogx : 2 - Real.log c ≤ Real.log (1 + x) := by
        have ht := Real.log_le_log hT (show T ≤ 1 + x by linarith only [hTx])
        simpa only [T, Real.log_exp] using ht
      have hnorm := (hbase z hz x hx).2.1
      have hlog := Real.log_le_log (mul_pos hc (by linarith only [hx])) hnorm
      rw [Real.log_mul hc.ne' (by positivity : (1 + x : ℝ) ≠ 0)] at hlog
      have hre : 1 ≤ (logarithmicLaplaceSymbol (z * (x : ℂ))).re := by
        rw [logarithmicLaplaceSymbol_re]
        linarith only [hlog, hlogx]
      exact (min_le_right b 1).trans (hre.trans (Complex.re_le_norm _))
  refine ⟨|Real.log m| + 1 + C / 2 + Real.pi, by positivity, fun z hz x hx => ?_⟩
  have hlog0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith only [hx])
  have hgn : 0 < ‖logarithmicLaplaceSymbol (z * (x : ℂ))‖ := hm.trans_le (hlow z hz x hx)
  have hgl := Real.log_le_log hm (hlow z hz x hx)
  have hgu := Real.log_le_sub_one_of_pos hgn
  have habs : |Real.log ‖logarithmicLaplaceSymbol (z * (x : ℂ))‖| ≤
      |Real.log m| + ‖logarithmicLaplaceSymbol (z * (x : ℂ))‖ := by
    apply abs_le.mpr
    constructor
    · linarith only [hgl, neg_abs_le (Real.log m), hgn.le]
    · linarith only [hgu, abs_nonneg (Real.log m)]
  have hnorm : ‖logarithmicLaplaceSymbol (z * (x : ℂ))‖ ≤
      1 + (1 / 2 : ℝ) * (Real.log (1 + x) + C) := by
    unfold logarithmicLaplaceSymbol
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖((1 / 2 : ℝ) : ℂ) * Complex.log (1 + z * (x : ℂ))‖ :=
        norm_add_le _ _
      _ = 1 + (1 / 2 : ℝ) * ‖Complex.log (1 + z * (x : ℂ))‖ := by
        rw [norm_one, norm_mul, Complex.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      _ ≤ _ := add_le_add (le_refl 1)
        (mul_le_mul_of_nonneg_left (hbase z hz x hx).2.2 (by norm_num))
  have hl := norm_complex_log_le (logarithmicLaplaceSymbol (z * (x : ℂ)))
  linarith only [hl, habs, hnorm, hlog0]

/-- The slit-plane integral defining the analytic Poisson factor. -/
def complexLogReferenceFactor (z : ℂ) : ℂ :=
  Complex.exp ((1 / (Real.pi : ℂ)) * ∫ t in Ioi (0 : ℝ),
    Complex.sqrt z * Complex.log (logarithmicLaplaceSymbol (z * (t : ℂ) ^ 2)) /
      (z + (t : ℂ) ^ 2))

/-- An integrable majorant for the logarithmic factor integrals. -/
def logFactorMajorant (t : ℝ) : ℝ :=
  (1 + Real.log (1 + t ^ 2)) / (1 + t ^ 2)

theorem integrable_logFactorMajorant : Integrable logFactorMajorant := by
  have hb : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) := integrable_inv_one_add_sq
  have hl : Integrable (fun t : ℝ => Real.log (2 + |t|) * (1 + t ^ 2)⁻¹) := by
    simpa only [one_pow] using integrable_log_mul_inv_sq_add_sq (a := 1) zero_lt_one
  apply (hb.add (hl.const_mul 2)).mono'
  · have hc : Continuous (fun t : ℝ => Real.log (1 + t ^ 2)) :=
      (continuous_const.add (continuous_id.pow 2)).log
        (fun t => (show 0 < 1 + t ^ 2 by positivity).ne')
    exact ((continuous_const.add hc).div (continuous_const.add (continuous_id.pow 2))
      (fun t => (show 0 < 1 + t ^ 2 by positivity).ne')).aestronglyMeasurable
  · filter_upwards with t
    have hlog0 : 0 ≤ Real.log (1 + t ^ 2) :=
      Real.log_nonneg (by nlinarith only [sq_nonneg t])
    have hs : 1 + t ^ 2 ≤ (2 + |t|) ^ 2 := by
      nlinarith only [sq_abs t, abs_nonneg t]
    have hlog := Real.log_le_log (by positivity : 0 < 1 + t ^ 2) hs
    rw [Real.log_pow] at hlog
    norm_num only [Nat.cast_ofNat] at hlog
    have hmul := mul_le_mul_of_nonneg_right hlog
      (show 0 ≤ (1 + t ^ 2)⁻¹ by positivity)
    change ‖logFactorMajorant t‖ ≤ (1 + t ^ 2)⁻¹ +
      2 * (Real.log (2 + |t|) * (1 + t ^ 2)⁻¹)
    rw [logFactorMajorant, Real.norm_of_nonneg (by positivity), div_eq_mul_inv, add_mul, one_mul]
    nlinarith only [hmul]

private def complexLogFactorIntegrand (z : ℂ) (t : ℝ) : ℂ :=
  Complex.sqrt z * Complex.log (logarithmicLaplaceSymbol (z * (t : ℂ) ^ 2)) /
    (z + (t : ℂ) ^ 2)

private theorem continuous_complexLogFactorIntegrand {z : ℂ} (hz : z ∈ slitPlane) :
    Continuous (complexLogFactorIntegrand z) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hb : 1 + z * (t : ℂ) ^ 2 ∈ slitPlane := by
    simpa only [Complex.ofReal_pow] using one_add_slit_ray hz (sq_nonneg t)
  have hg : logarithmicLaplaceSymbol (z * (t : ℂ) ^ 2) ∈ slitPlane := by
    simpa only [Complex.ofReal_pow] using logarithmicLaplaceSymbol_slit_ray hz (sq_nonneg t)
  have hc : ContinuousAt (fun u : ℝ => logarithmicLaplaceSymbol (z * (u : ℂ) ^ 2)) t := by
    have hlin : ContinuousAt (fun u : ℝ => 1 + z * (u : ℂ) ^ 2) t := by fun_prop
    have hl : ContinuousAt (fun u : ℝ => Complex.log (1 + z * (u : ℂ) ^ 2)) t :=
      ContinuousAt.comp (f := fun u : ℝ => 1 + z * (u : ℂ) ^ 2) (x := t)
        (Complex.hasDerivAt_log hb).continuousAt hlin
    exact continuousAt_const.add (continuousAt_const.mul hl)
  have hn : z + (t : ℂ) ^ 2 ≠ 0 := by
    have h := ofReal_add_ne_zero hz (sq_nonneg t)
    simpa only [Complex.ofReal_pow, add_comm] using h
  have hc2 : ContinuousAt
      (fun u : ℝ => Complex.log (logarithmicLaplaceSymbol (z * (u : ℂ) ^ 2))) t :=
    ContinuousAt.comp (f := fun u : ℝ => logarithmicLaplaceSymbol (z * (u : ℂ) ^ 2))
      (x := t) (Complex.hasDerivAt_log hg).continuousAt hc
  have hd : ContinuousAt (fun u : ℝ => z + (u : ℂ) ^ 2) t := by fun_prop
  exact (continuousAt_const.mul hc2).div hd hn

private theorem differentiableAt_complexLogFactorIntegrand {z : ℂ} (hz : z ∈ slitPlane)
    (t : ℝ) : DifferentiableAt ℂ (fun w => complexLogFactorIntegrand w t) z := by
  have hb : 1 + z * (t : ℂ) ^ 2 ∈ slitPlane := by
    simpa only [Complex.ofReal_pow] using one_add_slit_ray hz (sq_nonneg t)
  have hg : logarithmicLaplaceSymbol (z * (t : ℂ) ^ 2) ∈ slitPlane := by
    simpa only [Complex.ofReal_pow] using logarithmicLaplaceSymbol_slit_ray hz (sq_nonneg t)
  have hn : z + (t : ℂ) ^ 2 ≠ 0 := by
    have h := ofReal_add_ne_zero hz (sq_nonneg t)
    simpa only [Complex.ofReal_pow, add_comm] using h
  have hmul : DifferentiableAt ℂ (fun w : ℂ => w * (t : ℂ) ^ 2) z := by fun_prop
  have hl : DifferentiableAt ℂ
      (fun w : ℂ => Complex.log (logarithmicLaplaceSymbol (w * (t : ℂ) ^ 2))) z := by
    simpa only [Function.comp_def] using!
      (differentiableAt_logarithmicLogSymbol hb hg).comp z hmul
  have hd : DifferentiableAt ℂ (fun w : ℂ => w + (t : ℂ) ^ 2) z := by fun_prop
  simpa only [complexLogFactorIntegrand] using!
    ((Complex.differentiableAt_sqrt hz).mul hl).div hd hn

private theorem compact_complexLogFactorIntegrand_bound {K : Set ℂ} (hK : IsCompact K)
    (hKs : K ⊆ slitPlane) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ K, ∀ t : ℝ,
      ‖complexLogFactorIntegrand z t‖ ≤ B * logFactorMajorant t := by
  obtain ⟨c, C, hc, _, hden⟩ := compact_slit_ray_bounds hK hKs
  obtain ⟨D, hD, hlog⟩ := compact_logarithmic_symbol_bound hK hKs
  have hsqrt : ContinuousOn Complex.sqrt K := by
    intro z hz
    exact (Complex.differentiableAt_sqrt (hKs hz)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hsqrt
  refine ⟨(|M| + 1) * (D + 1) / c, by positivity, fun z hz t => ?_⟩
  have ht : 0 < 1 + t ^ 2 := by positivity
  have hl0 : 0 ≤ Real.log (1 + t ^ 2) :=
    Real.log_nonneg (by nlinarith only [sq_nonneg t])
  have hdb : c * (1 + t ^ 2) ≤ ‖z + (t : ℂ) ^ 2‖ := by
    simpa only [Complex.ofReal_pow] using (hden z hz (t ^ 2) (sq_nonneg t)).1
  have hlb : ‖Complex.log (logarithmicLaplaceSymbol (z * (t : ℂ) ^ 2))‖ ≤
      D + Real.log (1 + t ^ 2) := by
    simpa only [Complex.ofReal_pow] using hlog z hz (t ^ 2) (sq_nonneg t)
  have hsr : ‖Complex.sqrt z‖ ≤ |M| + 1 := by
    linarith only [hM z hz, le_abs_self M]
  have hnum : ‖Complex.sqrt z‖ *
      ‖Complex.log (logarithmicLaplaceSymbol (z * (t : ℂ) ^ 2))‖ ≤
        (|M| + 1) * (D + Real.log (1 + t ^ 2)) :=
    mul_le_mul hsr hlb (norm_nonneg _) (by positivity)
  have hDlog : D + Real.log (1 + t ^ 2) ≤ (D + 1) * (1 + Real.log (1 + t ^ 2)) := by
    nlinarith only [mul_nonneg hD.le hl0]
  unfold complexLogFactorIntegrand
  rw [norm_div, norm_mul]
  calc
    _ ≤ ((|M| + 1) * (D + Real.log (1 + t ^ 2))) / (c * (1 + t ^ 2)) :=
      div_le_div₀ (by positivity) hnum (mul_pos hc ht) hdb
    _ ≤ ((|M| + 1) * ((D + 1) * (1 + Real.log (1 + t ^ 2)))) /
        (c * (1 + t ^ 2)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hDlog (by positivity)) (by positivity)
    _ = _ := by
      simp only [logFactorMajorant, div_eq_mul_inv, mul_inv_rev]
      ring

/-- The literal complex factor is holomorphic on the slit plane. -/
theorem differentiableOn_complexLogReferenceFactor :
    DifferentiableOn ℂ complexLogReferenceFactor slitPlane := by
  intro z hz
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp Complex.isOpen_slitPlane z hz
  let R : ℝ := r / 2
  have hR : 0 < R := by dsimp only [R]; positivity
  have hKs : closedBall z R ⊆ slitPlane := by
    intro w hw
    apply hrs
    apply Metric.mem_ball.mpr
    exact (Metric.mem_closedBall.mp hw).trans_lt (by dsimp only [R]; linarith only [hr])
  obtain ⟨B, hB, hb⟩ := compact_complexLogFactorIntegrand_bound (isCompact_closedBall z R) hKs
  have hdiff : DifferentiableAt ℂ
      (fun w : ℂ => ∫ t in Ioi (0 : ℝ), complexLogFactorIntegrand w t) z := by
    apply differentiableAt_integral_of_cauchy_dominated
      (μ := volume.restrict (Ioi (0 : ℝ))) (bound := fun t => B * logFactorMajorant t) hR
    · intro w hw
      exact (continuous_complexLogFactorIntegrand (hKs (ball_subset_closedBall hw))).aestronglyMeasurable
    · intro t w hw
      exact (differentiableAt_complexLogFactorIntegrand (hKs (ball_subset_closedBall hw)) t).differentiableWithinAt
    · intro t w hw
      exact hb w (ball_subset_closedBall hw) t
    · exact (integrable_logFactorMajorant.const_mul B).integrableOn
  exact ((hdiff.const_mul (1 / (Real.pi : ℂ))).cexp).differentiableWithinAt

private theorem integral_Ioi_dilate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {c : ℝ} (hc : 0 < c) (f : ℝ → E) :
    (∫ t in Ioi (0 : ℝ), f t) = ∫ u in Ioi (0 : ℝ), c • f (c * u) := by
  have hi : Set.InjOn (fun u : ℝ => c * u) (Ioi (0 : ℝ)) := by
    intro u _ v _ huv
    exact mul_left_cancel₀ hc.ne' huv
  have hd (u : ℝ) (_ : u ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt (fun u : ℝ => c * u) c (Ioi (0 : ℝ)) u := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id u).const_mul c).hasDerivWithinAt
  have him : (fun u : ℝ => c * u) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mul_pos hc hu
    · intro ht
      refine ⟨t / c, div_pos ht hc, ?_⟩
      field_simp
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hi f
  simpa only [him, abs_of_pos hc] using h

private theorem complex_sqrt_ofReal {s : ℝ} (hs : 0 < s) :
    Complex.sqrt (s : ℂ) = (Real.sqrt s : ℂ) := by
  have hc : (0 : ℂ) ≤ (s : ℂ) := by exact_mod_cast hs.le
  simpa only [Complex.ofReal_re] using Complex.sqrt_of_nonneg hc

private theorem complexLogFactorIntegrand_ofReal {s : ℝ} (hs : 0 < s) (t : ℝ) :
    complexLogFactorIntegrand (s : ℂ) t =
      ((Real.sqrt s * Real.log (positiveLogarithmicSymbol (Real.sqrt s * t)) /
        (s + t ^ 2) : ℝ) : ℂ) := by
  have hr : ((Real.sqrt s : ℝ) : ℂ) ^ 2 = (s : ℂ) := by
    exact_mod_cast Real.sq_sqrt hs.le
  have he : (s : ℂ) * (t : ℂ) ^ 2 = ((Real.sqrt s * t : ℝ) : ℂ) ^ 2 := by
    push_cast
    rw [mul_pow, hr]
  unfold complexLogFactorIntegrand
  rw [complex_sqrt_ofReal hs, he, logarithmicLaplaceSymbol_ofReal_sq,
    ← Complex.ofReal_log (zero_le_one.trans (one_le_positiveLogarithmicSymbol _))]
  push_cast
  rfl

/-- The slit-plane factor agrees exactly with the positive real Poisson factor. -/
theorem complexLogReferenceFactor_ofReal {s : ℝ} (hs : 0 < s) :
    complexLogReferenceFactor (s : ℂ) = (logReferenceFactor s : ℂ) := by
  let r : ℝ := Real.sqrt s
  have hr : 0 < r := Real.sqrt_pos.mpr hs
  have hrs : r ^ 2 = s := Real.sq_sqrt hs.le
  let g : ℝ → ℝ := fun t => s * Real.log (positiveLogarithmicSymbol t) / (s ^ 2 + t ^ 2)
  have hpoint (u : ℝ) : r • complexLogFactorIntegrand (s : ℂ) (r * u) =
      ((s * g (s * u) : ℝ) : ℂ) := by
    rw [complexLogFactorIntegrand_ofReal hs, Complex.real_smul, ← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    have harg : r * (r * u) = s * u := by
      calc r * (r * u) = r ^ 2 * u := by ring
        _ = s * u := by rw [hrs]
    change r * (r * Real.log (positiveLogarithmicSymbol (r * (r * u))) /
      (s + (r * u) ^ 2)) = s * g (s * u)
    rw [harg]
    have hcoef : r * r / (s + (r * u) ^ 2) =
        s * s / (s ^ 2 + (s * u) ^ 2) := by
      rw [← pow_two r, mul_pow, hrs, mul_pow]
      have hd : 1 + u ^ 2 ≠ 0 := by positivity
      rw [show s + s * u ^ 2 = s * (1 + u ^ 2) by ring,
        show s ^ 2 + s ^ 2 * u ^ 2 = s ^ 2 * (1 + u ^ 2) by ring]
      field_simp [hs.ne', hd]
    dsimp only [g]
    calc
      _ = (r * r / (s + (r * u) ^ 2)) * Real.log (positiveLogarithmicSymbol (s * u)) := by ring
      _ = (s * s / (s ^ 2 + (s * u) ^ 2)) * Real.log (positiveLogarithmicSymbol (s * u)) := by rw [hcoef]
      _ = _ := by ring
  have hchange := integral_Ioi_dilate hr (complexLogFactorIntegrand (s : ℂ))
  have hreal := integral_Ioi_dilate hs g
  simp only [smul_eq_mul] at hreal
  rw [show (fun u => r • complexLogFactorIntegrand (s : ℂ) (r * u)) =
    (fun u => ((s * g (s * u) : ℝ) : ℂ)) from funext hpoint,
    integral_complex_ofReal, ← hreal] at hchange
  change Complex.exp ((1 / (Real.pi : ℂ)) *
    ∫ t in Ioi (0 : ℝ), complexLogFactorIntegrand (s : ℂ) t) = _
  rw [hchange, logReferenceFactor_eq_poisson hs, Complex.ofReal_exp]
  congr 1
  dsimp only [g]
  push_cast
  rfl

theorem complexLogReferenceFactor_ne_zero (z : ℂ) : complexLogReferenceFactor z ≠ 0 :=
  Complex.exp_ne_zero _

private theorem logarithmicLaplaceSymbol_conj {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    logarithmicLaplaceSymbol ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (logarithmicLaplaceSymbol z) := by
  have he : 1 + (starRingEnd ℂ) z = (starRingEnd ℂ) (1 + z) := by simp
  unfold logarithmicLaplaceSymbol
  rw [he, Complex.log_conj _ (Complex.mem_slitPlane_iff_arg.mp hz).1]
  simp only [map_add, map_mul, map_one, Complex.conj_ofReal]

private theorem complex_sqrt_conj {z : ℂ} (hz : z ∈ slitPlane) :
    Complex.sqrt ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Complex.sqrt z) := by
  have hc : (starRingEnd ℂ) z ∈ slitPlane := by
    simpa only [Complex.mem_slitPlane_iff, Complex.conj_re, Complex.conj_im, neg_ne_zero] using hz
  rw [sqrt_eq_exp (slitPlane_ne_zero hc), sqrt_eq_exp (slitPlane_ne_zero hz),
    Complex.log_conj _ (Complex.mem_slitPlane_iff_arg.mp hz).1, ← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_ofNat]

private theorem complexLogFactorIntegrand_conj {z : ℂ} (hz : z ∈ slitPlane) (t : ℝ) :
    complexLogFactorIntegrand ((starRingEnd ℂ) z) t =
      (starRingEnd ℂ) (complexLogFactorIntegrand z t) := by
  have hb : 1 + z * (t : ℂ) ^ 2 ∈ slitPlane := by
    simpa only [Complex.ofReal_pow] using one_add_slit_ray hz (sq_nonneg t)
  have hg : logarithmicLaplaceSymbol (z * (t : ℂ) ^ 2) ∈ slitPlane := by
    simpa only [Complex.ofReal_pow] using logarithmicLaplaceSymbol_slit_ray hz (sq_nonneg t)
  have he : (starRingEnd ℂ) z * (t : ℂ) ^ 2 =
      (starRingEnd ℂ) (z * (t : ℂ) ^ 2) := by simp
  unfold complexLogFactorIntegrand
  rw [complex_sqrt_conj hz, he, logarithmicLaplaceSymbol_conj hb,
    Complex.log_conj _ (Complex.mem_slitPlane_iff_arg.mp hg).1]
  simp only [map_div₀, map_mul, map_add, map_pow, Complex.conj_ofReal]

/-- Conjugation symmetry of the actual analytic factor. -/
theorem complexLogReferenceFactor_conj {z : ℂ} (hz : z ∈ slitPlane) :
    complexLogReferenceFactor ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (complexLogReferenceFactor z) := by
  have he : complexLogFactorIntegrand ((starRingEnd ℂ) z) =
      (fun t => (starRingEnd ℂ) (complexLogFactorIntegrand z t)) :=
    funext (complexLogFactorIntegrand_conj hz)
  change Complex.exp ((1 / (Real.pi : ℂ)) * ∫ t in Ioi (0 : ℝ),
    complexLogFactorIntegrand ((starRingEnd ℂ) z) t) =
      (starRingEnd ℂ) (Complex.exp ((1 / (Real.pi : ℂ)) * ∫ t in Ioi (0 : ℝ),
        complexLogFactorIntegrand z t))
  rw [he, integral_conj, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_div₀, map_one, Complex.conj_ofReal]

#print axioms differentiableOn_complexLogReferenceFactor
#print axioms complexLogReferenceFactor_ofReal
#print axioms complexLogReferenceFactor_conj


end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
