import GaloisForLFunctions.MultiscaleMollifiedZetaField.TwistedSecondMomentsBelowSquareRoot
import GaloisForLFunctions.RHTower.ZetaStripPolynomialBound
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Polynomial derivative bounds for the actual twisted moment

Replacing the squared modulus by the product at opposite heights gives a
holomorphic displacement parameter. The elementary zeta strip bound and
finite polynomial length bound dominate this integral. Cauchy's estimate
then controls every displacement derivative with an explicit constant.
-/

open Complex Filter MeasureTheory Metric Set Topology
open RHTower RHTower.ZetaGateProductAFE
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The actual mollified zeta function at a complex displacement. -/
def twistedMomentField (N : ℕ) (w : ℕ → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  riemannZeta ((1 / 2 : ℂ) - z + (t : ℂ) * I) *
    edPoly (fun n => (w n : ℂ)) (Finset.Icc 1 N)
      ((1 / 2 : ℂ) - z + (t : ℂ) * I)

/-- Holomorphic continuation of the real-displacement squared moment. -/
def holomorphicTwistedMoment (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∫ t, blockWindowC p q η t *
    (twistedMomentField N w z t * twistedMomentField N w z (-t))

/-- On real displacements the continuation equals the actual squared moment. -/
theorem holomorphicTwistedMoment_ofReal {d : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20)
    (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) :
    holomorphicTwistedMoment p q η N w (d : ℂ) =
      (twistedMoment d p q η N w : ℂ) := by
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hreal : ∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (w n : ℂ) = (w n : ℂ) :=
    fun n _ => Complex.conj_ofReal _
  have hpoint (u : ℝ) : (1 / 2 : ℂ) - (d : ℂ) + (u : ℂ) * I = displacedLinePt d u := by
    simp only [displacedLinePt, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat]
  unfold holomorphicTwistedMoment twistedMoment
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Complex.ofReal_mul, blockWindowC, twistedMomentField, hpoint]
  congr 1
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_mul,
    ← riemannZeta_conj_of_re_pos (displacedLinePt_re_pos (by linarith only [hd20]) t)
      (displacedLinePt_ne_one hd t),
    ← edPoly_conj (fun n => (w n : ℂ)) hs hreal,
    ← displacedLinePt_neg_eq_conj' d t]

private theorem momentPoint_ne_one {z : ℂ} (hz : |z.re| ≤ 1 / 4) (t : ℝ) :
    (1 / 2 : ℂ) - z + (t : ℂ) * I ≠ 1 := by
  intro he
  have hre := congrArg Complex.re he
  have hzlo := (abs_le.mp hz).1
  norm_num at hre
  linarith only [hre, hzlo]

private theorem continuous_twistedMomentField_height (N : ℕ) (w : ℕ → ℝ)
    {z : ℂ} (hz : |z.re| ≤ 1 / 4) : Continuous (twistedMomentField N w z) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hp : ContinuousAt (fun u : ℝ => (1 / 2 : ℂ) - z + (u : ℂ) * I) t := by fun_prop
  exact ((differentiableAt_riemannZeta (momentPoint_ne_one hz t)).continuousAt.comp
    (f := fun u : ℝ => (1 / 2 : ℂ) - z + (u : ℂ) * I) hp).mul
    (((differentiable_edPoly (fun n => (w n : ℂ))
      (fun n hn => (Finset.mem_Icc.mp hn).1)) _).continuousAt.comp
        (f := fun u : ℝ => (1 / 2 : ℂ) - z + (u : ℂ) * I) hp)

private theorem differentiableOn_twistedMomentField (N : ℕ) (w : ℕ → ℝ) (t : ℝ) :
    DifferentiableOn ℂ (fun z => twistedMomentField N w z t) (ball 0 (1 / 4)) := by
  intro z hz
  have hn : ‖z‖ < 1 / 4 := by simpa only [mem_ball, dist_zero_right] using hz
  have hzre : |z.re| ≤ 1 / 4 :=
    (Complex.abs_re_le_norm z).trans hn.le
  have hp : DifferentiableAt ℂ (fun v : ℂ => (1 / 2 : ℂ) - v + (t : ℂ) * I) z := by fun_prop
  exact (((differentiableAt_riemannZeta (momentPoint_ne_one hzre t)).comp z hp).mul
    ((differentiable_edPoly (fun n => (w n : ℂ))
      (fun n hn => (Finset.mem_Icc.mp hn).1) _).comp z hp)).differentiableWithinAt

private theorem moment_edPoly_bound {N : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖edPoly (fun n => (w n : ℂ)) (Finset.Icc 1 N) s‖ ≤ N := by
  refine (norm_edPoly_le _ (fun n hn => (Finset.mem_Icc.mp hn).1) s).trans ?_
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hp := Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr hs)
      simpa only [Complex.norm_real, Real.norm_eq_abs, one_mul] using
        mul_le_mul (hw n hn) hp (Real.rpow_nonneg (by positivity) _) zero_le_one
    _ = _ := by simp

private theorem norm_twistedMomentField_le {N : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ 1) {z : ℂ} (hzre : |z.re| ≤ 1 / 4)
    (hzim : |z.im| ≤ 1) {t : ℝ} (ht : 4 ≤ |t|) :
    ‖twistedMomentField N w z t‖ ≤ (2 + 8 * (|t| + 1)) * N := by
  have hsre : 1 / 4 ≤ ((1 / 2 : ℂ) - z + (t : ℂ) * I).re := by
    have hh := (abs_le.mp hzre).2
    norm_num
    linarith only [hh]
  have hsim : ((1 / 2 : ℂ) - z + (t : ℂ) * I).im = t - z.im := by simp; ring
  have himup : |t - z.im| ≤ |t| + 1 := (abs_sub t z.im).trans (by linarith only [hzim])
  have himlo : 2 ≤ |t - z.im| := by
    have hh := abs_add_le (t - z.im) z.im
    rw [sub_add_cancel] at hh
    linarith only [hh, hzim, ht]
  have hζ := norm_riemannZeta_le_quarter hsre (by simpa only [hsim] using himlo)
  rw [hsim] at hζ
  have hζ' : ‖riemannZeta ((1 / 2 : ℂ) - z + (t : ℂ) * I)‖ ≤ 2 + 8 * (|t| + 1) := by
    linarith only [hζ, himup]
  unfold twistedMomentField
  rw [norm_mul]
  exact mul_le_mul hζ' (moment_edPoly_bound hw (by linarith only [hsre]))
    (norm_nonneg _) (by positivity)

private theorem moment_kernel_bound {p q η : ℝ} (hη : 0 < η) (hp : 4 ≤ p - η)
    {N : ℕ} {w : ℕ → ℝ} (hw : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ 1)
    {z : ℂ} (hzre : |z.re| ≤ 1 / 4) (hzim : |z.im| ≤ 1) (t : ℝ) :
    ‖blockWindowC p q η t *
      (twistedMomentField N w z t * twistedMomentField N w z (-t))‖ ≤
        blockWindow p q η t * ((2 + 8 * (q + η + 1)) * N) ^ 2 := by
  by_cases ht : t ∈ Icc (p - η) (q + η)
  · have ht0 : 0 ≤ t := by linarith only [hp, ht.1]
    have hts : 4 ≤ |t| := by rw [abs_of_nonneg ht0]; exact hp.trans ht.1
    have hA : 0 ≤ (2 + 8 * (q + η + 1)) * (N : ℝ) := by
      have hh : 0 ≤ q + η := ht0.trans ht.2
      positivity
    have hscale : (2 + 8 * (|t| + 1)) * (N : ℝ) ≤
        (2 + 8 * (q + η + 1)) * (N : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [abs_of_nonneg ht0]
      linarith only [ht.2]
    have hplus := (norm_twistedMomentField_le hw hzre hzim hts).trans hscale
    have hminus := norm_twistedMomentField_le hw hzre hzim
      (show 4 ≤ |-t| by simpa only [abs_neg] using hts)
    rw [abs_neg] at hminus
    have hprod := mul_le_mul hplus (hminus.trans hscale) (norm_nonneg _) hA
    rw [norm_mul, norm_mul, norm_blockWindowC_eq]
    exact mul_le_mul_of_nonneg_left (by simpa only [pow_two] using hprod)
      (blockWindow_nonneg p q η t)
  · rw [blockWindowC_eq_zero hη ht]
    have hzero : blockWindow p q η t = 0 := by
      by_contra hn
      exact ht (support_blockWindow_subset hη hn)
    simp only [hzero, zero_mul, norm_zero, le_refl]

/-- The continuation has a uniform polynomial bound throughout a fixed complex strip. -/
theorem norm_holomorphicTwistedMoment_le {p q η : ℝ} (hη : 0 < η) (hpq : p ≤ q)
    (hp : 4 ≤ p - η) {N : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ 1) {z : ℂ}
    (hzre : |z.re| ≤ 1 / 4) (hzim : |z.im| ≤ 1) :
    ‖holomorphicTwistedMoment p q η N w z‖ ≤
      (q - p + 2 * η) * ((2 + 8 * (q + η + 1)) * N) ^ 2 := by
  have hW : Integrable (blockWindow p q η) volume :=
    (contDiff_blockWindow p q η).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_blockWindow hη)
  have hb := hW.mul_const (((2 + 8 * (q + η + 1)) * (N : ℝ)) ^ 2)
  have hbound := norm_integral_le_of_norm_le hb
    (Eventually.of_forall (moment_kernel_bound hη hp hw hzre hzim))
  unfold holomorphicTwistedMoment
  refine hbound.trans ?_
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (integral_blockWindow_le hη hpq) (sq_nonneg _)

/-- The actual opposite-height product is holomorphic before taking any displacement derivatives. -/
theorem differentiableOn_holomorphicTwistedMoment {p q η : ℝ} (hη : 0 < η)
    (hp : 4 ≤ p - η) {N : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ 1) :
    DifferentiableOn ℂ (holomorphicTwistedMoment p q η N w) (ball 0 (1 / 4)) := by
  intro z hz
  have hz0 : ‖z‖ < 1 / 4 := by simpa only [mem_ball, dist_zero_right] using hz
  let R : ℝ := (1 / 4 - ‖z‖) / 2
  have hR : 0 < R := by dsimp only [R]; linarith only [hz0]
  have hsub : ball z R ⊆ ball (0 : ℂ) (1 / 4) := by
    intro v hv
    have hh := norm_add_le (v - z) z
    rw [sub_add_cancel] at hh
    have hv' : ‖v - z‖ < R := by simpa only [mem_ball, dist_eq_norm] using hv
    rw [mem_ball, dist_zero_right]
    dsimp only [R] at hv'
    linarith only [hh, hv', hz0]
  have hparts {v : ℂ} (hv : v ∈ ball z R) : |v.re| ≤ 1 / 4 ∧ |v.im| ≤ 1 := by
    have hn : ‖v‖ ≤ 1 / 4 := by
      exact le_of_lt (by simpa only [mem_ball, dist_zero_right] using hsub hv)
    exact ⟨(Complex.abs_re_le_norm _).trans hn,
      ((Complex.abs_im_le_norm _).trans hn).trans (by norm_num)⟩
  have hW : Integrable (blockWindow p q η) volume :=
    (contDiff_blockWindow p q η).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_blockWindow hη)
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_integral_of_cauchy_dominated (R := R)
    (bound := fun t => blockWindow p q η t * ((2 + 8 * (q + η + 1)) * (N : ℝ)) ^ 2) hR
  · intro v hv
    have hc := continuous_twistedMomentField_height N w (hparts hv).1
    exact ((Complex.continuous_ofReal.comp (contDiff_blockWindow p q η).continuous).mul
      (hc.mul (hc.comp continuous_neg))).aestronglyMeasurable
  · intro t
    exact ((differentiableOn_twistedMomentField N w t).mul
      (differentiableOn_twistedMomentField N w (-t))).const_mul _ |>.mono hsub
  · intro t v hv
    exact moment_kernel_bound hη hp hw (hparts hv).1 (hparts hv).2 t
  · exact hW.mul_const _

/-- Every complex displacement jet is bounded by the same polynomial in height and length. -/
theorem norm_iteratedDeriv_holomorphicTwistedMoment_le {p q η : ℝ}
    (hη : 0 < η) (hpq : p ≤ q) (hp : 4 ≤ p - η) {N : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ 1) {d : ℝ} (hd : 0 ≤ d) (hd20 : d ≤ 1 / 20)
    (n : ℕ) :
    ‖iteratedDeriv n (holomorphicTwistedMoment p q η N w) (d : ℂ)‖ ≤
      (n.factorial : ℝ) * ((q - p + 2 * η) *
        ((2 + 8 * (q + η + 1)) * N) ^ 2) / (1 / 8) ^ n := by
  have hsub : closedBall (d : ℂ) (1 / 8) ⊆ ball (0 : ℂ) (1 / 4) := by
    intro z hz
    have hz' : ‖z - (d : ℂ)‖ ≤ 1 / 8 := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hh := norm_add_le (z - (d : ℂ)) (d : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd] at hh
    rw [mem_ball, dist_zero_right]
    linarith only [hz', hh, hd20]
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num)
    ((differentiableOn_holomorphicTwistedMoment hη hp hw).diffContOnCl_ball hsub)
  intro z hz
  have hn : ‖z‖ ≤ 1 / 4 := le_of_lt (by
    simpa only [mem_ball, dist_zero_right] using hsub (sphere_subset_closedBall hz))
  exact norm_holomorphicTwistedMoment_le hη hpq hp hw
    ((Complex.abs_re_le_norm _).trans hn)
    (((Complex.abs_im_le_norm _).trans hn).trans (by norm_num))

/-- Real displacement jets of the holomorphic squared moment. -/
def realTwistedMomentJet (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) (n : ℕ) (d : ℝ) : ℝ :=
  (iteratedDeriv n (holomorphicTwistedMoment p q η N w) (d : ℂ)).re

theorem realTwistedMomentJet_zero {d : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20)
    (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) :
    realTwistedMomentJet p q η N w 0 d = twistedMoment d p q η N w := by
  simpa only [realTwistedMomentJet, iteratedDeriv_zero, Complex.ofReal_re] using
    congrArg Complex.re (holomorphicTwistedMoment_ofReal hd hd20 p q η N w)

/-- The jets are literal successive derivatives in the real displacement. -/
theorem hasDerivAt_realTwistedMomentJet {p q η : ℝ} (hη : 0 < η)
    (hp : 4 ≤ p - η) {N : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ 1) {d : ℝ} (hd : |d| < 1 / 4) (n : ℕ) :
    HasDerivAt (realTwistedMomentJet p q η N w n)
      (realTwistedMomentJet p q η N w (n + 1) d) d := by
  have hmem : (d : ℂ) ∈ ball (0 : ℂ) (1 / 4) := by
    simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using hd
  have ha : ∀ j : ℕ, AnalyticAt ℂ
      (iteratedDeriv j (holomorphicTwistedMoment p q η N w)) (d : ℂ) := by
    intro j
    induction j with
    | zero =>
      exact (differentiableOn_holomorphicTwistedMoment (q := q) hη hp hw).analyticOnNhd
        isOpen_ball (d : ℂ) hmem
    | succ j hj => simpa only [iteratedDeriv_succ] using hj.deriv
  change HasDerivAt (fun x : ℝ =>
    (iteratedDeriv n (holomorphicTwistedMoment p q η N w) (x : ℂ)).re)
    (iteratedDeriv (n + 1) (holomorphicTwistedMoment p q η N w) (d : ℂ)).re d
  simpa only [iteratedDeriv_succ] using
    (ha n).differentiableAt.hasDerivAt.real_of_complex

/-- Real moment jets inherit the explicit polynomial Cauchy bound. -/
theorem abs_realTwistedMomentJet_le {p q η : ℝ} (hη : 0 < η) (hpq : p ≤ q)
    (hp : 4 ≤ p - η) {N : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 N, |w n| ≤ 1) {d : ℝ} (hd : 0 ≤ d) (hd20 : d ≤ 1 / 20)
    (n : ℕ) :
    |realTwistedMomentJet p q η N w n d| ≤
      (n.factorial : ℝ) * ((q - p + 2 * η) *
        ((2 + 8 * (q + η + 1)) * N) ^ 2) / (1 / 8) ^ n :=
  (Complex.abs_re_le_norm _).trans
    (norm_iteratedDeriv_holomorphicTwistedMoment_le hη hpq hp hw hd hd20 n)

end GaloisForLFunctions.MultiscaleMollifiedZetaField
