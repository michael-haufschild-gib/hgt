import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGaugeAtEveryRoot
import GaloisForLFunctions.BiScaleUncertainty.CubicSplineUniversalProbe
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Uniform derivative bounds for regularized splines

Convolving a smooth probability density with four unit boxes gives a smooth
regularization of the cubic spline. Its first four derivatives have `L¹` norm
at most one, independently of the derivatives of the smoothing density.
Each derivative replaces one box by the difference of its boundary masses.
This retains the knot contributions needed by fourth-order quadrature.
Multiplication by a fixed smooth cutoff equal to the exponential on the
spline support gives the same uniform control for the tilted spline.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped Convolution ContDiff
open RHTower.WeilDeletion

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open BiScaleUncertainty.ChebyshevGauge

/-- Convolution with `n` unit boxes, starting from a smooth density. -/
def boxRegularization (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => g
  | n + 1 => unif 1 ⋆ boxRegularization g n

theorem integrable_boxRegularization {g : ℝ → ℝ} (hg : Integrable g) (n : ℕ) :
    Integrable (boxRegularization g n) := by
  induction n with
  | zero => exact hg
  | succ n ih => exact (integrable_unif 1).integrable_convolution _ ih

theorem hasCompactSupport_boxRegularization {g : ℝ → ℝ} (hg : HasCompactSupport g)
    (n : ℕ) : HasCompactSupport (boxRegularization g n) := by
  induction n with
  | zero => exact hg
  | succ n ih => exact (hasCompactSupport_unif 1).convolution _ ih

theorem contDiff_boxRegularization {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (n : ℕ) : ContDiff ℝ ∞ (boxRegularization g n) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
      exact (hasCompactSupport_boxRegularization hgc n).contDiff_convolution_right _
        (integrable_unif 1).locallyIntegrable ih

theorem boxRegularization_nonneg {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) (n : ℕ) (x : ℝ) :
    0 ≤ boxRegularization g n x := by
  induction n generalizing x with
  | zero => exact hg x
  | succ n ih =>
      change 0 ≤ (unif 1 ⋆ boxRegularization g n) x
      rw [convolution_def]
      exact integral_nonneg fun t => mul_nonneg (unif_nonneg one_pos t) (ih _)

theorem integral_boxRegularization {g : ℝ → ℝ} (hg : Integrable g) (n : ℕ) :
    (∫ x, boxRegularization g n x) = ∫ x, g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (∫ x, (unif 1 ⋆ boxRegularization g n) x) = _
      rw [integral_convolution _ (integrable_unif 1) (integrable_boxRegularization hg n)]
      simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, integral_unif one_pos,
        one_mul] using ih

/-- Differentiating one box integral leaves its two endpoint values. -/
theorem deriv_unif_one_convolution {g : ℝ → ℝ} (hg : Continuous g) (hgi : Integrable g) :
    deriv (unif 1 ⋆ g) = fun x => (1 / 2 : ℝ) * (g (x + 1) - g (x - 1)) := by
  have heq : unif 1 ⋆ g = fun x => (1 / 2 : ℝ) *
      ((∫ t in (0 : ℝ)..x + 1, g t) - ∫ t in (0 : ℝ)..x - 1, g t) := by
    funext x
    simpa using unif_convolution_eq one_pos hgi x
  rw [heq]
  funext x
  have hp := fun u => (hg.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hplus := (hp (x + 1)).comp x ((hasDerivAt_id x).add_const 1)
  have hminus := (hp (x - 1)).comp x ((hasDerivAt_id x).sub_const 1)
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, mul_one] using
    ((hplus.sub hminus).const_mul (1 / 2 : ℝ)).deriv

/-- Every derivative removes a box and takes an endpoint difference. -/
theorem iteratedDeriv_boxRegularization_succ {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (n q : ℕ) (x : ℝ) :
    iteratedDeriv (q + 1) (boxRegularization g (n + 1)) x =
      (1 / 2 : ℝ) * (iteratedDeriv q (boxRegularization g n) (x + 1) -
        iteratedDeriv q (boxRegularization g n) (x - 1)) := by
  have hn := contDiff_boxRegularization hg hgc n
  have hi := integrable_boxRegularization (hg.continuous.integrable_of_hasCompactSupport hgc) n
  have hp : ContDiff ℝ ∞ (fun y => boxRegularization g n (y + 1)) :=
    hn.comp (contDiff_id.add contDiff_const)
  have hm : ContDiff ℝ ∞ (fun y => boxRegularization g n (y - 1)) :=
    hn.comp (contDiff_id.sub contDiff_const)
  rw [iteratedDeriv_succ', boxRegularization, deriv_unif_one_convolution hn.continuous hi,
    iteratedDeriv_const_mul _ (contDiffAt_of_smooth (hp.sub hm) q x),
    iteratedDeriv_fun_sub (contDiffAt_of_smooth hp q x) (contDiffAt_of_smooth hm q x),
    iteratedDeriv_comp_add_const, iteratedDeriv_comp_sub_const]

/-- The endpoint difference does not increase the `L¹` norm. -/
theorem integral_abs_iteratedDeriv_boxRegularization_succ_le {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (n q : ℕ) :
    (∫ x, |iteratedDeriv (q + 1) (boxRegularization g (n + 1)) x|) ≤
      ∫ x, |iteratedDeriv q (boxRegularization g n) x| := by
  have hn := contDiff_boxRegularization hg hgc n
  have hi : Integrable (fun x => |iteratedDeriv q (boxRegularization g n) x|) :=
    ((hn.continuous_iteratedDeriv q (natCast_le_infty q)).integrable_of_hasCompactSupport
      (hasCompactSupport_iteratedDeriv (hasCompactSupport_boxRegularization hgc n) q)).abs
  have hp := hi.comp_add_right 1
  have hm := hi.comp_sub_right 1
  calc
    (∫ x, |iteratedDeriv (q + 1) (boxRegularization g (n + 1)) x|) ≤
        ∫ x, (1 / 2 : ℝ) * (|iteratedDeriv q (boxRegularization g n) (x + 1)| +
          |iteratedDeriv q (boxRegularization g n) (x - 1)|) := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
        ((hp.add hm).const_mul _) (Eventually.of_forall fun x => ?_)
      change |iteratedDeriv (q + 1) (boxRegularization g (n + 1)) x| ≤
        (1 / 2 : ℝ) * (|iteratedDeriv q (boxRegularization g n) (x + 1)| +
          |iteratedDeriv q (boxRegularization g n) (x - 1)|)
      rw [iteratedDeriv_boxRegularization_succ hg hgc, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
    _ = ∫ x, |iteratedDeriv q (boxRegularization g n) x| := by
      rw [integral_const_mul, integral_add hp hm,
        integral_add_right_eq_self (fun x => |iteratedDeriv q (boxRegularization g n) x|),
        integral_sub_right_eq_self (fun x => |iteratedDeriv q (boxRegularization g n) x|)]
      ring

/-- Up to the number of boxes, derivative norms depend only on the mass of the
smoothing density. In particular, four boxes bound the fourth derivative. -/
theorem integral_abs_iteratedDeriv_boxRegularization_le {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hg0 : ∀ x, 0 ≤ g x)
    (n q : ℕ) (hq : q ≤ n) :
    (∫ x, |iteratedDeriv q (boxRegularization g n) x|) ≤ ∫ x, g x := by
  induction q generalizing n with
  | zero =>
      simp only [iteratedDeriv_zero,
        abs_of_nonneg (boxRegularization_nonneg hg0 n _)]
      exact (integral_boxRegularization (hg.continuous.integrable_of_hasCompactSupport hgc) n).le
  | succ q ih =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact (integral_abs_iteratedDeriv_boxRegularization_succ_le hg hgc m q).trans
        (ih m (by omega))

private theorem real_convolution_assoc_compact {f h g : ℝ → ℝ}
    (hf : Integrable f) (hh : Integrable h) (hhc : HasCompactSupport h)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    (f ⋆ h) ⋆ g = f ⋆ (h ⋆ g) := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let M := ContinuousLinearMap.mul ℝ ℝ
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hn : HasCompactSupport (fun x => ‖g x‖) := hgc.norm
  have hhn : Continuous ((fun x => ‖h x‖) ⋆[M] fun x => ‖g x‖) :=
    hn.continuous_convolution_right M hh.norm.locallyIntegrable hg.norm
  have hhnc : HasCompactSupport ((fun x => ‖h x‖) ⋆[M] fun x => ‖g x‖) :=
    hhc.norm.convolution M hn
  funext x
  exact convolution_assoc L L L L (fun a b c => mul_assoc a b c)
    hf.aestronglyMeasurable hh.aestronglyMeasurable hg.aestronglyMeasurable
    (hf.ae_convolution_exists L hh) (hh.norm.ae_convolution_exists M hgi.norm)
    (hhnc.convolutionExists_right M hf.norm.locallyIntegrable hhn x)

/-- The regularization is the original box spline convolved with its smoothing density. -/
theorem boxRegularization_eq_upow_convolution {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (n : ℕ) :
    boxRegularization g (n + 1) = upow 1 n ⋆ g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [boxRegularization, ih, upow]
      exact (real_convolution_assoc_compact (integrable_unif 1) (integrable_upow 1 n)
        (hasCompactSupport_upow 1 n) hg hgc).symm

/-- A probability smoothing of radius `ρ` moves the cubic spline by at most its
Lipschitz constant times `ρ`, uniformly on the real line. -/
theorem abs_boxRegularization_four_sub_cubicSpline_le {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hg0 : ∀ x, 0 ≤ g x)
    (hg1 : ∫ x, g x = 1) {ρ L : ℝ} (hgs : ∀ x, ρ < |x| → g x = 0)
    (hL : ∀ x y, |cubicSpline x - cubicSpline y| ≤ L * |x - y|) (x : ℝ) :
    |boxRegularization g 4 x - cubicSpline x| ≤ L * ρ := by
  rw [boxRegularization_eq_upow_convolution hg hgc 3]
  have he := abs_integral_mul_sub_le contDiff_cubicSpline.continuous hg hgc hg1 hgs hL x
  have hmass : (∫ s, |g s|) = 1 := by
    simpa only [abs_of_nonneg (hg0 _)] using hg1
  simpa only [hmass, mul_one, convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, cubicSpline] using he

/-- Support grows by one at each box convolution. -/
theorem support_boxRegularization_subset {g : ℝ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hg : Function.support g ⊆ Icc (-ρ) ρ) (n : ℕ) :
    Function.support (boxRegularization g n) ⊆ Icc (-(ρ + n)) (ρ + n) := by
  induction n with
  | zero => simpa only [boxRegularization, Nat.cast_zero, add_zero] using hg
  | succ n ih =>
      refine (support_convolution_subset _).trans ?_
      refine (Set.add_subset_add (support_unif_subset 1) ih).trans ?_
      rw [Set.Icc_add_Icc (by norm_num) (neg_le_self (by positivity : (0 : ℝ) ≤ ρ + n))]
      apply Set.Icc_subset_Icc <;> push_cast <;> linarith

/-- Arbitrarily close smooth approximations to the cubic spline have first four
`L¹` derivative norms at most one. The bound is uniform in approximation accuracy. -/
theorem exists_cubicSpline_regularization {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      (∀ x, x ∉ Icc (-5) 5 → G x = 0) ∧
      (∀ x, |G x - cubicSpline x| ≤ ε) ∧
      ∀ q : ℕ, q ≤ 4 → (∫ x, |iteratedDeriv q G x|) ≤ 1 := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    hasCompactSupport_cubicSpline contDiff_cubicSpline (by norm_num)
  let ρ : ℝ := min 1 (ε / ((L : ℝ) + 1))
  have hρ : 0 < ρ := lt_min one_pos (div_pos hε (by positivity))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρε : (L : ℝ) * ρ ≤ ε := by
    have hdiv := min_le_right 1 (ε / ((L : ℝ) + 1))
    have hmul := (le_div_iff₀ (by positivity : (0 : ℝ) < (L : ℝ) + 1)).mp hdiv
    change ρ * ((L : ℝ) + 1) ≤ ε at hmul
    nlinarith only [hmul, hρ]
  let b : ContDiffBump (0 : ℝ) := ⟨ρ / 2, ρ, half_pos hρ, half_lt_self hρ⟩
  let g : ℝ → ℝ := b.normed volume
  have hg : ContDiff ℝ ∞ g := b.contDiff_normed
  have hgc : HasCompactSupport g := b.hasCompactSupport_normed
  have hg0 : ∀ x, 0 ≤ g x := fun x => b.nonneg_normed (μ := volume) x
  have hg1 : (∫ x, g x) = 1 := b.integral_normed (μ := volume)
  have hgs : Function.support g ⊆ Icc (-ρ) ρ := by
    rw [show g = b.normed volume from rfl, b.support_normed_eq]
    intro x hx
    have hx' : |x| < ρ := by simpa [Metric.mem_ball, Real.dist_eq] using hx
    exact abs_le.mp hx'.le
  refine ⟨boxRegularization g 4, contDiff_boxRegularization hg hgc 4,
    hasCompactSupport_boxRegularization hgc 4, ?_, ?_, ?_⟩
  · intro x hx
    by_contra hm
    have hs := support_boxRegularization_subset hρ.le hgs 4 hm
    apply hx
    norm_num only [Nat.cast_ofNat] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · intro x
    refine (abs_boxRegularization_four_sub_cubicSpline_le hg.continuous hgc hg0 hg1
      (ρ := ρ) (L := L) ?_ ?_ x).trans hρε
    · intro y hy
      by_contra hm
      have hs := hgs hm
      exact (not_le_of_gt hy) (abs_le.mpr hs)
    · intro u v
      simpa only [Real.dist_eq] using hL.dist_le_mul u v
  · intro q hq
    simpa only [hg1] using integral_abs_iteratedDeriv_boxRegularization_le hg hgc hg0 4 q hq

private theorem integral_abs_iteratedDeriv_product_le {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {M : ℕ → ℝ} (hM : ∀ q x, |iteratedDeriv q f x| ≤ M q) (q : ℕ) :
    (∫ x, |iteratedDeriv q (fun x => f x * g x) x|) ≤
      leibnizBound M (fun j => ∫ x, |iteratedDeriv j g x|) q := by
  have hi : ∀ j, Integrable (fun x => |iteratedDeriv j g x|) := fun j =>
    ((hg.continuous_iteratedDeriv j (natCast_le_infty j)).integrable_of_hasCompactSupport
      (hasCompactSupport_iteratedDeriv hgc j)).abs
  have hb : ∀ x, |iteratedDeriv q (fun x => f x * g x) x| ≤
      ∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * M j * |iteratedDeriv (q - j) g x| := by
    intro x
    rw [iteratedDeriv_fun_mul (contDiffAt_of_smooth hf q x) (contDiffAt_of_smooth hg q x)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    simp only [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hM j x) (by positivity)) (abs_nonneg _)
  have hsum : Integrable (fun x => ∑ j ∈ Finset.range (q + 1),
      (q.choose j : ℝ) * M j * |iteratedDeriv (q - j) g x|) :=
    integrable_finsetSum _ fun j _ => (hi (q - j)).const_mul _
  calc
    (∫ x, |iteratedDeriv q (fun x => f x * g x) x|) ≤
        ∫ x, ∑ j ∈ Finset.range (q + 1),
          (q.choose j : ℝ) * M j * |iteratedDeriv (q - j) g x| :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hsum
        (Eventually.of_forall hb)
    _ = leibnizBound M (fun j => ∫ x, |iteratedDeriv j g x|) q := by
      rw [integral_finsetSum _ fun j _ => (hi (q - j)).const_mul _]
      exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- Exponential tilting preserves uniform fourth-derivative bounds because all
regularizations lie in one compact interval. -/
theorem exists_splineProbe_regularization_bounds :
    ∃ A : ℕ → ℝ, (∀ q, 0 ≤ A q) ∧ ∀ ε : ℝ, 0 < ε →
      ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
        (∀ x, |G x - splineProbe x| ≤ ε) ∧
        ∀ q : ℕ, q ≤ 4 → (∫ x, |iteratedDeriv q G x|) ≤ A q := by
  let b : ContDiffBump (0 : ℝ) := ⟨5, 6, by norm_num, by norm_num⟩
  let χ : ℝ → ℝ := fun x => Real.exp x * b x
  have hχ : ContDiff ℝ ∞ χ := Real.contDiff_exp.mul b.contDiff
  have hχc : HasCompactSupport χ := b.hasCompactSupport.mul_left
  obtain ⟨M, hM0, hM⟩ := exists_iteratedDeriv_bounds hχ hχc
  have hχB : ∀ x, χ x * cubicSpline x = splineProbe x := by
    intro x
    by_cases hx : |x| ≤ 4
    · have hb : b x = 1 := b.one_of_mem_closedBall (by
        simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hx.trans (by norm_num))
      simp only [χ, hb, mul_one, splineProbe, tiltedSource, one_mul]
    · simp only [χ, cubicSpline_eq_zero (lt_of_not_ge hx), mul_zero, splineProbe,
        tiltedSource]
  refine ⟨leibnizBound M (fun _ => 1),
    fun q => leibnizBound_nonneg hM0 (fun _ => zero_le_one) q, ?_⟩
  intro ε hε
  let δ := ε / (M 0 + 1)
  have hδ : 0 < δ := div_pos hε (by linarith [hM0 0])
  obtain ⟨G, hG, hGc, -, hclose, hGd⟩ := exists_cubicSpline_regularization hδ
  refine ⟨fun x => χ x * G x, hχ.mul hG, hGc.mul_left, ?_, ?_⟩
  · intro x
    have he : M 0 * δ ≤ ε := by
      have heq : δ * (M 0 + 1) = ε := div_mul_cancel₀ ε (by linarith [hM0 0])
      nlinarith only [heq, hδ]
    calc
      |χ x * G x - splineProbe x| = |χ x * (G x - cubicSpline x)| := by
        rw [← hχB x]; congr 1; ring
      _ = |χ x| * |G x - cubicSpline x| := abs_mul _ _
      _ ≤ M 0 * δ := mul_le_mul (by simpa using hM 0 x) (hclose x)
        (abs_nonneg _) (hM0 0)
      _ ≤ ε := he
  · intro q hq
    refine (integral_abs_iteratedDeriv_product_le hχ hG hGc hM q).trans ?_
    unfold leibnizBound
    refine Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_left (hGd (q - j) ((Nat.sub_le q j).trans hq))
      (mul_nonneg (Nat.cast_nonneg _) (hM0 j))

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis

#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.exists_cubicSpline_regularization
#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.exists_splineProbe_regularization_bounds
