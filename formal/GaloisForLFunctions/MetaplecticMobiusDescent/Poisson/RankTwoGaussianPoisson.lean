/-
Rank-two Gaussian Poisson summation adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicScatteringContinuation
import GaloisForLFunctions.MetaplecticMobiusDescent.WeightedCubicWhittakerAverages
import GaloisForLFunctions.MetaplecticMobiusDescent.CompactCubicQuotientPullbacks

/-!
# Rank-two Gaussian Poisson summation

Complex quadratic phases on the Eisenstein lattice (`QuadraticPhase`): successive Poisson
summation in two integer coordinates, principal square-root branches fixed by a positive real
determinant, and the fixed dual average `fixedDualAverage` of the trace Gauss phase, which
depends only on the conductor modulo four.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory

/-! Quadratic trace phases from Gaussian regularization and rank-two Poisson summation. -/

open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
namespace QuadraticPhase

namespace RankTwoPoisson
private theorem gauss_int_summable {a : ℂ} (ha : 0 < a.re) :
    Summable (fun n : ℤ => Complex.exp (-((Real.pi : ℂ) * a) * (n : ℂ) ^ 2)) := by
  have hpa : 0 < ((Real.pi : ℂ) * a).re := by
    simpa using mul_pos Real.pi_pos ha
  exact summable_of_isBigO (Real.summable_abs_int_rpow (show (1 : ℝ) < 2 by norm_num))
    ((isLittleO_exp_neg_mul_sq_cocompact hpa (-2)).isBigO.comp_tendsto
      Int.tendsto_coe_cofinite)

theorem real_gauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) := by
  have htc : 0 < (t : ℂ).re := by simpa using ht
  have h := (gauss_int_summable htc).norm
  simpa [Complex.norm_exp, ← Complex.ofReal_intCast, ← Complex.ofReal_pow, mul_assoc] using h
end RankTwoPoisson

namespace RankTwoComplex

open Real

/-- Positive quadratic decay dominates a product of one-dimensional Gaussian series. -/
theorem lattice_gaussian_summable_of_re_bound (F : ℤ × ℤ → ℂ)
    {eps : ℝ} (heps : 0 < eps)
    (hbound : ∀ z : ℤ × ℤ,
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤ (F z).re) :
    Summable (fun z : ℤ × ℤ => Complex.exp (-(Real.pi : ℂ) * F z)) := by
  have h1 := RankTwoPoisson.real_gauss_summable heps
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * eps * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * eps * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine hmaj.of_norm_bounded ?_
  intro z
  have hb := hbound z
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hm := mul_le_mul_of_nonneg_left hb hpi
  have hexp : (-(Real.pi : ℂ) * F z).re ≤
      -Real.pi * eps * (z.1 : ℝ) ^ 2 +
      -Real.pi * eps * (z.2 : ℝ) ^ 2 := by
    simp [Complex.mul_re] at *
    nlinarith [hm]
  simpa only [Complex.norm_exp, Real.exp_add] using
    (Real.exp_le_exp.mpr hexp)

noncomputable def schur (a b d : ℂ) : ℂ := d - b ^ 2 / a

noncomputable def binaryGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2))

noncomputable def firstGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * (z.1 : ℂ) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * schur a b d * (z.2 : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * (Complex.I * b / a * (z.1 : ℂ)) * (z.2 : ℂ))

noncomputable def dualGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * (z.1 : ℂ) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) / (schur a b d) *
      ((z.2 : ℂ) - b / a * (z.1 : ℂ)) ^ 2)

private theorem binary_split (a b d : ℂ) (m n : ℤ) :
    binaryGaussian a b d (m,n) =
      Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (-(b * (n : ℂ))) * (m : ℂ)) := by
  dsimp [binaryGaussian]
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem first_exponent_identity {a b d : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) +
      (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * (-(b * (n : ℂ)))) ^ 2) =
      (-(Real.pi : ℂ) / a * (k : ℂ) ^ 2) +
        (-(Real.pi : ℂ) * schur a b d * (n : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (Complex.I * b / a * (k : ℂ)) * (n : ℂ)) := by
  dsimp [schur]
  field_simp [ha]
  ring_nf
  simp [Complex.I_sq]

private theorem first_transform_term {a b d : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) *
      Complex.exp (-(Real.pi : ℂ) / a *
        ((k : ℂ) + Complex.I * (-(b * (n : ℂ)))) ^ 2) =
      firstGaussian a b d (k,n) := by
  rw [← Complex.exp_add, first_exponent_identity ha k n, Complex.exp_add]
  rfl

private theorem first_poisson_slice {a b d : ℂ} (ha : 0 < a.re) (n : ℤ) :
    (∑' m : ℤ, binaryGaussian a b d (m,n)) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d (k,n) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2)
  let B : ℂ := -(b * (n : ℂ))
  let F : ℤ → ℂ := fun m => Complex.exp
    (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (m : ℂ))
  let H : ℤ → ℂ := fun k => Complex.exp
    (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' m : ℤ, binaryGaussian a b d (m,n)) = C * ∑' m : ℤ, F m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    exact binary_split a b d m n
  have hpoisson : (∑' m : ℤ, F m) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k :=
    Complex.tsum_exp_neg_quadratic ha B
  calc
    (∑' m : ℤ, binaryGaussian a b d (m,n)) = C * ∑' m : ℤ, F m := hsplit
    _ = C * ((1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k) := by rw [hpoisson]
    _ = (1 / a ^ (1 / 2 : ℂ)) * (C * ∑' k : ℤ, H k) := by ring
    _ = (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d (k,n) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      exact first_transform_term ha0 k n

private theorem second_poisson_slice {a b d : ℂ}
    (hδ : 0 < (schur a b d).re) (k : ℤ) :
    (∑' n : ℤ, firstGaussian a b d (k,n)) =
      (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' l : ℤ, dualGaussian a b d (k,l) := by
  let A : ℂ := schur a b d
  let B : ℂ := Complex.I * b / a * (k : ℂ)
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) / a * (k : ℂ) ^ 2)
  let F : ℤ → ℂ := fun n => Complex.exp
    (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ))
  let H : ℤ → ℂ := fun l => Complex.exp
    (-(Real.pi : ℂ) / A * ((l : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' n : ℤ, firstGaussian a b d (k,n)) = C * ∑' n : ℤ, F n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rfl
  have hpoisson : (∑' n : ℤ, F n) =
      (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l :=
    Complex.tsum_exp_neg_quadratic hδ B
  have hterm (l : ℤ) : C * H l = dualGaussian a b d (k,l) := by
    have hb : Complex.I * B = -(b / a * (k : ℂ)) := by
      dsimp [B]
      field_simp
      ring_nf
      simp [Complex.I_sq]
    dsimp [H, dualGaussian, C, A]
    rw [hb]
    ring_nf
  calc
    (∑' n : ℤ, firstGaussian a b d (k,n)) = C * ∑' n : ℤ, F n := hsplit
    _ = C * ((1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l) := by rw [hpoisson]
    _ = (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) := by ring
    _ = (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' l : ℤ, dualGaussian a b d (k,l) := by
      change (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) =
        (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, dualGaussian a b d (k,l)
      congr 1
      rw [← tsum_mul_left]
      exact tsum_congr hterm

/-- Apply Poisson summation successively in the two integer coordinates. -/
theorem binary_gaussian_poisson {a b d : ℂ}
    (ha : 0 < a.re) (hδ : 0 < (schur a b d).re)
    (hO : Summable (binaryGaussian a b d))
    (hM : Summable (firstGaussian a b d))
    (hD : Summable (dualGaussian a b d)) :
    (∑' z : ℤ × ℤ, binaryGaussian a b d z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, dualGaussian a b d z := by
  have hOcomm :
      (∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d (m,n)) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d (m,n) :=
    (show Summable (Function.uncurry (fun m n : ℤ => binaryGaussian a b d (m,n)))
      from hO).tsum_comm
  have hMcomm :
      (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d (k,n)) =
        ∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d (k,n) :=
    (show Summable (Function.uncurry (fun k n : ℤ => firstGaussian a b d (k,n)))
      from hM).tsum_comm
  calc
    (∑' z : ℤ × ℤ, binaryGaussian a b d z) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d (m,n) := hO.tsum_prod
    _ = ∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d (m,n) := hOcomm.symm
    _ = ∑' n : ℤ, (1 / a ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, firstGaussian a b d (k,n) := by
      apply tsum_congr
      intro n
      exact first_poisson_slice ha n
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d (k,n)) := tsum_mul_left
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d (k,n)) := by
      rw [hMcomm]
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
            ∑' l : ℤ, dualGaussian a b d (k,l)) := by
      congr 1
      apply tsum_congr
      intro k
      exact second_poisson_slice hδ k
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' l : ℤ, dualGaussian a b d (k,l)) := by
      rw [tsum_mul_left]
      ring
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' z : ℤ × ℤ, dualGaussian a b d z := by
      rw [hD.tsum_prod]

end RankTwoComplex

namespace SqrtBranch
open Complex

private theorem arg_ne_pi_of_re_pos {a : ℂ} (ha : 0 < a.re) : a.arg ≠ Real.pi := by
  intro h
  have := (Complex.arg_eq_pi_iff.mp h).1
  linarith

/-- The positive real determinant fixes the compatible principal square-root branches. -/
theorem cpow_half_product {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    a ^ (1 / 2 : ℂ) * (((r : ℂ) / a) ^ (1 / 2 : ℂ)) =
      (r : ℂ) ^ (1 / 2 : ℂ) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have harg := arg_ne_pi_of_re_pos ha
  have hlog : Complex.log ((r : ℂ) / a) = (Real.log r : ℂ) - Complex.log a := by
    rw [div_eq_mul_inv, Complex.log_ofReal_mul hr (inv_ne_zero ha0),
      Complex.log_inv a harg]
    ring
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hdiv : (r : ℂ) / a ≠ 0 := div_ne_zero hr0 ha0
  rw [Complex.cpow_def_of_ne_zero ha0,
    Complex.cpow_def_of_ne_zero hdiv,
    Complex.cpow_def_of_ne_zero hr0, hlog, ← Complex.exp_add]
  congr 1
  rw [Complex.ofReal_log hr.le]
  ring

theorem prefactor_product {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    (1 / a ^ (1 / 2 : ℂ)) * (1 / (((r : ℂ) / a) ^ (1 / 2 : ℂ))) =
      1 / ((r : ℂ) ^ (1 / 2 : ℂ)) := by
  simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using
    congrArg (fun z : ℂ => z⁻¹) (cpow_half_product ha hr)

end SqrtBranch

namespace OscSpecial

private theorem real_quadratic_lower {u v w : ℝ}
    (hu : 0 < u) (hv : 0 < v) (_hdet : 0 < u * v - w ^ 2)
    (x y : ℝ) :
    ((u * v - w ^ 2) / (u + v)) * (x ^ 2 + y ^ 2) ≤
      u * x ^ 2 - 2 * w * x * y + v * y ^ 2 := by
  have hsum : 0 < u + v := add_pos hu hv
  have hid :
      (u + v) * (u * x ^ 2 - 2 * w * x * y + v * y ^ 2) -
        (u * v - w ^ 2) * (x ^ 2 + y ^ 2) =
      (u * x - w * y) ^ 2 + (w * x - v * y) ^ 2 := by ring
  have hsq := add_nonneg (sq_nonneg (u * x - w * y))
    (sq_nonneg (w * x - v * y))
  have hnum : (u * v - w ^ 2) * (x ^ 2 + y ^ 2) ≤
      (u + v) * (u * x ^ 2 - 2 * w * x * y + v * y ^ 2) := by
    linarith
  have h : ((u * v - w ^ 2) * (x ^ 2 + y ^ 2)) / (u + v) ≤
      u * x ^ 2 - 2 * w * x * y + v * y ^ 2 :=
    (div_le_iff₀ hsum).2 (by simpa only [mul_comm] using hnum)
  simpa only [div_mul_eq_mul_div] using h

private theorem schur_eq_real_det_div {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hdet : a * d - b ^ 2 = (R : ℂ)) :
    RankTwoComplex.schur a b d = (R : ℂ) / a := by
  unfold RankTwoComplex.schur
  rw [← hdet]
  field_simp [ha]

private theorem determinant_real_components {a b d : ℂ} {R : ℝ}
    (hdet : a * d - b ^ 2 = (R : ℂ)) :
    a.re * d.re - a.im * d.im - b.re ^ 2 + b.im ^ 2 = R ∧
    a.re * d.im + a.im * d.re - 2 * b.re * b.im = 0 := by
  constructor
  · have h := congrArg Complex.re hdet
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re] at h
    have hb : (b ^ 2).re = b.re ^ 2 - b.im ^ 2 := by
      rw [pow_two, Complex.mul_re]
      ring
    rw [hb] at h
    linarith
  · have h := congrArg Complex.im hdet
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im] at h
    have hb : (b ^ 2).im = 2 * b.re * b.im := by
      rw [pow_two, Complex.mul_im]
      ring
    rw [hb] at h
    linarith

private theorem first_real_coefficients {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hdet : a * d - b ^ 2 = (R : ℂ)) :
    (a⁻¹).re = a.re / Complex.normSq a ∧
    (RankTwoComplex.schur a b d).re = R * a.re / Complex.normSq a ∧
    (Complex.I * b / a).re =
      (b.re * a.im - b.im * a.re) / Complex.normSq a := by
  constructor
  · exact Complex.inv_re a
  constructor
  · rw [schur_eq_real_det_div ha hdet]
    simp [Complex.div_re]
  · rw [Complex.div_re]
    simp [Complex.mul_re, Complex.mul_im]
    ring

private theorem first_real_determinant {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hdet : a * d - b ^ 2 = (R : ℂ)) :
    (a.re / Complex.normSq a) * (R * a.re / Complex.normSq a) -
      ((b.re * a.im - b.im * a.re) / Complex.normSq a) ^ 2 =
      (a.re * d.re - b.re ^ 2) / Complex.normSq a := by
  have hN : Complex.normSq a ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  obtain ⟨hr, hi⟩ := determinant_real_components hdet
  have hid :
      R * a.re ^ 2 - (b.re * a.im - b.im * a.re) ^ 2 =
      (a.re ^ 2 + a.im ^ 2) * (a.re * d.re - b.re ^ 2) -
        a.im * a.re * (a.re * d.im + a.im * d.re - 2 * b.re * b.im) := by
    rw [← hr]
    ring
  rw [hi, mul_zero, sub_zero] at hid
  simp only [Complex.normSq_apply] at hN ⊢
  have hN' : a.re ^ 2 + a.im ^ 2 ≠ 0 := by simpa [pow_two] using hN
  field_simp [hN']
  nlinarith only [hid]

private noncomputable def middleForm (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  a⁻¹ * (z.1 : ℂ) ^ 2 -
    2 * (Complex.I * b / a) * (z.1 : ℂ) * (z.2 : ℂ) +
    RankTwoComplex.schur a b d * (z.2 : ℂ) ^ 2

private theorem middleForm_real (a b d : ℂ) (z : ℤ × ℤ) :
    (middleForm a b d z).re =
      (a⁻¹).re * (z.1 : ℝ) ^ 2 -
      2 * (Complex.I * b / a).re * (z.1 : ℝ) * (z.2 : ℝ) +
      (RankTwoComplex.schur a b d).re * (z.2 : ℝ) ^ 2 := by
  simp [middleForm, Complex.add_re, Complex.sub_re, Complex.mul_re, pow_two]

private theorem middleForm_exp (a b d : ℂ) (z : ℤ × ℤ) :
    RankTwoComplex.firstGaussian a b d z =
      Complex.exp (-(Real.pi : ℂ) * middleForm a b d z) := by
  simp only [RankTwoComplex.firstGaussian, middleForm]
  rw [← Complex.exp_add]
  congr 1
  simp [div_eq_mul_inv]
  ring

private theorem firstGaussian_summable {a b d : ℂ} {R : ℝ}
    (ha : 0 < a.re) (hR : 0 < R)
    (hdet : a * d - b ^ 2 = (R : ℂ))
    (hpd : 0 < a.re * d.re - b.re ^ 2) :
    Summable (RankTwoComplex.firstGaussian a b d) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hN : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha0
  let u : ℝ := a.re / Complex.normSq a
  let v : ℝ := R * a.re / Complex.normSq a
  let w : ℝ := (b.re * a.im - b.im * a.re) / Complex.normSq a
  have hu : 0 < u := div_pos ha hN
  have hv : 0 < v := div_pos (mul_pos hR ha) hN
  have hq : 0 < u * v - w ^ 2 := by
    dsimp [u, v, w]
    rw [first_real_determinant ha0 hdet]
    exact div_pos hpd hN
  let eps : ℝ := (u * v - w ^ 2) / (u + v)
  have heps : 0 < eps := div_pos hq (add_pos hu hv)
  have hcoeff := first_real_coefficients ha0 hdet
  have hbound (z : ℤ × ℤ) :
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤
      (middleForm a b d z).re := by
    rw [middleForm_real, hcoeff.1, hcoeff.2.1, hcoeff.2.2]
    exact real_quadratic_lower hu hv hq (z.1 : ℝ) (z.2 : ℝ)
  exact (RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (middleForm a b d) heps hbound).congr (fun z => (middleForm_exp a b d z).symm)

private noncomputable def originalForm (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2

private theorem originalForm_real (a b d : ℂ) (z : ℤ × ℤ) :
    (originalForm a b d z).re =
      a.re * (z.1 : ℝ) ^ 2 + 2 * b.re * (z.1 : ℝ) * (z.2 : ℝ) +
      d.re * (z.2 : ℝ) ^ 2 := by
  simp [originalForm, Complex.add_re, Complex.mul_re, pow_two]

private theorem originalGaussian_summable {a b d : ℂ}
    (ha : 0 < a.re) (hpd : 0 < a.re * d.re - b.re ^ 2) :
    Summable (RankTwoComplex.binaryGaussian a b d) := by
  have hd : 0 < d.re := by
    by_contra h
    have h' : d.re ≤ 0 := le_of_not_gt h
    have hm := mul_nonpos_of_nonneg_of_nonpos ha.le h'
    nlinarith [sq_nonneg b.re]
  let eps : ℝ := (a.re * d.re - b.re ^ 2) / (a.re + d.re)
  have heps : 0 < eps := div_pos hpd (add_pos ha hd)
  have hbound (z : ℤ × ℤ) :
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤
      (originalForm a b d z).re := by
    rw [originalForm_real]
    dsimp [eps]
    convert real_quadratic_lower (w := -b.re) ha hd (by simpa using hpd)
      (z.1 : ℝ) (z.2 : ℝ) using 1 <;> ring
  exact (RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (originalForm a b d) heps hbound).congr (fun z => by rfl)

noncomputable def inverseForm (a b d : ℂ) (R : ℝ) (z : ℤ × ℤ) : ℂ :=
  (d * (z.1 : ℂ) ^ 2 - 2 * b * (z.1 : ℂ) * (z.2 : ℂ) +
    a * (z.2 : ℂ) ^ 2) / (R : ℂ)

private theorem inverseForm_real (a b d : ℂ) {R : ℝ} (hR : R ≠ 0) (z : ℤ × ℤ) :
    (inverseForm a b d R z).re =
      (d.re * (z.1 : ℝ) ^ 2 - 2 * b.re * (z.1 : ℝ) * (z.2 : ℝ) +
        a.re * (z.2 : ℝ) ^ 2) / R := by
  simp [inverseForm, Complex.div_re, Complex.add_re, Complex.sub_re,
    Complex.mul_re, Complex.normSq_apply, pow_two]
  field_simp [hR]

theorem dualGaussian_inverseForm {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hR : R ≠ 0)
    (hdet : a * d - b ^ 2 = (R : ℂ)) (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian a b d z =
      Complex.exp (-(Real.pi : ℂ) * inverseForm a b d R z) := by
  unfold RankTwoComplex.dualGaussian
  rw [← Complex.exp_add]
  congr 1
  rw [schur_eq_real_det_div ha hdet]
  dsimp [inverseForm]
  have hdet0 : a * d - b ^ 2 ≠ 0 := by rw [hdet]; exact_mod_cast hR
  rw [← hdet]
  field_simp [ha, hdet0] ; ring

private theorem dualGaussian_summable {a b d : ℂ} {R : ℝ}
    (ha : 0 < a.re) (hR : 0 < R)
    (hdet : a * d - b ^ 2 = (R : ℂ))
    (hpd : 0 < a.re * d.re - b.re ^ 2) :
    Summable (RankTwoComplex.dualGaussian a b d) := by
  have hd : 0 < d.re := by
    by_contra h
    have h' : d.re ≤ 0 := le_of_not_gt h
    have hm := mul_nonpos_of_nonneg_of_nonpos ha.le h'
    nlinarith [sq_nonneg b.re]
  let eps : ℝ := ((d.re * a.re - b.re ^ 2) / (d.re + a.re)) / R
  have heps : 0 < eps := div_pos (div_pos (by nlinarith [hpd]) (add_pos hd ha)) hR
  have hbound (z : ℤ × ℤ) :
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤
      (inverseForm a b d R z).re := by
    rw [inverseForm_real a b d hR.ne']
    have hbase := real_quadratic_lower (u := d.re) (v := a.re) (w := b.re)
      hd ha (by nlinarith [hpd]) (z.1 : ℝ) (z.2 : ℝ)
    have hdivide := div_le_div_of_nonneg_right hbase hR.le
    simpa [eps, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdivide
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  exact (RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (inverseForm a b d R) heps hbound).congr
      (fun z => (dualGaussian_inverseForm ha0 hR.ne' hdet z).symm)

/-- A positive real determinant and positive definite real part give the complete transform. -/
theorem binary_gaussian_poisson_real_det {a b d : ℂ} {R : ℝ}
    (ha : 0 < a.re) (hR : 0 < R)
    (hdet : a * d - b ^ 2 = (R : ℂ))
    (hpd : 0 < a.re * d.re - b.re ^ 2) :
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian a b d z) =
      (1 / ((R : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' z : ℤ × ℤ, RankTwoComplex.dualGaussian a b d z := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hN : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha0
  have hδ : 0 < (RankTwoComplex.schur a b d).re := by
    rw [schur_eq_real_det_div ha0 hdet]
    simpa [Complex.div_re] using div_pos (mul_pos hR ha) hN
  have hO := originalGaussian_summable ha hpd
  have hM := firstGaussian_summable ha hR hdet hpd
  have hD := dualGaussian_summable ha hR hdet hpd
  calc
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian a b d z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (RankTwoComplex.schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, RankTwoComplex.dualGaussian a b d z :=
      RankTwoComplex.binary_gaussian_poisson ha hδ hO hM hD
    _ = (1 / ((R : ℂ) ^ (1 / 2 : ℂ))) *
          ∑' z : ℤ × ℤ, RankTwoComplex.dualGaussian a b d z := by
      rw [schur_eq_real_det_div ha0 hdet,
        SqrtBranch.prefactor_product ha hR]

noncomputable def q (a b : ℝ) : ℝ := a ^ 2 - a * b + b ^ 2
noncomputable def A (η a b : ℝ) : ℂ :=
  (η : ℂ) + 2 * Complex.I * (b : ℂ) / (q a b : ℂ)
noncomputable def B (η a b : ℝ) : ℂ :=
  -(η : ℂ) / 2 - 2 * Complex.I * (a : ℂ) / (q a b : ℂ)
noncomputable def D (η a b : ℝ) : ℂ :=
  (η : ℂ) + 2 * Complex.I * ((a-b : ℝ) : ℂ) / (q a b : ℂ)
noncomputable def R (η a b : ℝ) : ℝ := 4 / q a b + 3 * η ^ 2 / 4

theorem coefficient_re (η a b : ℝ) (_hq : q a b ≠ 0) :
    (A η a b).re = η ∧ (B η a b).re = -η / 2 ∧ (D η a b).re = η := by
  simp [A, B, D, Complex.div_re, Complex.normSq_apply]

theorem oscillatory_determinant (η a b : ℝ) (hq : q a b ≠ 0) :
    A η a b * D η a b - (B η a b) ^ 2 = (R η a b : ℂ) := by
  have hqc : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq
  have hqexpr : (q a b : ℂ) = (a : ℂ) ^ 2 - (a : ℂ) * (b : ℂ) + (b : ℂ) ^ 2 := by
    simp [q]
  have hRcast : (R η a b : ℂ) = 4 / (q a b : ℂ) + 3 * (η : ℂ) ^ 2 / 4 := by
    simp [R]
  rw [hRcast]
  dsimp [A, B, D]
  field_simp [hqc]
  rw [hqexpr]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem real_positive_definite {η a b : ℝ} (hη : 0 < η) (hq : q a b ≠ 0) :
    0 < (A η a b).re * (D η a b).re - (B η a b).re ^ 2 := by
  obtain ⟨hA, hB, hD⟩ := coefficient_re η a b hq
  rw [hA, hB, hD]
  nlinarith [sq_pos_of_pos hη]


/-- The damped quadratic trace form has an exact, absolutely convergent Poisson transform. -/
theorem oscillatory_gaussian_poisson {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) :
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian (A η a b) (B η a b) (D η a b) z) =
      (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' z : ℤ × ℤ,
          RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have ha : 0 < (A η a b).re := by
    rw [(coefficient_re η a b hq0).1]
    exact hη
  have hR : 0 < R η a b := by
    unfold R
    positivity
  exact binary_gaussian_poisson_real_det ha hR
    (oscillatory_determinant η a b hq0)
    (real_positive_definite hη hq0)

noncomputable def r (η a b : ℝ) : ℝ := 1 + 3 * q a b * η ^ 2 / 16

theorem r_pos {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    0 < r η a b := by
  unfold r
  positivity

private theorem inverseForm_explicit {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    inverseForm (A η a b) (B η a b) (D η a b) (R η a b) z =
      ((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ))) *
        ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) +
      Complex.I / (2 * (r η a b : ℂ)) *
        (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
          2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
          (b : ℂ) * (z.2 : ℂ) ^ 2) := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have hqc : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hr0 : r η a b ≠ 0 := (r_pos hη hq).ne'
  have hrc : (r η a b : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hR : 0 < R η a b := by unfold R; positivity
  have hRexpr : (R η a b : ℂ) = 4 * (r η a b : ℂ) / (q a b : ℂ) := by
    simp [R, r]
    field_simp [hqc]
    ring
  have hqexpr : (q a b : ℂ) = (a : ℂ) ^ 2 - (a : ℂ) * (b : ℂ) + (b : ℂ) ^ 2 := by
    simp [q]
  have hrexpr : (r η a b : ℂ) = 1 + 3 * (q a b : ℂ) * (η : ℂ) ^ 2 / 16 := by
    simp [r]
  dsimp [inverseForm, A, B, D]
  rw [hRexpr]
  field_simp [hqc, hrc]
  push_cast
  ring

/-- The inverse form separates a positive Gaussian scale from its quadratic phase. -/
theorem dualGaussian_explicit {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z =
      Complex.exp (-(Real.pi : ℂ) *
        (((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ))) *
          ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) +
         Complex.I / (2 * (r η a b : ℂ)) *
          (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
            2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
            (b : ℂ) * (z.2 : ℂ) ^ 2))) := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have hA0 : A η a b ≠ 0 := by
    intro h
    have hAr : (A η a b).re = η := (coefficient_re η a b hq0).1
    simp [h] at hAr
    linarith
  have hR : 0 < R η a b := by unfold R; positivity
  rw [dualGaussian_inverseForm hA0 hR.ne'
    (oscillatory_determinant η a b hq0) z,
    inverseForm_explicit hη hq z]

end OscSpecial
end QuadraticPhase

open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory

namespace QuadraticPhase

namespace RankTwoPoisson
noncomputable def cg (a : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (-((Real.pi : ℂ) * a) * (n : ℂ) ^ 2)

noncomputable def eisQ (z : ℤ × ℤ) : ℝ :=
  (z.1 : ℝ) ^ 2 - (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2

noncomputable def eisGauss (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp ((-Real.pi * t * eisQ z : ℝ) : ℂ)

theorem eisQ_lower (z : ℤ × ℤ) :
    ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / 2 ≤ eisQ z := by
  dsimp [eisQ]
  nlinarith [sq_nonneg ((z.1 : ℝ) - (z.2 : ℝ))]

theorem eis_gauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (eisGauss t) := by
  have ht2 : 0 < t / 2 := by positivity
  have h1 := real_gauss_summable ht2
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * (t / 2) * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (t / 2) * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine hmaj.of_norm_bounded ?_
  intro z
  have hq := eisQ_lower z
  have hpi : 0 ≤ Real.pi * t := (mul_pos Real.pi_pos ht).le
  have hmul := mul_le_mul_of_nonneg_left hq hpi
  have hexp : -Real.pi * t * eisQ z ≤
      -Real.pi * (t / 2) * (z.1 : ℝ) ^ 2 +
      -Real.pi * (t / 2) * (z.2 : ℝ) ^ 2 := by
    nlinarith [hmul]
  simpa [eisGauss, Complex.norm_exp, Real.exp_add] using
    (Real.exp_le_exp.mpr hexp)


end RankTwoPoisson

namespace RankTwoAffine

open RankTwoComplex

noncomputable def binaryGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2) +
    2 * (Real.pi : ℂ) * (u * (z.1 : ℂ) + v * (z.2 : ℂ)))

noncomputable def firstGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * ((z.1 : ℂ) + Complex.I * u) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * schur a b d * (z.2 : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) *
        (v + Complex.I * b / a * ((z.1 : ℂ) + Complex.I * u)) * (z.2 : ℂ))

noncomputable def dualGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * ((z.1 : ℂ) + Complex.I * u) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) / (schur a b d) *
      ((z.2 : ℂ) + Complex.I *
        (v + Complex.I * b / a * ((z.1 : ℂ) + Complex.I * u))) ^ 2)

private theorem binary_split (a b d u v : ℂ) (m n : ℤ) :
    binaryGaussian a b d u v (m,n) =
      Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * v * (n : ℂ)) *
        Complex.exp (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (u - b * (n : ℂ)) * (m : ℂ)) := by
  dsimp [binaryGaussian]
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem first_exponent_identity {a b d u v : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * v * (n : ℂ)) +
      (-(Real.pi : ℂ) / a *
        ((k : ℂ) + Complex.I * (u - b * (n : ℂ))) ^ 2) =
      (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * u) ^ 2) +
        (-(Real.pi : ℂ) * schur a b d * (n : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) *
            (v + Complex.I * b / a * ((k : ℂ) + Complex.I * u)) * (n : ℂ)) := by
  dsimp [schur]
  field_simp [ha]
  ring_nf
  simp [Complex.I_sq]

private theorem first_transform_term {a b d u v : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * v * (n : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) / a *
        ((k : ℂ) + Complex.I * (u - b * (n : ℂ))) ^ 2) =
      firstGaussian a b d u v (k,n) := by
  rw [← Complex.exp_add, first_exponent_identity ha k n, Complex.exp_add]
  rfl

private theorem first_poisson_slice {a b d u v : ℂ} (ha : 0 < a.re) (n : ℤ) :
    (∑' m : ℤ, binaryGaussian a b d u v (m,n)) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d u v (k,n) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
    2 * (Real.pi : ℂ) * v * (n : ℂ))
  let B : ℂ := u - b * (n : ℂ)
  let F : ℤ → ℂ := fun m => Complex.exp
    (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (m : ℂ))
  let H : ℤ → ℂ := fun k => Complex.exp
    (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' m : ℤ, binaryGaussian a b d u v (m,n)) = C * ∑' m : ℤ, F m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    exact binary_split a b d u v m n
  have hpoisson : (∑' m : ℤ, F m) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k :=
    Complex.tsum_exp_neg_quadratic ha B
  calc
    (∑' m : ℤ, binaryGaussian a b d u v (m,n)) = C * ∑' m : ℤ, F m := hsplit
    _ = C * ((1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k) := by rw [hpoisson]
    _ = (1 / a ^ (1 / 2 : ℂ)) * (C * ∑' k : ℤ, H k) := by ring
    _ = (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d u v (k,n) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      exact first_transform_term ha0 k n

private theorem second_poisson_slice {a b d u v : ℂ}
    (hδ : 0 < (schur a b d).re) (k : ℤ) :
    (∑' n : ℤ, firstGaussian a b d u v (k,n)) =
      (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' l : ℤ, dualGaussian a b d u v (k,l) := by
  let A : ℂ := schur a b d
  let B : ℂ := v + Complex.I * b / a * ((k : ℂ) + Complex.I * u)
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * u) ^ 2)
  let F : ℤ → ℂ := fun n => Complex.exp
    (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ))
  let H : ℤ → ℂ := fun l => Complex.exp
    (-(Real.pi : ℂ) / A * ((l : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' n : ℤ, firstGaussian a b d u v (k,n)) = C * ∑' n : ℤ, F n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rfl
  have hpoisson : (∑' n : ℤ, F n) =
      (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l :=
    Complex.tsum_exp_neg_quadratic hδ B
  calc
    (∑' n : ℤ, firstGaussian a b d u v (k,n)) = C * ∑' n : ℤ, F n := hsplit
    _ = C * ((1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l) := by rw [hpoisson]
    _ = (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) := by ring
    _ = (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' l : ℤ, dualGaussian a b d u v (k,l) := by
      change (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) =
        (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, dualGaussian a b d u v (k,l)
      congr 1
      rw [← tsum_mul_left]
      rfl

/-- Successive one-dimensional transforms include the affine linear terms. -/
theorem affine_gaussian_poisson {a b d u v : ℂ}
    (ha : 0 < a.re) (hδ : 0 < (schur a b d).re)
    (hO : Summable (binaryGaussian a b d u v))
    (hM : Summable (firstGaussian a b d u v))
    (hD : Summable (dualGaussian a b d u v)) :
    (∑' z : ℤ × ℤ, binaryGaussian a b d u v z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, dualGaussian a b d u v z := by
  have hOcomm :
      (∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d u v (m,n)) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d u v (m,n) :=
    (show Summable (Function.uncurry (fun m n : ℤ => binaryGaussian a b d u v (m,n)))
      from hO).tsum_comm
  have hMcomm :
      (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d u v (k,n)) =
        ∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d u v (k,n) :=
    (show Summable (Function.uncurry (fun k n : ℤ => firstGaussian a b d u v (k,n)))
      from hM).tsum_comm
  calc
    (∑' z : ℤ × ℤ, binaryGaussian a b d u v z) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d u v (m,n) := hO.tsum_prod
    _ = ∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d u v (m,n) := hOcomm.symm
    _ = ∑' n : ℤ, (1 / a ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, firstGaussian a b d u v (k,n) := by
      apply tsum_congr
      intro n
      exact first_poisson_slice ha n
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d u v (k,n)) := tsum_mul_left
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d u v (k,n)) := by
      rw [hMcomm]
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
            ∑' l : ℤ, dualGaussian a b d u v (k,l)) := by
      congr 1
      apply tsum_congr
      intro k
      exact second_poisson_slice hδ k
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' l : ℤ, dualGaussian a b d u v (k,l)) := by
      rw [tsum_mul_left]
      ring
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' z : ℤ × ℤ, dualGaussian a b d u v z := by
      rw [hD.tsum_prod]

end RankTwoAffine

namespace RankTwoEisShift

noncomputable def Q (x y : ℝ) : ℝ := x ^ 2 - x * y + y ^ 2

noncomputable def shifted (t x y : ℝ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (((-Real.pi * t * Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) : ℝ) : ℂ))

noncomputable def A (t : ℝ) : ℂ := (t : ℂ)
noncomputable def B (t : ℝ) : ℂ := ((-t / 2 : ℝ) : ℂ)
noncomputable def D (t : ℝ) : ℂ := (t : ℂ)
noncomputable def U (t x y : ℝ) : ℂ := ((-t * (x - y / 2) : ℝ) : ℂ)
noncomputable def V (t x y : ℝ) : ℂ := ((-t * (y - x / 2) : ℝ) : ℂ)
noncomputable def C (t x y : ℝ) : ℂ :=
  Complex.exp (((-Real.pi * t * Q x y : ℝ) : ℂ))

private theorem shifted_eq_affine (t x y : ℝ) (m n : ℤ) :
    shifted t x y (m,n) =
      C t x y * RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) (m,n) := by
  dsimp [shifted, C, Q, RankTwoAffine.binaryGaussian, A, B, D, U, V]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem schur_eis {t : ℝ} (ht : 0 < t) :
    RankTwoComplex.schur (A t) (B t) (D t) = (((3 * t) / 4 : ℝ) : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  dsimp [RankTwoComplex.schur, A, B, D]
  push_cast
  field_simp [ht0]
  ring

private theorem schur_eis_pos {t : ℝ} (ht : 0 < t) :
    0 < (RankTwoComplex.schur (A t) (B t) (D t)).re := by
  rw [schur_eis ht]
  have h : 0 < 3 * t / 4 := by positivity
  simpa using h

noncomputable def dualPhase (k l : ℤ) (x y : ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi * ((k : ℝ) * x + (l : ℝ) * y) : ℝ) : ℂ)) * Complex.I)

private theorem shifted_dual_term {t : ℝ} (ht : 0 < t) (x y : ℝ) (k l : ℤ) :
    C t x y *
      RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) (k,l) =
      RankTwoPoisson.eisGauss (4 / (3 * t)) (k,-l) * dualPhase k l x y := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  dsimp [C, Q, RankTwoAffine.dualGaussian, RankTwoPoisson.eisGauss,
    RankTwoPoisson.eisQ, dualPhase, A, B, D, U, V]
  rw [show RankTwoComplex.schur (t : ℂ) ((-t / 2 : ℝ) : ℂ) (t : ℂ) =
      (((3 * t) / 4 : ℝ) : ℂ) from schur_eis ht]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ht0]
  ring_nf
  norm_num [Complex.I_pow_eq_pow_mod, Complex.I_sq]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

private theorem shifted_real_gauss_summable {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * ((n : ℝ) + y) ^ 2)) := by
  have ht2 : 0 < t / 2 := by positivity
  have hbase := RankTwoPoisson.real_gauss_summable ht2
  have hmaj : Summable (fun n : ℤ =>
      Real.exp (Real.pi * t * y ^ 2) *
        Real.exp (-Real.pi * (t / 2) * (n : ℝ) ^ 2)) :=
    hbase.mul_left _
  refine hmaj.of_norm_bounded ?_
  intro n
  have hs : (n : ℝ) ^ 2 / 2 - y ^ 2 ≤ ((n : ℝ) + y) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) + 2 * y)]
  have hm := mul_le_mul_of_nonneg_left hs (mul_pos Real.pi_pos ht).le
  have he : -Real.pi * t * ((n : ℝ) + y) ^ 2 ≤
      Real.pi * t * y ^ 2 + -Real.pi * (t / 2) * (n : ℝ) ^ 2 := by
    nlinarith [hm]
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_add] using
    (Real.exp_le_exp.mpr he)

noncomputable def middlePhase (k n : ℤ) (x y : ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi * (k : ℝ) * (x - ((n : ℝ) + y) / 2) : ℝ) : ℂ)) * Complex.I)

private theorem middlePhase_norm (k n : ℤ) (x y : ℝ) :
    ‖middlePhase k n x y‖ = 1 := by
  simp [middlePhase, Complex.norm_exp, Complex.mul_re]

private theorem shifted_middle_term {t : ℝ} (ht : 0 < t) (x y : ℝ) (k n : ℤ) :
    C t x y *
      RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y) (k,n) =
      RankTwoPoisson.cg ((t⁻¹ : ℝ) : ℂ) k *
        Complex.exp (((-Real.pi * (3 * t / 4) * ((n : ℝ) + y) ^ 2 : ℝ) : ℂ)) *
        middlePhase k n x y := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  dsimp [C, Q, RankTwoAffine.firstGaussian, RankTwoPoisson.cg,
    middlePhase, A, B, D, U, V]
  rw [show RankTwoComplex.schur (t : ℂ) ((-t / 2 : ℝ) : ℂ) (t : ℂ) =
      (((3 * t) / 4 : ℝ) : ℂ) from schur_eis ht]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ht0]
  ring_nf
  norm_num [Complex.I_pow_eq_pow_mod, Complex.I_sq]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem middle_norm {t : ℝ} (ht : 0 < t) (x y : ℝ) (k n : ℤ) :
    ‖C t x y *
      RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y) (k,n)‖ =
      Real.exp (-Real.pi * t⁻¹ * (k : ℝ) ^ 2) *
      Real.exp (-Real.pi * (3 * t / 4) * ((n : ℝ) + y) ^ 2) := by
  rw [shifted_middle_term ht]
  simp [ middlePhase_norm, RankTwoPoisson.cg, Complex.norm_exp,
    ← Complex.ofReal_intCast, ← Complex.ofReal_pow, mul_assoc]

private theorem affine_middle_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y)) := by
  have htinv : 0 < t⁻¹ := inv_pos.mpr ht
  have ht3 : 0 < 3 * t / 4 := by positivity
  have h1 := RankTwoPoisson.real_gauss_summable htinv
  have h2 := shifted_real_gauss_summable ht3 y
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * t⁻¹ * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (3 * t / 4) * ((z.2 : ℝ) + y) ^ 2)) :=
    h1.mul_of_nonneg h2 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hCmid : Summable (fun z : ℤ × ℤ =>
      C t x y * RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
    refine hmaj.of_norm_bounded ?_
    intro z
    rw [middle_norm ht]
  have hC : C t x y ≠ 0 := Complex.exp_ne_zero _
  have h := hCmid.mul_left (C t x y)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hC, one_mul] using h

theorem dualPhase_norm (k l : ℤ) (x y : ℝ) :
    ‖dualPhase k l x y‖ = 1 := by
  simp [dualPhase, Complex.norm_exp, Complex.mul_re]

private theorem affine_dual_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y)) := by
  have htd : 0 < 4 / (3 * t) := by positivity
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss (4 / (3 * t)) (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable htd)
  have hCdual : Summable (fun z : ℤ × ℤ =>
      C t x y * RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
    refine hE.norm.of_norm_bounded ?_
    intro z
    rw [shifted_dual_term ht]
    simp [ dualPhase_norm]
  have hC : C t x y ≠ 0 := Complex.exp_ne_zero _
  have h := hCdual.mul_left (C t x y)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hC, one_mul] using h

private theorem shifted_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (shifted t x y) := by
  have ht4 : 0 < t / 4 := by positivity
  have h1 := RankTwoPoisson.real_gauss_summable ht4
  have hbase : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * (t / 4) * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (t / 4) * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (Real.pi * t * (x ^ 2 + y ^ 2) / 2) *
        (Real.exp (-Real.pi * (t / 4) * (z.1 : ℝ) ^ 2) *
         Real.exp (-Real.pi * (t / 4) * (z.2 : ℝ) ^ 2))) :=
    hbase.mul_left _
  refine hmaj.of_norm_bounded ?_
  intro z
  have hq : (((z.1 : ℝ) + x) ^ 2 + ((z.2 : ℝ) + y) ^ 2) / 2 ≤
      Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) := by
    dsimp [Q]
    nlinarith [sq_nonneg (((z.1 : ℝ) + x) - ((z.2 : ℝ) + y))]
  have hm : (z.1 : ℝ) ^ 2 / 2 - x ^ 2 ≤ ((z.1 : ℝ) + x) ^ 2 := by
    nlinarith [sq_nonneg ((z.1 : ℝ) + 2 * x)]
  have hn : (z.2 : ℝ) ^ 2 / 2 - y ^ 2 ≤ ((z.2 : ℝ) + y) ^ 2 := by
    nlinarith [sq_nonneg ((z.2 : ℝ) + 2 * y)]
  have hl : ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / 4 -
      (x ^ 2 + y ^ 2) / 2 ≤ Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) := by
    nlinarith [hq, hm, hn]
  have hpt : 0 ≤ Real.pi * t := (mul_pos Real.pi_pos ht).le
  have hmul := mul_le_mul_of_nonneg_left hl hpt
  have he : -Real.pi * t * Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) ≤
      Real.pi * t * (x ^ 2 + y ^ 2) / 2 +
        (-Real.pi * (t / 4) * (z.1 : ℝ) ^ 2 +
         -Real.pi * (t / 4) * (z.2 : ℝ) ^ 2) := by
    nlinarith [hmul]
  simpa [shifted, Complex.norm_exp, Real.exp_add, mul_assoc] using
    (Real.exp_le_exp.mpr he)

private theorem affine_original_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y)) := by
  have hS := shifted_summable ht x y
  have hC : C t x y ≠ 0 := Complex.exp_ne_zero _
  have hCA : Summable (fun z : ℤ × ℤ =>
      C t x y * RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) :=
    hS.congr (fun z => shifted_eq_affine t x y z.1 z.2)
  have h := hCA.mul_left (C t x y)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hC, one_mul] using h

/-- Poisson summation for an arbitrary real shift of the Eisenstein norm form. -/
theorem shifted_eisenstein_gaussian_poisson {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    (∑' z : ℤ × ℤ, shifted t x y z) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
        (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisGauss (4 / (3 * t)) (z.1,-z.2) *
            dualPhase z.1 z.2 x y := by
  have ha : 0 < (A t).re := by simpa [A] using ht
  have hδ := schur_eis_pos ht
  have hO := affine_original_summable ht x y
  have hM := affine_middle_summable ht x y
  have hD := affine_dual_summable ht x y
  let pref : ℂ :=
    (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
      (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ))
  have haff :
      (∑' z : ℤ × ℤ,
        RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) =
      pref * (∑' z : ℤ × ℤ,
        RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
    have h := RankTwoAffine.affine_gaussian_poisson ha hδ hO hM hD
    rw [schur_eis ht] at h
    exact h
  calc
    (∑' z : ℤ × ℤ, shifted t x y z) =
        C t x y * (∑' z : ℤ × ℤ,
          RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      exact shifted_eq_affine t x y z.1 z.2
    _ = C t x y * (pref * (∑' z : ℤ × ℤ,
          RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) z)) := by
      rw [haff]
    _ = pref * (∑' z : ℤ × ℤ,
          C t x y * RankTwoAffine.dualGaussian (A t) (B t) (D t)
            (U t x y) (V t x y) z) := by
      rw [tsum_mul_left]
      ring
    _ = pref * (∑' z : ℤ × ℤ,
          RankTwoPoisson.eisGauss (4 / (3 * t)) (z.1,-z.2) *
            dualPhase z.1 z.2 x y) := by
      congr 1
      apply tsum_congr
      intro z
      exact shifted_dual_term ht x y z.1 z.2

end RankTwoEisShift

namespace RankTwoLimit

section

open scoped Topology

open RankTwoPoisson RankTwoEisShift Filter

private theorem eisQ_nonneg (z : ℤ × ℤ) : 0 ≤ RankTwoPoisson.eisQ z := by
  have h := RankTwoPoisson.eisQ_lower z
  nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]

private theorem eisQ_pos {z : ℤ × ℤ} (hz : z ≠ (0,0)) :
    0 < RankTwoPoisson.eisQ z := by
  by_cases hm : z.1 = 0
  · have hn : z.2 ≠ 0 := by
      intro h0
      exact hz (Prod.ext hm h0)
    have hnR : (z.2 : ℝ) ≠ 0 := by exact_mod_cast hn
    have h := RankTwoPoisson.eisQ_lower z
    nlinarith [sq_pos_of_ne_zero hnR]
  · have hmR : (z.1 : ℝ) ≠ 0 := by exact_mod_cast hm
    have h := RankTwoPoisson.eisQ_lower z
    nlinarith [sq_pos_of_ne_zero hmR, sq_nonneg (z.2 : ℝ)]

private theorem eisGauss_norm (T : ℝ) (z : ℤ × ℤ) :
    ‖RankTwoPoisson.eisGauss T z‖ =
      Real.exp (-Real.pi * T * RankTwoPoisson.eisQ z) := by
  simp [RankTwoPoisson.eisGauss, Complex.norm_exp]

noncomputable def dualTerm (T : ℝ) (x y : ℝ) (z : ℤ × ℤ) : ℂ :=
  RankTwoPoisson.eisGauss T (z.1,-z.2) * RankTwoEisShift.dualPhase z.1 z.2 x y

noncomputable def limitTerm (z : ℤ × ℤ) : ℂ :=
  if z = (0,0) then 1 else 0

private theorem dualTerm_tendsto (x y : ℝ) (z : ℤ × ℤ) :
    Tendsto (fun T : ℝ => dualTerm T x y z) atTop (𝓝 (limitTerm z)) := by
  by_cases hz : z = (0,0)
  · subst z
    simp [dualTerm, limitTerm, RankTwoPoisson.eisGauss,
      RankTwoPoisson.eisQ, RankTwoEisShift.dualPhase]
  · have hz' : (z.1,-z.2) ≠ ((0,0) : ℤ × ℤ) := by
      intro h
      apply hz
      have h1 : z.1 = 0 := by simpa using congrArg Prod.fst h
      have h2 : z.2 = 0 := by simpa using congrArg Prod.snd h
      exact Prod.ext h1 h2
    have hq := eisQ_pos hz'
    have hneg : -Real.pi * RankTwoPoisson.eisQ (z.1,-z.2) < 0 := by
      nlinarith [mul_pos Real.pi_pos hq]
    have harg : Tendsto
        (fun T : ℝ => -Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2))
        atTop atBot := by
      convert tendsto_id.const_mul_atTop_of_neg hneg using 1
      ext T
      simp [mul_assoc, mul_comm]
    have hexp : Tendsto
        (fun T : ℝ => Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp harg
    have hc : Tendsto (fun T : ℝ => RankTwoPoisson.eisGauss T (z.1,-z.2))
        atTop (𝓝 (0 : ℂ)) := by
      have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp hexp
      have heq : (fun T : ℝ =>
          ((Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)) : ℝ) : ℂ)) =
          (fun T : ℝ => RankTwoPoisson.eisGauss T (z.1,-z.2)) := by
        funext T
        simp [RankTwoPoisson.eisGauss, Complex.ofReal_exp]
      change Tendsto (fun T : ℝ =>
        ((Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)) : ℝ) : ℂ))
        atTop (𝓝 (0 : ℂ)) at hh
      rw [heq] at hh
      exact hh
    simpa [dualTerm, limitTerm, hz] using
      hc.mul_const (RankTwoEisShift.dualPhase z.1 z.2 x y)

/-- A fixed Gaussian majorant permits passage to the zero-frequency limit. -/
theorem dual_sum_tendsto_one (x y : ℝ) :
    Tendsto (fun T : ℝ => ∑' z : ℤ × ℤ, dualTerm T x y z)
      atTop (𝓝 (1 : ℂ)) := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss 1 (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable (by norm_num))
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ z : ℤ × ℤ,
      ‖dualTerm T x y z‖ ≤ ‖RankTwoPoisson.eisGauss 1 (z.1,-z.2)‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT z
    rw [dualTerm, norm_mul, RankTwoEisShift.dualPhase_norm, mul_one,
      eisGauss_norm, eisGauss_norm]
    have hq := eisQ_nonneg (z.1,-z.2)
    have hpq : 0 ≤ Real.pi * RankTwoPoisson.eisQ (z.1,-z.2) :=
      mul_nonneg Real.pi_pos.le hq
    have hm := mul_le_mul_of_nonneg_right hT hpq
    apply Real.exp_le_exp.mpr
    nlinarith [hm]
  have h := tendsto_tsum_of_dominated_convergence hE.norm
    (dualTerm_tendsto x y) hbound
  simpa [limitTerm] using h

end

open scoped Topology
open Filter

theorem dual_sum_tendsto_one_small_t (x y : ℝ) :
    Tendsto (fun t : ℝ => ∑' z : ℤ × ℤ, dualTerm (4 / (3 * t)) x y z)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hT : Tendsto (fun t : ℝ => (4 / 3 : ℝ) * t⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 4 / 3)).2
      tendsto_inv_nhdsGT_zero
  have h := (dual_sum_tendsto_one x y).comp hT
  simpa [Function.comp_def, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

end RankTwoLimit

namespace EisensteinGaussianPrefactor

theorem sqrt_product (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt t * Real.sqrt (3*t/4) =
      Real.sqrt 3 * t / 2 := by
  have h3 : Real.sqrt (3/4 : ℝ) = Real.sqrt 3 / 2 := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)]
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have harg : 3*t/4 = (3/4:ℝ)*t := by ring
  rw [harg, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3/4), h3]
  calc
    Real.sqrt t * (Real.sqrt 3 / 2 * Real.sqrt t) =
        Real.sqrt 3 / 2 * (Real.sqrt t)^2 := by ring
    _ = Real.sqrt 3 * t / 2 := by rw [Real.sq_sqrt ht]; ring

theorem eta_times_prefactor (η q : ℝ) (hη : 0 < η) (hq : 0 < q) :
    η * (1 / Real.sqrt (η*q)) *
      (1 / Real.sqrt (3*(η*q)/4)) =
      2 / (Real.sqrt 3 * q) := by
  have ht : 0 < η*q := mul_pos hη hq
  have hsqrt : Real.sqrt (η*q) * Real.sqrt (3*(η*q)/4) =
      Real.sqrt 3 * (η*q) / 2 := sqrt_product (η*q) ht.le
  have hne1 : Real.sqrt (η*q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hne2 : Real.sqrt (3*(η*q)/4) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    positivity
  have hne3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  calc
    η * (1 / Real.sqrt (η*q)) *
        (1 / Real.sqrt (3*(η*q)/4)) =
        η / (Real.sqrt (η*q) * Real.sqrt (3*(η*q)/4)) := by ring
    _ = η / (Real.sqrt 3 * (η*q) / 2) := by rw [hsqrt]
    _ = 2 / (Real.sqrt 3 * q) := by
      field_simp

end EisensteinGaussianPrefactor

namespace EisensteinGaussianPrefactor

theorem complex_eta_times_prefactor (η q : ℝ) (hη : 0 < η) (hq : 0 < q) :
    (η : ℂ) *
      (1 / ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ)) *
      (1 / (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ))) =
      ((2 / (Real.sqrt 3 * q) : ℝ) : ℂ) := by
  have ht : 0 ≤ η*q := (mul_pos hη hq).le
  have hs : 0 ≤ 3*(η*q)/4 := by positivity
  have hpow1 : ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ) =
      (Real.sqrt (η*q) : ℂ) := by
    calc
      ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ) =
          ((η*q : ℝ) : ℂ) ^ (((1/2 : ℝ) : ℂ)) := by norm_num
      _ = (((η*q) ^ (1/2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow ht (1/2 : ℝ)).symm
      _ = (Real.sqrt (η*q) : ℂ) := by rw [← Real.sqrt_eq_rpow]
  have hpow2 : (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ)) =
      (Real.sqrt (3*(η*q)/4) : ℂ) := by
    calc
      (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ)) =
          (((3*(η*q)/4 : ℝ) : ℂ) ^ (((1/2 : ℝ) : ℂ))) := by norm_num
      _ = (((3*(η*q)/4) ^ (1/2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow hs (1/2 : ℝ)).symm
      _ = (Real.sqrt (3*(η*q)/4) : ℂ) := by rw [← Real.sqrt_eq_rpow]
  rw [hpow1, hpow2]
  exact_mod_cast eta_times_prefactor η q hη hq

end EisensteinGaussianPrefactor

namespace EisensteinAbelFiber

open scoped Topology
open Filter

/-- Every real lattice shift has Abel mass equal to the reciprocal covolume. -/
theorem shifted_gaussian_mass (x y : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z))
      (𝓝[>] (0 : ℝ)) (𝓝 (((2 / Real.sqrt 3 : ℝ) : ℂ))) := by
  have hpoint (t : ℝ) (ht : 0 < t) :
      (t : ℂ) * (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z) =
        ((2 / Real.sqrt 3 : ℝ) : ℂ) *
          (∑' z : ℤ × ℤ, RankTwoLimit.dualTerm (4 / (3 * t)) x y z) := by
    rw [RankTwoEisShift.shifted_eisenstein_gaussian_poisson ht x y]
    have hpre := EisensteinGaussianPrefactor.complex_eta_times_prefactor
      t 1 ht (by norm_num)
    simp only [mul_one] at hpre
    change (t : ℂ) *
        ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) = _
    calc
      (t : ℂ) * ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) =
        (((t : ℂ) * (1 / (t : ℂ) ^ (1 / 2 : ℂ))) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ)))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z) := by ring
      _ = _ := by rw [hpre]
  have hlim := (RankTwoLimit.dual_sum_tendsto_one_small_t x y).const_mul
    (((2 / Real.sqrt 3 : ℝ) : ℂ))
  have heq : (fun t : ℝ => (t : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ((2 / Real.sqrt 3 : ℝ) : ℂ) *
        (∑' z : ℤ × ℤ, RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpoint t ht
  simpa using hlim.congr' heq.symm

theorem scaled_shifted_gaussian_mass (q : ℝ) (hq : 0 < q)
    (x y : ℝ) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted (η*q) x y z))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 * q) : ℝ) : ℂ))) := by
  have hscale : Tendsto (fun η : ℝ => η*q)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hid : Tendsto (fun η : ℝ => η)
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      simpa using hid.mul_const q
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact mul_pos hη hq
  have hlim := (shifted_gaussian_mass x y).comp hscale
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hlim' := hlim.const_mul (1 / (q : ℂ))
  convert hlim' using 1
  · funext η
    dsimp
    push_cast
    field_simp [hqC]
  · push_cast
    field_simp [hqC]

end EisensteinAbelFiber

end QuadraticPhase

open scoped BigOperators

namespace QuadraticPhase.Eisenstein
open Coordinates

/-- Dividing by a principal modulus gives the alternating coordinate pairing over its norm. -/
theorem trace_fraction_coordinates (a b x y : ℤ) (hc : eval a b ≠ 0) :
    Algebra.trace ℚ K
      (algebraMap O K (eval x y) /
        (algebraMap O K traceLambda * algebraMap O K (eval a b))) =
      ((a*y-b*x : ℤ) : ℚ) / ((a*a-a*b+b*b : ℤ) : ℚ) := by
  have hcK : algebraMap O K (eval a b) ≠ 0 :=
    fun h => hc (NumberField.RingOfIntegers.coe_injective h)
  have hnorm : algebraMap O K (eval a b) * algebraMap O K (conjO (eval a b)) =
      ((a*a-a*b+b*b : ℤ) : K) := by
    have h := congrArg (algebraMap O K) (eval_mul_conj a b)
    simpa only [map_mul, map_intCast, pow_two] using h
  have hnum : algebraMap O K (eval x y) * algebraMap O K (conjO (eval a b)) =
      ((x*(a-b)+y*b : ℤ) : K) + ((a*y-b*x : ℤ) : K) * algebraMap O K omega := by
    rw [← map_mul, conj_eval, eval_mul]
    simp only [eval, map_add, map_mul, map_intCast]
    push_cast
    ring
  have hquot : algebraMap O K (eval x y) / algebraMap O K (eval a b) =
      ((((x*(a-b)+y*b : ℤ) : ℚ) / ((a*a-a*b+b*b : ℤ) : ℚ)) : K) +
      ((((a*y-b*x : ℤ) : ℚ) / ((a*a-a*b+b*b : ℤ) : ℚ)) : K) * algebraMap O K omega := by
    calc
      _ = (algebraMap O K (eval x y) * algebraMap O K (conjO (eval a b))) /
          ((a*a-a*b+b*b : ℤ) : K) := by
        rw [← hnorm]
        have hconj : algebraMap O K (conjO (eval a b)) ≠ 0 := by
          intro h
          apply hc
          apply conjO.injective
          simpa only [map_zero] using NumberField.RingOfIntegers.coe_injective h
        field_simp [hcK, hconj]
      _ = _ := by rw [hnum]; push_cast; ring
  have harg : algebraMap O K (eval x y) /
      (algebraMap O K traceLambda * algebraMap O K (eval a b)) =
      (algebraMap O K (eval x y) / algebraMap O K (eval a b)) /
        algebraMap O K traceLambda := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [harg, hquot]
  convert trace_div_traceLambda
    (((x*(a-b)+y*b : ℤ) : ℚ) / ((a*a-a*b+b*b : ℤ) : ℚ))
    (((a*y-b*x : ℤ) : ℚ) / ((a*a-a*b+b*b : ℤ) : ℚ)) using 1
  push_cast
  rfl

/-- The analytic trace character in integral coordinates. -/
theorem principalTraceChar_eval (a b x y : ℤ) (hc : eval a b ≠ 0) :
    principalTraceChar (eval a b) hc (Ideal.Quotient.mk (Ideal.span {eval a b}) (eval x y)) =
      Complex.exp (2 * Real.pi * Complex.I *
        (((a*y-b*x : ℤ) : ℂ) / ((a*a-a*b+b*b : ℤ) : ℂ))) := by
  rw [principalTraceChar_apply, trace_fraction_coordinates a b x y hc]
  congr 1
  push_cast
  ring

/-- Squaring the residue argument gives the oscillatory binary phase. -/
theorem principalTraceChar_square (a b x y : ℤ) (hc : eval a b ≠ 0) :
    principalTraceChar (eval a b) hc
      (Ideal.Quotient.mk (Ideal.span {eval a b}) (eval x y) ^ 2) =
      Complex.exp (2 * Real.pi * Complex.I *
        (((-b*x*x+2*a*x*y+(b-a)*y*y : ℤ) : ℂ) /
          ((a*a-a*b+b*b : ℤ) : ℂ))) := by
  rw [← map_pow, pow_two, eval_mul, principalTraceChar_eval]
  congr 1
  push_cast
  ring

/-- The quadratic trace sum on the actual principal quotient. -/
def quadraticTraceGauss (c : O) (hc : c ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {c}) :=
    (Ideal.span {c}).finiteQuotientOfFreeOfNeBot
      (fun h => hc (Ideal.span_singleton_eq_bot.mp h))
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact ∑ x : O ⧸ Ideal.span {c}, principalTraceChar c hc (x ^ 2)

/-- Divide the quadratic trace sum by the complex modulus of the generator. -/
def normalizedQuadraticTraceGauss (c : O) (hc : c ≠ 0) : ℂ :=
  quadraticTraceGauss c hc / (‖ringComplex c‖ : ℂ)

/-- The fixed dual phase is an actual quadratic residue phase modulo four. -/
def fixedDualPhase (c y : O) : ℂ :=
  principalTraceChar 4 (by norm_num) (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (-(c*y^2)))

/-- A shift by two changes the squared numerator by a multiple of four. -/
theorem fixedDualPhase_period_two (c y w : O) :
    fixedDualPhase c (y + 2*w) = fixedDualPhase c y := by
  apply congrArg (principalTraceChar 4 (by norm_num))
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨-(c * (y*w+w^2)), ?_⟩
  ring

theorem fixedDualPhase_eq_of_mod_two (c y z : O)
    (h : Ideal.Quotient.mk (Ideal.span {(2 : O)}) y =
      Ideal.Quotient.mk (Ideal.span {(2 : O)}) z) :
    fixedDualPhase c y = fixedDualPhase c z := by
  have hsub : y-z ∈ Ideal.span {(2 : O)} :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hsub
  have hy : y = z + 2*w := by
    calc
      y = z+(y-z) := by ring
      _ = z+2*w := by rw [hw]
  rw [hy, fixedDualPhase_period_two]

/-- At modulus four, the analytic character is the fourth root prescribed by the second coordinate. -/
theorem principalTraceChar_four (x y : ℤ) :
    principalTraceChar 4 (by norm_num)
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (eval x y)) = Complex.I ^ y := by
  have h4 : eval 4 0 = 4 := by norm_num [eval]
  have ht := trace_fraction_coordinates 4 0 x y (by rw [h4]; norm_num)
  rw [h4] at ht
  rw [principalTraceChar_apply, ht]
  calc
    _ = Complex.exp ((y : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I)) := by
      congr 1
      push_cast
      ring
    _ = Complex.I ^ y := by
      rw [Complex.exp_int_mul, Complex.exp_pi_div_two_mul_I]

private theorem neg_eval (a b : ℤ) : -eval a b = eval (-a) (-b) := by
  simp only [eval, Int.cast_neg]
  ring

/-- The fixed dual phase is a fourth root of unity with an explicit integral exponent. -/
theorem fixedDualPhase_eval (a b x y : ℤ) :
    fixedDualPhase (eval a b) (eval x y) =
      Complex.I ^ (-(b*x*x + 2*(a-b)*x*y - a*y*y)) := by
  unfold fixedDualPhase
  rw [pow_two, eval_mul, eval_mul, neg_eval, principalTraceChar_four]
  congr 1
  ring

/-- The fixed phase has unit modulus. -/
theorem fixedDualPhase_norm (c y : O) : ‖fixedDualPhase c y‖ = 1 := by
  obtain ⟨a,b,rfl⟩ := exists_coordinates c
  obtain ⟨x,y,rfl⟩ := exists_coordinates y
  change ‖fixedDualPhase (eval a b) (eval x y)‖ = 1
  rw [fixedDualPhase_eval, norm_zpow, Complex.norm_I, one_zpow]

/-- The four residue phases, with the normalization from the rank-two Gaussian transform. -/
def fixedDualAverage (c : O) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
    (Ideal.span {(2 : O)}).finiteQuotientOfFreeOfNeBot
      (fun h => (by norm_num : (2 : O) ≠ 0) (Ideal.span_singleton_eq_bot.mp h))
  letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  exact (∑ r : O ⧸ Ideal.span {(2 : O)},
    fixedDualPhase c (Classical.choose (Ideal.Quotient.mk_surjective r))) / 2

private theorem sum_zmod_two_square (f : ZMod 2 × ZMod 2 → ℂ) :
    (∑ p : ZMod 2 × ZMod 2, f p) =
      f (0,0) + f (0,1) + f (1,0) + f (1,1) := by
  rw [Fintype.sum_prod_type]
  have hu : (Finset.univ : Finset (ZMod 2)) = {0,1} := rfl
  simp [hu]
  ring

/-- The dual residue average depends only on the modulus coordinates modulo four. -/
theorem fixedDualAverage_formula (a b : ℤ) :
    fixedDualAverage (eval a b) =
      (1 + Complex.I ^ (-b) + Complex.I ^ a + Complex.I ^ (b-a)) / 2 := by
  letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
    (Ideal.span {(2 : O)}).finiteQuotientOfFreeOfNeBot
      (fun h => (by norm_num : (2 : O) ≠ 0) (Ideal.span_singleton_eq_bot.mp h))
  letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let e := rationalCoordEquiv 2 (by norm_num)
  let P : O ⧸ Ideal.span {(2 : O)} → ℂ := fun r =>
    fixedDualPhase (eval a b) (Classical.choose (Ideal.Quotient.mk_surjective r))
  have hpoint (p : ZMod 2 × ZMod 2) : P (e p) =
      fixedDualPhase (eval a b) (eval (ZMod.cast p.1) (ZMod.cast p.2)) := by
    apply fixedDualPhase_eq_of_mod_two
    exact (Classical.choose_spec (Ideal.Quotient.mk_surjective (e p))).trans (by rfl)
  have hsum : (∑ r, P r) = ∑ p : ZMod 2 × ZMod 2,
      fixedDualPhase (eval a b) (eval (ZMod.cast p.1) (ZMod.cast p.2)) := by
    calc
      _ = ∑ p, P (e p) := (e.sum_comp P).symm
      _ = _ := Finset.sum_congr rfl (fun p _ => hpoint p)
  change (∑ r, P r) / 2 = _
  rw [hsum, sum_zmod_two_square]
  have hcast1 : (ZMod.cast (1 : ZMod 2) : ℤ) = 1 := by decide
  simp only [ZMod.cast_zero, hcast1, fixedDualPhase_eval,
    mul_zero, mul_one, add_zero, sub_zero, neg_zero, zero_sub, zpow_zero, neg_neg]
  rw [show -(b + 2 * (a-b) - a) = b-a by ring]
  ring

theorem fixedDualPhase_eq_of_mod_four (c d y : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) :
    fixedDualPhase c y = fixedDualPhase d y := by
  simp only [fixedDualPhase, map_neg, map_mul, h]

/-- The complete dual average factors through reduction of the modulus modulo four. -/
theorem fixedDualAverage_eq_of_mod_four (c d : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) :
    fixedDualAverage c = fixedDualAverage d := by
  unfold fixedDualAverage
  congr 1
  exact Finset.sum_congr rfl (fun r _ => fixedDualPhase_eq_of_mod_four c d _ h)

theorem fixedDualAverage_one : fixedDualAverage 1 = 1 := by
  have h := fixedDualAverage_formula 1 0
  norm_num [eval] at h
  exact h

/-- The principal residue class modulo four has trivial dual Gauss phase. -/
theorem fixedDualAverage_eq_one (c : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c = 1) :
    fixedDualAverage c = 1 := by
  rw [fixedDualAverage_eq_of_mod_four c 1 (by simpa only [map_one] using h),
    fixedDualAverage_one]

end QuadraticPhase.Eisenstein

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
