/-
Portions adapted from OpenAI’s Gauss-sum formalization, Apache-2.0.
See LICENSE and NOTICE in this directory for source attribution.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Poisson summation for the oscillatory binary Gaussian

Two one-dimensional Gaussian transforms give the binary formula. Positivity
of the real quadratic forms proves summability at both intermediate stages;
a logarithm calculation fixes the square-root branch. For the quadratic
Eisenstein trace phase the determinant is the positive real number
`4 / (a²-ab+b²) + 3η²/4`, so no oscillatory convergence assumption remains.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
namespace GaloisForLFunctions.MetaplecticMobiusDescent

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
end GaloisForLFunctions.MetaplecticMobiusDescent

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.OscSpecial.binary_gaussian_poisson_real_det
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.OscSpecial.oscillatory_gaussian_poisson
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.OscSpecial.dualGaussian_explicit
