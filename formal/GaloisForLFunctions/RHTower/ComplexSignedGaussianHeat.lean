import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Signed Gaussian integration on the two complex spectral sectors

On `Re(z^2)>0`, the Gaussian integral chooses the sign of `Re z`.
Truncation on symmetric real intervals is odd in `z`, converges to the
complete integral, and has a uniform bound controlled by the spectral angle.
-/

open Complex MeasureTheory Set Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- The Gaussian integral in the right component of the square-positive region. -/
theorem integral_complexGaussian_sq_of_re_pos {z : ℂ}
    (hz : 0 < z.re) (hzsq : 0 < (z ^ 2).re) :
    (∫ t : ℝ, Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2)) =
      (Real.sqrt Real.pi : ℂ) / z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hroot : 0 < ((Real.sqrt Real.pi : ℂ) / z).re := by
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
    exact div_pos (mul_pos hp hz) (Complex.normSq_pos.mpr hz0)
  have hsq : ((Real.sqrt Real.pi : ℂ) / z) ^ 2 = (Real.pi : ℂ) / z ^ 2 := by
    rw [div_pow, ← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  rw [integral_gaussian_complex hzsq, ← hsq]
  simpa only [one_div] using Complex.sq_cpow_two_inv hroot

/-- The left component carries the opposite Gaussian orientation. -/
theorem integral_complexGaussian_sq_of_re_neg {z : ℂ}
    (hz : z.re < 0) (hzsq : 0 < (z ^ 2).re) :
    (∫ t : ℝ, Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2)) =
      -((Real.sqrt Real.pi : ℂ) / z) := by
  simpa only [neg_sq, div_neg] using
    integral_complexGaussian_sq_of_re_pos
      (z := -z) (by simpa using hz) (by simpa only [neg_sq] using hzsq)

theorem norm_complexGaussian_sq (z : ℂ) (t : ℝ) :
    ‖Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2)‖ =
      Real.exp (-((z ^ 2).re) * t ^ 2) := by
  simp only [Complex.norm_exp, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

/-- Signed Gaussian integral over a symmetric finite time window. -/
def complexSignedGaussianWindow (N : ℕ) (z : ℂ) : ℂ :=
  z / (Real.sqrt Real.pi : ℂ) *
    ∫ t : ℝ in Icc (-(N : ℝ)) N, Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2)

theorem complexSignedGaussianWindow_neg (N : ℕ) (z : ℂ) :
    complexSignedGaussianWindow N (-z) = -complexSignedGaussianWindow N z := by
  simp only [complexSignedGaussianWindow, neg_sq, neg_div, neg_mul]

/-- A bound uniform in the cutoff, depending only on the spectral angle. -/
theorem norm_complexSignedGaussianWindow_le (N : ℕ) {z : ℂ}
    (hzsq : 0 < (z ^ 2).re) :
    ‖complexSignedGaussianWindow N z‖ ≤ ‖z‖ / Real.sqrt (z ^ 2).re := by
  have hg := integrable_cexp_neg_mul_sq hzsq
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hA : Real.sqrt (z ^ 2).re ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hzsq)
  have hi :
      ‖∫ t : ℝ in Icc (-(N : ℝ)) N, Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2)‖ ≤
        Real.sqrt Real.pi / Real.sqrt (z ^ 2).re := by
    calc
      _ ≤ ∫ t : ℝ in Icc (-(N : ℝ)) N,
          ‖Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, ‖Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2)‖ :=
        setIntegral_le_integral hg.norm (ae_of_all _ (fun _ => norm_nonneg _))
      _ = Real.sqrt (Real.pi / (z ^ 2).re) := by
        simp only [norm_complexGaussian_sq]
        exact integral_gaussian _
      _ = _ := Real.sqrt_div Real.pi_pos.le _
  rw [complexSignedGaussianWindow, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (‖z‖ / Real.sqrt Real.pi) *
        (Real.sqrt Real.pi / Real.sqrt (z ^ 2).re) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by field_simp [hp, hA]

/-- A uniform Gaussian tail estimate on a square-positive sector with a fixed gap. -/
theorem norm_complexSignedGaussianWindow_sub_le (N : ℕ) {z : ℂ}
    (hgap : 2 ≤ (z ^ 2).re) (hsector : ‖z‖ ^ 2 ≤ 2 * (z ^ 2).re) :
    ‖complexSignedGaussianWindow N z - z / (Real.sqrt Real.pi : ℂ) *
        (∫ t : ℝ, Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2))‖ ≤
      2 * Real.exp (-(N : ℝ) ^ 2) := by
  let A : ℝ := (z ^ 2).re
  have hA : 0 < A := by dsimp [A]; linarith
  have hhalf : 0 < A / 2 := by positivity
  have hg := integrable_cexp_neg_mul_sq hA
  have hmajor := (integrable_exp_neg_mul_sq hhalf).const_mul
    (Real.exp (-(N : ℝ) ^ 2))
  have hpoint (t : ℝ) (ht : t ∈ (Icc (-(N : ℝ)) N)ᶜ) :
      ‖Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2)‖ ≤
        Real.exp (-(N : ℝ) ^ 2) * Real.exp (-(A / 2) * t ^ 2) := by
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have ht2 : (N : ℝ) ^ 2 ≤ t ^ 2 := by
      rcases lt_or_ge t (-(N : ℝ)) with hlo | hlo
      · nlinarith [mul_nonneg (show 0 ≤ -t - (N : ℝ) by linarith)
          (show 0 ≤ -t + (N : ℝ) by linarith)]
      · have hhi : (N : ℝ) < t :=
          lt_of_not_ge (fun h => ht ⟨hlo, h⟩)
        nlinarith [mul_nonneg (show 0 ≤ t - (N : ℝ) by linarith)
          (show 0 ≤ t + (N : ℝ) by linarith)]
    rw [norm_complexGaussian_sq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hA2 : 0 ≤ A / 2 - 1 := by dsimp [A]; linarith
    change -A * t ^ 2 ≤ -(N : ℝ) ^ 2 + -(A / 2) * t ^ 2
    nlinarith [mul_nonneg hA2 (sq_nonneg t)]
  have htail :
      ‖∫ t : ℝ in (Icc (-(N : ℝ)) N)ᶜ,
        Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2)‖ ≤
      Real.exp (-(N : ℝ) ^ 2) * (Real.sqrt Real.pi / Real.sqrt (A / 2)) := by
    calc
      _ ≤ ∫ t : ℝ in (Icc (-(N : ℝ)) N)ᶜ,
          ‖Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ in (Icc (-(N : ℝ)) N)ᶜ,
          Real.exp (-(N : ℝ) ^ 2) * Real.exp (-(A / 2) * t ^ 2) :=
        setIntegral_mono_on hg.norm.integrableOn hmajor.integrableOn
          measurableSet_Icc.compl hpoint
      _ ≤ ∫ t : ℝ,
          Real.exp (-(N : ℝ) ^ 2) * Real.exp (-(A / 2) * t ^ 2) :=
        setIntegral_le_integral hmajor (ae_of_all _ (fun _ => by positivity))
      _ = _ := by
        rw [integral_const_mul, integral_gaussian, Real.sqrt_div Real.pi_pos.le]
  have herr :
      complexSignedGaussianWindow N z - z / (Real.sqrt Real.pi : ℂ) *
          (∫ t : ℝ, Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2)) =
        -(z / (Real.sqrt Real.pi : ℂ) *
          ∫ t : ℝ in (Icc (-(N : ℝ)) N)ᶜ,
            Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2)) := by
    rw [setIntegral_compl measurableSet_Icc hg]
    unfold complexSignedGaussianWindow
    ring
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hs : 0 < Real.sqrt (A / 2) := Real.sqrt_pos.mpr hhalf
  have hratio : ‖z‖ / Real.sqrt (A / 2) ≤ 2 := by
    apply (div_le_iff₀ hs).mpr
    have hs2 := Real.sq_sqrt hhalf.le
    change ‖z‖ ^ 2 ≤ 2 * A at hsector
    nlinarith [norm_nonneg z]
  rw [herr, norm_neg, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (‖z‖ / Real.sqrt Real.pi) *
        (Real.exp (-(N : ℝ) ^ 2) * (Real.sqrt Real.pi / Real.sqrt (A / 2))) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = Real.exp (-(N : ℝ) ^ 2) * (‖z‖ / Real.sqrt (A / 2)) := by
      field_simp [hp, ne_of_gt hs]
    _ ≤ Real.exp (-(N : ℝ) ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- Increasing Gaussian time windows converge to the full signed transform. -/
theorem tendsto_complexSignedGaussianWindow {z : ℂ} (hzsq : 0 < (z ^ 2).re) :
    Tendsto (fun N : ℕ => complexSignedGaussianWindow N z) atTop
      (𝓝 (z / (Real.sqrt Real.pi : ℂ) *
        ∫ t : ℝ, Complex.exp (-(z ^ 2) * (t : ℂ) ^ 2))) := by
  have hmono : Monotone (fun N : ℕ => Icc (-(N : ℝ)) N) := by
    intro m n hmn t ht
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have huniv : (⋃ N : ℕ, Icc (-(N : ℝ)) N) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    obtain ⟨N, hN⟩ := exists_nat_gt |t|
    exact Set.mem_iUnion.mpr ⟨N, by
      constructor <;> linarith [neg_abs_le t, le_abs_self t]⟩
  have h := tendsto_setIntegral_of_monotone
    (fun N : ℕ => measurableSet_Icc (a := -(N : ℝ)) (b := N)) hmono
    (integrable_cexp_neg_mul_sq hzsq).integrableOn
  simp only [huniv, Measure.restrict_univ] at h
  exact h.const_mul _

end

end RHTower
