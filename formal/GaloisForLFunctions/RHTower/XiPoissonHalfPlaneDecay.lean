import GaloisForLFunctions.RHTower.XiPoissonTraceAnalytic
import GaloisForLFunctions.RHTower.XiPoissonBottomExtraction
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Boundedness on one vertical line upgrades to half-plane decay

Twist the Poisson trace by the bottom height:

`W(y) = Theta (sigma + y I) * exp (I g_1 y)`.

On the real `y`-axis the twist has modulus one, so `W` is bounded there exactly when `Theta` is
bounded on the vertical line `Re t = sigma`.  On the negative imaginary `y`-axis the twist is
`exp (g_1 v)` while `Theta` decays like `exp (-(sigma+v) R)`, and `R >= g_1` for every copy, so `W`
is bounded there unconditionally.  `W` has exponential type, hence order `1 < 2`, so
Phragmén--Lindelöf on the two lower quadrants propagates the two boundary bounds into the whole
closed lower half `y`-plane.  Back in the heat time this reads

`‖Theta t‖ <= M exp (-g_1 (Re t - sigma))`   for `Re t >= sigma`.

The order-`1` envelope is what makes the quadrant hypothesis `∃ c < 2` available; the Gaussian trace,
whose vertical envelope has order exactly `2`, fails it.
-/

open Complex Filter Asymptotics
open scoped BigOperators

namespace RHTower

noncomputable section

theorem xiPoissonBottomHeight_nonneg : 0 ≤ xiPoissonBottomHeight :=
  xiPoissonPoint_re_nonneg _

theorem xiPoissonTraceReal_nonneg (σ : ℝ) : 0 ≤ xiPoissonTraceReal σ := by
  rw [xiPoissonTraceReal]
  exact tsum_nonneg fun q => (xiPoissonWeight_pos σ q).le

/-- The real-time Poisson trace is antitone. -/
theorem xiPoissonTraceReal_antitone {σ v : ℝ} (hσ : 0 < σ) (hv : 0 ≤ v) :
    xiPoissonTraceReal (σ + v) ≤ xiPoissonTraceReal σ := by
  have hkey := exp_bottomHeight_mul_xiPoissonTraceReal_le hσ hv
  have hone : (1 : ℝ) ≤ Real.exp (xiPoissonBottomHeight * v) :=
    Real.one_le_exp (mul_nonneg xiPoissonBottomHeight_nonneg hv)
  nlinarith [xiPoissonTraceReal_nonneg (σ + v)]

/-- The bottom-height twist of the Poisson trace, in the vertical variable. -/
def xiPoissonTwist (σ : ℝ) (y : ℂ) : ℂ :=
  xiPoissonTraceC ((σ : ℂ) + y * I) * Complex.exp (I * (xiPoissonBottomHeight : ℂ) * y)

theorem norm_exp_bottomTwist (y : ℂ) :
    ‖Complex.exp (I * (xiPoissonBottomHeight : ℂ) * y)‖ =
      Real.exp (-(xiPoissonBottomHeight * y.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- On the closed lower half `y`-plane the twist is differentiable. -/
theorem differentiableOn_xiPoissonTwist (σ : ℝ) :
    DifferentiableOn ℂ (xiPoissonTwist σ) {y : ℂ | y.im < σ} := by
  intro y hy
  have hre : 0 < ((σ : ℂ) + y * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub]
    have : y.im < σ := hy
    linarith
  have h1 : DifferentiableAt ℂ (fun z : ℂ => xiPoissonTraceC ((σ : ℂ) + z * I)) y := by
    have hcomp : DifferentiableAt ℂ (fun z : ℂ => (σ : ℂ) + z * I) y := by fun_prop
    exact (differentiableAt_xiPoissonTraceC hre).comp y hcomp
  have h2 : DifferentiableAt ℂ
      (fun z : ℂ => Complex.exp (I * (xiPoissonBottomHeight : ℂ) * z)) y := by fun_prop
  exact ((h1.mul h2)).differentiableWithinAt

/-- The unconditional exponential-type bound for the twist on the closed lower half plane. -/
theorem norm_xiPoissonTwist_le {σ : ℝ} (hσ : 0 < σ) {y : ℂ} (hy : y.im ≤ 0) :
    ‖xiPoissonTwist σ y‖ ≤
      xiPoissonTraceReal σ *
        Real.exp ((1 / 2 + xiPoissonBottomHeight) * ‖y‖) := by
  have hre : 0 < ((σ : ℂ) + y * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub]
    linarith
  have hreEq : ((σ : ℂ) + y * I).re = σ - y.im := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub]
    ring
  have himEq : ((σ : ℂ) + y * I).im = y.re := by
    simp [Complex.mul_im]
  have hΘ := norm_xiPoissonTraceC_le (τ := (σ : ℂ) + y * I) hre
  rw [himEq, hreEq] at hΘ
  have hmono : xiPoissonTraceReal (σ - y.im) ≤ xiPoissonTraceReal σ := by
    have h := xiPoissonTraceReal_antitone (σ := σ) (v := -y.im) hσ (by linarith)
    have heq : σ + -y.im = σ - y.im := by ring
    rwa [heq] at h
  have hΘ' : ‖xiPoissonTraceC ((σ : ℂ) + y * I)‖ ≤
      Real.exp (|y.re| / 2) * xiPoissonTraceReal σ := by
    refine hΘ.trans ?_
    exact mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
  rw [xiPoissonTwist, norm_mul, norm_exp_bottomTwist]
  have hb1 : |y.re| / 2 ≤ ‖y‖ / 2 := by
    have := Complex.abs_re_le_norm y
    linarith
  have hb2 : -(xiPoissonBottomHeight * y.im) ≤ xiPoissonBottomHeight * ‖y‖ := by
    have him : |y.im| ≤ ‖y‖ := Complex.abs_im_le_norm y
    have h1 : -y.im ≤ ‖y‖ := le_trans (neg_le_abs _) him
    nlinarith [xiPoissonBottomHeight_nonneg]
  calc ‖xiPoissonTraceC ((σ : ℂ) + y * I)‖ * Real.exp (-(xiPoissonBottomHeight * y.im))
      ≤ (Real.exp (|y.re| / 2) * xiPoissonTraceReal σ) *
          Real.exp (xiPoissonBottomHeight * ‖y‖) := by
        refine mul_le_mul hΘ' (Real.exp_le_exp.mpr hb2) (Real.exp_pos _).le ?_
        exact mul_nonneg (Real.exp_pos _).le (xiPoissonTraceReal_nonneg σ)
    _ ≤ xiPoissonTraceReal σ * Real.exp ((1 / 2 + xiPoissonBottomHeight) * ‖y‖) := by
        rw [mul_comm (Real.exp (|y.re| / 2)), mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ?_
        · nlinarith [hb1]
        · exact xiPoissonTraceReal_nonneg σ

/-- The boundary bound on the negative imaginary ray, unconditionally. -/
theorem norm_xiPoissonTwist_imaginary_ray {σ : ℝ} (hσ : 0 < σ) {x : ℝ} (hx : x ≤ 0) :
    ‖xiPoissonTwist σ ((x : ℂ) * I)‖ ≤ xiPoissonTraceReal σ := by
  have harg : (σ : ℂ) + ((x : ℂ) * I) * I = ((σ - x : ℝ) : ℂ) := by
    have : ((x : ℂ) * I) * I = -(x : ℂ) := by
      rw [mul_assoc, Complex.I_mul_I]; ring
    rw [this]
    push_cast
    ring
  have hre : 0 < (((σ - x : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hΘ := norm_xiPoissonTraceC_le (τ := ((σ - x : ℝ) : ℂ)) hre
  simp only [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_div, Real.exp_zero,
    one_mul] at hΘ
  have htw : ‖Complex.exp (I * (xiPoissonBottomHeight : ℂ) * ((x : ℂ) * I))‖ =
      Real.exp (-(xiPoissonBottomHeight * x)) := by
    rw [norm_exp_bottomTwist]
    congr 2
    simp
  rw [xiPoissonTwist, norm_mul, harg, htw]
  have hkey := exp_bottomHeight_mul_xiPoissonTraceReal_le hσ (v := -x) (by linarith)
  have hrw : σ + -x = σ - x := by ring
  rw [hrw] at hkey
  have hexp : Real.exp (-(xiPoissonBottomHeight * x)) =
      Real.exp (xiPoissonBottomHeight * -x) := by congr 1; ring
  rw [hexp, mul_comm]
  refine le_trans (mul_le_mul_of_nonneg_left hΘ (Real.exp_pos _).le) hkey

/-- The boundary bound on the real ray: the twist has modulus one there. -/
theorem norm_xiPoissonTwist_real_ray {σ C : ℝ}
    (hline : ∀ x : ℝ, ‖xiPoissonTraceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) (x : ℝ) :
    ‖xiPoissonTwist σ ((x : ℝ) : ℂ)‖ ≤ C := by
  rw [xiPoissonTwist, norm_mul, norm_exp_bottomTwist]
  simp only [Complex.ofReal_im, mul_zero, neg_zero, Real.exp_zero, mul_one]
  exact hline x

/-- **Phragmén--Lindelöf on the two lower quadrants.**  A bound on one vertical line propagates to
the whole closed lower half `y`-plane, because the twist has exponential type (order `1 < 2`) and its
two boundary rays are bounded. -/
theorem norm_xiPoissonTwist_le_of_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖xiPoissonTraceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C)
    {y : ℂ} (hy : y.im ≤ 0) :
    ‖xiPoissonTwist σ y‖ ≤ max C (xiPoissonTraceReal σ) := by
  have hdiff := differentiableOn_xiPoissonTwist σ
  have hsub : ∀ s t : Set ℝ, closure (s ×ℂ t) ⊆ {z : ℂ | z.im < σ} →
      DiffContOnCl ℂ (xiPoissonTwist σ) (s ×ℂ t) := by
    intro s t hsu
    exact ⟨hdiff.mono (subset_closure.trans hsu), (hdiff.mono hsu).continuousOn⟩
  have hclos : ∀ s : Set ℝ, closure (s ×ℂ Set.Iio 0) ⊆ {z : ℂ | z.im < σ} := by
    intro s z hz
    rw [Complex.closure_reProdIm, closure_Iio] at hz
    have h := (Complex.mem_reProdIm.mp hz).2
    simp only [Set.mem_Iic] at h
    simp only [Set.mem_setOf_eq]
    linarith
  have hO : ∀ S : Set ℂ, (∀ z ∈ S, z.im ≤ 0) →
      (xiPoissonTwist σ) =O[Bornology.cobounded ℂ ⊓ 𝓟 S]
        (fun z => Real.exp ((1 / 2 + xiPoissonBottomHeight) * ‖z‖ ^ (1 : ℝ))) := by
    intro S hS
    refine isBigO_iff.mpr ⟨xiPoissonTraceReal σ, ?_⟩
    rw [eventually_inf_principal]
    filter_upwards with z hz
    rw [Real.rpow_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact norm_xiPoissonTwist_le hσ (hS z hz)
  have hgrow : ∀ S : Set ℂ, (∀ z ∈ S, z.im ≤ 0) →
      ∃ c < (2 : ℝ), ∃ B, (xiPoissonTwist σ) =O[Bornology.cobounded ℂ ⊓ 𝓟 S]
        fun z => Real.exp (B * ‖z‖ ^ c) :=
    fun S hS => ⟨1, by norm_num, 1 / 2 + xiPoissonBottomHeight, hO S hS⟩
  have hrealRay : ∀ x : ℝ, ‖xiPoissonTwist σ ((x : ℝ) : ℂ)‖ ≤ max C (xiPoissonTraceReal σ) :=
    fun x => le_trans (norm_xiPoissonTwist_real_ray hline x) (le_max_left _ _)
  rcases le_or_gt y.re 0 with hcase | hcase
  · refine PhragmenLindelof.quadrant_III
      (hsub (Set.Iio 0) (Set.Iio 0) (hclos (Set.Iio 0)))
      (hgrow (Set.Iio 0 ×ℂ Set.Iio 0)
        (fun z hz => (Set.mem_Iio.mp (Complex.mem_reProdIm.mp hz).2).le))
      (fun x _ => hrealRay x)
      (fun x hx => le_trans (norm_xiPoissonTwist_imaginary_ray hσ hx) (le_max_right _ _))
      hcase hy
  · refine PhragmenLindelof.quadrant_IV
      (hsub (Set.Ioi 0) (Set.Iio 0) (hclos (Set.Ioi 0)))
      (hgrow (Set.Ioi 0 ×ℂ Set.Iio 0)
        (fun z hz => (Set.mem_Iio.mp (Complex.mem_reProdIm.mp hz).2).le))
      (fun x _ => hrealRay x)
      (fun x hx => le_trans (norm_xiPoissonTwist_imaginary_ray hσ hx) (le_max_right _ _))
      hcase.le hy

/-- **Half-plane decay from a single line bound.**  If the Poisson trace is bounded on the vertical
line `Re t = sigma`, then on the whole half-plane `Re t >= sigma` it decays at the bottom-shell
rate. -/
theorem norm_xiPoissonTraceC_le_of_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖xiPoissonTraceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C)
    {t : ℂ} (ht : σ ≤ t.re) :
    ‖xiPoissonTraceC t‖ ≤
      max C (xiPoissonTraceReal σ) * Real.exp (-(xiPoissonBottomHeight * (t.re - σ))) := by
  set y : ℂ := -I * (t - (σ : ℂ)) with hy
  have hyim : y.im = σ - t.re := by
    rw [hy]
    simp [Complex.mul_im]
  have hyle : y.im ≤ 0 := by rw [hyim]; linarith
  have harg : (σ : ℂ) + y * I = t := by
    rw [hy]
    have : (-I * (t - (σ : ℂ))) * I = t - (σ : ℂ) := by
      rw [mul_comm (-I) _, mul_assoc]
      simp [Complex.I_mul_I]
    rw [this]
    ring
  have hpl := norm_xiPoissonTwist_le_of_line_bound hσ hline hyle
  rw [xiPoissonTwist, harg, norm_mul, norm_exp_bottomTwist, hyim] at hpl
  have hexp : Real.exp (-(xiPoissonBottomHeight * (σ - t.re))) =
      Real.exp (xiPoissonBottomHeight * (t.re - σ)) := by congr 1; ring
  rw [hexp] at hpl
  rw [← le_div_iff₀ (Real.exp_pos _)] at hpl
  refine le_trans hpl (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

end

end RHTower
