import GaloisForLFunctions.RHTower.ThetaGroupCuspChargeTail
import Zeta23.Defs

/-!
# Riemann's kernel lies in the radical of the Weil form

Riemann's kernel `Φ = T'' - T/4`, with `T(x) = e^{x/2}(θ(ie^{2x}) - 1)/2`, has two-sided Laplace
transform `∫ Φ(x) e^{(s-1/2)x} dx = s(s-1)Λ(s)/2`. The proof is two integrations by parts
against `e^{(s-1/2)x}`, which reduce the transform to the Mellin transform of `θ(iy) - 1`, and then
analytic continuation from `re s > 1` to `ℂ \ {0, 1}`. The tail grows like `e^{-x/2}` at `-∞`,
because the cusp value `1` of `θ` is reflected into the mode `sinh(x/2)`; this growth is harmless
for `re s > 1`.

Consequently the transform of `Φ` vanishes at every nontrivial zero of `ζ`, on the critical line
or not (`riemannPhiTransform_eq_zero_of_nontrivial`): `Φ` lies in the radical of the Weil form,
unconditionally.
-/

open Complex MeasureTheory Filter Topology
open scoped Real
open Bottcher

namespace RHTower

noncomputable section

/-! ## The theta instance -/

theorem thetaGroupBasis_zero_eq : thetaGroupBasis 0 = thetaThree := by
  funext τ; simp [thetaGroupBasis]

theorem thetaThree_differentiableOn : DifferentiableOn ℂ thetaThree modUpperSet := by
  rw [← thetaGroupBasis_zero_eq]; exact differentiableOn_thetaGroupBasis 0

theorem thetaThree_axis (x : ℝ) :
    thetaThree (modAxisPoint (-x)) = (Real.exp x : ℂ) * thetaThree (modAxisPoint x) := by
  rw [← thetaGroupBasis_zero_eq]; exact thetaGroupBasis_axis 0 x

theorem thetaThree_cuspDecay (τ : ℂ) (hτ : 1 ≤ τ.im) :
    ‖thetaThree τ - 1‖ ≤ jacobiThetaTailConstant * Real.exp (-π * τ.im) :=
  norm_thetaThree_sub_one_le hτ

/-! ## Reflection of the tail with a nonzero cusp value -/

section Reflection

variable {F : ℂ → ℂ} (c : ℂ)

theorem modTailDeriv_neg (hF : DifferentiableOn ℂ F modUpperSet)
    (hS : ∀ x : ℝ, F (modAxisPoint (-x)) = (Real.exp x : ℂ) * F (modAxisPoint x)) (y : ℝ) :
    modTailDeriv F c (-y) = -modTailDeriv F c y - c * modReflectionModeDeriv y := by
  have hrefl : modTail F c ∘ Neg.neg = fun z => modTail F c z + c * modReflectionMode z := by
    funext z; exact modTail_neg c hS z
  have hl := (hasDerivAt_modTail c hF (-y)).scomp y (hasDerivAt_neg y)
  have hr := (hasDerivAt_modTail c hF y).add ((hasDerivAt_modReflectionMode y).const_mul c)
  rw [hrefl] at hl
  have := hl.unique hr
  simp only [neg_smul, one_smul] at this
  linear_combination -this

theorem modTailDeriv2_neg (hF : DifferentiableOn ℂ F modUpperSet)
    (hS : ∀ x : ℝ, F (modAxisPoint (-x)) = (Real.exp x : ℂ) * F (modAxisPoint x)) (y : ℝ) :
    modTailDeriv2 F c (-y) = modTailDeriv2 F c y + c * ((1 / 4 : ℂ) * modReflectionMode y) := by
  have hfirstFun : (fun z => -modTailDeriv F c (-z)) =
      fun z => modTailDeriv F c z + c * modReflectionModeDeriv z := by
    funext z; rw [modTailDeriv_neg c hF hS z]; ring
  have hl := ((hasDerivAt_modTailDeriv c hF (-y)).scomp y (hasDerivAt_neg y)).neg
  have hr := (hasDerivAt_modTailDeriv c hF y).add
    ((hasDerivAt_modReflectionModeDeriv y).const_mul c)
  have hl' : HasDerivAt (fun z => -modTailDeriv F c (-z)) (modTailDeriv2 F c (-y)) y := by
    have h0 := hl
    simp only [Function.comp_def, neg_smul, one_smul, neg_neg] at h0
    exact h0
  rw [hfirstFun] at hl'
  have := hl'.unique hr
  linear_combination this

end Reflection

/-! ## Growth of the tail and its derivatives for the theta function -/

section ThetaTail

local notation "Tθ" => modTail thetaThree 1
local notation "T'θ" => modTailDeriv thetaThree 1
local notation "T''θ" => modTailDeriv2 thetaThree 1
local notation "Mθ" => jacobiThetaTailConstant

theorem jacobiThetaTailConstant_nonneg : 0 ≤ Mθ :=
  cuspDecay_const_nonneg thetaThree_cuspDecay

theorem continuous_thetaTail : Continuous Tθ :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_modTail 1 thetaThree_differentiableOn x).continuousAt

theorem continuous_thetaTailDeriv : Continuous T'θ :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_modTailDeriv 1 thetaThree_differentiableOn x).continuousAt

theorem continuous_thetaTailDeriv2 : Continuous T''θ := by
  have h : T''θ = fun x => modSource thetaThree x + Tθ x / 4 := by
    funext x; rw [modSource_eq thetaThree 1 x]; ring
  rw [h]
  exact (continuous_modSource thetaThree_differentiableOn).add (continuous_thetaTail.div_const 4)

/-- Far-cusp bound: for `e^{2x} ≥ 3` the tail and its first two derivatives are dominated by
`K e^{x/2}(1 + y + y²)e^{-πy}`, `y = e^{2x}`. -/
theorem norm_thetaTail_derivs_le {x : ℝ} (hx : 3 ≤ Real.exp (2 * x)) :
    ‖Tθ x‖ ≤ 16 * Mθ * Real.exp π * Real.exp (x / 2) *
        (1 + Real.exp (2 * x) + Real.exp (2 * x) ^ 2) * Real.exp (-π * Real.exp (2 * x)) ∧
      ‖T'θ x‖ ≤ 16 * Mθ * Real.exp π * Real.exp (x / 2) *
        (1 + Real.exp (2 * x) + Real.exp (2 * x) ^ 2) * Real.exp (-π * Real.exp (2 * x)) ∧
      ‖T''θ x‖ ≤ 16 * Mθ * Real.exp π * Real.exp (x / 2) *
        (1 + Real.exp (2 * x) + Real.exp (2 * x) ^ 2) * Real.exp (-π * Real.exp (2 * x)) := by
  have hM := jacobiThetaTailConstant_nonneg
  set y := Real.exp (2 * x) with hy
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hpim : (modAxisPoint x).im = y := modAxisPoint_im x
  have hpn : ‖modAxisPoint x‖ = y := norm_modAxisPoint x
  have h0 : ‖thetaThree (modAxisPoint x) - 1‖ ≤ Mθ * Real.exp (-π * y) := by
    have := thetaThree_cuspDecay (modAxisPoint x) (by rw [hpim]; linarith)
    rwa [hpim] at this
  have h1 : ‖deriv thetaThree (modAxisPoint x)‖ ≤ 2 * Mθ * Real.exp (π / 2) * Real.exp (-π * y) := by
    have := norm_deriv_le_of_cuspDecay thetaThree_differentiableOn thetaThree_cuspDecay
      (τ := modAxisPoint x) (by rw [hpim]; linarith)
    rwa [hpim] at this
  have h2 : ‖deriv (deriv thetaThree) (modAxisPoint x)‖ ≤ 4 * Mθ * Real.exp π * Real.exp (-π * y) := by
    have := norm_deriv_deriv_le_of_cuspDecay thetaThree_differentiableOn thetaThree_cuspDecay
      (τ := modAxisPoint x) (by rw [hpim]; linarith)
    rwa [hpim] at this
  have hE : 0 ≤ Real.exp (-π * y) := (Real.exp_pos _).le
  have hepi : 1 ≤ Real.exp π := Real.one_le_exp (by linarith [Real.pi_pos])
  have hepi2 : Real.exp (π / 2) ≤ Real.exp π := Real.exp_le_exp.mpr (by linarith [Real.pi_pos])
  have hex : 0 < Real.exp (x / 2) := Real.exp_pos _
  have hexn : ‖(Real.exp (x / 2) : ℂ)‖ = Real.exp (x / 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hex]
  have hA : Mθ * Real.exp (-π * y) ≤ 16 * Mθ * Real.exp π * (1 + y + y ^ 2) * Real.exp (-π * y) := by
    have : 1 ≤ 16 * Real.exp π * (1 + y + y ^ 2) := by nlinarith
    nlinarith [mul_nonneg hM hE]
  refine ⟨?_, ?_, ?_⟩
  · unfold modTail
    rw [norm_div, norm_mul, hexn, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have := mul_le_mul_of_nonneg_left h0 hex.le
    nlinarith [mul_nonneg hex.le (mul_nonneg hM hE), mul_le_mul_of_nonneg_left hA hex.le]
  · unfold modTailDeriv
    rw [norm_div, norm_mul, hexn, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hin : ‖(thetaThree (modAxisPoint x) - 1) / 2 + 2 * modAxisPoint x *
        deriv thetaThree (modAxisPoint x)‖ ≤
        Mθ * Real.exp (-π * y) / 2 + 2 * y * (2 * Mθ * Real.exp (π / 2) * Real.exp (-π * y)) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_div, norm_mul, norm_mul, hpn, show ‖(2 : ℂ)‖ = 2 by norm_num]
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * y)
      nlinarith
    have hin2 : Mθ * Real.exp (-π * y) / 2 + 2 * y * (2 * Mθ * Real.exp (π / 2) * Real.exp (-π * y))
        ≤ 2 * (16 * Mθ * Real.exp π * (1 + y + y ^ 2) * Real.exp (-π * y)) := by
      have hMe : 0 ≤ Mθ * Real.exp (-π * y) := mul_nonneg hM hE
      have : Real.exp (π / 2) * (Mθ * Real.exp (-π * y)) ≤ Real.exp π * (Mθ * Real.exp (-π * y)) :=
        mul_le_mul_of_nonneg_right hepi2 hMe
      nlinarith [mul_le_mul_of_nonneg_left this hy0, mul_nonneg (mul_nonneg hy0 hy0) (mul_nonneg (by linarith : (0:ℝ) ≤ Real.exp π) hMe), mul_nonneg hy0 (mul_nonneg (by linarith : (0:ℝ) ≤ Real.exp π) hMe)]
    have := mul_le_mul_of_nonneg_left (hin.trans hin2) hex.le
    nlinarith
  · unfold modTailDeriv2
    rw [norm_div, norm_mul, hexn, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hin : ‖(thetaThree (modAxisPoint x) - 1) / 4 + 6 * modAxisPoint x *
        deriv thetaThree (modAxisPoint x) + 4 * modAxisPoint x ^ 2 *
        deriv (deriv thetaThree) (modAxisPoint x)‖ ≤
        Mθ * Real.exp (-π * y) / 4 + 6 * y * (2 * Mθ * Real.exp (π / 2) * Real.exp (-π * y)) +
          4 * y ^ 2 * (4 * Mθ * Real.exp π * Real.exp (-π * y)) := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [norm_div, show ‖(4 : ℂ)‖ = 4 by norm_num]; linarith
      · rw [norm_mul, norm_mul, hpn, show ‖(6 : ℂ)‖ = 6 by norm_num]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      · rw [norm_mul, norm_mul, norm_pow, hpn, show ‖(4 : ℂ)‖ = 4 by norm_num]
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have hin2 : Mθ * Real.exp (-π * y) / 4 + 6 * y * (2 * Mθ * Real.exp (π / 2) * Real.exp (-π * y)) +
          4 * y ^ 2 * (4 * Mθ * Real.exp π * Real.exp (-π * y))
        ≤ 2 * (16 * Mθ * Real.exp π * (1 + y + y ^ 2) * Real.exp (-π * y)) := by
      have hMe : 0 ≤ Mθ * Real.exp (-π * y) := mul_nonneg hM hE
      have : Real.exp (π / 2) * (Mθ * Real.exp (-π * y)) ≤ Real.exp π * (Mθ * Real.exp (-π * y)) :=
        mul_le_mul_of_nonneg_right hepi2 hMe
      nlinarith [mul_le_mul_of_nonneg_left this hy0,
        mul_nonneg (mul_nonneg hy0 hy0) (mul_nonneg (by linarith : (0:ℝ) ≤ Real.exp π) hMe),
        mul_nonneg hy0 (mul_nonneg (by linarith : (0:ℝ) ≤ Real.exp π) hMe)]
    have := mul_le_mul_of_nonneg_left (hin.trans hin2) hex.le
    nlinarith

/-- A continuous function obeying an exponential bound outside a compact interval obeys it
everywhere, with a larger constant. -/
theorem exists_global_exp_bound {g : ℝ → ℂ} (hg : Continuous g) {R C₁ δ : ℝ} (hδ : 0 ≤ δ)
    (hfar : ∀ x : ℝ, R ≤ |x| → ‖g x‖ ≤ C₁ * Real.exp (-δ * |x|)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖g x‖ ≤ C * Real.exp (-δ * |x|) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max (max C₁ 0) (max B 0 * Real.exp (δ * |R|)), by positivity, fun x => ?_⟩
  by_cases hx : R ≤ |x|
  · refine (hfar x hx).trans ?_
    exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (Real.exp_pos _).le
  · push Not at hx
    have hxI : x ∈ Set.Icc (-R) R := ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    have h1 : ‖g x‖ ≤ max B 0 := by
      have := hB x hxI
      exact this.trans (le_max_left _ _)
    have h2 : 1 ≤ Real.exp (δ * |R|) * Real.exp (-δ * |x|) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have : |x| ≤ |R| := by
        have := hx.le; have := le_abs_self R; linarith
      nlinarith
    calc ‖g x‖ ≤ max B 0 * 1 := by linarith
      _ ≤ max B 0 * (Real.exp (δ * |R|) * Real.exp (-δ * |x|)) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = (max B 0 * Real.exp (δ * |R|)) * Real.exp (-δ * |x|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- Super-exponential decay beats every exponential: for `x ≥ 0`,
`e^{bx}(1 + e^{2x} + e^{4x})e^{-πe^{2x}} ≤ C_b e^{-x}`. -/
theorem exists_superexp_le (b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
    Real.exp (b * x) * (1 + Real.exp (2 * x) + Real.exp (2 * x) ^ 2) *
      Real.exp (-π * Real.exp (2 * x)) ≤ C * Real.exp (-x) := by
  set N : ℕ := ⌈|b|⌉₊ with hN
  refine ⟨3 * ((N + 3).factorial : ℝ), by positivity, fun x hx => ?_⟩
  set y := Real.exp (2 * x) with hy
  have hy1 : 1 ≤ y := Real.one_le_exp (by linarith)
  have hbN : b * x + x ≤ 2 * ((N : ℝ) + 1) * x := by
    have : b ≤ (N : ℝ) := (le_abs_self b).trans (Nat.le_ceil _)
    nlinarith
  have hpow : Real.exp (b * x) * Real.exp x ≤ y ^ (N + 1) := by
    rw [← Real.exp_add, hy, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr; push_cast; linarith
  have hpoly : 1 + y + y ^ 2 ≤ 3 * y ^ 2 := by nlinarith
  have hfac : y ^ (N + 3) * Real.exp (-π * y) ≤ ((N + 3).factorial : ℝ) := by
    have h1 := Real.pow_div_factorial_le_exp (x := y) (by linarith) (N + 3)
    have hfpos : (0 : ℝ) < ((N + 3).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have h2 : y ^ (N + 3) ≤ ((N + 3).factorial : ℝ) * Real.exp y := by
      rw [div_le_iff₀ hfpos] at h1; linarith
    have h3 : Real.exp y * Real.exp (-π * y) ≤ 1 := by
      rw [← Real.exp_add]; apply Real.exp_le_one_iff.mpr; nlinarith [Real.pi_gt_three]
    calc y ^ (N + 3) * Real.exp (-π * y)
        ≤ ((N + 3).factorial : ℝ) * Real.exp y * Real.exp (-π * y) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = ((N + 3).factorial : ℝ) * (Real.exp y * Real.exp (-π * y)) := by ring
      _ ≤ ((N + 3).factorial : ℝ) * 1 := mul_le_mul_of_nonneg_left h3 hfpos.le
      _ = _ := by ring
  have hE := Real.exp_pos (-π * y)
  have hex := Real.exp_pos x
  have key : Real.exp (b * x) * (1 + y + y ^ 2) * Real.exp (-π * y) * Real.exp x ≤
      3 * ((N + 3).factorial : ℝ) := by
    calc Real.exp (b * x) * (1 + y + y ^ 2) * Real.exp (-π * y) * Real.exp x
        = (Real.exp (b * x) * Real.exp x) * (1 + y + y ^ 2) * Real.exp (-π * y) := by ring
      _ ≤ y ^ (N + 1) * (3 * y ^ 2) * Real.exp (-π * y) := by
          have h0 : 0 ≤ 1 + y + y ^ 2 := by positivity
          have := mul_le_mul hpow hpoly h0 (by positivity)
          exact mul_le_mul_of_nonneg_right this hE.le
      _ = 3 * (y ^ (N + 3) * Real.exp (-π * y)) := by ring
      _ ≤ 3 * ((N + 3).factorial : ℝ) := by linarith
  have hexinv : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp (b * x) * (1 + y + y ^ 2) * Real.exp (-π * y)
      = (Real.exp (b * x) * (1 + y + y ^ 2) * Real.exp (-π * y) * Real.exp x) * Real.exp (-x) := by
        have hc : Real.exp x * Real.exp (-x) = 1 := by rw [mul_comm]; exact hexinv
        rw [mul_assoc _ (Real.exp x), hc, mul_one]
    _ ≤ 3 * ((N + 3).factorial : ℝ) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right key (Real.exp_pos _).le

theorem norm_cexp_sub_half_mul (s : ℂ) (x : ℝ) :
    ‖Complex.exp ((s - 1 / 2) * x)‖ = Real.exp ((s.re - 1 / 2) * x) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]

/-- Weighted integrability bound for a tail-type function: continuity, far-cusp decay on the
right and reflection with an `e^{y/2}` defect on the left give a two-sided exponential bound for
`e^{(s-1/2)x}U(x)` whenever `re s > 1`. -/
theorem exists_weighted_bound_of_tail {U : ℝ → ℂ} (hU : Continuous U) {K : ℝ} (hK : 0 ≤ K)
    (hfar : ∀ x : ℝ, 3 ≤ Real.exp (2 * x) → ‖U x‖ ≤ K * Real.exp (x / 2) *
      (1 + Real.exp (2 * x) + Real.exp (2 * x) ^ 2) * Real.exp (-π * Real.exp (2 * x)))
    (hrefl : ∀ y : ℝ, 0 ≤ y → ‖U (-y)‖ ≤ ‖U y‖ + Real.exp (y / 2))
    {s : ℂ} (hs : 1 < s.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖Complex.exp ((s - 1 / 2) * x) * U x‖ ≤ C * Real.exp (-(min 1 (s.re - 1)) * |x|) := by
  set δ := min 1 (s.re - 1) with hδ
  have hδ0 : 0 ≤ δ := le_min zero_le_one (by linarith)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδσ : δ ≤ s.re - 1 := min_le_right _ _
  set x₀ : ℝ := Real.log 3 / 2 with hx₀
  have hx₀pos : 0 ≤ x₀ := by
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num); linarith
  have he3 : Real.exp (2 * x₀) = 3 := by
    rw [hx₀, show 2 * (Real.log 3 / 2) = Real.log 3 by ring, Real.exp_log (by norm_num)]
  obtain ⟨Cσ, hCσ0, hCσ⟩ := exists_superexp_le s.re
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_superexp_le 0
  refine exists_global_exp_bound ((by fun_prop : Continuous fun x : ℝ =>
    Complex.exp ((s - 1 / 2) * x)).mul hU) (R := x₀) (C₁ := K * Cσ + (K * C₀ + 1)) hδ0 ?_
  intro x hx
  simp only [Pi.mul_apply]
  rw [norm_mul, norm_cexp_sub_half_mul]
  rcases le_or_gt 0 x with hx0 | hx0
  · -- right side
    have hxx : x₀ ≤ x := by rwa [abs_of_nonneg hx0] at hx
    have hy3 : 3 ≤ Real.exp (2 * x) := by rw [← he3]; exact Real.exp_le_exp.mpr (by linarith)
    have h1 := hfar x hy3
    have h2 := hCσ x hx0
    have hEq : Real.exp ((s.re - 1 / 2) * x) * Real.exp (x / 2) = Real.exp (s.re * x) := by
      rw [← Real.exp_add]; congr 1; ring
    have hdec : Real.exp (-x) ≤ Real.exp (-δ * |x|) := by
      rw [abs_of_nonneg hx0]; apply Real.exp_le_exp.mpr; nlinarith
    calc Real.exp ((s.re - 1 / 2) * x) * ‖U x‖
        ≤ Real.exp ((s.re - 1 / 2) * x) * (K * Real.exp (x / 2) *
            (1 + Real.exp (2 * x) + Real.exp (2 * x) ^ 2) * Real.exp (-π * Real.exp (2 * x))) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = K * (Real.exp (s.re * x) * (1 + Real.exp (2 * x) + Real.exp (2 * x) ^ 2) *
            Real.exp (-π * Real.exp (2 * x))) := by rw [← hEq]; ring
      _ ≤ K * (Cσ * Real.exp (-x)) := mul_le_mul_of_nonneg_left h2 hK
      _ ≤ K * (Cσ * Real.exp (-δ * |x|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdec hCσ0) hK
      _ ≤ (K * Cσ + (K * C₀ + 1)) * Real.exp (-δ * |x|) := by
          have : 0 ≤ (K * C₀ + 1) * Real.exp (-δ * |x|) := by positivity
          nlinarith
  · -- left side, by reflection
    set y := -x with hy
    have hy0 : 0 ≤ y := by linarith
    have hyy : x₀ ≤ y := by rwa [abs_of_neg hx0] at hx
    have hy3 : 3 ≤ Real.exp (2 * y) := by rw [← he3]; exact Real.exp_le_exp.mpr (by linarith)
    have hxy : x = -y := by rw [hy]; ring
    have h1 := hrefl y hy0
    have h2 := hfar y hy3
    have h3 := hC₀ y hy0
    have hpoly : (1 + Real.exp (2 * y) + Real.exp (2 * y) ^ 2) * Real.exp (-π * Real.exp (2 * y))
        ≤ C₀ := by
      have hm := Real.exp_le_one_iff.mpr (by linarith : -y ≤ 0)
      simp only [zero_mul, Real.exp_zero, one_mul] at h3
      nlinarith
    have hUy : ‖U y‖ ≤ K * C₀ * Real.exp (y / 2) := by
      calc ‖U y‖ ≤ K * Real.exp (y / 2) * ((1 + Real.exp (2 * y) + Real.exp (2 * y) ^ 2) *
            Real.exp (-π * Real.exp (2 * y))) := by rw [← mul_assoc]; exact h2
        _ ≤ K * Real.exp (y / 2) * C₀ := mul_le_mul_of_nonneg_left hpoly (by positivity)
        _ = K * C₀ * Real.exp (y / 2) := by ring
    have hUx : ‖U x‖ ≤ (K * C₀ + 1) * Real.exp (y / 2) := by
      rw [hxy]; linarith
    have hw : Real.exp ((s.re - 1 / 2) * x) * Real.exp (y / 2) = Real.exp (-(s.re - 1) * y) := by
      rw [← Real.exp_add, hxy]; congr 1; ring
    have hdec : Real.exp (-(s.re - 1) * y) ≤ Real.exp (-δ * |x|) := by
      rw [abs_of_neg hx0, ← hy]; apply Real.exp_le_exp.mpr; nlinarith
    calc Real.exp ((s.re - 1 / 2) * x) * ‖U x‖
        ≤ Real.exp ((s.re - 1 / 2) * x) * ((K * C₀ + 1) * Real.exp (y / 2)) :=
          mul_le_mul_of_nonneg_left hUx (Real.exp_pos _).le
      _ = (K * C₀ + 1) * Real.exp (-(s.re - 1) * y) := by rw [← hw]; ring
      _ ≤ (K * C₀ + 1) * Real.exp (-δ * |x|) :=
          mul_le_mul_of_nonneg_left hdec (by positivity)
      _ ≤ (K * Cσ + (K * C₀ + 1)) * Real.exp (-δ * |x|) := by
          have : 0 ≤ K * Cσ * Real.exp (-δ * |x|) := by positivity
          nlinarith

theorem norm_modReflectionMode_le {y : ℝ} (hy : 0 ≤ y) :
    ‖modReflectionMode y‖ ≤ Real.exp (y / 2) := by
  unfold modReflectionMode
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 : Real.exp (-y / 2) ≤ Real.exp (y / 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 := Real.exp_pos (-y / 2)
  rw [abs_le]; constructor <;> linarith

theorem norm_modReflectionModeDeriv_le {y : ℝ} (hy : 0 ≤ y) :
    ‖modReflectionModeDeriv y‖ ≤ Real.exp (y / 2) := by
  unfold modReflectionModeDeriv
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 : Real.exp (-y / 2) ≤ Real.exp (y / 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 := Real.exp_pos (-y / 2)
  have h3 := Real.exp_pos (y / 2)
  rw [abs_le]; constructor <;> linarith

theorem thetaTail_refl_le {y : ℝ} (hy : 0 ≤ y) : ‖Tθ (-y)‖ ≤ ‖Tθ y‖ + Real.exp (y / 2) := by
  rw [modTail_neg 1 thetaThree_axis y, one_mul]
  exact (norm_add_le _ _).trans (add_le_add_right (norm_modReflectionMode_le hy) _)

theorem thetaTailDeriv_refl_le {y : ℝ} (hy : 0 ≤ y) :
    ‖T'θ (-y)‖ ≤ ‖T'θ y‖ + Real.exp (y / 2) := by
  rw [modTailDeriv_neg 1 thetaThree_differentiableOn thetaThree_axis y, one_mul]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg]; exact add_le_add_right (norm_modReflectionModeDeriv_le hy) _

theorem thetaTailDeriv2_refl_le {y : ℝ} (hy : 0 ≤ y) :
    ‖T''θ (-y)‖ ≤ ‖T''θ y‖ + Real.exp (y / 2) := by
  rw [modTailDeriv2_neg 1 thetaThree_differentiableOn thetaThree_axis y, one_mul]
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  rw [norm_mul, show ‖(1 / 4 : ℂ)‖ = 1 / 4 by norm_num]
  have := norm_modReflectionMode_le hy
  have := Real.exp_pos (y / 2)
  linarith

theorem integrable_weighted_thetaTail {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun x : ℝ => Complex.exp ((s - 1 / 2) * x) * Tθ x) ∧
      Integrable (fun x : ℝ => Complex.exp ((s - 1 / 2) * x) * T'θ x) ∧
      Integrable (fun x : ℝ => Complex.exp ((s - 1 / 2) * x) * T''θ x) := by
  have hK : 0 ≤ 16 * Mθ * Real.exp π := by
    have := jacobiThetaTailConstant_nonneg; positivity
  have hδ : 0 < min 1 (s.re - 1) := lt_min one_pos (by linarith)
  have hint := integrable_exp_neg_mul_abs_modSource hδ
  have mk : ∀ {U : ℝ → ℂ}, Continuous U →
      (∀ x : ℝ, 3 ≤ Real.exp (2 * x) → ‖U x‖ ≤ 16 * Mθ * Real.exp π * Real.exp (x / 2) *
        (1 + Real.exp (2 * x) + Real.exp (2 * x) ^ 2) * Real.exp (-π * Real.exp (2 * x))) →
      (∀ y : ℝ, 0 ≤ y → ‖U (-y)‖ ≤ ‖U y‖ + Real.exp (y / 2)) →
      Integrable (fun x : ℝ => Complex.exp ((s - 1 / 2) * x) * U x) := by
    intro U hU hfar hrefl
    obtain ⟨C, -, hC⟩ := exists_weighted_bound_of_tail hU hK hfar hrefl hs
    refine Integrable.mono' (hint.const_mul C) (by fun_prop) (Eventually.of_forall fun x => ?_)
    have := hC x
    simpa [neg_mul] using this
  exact ⟨mk continuous_thetaTail (fun x hx => (norm_thetaTail_derivs_le hx).1)
      (fun y hy => thetaTail_refl_le hy),
    mk continuous_thetaTailDeriv (fun x hx => (norm_thetaTail_derivs_le hx).2.1)
      (fun y hy => thetaTailDeriv_refl_le hy),
    mk continuous_thetaTailDeriv2 (fun x hx => (norm_thetaTail_derivs_le hx).2.2)
      (fun y hy => thetaTailDeriv2_refl_le hy)⟩

/-- **Two integrations by parts** for the theta tail: for `re s > 1`,
`∫ e^{(s-1/2)x}(T'' - T/4) = s(s-1) ∫ e^{(s-1/2)x} T`. -/
theorem integral_weighted_modSource_theta {s : ℂ} (hs : 1 < s.re) :
    ∫ x : ℝ, Complex.exp ((s - 1 / 2) * x) * modSource thetaThree x =
      s * (s - 1) * ∫ x : ℝ, Complex.exp ((s - 1 / 2) * x) * Tθ x := by
  obtain ⟨i0, i1, i2⟩ := integrable_weighted_thetaTail hs
  set e : ℝ → ℂ := fun x => Complex.exp ((s - 1 / 2) * x) with he
  have hde : ∀ x : ℝ, HasDerivAt e ((s - 1 / 2) * e x) x := by
    intro x
    have h := ((hasDerivAt_id (x : ℂ)).const_mul (s - 1 / 2)).cexp
    have h2 := h.comp_ofReal
    simp only [he]
    convert h2 using 1
    · funext y; simp
    · simp; ring
  have ibp1 : ∫ x : ℝ, e x * T''θ x = -∫ x : ℝ, ((s - 1 / 2) * e x) * T'θ x := by
    refine integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hde x)
      (fun x _ => hasDerivAt_modTailDeriv 1 thetaThree_differentiableOn x) i2 ?_ i1
    exact (i1.const_mul (s - 1 / 2)).congr (Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, he]; ring)
  have ibp2 : ∫ x : ℝ, e x * T'θ x = -∫ x : ℝ, ((s - 1 / 2) * e x) * Tθ x := by
    refine integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hde x)
      (fun x _ => hasDerivAt_modTail 1 thetaThree_differentiableOn x) i1 ?_ i0
    exact (i0.const_mul (s - 1 / 2)).congr (Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, he]; ring)
  have hpull : ∀ g : ℝ → ℂ, ∫ x : ℝ, ((s - 1 / 2) * e x) * g x =
      (s - 1 / 2) * ∫ x : ℝ, e x * g x := by
    intro g
    rw [← integral_const_mul]; congr 1; funext x; ring
  have hI2 : ∫ x : ℝ, e x * T''θ x = (s - 1 / 2) ^ 2 * ∫ x : ℝ, e x * Tθ x := by
    rw [ibp1, hpull, ibp2, hpull]; ring
  have hsplit : (fun x : ℝ => e x * modSource thetaThree x) =
      fun x => e x * T''θ x - (1 / 4 : ℂ) * (e x * Tθ x) := by
    funext x; rw [modSource_eq thetaThree 1 x]; ring
  change ∫ x : ℝ, e x * modSource thetaThree x = s * (s - 1) * ∫ x : ℝ, e x * Tθ x
  rw [hsplit, integral_sub i2 (i0.const_mul _), integral_const_mul, hI2]
  ring

theorem ofReal_rexp_cpow_mul (r : ℝ) (z : ℂ) : ((Real.exp r : ℝ) : ℂ) ^ z = Complex.exp (r * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos r).ne'),
    ← Complex.ofReal_log (Real.exp_pos r).le, Real.log_exp]

theorem evenKernel_zero_eq (y : ℝ) :
    ((HurwitzZeta.evenKernel 0 y : ℝ) : ℂ) = thetaThree (I * y) := by
  have h := HurwitzZeta.evenKernel_def 0 y
  simp only [QuotientAddGroup.mk_zero, Complex.ofReal_zero, zero_mul, mul_zero,
    zero_pow two_ne_zero, Complex.exp_zero, one_mul] at h
  simpa [thetaThree] using h

/-- Change of variables `y = e^{2x}` in a Mellin transform. -/
theorem mellin_eq_integral_exp_two (G : ℝ → ℂ) (t : ℂ) :
    mellin G t = 2 * ∫ x : ℝ, Complex.exp (2 * t * x) * G (Real.exp (2 * x)) := by
  have himage : (fun x : ℝ => Real.exp (2 * x)) '' Set.univ = Set.Ioi 0 := by
    ext y; constructor
    · rintro ⟨x, -, rfl⟩; exact Real.exp_pos _
    · intro hy
      refine ⟨Real.log y / 2, trivial, ?_⟩
      simp only
      rw [show 2 * (Real.log y / 2) = Real.log y by ring, Real.exp_log hy]
  have hder : ∀ x ∈ (Set.univ : Set ℝ), HasDerivWithinAt (fun x : ℝ => Real.exp (2 * x))
      (2 * Real.exp (2 * x)) Set.univ x := by
    intro x _
    have h := ((hasDerivAt_id' x).const_mul (2 : ℝ)).exp
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (2 * x)) (2 * Real.exp (2 * x)) x := by
      convert h using 1; ring
    exact h2.hasDerivWithinAt
  have hinj : Set.InjOn (fun x : ℝ => Real.exp (2 * x)) Set.univ := by
    intro a _ b _ hab
    have := Real.exp_injective hab
    linarith
  have hcv := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hder hinj
    (fun y : ℝ => (y : ℂ) ^ (t - 1) • G y)
  rw [himage, Measure.restrict_univ] at hcv
  unfold mellin
  rw [hcv, ← integral_const_mul]
  congr 1
  funext x
  rw [abs_of_pos (by positivity : (0:ℝ) < 2 * Real.exp (2 * x)), ofReal_rexp_cpow_mul, smul_eq_mul,
    Complex.real_smul]
  push_cast
  rw [show (2 : ℂ) * Complex.exp (2 * (x : ℂ)) * (Complex.exp ((2 * (x : ℂ)) * (t - 1)) *
      G (Real.exp (2 * x))) = 2 * (Complex.exp (2 * (x : ℂ) + (2 * (x : ℂ)) * (t - 1)) *
      G (Real.exp (2 * x))) by rw [Complex.exp_add]; ring]
  congr 3; ring

/-- **The theta tail is the completed zeta function**: for `re s > 1`,
`∫ e^{(s-1/2)x} T(x) dx = Λ(s)/2` with `T(x) = e^{x/2}(θ(ie^{2x}) - 1)/2`. -/
theorem integral_weighted_thetaTail_eq {s : ℂ} (hs : 1 < s.re) :
    ∫ x : ℝ, Complex.exp ((s - 1 / 2) * x) * Tθ x = completedRiemannZeta s / 2 := by
  set G : ℝ → ℂ := fun y => (HurwitzZeta.hurwitzEvenFEPair 0).f y -
    (HurwitzZeta.hurwitzEvenFEPair 0).f₀ with hG
  have hk : (HurwitzZeta.hurwitzEvenFEPair 0).k < (s / 2).re := by
    change (1 / 2 : ℝ) < (s / 2).re
    rw [Complex.div_re]; norm_num; linarith
  have hM := (HurwitzZeta.hurwitzEvenFEPair 0).hasMellin hk
  have hmel : mellin G (s / 2) = 2 * completedRiemannZeta s := by
    rw [hM.2, ← HurwitzZeta.completedHurwitzZetaEven_zero]
    change _ = 2 * ((HurwitzZeta.hurwitzEvenFEPair 0).Λ (s / 2) / 2)
    ring
  rw [mellin_eq_integral_exp_two G (s / 2)] at hmel
  have hpt : ∀ x : ℝ, Complex.exp ((s - 1 / 2) * x) * Tθ x =
      (1 / 2 : ℂ) * (Complex.exp (2 * (s / 2) * x) * G (Real.exp (2 * x))) := by
    intro x
    have hG' : G (Real.exp (2 * x)) = thetaThree (modAxisPoint x) - 1 := by
      simp only [hG, HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, if_true]
      rw [evenKernel_zero_eq, modAxisPoint]
    rw [hG']
    unfold modTail
    rw [Complex.ofReal_exp]
    have he : Complex.exp ((s - 1 / 2) * x) * Complex.exp ((x : ℂ) / 2) =
        Complex.exp (2 * (s / 2) * x) := by
      rw [← Complex.exp_add]; congr 1; ring
    push_cast
    linear_combination ((thetaThree (modAxisPoint x) - 1) / 2) * he
  simp_rw [hpt]
  rw [integral_const_mul]
  linear_combination (1 / 4 : ℂ) * hmel

end ThetaTail

/-! ## Riemann's kernel lies in the radical of the Weil form -/

/-- Riemann's kernel `Φ = T'' - T/4` of the theta function, `ξ(s) = ∫ Φ(x) e^{(s-1/2)x} dx`. -/
def riemannPhiKernel : ℝ → ℂ := modSource thetaThree

/-- The two-sided Laplace transform `s ↦ ∫ Φ(x) e^{(s-1/2)x} dx`. -/
def riemannPhiTransform (s : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp ((s - 1 / 2) * x) * riemannPhiKernel x

theorem riemannPhiTransform_eq_modXi (s : ℂ) :
    riemannPhiTransform s = modXi thetaThree (I * (s - 1 / 2)) := by
  unfold riemannPhiTransform modXi modXiIntegrand riemannPhiKernel
  congr 1; funext x
  congr 2
  ring_nf; rw [Complex.I_sq]; ring

theorem differentiable_riemannPhiTransform : Differentiable ℂ riemannPhiTransform := by
  have h := differentiable_modXi (c := 1) (M := jacobiThetaTailConstant)
    thetaThree_differentiableOn thetaThree_axis thetaThree_cuspDecay
  have : riemannPhiTransform = fun s => modXi thetaThree (I * (s - 1 / 2)) :=
    funext riemannPhiTransform_eq_modXi
  rw [this]
  exact h.comp ((differentiable_id.sub_const _).const_mul I)

theorem riemannPhiTransform_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannPhiTransform s = s * (s - 1) / 2 * completedRiemannZeta s := by
  unfold riemannPhiTransform riemannPhiKernel
  rw [integral_weighted_modSource_theta hs, integral_weighted_thetaTail_eq hs]
  ring

/-- `∫ Φ(x)e^{(s-1/2)x}dx = s(s-1)Λ(s)/2` away from the poles of `Λ` (analytic continuation). -/
theorem riemannPhiTransform_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannPhiTransform s = s * (s - 1) / 2 * completedRiemannZeta s := by
  set U : Set ℂ := ({0, 1} : Set ℂ)ᶜ with hU
  have hUo : IsOpen U := (Set.Finite.isClosed (by simp)).isOpen_compl
  have hUc : IsPreconnected U := by
    have h := (Set.Countable.isConnected_compl_of_one_lt_rank (E := ℂ)
      (by rw [Complex.rank_real_complex]; norm_num) (s := ({0, 1} : Set ℂ)) (by simp))
    exact h.isPreconnected
  have hf : AnalyticOnNhd ℂ riemannPhiTransform U :=
    (differentiable_riemannPhiTransform.differentiableOn).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => s * (s - 1) / 2 * completedRiemannZeta s) U := by
    apply DifferentiableOn.analyticOnNhd _ hUo
    intro z hz
    have hz0 : z ≠ 0 := fun h => hz (by simp [h])
    have hz1 : z ≠ 1 := fun h => hz (by simp [h])
    exact ((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s * (s - 1) / 2) z).mul
      (differentiableAt_completedZeta hz0 hz1)).differentiableWithinAt
  have h2U : (2 : ℂ) ∈ U := by simp [hU]
  have hev : riemannPhiTransform =ᶠ[𝓝 (2 : ℂ)]
      fun s : ℂ => s * (s - 1) / 2 * completedRiemannZeta s := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with s hs
    exact riemannPhiTransform_eq_of_one_lt_re hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h2U hev (by simp [hU, hs0, hs1])

/-- **Radical property**: the transform of Riemann's kernel vanishes at every nontrivial zero,
on or off the critical line. -/
theorem riemannPhiTransform_eq_zero_of_nontrivial {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1) : riemannPhiTransform ρ = 0 := by
  have hρ0 : ρ ≠ 0 := fun h => by simp [h] at hre0
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at hre1
  rw [riemannPhiTransform_eq hρ0 hρ1]
  have hΛ : completedRiemannZeta ρ = 0 := by
    have h := riemannZeta_def_of_ne_zero hρ0
    rw [hζ] at h
    have hG := Gammaℝ_ne_zero_of_re_pos hre0
    exact (div_eq_zero_iff.mp h.symm).resolve_right hG
  rw [hΛ, mul_zero]

theorem riemannPhiTransform_two_ne_zero : riemannPhiTransform 2 ≠ 0 := by
  rw [riemannPhiTransform_eq_of_one_lt_re (by norm_num)]
  have h := riemannZeta_def_of_ne_zero (s := 2) two_ne_zero
  rw [riemannZeta_two] at h
  have hG : Complex.Gammaℝ 2 ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hΛ : completedRiemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6 * Complex.Gammaℝ 2 := by
    rw [h, div_mul_cancel₀ _ hG]
  rw [hΛ]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  norm_num
  exact hG

/-- The Zeta23 transform of Riemann's kernel is the Laplace transform at `s = 1/2 + iz`. -/
theorem paperFT_riemannPhiKernel (z : ℂ) :
    Zeta23.paperFT riemannPhiKernel z = riemannPhiTransform (1 / 2 + I * z) := by
  unfold Zeta23.paperFT riemannPhiTransform
  congr 1; funext x
  rw [mul_comm]; congr 2; ring

end

end RHTower
