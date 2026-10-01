import GaloisForLFunctions.RHTower.HorizontalTradeoffHyperbolicBounds
import Zeta23.ThmD.ParamsD

/-!
# The overlap deficit of the Montgomery–Taylor window

For a window `φ` on `[−L/2, L/2]` with `φ² ≤ 1`, `φ(u)² ≤ cos(2θu/L)` and `φ² ≥ cos θ` on
`|u| ≤ L/2 − w` (`0 < θ`, `θ² ≤ 1/2`), every `ε > 0` and `24 w e²⁵ ≤ L`,

`1 − 2J²/(I₀I₂) ≤ εL/24 + 2w/L`   (`window_deficit_le`),

with `I₀ = ∫φ²`, `J = ∫φ² cosh(εu)`, `I₂ = ∫φ² cosh²(εu)`.

Proof.
* Weight comparison (`window_weight_comparison`).  With `a = L/2 − w`, `A₁ = ∫_{−a}^{a} cosh(εu)`
  and `A₂ = ∫_{−a}^{a} cosh²(εu)`, write `J = cos θ·A₁ + D₁` and `I₂ = cos θ·A₂ + D₂`.  Pointwise,
  `D₁ ≥ 0` and `D₂ ≤ cosh(εL/2)·D₁`.  So `J²A₂ ≥ cos θ·A₁²·I₂` as soon as
  `cosh(εL/2)·A₁ ≤ 2A₂`.  This side condition holds for `εL < 24` once `24 w e²⁵ ≤ L`
  (`sinh_mul_cosh_add_sub_le`).
* Hence `2J²/(I₀I₂) ≥ (θ cos θ/sin θ)·16 sinh²(y/2)/(x(y + sinh y))` with `x = εL`, `y = x − 2εw`,
  using `I₀ ≤ L sin θ/θ`.  The window constant is `≥ 4/5` (`window_constant_four_fifths`), and
  `(64/5) sinh²(y/2) ≥ (1 − y/24) y(y + sinh y)` (`deficit_sharp`).

The Montgomery–Taylor window `φ_D = √(cos(√2λu/L)) · taper` satisfies the hypotheses with
`θ = √2λ/2` (`phiD_window_deficit_le`).
-/

open Real MeasureTheory

namespace RHTower

noncomputable section

/-- `∫_{−L/2}^{L/2} cos(2θu/L) du = L sin θ/θ`. -/
theorem integral_cos_window {θ L : ℝ} (hθ : 0 < θ) (hL : 0 < L) :
    ∫ u in (-(L / 2))..(L / 2), Real.cos (2 * θ * u / L) = L * Real.sin θ / θ := by
  have hd : ∀ u ∈ Set.uIcc (-(L / 2)) (L / 2),
      HasDerivAt (fun u => L / (2 * θ) * Real.sin (2 * θ * u / L)) (Real.cos (2 * θ * u / L)) u := by
    intro u _
    have h : HasDerivAt (fun u => 2 * θ * u / L) (2 * θ * 1 / L) u :=
      ((hasDerivAt_id' u).const_mul (2 * θ)).div_const L
    exact (h.sin.const_mul (L / (2 * θ))).congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun u => Real.cos (2 * θ * u / L)).intervalIntegrable _ _)]
  have e1 : 2 * θ * (L / 2) / L = θ := by field_simp
  have e2 : 2 * θ * -(L / 2) / L = -θ := by field_simp
  simp only [e1, e2, Real.sin_neg]
  field_simp
  ring

/-- `∫_{−L/2}^{L/2} cosh²(εu) du = L/2 + sinh(εL)/(2ε)`. -/
theorem integral_cosh_sq_window {ε L : ℝ} (hε : 0 < ε) :
    ∫ u in (-(L / 2))..(L / 2), Real.cosh (ε * u) ^ 2 = L / 2 + Real.sinh (ε * L) / (2 * ε) := by
  have hd : ∀ u ∈ Set.uIcc (-(L / 2)) (L / 2),
      HasDerivAt (fun u => u / 2 + Real.sinh (2 * ε * u) / (4 * ε)) (Real.cosh (ε * u) ^ 2) u := by
    intro u _
    have h : HasDerivAt (fun u => 2 * ε * u) (2 * ε * 1) u := (hasDerivAt_id' u).const_mul (2 * ε)
    have h2 := ((hasDerivAt_id' u).div_const 2).add (h.sinh.div_const (4 * ε))
    refine h2.congr_deriv ?_
    have hc : Real.cosh (2 * ε * u) = 2 * Real.cosh (ε * u) ^ 2 - 1 := by
      rw [show 2 * ε * u = 2 * (ε * u) by ring, Real.cosh_two_mul, Real.sinh_sq]; ring
    rw [hc]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun u => Real.cosh (ε * u) ^ 2).intervalIntegrable _ _)]
  have e1 : 2 * ε * (L / 2) = ε * L := by ring
  have e2 : 2 * ε * -(L / 2) = -(ε * L) := by ring
  rw [e1, e2, Real.sinh_neg]
  field_simp
  ring

/-- `∫_{−a}^{a} cosh(εu) du = 2 sinh(εa)/ε`. -/
theorem integral_cosh_symm {ε a : ℝ} (hε : 0 < ε) :
    ∫ u in (-a)..a, Real.cosh (ε * u) = 2 * Real.sinh (ε * a) / ε := by
  have hd : ∀ u ∈ Set.uIcc (-a) a,
      HasDerivAt (fun u => Real.sinh (ε * u) / ε) (Real.cosh (ε * u)) u := by
    intro u _
    have h : HasDerivAt (fun u => ε * u) (ε * 1) u := (hasDerivAt_id' u).const_mul ε
    exact (h.sinh.div_const ε).congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun u => Real.cosh (ε * u)).intervalIntegrable _ _)]
  rw [show ε * -a = -(ε * a) by ring, Real.sinh_neg]
  ring

/-- A nonnegative integrand has a larger integral over a larger symmetric interval. -/
theorem integral_symm_le_of_nonneg {g : ℝ → ℝ} (hg : Continuous g) (hpos : ∀ u, 0 ≤ g u)
    {a b : ℝ} (hab : a ≤ b) :
    ∫ u in (-a)..a, g u ≤ ∫ u in (-b)..b, g u := by
  have hi : ∀ p q : ℝ, IntervalIntegrable g volume p q := fun p q => hg.intervalIntegrable p q
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-b) (-a)) (hi (-a) b),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-a) a) (hi a b)]
  have h1 : 0 ≤ ∫ u in (-b)..(-a), g u :=
    intervalIntegral.integral_nonneg (by linarith) fun u _ => hpos u
  have h2 : 0 ≤ ∫ u in a..b, g u := intervalIntegral.integral_nonneg hab fun u _ => hpos u
  linarith

/-- **Window integrals.**  `I₀ ≤ L sin θ/θ`, `I₂ ≤ L/2 + sinh(εL)/(2ε)`, and `I₀, I₂ > 0`. -/
theorem window_integral_bounds {φ : ℝ → ℝ} {L w θ ε : ℝ} (hφ : Continuous φ) (hL : 0 < L)
    (hw : 0 ≤ w) (hLw : 2 * w < L) (hθ : 0 < θ) (hcosθ : 0 < Real.cos θ) (hε : 0 < ε)
    (hup : ∀ u, |u| ≤ L / 2 → φ u ^ 2 ≤ Real.cos (2 * θ * u / L))
    (hle1 : ∀ u, φ u ^ 2 ≤ 1)
    (hlow : ∀ u, |u| ≤ L / 2 - w → Real.cos θ ≤ φ u ^ 2) :
    (∫ u in (-(L / 2))..(L / 2), φ u ^ 2) ≤ L * Real.sin θ / θ ∧
      (∫ u in (-(L / 2))..(L / 2), (φ u * Real.cosh (ε * u)) ^ 2)
        ≤ L / 2 + Real.sinh (ε * L) / (2 * ε) ∧
      0 < (∫ u in (-(L / 2))..(L / 2), φ u ^ 2) ∧
      0 < ∫ u in (-(L / 2))..(L / 2), (φ u * Real.cosh (ε * u)) ^ 2 := by
  set a := L / 2 - w with ha
  have ha0 : 0 < a := by linarith
  have haL : a ≤ L / 2 := by linarith
  have hI₀up : (∫ u in (-(L / 2))..(L / 2), φ u ^ 2) ≤ L * Real.sin θ / θ := by
    rw [← integral_cos_window hθ hL]
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (by fun_prop : Continuous fun u => φ u ^ 2).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun u => Real.cos (2 * θ * u / L)).intervalIntegrable _ _
    intro u hu
    exact hup u (abs_le.mpr ⟨hu.1, hu.2⟩)
  have hI₂up : (∫ u in (-(L / 2))..(L / 2), (φ u * Real.cosh (ε * u)) ^ 2)
      ≤ L / 2 + Real.sinh (ε * L) / (2 * ε) := by
    rw [← integral_cosh_sq_window hε]
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (by fun_prop : Continuous fun u => (φ u * Real.cosh (ε * u)) ^ 2).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun u => Real.cosh (ε * u) ^ 2).intervalIntegrable _ _
    intro u _
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) (hle1 u)
  have hI₀pos : 0 < ∫ u in (-(L / 2))..(L / 2), φ u ^ 2 := by
    have h1 := integral_symm_le_of_nonneg (g := fun u => φ u ^ 2) (by fun_prop)
      (fun u => sq_nonneg _) haL
    have h2 : ∫ u in (-a)..a, Real.cos θ ≤ ∫ u in (-a)..a, φ u ^ 2 := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact intervalIntegrable_const
      · exact (by fun_prop : Continuous fun u => φ u ^ 2).intervalIntegrable _ _
      intro u hu
      exact hlow u (abs_le.mpr ⟨hu.1, hu.2⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h2
    have : 0 < (a - -a) * Real.cos θ := mul_pos (by linarith) hcosθ
    linarith
  have hI₂pos : 0 < ∫ u in (-(L / 2))..(L / 2), (φ u * Real.cosh (ε * u)) ^ 2 := by
    have h : (∫ u in (-(L / 2))..(L / 2), φ u ^ 2)
        ≤ ∫ u in (-(L / 2))..(L / 2), (φ u * Real.cosh (ε * u)) ^ 2 := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (by fun_prop : Continuous fun u => φ u ^ 2).intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun u => (φ u * Real.cosh (ε * u)) ^ 2).intervalIntegrable _ _
      intro u _
      have h1 : 1 ≤ Real.cosh (ε * u) ^ 2 := by nlinarith [Real.one_le_cosh (ε * u)]
      rw [mul_pow]
      nlinarith [sq_nonneg (φ u)]
    linarith
  exact ⟨hI₀up, hI₂up, hI₀pos, hI₂pos⟩

/-- **Weight comparison.**  If `φ² ≥ m ≥ 0` on `[−a, a] ⊆ [−L/2, L/2]` and
`cosh(εL/2)·A₁ ≤ 2A₂` for the flat integrals `A₁ = 2 sinh(εa)/ε`, `A₂ = a + sinh(2εa)/(2ε)`, then
`m A₁² I₂ ≤ J² A₂`. -/
theorem window_weight_comparison {φ : ℝ → ℝ} {L a m ε : ℝ} (hφ : Continuous φ) (ha : 0 < a)
    (haL : a ≤ L / 2) (hm : 0 ≤ m) (hε : 0 < ε) (hlow : ∀ u, |u| ≤ a → m ≤ φ u ^ 2)
    (hcond : Real.cosh (ε * (L / 2)) * (2 * Real.sinh (ε * a) / ε)
      ≤ 2 * (a + Real.sinh (ε * (2 * a)) / (2 * ε))) :
    m * (2 * Real.sinh (ε * a) / ε) ^ 2
        * (∫ u in (-(L / 2))..(L / 2), (φ u * Real.cosh (ε * u)) ^ 2)
      ≤ (∫ u in (-(L / 2))..(L / 2), φ u ^ 2 * Real.cosh (ε * u)) ^ 2
        * (a + Real.sinh (ε * (2 * a)) / (2 * ε)) := by
  set M := Real.cosh (ε * (L / 2)) with hM
  set g₁ : ℝ → ℝ := fun u => φ u ^ 2 * Real.cosh (ε * u) with hg₁
  set g₂ : ℝ → ℝ := fun u => (φ u * Real.cosh (ε * u)) ^ 2 with hg₂
  have hg₁c : Continuous g₁ := by fun_prop
  have hg₂c : Continuous g₂ := by fun_prop
  have hi : ∀ (g : ℝ → ℝ), Continuous g → ∀ p q : ℝ, IntervalIntegrable g MeasureTheory.volume p q :=
    fun g hg p q => hg.intervalIntegrable p q
  -- splitting at `−a` and `a`
  have hsplit : ∀ g : ℝ → ℝ, Continuous g → (∫ u in (-(L / 2))..(L / 2), g u)
      = (∫ u in (-(L / 2))..(-a), g u) + (∫ u in (-a)..a, g u) + ∫ u in a..(L / 2), g u := by
    intro g hg
    rw [intervalIntegral.integral_add_adjacent_intervals (hi g hg _ _) (hi g hg _ _),
      intervalIntegral.integral_add_adjacent_intervals (hi g hg _ _) (hi g hg _ _)]
  have hcoshM : ∀ u, |u| ≤ L / 2 → Real.cosh (ε * u) ≤ M := by
    intro u hu
    rw [hM, Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos hε,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ L / 2)]
    exact mul_le_mul_of_nonneg_left hu hε.le
  have hcosh1 : ∀ u, 1 ≤ Real.cosh (ε * u) := fun u => Real.one_le_cosh _
  -- edges: `0 ≤ ∫ g₁` and `∫ g₂ ≤ M ∫ g₁`
  have hedge : ∀ p q : ℝ, p ≤ q → (∀ u ∈ Set.Icc p q, |u| ≤ L / 2) →
      0 ≤ (∫ u in p..q, g₁ u) ∧ (∫ u in p..q, g₂ u) ≤ M * ∫ u in p..q, g₁ u := by
    intro p q hpq hpqL
    refine ⟨intervalIntegral.integral_nonneg hpq fun u _ =>
      mul_nonneg (sq_nonneg _) (le_trans zero_le_one (hcosh1 u)), ?_⟩
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hpq (hi g₂ hg₂c _ _)
      ((continuous_const.mul hg₁c).intervalIntegrable _ _)
    intro u hu
    have h1 := hcoshM u (hpqL u hu)
    have h2 := hcosh1 u
    simp only [Pi.mul_apply, hg₁, hg₂]
    rw [mul_pow]
    have hc0 : 0 ≤ Real.cosh (ε * u) := le_trans zero_le_one h2
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (φ u)) hc0) (sub_nonneg.mpr h1)]
  obtain ⟨hl1, hl2⟩ := hedge (-(L / 2)) (-a) (by linarith) fun u hu => abs_le.mpr ⟨hu.1, by linarith [hu.2]⟩
  obtain ⟨hr1, hr2⟩ := hedge a (L / 2) haL fun u hu => abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
  -- centre: `Q₁ ≥ m A₁` and `Q₂ − m A₂ ≤ M (Q₁ − m A₁)`
  have hA₁ : ∫ u in (-a)..a, Real.cosh (ε * u) = 2 * Real.sinh (ε * a) / ε := integral_cosh_symm hε
  have hA₂ : ∫ u in (-a)..a, Real.cosh (ε * u) ^ 2 = a + Real.sinh (ε * (2 * a)) / (2 * ε) := by
    have h := integral_cosh_sq_window (L := 2 * a) hε
    rw [show 2 * a / 2 = a by ring] at h
    exact h
  have hQ₁ : m * (2 * Real.sinh (ε * a) / ε) ≤ ∫ u in (-a)..a, g₁ u := by
    rw [← hA₁, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
      ((by fun_prop : Continuous fun u => m * Real.cosh (ε * u)).intervalIntegrable _ _)
      (hi g₁ hg₁c _ _)
    intro u hu
    exact mul_le_mul_of_nonneg_right (hlow u (abs_le.mpr ⟨hu.1, hu.2⟩))
      (le_trans zero_le_one (hcosh1 u))
  have hQ₂ : (∫ u in (-a)..a, g₂ u) - m * (a + Real.sinh (ε * (2 * a)) / (2 * ε))
      ≤ M * ((∫ u in (-a)..a, g₁ u) - m * (2 * Real.sinh (ε * a) / ε)) := by
    have hmono : (∫ u in (-a)..a, (g₂ u - m * Real.cosh (ε * u) ^ 2))
        ≤ ∫ u in (-a)..a, M * (g₁ u - m * Real.cosh (ε * u)) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((hg₂c.sub (by fun_prop)).intervalIntegrable _ _)
        ((continuous_const.mul (hg₁c.sub (by fun_prop))).intervalIntegrable _ _)
      intro u hu
      have hu' : |u| ≤ a := abs_le.mpr ⟨hu.1, hu.2⟩
      have h1 := hcoshM u (le_trans hu' haL)
      have h2 := hcosh1 u
      have h3 := hlow u hu'
      simp only [Pi.sub_apply, Pi.mul_apply, hg₁, hg₂]
      rw [mul_pow]
      have hd : 0 ≤ φ u ^ 2 - m := by linarith
      have hc0 : 0 ≤ Real.cosh (ε * u) := le_trans zero_le_one h2
      nlinarith [mul_nonneg (mul_nonneg hd hc0) (sub_nonneg.mpr h1)]
    have e1 : (∫ u in (-a)..a, (g₂ u - m * Real.cosh (ε * u) ^ 2))
        = (∫ u in (-a)..a, g₂ u) - m * (a + Real.sinh (ε * (2 * a)) / (2 * ε)) := by
      rw [intervalIntegral.integral_sub (hi g₂ hg₂c _ _)
        ((by fun_prop : Continuous fun u => m * Real.cosh (ε * u) ^ 2).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, hA₂]
    have e2 : (∫ u in (-a)..a, M * (g₁ u - m * Real.cosh (ε * u)))
        = M * ((∫ u in (-a)..a, g₁ u) - m * (2 * Real.sinh (ε * a) / ε)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hi g₁ hg₁c _ _)
        ((by fun_prop : Continuous fun u => m * Real.cosh (ε * u)).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, hA₁]
    rw [← e1, ← e2]
    exact hmono
  -- the algebra
  rw [hsplit g₁ hg₁c, hsplit g₂ hg₂c]
  set A₁ := 2 * Real.sinh (ε * a) / ε with hA₁def
  set A₂ := a + Real.sinh (ε * (2 * a)) / (2 * ε) with hA₂def
  have hA₁0 : 0 ≤ A₁ := by
    have : 0 ≤ Real.sinh (ε * a) := Real.sinh_nonneg_iff.mpr (by positivity)
    positivity
  have hA₂0 : 0 ≤ A₂ := by
    have : 0 ≤ Real.sinh (ε * (2 * a)) := Real.sinh_nonneg_iff.mpr (by positivity)
    positivity
  set D₁ := (∫ u in (-(L / 2))..(-a), g₁ u) + ((∫ u in (-a)..a, g₁ u) - m * A₁)
    + ∫ u in a..(L / 2), g₁ u with hD₁
  set D₂ := (∫ u in (-(L / 2))..(-a), g₂ u) + ((∫ u in (-a)..a, g₂ u) - m * A₂)
    + ∫ u in a..(L / 2), g₂ u with hD₂
  have hD₁0 : 0 ≤ D₁ := by simp only [hD₁]; linarith
  have hD₂M : D₂ ≤ M * D₁ := by simp only [hD₁, hD₂]; nlinarith
  have hJ : (∫ u in (-(L / 2))..(-a), g₁ u) + (∫ u in (-a)..a, g₁ u) + ∫ u in a..(L / 2), g₁ u
      = m * A₁ + D₁ := by simp only [hD₁]; ring
  have hI : (∫ u in (-(L / 2))..(-a), g₂ u) + (∫ u in (-a)..a, g₂ u) + ∫ u in a..(L / 2), g₂ u
      = m * A₂ + D₂ := by simp only [hD₂]; ring
  rw [hJ, hI]
  have hcond' : M * A₁ ≤ 2 * A₂ := hcond
  have e1 : 0 ≤ m * A₁ * D₁ * (2 * A₂ - M * A₁) :=
    mul_nonneg (mul_nonneg (mul_nonneg hm hA₁0) hD₁0) (by linarith)
  have e2 : 0 ≤ D₁ ^ 2 * A₂ := mul_nonneg (sq_nonneg _) hA₂0
  have e3 : 0 ≤ m * A₁ ^ 2 * (M * D₁ - D₂) :=
    mul_nonneg (mul_nonneg hm (sq_nonneg _)) (by linarith)
  nlinarith

/-- The closed form of the comparison ratio. -/
theorem window_ratio_closed_form {L w θ ε : ℝ} (hL : 0 < L) (hθ : 0 < θ)
    (hsinθ : 0 < Real.sin θ) (hε : 0 < ε) (ha : 0 < L / 2 - w) :
    2 * Real.cos θ * (2 * Real.sinh (ε * (L / 2 - w)) / ε) ^ 2
        / ((L * Real.sin θ / θ) * ((L / 2 - w) + Real.sinh (ε * (2 * (L / 2 - w))) / (2 * ε)))
      = θ * Real.cos θ / Real.sin θ
        * (16 * Real.sinh ((ε * L - 2 * (ε * w)) / 2) ^ 2
          / (ε * L * ((ε * L - 2 * (ε * w)) + Real.sinh (ε * L - 2 * (ε * w))))) := by
  have e1 : ε * (L / 2 - w) = (ε * L - 2 * (ε * w)) / 2 := by ring
  have e2 : ε * (2 * (L / 2 - w)) = ε * L - 2 * (ε * w) := by ring
  rw [e1, e2]
  have hy : 0 < ε * L - 2 * (ε * w) := by nlinarith
  have hsy : 0 ≤ Real.sinh (ε * L - 2 * (ε * w)) := Real.sinh_nonneg_iff.mpr hy.le
  field_simp
  ring

/-- `1 − (4/5)·16 sinh²(y/2)/(x(y + sinh y)) ≤ x/24 + 2b/x` for `y = x − 2b`, `0 ≤ b`, `0 ≤ y`. -/
theorem deficit_ratio_sharp {x b : ℝ} (hx : 0 < x) (hb : 0 ≤ b) (hy : 0 ≤ x - 2 * b) :
    1 - 4 / 5 * (16 * Real.sinh ((x - 2 * b) / 2) ^ 2
        / (x * ((x - 2 * b) + Real.sinh (x - 2 * b)))) ≤ x / 24 + 2 * b / x := by
  set y := x - 2 * b with hydef
  have hsinh0 : 0 ≤ Real.sinh y := Real.sinh_nonneg_iff.mpr hy
  have hdef := deficit_sharp hy
  have hS : Real.cosh y - 1 = 2 * Real.sinh (y / 2) ^ 2 := by
    have := Real.cosh_two_mul (y / 2)
    rw [show 2 * (y / 2) = y by ring, Real.cosh_sq] at this
    rw [this]; ring
  rw [hS] at hdef
  rcases eq_or_lt_of_le hy with hy0 | hypos
  · -- `y = 0`: then `2b = x`
    have : 2 * b / x = 1 := by rw [div_eq_one_iff_eq hx.ne']; linarith
    rw [← hy0]
    simp only [zero_div, Real.sinh_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, zero_add, div_zero, sub_zero]
    linarith [div_nonneg hx.le (by norm_num : (0:ℝ) ≤ 24)]
  have hD : 0 < x * (y + Real.sinh y) := by positivity
  -- `(4/5)·16 sinh²(y/2)/(x(y + sinh y)) ≥ (1 − y/24) y/x`
  have h1 : (1 - y / 24) * y / x ≤ 4 / 5 * (16 * Real.sinh (y / 2) ^ 2 / (x * (y + Real.sinh y))) := by
    rw [mul_div_assoc', div_le_div_iff₀ hx hD]
    have hyx : 0 < y + Real.sinh y := by positivity
    have := mul_le_mul_of_nonneg_left hdef hx.le
    nlinarith
  -- `1 − (1 − y/24) y/x ≤ x/24 + 2b/x`
  have e1 : y / x = 1 - 2 * b / x := by
    rw [hydef]; field_simp
  have e2 : y ^ 2 / (24 * x) ≤ x / 24 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hyx : y ≤ x := by linarith
    nlinarith [mul_le_mul hyx hyx hy hx.le]
  have e3 : (1 - y / 24) * y / x = y / x - y ^ 2 / (24 * x) := by
    field_simp
  have h2 : 1 - (1 - y / 24) * y / x ≤ x / 24 + 2 * b / x := by
    rw [e3, e1]; linarith
  linarith

/-- **Window deficit.** -/
theorem window_deficit_le {φ : ℝ → ℝ} {L w θ ε : ℝ} (hφ : Continuous φ) (hL : 0 < L) (hw : 0 < w)
    (hLw : 24 * w * Real.exp 25 ≤ L) (hθ : 0 < θ) (hθ2 : θ ^ 2 ≤ 1 / 2) (hε : 0 < ε)
    (hup : ∀ u, |u| ≤ L / 2 → φ u ^ 2 ≤ Real.cos (2 * θ * u / L))
    (hle1 : ∀ u, φ u ^ 2 ≤ 1)
    (hlow : ∀ u, |u| ≤ L / 2 - w → Real.cos θ ≤ φ u ^ 2) :
    1 - 2 * (∫ u in (-(L / 2))..(L / 2), φ u ^ 2 * Real.cosh (ε * u)) ^ 2
        / ((∫ u in (-(L / 2))..(L / 2), φ u ^ 2)
          * ∫ u in (-(L / 2))..(L / 2), (φ u * Real.cosh (ε * u)) ^ 2)
      ≤ ε * L / 24 + 2 * w / L := by
  have hθ1 : θ ≤ 1 := by nlinarith
  have hcosθ : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_gt_three])
  have he25 : 1 ≤ Real.exp 25 := Real.one_le_exp (by norm_num)
  have hLw' : 24 * w ≤ L := le_trans (le_mul_of_one_le_right (by positivity) he25) hLw
  obtain ⟨hI₀up, hI₂up, hI₀pos, hI₂pos⟩ :=
    window_integral_bounds (ε := ε) hφ hL hw.le (by linarith) hθ hcosθ hε hup hle1 hlow
  have hcmp := fun (hcond : Real.cosh (ε * (L / 2)) * (2 * Real.sinh (ε * (L / 2 - w)) / ε)
      ≤ 2 * ((L / 2 - w) + Real.sinh (ε * (2 * (L / 2 - w))) / (2 * ε))) =>
    window_weight_comparison (φ := φ) (L := L) (a := L / 2 - w) (m := Real.cos θ) hφ
      (by linarith) (by linarith) hcosθ.le hε hlow hcond
  generalize (∫ u in (-(L / 2))..(L / 2), φ u ^ 2 * Real.cosh (ε * u)) = J at hcmp ⊢
  generalize (∫ u in (-(L / 2))..(L / 2), φ u ^ 2) = I₀ at hI₀up hI₀pos ⊢
  generalize (∫ u in (-(L / 2))..(L / 2), (φ u * Real.cosh (ε * u)) ^ 2) = I₂ at hcmp hI₂up hI₂pos ⊢
  have hR0 : 0 ≤ 2 * J ^ 2 / (I₀ * I₂) := by positivity
  have hwL0 : 0 < 2 * w / L := by positivity
  rcases le_or_gt 24 (ε * L) with h24 | h24
  · have : 1 ≤ ε * L / 24 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  -- the side condition of the weight comparison
  set t := ε * (L / 2 - w) with ht
  set b := ε * w with hb
  have hb0 : 0 ≤ b := by positivity
  have ht0 : 0 ≤ t := mul_nonneg hε.le (by linarith)
  have htb : ε * (L / 2) = t + b := by simp only [ht, hb]; ring
  have ht12 : t ≤ 12 := by
    have : t ≤ ε * L / 2 := by simp only [ht]; nlinarith
    linarith
  have hbe : b * Real.exp 25 ≤ 1 := by
    have h1 : b * L ≤ 24 * w := by simp only [hb]; nlinarith
    have h2 : b * (24 * w * Real.exp 25) ≤ b * L := mul_le_mul_of_nonneg_left hLw hb0
    have h3 : b * Real.exp 25 * (24 * w) ≤ 1 * (24 * w) := by nlinarith
    exact le_of_mul_le_mul_right h3 (by positivity)
  have hcond : Real.cosh (ε * (L / 2)) * (2 * Real.sinh (ε * (L / 2 - w)) / ε)
      ≤ 2 * ((L / 2 - w) + Real.sinh (ε * (2 * (L / 2 - w))) / (2 * ε)) := by
    have key := sinh_mul_cosh_add_sub_le ht0 ht12 hb0 hbe
    have e1 : Real.cosh (ε * (L / 2)) = Real.cosh (t + b) := by rw [htb]
    have e2 : Real.sinh (ε * (2 * (L / 2 - w))) = 2 * Real.sinh t * Real.cosh t := by
      rw [show ε * (2 * (L / 2 - w)) = 2 * t by rw [ht]; ring, Real.sinh_two_mul]
    have e3 : Real.sinh (ε * (L / 2 - w)) = Real.sinh t := by rw [ht]
    have e4 : L / 2 - w = t / ε := by rw [ht]; field_simp
    rw [e1, e2, e3, e4]
    have f1 : Real.cosh (t + b) * (2 * Real.sinh t / ε)
        = 2 * (Real.sinh t * Real.cosh (t + b)) / ε := by ring
    have f2 : 2 * (t / ε + 2 * Real.sinh t * Real.cosh t / (2 * ε))
        = (2 * t + 2 * (Real.sinh t * Real.cosh t)) / ε := by field_simp
    rw [f1, f2]
    apply div_le_div_of_nonneg_right _ hε.le
    nlinarith [key]
  have hJ2 := hcmp hcond
  -- `R ≥ 2 cos θ A₁²/((L sin θ/θ) A₂)`
  set A₁ := 2 * Real.sinh (ε * (L / 2 - w)) / ε with hA₁
  set A₂ := (L / 2 - w) + Real.sinh (ε * (2 * (L / 2 - w))) / (2 * ε) with hA₂
  have hA₂pos : 0 < A₂ := by
    have : 0 ≤ Real.sinh (ε * (2 * (L / 2 - w))) := Real.sinh_nonneg_iff.mpr
      (mul_nonneg hε.le (by linarith))
    have : 0 < L / 2 - w := by linarith
    positivity
  have hA0pos : 0 < L * Real.sin θ / θ := by positivity
  have hR1 : 2 * Real.cos θ * A₁ ^ 2 / ((L * Real.sin θ / θ) * A₂) ≤ 2 * J ^ 2 / (I₀ * I₂) := by
    have h1 : 2 * Real.cos θ * A₁ ^ 2 / ((L * Real.sin θ / θ) * A₂)
        ≤ 2 * Real.cos θ * A₁ ^ 2 / (I₀ * A₂) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hI₀up hA₂pos.le)
    have h2 : 2 * Real.cos θ * A₁ ^ 2 / (I₀ * A₂) ≤ 2 * J ^ 2 / (I₀ * I₂) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hJ2 (by positivity : (0:ℝ) ≤ 2 * I₀)
      nlinarith
    linarith
  rw [hA₁, hA₂, window_ratio_closed_form hL hθ hsinθ hε (by linarith)] at hR1
  have hk : 4 / 5 ≤ θ * Real.cos θ / Real.sin θ := by
    rw [le_div_iff₀ hsinθ]
    have := window_constant_four_fifths hθ.le hθ2
    linarith
  have hx0 : 0 < ε * L := mul_pos hε hL
  have hy0 : 0 ≤ ε * L - 2 * b := by
    simp only [hb]; nlinarith
  have hratio := deficit_ratio_sharp hx0 hb0 hy0
  have hfrac0 : 0 ≤ 16 * Real.sinh ((ε * L - 2 * b) / 2) ^ 2
      / (ε * L * ((ε * L - 2 * b) + Real.sinh (ε * L - 2 * b))) := by
    have : 0 ≤ Real.sinh (ε * L - 2 * b) := Real.sinh_nonneg_iff.mpr hy0
    positivity
  have h3 := mul_le_mul_of_nonneg_right hk hfrac0
  have hbx : 2 * b / (ε * L) = 2 * w / L := by
    simp only [hb]; field_simp
  rw [hbx] at hratio
  linarith

/-- **The Montgomery–Taylor window satisfies the deficit bound.** -/
theorem phiD_window_deficit_le {P : Zeta23.Params} (hP : P.Valid) (T : ℝ) (hL : 0 < P.L T)
    (hLw : 24 * P.w * Real.exp 25 ≤ P.L T) (hc : Continuous (P.phiD T)) {ε : ℝ} (hε : 0 < ε) :
    1 - 2 * (∫ u in (-(P.L T / 2))..(P.L T / 2), P.phiD T u ^ 2 * Real.cosh (ε * u)) ^ 2
        / ((∫ u in (-(P.L T / 2))..(P.L T / 2), P.phiD T u ^ 2)
          * ∫ u in (-(P.L T / 2))..(P.L T / 2), (P.phiD T u * Real.cosh (ε * u)) ^ 2)
      ≤ ε * P.L T / 24 + 2 * P.w / P.L T := by
  have hw : 0 < P.w := lt_of_lt_of_le one_pos hP.one_le_w
  have hlam0 := hP.lam_pos
  have hlam1 := hP.lam_le_one
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  set θ := Real.sqrt 2 * P.lam / 2 with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ2 : θ ^ 2 ≤ 1 / 2 := by
    rw [hθ, div_pow, mul_pow, hs2]
    nlinarith [pow_le_one₀ hlam0.le hlam1 (n := 2)]
  have hφ : ∀ u, P.phiD T u = Real.sqrt (Zeta23.ThmD.vStar P.lam (u / P.L T))
      * Zeta23.Taper.phi P.ϱ (P.L T) P.w u := fun u => rfl
  have harg : ∀ u, Real.sqrt 2 * P.lam * (u / P.L T) = 2 * θ * u / P.L T := fun u => by
    rw [hθ]; ring
  have hsq : ∀ u, |u| ≤ P.L T / 2 → P.phiD T u ^ 2
      = Real.cos (2 * θ * u / P.L T) * Zeta23.Taper.phi P.ϱ (P.L T) P.w u ^ 2 := by
    intro u hu
    have hv := Zeta23.ThmD.cos_factor_ge hlam0 hlam1 hL hu
    rw [hφ, mul_pow, Real.sq_sqrt (by linarith)]
    simp only [Zeta23.ThmD.vStar, harg]
  refine window_deficit_le hc hL hw hLw hθ0 hθ2 hε ?_ ?_ ?_
  · intro u hu
    rw [hsq u hu]
    have h1 := Zeta23.Taper.phi_le_one hP.taper (L := P.L T) (w := P.w) u
    have h0 := Zeta23.Taper.phi_nonneg hP.taper (L := P.L T) (w := P.w) u
    have hcos : 0 ≤ Real.cos (2 * θ * u / P.L T) := by
      have hv := Zeta23.ThmD.cos_factor_ge hlam0 hlam1 hL hu
      simp only [Zeta23.ThmD.vStar, harg] at hv
      linarith
    have : Zeta23.Taper.phi P.ϱ (P.L T) P.w u ^ 2 ≤ 1 := by nlinarith
    exact mul_le_of_le_one_right hcos this
  · intro u
    have h1 := Zeta23.ThmD.phiD_le_one (lam := P.lam) (L := P.L T) (w := P.w) hP.taper u
    have h0 := Zeta23.ThmD.phiD_nonneg (lam := P.lam) (L := P.L T) (w := P.w) hP.taper u
    show Zeta23.ThmD.phiD P.ϱ P.lam (P.L T) P.w u ^ 2 ≤ 1
    nlinarith
  · intro u hu
    have hu' : |u| ≤ P.L T / 2 := by linarith
    rw [hsq u hu', Zeta23.Taper.phi_eq_one hP.taper hw hu, one_pow, mul_one,
      ← Real.cos_abs (2 * θ * u / P.L T)]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
    · nlinarith [Real.pi_gt_three]
    · rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * θ), abs_of_pos hL,
        div_le_iff₀ hL]
      nlinarith [abs_nonneg u]

end

end RHTower
