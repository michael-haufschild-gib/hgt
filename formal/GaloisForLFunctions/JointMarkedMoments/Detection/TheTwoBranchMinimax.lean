import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# The exact two-branch minimax of zero detection

The zero-detection exponent at a split length `t` is the larger of the decreasing detector branch
`f(t) = 1 − δ(A + 2Kt/3)` (the inverse saving at width `r = 2t/3`, equal to the ordinary saving at
width `m = t/3`) and the increasing count branch `q(t) = 1/6 + Vt`.

* `detectionExponent_lt_of_ne_minimizer`: on every interval `[a, b]` the maximum has the unique
  minimizer `min b (max a t∗)`, where `t∗ = (5/6 − δA)/D`, `D = V + 2δK/3`, is the crossing.
* `detectionExponent_minimizer_eq`: at an interior crossing the minimum is `C∗ = 1/6 + Vt∗`.
* `minimaxValue_eq_improvedCount`: for an affine supporting line `g(r) = g₀ − g₁r`, with
  `A = x(1 + 2g₀)`, `K = 1 − x(1 + 2g₁)`, `V = 5/6 − δ`, the minimum is the improved count
  `R_g = 1 − δ + δV(1 − x(1 + 6g₀ − 4g₁))/J_g`, `J_g = 3V + 2δK`.
* `hasDerivAt_minimaxValue_intercept`, `hasDerivAt_minimaxValue_slope`: the sensitivities
  `∂C∗/∂g₀ = −2δxV/D` and `∂C∗/∂g₁ = 4δxVt∗/(3D)`.
-/

namespace GaloisForLFunctions.JointMarkedMoments

open Set

noncomputable section

/-- The detector branch `1 − δ(A + 2Kt/3)`. -/
def detectorBranch (δ A K t : ℝ) : ℝ := 1 - δ * (A + 2 * K / 3 * t)

/-- The count branch `1/6 + Vt` of the long inverse estimate. -/
def countBranch (V t : ℝ) : ℝ := 1 / 6 + V * t

/-- The crossing denominator `D = V + 2δK/3`. -/
def crossingDenominator (δ K V : ℝ) : ℝ := V + 2 * δ * K / 3

/-- The crossing `t∗ = (5/6 − δA)/D` of the two branches. -/
def crossingPoint (δ A K V : ℝ) : ℝ := (5 / 6 - δ * A) / crossingDenominator δ K V

/-- The detection exponent: the larger of the two branches. -/
def detectionExponent (δ A K V t : ℝ) : ℝ := max (detectorBranch δ A K t) (countBranch V t)

/-- The clamped crossing `min b (max a t∗)`. -/
def detectionMinimizer (δ A K V a b : ℝ) : ℝ := min b (max a (crossingPoint δ A K V))

/-- The interior minimum `C∗ = 1/6 + V t∗`. -/
def minimaxValue (δ A K V : ℝ) : ℝ := 1 / 6 + V * crossingPoint δ A K V

/-- At `r = 2m = 2t/3` the inverse saving `δ(A + Kr)` and the ordinary saving `δ(A + 2Km)`
agree, and the detector branch is the common saving. -/
theorem inverse_and_ordinary_savings_agree (δ A K t : ℝ) :
    δ * (A + K * (2 * t / 3)) = δ * (A + 2 * K * (t / 3)) ∧
      detectorBranch δ A K t = 1 - δ * (A + K * (2 * t / 3)) := by
  exact ⟨by ring, by unfold detectorBranch; ring⟩

/-- The gap between the branches is `D (t∗ − t)`. -/
theorem detectorBranch_sub_countBranch {δ A K V : ℝ} (hD : crossingDenominator δ K V ≠ 0)
    (t : ℝ) :
    detectorBranch δ A K t - countBranch V t =
      crossingDenominator δ K V * (crossingPoint δ A K V - t) := by
  have h : crossingDenominator δ K V * crossingPoint δ A K V = 5 / 6 - δ * A := by
    unfold crossingPoint; field_simp
  unfold crossingDenominator at h ⊢
  unfold detectorBranch countBranch
  linear_combination (-1 : ℝ) * h

/-- The clamped crossing minimizes the detection exponent on `[a, b]`, uniquely. -/
theorem detectionExponent_lt_of_ne_minimizer {δ A K V a b : ℝ} (hδ : 0 < δ) (hK : 0 < K)
    (hV : 0 < V) (hab : a ≤ b) :
    detectionMinimizer δ A K V a b ∈ Icc a b ∧
      ∀ t ∈ Icc a b, t ≠ detectionMinimizer δ A K V a b →
        detectionExponent δ A K V (detectionMinimizer δ A K V a b) <
          detectionExponent δ A K V t := by
  have hDpos : 0 < crossingDenominator δ K V := by
    unfold crossingDenominator; positivity
  have gap := detectorBranch_sub_countBranch (A := A) hDpos.ne'
  set ts := crossingPoint δ A K V
  have hf : ∀ s t, detectorBranch δ A K t - detectorBranch δ A K s = -(2 * δ * K / 3) * (t - s) := by
    intro s t; unfold detectorBranch; ring
  have hq : ∀ s t, countBranch V t - countBranch V s = V * (t - s) := by
    intro s t; unfold countBranch; ring
  have hcK : 0 < 2 * δ * K / 3 := by positivity
  unfold detectionMinimizer detectionExponent
  rcases lt_or_ge ts a with h1 | h1
  · -- the crossing lies left of the interval: the minimizer is `a`
    rw [max_eq_left h1.le, min_eq_right hab]
    refine ⟨⟨le_rfl, hab⟩, fun t ht hne => ?_⟩
    have hta : a < t := lt_of_le_of_ne ht.1 (Ne.symm hne)
    have hga := gap a
    have hqa := hq a t
    rw [max_eq_right (by nlinarith)]
    exact lt_of_lt_of_le (by nlinarith) (le_max_right _ _)
  · rcases le_or_gt ts b with h2 | h2
    · -- interior crossing: the minimizer is `t∗`
      rw [max_eq_right h1, min_eq_right h2]
      refine ⟨⟨h1, h2⟩, fun t _ hne => ?_⟩
      have hgs := gap ts
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hf ts t
        rw [max_eq_left (by nlinarith)]
        exact lt_of_lt_of_le (by nlinarith) (le_max_left _ _)
      · have := hq ts t
        rw [max_eq_right (by nlinarith)]
        exact lt_of_lt_of_le (by nlinarith) (le_max_right _ _)
    · -- the crossing lies right of the interval: the minimizer is `b`
      rw [max_eq_right (hab.trans h2.le), min_eq_left h2.le]
      refine ⟨⟨hab, le_rfl⟩, fun t ht hne => ?_⟩
      have htb : t < b := lt_of_le_of_ne ht.2 hne
      have hgb := gap b
      have := hf b t
      rw [max_eq_left (by nlinarith)]
      exact lt_of_lt_of_le (by nlinarith) (le_max_left _ _)

/-- At an interior crossing the minimum of the detection exponent is `C∗ = 1/6 + V t∗`. -/
theorem detectionExponent_minimizer_eq {δ A K V a b : ℝ} (hD : crossingDenominator δ K V ≠ 0)
    (ha : a ≤ crossingPoint δ A K V) (hb : crossingPoint δ A K V ≤ b) :
    detectionMinimizer δ A K V a b = crossingPoint δ A K V ∧
      detectionExponent δ A K V (crossingPoint δ A K V) = minimaxValue δ A K V := by
  refine ⟨by unfold detectionMinimizer; rw [max_eq_right ha, min_eq_right hb], ?_⟩
  have h := detectorBranch_sub_countBranch (A := A) hD (crossingPoint δ A K V)
  rw [sub_self, mul_zero, sub_eq_zero] at h
  unfold detectionExponent minimaxValue
  rw [h, max_self]
  rfl

/-- The denominator `J_g = 3V + 2δ(1 − x(1 + 2g₁))` of the improved count, `V = 5/6 − δ`. -/
def improvedCountDenominator (δ x g₁ : ℝ) : ℝ := 3 * (5 / 6 - δ) + 2 * δ * (1 - x * (1 + 2 * g₁))

/-- The improved count `R_g = 1 − δ + δV(1 − x(1 + 6g₀ − 4g₁))/J_g` of an affine supporting line
`g(r) = g₀ − g₁ r`. -/
def improvedCount (δ x g₀ g₁ : ℝ) : ℝ :=
  1 - δ + δ * (5 / 6 - δ) * (1 - x * (1 + 6 * g₀ - 4 * g₁)) / improvedCountDenominator δ x g₁

/-- The interior minimax value with `A = x(1 + 2g₀)`, `K = 1 − x(1 + 2g₁)`, `V = 5/6 − δ` is
the improved count `R_g`. -/
theorem minimaxValue_eq_improvedCount {δ x g₀ g₁ : ℝ} (hJ : improvedCountDenominator δ x g₁ ≠ 0) :
    minimaxValue δ (x * (1 + 2 * g₀)) (1 - x * (1 + 2 * g₁)) (5 / 6 - δ) =
      improvedCount δ x g₀ g₁ := by
  have hcd : crossingDenominator δ (1 - x * (1 + 2 * g₁)) (5 / 6 - δ) =
      improvedCountDenominator δ x g₁ / 3 := by
    unfold crossingDenominator improvedCountDenominator; ring
  have key : 3 * ((5 / 6 - δ) * (5 / 6 - δ * (x * (1 + 2 * g₀)))) =
      (5 / 6 - δ) * improvedCountDenominator δ x g₁ +
        δ * (5 / 6 - δ) * (1 - x * (1 + 6 * g₀ - 4 * g₁)) := by
    unfold improvedCountDenominator; ring
  unfold minimaxValue crossingPoint improvedCount
  rw [hcd]
  generalize improvedCountDenominator δ x g₁ = J at hJ key ⊢
  have e1 : (5 / 6 - δ) * ((5 / 6 - δ * (x * (1 + 2 * g₀))) / (J / 3)) =
      3 * ((5 / 6 - δ) * (5 / 6 - δ * (x * (1 + 2 * g₀)))) / J := by
    field_simp
  have e2 : (5 / 6 - δ) * J / J = 5 / 6 - δ := by field_simp
  rw [e1, key, add_div, e2]
  ring

/-- `∂C∗/∂g₀ = −2δxV/D`. -/
theorem hasDerivAt_minimaxValue_intercept (δ x V g₀ g₁ : ℝ) :
    HasDerivAt (fun g => minimaxValue δ (x * (1 + 2 * g)) (1 - x * (1 + 2 * g₁)) V)
      (-(2 * δ * x * V) / crossingDenominator δ (1 - x * (1 + 2 * g₁)) V) g₀ := by
  set D := crossingDenominator δ (1 - x * (1 + 2 * g₁)) V
  have hfun : (fun g => minimaxValue δ (x * (1 + 2 * g)) (1 - x * (1 + 2 * g₁)) V) =
      fun g => (1 / 6 + V * (5 / 6 - δ * x) / D) + (-(2 * δ * x * V) / D) * g := by
    funext g; unfold minimaxValue crossingPoint; rw [← show D = _ from rfl]; ring
  rw [hfun]
  exact ((hasDerivAt_const_add_iff (1 / 6 + V * (5 / 6 - δ * x) / D)).mpr
    (HasDerivAt.const_mul (-(2 * δ * x * V) / D) (hasDerivAt_id' (x := g₀)))).congr_deriv
      (mul_one _)

/-- `∂C∗/∂g₁ = 4δxVt∗/(3D)` at a nonzero crossing denominator. -/
theorem hasDerivAt_minimaxValue_slope (δ x V A g₁ : ℝ)
    (hD : crossingDenominator δ (1 - x * (1 + 2 * g₁)) V ≠ 0) :
    HasDerivAt (fun g => minimaxValue δ A (1 - x * (1 + 2 * g)) V)
      (4 * δ * x * V * crossingPoint δ A (1 - x * (1 + 2 * g₁)) V /
        (3 * crossingDenominator δ (1 - x * (1 + 2 * g₁)) V)) g₁ := by
  have hd : HasDerivAt (fun g => crossingDenominator δ (1 - x * (1 + 2 * g)) V)
      (-(4 * δ * x / 3)) g₁ := by
    have h := (hasDerivAt_const_add_iff V).mpr (HasDerivAt.const_mul (2 * δ / 3)
      (HasDerivAt.const_sub (1 - x) (HasDerivAt.const_mul (2 * x) (hasDerivAt_id' (x := g₁)))))
    convert h using 1
    · funext g; unfold crossingDenominator; ring
    · ring
  have hq := (hasDerivAt_const_add_iff (1 / 6 : ℝ)).mpr
    (HasDerivAt.const_mul V (HasDerivAt.div (hasDerivAt_const g₁ (5 / 6 - δ * A)) hd hD))
  convert hq using 1
  · funext g; unfold minimaxValue crossingPoint; rfl
  · unfold crossingPoint
    field_simp
    ring

end

end GaloisForLFunctions.JointMarkedMoments
