import GaloisForLFunctions.RHTower.PrimeArchHermiteMomentBoundary
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# The Gaussian–Hermite perturbation density

Let `φ(y) = e^{-y²/2}/√(2π)` and `P = -He₄ + He₆ - 2He₈ + He₁₀`
(probabilists' Hermite polynomials), so that
`P(y) = y¹⁰ - 47y⁸ + 687y⁶ - 3586y⁴ + 5616y² - 1173`.  For `τ ≥ 0` put

```text
ρ_τ(x) = 6 φ(6x) (1 + τ P(6x)).
```

Gaussian integration by parts gives `∫ y^{2k} φ = (2k-1)!!`, so the even moments of `ρ_τ` are
`6^{-2j}(m_j + τ c_j)` with the Wick moments `m_j` and corrections `c_j` of
`PrimeArchHermiteMomentBoundary`; in particular `∫ ρ_τ = 1`.  Since `P - y¹⁰/2` is bounded
below and `P'(y) = y R(y)`, `R, P'' ≤ K(1 + y⁸)`, a split at `y² = 24K + 1` shows that for all
sufficiently small `τ > 0`:

* `ρ_τ ≥ (9/10) ρ_0`;
* `-(log ρ_τ)'' ≥ 30` everywhere (strong log-concavity);
* `-ρ_τ'/ρ_τ ≥ 30x` for `x ≥ 0`;
* the score defect density `ρ_τ - 16xρ_τ' - 303x²ρ_τ` is at least `(1 + 177x²)ρ_τ` on `x ≥ 0`.

Integration by parts identifies its even moments with `(32k+17)M_k - 303M_{k+1}`.
-/

open MeasureTheory Set Filter Topology Polynomial

noncomputable section

namespace RHTower

/-! ## The standard Gaussian -/

/-- The standard Gaussian density `e^{-y²/2}/√(2π)`. -/
def stdGaussianDensity (y : ℝ) : ℝ := Real.exp (-(1 / 2) * y ^ 2) / Real.sqrt (2 * Real.pi)

theorem stdGaussianDensity_pos (y : ℝ) : 0 < stdGaussianDensity y := by
  unfold stdGaussianDensity
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  positivity

theorem stdGaussianDensity_neg (y : ℝ) : stdGaussianDensity (-y) = stdGaussianDensity y := by
  simp [stdGaussianDensity]

theorem continuous_stdGaussianDensity : Continuous stdGaussianDensity := by
  unfold stdGaussianDensity
  fun_prop

theorem hasDerivAt_stdGaussianDensity (y : ℝ) :
    HasDerivAt stdGaussianDensity (-y * stdGaussianDensity y) y := by
  have h1 : HasDerivAt (fun y : ℝ => -(1 / 2) * y ^ 2) (-(1 / 2) * (2 * y)) y := by
    simpa using ((hasDerivAt_pow 2 y).const_mul (-(1 / 2 : ℝ)))
  have h := (h1.exp).div_const (Real.sqrt (2 * Real.pi))
  have e : Real.exp (-(1 / 2) * y ^ 2) * (-(1 / 2) * (2 * y)) / Real.sqrt (2 * Real.pi) =
      -y * stdGaussianDensity y := by
    unfold stdGaussianDensity; ring
  rw [e] at h
  exact h

theorem integrable_pow_mul_stdGaussianDensity (n : ℕ) :
    Integrable fun y : ℝ => y ^ n * stdGaussianDensity y := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := (n : ℝ))
    (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  simp_rw [Real.rpow_natCast] at h
  refine (h.div_const (Real.sqrt (2 * Real.pi))).congr (Eventually.of_forall fun y => ?_)
  unfold stdGaussianDensity
  ring

theorem integral_stdGaussianDensity : ∫ y, stdGaussianDensity y = 1 := by
  unfold stdGaussianDensity
  rw [integral_div, integral_gaussian]
  have hπ : Real.pi / (1 / 2) = 2 * Real.pi := by ring
  rw [hπ, div_self (Real.sqrt_pos.2 (by positivity)).ne']

/-- Gaussian integration by parts: `∫ y^{n+2} φ = (n+1) ∫ y^n φ`. -/
theorem integral_pow_add_two_mul_stdGaussianDensity (n : ℕ) :
    ∫ y, y ^ (n + 2) * stdGaussianDensity y = (n + 1) * ∫ y, y ^ n * stdGaussianDensity y := by
  have hu : ∀ y ∈ tsupport (fun y : ℝ => -stdGaussianDensity y),
      HasDerivAt (fun y : ℝ => y ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * y ^ n) y := by
    intro y _
    simpa using hasDerivAt_pow (n + 1) y
  have hv : ∀ y ∈ tsupport (fun y : ℝ => y ^ (n + 1)),
      HasDerivAt (fun y : ℝ => -stdGaussianDensity y) (y * stdGaussianDensity y) y := by
    intro y _
    have h := (hasDerivAt_stdGaussianDensity y).neg
    rw [show -(-y * stdGaussianDensity y) = y * stdGaussianDensity y by ring] at h
    exact h
  have h1 : Integrable ((fun y : ℝ => y ^ (n + 1)) * fun y => y * stdGaussianDensity y) :=
    (integrable_pow_mul_stdGaussianDensity (n + 2)).congr
      (Eventually.of_forall fun y => by simp only [Pi.mul_apply]; ring)
  have h2 : Integrable ((fun y : ℝ => ((n + 1 : ℕ) : ℝ) * y ^ n) * fun y => -stdGaussianDensity y) :=
    ((integrable_pow_mul_stdGaussianDensity n).const_mul (-((n + 1 : ℕ) : ℝ))).congr
      (Eventually.of_forall fun y => by simp only [Pi.mul_apply]; ring)
  have h3 : Integrable ((fun y : ℝ => y ^ (n + 1)) * fun y => -stdGaussianDensity y) :=
    (integrable_pow_mul_stdGaussianDensity (n + 1)).neg.congr
      (Eventually.of_forall fun y => by simp only [Pi.mul_apply, Pi.neg_apply]; ring)
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable hu hv h1 h2 h3
  have e1 : (∫ y, y ^ (n + 1) * (y * stdGaussianDensity y)) =
      ∫ y, y ^ (n + 2) * stdGaussianDensity y := by
    congr 1; funext y; ring
  have e2 : (∫ y, ((n + 1 : ℕ) : ℝ) * y ^ n * -stdGaussianDensity y) =
      -((n + 1) * ∫ y, y ^ n * stdGaussianDensity y) := by
    rw [← integral_const_mul, ← integral_neg]
    congr 1; funext y; push_cast; ring
  rw [e1, e2, neg_neg] at h
  exact h

/-- `∫ y^{2k} φ(y) dy` is the Wick moment `(2k-1)!!`. -/
theorem integral_even_pow_mul_stdGaussianDensity (k : ℕ) :
    ∫ y, y ^ (2 * k) * stdGaussianDensity y = gaussianEvenWickMoment k := by
  induction k with
  | zero => simpa [gaussianEvenWickMoment] using integral_stdGaussianDensity
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, integral_pow_add_two_mul_stdGaussianDensity, ih,
        gaussianEvenWickMoment]
      push_cast
      ring

/-! ## The Hermite boundary polynomial -/

/-- `P(y) = y¹⁰ - 47y⁸ + 687y⁶ - 3586y⁴ + 5616y² - 1173`. -/
def hermiteBoundaryPoly (y : ℝ) : ℝ :=
  y ^ 10 - 47 * y ^ 8 + 687 * y ^ 6 - 3586 * y ^ 4 + 5616 * y ^ 2 - 1173

private theorem hermite_two : (hermite 2 : ℤ[X]) = X ^ 2 - 1 := by
  rw [hermite_succ, hermite_one]; simp only [derivative_X]; ring

private theorem hermite_three : (hermite 3 : ℤ[X]) = X ^ 3 - 3 * X := by
  rw [hermite_succ, hermite_two]
  simp only [derivative_sub, derivative_X_pow, derivative_one]
  norm_num; ring

private theorem hermite_four : (hermite 4 : ℤ[X]) = X ^ 4 - 6 * X ^ 2 + 3 := by
  rw [hermite_succ, hermite_three]
  simp only [derivative_sub, derivative_X_pow, derivative_mul, derivative_X, derivative_ofNat]
  norm_num; ring

private theorem hermite_five : (hermite 5 : ℤ[X]) = X ^ 5 - 10 * X ^ 3 + 15 * X := by
  rw [hermite_succ, hermite_four]
  simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_mul,
    derivative_ofNat]
  norm_num; ring

private theorem hermite_six : (hermite 6 : ℤ[X]) = X ^ 6 - 15 * X ^ 4 + 45 * X ^ 2 - 15 := by
  rw [hermite_succ, hermite_five]
  simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_mul,
    derivative_ofNat]
  norm_num; ring

private theorem hermite_seven :
    (hermite 7 : ℤ[X]) = X ^ 7 - 21 * X ^ 5 + 105 * X ^ 3 - 105 * X := by
  rw [hermite_succ, hermite_six]
  simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_mul,
    derivative_ofNat]
  norm_num; ring

private theorem hermite_eight :
    (hermite 8 : ℤ[X]) = X ^ 8 - 28 * X ^ 6 + 210 * X ^ 4 - 420 * X ^ 2 + 105 := by
  rw [hermite_succ, hermite_seven]
  simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_mul,
    derivative_ofNat]
  norm_num; ring

private theorem hermite_nine :
    (hermite 9 : ℤ[X]) = X ^ 9 - 36 * X ^ 7 + 378 * X ^ 5 - 1260 * X ^ 3 + 945 * X := by
  rw [hermite_succ, hermite_eight]
  simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_mul,
    derivative_ofNat]
  norm_num; ring

private theorem hermite_ten :
    (hermite 10 : ℤ[X]) =
      X ^ 10 - 45 * X ^ 8 + 630 * X ^ 6 - 3150 * X ^ 4 + 4725 * X ^ 2 - 945 := by
  rw [hermite_succ, hermite_nine]
  simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_mul,
    derivative_ofNat]
  norm_num; ring

/-- The polynomial is exactly `-He₄ + He₆ - 2He₈ + He₁₀`. -/
theorem hermiteBoundaryPoly_eq_hermite (y : ℝ) :
    hermiteBoundaryPoly y =
      ((-(hermite 4) + hermite 6 - 2 * hermite 8 + hermite 10 : ℤ[X]).map
        (Int.castRingHom ℝ)).eval y := by
  rw [hermite_four, hermite_six, hermite_eight, hermite_ten]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_neg, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_X, eval_ofNat]
  unfold hermiteBoundaryPoly
  ring

theorem hermiteBoundaryPoly_neg (y : ℝ) : hermiteBoundaryPoly (-y) = hermiteBoundaryPoly y := by
  unfold hermiteBoundaryPoly; ring

/-- `P'(y)`. -/
def hermiteBoundaryPolyDeriv (y : ℝ) : ℝ :=
  10 * y ^ 9 - 376 * y ^ 7 + 4122 * y ^ 5 - 14344 * y ^ 3 + 11232 * y

/-- `P''(y)`. -/
def hermiteBoundaryPolySecond (y : ℝ) : ℝ :=
  90 * y ^ 8 - 2632 * y ^ 6 + 20610 * y ^ 4 - 43032 * y ^ 2 + 11232

theorem hasDerivAt_hermiteBoundaryPoly (y : ℝ) :
    HasDerivAt hermiteBoundaryPoly (hermiteBoundaryPolyDeriv y) y := by
  have h := ((((((hasDerivAt_pow 10 y).sub ((hasDerivAt_pow 8 y).const_mul 47)).add
    ((hasDerivAt_pow 6 y).const_mul 687)).sub ((hasDerivAt_pow 4 y).const_mul 3586)).add
    ((hasDerivAt_pow 2 y).const_mul 5616)).sub_const 1173)
  have e : ((10 : ℕ) : ℝ) * y ^ (10 - 1) - 47 * (((8 : ℕ) : ℝ) * y ^ (8 - 1)) +
      687 * (((6 : ℕ) : ℝ) * y ^ (6 - 1)) - 3586 * (((4 : ℕ) : ℝ) * y ^ (4 - 1)) +
      5616 * (((2 : ℕ) : ℝ) * y ^ (2 - 1)) = hermiteBoundaryPolyDeriv y := by
    unfold hermiteBoundaryPolyDeriv; norm_num; ring
  rw [e] at h
  exact h

theorem hasDerivAt_hermiteBoundaryPolyDeriv (y : ℝ) :
    HasDerivAt hermiteBoundaryPolyDeriv (hermiteBoundaryPolySecond y) y := by
  have h := (((((hasDerivAt_pow 9 y).const_mul 10).sub ((hasDerivAt_pow 7 y).const_mul 376)).add
    ((hasDerivAt_pow 5 y).const_mul 4122)).sub ((hasDerivAt_pow 3 y).const_mul 14344)).add
    ((hasDerivAt_id y).const_mul 11232)
  have e : 10 * (((9 : ℕ) : ℝ) * y ^ (9 - 1)) - 376 * (((7 : ℕ) : ℝ) * y ^ (7 - 1)) +
      4122 * (((5 : ℕ) : ℝ) * y ^ (5 - 1)) - 14344 * (((3 : ℕ) : ℝ) * y ^ (3 - 1)) +
      11232 * 1 = hermiteBoundaryPolySecond y := by
    unfold hermiteBoundaryPolySecond; norm_num; ring
  rw [e] at h
  exact h

private theorem pow_le_one_add_pow_four {t : ℝ} (ht : 0 ≤ t) :
    t ≤ 1 + t ^ 4 ∧ t ^ 2 ≤ 1 + t ^ 4 ∧ t ^ 3 ≤ 1 + t ^ 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> rcases le_total t 1 with h | h
  · nlinarith [pow_nonneg ht 4]
  · nlinarith [pow_le_pow_left₀ zero_le_one h 3, pow_nonneg ht 3]
  · nlinarith [pow_nonneg ht 4, mul_le_one₀ h ht h]
  · nlinarith [pow_le_pow_left₀ zero_le_one h 2, pow_nonneg ht 2, sq_nonneg (t ^ 2 - 1)]
  · nlinarith [pow_nonneg ht 4, pow_le_one₀ ht h (n := 3)]
  · nlinarith [pow_le_pow_left₀ zero_le_one h 3, pow_nonneg ht 3]

/-- `P'(y) = y R(y)` with `R(y) ≤ 15364 (1 + y⁸)`. -/
theorem hermiteBoundaryPolyDeriv_eq (y : ℝ) :
    hermiteBoundaryPolyDeriv y =
      y * (10 * y ^ 8 - 376 * y ^ 6 + 4122 * y ^ 4 - 14344 * y ^ 2 + 11232) := by
  unfold hermiteBoundaryPolyDeriv; ring

theorem hermiteBoundaryRatio_le (y : ℝ) :
    10 * y ^ 8 - 376 * y ^ 6 + 4122 * y ^ 4 - 14344 * y ^ 2 + 11232 ≤ 15364 * (1 + y ^ 8) := by
  have ht : 0 ≤ y ^ 2 := sq_nonneg y
  obtain ⟨-, h2, -⟩ := pow_le_one_add_pow_four ht
  have e4 : (y ^ 2) ^ 2 = y ^ 4 := by ring
  have e8 : (y ^ 2) ^ 4 = y ^ 8 := by ring
  rw [e4, e8] at h2
  nlinarith [pow_nonneg ht 3, sq_nonneg y, pow_nonneg (sq_nonneg y) 3]

theorem hermiteBoundaryPolySecond_le (y : ℝ) :
    hermiteBoundaryPolySecond y ≤ 31932 * (1 + y ^ 8) := by
  have ht : 0 ≤ y ^ 2 := sq_nonneg y
  obtain ⟨-, h2, -⟩ := pow_le_one_add_pow_four ht
  have e4 : (y ^ 2) ^ 2 = y ^ 4 := by ring
  have e8 : (y ^ 2) ^ 4 = y ^ 8 := by ring
  rw [e4, e8] at h2
  unfold hermiteBoundaryPolySecond
  nlinarith [pow_nonneg ht 3, sq_nonneg y, pow_nonneg (sq_nonneg y) 3]

/-- `P(y) - y¹⁰/2` is bounded below. -/
theorem exists_hermiteBoundaryPoly_lower :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y : ℝ, y ^ 10 / 2 - L ≤ hermiteBoundaryPoly y := by
  set Q : ℝ → ℝ := fun t => t ^ 5 / 2 - 47 * t ^ 4 + 687 * t ^ 3 - 3586 * t ^ 2 + 5616 * t - 1173
  have hQc : ContinuousOn Q (Icc 0 200) := by
    apply Continuous.continuousOn; simp only [Q]; fun_prop
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hQc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, by norm_num⟩)
  have hQ : ∀ t, 0 ≤ t → -B ≤ Q t := by
    intro t ht
    rcases le_or_gt t 200 with h | h
    · have := hB t ⟨ht, h⟩
      rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (Q t)]
    · have h4 : 0 ≤ t ^ 4 := by positivity
      have hA : 53 * t ^ 4 ≤ t ^ 4 * (t / 2 - 47) := by nlinarith
      have ht2 : 40000 ≤ t ^ 2 := by nlinarith
      have hC : 3586 * t ^ 2 + 1173 ≤ 53 * t ^ 4 := by
        have e : t ^ 4 = t ^ 2 * t ^ 2 := by ring
        rw [e]; nlinarith [mul_le_mul_of_nonneg_left ht2 (sq_nonneg t)]
      have hD : 0 ≤ 687 * t ^ 3 + 5616 * t := by positivity
      simp only [Q]
      nlinarith
  refine ⟨B, hB0, fun y => ?_⟩
  have h := hQ (y ^ 2) (sq_nonneg y)
  simp only [Q] at h
  unfold hermiteBoundaryPoly
  nlinarith

/-! ## Small perturbations are dominated -/

/-- The common smallness threshold for the perturbation parameter. -/
def gaussianHermiteThreshold (L : ℝ) : ℝ :=
  1 / (10 * L + 12 * 31932 * (1 + (24 * 31932 + 1) ^ 4) + 1)

theorem gaussianHermiteThreshold_pos {L : ℝ} (hL : 0 ≤ L) : 0 < gaussianHermiteThreshold L := by
  unfold gaussianHermiteThreshold; positivity

private theorem small_perturbation_base {L τ : ℝ} (hL : 0 ≤ L)
    (hP : ∀ y : ℝ, y ^ 10 / 2 - L ≤ hermiteBoundaryPoly y) (hτ : 0 ≤ τ)
    (hτ₀ : τ ≤ gaussianHermiteThreshold L) (y : ℝ) :
    τ * L ≤ 1 / 10 ∧ 1 / 2 + τ * y ^ 10 / 2 ≤ 1 + τ * hermiteBoundaryPoly y ∧
      9 / 10 ≤ 1 + τ * hermiteBoundaryPoly y := by
  set D : ℝ := 10 * L + 12 * 31932 * (1 + (24 * 31932 + 1) ^ 4) + 1
  have hD : 0 < D := by positivity
  have hτD : τ * D ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hτ₀ hD.le
    unfold gaussianHermiteThreshold at this
    rwa [one_div, inv_mul_cancel₀ hD.ne'] at this
  have hτL : τ * L ≤ 1 / 10 := by
    have hX : (0 : ℝ) ≤ 12 * 31932 * (1 + (24 * 31932 + 1) ^ 4) := by positivity
    have : τ * (10 * L) ≤ τ * D := mul_le_mul_of_nonneg_left (by simp only [D]; linarith) hτ
    nlinarith
  have hlow := mul_le_mul_of_nonneg_left (hP y) hτ
  have hy10 : 0 ≤ τ * y ^ 10 := mul_nonneg hτ (by positivity)
  refine ⟨hτL, ?_, ?_⟩ <;> nlinarith

/-- For every perturbation below the threshold, a degree-eight upper bound is dominated by
`(1 + τP)/6`. -/
theorem small_perturbation_dominates {L τ : ℝ} (hL : 0 ≤ L)
    (hP : ∀ y : ℝ, y ^ 10 / 2 - L ≤ hermiteBoundaryPoly y) (hτ : 0 ≤ τ)
    (hτ₀ : τ ≤ gaussianHermiteThreshold L) {y S : ℝ} (hS : S ≤ 31932 * (1 + y ^ 8)) :
    τ * S ≤ (1 + τ * hermiteBoundaryPoly y) / 6 := by
  set K : ℝ := 31932
  set M : ℝ := 24 * K + 1
  set D : ℝ := 10 * L + 12 * K * (1 + M ^ 4) + 1
  have hD : 0 < D := by positivity
  have hτD : τ * D ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hτ₀ hD.le
    unfold gaussianHermiteThreshold at this
    rwa [one_div, inv_mul_cancel₀ hD.ne'] at this
  obtain ⟨-, hbase, -⟩ := small_perturbation_base hL hP hτ hτ₀ y
  have hτS : τ * S ≤ τ * (K * (1 + y ^ 8)) := mul_le_mul_of_nonneg_left hS hτ
  rcases le_or_gt (y ^ 2) M with hy | hy
  · have hy8 : y ^ 8 ≤ M ^ 4 := by
      have : (y ^ 2) ^ 4 ≤ M ^ 4 := pow_le_pow_left₀ (sq_nonneg y) hy 4
      calc y ^ 8 = (y ^ 2) ^ 4 := by ring
        _ ≤ M ^ 4 := this
    have h1 : τ * (K * (1 + y ^ 8)) ≤ τ * (K * (1 + M ^ 4)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hτ
    have h2 : τ * (12 * K * (1 + M ^ 4)) ≤ 1 := by
      have : τ * (12 * K * (1 + M ^ 4)) ≤ τ * D :=
        mul_le_mul_of_nonneg_left (by simp only [D]; nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 10) hL]) hτ
      linarith
    have hy10 : 0 ≤ τ * y ^ 10 := mul_nonneg hτ (by positivity)
    nlinarith
  · have hM1 : 1 ≤ M := by simp only [M, K]; norm_num
    have hy1 : 1 ≤ y ^ 2 := hM1.trans hy.le
    have hy8 : 1 ≤ y ^ 8 := by
      calc (1 : ℝ) = 1 ^ 4 := by norm_num
        _ ≤ (y ^ 2) ^ 4 := pow_le_pow_left₀ zero_le_one hy1 4
        _ = y ^ 8 := by ring
    have h10 : 24 * K * y ^ 8 ≤ y ^ 10 := by
      have : y ^ 10 = y ^ 8 * y ^ 2 := by ring
      rw [this]
      have : 24 * K ≤ y ^ 2 := by simp only [M] at hy; linarith
      nlinarith [pow_nonneg (sq_nonneg y) 4]
    have hK : 0 ≤ K := by simp only [K]; norm_num
    have h3 : τ * (K * (1 + y ^ 8)) ≤ τ * (2 * K * y ^ 8) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hτ
    have h4 : τ * (2 * K * y ^ 8) ≤ τ * y ^ 10 / 12 := by
      have := mul_le_mul_of_nonneg_left h10 hτ
      nlinarith
    nlinarith

/-! ## The perturbed density -/

/-- The Gaussian–Hermite density `ρ_τ(x) = 6 φ(6x)(1 + τP(6x))`. -/
def gaussianHermiteDensity (τ x : ℝ) : ℝ :=
  6 * stdGaussianDensity (6 * x) * (1 + τ * hermiteBoundaryPoly (6 * x))

/-- Its exact derivative. -/
def gaussianHermiteDensityDeriv (τ x : ℝ) : ℝ :=
  6 * (-(36 * x) * stdGaussianDensity (6 * x) * (1 + τ * hermiteBoundaryPoly (6 * x)) +
    stdGaussianDensity (6 * x) * (6 * τ * hermiteBoundaryPolyDeriv (6 * x)))

theorem hasDerivAt_gaussianHermiteDensity (τ x : ℝ) :
    HasDerivAt (gaussianHermiteDensity τ) (gaussianHermiteDensityDeriv τ x) x := by
  have h6 : HasDerivAt (fun x : ℝ => 6 * x) 6 x := by
    simpa using (hasDerivAt_id x).const_mul (6 : ℝ)
  have hφ : HasDerivAt (fun x => stdGaussianDensity (6 * x))
      (-(6 * x) * stdGaussianDensity (6 * x) * 6) x :=
    (hasDerivAt_stdGaussianDensity (6 * x)).comp x h6
  have hP : HasDerivAt (fun x => 1 + τ * hermiteBoundaryPoly (6 * x))
      (τ * (hermiteBoundaryPolyDeriv (6 * x) * 6)) x :=
    (((hasDerivAt_hermiteBoundaryPoly (6 * x)).comp x h6).const_mul τ).const_add 1
  have h := (hφ.const_mul 6).mul hP
  have e : 6 * (-(6 * x) * stdGaussianDensity (6 * x) * 6) * (1 + τ * hermiteBoundaryPoly (6 * x)) +
      6 * stdGaussianDensity (6 * x) * (τ * (hermiteBoundaryPolyDeriv (6 * x) * 6)) =
      gaussianHermiteDensityDeriv τ x := by
    unfold gaussianHermiteDensityDeriv; ring
  rw [e] at h
  exact h

theorem gaussianHermiteDensity_neg (τ x : ℝ) :
    gaussianHermiteDensity τ (-x) = gaussianHermiteDensity τ x := by
  unfold gaussianHermiteDensity
  rw [show 6 * -x = -(6 * x) by ring, stdGaussianDensity_neg, hermiteBoundaryPoly_neg]

theorem gaussianHermiteDensityDeriv_neg (τ x : ℝ) :
    gaussianHermiteDensityDeriv τ (-x) = -gaussianHermiteDensityDeriv τ x := by
  unfold gaussianHermiteDensityDeriv hermiteBoundaryPolyDeriv
  rw [show 6 * -x = -(6 * x) by ring, stdGaussianDensity_neg, hermiteBoundaryPoly_neg]
  ring

theorem continuous_gaussianHermiteDensity (τ : ℝ) : Continuous (gaussianHermiteDensity τ) := by
  unfold gaussianHermiteDensity hermiteBoundaryPoly
  have := continuous_stdGaussianDensity
  fun_prop

theorem continuous_gaussianHermiteDensityDeriv (τ : ℝ) :
    Continuous (gaussianHermiteDensityDeriv τ) := by
  unfold gaussianHermiteDensityDeriv hermiteBoundaryPoly hermiteBoundaryPolyDeriv
  have := continuous_stdGaussianDensity
  fun_prop

theorem integrable_pow_mul_stdGaussianDensity_six (m : ℕ) :
    Integrable fun x : ℝ => x ^ m * stdGaussianDensity (6 * x) := by
  have h := (integrable_pow_mul_stdGaussianDensity m).comp_mul_left' (by norm_num : (6 : ℝ) ≠ 0)
  have hc : ((1 : ℝ) / 6) ^ m * 6 ^ m = 1 := by rw [← mul_pow]; norm_num
  refine (h.const_mul ((1 / 6 : ℝ) ^ m)).congr (Eventually.of_forall fun x => ?_)
  show (1 / 6) ^ m * ((6 * x) ^ m * stdGaussianDensity (6 * x)) = x ^ m * stdGaussianDensity (6 * x)
  rw [mul_pow, ← mul_assoc, ← mul_assoc, hc, one_mul]

/-- Polynomial-times-density integrability. -/
theorem integrable_pow_mul_gaussianHermiteDensity (τ : ℝ) (n : ℕ) :
    Integrable fun x : ℝ => x ^ n * gaussianHermiteDensity τ x := by
  have hint : ∀ m : ℕ, Integrable fun x : ℝ => x ^ m * stdGaussianDensity (6 * x) :=
    integrable_pow_mul_stdGaussianDensity_six
  have e : (fun x : ℝ => x ^ n * gaussianHermiteDensity τ x) = fun x =>
      6 * (x ^ n * stdGaussianDensity (6 * x)) +
      6 * τ * (6 ^ 10 * (x ^ (n + 10) * stdGaussianDensity (6 * x)) -
        47 * 6 ^ 8 * (x ^ (n + 8) * stdGaussianDensity (6 * x)) +
        687 * 6 ^ 6 * (x ^ (n + 6) * stdGaussianDensity (6 * x)) -
        3586 * 6 ^ 4 * (x ^ (n + 4) * stdGaussianDensity (6 * x)) +
        5616 * 6 ^ 2 * (x ^ (n + 2) * stdGaussianDensity (6 * x)) -
        1173 * (x ^ n * stdGaussianDensity (6 * x))) := by
    funext x
    unfold gaussianHermiteDensity hermiteBoundaryPoly
    ring
  rw [e]
  have hpoly : Integrable fun x : ℝ =>
      6 ^ 10 * (x ^ (n + 10) * stdGaussianDensity (6 * x)) -
        47 * 6 ^ 8 * (x ^ (n + 8) * stdGaussianDensity (6 * x)) +
        687 * 6 ^ 6 * (x ^ (n + 6) * stdGaussianDensity (6 * x)) -
        3586 * 6 ^ 4 * (x ^ (n + 4) * stdGaussianDensity (6 * x)) +
        5616 * 6 ^ 2 * (x ^ (n + 2) * stdGaussianDensity (6 * x)) -
        1173 * (x ^ n * stdGaussianDensity (6 * x)) :=
    (((((((hint (n + 10)).const_mul _).sub ((hint (n + 8)).const_mul _)).add
      ((hint (n + 6)).const_mul _)).sub ((hint (n + 4)).const_mul _)).add
      ((hint (n + 2)).const_mul _)).sub ((hint n).const_mul _))
  exact ((hint n).const_mul 6).add (hpoly.const_mul (6 * τ))

theorem integrable_pow_mul_gaussianHermiteDensityDeriv (τ : ℝ) (n : ℕ) :
    Integrable fun x : ℝ => x ^ n * gaussianHermiteDensityDeriv τ x := by
  have hint : ∀ m : ℕ, Integrable fun x : ℝ => x ^ m * stdGaussianDensity (6 * x) :=
    integrable_pow_mul_stdGaussianDensity_six
  have hρ := integrable_pow_mul_gaussianHermiteDensity τ (n + 1)
  have e : (fun x : ℝ => x ^ n * gaussianHermiteDensityDeriv τ x) = fun x =>
      -36 * (x ^ (n + 1) * gaussianHermiteDensity τ x) +
      36 * τ * (10 * 6 ^ 9 * (x ^ (n + 9) * stdGaussianDensity (6 * x)) -
        376 * 6 ^ 7 * (x ^ (n + 7) * stdGaussianDensity (6 * x)) +
        4122 * 6 ^ 5 * (x ^ (n + 5) * stdGaussianDensity (6 * x)) -
        14344 * 6 ^ 3 * (x ^ (n + 3) * stdGaussianDensity (6 * x)) +
        11232 * 6 * (x ^ (n + 1) * stdGaussianDensity (6 * x))) := by
    funext x
    unfold gaussianHermiteDensityDeriv gaussianHermiteDensity hermiteBoundaryPolyDeriv
    ring
  rw [e]
  have hpoly : Integrable fun x : ℝ =>
      10 * 6 ^ 9 * (x ^ (n + 9) * stdGaussianDensity (6 * x)) -
        376 * 6 ^ 7 * (x ^ (n + 7) * stdGaussianDensity (6 * x)) +
        4122 * 6 ^ 5 * (x ^ (n + 5) * stdGaussianDensity (6 * x)) -
        14344 * 6 ^ 3 * (x ^ (n + 3) * stdGaussianDensity (6 * x)) +
        11232 * 6 * (x ^ (n + 1) * stdGaussianDensity (6 * x)) :=
    ((((((hint (n + 9)).const_mul _).sub ((hint (n + 7)).const_mul _)).add
      ((hint (n + 5)).const_mul _)).sub ((hint (n + 3)).const_mul _)).add
      ((hint (n + 1)).const_mul _))
  exact (hρ.const_mul (-36)).add (hpoly.const_mul (36 * τ))

/-- Even moments: `∫ x^{2j} ρ_τ = 6^{-2j}(m_j + τ c_j)`. -/
theorem integral_even_pow_mul_gaussianHermiteDensity (τ : ℝ) (j : ℕ) :
    ∫ x, x ^ (2 * j) * gaussianHermiteDensity τ x =
      (1 / 6) ^ (2 * j) *
        (gaussianEvenWickMoment j + τ * hermiteBoundaryWickCorrection j) := by
  have hint : ∀ m : ℕ, Integrable fun y : ℝ => y ^ m * stdGaussianDensity y :=
    integrable_pow_mul_stdGaussianDensity
  have hmom : ∀ k : ℕ, ∫ y, y ^ (2 * k) * stdGaussianDensity y = gaussianEvenWickMoment k :=
    integral_even_pow_mul_stdGaussianDensity
  have e : (fun x : ℝ => x ^ (2 * j) * gaussianHermiteDensity τ x) = fun x =>
      x ^ (2 * j) * (6 * stdGaussianDensity (6 * x)) * (1 + τ * hermiteBoundaryPoly (6 * x)) := by
    funext x; unfold gaussianHermiteDensity; ring
  rw [e]
  -- substitute and expand the polynomial in the Gaussian variable
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun y : ℝ => (y / 6) ^ (2 * j) * (6 * stdGaussianDensity y) * (1 + τ * hermiteBoundaryPoly y))
    (6 : ℝ)
  have e1 : (fun x : ℝ => (6 * x / 6) ^ (2 * j) * (6 * stdGaussianDensity (6 * x)) *
      (1 + τ * hermiteBoundaryPoly (6 * x))) = fun x =>
      x ^ (2 * j) * (6 * stdGaussianDensity (6 * x)) * (1 + τ * hermiteBoundaryPoly (6 * x)) := by
    funext x; congr 3; field_simp
  rw [e1] at h
  rw [h, abs_of_pos (by norm_num : (0 : ℝ) < 6⁻¹), smul_eq_mul]
  have e2 : (fun y : ℝ => (y / 6) ^ (2 * j) * (6 * stdGaussianDensity y) *
      (1 + τ * hermiteBoundaryPoly y)) = fun y => 6 * (1 / 6) ^ (2 * j) *
      (y ^ (2 * j) * stdGaussianDensity y + τ * (y ^ (2 * (j + 5)) * stdGaussianDensity y -
        47 * (y ^ (2 * (j + 4)) * stdGaussianDensity y) +
        687 * (y ^ (2 * (j + 3)) * stdGaussianDensity y) -
        3586 * (y ^ (2 * (j + 2)) * stdGaussianDensity y) +
        5616 * (y ^ (2 * (j + 1)) * stdGaussianDensity y) -
        1173 * (y ^ (2 * j) * stdGaussianDensity y))) := by
    funext y; unfold hermiteBoundaryPoly
    rw [show y / 6 = y * (1 / 6) by ring, mul_pow]; ring
  set g : ℕ → ℝ → ℝ := fun k y => y ^ (2 * k) * stdGaussianDensity y with hg
  have hgi : ∀ k, Integrable (g k) := fun k => hint (2 * k)
  have hP : Integrable fun y => g (j + 5) y - 47 * g (j + 4) y + 687 * g (j + 3) y -
      3586 * g (j + 2) y + 5616 * g (j + 1) y - 1173 * g j y :=
    (((((hgi _).sub ((hgi _).const_mul _)).add ((hgi _).const_mul _)).sub
      ((hgi _).const_mul _)).add ((hgi _).const_mul _)).sub ((hgi _).const_mul _)
  have hIP : ∫ y, (g (j + 5) y - 47 * g (j + 4) y + 687 * g (j + 3) y -
      3586 * g (j + 2) y + 5616 * g (j + 1) y - 1173 * g j y) =
      hermiteBoundaryWickCorrection j := by
    have h1 : Integrable fun y => g (j + 5) y - 47 * g (j + 4) y :=
      (hgi (j + 5)).sub ((hgi (j + 4)).const_mul 47)
    have h2 : Integrable fun y => g (j + 5) y - 47 * g (j + 4) y + 687 * g (j + 3) y :=
      h1.add ((hgi (j + 3)).const_mul 687)
    have h3 : Integrable fun y => g (j + 5) y - 47 * g (j + 4) y + 687 * g (j + 3) y -
        3586 * g (j + 2) y := h2.sub ((hgi (j + 2)).const_mul 3586)
    have h4 : Integrable fun y => g (j + 5) y - 47 * g (j + 4) y + 687 * g (j + 3) y -
        3586 * g (j + 2) y + 5616 * g (j + 1) y := h3.add ((hgi (j + 1)).const_mul 5616)
    rw [integral_sub h4 ((hgi j).const_mul 1173), integral_add h3 ((hgi _).const_mul _),
      integral_sub h2 ((hgi _).const_mul _), integral_add h1 ((hgi _).const_mul _),
      integral_sub (hgi _) ((hgi _).const_mul _)]
    simp only [integral_const_mul, hg, hmom, hermiteBoundaryWickCorrection]
  rw [e2]
  change 6⁻¹ * ∫ y, 6 * (1 / 6) ^ (2 * j) * (g j y + τ * (g (j + 5) y - 47 * g (j + 4) y +
      687 * g (j + 3) y - 3586 * g (j + 2) y + 5616 * g (j + 1) y - 1173 * g j y)) = _
  rw [integral_const_mul, integral_add (hgi j) (hP.const_mul τ), integral_const_mul, hIP]
  have hgj : ∫ y, g j y = gaussianEvenWickMoment j := hmom j
  rw [hgj]
  ring

theorem integral_gaussianHermiteDensity (τ : ℝ) : ∫ x, gaussianHermiteDensity τ x = 1 := by
  have h := integral_even_pow_mul_gaussianHermiteDensity τ 0
  have hc : hermiteBoundaryWickCorrection 0 = 0 := hermiteBoundaryWickCorrection_exact.1
  simpa [hc, gaussianEvenWickMoment] using h

/-! ## Small-perturbation positivity, score and log-concavity -/

section Small

variable {L τ : ℝ} (hL : 0 ≤ L) (hP : ∀ y : ℝ, y ^ 10 / 2 - L ≤ hermiteBoundaryPoly y)
  (hτ : 0 ≤ τ) (hτ₀ : τ ≤ gaussianHermiteThreshold L)
include hL hP hτ hτ₀

theorem nine_tenths_le_one_add_mul_hermiteBoundaryPoly (y : ℝ) :
    9 / 10 ≤ 1 + τ * hermiteBoundaryPoly y :=
  (small_perturbation_base hL hP hτ hτ₀ y).2.2

/-- `ρ_τ ≥ (9/10) ρ_0`. -/
theorem nine_tenths_mul_le_gaussianHermiteDensity (x : ℝ) :
    9 / 10 * gaussianHermiteDensity 0 x ≤ gaussianHermiteDensity τ x := by
  have h := nine_tenths_le_one_add_mul_hermiteBoundaryPoly hL hP hτ hτ₀ (6 * x)
  have hφ := stdGaussianDensity_pos (6 * x)
  unfold gaussianHermiteDensity
  nlinarith

theorem gaussianHermiteDensity_pos (x : ℝ) : 0 < gaussianHermiteDensity τ x := by
  have h := nine_tenths_le_one_add_mul_hermiteBoundaryPoly hL hP hτ hτ₀ (6 * x)
  have hφ := stdGaussianDensity_pos (6 * x)
  unfold gaussianHermiteDensity
  have : 0 < 1 + τ * hermiteBoundaryPoly (6 * x) := by linarith
  positivity

/-- **Score bound.**  `-ρ_τ' ≥ 30 x ρ_τ` on `x ≥ 0`. -/
theorem thirty_mul_le_neg_gaussianHermiteDensityDeriv {x : ℝ} (hx : 0 ≤ x) :
    30 * x * gaussianHermiteDensity τ x ≤ -gaussianHermiteDensityDeriv τ x := by
  have hS := small_perturbation_dominates hL hP hτ hτ₀ (y := 6 * x)
    ((hermiteBoundaryRatio_le (6 * x)).trans (by nlinarith [pow_nonneg (sq_nonneg (6 * x)) 4]))
  have hφ := stdGaussianDensity_pos (6 * x)
  have hy : 0 ≤ 6 * x := by linarith
  have hkey : τ * hermiteBoundaryPolyDeriv (6 * x) ≤ x * (1 + τ * hermiteBoundaryPoly (6 * x)) := by
    rw [hermiteBoundaryPolyDeriv_eq]
    have := mul_le_mul_of_nonneg_left hS hy
    nlinarith
  unfold gaussianHermiteDensity gaussianHermiteDensityDeriv
  nlinarith [mul_le_mul_of_nonneg_left hkey (le_of_lt (mul_pos (by norm_num : (0:ℝ) < 36) hφ))]

/-- The score-defect density `ρ - 16xρ' - 303x²ρ`. -/
def gaussianHermiteDefectDensity (τ x : ℝ) : ℝ :=
  gaussianHermiteDensity τ x - 16 * x * gaussianHermiteDensityDeriv τ x -
    303 * x ^ 2 * gaussianHermiteDensity τ x

omit hL hP hτ hτ₀ in
theorem gaussianHermiteDefectDensity_neg (τ x : ℝ) :
    gaussianHermiteDefectDensity τ (-x) = gaussianHermiteDefectDensity τ x := by
  unfold gaussianHermiteDefectDensity
  rw [gaussianHermiteDensity_neg, gaussianHermiteDensityDeriv_neg]
  ring

/-- **Score defect.**  `ρ - 16xρ' - 303x²ρ ≥ (1 + 177x²) ρ` on `x ≥ 0`. -/
theorem one_add_mul_le_gaussianHermiteDefectDensity {x : ℝ} (hx : 0 ≤ x) :
    (1 + 177 * x ^ 2) * gaussianHermiteDensity τ x ≤ gaussianHermiteDefectDensity τ x := by
  have h := thirty_mul_le_neg_gaussianHermiteDensityDeriv hL hP hτ hτ₀ hx
  have h2 := mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hx)
  unfold gaussianHermiteDefectDensity
  nlinarith

/-- The logarithmic derivative `(log ρ_τ)' = -36x + 6τP'(6x)/(1 + τP(6x))`. -/
def gaussianHermiteLogDeriv (τ x : ℝ) : ℝ :=
  -(36 * x) + 6 * τ * hermiteBoundaryPolyDeriv (6 * x) / (1 + τ * hermiteBoundaryPoly (6 * x))

theorem hasDerivAt_log_gaussianHermiteDensity (x : ℝ) :
    HasDerivAt (fun x => Real.log (gaussianHermiteDensity τ x)) (gaussianHermiteLogDeriv τ x) x := by
  have hpos := gaussianHermiteDensity_pos hL hP hτ hτ₀ x
  have h := (hasDerivAt_gaussianHermiteDensity τ x).log hpos.ne'
  have hu := nine_tenths_le_one_add_mul_hermiteBoundaryPoly hL hP hτ hτ₀ (6 * x)
  have hφ := stdGaussianDensity_pos (6 * x)
  have e : gaussianHermiteDensityDeriv τ x / gaussianHermiteDensity τ x =
      gaussianHermiteLogDeriv τ x := by
    unfold gaussianHermiteDensityDeriv gaussianHermiteDensity gaussianHermiteLogDeriv
    have : 1 + τ * hermiteBoundaryPoly (6 * x) ≠ 0 := by linarith
    field_simp
  rw [e] at h
  exact h

theorem hasDerivAt_gaussianHermiteLogDeriv (x : ℝ) :
    HasDerivAt (gaussianHermiteLogDeriv τ)
      (-36 + 36 * τ * (hermiteBoundaryPolySecond (6 * x) * (1 + τ * hermiteBoundaryPoly (6 * x)) -
        τ * hermiteBoundaryPolyDeriv (6 * x) ^ 2) / (1 + τ * hermiteBoundaryPoly (6 * x)) ^ 2) x := by
  have hu := nine_tenths_le_one_add_mul_hermiteBoundaryPoly hL hP hτ hτ₀ (6 * x)
  have hune : 1 + τ * hermiteBoundaryPoly (6 * x) ≠ 0 := by linarith
  have h6 : HasDerivAt (fun x : ℝ => 6 * x) 6 x := by
    simpa using (hasDerivAt_id x).const_mul (6 : ℝ)
  have hN : HasDerivAt (fun x => 6 * τ * hermiteBoundaryPolyDeriv (6 * x))
      (6 * τ * (hermiteBoundaryPolySecond (6 * x) * 6)) x :=
    ((hasDerivAt_hermiteBoundaryPolyDeriv (6 * x)).comp x h6).const_mul (6 * τ)
  have hD : HasDerivAt (fun x => 1 + τ * hermiteBoundaryPoly (6 * x))
      (τ * (hermiteBoundaryPolyDeriv (6 * x) * 6)) x :=
    (((hasDerivAt_hermiteBoundaryPoly (6 * x)).comp x h6).const_mul τ).const_add 1
  have h0 : HasDerivAt (fun x : ℝ => 36 * x) 36 x := by
    simpa using (hasDerivAt_id x).const_mul (36 : ℝ)
  have h36 := h0.neg
  have h := h36.add (hN.div hD hune)
  have e : -36 + (6 * τ * (hermiteBoundaryPolySecond (6 * x) * 6) *
      (1 + τ * hermiteBoundaryPoly (6 * x)) - 6 * τ * hermiteBoundaryPolyDeriv (6 * x) *
        (τ * (hermiteBoundaryPolyDeriv (6 * x) * 6))) / (1 + τ * hermiteBoundaryPoly (6 * x)) ^ 2 =
      -36 + 36 * τ * (hermiteBoundaryPolySecond (6 * x) * (1 + τ * hermiteBoundaryPoly (6 * x)) -
        τ * hermiteBoundaryPolyDeriv (6 * x) ^ 2) / (1 + τ * hermiteBoundaryPoly (6 * x)) ^ 2 := by
    ring
  rw [e] at h
  exact h

/-- **Strong log-concavity.**  `-(log ρ_τ)'' ≥ 30` everywhere. -/
theorem thirty_le_neg_deriv_deriv_log_gaussianHermiteDensity (x : ℝ) :
    30 ≤ -deriv (deriv fun x => Real.log (gaussianHermiteDensity τ x)) x := by
  have hd : deriv (fun x => Real.log (gaussianHermiteDensity τ x)) = gaussianHermiteLogDeriv τ :=
    funext fun x => (hasDerivAt_log_gaussianHermiteDensity hL hP hτ hτ₀ x).deriv
  rw [hd, (hasDerivAt_gaussianHermiteLogDeriv hL hP hτ hτ₀ x).deriv]
  set u := 1 + τ * hermiteBoundaryPoly (6 * x)
  have hu : 9 / 10 ≤ u := nine_tenths_le_one_add_mul_hermiteBoundaryPoly hL hP hτ hτ₀ (6 * x)
  have hupos : 0 < u := by linarith
  have hS : τ * hermiteBoundaryPolySecond (6 * x) ≤ u / 6 :=
    small_perturbation_dominates hL hP hτ hτ₀ (hermiteBoundaryPolySecond_le (6 * x))
  have hsq : 0 ≤ τ * hermiteBoundaryPolyDeriv (6 * x) ^ 2 * τ :=
    mul_nonneg (mul_nonneg hτ (sq_nonneg _)) hτ
  have key : 36 * τ * (hermiteBoundaryPolySecond (6 * x) * u - τ * hermiteBoundaryPolyDeriv (6 * x) ^ 2) /
      u ^ 2 ≤ 6 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end Small

/-! ## Moments of the score-defect density -/

/-- Integration by parts: `∫ x^{2k+1} ρ_τ' = -(2k+1) ∫ x^{2k} ρ_τ`. -/
theorem integral_pow_mul_gaussianHermiteDensityDeriv (τ : ℝ) (k : ℕ) :
    ∫ x, x ^ (2 * k + 1) * gaussianHermiteDensityDeriv τ x =
      -((2 * k + 1) * ∫ x, x ^ (2 * k) * gaussianHermiteDensity τ x) := by
  have hu : ∀ x ∈ tsupport (gaussianHermiteDensity τ),
      HasDerivAt (fun x : ℝ => x ^ (2 * k + 1)) (((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k)) x := by
    intro x _
    simpa using hasDerivAt_pow (2 * k + 1) x
  have hv : ∀ x ∈ tsupport (fun x : ℝ => x ^ (2 * k + 1)),
      HasDerivAt (gaussianHermiteDensity τ) (gaussianHermiteDensityDeriv τ x) x :=
    fun x _ => hasDerivAt_gaussianHermiteDensity τ x
  have h1 : Integrable ((fun x : ℝ => x ^ (2 * k + 1)) * gaussianHermiteDensityDeriv τ) :=
    integrable_pow_mul_gaussianHermiteDensityDeriv τ (2 * k + 1)
  have h2 : Integrable ((fun x : ℝ => ((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k)) *
      gaussianHermiteDensity τ) :=
    ((integrable_pow_mul_gaussianHermiteDensity τ (2 * k)).const_mul ((2 * k + 1 : ℕ) : ℝ)).congr
      (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have h3 : Integrable ((fun x : ℝ => x ^ (2 * k + 1)) * gaussianHermiteDensity τ) :=
    integrable_pow_mul_gaussianHermiteDensity τ (2 * k + 1)
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable hu hv h1 h2 h3
  rw [h, ← integral_const_mul]
  congr 1
  congr 1
  funext x
  push_cast
  ring

/-- The even moments of the score-defect density are the score gaps
`(32k+17)M_k - 303M_{k+1}` of the density moments `M_k = ∫ x^{2k} ρ_τ`. -/
theorem integral_even_pow_mul_gaussianHermiteDefectDensity (τ : ℝ) (k : ℕ) :
    ∫ x, x ^ (2 * k) * gaussianHermiteDefectDensity τ x =
      (32 * k + 17) * (∫ x, x ^ (2 * k) * gaussianHermiteDensity τ x) -
        303 * ∫ x, x ^ (2 * (k + 1)) * gaussianHermiteDensity τ x := by
  have hA := integrable_pow_mul_gaussianHermiteDensity τ (2 * k)
  have hB := integrable_pow_mul_gaussianHermiteDensityDeriv τ (2 * k + 1)
  have hC := integrable_pow_mul_gaussianHermiteDensity τ (2 * (k + 1))
  have e : (fun x => x ^ (2 * k) * gaussianHermiteDefectDensity τ x) = fun x =>
      x ^ (2 * k) * gaussianHermiteDensity τ x -
        16 * (x ^ (2 * k + 1) * gaussianHermiteDensityDeriv τ x) -
        303 * (x ^ (2 * (k + 1)) * gaussianHermiteDensity τ x) := by
    funext x; unfold gaussianHermiteDefectDensity; ring
  have hAB : Integrable fun x : ℝ => x ^ (2 * k) * gaussianHermiteDensity τ x -
      16 * (x ^ (2 * k + 1) * gaussianHermiteDensityDeriv τ x) := hA.sub (hB.const_mul 16)
  rw [e, integral_sub hAB (hC.const_mul 303),
    integral_sub hA (hB.const_mul 16), integral_const_mul, integral_const_mul,
    integral_pow_mul_gaussianHermiteDensityDeriv]
  ring

theorem integrable_pow_mul_gaussianHermiteDefectDensity (τ : ℝ) (n : ℕ) :
    Integrable fun x : ℝ => x ^ n * gaussianHermiteDefectDensity τ x := by
  have hA := integrable_pow_mul_gaussianHermiteDensity τ n
  have hB := integrable_pow_mul_gaussianHermiteDensityDeriv τ (n + 1)
  have hC := integrable_pow_mul_gaussianHermiteDensity τ (n + 2)
  refine ((hA.sub (hB.const_mul 16)).sub (hC.const_mul 303)).congr
    (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  unfold gaussianHermiteDefectDensity
  ring

end RHTower
