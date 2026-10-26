import GaloisForLFunctions.ArithmeticCorrelationGeometry.AlmostEveryGaugePointCancelsToTheSquareRoot

/-!
# Successor correlations cancel to the square root almost surely

The twisted successor correlation `Σ_{n ≤ N} (χ_x a)(n) · conj((χ_x a)(n+h))` is gauge charged
(`SuccessorCorrelationsArePureGaugeCharge`): its terms are the characters of the ratios
`n/(n+h)`, which are distinct. So they form an orthonormal system on the gauge torus
(`integral_succMonomial_mul_conj`), and so do the terms `χ_x(n(n+h))` of the unconjugated pattern
(`integral_prodMonomial_mul_conj`). The Rademacher–Menshov law of
`AlmostEveryGaugePointCancelsToTheSquareRoot` applies to both.

* **Almost-sure square-root Chowla at every shift** (`ae_succCorr_sqrt_law`,
  `ae_prodCorr_sqrt_law`). For every source bounded by one, at Haar-almost every gauge point,
  simultaneously for all shifts `h ≥ 1`, both successor patterns of the twisted source satisfy
  `|Σ_{n ≤ N} ·| ≤ C_{x,h} √(N+1) (1 + log(N+1))²`.
* **The Möbius orbit** (`ae_moebius_chowla`). For Haar-almost every twist `f = μχ_x` of the Möbius
  function, `Σ_{n ≤ N} f(n) conj f(n+h)` and `Σ_{n ≤ N} f(n) f(n+h)` are `O(√N log² N)` for every
  `h ≥ 1`. At the gauge point `0` both are `Σ_{n ≤ N} μ(n)μ(n+h)`: the two-point Chowla conjecture
  at square-root scale.

Gauge status: two-point Chowla at square-root scale is a Haar-full property of the Möbius gauge
orbit; its truth for `μ` is the typicality of the point `0`. The sizes are gauge invariant (P4),
the values are not.
-/

open MeasureTheory Finset Filter
open scoped ComplexConjugate ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

/-- The successor monomial `χ_x(n) conj χ_x(n+h)`. -/
def succMonomial (h n : ℕ) (x : GaugeTorus) : ℂ := twist x n * conj (twist x (n + h))

/-- The unconjugated successor monomial `χ_x(n) χ_x(n+h) = χ_x(n(n+h))`. -/
def prodMonomial (h n : ℕ) (x : GaugeTorus) : ℂ := twist x n * twist x (n + h)

theorem continuous_succMonomial (h n : ℕ) : Continuous (succMonomial h n) :=
  (continuous_twist n).mul (Complex.continuous_conj.comp (continuous_twist (n + h)))

theorem continuous_prodMonomial (h n : ℕ) : Continuous (prodMonomial h n) :=
  (continuous_twist n).mul (continuous_twist (n + h))

theorem norm_succMonomial (h n : ℕ) (x : GaugeTorus) : ‖succMonomial h n x‖ = 1 := by
  rw [succMonomial, norm_mul, Complex.norm_conj, norm_twist, norm_twist, mul_one]

theorem norm_prodMonomial (h n : ℕ) (x : GaugeTorus) : ‖prodMonomial h n x‖ = 1 := by
  rw [prodMonomial, norm_mul, norm_twist, norm_twist, mul_one]

/-- **Successor monomials are orthonormal**: distinct successor pairs have distinct ratios. -/
theorem integral_succMonomial_mul_conj {h : ℕ} (hh : 1 ≤ h) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ∫ x, succMonomial h m x * conj (succMonomial h n x) ∂gaugeHaar = if m = n then 1 else 0 := by
  have hm' : m + h ≠ 0 := by omega
  have hn' : n + h ≠ 0 := by omega
  have hprod : ∀ x, succMonomial h m x * conj (succMonomial h n x) =
      twist x (m * (n + h)) * conj (twist x (n * (m + h))) := by
    intro x
    simp only [succMonomial, map_mul, Complex.conj_conj, twist_mul x hm hn', twist_mul x hn hm']
    ring
  simp_rw [hprod]
  rw [integral_twist_mul_conj (Nat.mul_ne_zero hm hn') (Nat.mul_ne_zero hn hm')]
  congr 1
  apply propext
  constructor
  · intro heq
    have : m * h = n * h := by nlinarith
    exact Nat.eq_of_mul_eq_mul_right hh this
  · rintro rfl; ring

/-- **Unconjugated successor monomials are orthonormal**: `n ↦ n(n+h)` is injective. -/
theorem integral_prodMonomial_mul_conj (h : ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ∫ x, prodMonomial h m x * conj (prodMonomial h n x) ∂gaugeHaar = if m = n then 1 else 0 := by
  have hprod : ∀ x, prodMonomial h m x * conj (prodMonomial h n x) =
      twist x (m * (m + h)) * conj (twist x (n * (n + h))) := by
    intro x
    simp only [prodMonomial, twist_mul x hm (by omega : m + h ≠ 0),
      twist_mul x hn (by omega : n + h ≠ 0)]
  simp_rw [hprod]
  rw [integral_twist_mul_conj (Nat.mul_ne_zero hm (by omega)) (Nat.mul_ne_zero hn (by omega))]
  congr 1
  apply propext
  constructor
  · intro heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : m * (m + h) < n * (n + h) := Nat.mul_lt_mul'' hlt (by omega)
      omega
    · have : n * (n + h) < m * (m + h) := Nat.mul_lt_mul'' hlt (by omega)
      omega
  · rintro rfl; rfl

/-- **Almost-sure square-root law for the conjugate successor pattern, at every shift.** -/
theorem ae_succCorr_sqrt_law (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ∀ᵐ x ∂gaugeHaar, ∀ h : ℕ, 1 ≤ h → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖∑ n ∈ Ioc 0 N, a n * twist x n * conj (a (n + h) * twist x (n + h))‖ ≤
        C * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2 := by
  rw [ae_all_iff]
  intro h
  by_cases hh : 1 ≤ h
  · have hlaw := ae_exists_norm_orthoSum_le (P := gaugeHaar) (e := succMonomial h)
      (fun n => (continuous_succMonomial h n).measurable)
      (fun n x => (norm_succMonomial h n x).le)
      (fun m n hm hn => integral_succMonomial_mul_conj hh hm hn)
      (fun n => a n * conj (a (n + h)))
      (fun n => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_one₀ (ha n) (norm_nonneg _) (ha (n + h)))
    filter_upwards [hlaw] with x ⟨C, hC, hb⟩ _
    refine ⟨C, hC, fun N => ?_⟩
    have := hb N
    simp only [orthoSum, succMonomial] at this
    convert this using 2
    refine sum_congr rfl fun n _ => ?_
    rw [map_mul]
    ring
  · exact Eventually.of_forall fun x h1 => absurd h1 hh

/-- **Almost-sure square-root law for the unconjugated successor pattern, at every shift.** -/
theorem ae_prodCorr_sqrt_law (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    ∀ᵐ x ∂gaugeHaar, ∀ h : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖∑ n ∈ Ioc 0 N, a n * twist x n * (a (n + h) * twist x (n + h))‖ ≤
        C * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2 := by
  rw [ae_all_iff]
  intro h
  have hlaw := ae_exists_norm_orthoSum_le (P := gaugeHaar) (e := prodMonomial h)
    (fun n => (continuous_prodMonomial h n).measurable)
    (fun n x => (norm_prodMonomial h n x).le)
    (fun m n hm hn => integral_prodMonomial_mul_conj h hm hn)
    (fun n => a n * a (n + h))
    (fun n => by
      rw [norm_mul]
      exact mul_le_one₀ (ha n) (norm_nonneg _) (ha (n + h)))
  filter_upwards [hlaw] with x ⟨C, hC, hb⟩
  refine ⟨C, hC, fun N => ?_⟩
  have := hb N
  simp only [orthoSum, prodMonomial] at this
  convert this using 2
  refine sum_congr rfl fun n _ => ?_
  ring

/-- **Square-root Chowla on almost all of the Möbius gauge orbit.** For Haar-almost every twist
`f = μχ_x`, both two-point correlations `Σ f(n) conj f(n+h)` and `Σ f(n) f(n+h)` are
`O(√N log² N)` at every shift `h ≥ 1`. -/
theorem ae_moebius_chowla :
    ∀ᵐ x ∂gaugeHaar, ∀ h : ℕ, 1 ≤ h →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
        ‖∑ n ∈ Ioc 0 N, ((μ n : ℤ) : ℂ) * twist x n * conj (((μ (n + h) : ℤ) : ℂ) *
          twist x (n + h))‖ ≤ C * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
        ‖∑ n ∈ Ioc 0 N, ((μ n : ℤ) : ℂ) * twist x n * (((μ (n + h) : ℤ) : ℂ) *
          twist x (n + h))‖ ≤ C * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2) := by
  have hμ : ∀ n, ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := fun n => by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  filter_upwards [ae_succCorr_sqrt_law _ hμ, ae_prodCorr_sqrt_law _ hμ] with x h1 h2 h hh
  exact ⟨h1 h hh, h2 h⟩

/-- At the gauge point `0` both patterns are the untwisted Möbius correlation `Σ μ(n)μ(n+h)`. -/
theorem moebius_chowla_at_zero (h N : ℕ) :
    ∑ n ∈ Ioc 0 N, ((μ n : ℤ) : ℂ) * twist 0 n * conj (((μ (n + h) : ℤ) : ℂ) * twist 0 (n + h)) =
      ((∑ n ∈ Ioc 0 N, (μ n * μ (n + h) : ℤ) : ℤ) : ℂ) := by
  push_cast
  refine sum_congr rfl fun n _ => ?_
  rw [twist_zero, twist_zero, mul_one, mul_one, Complex.conj_intCast]

end GaloisForLFunctions.ArithmeticCorrelationGeometry
