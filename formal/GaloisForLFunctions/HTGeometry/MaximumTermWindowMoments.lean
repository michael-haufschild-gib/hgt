import GaloisForLFunctions.HTGeometry.GutzmerEntire

/-!
# Window sums against the maximum modulus

Bessel's inequality on a circle says the terms of a power series have `l²` norm at most the maximum
modulus.  Cauchy--Schwarz then turns any *finite* window of terms into a bound by the square root of
its cardinality times that modulus:

`∑_{n ∈ s} |a_n| r^n ≤ sqrt(card s) · sup_θ |f(r e^{iθ})|`.

This is the estimate that the maximum-term inequality `|a_n| r^n ≤ mu(r)` cannot give.  Its content
is that the terms of a window cannot all be as large as the maximum term unless the value is
correspondingly large: a window of `k` comparable terms forces the modulus up by `sqrt k`.  In the
Wiman--Valiron estimate this is exactly the factor that converts a bound of the order of the central
index into one of the order of its square root.
-/

open MeasureTheory Complex

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ} {r : ℝ}

/-- **A window of terms against the maximum modulus.**  Over any finite set of indices the sum of the
terms is at most the square root of the number of indices times a bound for `‖f‖` on the circle. -/
theorem sum_window_le_sqrt_card_mul_bound
    (ha : EntireCoeffs a) (hr0 : 0 ≤ r) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ θ : ℝ, ‖coeffFun a (circleMap 0 r θ)‖ ≤ M) (s : Finset ℕ) :
    ∑ n ∈ s, ‖a n‖ * r ^ n ≤ Real.sqrt (s.card) * M := by
  classical
  have hbessel := tsum_normSq_coeff_le_of_bound ha hr0 hM0 hM
  have hsummable : Summable fun k : ℕ => ‖a k‖ ^ (2 : ℕ) * r ^ (2 * k) :=
    (hasSum_gutzmer_coeffFun ha hr0).summable
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ ‖a n‖ ^ (2 : ℕ) * r ^ (2 * n) := fun n => by positivity
  -- the window's `l²` mass is below the total
  have hpart : ∑ n ∈ s, ‖a n‖ ^ (2 : ℕ) * r ^ (2 * n) ≤ M ^ (2 : ℕ) :=
    le_trans (Summable.sum_le_tsum s (fun n _ => hnn n) hsummable) hbessel
  -- Cauchy--Schwarz against the constant one
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun n => ‖a n‖ * r ^ n)
  have hone : ∑ _n ∈ s, (1 : ℝ) ^ (2 : ℕ) = (s.card : ℝ) := by
    simp
  have hsq : ∀ n : ℕ, (‖a n‖ * r ^ n) ^ (2 : ℕ) = ‖a n‖ ^ (2 : ℕ) * r ^ (2 * n) := by
    intro n
    rw [mul_pow, ← pow_mul]
    ring_nf
  have hprod : ∀ n : ℕ, (1 : ℝ) * (‖a n‖ * r ^ n) = ‖a n‖ * r ^ n := fun n => one_mul _
  rw [Finset.sum_congr rfl (fun n _ => hprod n), hone,
    Finset.sum_congr rfl (fun n _ => hsq n)] at hCS
  have hcard : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hchain : (∑ n ∈ s, ‖a n‖ * r ^ n) ^ (2 : ℕ) ≤ (s.card : ℝ) * M ^ (2 : ℕ) := by
    refine le_trans hCS ?_
    exact mul_le_mul_of_nonneg_left hpart hcard
  have hsum_nn : (0 : ℝ) ≤ ∑ n ∈ s, ‖a n‖ * r ^ n :=
    Finset.sum_nonneg fun n _ => by positivity
  have hsqrt : Real.sqrt (s.card) * M = Real.sqrt ((s.card : ℝ) * M ^ (2 : ℕ)) := by
    rw [Real.sqrt_mul hcard, Real.sqrt_sq hM0]
  rw [hsqrt]
  have hnonneg : (0 : ℝ) ≤ (s.card : ℝ) * M ^ (2 : ℕ) := by positivity
  nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg ((s.card : ℝ) * M ^ (2 : ℕ)), hchain, hsum_nn]

/-- **The same bound for the normalised coefficients.**  Dividing by the central term turns the
window bound into a statement about the profile: a window of `k` indices carries `l¹` mass at most
`sqrt k` times the normalised modulus of the value. -/
theorem sum_window_normalised_le_sqrt_card
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    (hmax : ∀ θ : ℝ, ‖coeffFun a (circleMap 0 r θ)‖ ≤ ‖coeffFun a z‖) (s : Finset ℕ) :
    ∑ n ∈ s, ‖normalisedCoeff a r z n‖
      ≤ Real.sqrt (s.card) * (‖coeffFun a z‖ / maxTerm a r) := by
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  have hCn : ‖a (centralIndex a r) * z ^ centralIndex a r‖ = maxTerm a r := by
    rw [norm_mul, norm_pow, hz]
    exact term_centralIndex_eq ha hr hn₀
  have hrw : ∀ n : ℕ, ‖normalisedCoeff a r z n‖ = (‖a n‖ * r ^ n) / maxTerm a r := by
    intro n
    rw [normalisedCoeff_def, norm_div, hCn, norm_mul, norm_pow, hz]
  rw [Finset.sum_congr rfl (fun n _ => hrw n), ← Finset.sum_div]
  calc (∑ n ∈ s, ‖a n‖ * r ^ n) / maxTerm a r
      ≤ (Real.sqrt (s.card) * ‖coeffFun a z‖) / maxTerm a r :=
        div_le_div_of_nonneg_right
          (sum_window_le_sqrt_card_mul_bound ha hr.le (norm_nonneg _) hmax s) hμpos.le
    _ = Real.sqrt (s.card) * (‖coeffFun a z‖ / maxTerm a r) := by rw [mul_div_assoc]

end GaloisForLFunctions.HTGeometry
