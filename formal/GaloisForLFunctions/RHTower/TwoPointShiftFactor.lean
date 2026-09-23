import GaloisForLFunctions.RHTower.MellinContinuationOrder

/-!
# The rational factor `(s − ρ₁)(s − ρ₂)/(s(s − 1))`

Burnol's Proposition 6.5 omits two top-order evaluators from the list; the Mellin transform of a
Sonine function orthogonal to what remains is `s(s − 1)ζ(s)θ(s)/((s − ρ₁)(s − ρ₂))` with `θ` entire.
The rational factor that produces `θ` is collected here: it is analytic away from `0` and `1`, its
order is the difference of the orders of its numerator and denominator, and — this is what makes
the growth argument work — it is *bounded* on the complement of the unit discs around `0` and `1`,
because it tends to `1` at infinity.

## Main results

* `twoPointShift`
* `meromorphicOrderAt_twoPointShift`
* `exists_bound_twoPointShift`
-/

open Complex Set Topology Filter

namespace RHTower

noncomputable section

/-- The rational factor `(s − ρ₁)(s − ρ₂)/(s(s − 1))`. -/
def twoPointShift (ρ₁ ρ₂ : ℂ) : ℂ → ℂ := fun s => (s - ρ₁) * (s - ρ₂) / (s * (s - 1))

/-- The numerator of the rational factor. -/
def twoPointNumer (ρ₁ ρ₂ : ℂ) : ℂ → ℂ := fun s => (s - ρ₁) * (s - ρ₂)

/-- The denominator `s(s − 1)` of the rational factor. -/
def twoPointDenom : ℂ → ℂ := fun s => s * (s - 1)

theorem analyticAt_twoPointNumer (ρ₁ ρ₂ : ℂ) (z : ℂ) : AnalyticAt ℂ (twoPointNumer ρ₁ ρ₂) z :=
  (analyticAt_id.sub analyticAt_const).mul (analyticAt_id.sub analyticAt_const)

theorem analyticAt_twoPointDenom (z : ℂ) : AnalyticAt ℂ twoPointDenom z :=
  analyticAt_id.mul (analyticAt_id.sub analyticAt_const)

theorem twoPointShift_eq_div (ρ₁ ρ₂ : ℂ) :
    twoPointShift ρ₁ ρ₂ = twoPointNumer ρ₁ ρ₂ / twoPointDenom := by
  funext s
  rfl

theorem analyticAt_twoPointShift {ρ₁ ρ₂ z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    AnalyticAt ℂ (twoPointShift ρ₁ ρ₂) z := by
  rw [twoPointShift_eq_div]
  refine (analyticAt_twoPointNumer ρ₁ ρ₂ z).div (analyticAt_twoPointDenom z) ?_
  exact mul_ne_zero h0 (sub_ne_zero.2 h1)

theorem meromorphicAt_twoPointShift (ρ₁ ρ₂ : ℂ) (z : ℂ) :
    MeromorphicAt (twoPointShift ρ₁ ρ₂) z := by
  rw [twoPointShift_eq_div]
  exact (analyticAt_twoPointNumer ρ₁ ρ₂ z).meromorphicAt.div
    (analyticAt_twoPointDenom z).meromorphicAt

theorem meromorphicOrderAt_twoPointShift (ρ₁ ρ₂ z : ℂ) :
    meromorphicOrderAt (twoPointShift ρ₁ ρ₂) z
      = meromorphicOrderAt (twoPointNumer ρ₁ ρ₂) z - meromorphicOrderAt twoPointDenom z := by
  rw [twoPointShift_eq_div,
    meromorphicOrderAt_div (analyticAt_twoPointNumer ρ₁ ρ₂ z).meromorphicAt
      (analyticAt_twoPointDenom z).meromorphicAt]

theorem meromorphicOrderAt_twoPointDenom_zero :
    meromorphicOrderAt twoPointDenom 0 = ((1 : ℤ) : WithTop ℤ) := by
  have hord : analyticOrderAt twoPointDenom 0 = ((1 : ℕ) : ℕ∞) := by
    refine ((analyticAt_twoPointDenom 0).analyticOrderAt_eq_natCast).2 ?_
    refine ⟨fun s : ℂ => s - 1, analyticAt_id.sub analyticAt_const, by norm_num, ?_⟩
    filter_upwards with s
    simp [twoPointDenom]
  rw [(analyticAt_twoPointDenom 0).meromorphicOrderAt_eq, hord]
  simp

theorem meromorphicOrderAt_twoPointDenom_one :
    meromorphicOrderAt twoPointDenom 1 = ((1 : ℤ) : WithTop ℤ) := by
  have hord : analyticOrderAt twoPointDenom 1 = ((1 : ℕ) : ℕ∞) := by
    refine ((analyticAt_twoPointDenom 1).analyticOrderAt_eq_natCast).2 ?_
    refine ⟨fun s : ℂ => s, analyticAt_id, by norm_num, ?_⟩
    filter_upwards with s
    simp [twoPointDenom]
    ring
  rw [(analyticAt_twoPointDenom 1).meromorphicOrderAt_eq, hord]
  simp

theorem meromorphicOrderAt_twoPointDenom_of_ne {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) :
    meromorphicOrderAt twoPointDenom z = (0 : WithTop ℤ) := by
  have hne : twoPointDenom z ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 h1)
  rw [(analyticAt_twoPointDenom z).meromorphicOrderAt_eq,
    (analyticAt_twoPointDenom z).analyticOrderAt_eq_zero.2 hne]
  simp

theorem zero_le_meromorphicOrderAt_twoPointNumer (ρ₁ ρ₂ z : ℂ) :
    (0 : WithTop ℤ) ≤ meromorphicOrderAt (twoPointNumer ρ₁ ρ₂) z := by
  rw [(analyticAt_twoPointNumer ρ₁ ρ₂ z).meromorphicOrderAt_eq]
  induction analyticOrderAt (twoPointNumer ρ₁ ρ₂) z with
  | top => simp
  | coe n => simp

/-- **The rational factor is bounded off the unit discs around `0` and `1`**: it tends to `1` at
infinity, and the two excluded discs contain both poles. -/
theorem exists_bound_twoPointShift (ρ₁ ρ₂ : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 ≤ ‖s‖ → 1 ≤ ‖s - 1‖ → ‖twoPointShift ρ₁ ρ₂ s‖ ≤ C := by
  set r : ℝ := max ‖ρ₁‖ ‖ρ₂‖ with hrdef
  have hr0 : 0 ≤ r := le_trans (norm_nonneg ρ₁) (le_max_left _ _)
  refine ⟨(3 + r) ^ (2 : ℕ) + 2 * (1 + r) ^ (2 : ℕ), by positivity, ?_⟩
  intro s hs hs1
  have hs0 : (0 : ℝ) < ‖s‖ := by linarith
  have hs1' : (0 : ℝ) < ‖s - 1‖ := by linarith
  have h1 : ‖s - ρ₁‖ ≤ ‖s‖ + r :=
    le_trans (norm_sub_le s ρ₁) (by gcongr; exact le_max_left _ _)
  have h2 : ‖s - ρ₂‖ ≤ ‖s‖ + r :=
    le_trans (norm_sub_le s ρ₂) (by gcongr; exact le_max_right _ _)
  have hnorm : ‖twoPointShift ρ₁ ρ₂ s‖ = ‖s - ρ₁‖ * ‖s - ρ₂‖ / (‖s‖ * ‖s - 1‖) := by
    rw [twoPointShift, norm_div, norm_mul, norm_mul]
  rw [hnorm, div_le_iff₀ (by positivity)]
  have hprod : ‖s - ρ₁‖ * ‖s - ρ₂‖ ≤ (‖s‖ + r) ^ (2 : ℕ) := by
    have := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    nlinarith [this]
  rcases le_or_gt ‖s‖ 3 with hle | hgt
  · have hb : (‖s‖ + r) ^ (2 : ℕ) ≤ (3 + r) ^ (2 : ℕ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs1 (le_of_lt hs0), sq_nonneg (1 + r)]
  · have hsub : ‖s‖ - 1 ≤ ‖s - 1‖ := by
      have := norm_sub_norm_le s 1
      simpa using this
    have hbig : (2 / 3 : ℝ) * ‖s‖ ≤ ‖s - 1‖ := by linarith
    have hlin : ‖s‖ + r ≤ ‖s‖ * (1 + r) := by nlinarith
    have hnum : (‖s‖ + r) ^ (2 : ℕ) ≤ ‖s‖ ^ (2 : ℕ) * (1 + r) ^ (2 : ℕ) := by
      have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ‖s‖ + r) hlin 2
      rw [mul_pow] at h
      exact h
    have hden : (2 / 3 : ℝ) * ‖s‖ ^ (2 : ℕ) ≤ ‖s‖ * ‖s - 1‖ := by nlinarith
    have hC : (0:ℝ) ≤ (3 + r) ^ (2 : ℕ) := by positivity
    calc ‖s - ρ₁‖ * ‖s - ρ₂‖ ≤ ‖s‖ ^ (2 : ℕ) * (1 + r) ^ (2 : ℕ) := le_trans hprod hnum
      _ ≤ ((3 + r) ^ (2 : ℕ) + 2 * (1 + r) ^ (2 : ℕ)) * ((2 / 3 : ℝ) * ‖s‖ ^ (2 : ℕ)) := by
          nlinarith [sq_nonneg ‖s‖, sq_nonneg (1 + r), mul_nonneg hC (sq_nonneg ‖s‖)]
      _ ≤ ((3 + r) ^ (2 : ℕ) + 2 * (1 + r) ^ (2 : ℕ)) * (‖s‖ * ‖s - 1‖) :=
          mul_le_mul_of_nonneg_left hden (by positivity)

end

end RHTower
