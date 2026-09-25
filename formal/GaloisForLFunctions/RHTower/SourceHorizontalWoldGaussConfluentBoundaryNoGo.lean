import GaloisForLFunctions.RHTower.SourceHorizontalWoldGaussFiniteCoercivity
import GaloisForLFunctions.RHTower.XiGammaSixFilteredBoundaryConfluentFlux

/-!
# Confluent Gamma-six boundary is too small for labelwise Wold–Gauss payment

The actual prime-labelled confluent boundary coefficient is nonnegative and at
most `log 2 / p`. The finite Wold–Gauss virial has a uniform `p*t²` floor after
one inner-clock threshold. Their exact quadratic prime-scale separation rules
out additive, labelwise cancellation at every nonzero horizontal grade, even
with a moving inner clock. A nonlocal or indefinite source transport is not
addressed by this theorem.
-/

noncomputable section
open Filter
namespace RHTower

/-- The literal confluent boundary counterterm is of reciprocal-prime scale. -/
theorem gammaSixFilteredBoundaryConfluentCounterterm_one_bounds
    (t : ℝ) (p : Nat.Primes) :
    0 ≤ gammaSixFilteredBoundaryConfluentCounterterm 1 t p ∧
    gammaSixFilteredBoundaryConfluentCounterterm 1 t p ≤
      Real.log 2 / (p : ℝ) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hr0 : 0 ≤ (p : ℝ) ^ (-|t|) := Real.rpow_nonneg hp0.le _
  have hr1 : (p : ℝ) ^ (-|t|) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr (abs_nonneg t))
  have hs0 : 0 ≤ (1 - (p : ℝ) ^ (-|t|)) ^ (2 : ℕ) := sq_nonneg _
  have hs1 : (1 - (p : ℝ) ^ (-|t|)) ^ (2 : ℕ) ≤ 1 := by
    nlinarith [mul_nonneg hr0 (by linarith : 0 ≤ 2 - (p : ℝ) ^ (-|t|))]
  unfold gammaSixFilteredBoundaryConfluentCounterterm
  norm_num
  constructor
  · positivity
  · calc
      Real.log 2 * (p : ℝ)⁻¹ *
          (1 - (p : ℝ) ^ (-|t|)) ^ (2 : ℕ) ≤
        Real.log 2 * (p : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = Real.log 2 / (p : ℝ) := by simp [div_eq_mul_inv]

private theorem gammaSixFilteredBoundaryConfluentCounterterm_one_sublinear (t : ℝ) :
    Tendsto (fun n : ℕ =>
      gammaSixFilteredBoundaryConfluentCounterterm 1 t (nthPrimeSubtype n) /
        (nthPrimeSubtype n : ℝ)) atTop (nhds 0) := by
  have hp : Tendsto (fun n : ℕ => (nthPrimeSubtype n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp nthPrimeSubtype_strictMono.tendsto_atTop
  have hinv : Tendsto (fun n : ℕ => (nthPrimeSubtype n : ℝ)⁻¹) atTop (nhds 0) := by
    simpa only [Function.comp_def] using tendsto_inv_atTop_zero.comp hp
  have hmajor : Tendsto (fun n : ℕ =>
      Real.log 2 * ((nthPrimeSubtype n : ℝ)⁻¹) ^ (2 : ℕ)) atTop (nhds 0) := by
    simpa using (hinv.pow 2).const_mul (Real.log 2)
  apply squeeze_zero
  · intro n
    exact div_nonneg
      (gammaSixFilteredBoundaryConfluentCounterterm_one_bounds t (nthPrimeSubtype n)).1
      (by exact_mod_cast (nthPrimeSubtype n).property.pos.le)
  · intro n
    have hp0 : (0 : ℝ) < (nthPrimeSubtype n : ℝ) := by
      exact_mod_cast (nthPrimeSubtype n).property.pos
    calc
      gammaSixFilteredBoundaryConfluentCounterterm 1 t (nthPrimeSubtype n) /
          (nthPrimeSubtype n : ℝ) ≤
        (Real.log 2 / (nthPrimeSubtype n : ℝ)) /
          (nthPrimeSubtype n : ℝ) :=
            div_le_div_of_nonneg_right
              (gammaSixFilteredBoundaryConfluentCounterterm_one_bounds t
                (nthPrimeSubtype n)).2 hp0.le
      _ = Real.log 2 * ((nthPrimeSubtype n : ℝ)⁻¹) ^ (2 : ℕ) := by
        field_simp
  · exact hmajor

/-- Exact quadratic prime-scale separation from the source virial, uniformly
after one inner-clock threshold and for all real grades. -/
theorem gaussWoldFiniteSourceVirialResponse_confluent_quadratic_gap :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (p : Nat.Primes) (t : ℝ),
      (p : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) *
          gammaSixFilteredBoundaryConfluentCounterterm 1 t p ≤
        36 * gaussWoldFiniteSourceVirialResponse N 1 p t := by
  obtain ⟨N₀, hN₀⟩ :=
    gaussWoldFiniteSourceVirialResponse_uniform_linear_lower
  refine ⟨N₀, ?_⟩
  intro N hN p t
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hC := (gammaSixFilteredBoundaryConfluentCounterterm_one_bounds t p).2
  have hV := hN₀ N hN p t
  calc
    (p : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) *
        gammaSixFilteredBoundaryConfluentCounterterm 1 t p ≤
      (p : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) * (Real.log 2 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hC
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = 36 * (Real.log 2 / 36 * (p : ℝ) * t ^ (2 : ℕ)) := by
      field_simp [hp0.ne']
    _ ≤ 36 * gaussWoldFiniteSourceVirialResponse N 1 p t :=
      mul_le_mul_of_nonneg_left hV (by norm_num)

/-- The confluent Gamma-six boundary term cannot be an additive labelwise
payment for the Wold–Gauss virial at any nonzero horizontal grade. -/
theorem gaussWoldFiniteSourceVirialResponse_no_confluent_labelwise_payment
    (t : ℝ) (ht : t ≠ 0) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℝ,
      ∃ n : ℕ, B < gaussWoldFiniteSourceVirialResponse N 1
        (nthPrimeSubtype n) t -
        gammaSixFilteredBoundaryConfluentCounterterm 1 t (nthPrimeSubtype n) := by
  exact gaussWoldFiniteSourceVirialResponse_no_sublinear_correction t ht
    (gammaSixFilteredBoundaryConfluentCounterterm 1 t)
    (gammaSixFilteredBoundaryConfluentCounterterm_one_sublinear t)

end RHTower
