import GaloisForLFunctions.RHTower.Sieve.TwistedMeanValueError

/-!
# Mollified twisted mean-value theorem

This file sums the existing twisted mean-value theorem over two finite mollifier indices.  It
retains the exact arithmetic diagonal `n * k = m * h` and bounds the accumulated error by the
product of the two mollifier `ell^(1 : ℕ)` masses.  An exact expansion identifies this weighted family
with a literal four-Dirichlet-polynomial correlation.
-/

open Finset Complex
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.Sieve

/-- Finite mollifier-weighted family of twisted Dirichlet correlations. -/
def mollifiedTwistedMoment
    (a b u v : ℕ → ℂ) (s q : Finset ℕ) (sigma T U : ℝ) : ℂ :=
  ∑ h ∈ q, ∑ k ∈ q,
    (u h * (starRingEnd ℂ) (v k)) *
      (∫ t in T..(T + U),
        cdpoly a s sigma t * (starRingEnd ℂ) (cdpoly b s sigma t) *
          Complex.exp ((((Real.log k - Real.log h) * t : ℝ)) * I))

/-- Exact arithmetic diagonal of the mollifier-weighted twisted correlations. -/
def mollifiedTwistedDiagonal
    (a b u v : ℕ → ℂ) (s q : Finset ℕ) (sigma : ℝ) : ℂ :=
  ∑ h ∈ q, ∑ k ∈ q,
    (u h * (starRingEnd ℂ) (v k)) *
      (∑ m ∈ s, ∑ n ∈ s.filter (fun n => n * k = m * h),
        twistedCoeff a b sigma m n)

/-- Two finite `cdpoly` mollifiers expand into the integer-ratio twists used
by `twisted_meanValue_error`. -/
theorem cdpoly_zero_mul_conj_eq_sum_ratio_twists
    (u v : ℕ → ℂ) (q : Finset ℕ) (t : ℝ) :
    cdpoly u q 0 t * (starRingEnd ℂ) (cdpoly v q 0 t) =
      ∑ h ∈ q, ∑ k ∈ q,
        (u h * (starRingEnd ℂ) (v k)) *
          Complex.exp ((((Real.log k - Real.log h) * t : ℝ)) * I) := by
  classical
  unfold cdpoly
  rw [map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k hk
  rw [conj_cdterm]
  simp only [cdterm, neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
  rw [show
      u h * Complex.exp (((-Real.log h * t : ℝ) : ℂ) * I) *
          ((starRingEnd ℂ) (v k) *
            Complex.exp ((((Real.log k) * t : ℝ) : ℂ) * I)) =
        (u h * (starRingEnd ℂ) (v k)) *
          (Complex.exp (((-Real.log h * t : ℝ) : ℂ) * I) *
            Complex.exp ((((Real.log k) * t : ℝ) : ℂ) * I)) by ring]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- The weighted sum of twisted moments is the literal four-polynomial
correlation with the two mollifier factors. -/
theorem integral_mollified_cdpoly_eq_mollifiedTwistedMoment
    (a b u v : ℕ → ℂ) (s q : Finset ℕ) (sigma T U : ℝ) :
    (∫ t in T..(T + U),
        (cdpoly a s sigma t * (starRingEnd ℂ) (cdpoly b s sigma t)) *
          (cdpoly u q 0 t * (starRingEnd ℂ) (cdpoly v q 0 t))) =
      mollifiedTwistedMoment a b u v s q sigma T U := by
  classical
  have hpoint : ∀ t : ℝ,
      (cdpoly a s sigma t * (starRingEnd ℂ) (cdpoly b s sigma t)) *
          (cdpoly u q 0 t * (starRingEnd ℂ) (cdpoly v q 0 t)) =
        ∑ h ∈ q, ∑ k ∈ q,
          (u h * (starRingEnd ℂ) (v k)) *
            (cdpoly a s sigma t * (starRingEnd ℂ) (cdpoly b s sigma t) *
              Complex.exp ((((Real.log k - Real.log h) * t : ℝ)) * I)) := by
    intro t
    rw [cdpoly_zero_mul_conj_eq_sum_ratio_twists]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hpoint t)]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro h hh
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [intervalIntegral.integral_const_mul]
    · intro k hk
      apply Continuous.intervalIntegrable
      unfold cdpoly cdterm
      fun_prop
  · intro h hh
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro k hk
    unfold cdpoly cdterm
    fun_prop

/-- Summing the twisted mean-value theorem over both mollifier indices preserves
the exact diagonal and costs the product of the two mollifier `ell^(1 : ℕ)` masses. -/
theorem mollifiedTwistedMeanValue_error
    (a b u v : ℕ → ℂ) (s q : Finset ℕ) (sigma : ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hq : ∀ h ∈ q, 1 ≤ h)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n ∈ s, ∀ j ∈ q, ((n * j : ℕ) : ℝ) ≤ B)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ m ∈ s, ∀ n ∈ s, ‖twistedCoeff a b sigma m n‖ ≤ C)
    (T U : ℝ) :
    ‖mollifiedTwistedMoment a b u v s q sigma T U -
        (U : ℂ) * mollifiedTwistedDiagonal a b u v s q sigma‖
      ≤ (4 * (s.card : ℝ) * C * B * (1 + Real.log s.card)) *
          (∑ h ∈ q, ‖u h‖) * (∑ k ∈ q, ‖v k‖) := by
  classical
  have hrewrite :
      mollifiedTwistedMoment a b u v s q sigma T U -
          (U : ℂ) * mollifiedTwistedDiagonal a b u v s q sigma =
        ∑ h ∈ q, ∑ k ∈ q,
          (u h * (starRingEnd ℂ) (v k)) *
            ((∫ t in T..(T + U),
                cdpoly a s sigma t * (starRingEnd ℂ) (cdpoly b s sigma t) *
                  Complex.exp ((((Real.log k - Real.log h) * t : ℝ)) * I)) -
              (U : ℂ) *
                (∑ m ∈ s, ∑ n ∈ s.filter (fun n => n * k = m * h),
                  twistedCoeff a b sigma m n)) := by
    unfold mollifiedTwistedMoment mollifiedTwistedDiagonal
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hrewrite]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun h hh => norm_sum_le _ _) ?_
  have hterm : ∀ h ∈ q, ∀ k ∈ q,
      ‖(u h * (starRingEnd ℂ) (v k)) *
          ((∫ t in T..(T + U),
              cdpoly a s sigma t * (starRingEnd ℂ) (cdpoly b s sigma t) *
                Complex.exp ((((Real.log k - Real.log h) * t : ℝ)) * I)) -
            (U : ℂ) *
              (∑ m ∈ s, ∑ n ∈ s.filter (fun n => n * k = m * h),
                twistedCoeff a b sigma m n))‖
        ≤ (‖u h‖ * ‖v k‖) *
            (4 * (s.card : ℝ) * C * B * (1 + Real.log s.card)) := by
    intro h hh k hk
    rw [norm_mul, norm_mul]
    change ‖u h‖ * ‖star (v k)‖ * _ ≤ _
    rw [norm_star]
    exact mul_le_mul_of_nonneg_left
      (twisted_meanValue_error a b s sigma (hq h hh) (hq k hk) hs hB0
        (fun n hn j hj => hB n hn j (by rcases hj with rfl | rfl <;> assumption))
        hC0 hC T U)
      (by positivity)
  refine le_trans (Finset.sum_le_sum fun h hh =>
    Finset.sum_le_sum fun k hk => hterm h hh k hk) ?_
  exact le_of_eq (by
  calc
    (∑ h ∈ q, ∑ k ∈ q,
        ‖u h‖ * ‖v k‖ *
          (4 * (s.card : ℝ) * C * B * (1 + Real.log s.card))) =
        ∑ h ∈ q, ‖u h‖ *
          ((∑ k ∈ q, ‖v k‖) *
            (4 * (s.card : ℝ) * C * B * (1 + Real.log s.card))) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (4 * (s.card : ℝ) * C * B * (1 + Real.log s.card)) *
          (∑ h ∈ q, ‖u h‖) * (∑ k ∈ q, ‖v k‖) := by
      rw [← Finset.sum_mul]
      ring)

/-- Four-polynomial form of the mollified twisted mean-value theorem. -/
theorem integral_mollified_cdpoly_error
    (a b u v : ℕ → ℂ) (s q : Finset ℕ) (sigma : ℝ)
    (hs : ∀ n ∈ s, 1 ≤ n) (hq : ∀ h ∈ q, 1 ≤ h)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n ∈ s, ∀ j ∈ q, ((n * j : ℕ) : ℝ) ≤ B)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ m ∈ s, ∀ n ∈ s, ‖twistedCoeff a b sigma m n‖ ≤ C)
    (T U : ℝ) :
    ‖(∫ t in T..(T + U),
          (cdpoly a s sigma t * (starRingEnd ℂ) (cdpoly b s sigma t)) *
            (cdpoly u q 0 t * (starRingEnd ℂ) (cdpoly v q 0 t))) -
        (U : ℂ) * mollifiedTwistedDiagonal a b u v s q sigma‖
      ≤ (4 * (s.card : ℝ) * C * B * (1 + Real.log s.card)) *
          (∑ h ∈ q, ‖u h‖) * (∑ k ∈ q, ‖v k‖) := by
  rw [integral_mollified_cdpoly_eq_mollifiedTwistedMoment]
  exact mollifiedTwistedMeanValue_error a b u v s q sigma hs hq
    hB0 hB hC0 hC T U

end RHTower.Sieve
