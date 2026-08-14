import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentAggregateCellExtraction
import GaloisForLFunctions.HTGeometry.MellinConjugate

/-!
# Positive-ordinate reflection for the adjacent Route-T defect

Every arithmetic coefficient and smooth physical window in the adjacent Perron defect is real.
Consequently the full vertical integrand at `-y` is the complex conjugate of its value at `y`.
This module closes that symmetry in Lean and upgrades four-wing annular extraction to the two
positive wings required by Maynard's ordinate receivers.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter

/-- A real arithmetic function has a conjugation-equivariant complex Dirichlet series. -/
theorem conj_LSeries_complexCoeff (F : ArithmeticFunction ℝ) (s : ℂ) :
    (starRingEnd ℂ) (LSeries (complexCoeff F) s) =
      LSeries (complexCoeff F) ((starRingEnd ℂ) s) := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  apply tsum_congr
  intro n
  rw [LSeries.term_def, LSeries.term_def]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, if_neg hn]
    rw [map_div₀ (starRingEnd ℂ)]
    change (starRingEnd ℂ) (complexCoeff F n) /
        (starRingEnd ℂ) ((n : ℂ) ^ s) =
      complexCoeff F n / (n : ℂ) ^ ((starRingEnd ℂ) s)
    congr 1
    · simp [complexCoeff_apply]
    · have harg : ((n : ℂ)).arg ≠ Real.pi := by
        rw [show ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) by push_cast; ring,
          Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
        exact ne_of_lt Real.pi_pos
      simpa using (Complex.cpow_conj (n : ℂ) s harg).symm

/-- The eligible window-relevant aggregate inherits conjugation from its real packet. -/
theorem conj_heathBrownWindowRelevantEligibleDyadicAggregate
    (L X k : ℕ) (T0 t N : ℝ) (s : ℂ) :
    (starRingEnd ℂ)
        (heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N s) =
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
        ((starRingEnd ℂ) s) := by
  rw [← LSeries_heathBrownWindowRelevantEligiblePacket]
  rw [conj_LSeries_complexCoeff]
  exact LSeries_heathBrownWindowRelevantEligiblePacket L X k T0 t N _

/-- A real smooth window gives a conjugation-equivariant normalized Mellin transform. -/
theorem conj_routeTNormalizedSmoothWindowMellin
    (N H : ℝ) (s : ℂ) :
    (starRingEnd ℂ) (routeTNormalizedSmoothWindowMellin N H s) =
      routeTNormalizedSmoothWindowMellin N H ((starRingEnd ℂ) s) := by
  rw [routeTNormalizedSmoothWindowMellin, map_mul]
  congr 1
  · simp
  · rw [GaloisForLFunctions.HTGeometry.mellin_conj_of_conj_invariant]
    intro x
    simp

/-- Conjugate-reflected functions have equal interval-integral norms on reflected intervals. -/
theorem norm_intervalIntegral_reflection_of_conj
    {f : ℝ → ℂ} (hf : ∀ y : ℝ, f (-y) = (starRingEnd ℂ) (f y))
    (a b : ℝ) :
    ‖∫ y in (-b)..(-a), f y‖ = ‖∫ y in a..b, f y‖ := by
  have href : (∫ y in (-b)..(-a), f y) =
      (starRingEnd ℂ) (∫ y in a..b, f y) := by
    rw [← intervalIntegral.intervalIntegral_conj,
      ← intervalIntegral.integral_comp_neg]
    apply intervalIntegral.integral_congr
    intro y hy
    exact hf y
  rw [href, Complex.norm_conj]

/-- Exact reflection law for the full adjacent aggregate-kernel defect. -/
theorem conj_windowRelevantAggregate_mul_adjacentKernel
    (L X k : ℕ) (T0 t N H R y : ℝ) :
    (starRingEnd ℂ)
        (heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((1 : ℂ) + (y : ℝ) * I) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I))) =
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((1 : ℂ) + ((-y : ℝ) : ℂ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + ((-y : ℝ) : ℂ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + ((-y : ℝ) : ℂ) * I)) := by
  rw [map_mul, map_sub,
    conj_heathBrownWindowRelevantEligibleDyadicAggregate,
    conj_routeTNormalizedSmoothWindowMellin,
    conj_routeTNormalizedSmoothWindowMellin]
  congr 1 <;> simp

/-- Reflection reduces a four-wing signed annulus to its two positive wings without loss. -/
theorem exists_positive_interval_norm_ge_quarter_of_annulus_of_conj
    {f : ℝ → ℂ} (hf : Integrable f)
    (hconj : ∀ y : ℝ, f (-y) = (starRingEnd ℂ) (f y))
    {B U T V : ℝ} (hU : 0 ≤ U) (hUT : U ≤ T) (hTV : T ≤ V)
    (hB : B ≤ ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V}, f y‖) :
    B / 4 ≤ ‖∫ y in U..T, f y‖ ∨
      B / 4 ≤ ‖∫ y in T..V, f y‖ := by
  rcases exists_interval_norm_ge_quarter_of_annulus hf hU hUT hTV hB with
      houterNeg | hcentralNeg | hcentralPos | houterPos
  · right
    rwa [norm_intervalIntegral_reflection_of_conj hconj T V] at houterNeg
  · left
    rwa [norm_intervalIntegral_reflection_of_conj hconj U T] at hcentralNeg
  · exact Or.inl hcentralPos
  · exact Or.inr houterPos

/-- The quantitative adjacent defect always has a large positive central or outer wing. -/
theorem exists_positive_interval_norm_ge_quarter_of_adjacent_annulus
    (L X k : ℕ) (T0 t : ℝ) {N H R B U T V : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hU : 0 ≤ U) (hUT : U ≤ T) (hTV : T ≤ V)
    (hB : B ≤ ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V},
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((1 : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))‖) :
    B / 4 ≤ ‖∫ y in U..T,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((1 : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))‖ ∨
    B / 4 ≤ ‖∫ y in T..V,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
            ((1 : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))‖ := by
  let f : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((1 : ℂ) + (y : ℝ) * I) *
      (routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * I) -
        routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * I))
  have hf : Integrable f := by
    have hRint := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
      L X k T0 t N hN hR (by norm_num : (0 : ℝ) < 1)
    have hHint := integrable_heathBrownWindowRelevantAggregate_mul_routeTNormalizedMellin
      L X k T0 t N hN hH (by norm_num : (0 : ℝ) < 1)
    exact (hRint.sub hHint).congr (Filter.Eventually.of_forall fun y => by
      simp only [f, Pi.sub_apply, mul_sub, ofReal_one])
  have hconj : ∀ y : ℝ, f (-y) = (starRingEnd ℂ) (f y) := by
    intro y
    exact (conj_windowRelevantAggregate_mul_adjacentKernel
      L X k T0 t N H R y).symm
  exact exists_positive_interval_norm_ge_quarter_of_annulus_of_conj
    hf hconj hU hUT hTV (by simpa only [f] using hB)

end RHTower.Sieve
