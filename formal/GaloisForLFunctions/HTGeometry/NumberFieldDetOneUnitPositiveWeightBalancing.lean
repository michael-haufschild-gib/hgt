import GaloisForLFunctions.HTGeometry.NumberFieldDetOneUnitWeightBalancing

/-!
# Multiplicative determinant-one balancing of positive place weights

Exponentiating the additive log-weight theorem gives the form used in reduction theory: after a
product-one unit rescaling, every positive place weight is within one uniform multiplicative factor
of a product of a coordinate-only scale and a place-only scale.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Uniform multiplicative balancing of every positive place-weight table by a determinant-one
tuple of number-ring units. -/
theorem exists_numberFieldDetOneUnit_positiveWeight_balancingRadius :
    ∃ R : ℝ, 0 < R ∧ ∀ (n : ℕ)
      (a : Fin (n + 1) → InfinitePlace K → ℝ),
      (∀ i w, 0 < a i w) →
      ∃ u : Fin (n + 1) → (𝓞 K)ˣ,
        (∏ i, u i = 1) ∧
        ∀ i w,
          Real.exp (-(2 * (n + 1 : ℝ) * R)) *
                (Real.exp (numberFieldWeightedPlaceMean (fun v => Real.log (a i v))) *
                  Real.exp (numberFieldCenteredPlaceProfileAverage
                    (fun j v => Real.log (a j v)) w)) ≤
            a i w * (w ((u i : 𝓞 K) : K)) ^ 2 ∧
          a i w * (w ((u i : 𝓞 K) : K)) ^ 2 ≤
            Real.exp (2 * (n + 1 : ℝ) * R) *
                (Real.exp (numberFieldWeightedPlaceMean (fun v => Real.log (a i v))) *
                  Real.exp (numberFieldCenteredPlaceProfileAverage
                    (fun j v => Real.log (a j v)) w)) := by
  obtain ⟨R, hR, hbalance⟩ :=
    exists_numberFieldDetOneUnit_logWeight_balancingRadius (K := K)
  refine ⟨R, hR, ?_⟩
  intro n a ha
  let f : Fin (n + 1) → InfinitePlace K → ℝ := fun i w => Real.log (a i w)
  obtain ⟨u, hu, hubound⟩ := hbalance n f
  refine ⟨u, hu, ?_⟩
  intro i w
  let q : ℝ :=
    (f i w + 2 * numberFieldUnitPlaceLogEmbeddings (u i) w) -
      (numberFieldWeightedPlaceMean (f i) +
        numberFieldCenteredPlaceProfileAverage f w)
  let C : ℝ := 2 * (n + 1 : ℝ) * R
  have hqabs : |q| ≤ C := hubound i w
  have hq := abs_le.mp hqabs
  have hwu : 0 < w ((u i : 𝓞 K) : K) := by
    rw [InfinitePlace.pos_iff]
    norm_cast
    exact (u i).ne_zero
  have hfactor :
      a i w * (w ((u i : 𝓞 K) : K)) ^ 2 =
        Real.exp q *
          (Real.exp (numberFieldWeightedPlaceMean (f i)) *
            Real.exp (numberFieldCenteredPlaceProfileAverage f w)) := by
    rw [← Real.exp_log (ha i w)]
    rw [show (w ((u i : 𝓞 K) : K)) ^ 2 =
        Real.exp (2 * Real.log (w ((u i : 𝓞 K) : K))) by
          rw [show 2 * Real.log (w ((u i : 𝓞 K) : K)) =
              Real.log (w ((u i : 𝓞 K) : K)) +
                Real.log (w ((u i : 𝓞 K) : K)) by ring,
            Real.exp_add, Real.exp_log hwu]
          ring]
    calc
      Real.exp (Real.log (a i w)) *
          Real.exp (2 * Real.log (w ((u i : 𝓞 K) : K))) =
          Real.exp (Real.log (a i w) +
            2 * Real.log (w ((u i : 𝓞 K) : K))) :=
        (Real.exp_add _ _).symm
      _ = Real.exp (q +
          (numberFieldWeightedPlaceMean (f i) +
            numberFieldCenteredPlaceProfileAverage f w)) := by
        congr 1
        dsimp [q, f, numberFieldUnitPlaceLogEmbeddings]
        ring
      _ = Real.exp q * Real.exp
          (numberFieldWeightedPlaceMean (f i) +
            numberFieldCenteredPlaceProfileAverage f w) := Real.exp_add _ _
      _ = Real.exp q *
          (Real.exp (numberFieldWeightedPlaceMean (f i)) *
            Real.exp (numberFieldCenteredPlaceProfileAverage f w)) := by
        rw [Real.exp_add]
  have hscale : 0 ≤
      Real.exp (numberFieldWeightedPlaceMean (f i)) *
        Real.exp (numberFieldCenteredPlaceProfileAverage f w) := by positivity
  constructor
  · rw [hfactor]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hq.1) hscale
  · rw [hfactor]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hq.2) hscale

end

end GaloisForLFunctions.HTGeometry
