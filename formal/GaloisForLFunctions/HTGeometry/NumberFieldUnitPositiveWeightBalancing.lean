import GaloisForLFunctions.HTGeometry.NumberFieldDetOneUnitPositiveWeightBalancing

/-!
# Single-unit balancing of positive place weights

Dirichlet-unit covering balances one arbitrary positive archimedean weight profile around its
multiplicity-weighted geometric mean.  Unlike determinant-one coordinate balancing, this is the
form needed when a primitive-minimal vector is compared with one unit-scaled coordinate vector.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- A single number-ring unit uniformly balances any positive place-weight profile around its
multiplicity-weighted geometric mean. -/
theorem exists_numberFieldUnit_positiveWeight_balancingRadius :
    ∃ R : ℝ, 0 < R ∧ ∀ (a : InfinitePlace K → ℝ),
      (∀ w, 0 < a w) →
      ∃ u : (𝓞 K)ˣ, ∀ w,
        Real.exp (-2 * R) *
              Real.exp (numberFieldWeightedPlaceMean (fun v ↦ Real.log (a v))) ≤
            a w * (w ((u : 𝓞 K) : K)) ^ 2 ∧
          a w * (w ((u : 𝓞 K) : K)) ^ 2 ≤
            Real.exp (2 * R) *
              Real.exp (numberFieldWeightedPlaceMean (fun v ↦ Real.log (a v))) := by
  obtain ⟨R, hR, hcover⟩ :=
    exists_numberFieldUnitPlaceLog_coveringRadius (K := K)
  refine ⟨R, hR, ?_⟩
  intro a ha
  let f : InfinitePlace K → ℝ := fun w ↦ Real.log (a w)
  let y : InfinitePlace K → ℝ :=
    (-1 / 2 : ℝ) • numberFieldCenteredPlaceProfile f
  have hy : y ∈ numberFieldUnitPlaceLogHyperplane (K := K) := by
    exact (numberFieldUnitPlaceLogHyperplane (K := K)).smul_mem _
      (numberFieldCenteredPlaceProfile_mem_hyperplane f)
  obtain ⟨u, hu⟩ := hcover y hy
  refine ⟨u, ?_⟩
  intro w
  have heval :
      |numberFieldUnitPlaceLogEmbeddings u w - y w| ≤
        ‖numberFieldUnitPlaceLogEmbeddings u - y‖ := by
    simpa [Real.norm_eq_abs] using
      norm_le_pi_norm (numberFieldUnitPlaceLogEmbeddings u - y) w
  have hcoord :
      |numberFieldUnitPlaceLogEmbeddings u w - y w| ≤ R :=
    heval.trans hu
  let q : ℝ :=
    (f w + 2 * numberFieldUnitPlaceLogEmbeddings u w) -
      numberFieldWeightedPlaceMean f
  have hqeq :
      q = 2 * (numberFieldUnitPlaceLogEmbeddings u w - y w) := by
    dsimp [q, y, numberFieldCenteredPlaceProfile]
    ring
  have hqabs : |q| ≤ 2 * R := by
    rw [hqeq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  have hq := abs_le.mp hqabs
  have hwu : 0 < w ((u : 𝓞 K) : K) := by
    rw [InfinitePlace.pos_iff]
    norm_cast
    exact u.ne_zero
  have hfactor :
      a w * (w ((u : 𝓞 K) : K)) ^ 2 =
        Real.exp q * Real.exp (numberFieldWeightedPlaceMean f) := by
    rw [← Real.exp_log (ha w)]
    rw [show (w ((u : 𝓞 K) : K)) ^ 2 =
        Real.exp (2 * Real.log (w ((u : 𝓞 K) : K))) by
          rw [show 2 * Real.log (w ((u : 𝓞 K) : K)) =
              Real.log (w ((u : 𝓞 K) : K)) +
                Real.log (w ((u : 𝓞 K) : K)) by ring,
            Real.exp_add, Real.exp_log hwu]
          ring]
    calc
      Real.exp (Real.log (a w)) *
          Real.exp (2 * Real.log (w ((u : 𝓞 K) : K))) =
          Real.exp (Real.log (a w) +
            2 * Real.log (w ((u : 𝓞 K) : K))) :=
        (Real.exp_add _ _).symm
      _ = Real.exp (q + numberFieldWeightedPlaceMean f) := by
        congr 1
        dsimp [q, f, numberFieldUnitPlaceLogEmbeddings]
        ring
      _ = Real.exp q * Real.exp (numberFieldWeightedPlaceMean f) :=
        Real.exp_add _ _
  have hscale : 0 ≤ Real.exp (numberFieldWeightedPlaceMean f) := by positivity
  constructor
  · rw [hfactor]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by simpa only [neg_mul] using hq.1)) hscale
  · rw [hfactor]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hq.2) hscale

/-- The multiplicity-weighted geometric mean of positive archimedean place weights is bounded by
their unweighted sum. -/
theorem exp_numberFieldWeightedPlaceMean_log_le_sum
    (a : InfinitePlace K → ℝ) (ha : ∀ w, 0 < a w) :
    Real.exp (numberFieldWeightedPlaceMean (fun w ↦ Real.log (a w))) ≤
      ∑ w, a w := by
  let S : ℝ := ∑ w, a w
  let w₀ : InfinitePlace K := Classical.choice inferInstance
  have hS : 0 < S := by
    exact Finset.sum_pos (fun w _ ↦ ha w) ⟨w₀, Finset.mem_univ w₀⟩
  have haw (w : InfinitePlace K) : a w ≤ S := by
    exact Finset.single_le_sum (fun v _ ↦ (ha v).le) (Finset.mem_univ w)
  have hlog (w : InfinitePlace K) : Real.log (a w) ≤ Real.log S :=
    Real.log_le_log (ha w) (haw w)
  have hsum :
      (∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (a w)) ≤
        ∑ w : InfinitePlace K, (mult w : ℝ) * Real.log S := by
    exact Finset.sum_le_sum fun w _ ↦
      mul_le_mul_of_nonneg_left (hlog w) (by positivity)
  have hright :
      (∑ w : InfinitePlace K, (mult w : ℝ) * Real.log S) =
        numberFieldInfinitePlaceWeight (K := K) * Real.log S := by
    rw [← Finset.sum_mul]
    rfl
  rw [hright] at hsum
  have hweight : 0 < numberFieldInfinitePlaceWeight (K := K) :=
    numberFieldInfinitePlaceWeight_pos (K := K)
  have hmean :
      numberFieldWeightedPlaceMean (fun w ↦ Real.log (a w)) ≤ Real.log S := by
    unfold numberFieldWeightedPlaceMean
    apply (div_le_iff₀ hweight).2
    simpa [mul_comm] using hsum
  have hexp := Real.exp_le_exp.mpr hmean
  rw [Real.exp_log hS] at hexp
  exact hexp

end

end GaloisForLFunctions.HTGeometry
