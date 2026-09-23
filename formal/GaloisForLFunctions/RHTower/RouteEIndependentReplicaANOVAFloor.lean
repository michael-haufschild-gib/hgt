import GaloisForLFunctions.HTGeometry.ConstitutiveInteractionSpectrumMechanics

/-!
# Route E independent-replica ANOVA floor

For `M` independent Bernoulli replicas of one binary component, the squared empirical parity
bias has expectation

`(1 - 2q)^(2 : ℕ) + 4q(1-q)/M`.

Across independent components these factors multiply.  The resulting histogram ANOVA is therefore
at least the square of the original one-copy product parity mean.  Independent replica
productization cannot create a new cancellation rate; a successful replica route must use the
physical aperture conditioning or another source-specific correlation.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Empirical parity bias of a binary component occurring in `k` of `M` replica slots. -/
def routeEReplicaHistogramBias (M k : ℕ) : ℝ :=
  1 - 2 * (k : ℝ) / (M : ℝ)

/-- Product-Bernoulli mean square of the empirical parity bias for one component. -/
def routeEIndependentReplicaLocalANOVA
    {R : Type*} [Fintype R] [DecidableEq R] (q : ℝ) : ℝ :=
  ∑ S : Finset R, interactionWorkWeight (fun _ => q) S *
    routeEReplicaHistogramBias (Fintype.card R) S.card ^ (2 : ℕ)

/-- Exact bias-variance decomposition for an arbitrary product Bernoulli replica law. -/
theorem routeE_replica_degree_bias_second_moment
    {R : Type*} [Fintype R] [DecidableEq R]
    (a : R → ℝ) (M : ℝ) (hM : M ≠ 0) :
    (∑ S : Finset R, interactionWorkWeight a S *
        (1 - 2 * (S.card : ℝ) / M) ^ (2 : ℕ)) =
      (1 - 2 * meanInteractionDegree a / M) ^ (2 : ℕ) +
        4 * interactionDegreeVariance a / M ^ (2 : ℕ) := by
  have hcenter :
      interactionDegreeVariance a =
        (∑ S : Finset R, interactionWorkWeight a S * (S.card : ℝ) ^ (2 : ℕ)) -
          meanInteractionDegree a ^ (2 : ℕ) := by
    unfold interactionDegreeVariance
    calc
      (∑ S : Finset R, interactionWorkWeight a S *
          ((S.card : ℝ) - meanInteractionDegree a) ^ (2 : ℕ)) =
          ∑ S : Finset R,
            (interactionWorkWeight a S * (S.card : ℝ) ^ (2 : ℕ) -
              2 * meanInteractionDegree a *
                (interactionWorkWeight a S * (S.card : ℝ)) +
              meanInteractionDegree a ^ (2 : ℕ) * interactionWorkWeight a S) := by
            apply Finset.sum_congr rfl
            intro S hS
            ring
      _ = (∑ S : Finset R, interactionWorkWeight a S * (S.card : ℝ) ^ (2 : ℕ)) -
            2 * meanInteractionDegree a *
              (∑ S : Finset R, interactionWorkWeight a S * (S.card : ℝ)) +
            meanInteractionDegree a ^ (2 : ℕ) *
              (∑ S : Finset R, interactionWorkWeight a S) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [Finset.mul_sum, Finset.mul_sum]
      _ = (∑ S : Finset R, interactionWorkWeight a S * (S.card : ℝ) ^ (2 : ℕ)) -
            meanInteractionDegree a ^ (2 : ℕ) := by
            rw [← meanInteractionDegree, sum_interactionWorkWeight_eq_one]
            ring
  calc
    (∑ S : Finset R, interactionWorkWeight a S *
        (1 - 2 * (S.card : ℝ) / M) ^ (2 : ℕ)) =
        (∑ S : Finset R, interactionWorkWeight a S) -
          (4 / M) *
            (∑ S : Finset R, interactionWorkWeight a S * (S.card : ℝ)) +
          (4 / M ^ (2 : ℕ)) *
            (∑ S : Finset R, interactionWorkWeight a S * (S.card : ℝ) ^ (2 : ℕ)) := by
          rw [show
            (∑ S : Finset R, interactionWorkWeight a S) -
                (4 / M) *
                  (∑ S : Finset R, interactionWorkWeight a S * (S.card : ℝ)) +
                (4 / M ^ (2 : ℕ)) *
                  (∑ S : Finset R, interactionWorkWeight a S * (S.card : ℝ) ^ (2 : ℕ)) =
              ∑ S : Finset R,
                (interactionWorkWeight a S -
                  (4 / M) * (interactionWorkWeight a S * (S.card : ℝ)) +
                  (4 / M ^ (2 : ℕ)) *
                    (interactionWorkWeight a S * (S.card : ℝ) ^ (2 : ℕ))) by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                ← Finset.mul_sum, ← Finset.mul_sum]]
          apply Finset.sum_congr rfl
          intro S hS
          field_simp
          ring
    _ = 1 - (4 / M) * meanInteractionDegree a +
          (4 / M ^ (2 : ℕ)) *
            (interactionDegreeVariance a + meanInteractionDegree a ^ (2 : ℕ)) := by
          rw [sum_interactionWorkWeight_eq_one, ← meanInteractionDegree]
          rw [show (∑ S : Finset R, interactionWorkWeight a S * (S.card : ℝ) ^ (2 : ℕ)) =
              interactionDegreeVariance a + meanInteractionDegree a ^ (2 : ℕ) by linarith [hcenter]]
    _ = (1 - 2 * meanInteractionDegree a / M) ^ (2 : ℕ) +
          4 * interactionDegreeVariance a / M ^ (2 : ℕ) := by
          field_simp
          ring

/-- Independent identically distributed replicas have the exact one-copy floor plus variance. -/
theorem routeE_independent_replica_localANOVA_eq
    {R : Type*} [Fintype R] [DecidableEq R] [Nonempty R] (q : ℝ) :
    routeEIndependentReplicaLocalANOVA (R := R) q =
      (1 - 2 * q) ^ (2 : ℕ) +
        4 * q * (1 - q) / (Fintype.card R : ℝ) := by
  have hcard : (Fintype.card R : ℝ) ≠ 0 := by positivity
  unfold routeEIndependentReplicaLocalANOVA routeEReplicaHistogramBias
  rw [routeE_replica_degree_bias_second_moment (fun _ : R => q)
    (Fintype.card R : ℝ) hcard]
  rw [meanInteractionDegree_eq_sum, interactionDegreeVariance_eq_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Replication cannot lower one component below its original squared parity mean. -/
theorem routeE_independent_replica_localANOVA_floor
    {R : Type*} [Fintype R] [DecidableEq R] [Nonempty R]
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - 2 * q) ^ (2 : ℕ) ≤ routeEIndependentReplicaLocalANOVA (R := R) q := by
  rw [routeE_independent_replica_localANOVA_eq]
  have hcard : 0 < (Fintype.card R : ℝ) := by positivity
  have hcorrection : 0 ≤ 4 * q * (1 - q) / (Fintype.card R : ℝ) := by positivity
  linarith

/-- Across independent components, replica ANOVA cannot beat the original product parity mean. -/
theorem routeE_independent_replica_productANOVA_floor
    {C R : Type*} [Fintype C] [Fintype R]
    [DecidableEq C] [DecidableEq R] [Nonempty R]
    (q : C → ℝ) (hq0 : ∀ c, 0 ≤ q c) (hq1 : ∀ c, q c ≤ 1) :
    (∏ c, (1 - 2 * q c)) ^ (2 : ℕ) ≤
      ∏ c, routeEIndependentReplicaLocalANOVA (R := R) (q c) := by
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro c hc
    positivity
  · intro c hc
    exact routeE_independent_replica_localANOVA_floor (q c) (hq0 c) (hq1 c)

end

end RHTower
