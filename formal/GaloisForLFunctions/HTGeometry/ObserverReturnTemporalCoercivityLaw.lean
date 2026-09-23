import GaloisForLFunctions.HTGeometry.ObserverReturnTemporalMetricLaw
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Observer return temporal coercivity

Every finite separating family of observer-visible gaps defines a
positive-definite Gram matrix. Consequently its temporal metric has uniform
positive lower and upper quadratic bounds. This removes coercivity constants
as hypotheses from the local recurrence-volume law: they are forced by
finite-dimensional observer separation.
-/

open scoped BigOperators
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Weighted Gram matrix of the observer-visible gap-coordinate family. -/
def observerTemporalGramMatrix
    {J : Type*} [Fintype J] {τ : ℕ}
    (weight : J → ℝ) (gap : J → Fin τ → ℝ) :
    Matrix (Fin τ) (Fin τ) ℝ :=
  fun p q => ∑ j, weight j * gap j p * gap j q

/-- The temporal metric energy is exactly the quadratic form of its weighted
gap Gram matrix. -/
theorem observerTemporalMetricEnergy_eq_gramQuadratic
    {J : Type*} [Fintype J] {τ : ℕ}
    (weight : J → ℝ) (gap : J → Fin τ → ℝ)
    (theta : Fin τ → ℝ) :
    observerTemporalMetricEnergy weight gap theta =
      theta ⬝ᵥ observerTemporalGramMatrix weight gap *ᵥ theta := by
  simp only [observerTemporalMetricEnergy,
    observerTemporalCoordinateAction, observerTemporalGramMatrix,
    dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  simp_rw [pow_two, Finset.mul_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  trans ∑ q : Fin τ, ∑ p : Fin τ, ∑ j : J,
      weight j * (gap j p * theta p * (gap j q * theta q))
  · apply Finset.sum_congr rfl
    intro q _hq
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _hp
    apply Finset.sum_congr rfl
    intro q _hq
    apply Finset.sum_congr rfl
    intro j _hj
    ring

/-- Positive weights and separation make the observer temporal Gram matrix
positive definite. -/
theorem observerTemporalGramMatrix_posDef
    {J : Type*} [Fintype J] {τ : ℕ}
    (weight : J → ℝ) (gap : J → Fin τ → ℝ)
    (hweight : ∀ j, 0 < weight j)
    (hnondegenerate : ObserverTemporalMetricNondegenerate gap) :
    (observerTemporalGramMatrix weight gap).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext p q
    simp only [observerTemporalGramMatrix, Matrix.conjTranspose_apply,
      star_trivial]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  · intro theta htheta
    have hpos : 0 < observerTemporalMetricEnergy weight gap theta := by
      have hnonneg :=
        observerTemporalMetricEnergy_nonneg
          weight gap (fun j => (hweight j).le) theta
      have hne :
          observerTemporalMetricEnergy weight gap theta ≠ 0 := by
        intro hzero
        exact htheta
          ((observerTemporalMetricEnergy_eq_zero_iff
            weight gap hweight hnondegenerate theta).mp hzero)
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    simpa only [star_trivial,
      observerTemporalMetricEnergy_eq_gramQuadratic] using hpos

/-- A separating positively weighted finite gap family has a uniform positive
lower quadratic bound. -/
theorem observerTemporalMetricEnergy_lower_bound
    {J : Type*} [Fintype J] {τ : ℕ}
    (weight : J → ℝ) (gap : J → Fin τ → ℝ)
    (hweight : ∀ j, 0 < weight j)
    (hnondegenerate : ObserverTemporalMetricNondegenerate gap) :
    ∃ m : ℝ, 0 < m ∧
      ∀ theta : EuclideanSpace ℝ (Fin τ),
        m * ‖theta‖ ^ (2 : ℕ) ≤
          observerTemporalMetricEnergy weight gap (fun k => theta k) := by
  obtain ⟨m, hm, hbound⟩ :=
    posDef_coercive
      (observerTemporalGramMatrix_posDef
        weight gap hweight hnondegenerate)
  refine ⟨m, hm, fun theta => ?_⟩
  rw [observerTemporalMetricEnergy_eq_gramQuadratic]
  have hnorm :
      (fun k => theta k) ⬝ᵥ (fun k => theta k) = ‖theta‖ ^ (2 : ℕ) := by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  rw [← hnorm]
  exact hbound (fun k => theta k)

/-- Every finite weighted gap family has a uniform upper quadratic bound. -/
theorem observerTemporalMetricEnergy_upper_bound
    {J : Type*} [Fintype J] {τ : ℕ}
    (weight : J → ℝ) (gap : J → Fin τ → ℝ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ theta : EuclideanSpace ℝ (Fin τ),
        observerTemporalMetricEnergy weight gap (fun k => theta k) ≤
          M * ‖theta‖ ^ (2 : ℕ) := by
  let G := observerTemporalGramMatrix weight gap
  let ε : ℝ := ∑ p : Fin τ, ∑ q : Fin τ, |G p q|
  have hε : 0 ≤ ε := by
    dsimp [ε]
    exact Finset.sum_nonneg fun p _ =>
      Finset.sum_nonneg fun q _ => abs_nonneg _
  have hentry : ∀ p q, |G p q| ≤ ε := by
    intro p q
    have hq :
        |G p q| ≤ ∑ q' : Fin τ, |G p q'| :=
      Finset.single_le_sum
        (fun q' _hq' => abs_nonneg (G p q'))
        (Finset.mem_univ q)
    have hp :
        (∑ q' : Fin τ, |G p q'|) ≤
          ∑ p' : Fin τ, ∑ q' : Fin τ, |G p' q'| :=
      Finset.single_le_sum
        (fun p' _hp' => Finset.sum_nonneg fun q' _hq' =>
          abs_nonneg (G p' q'))
        (Finset.mem_univ p)
    exact hq.trans hp
  refine ⟨(τ : ℝ) * ε + 1, by positivity, fun theta => ?_⟩
  rw [observerTemporalMetricEnergy_eq_gramQuadratic]
  have habs :=
    abs_dotProduct_mulVec_le G hε hentry (fun k => theta k)
  have hnorm :
      (fun k => theta k) ⬝ᵥ (fun k => theta k) = ‖theta‖ ^ (2 : ℕ) := by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  rw [hnorm] at habs
  have hnormSq : 0 ≤ ‖theta‖ ^ (2 : ℕ) := sq_nonneg _
  calc
    (fun k => theta k) ⬝ᵥ G *ᵥ (fun k => theta k) ≤
        |(fun k => theta k) ⬝ᵥ G *ᵥ (fun k => theta k)| :=
      le_abs_self _
    _ ≤ (τ : ℝ) * ε * ‖theta‖ ^ (2 : ℕ) := habs
    _ ≤ ((τ : ℝ) * ε + 1) * ‖theta‖ ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one) hnormSq

/-- Separating positive visible gaps automatically provide both coercivity
constants required by the local recurrence-volume law. -/
theorem observerTemporalMetricEnergy_two_sided_bounds
    {J : Type*} [Fintype J] {τ : ℕ}
    (weight : J → ℝ) (gap : J → Fin τ → ℝ)
    (hweight : ∀ j, 0 < weight j)
    (hnondegenerate : ObserverTemporalMetricNondegenerate gap) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ theta : EuclideanSpace ℝ (Fin τ),
        m * ‖theta‖ ^ (2 : ℕ) ≤
            observerTemporalMetricEnergy weight gap (fun k => theta k) ∧
          observerTemporalMetricEnergy weight gap (fun k => theta k) ≤
            M * ‖theta‖ ^ (2 : ℕ) := by
  obtain ⟨m, hm, hlower⟩ :=
    observerTemporalMetricEnergy_lower_bound
      weight gap hweight hnondegenerate
  obtain ⟨M, hM, hupper⟩ :=
    observerTemporalMetricEnergy_upper_bound weight gap
  exact ⟨m, M, hm, hM, fun theta => ⟨hlower theta, hupper theta⟩⟩

/-- Every finite gap-coordinate family has a positive Euclidean radius on
which all visible actions remain inside the principal phase window. -/
theorem exists_observerTemporalPrincipalPhaseRadius
    {J : Type*} [Fintype J] {τ : ℕ}
    (gap : J → Fin τ → ℝ) :
    ∃ r : ℝ, 0 < r ∧
      ∀ theta : EuclideanSpace ℝ (Fin τ),
        ‖theta‖ < r →
          ∀ j, |observerTemporalCoordinateAction gap
            (fun k => theta k) j| ≤ Real.pi := by
  let B : ℝ := (∑ j : J, ∑ k : Fin τ, gap j k ^ (2 : ℕ)) + 1
  have hsum : 0 ≤ ∑ j : J, ∑ k : Fin τ, gap j k ^ (2 : ℕ) :=
    Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _
  have hB : 0 < B := by
    dsimp [B]
    linarith
  have hsqrtB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  refine ⟨Real.pi / Real.sqrt B, div_pos Real.pi_pos hsqrtB,
    fun theta htheta j => ?_⟩
  have hgap :
      (∑ k : Fin τ, gap j k ^ (2 : ℕ)) ≤ B := by
    have hsingle :
        (∑ k : Fin τ, gap j k ^ (2 : ℕ)) ≤
          ∑ j' : J, ∑ k : Fin τ, gap j' k ^ (2 : ℕ) :=
      Finset.single_le_sum
        (fun j' _hj' => Finset.sum_nonneg fun k _hk =>
          sq_nonneg (gap j' k))
        (Finset.mem_univ j)
    dsimp [B]
    linarith
  have hnorm :
      (∑ k : Fin τ, theta k ^ (2 : ℕ)) = ‖theta‖ ^ (2 : ℕ) := by
    rw [← real_inner_self_eq_norm_sq]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, pow_two]
  have hcauchy :
      observerTemporalCoordinateAction gap (fun k => theta k) j ^ (2 : ℕ) ≤
        (∑ k : Fin τ, gap j k ^ (2 : ℕ)) *
          ∑ k : Fin τ, theta k ^ (2 : ℕ) := by
    exact Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin τ))
      (fun k => gap j k) (fun k => theta k)
  rw [hnorm] at hcauchy
  have hmetric :
      observerTemporalCoordinateAction gap (fun k => theta k) j ^ (2 : ℕ) ≤
        B * ‖theta‖ ^ (2 : ℕ) := by
    exact hcauchy.trans
      (mul_le_mul_of_nonneg_right hgap (sq_nonneg ‖theta‖))
  have hmul :
      ‖theta‖ * Real.sqrt B < Real.pi :=
    (lt_div_iff₀ hsqrtB).mp htheta
  have hmulNonneg :
      0 ≤ ‖theta‖ * Real.sqrt B :=
    mul_nonneg (norm_nonneg theta) hsqrtB.le
  have hsq :
      (‖theta‖ * Real.sqrt B) ^ (2 : ℕ) < Real.pi ^ (2 : ℕ) :=
    (sq_lt_sq₀ hmulNonneg Real.pi_pos.le).2 hmul
  have hsqrtSq : (Real.sqrt B) ^ (2 : ℕ) = B :=
    Real.sq_sqrt hB.le
  have hactionSq :
      observerTemporalCoordinateAction gap (fun k => theta k) j ^ (2 : ℕ) <
        Real.pi ^ (2 : ℕ) := by
    calc
      observerTemporalCoordinateAction gap (fun k => theta k) j ^ (2 : ℕ) ≤
          B * ‖theta‖ ^ (2 : ℕ) := hmetric
      _ = (‖theta‖ * Real.sqrt B) ^ (2 : ℕ) := by
        rw [mul_pow, hsqrtSq]
        ring
      _ < Real.pi ^ (2 : ℕ) := hsq
  exact ((sq_lt_sq₀ (abs_nonneg _) Real.pi_pos.le).mp
    (by simpa [sq_abs] using hactionSq)).le

end

end GaloisForLFunctions.HTGeometry
