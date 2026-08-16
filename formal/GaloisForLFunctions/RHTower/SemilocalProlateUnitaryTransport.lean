import GaloisForLFunctions.RHTower.SoninSemilocalJacobiResidueCorollaries

/-!
# The semilocal prolate unitary-transport trilemma

A unitary that intertwines both the scaling operator and the number operator of two cyclic pairs
must match their first Jacobi coefficients: the number operator pins the ground state, and unitarity
transports `‖D p₀‖` exactly.  Since the normalized semilocal first Jacobi coefficient contracts
strictly below the archimedean value `1/2`, no such unitary exists.

Intertwining the formal prolate families at two distinct positive parameters is no weaker:
subtracting the two identities recovers the number-operator intertwining, and the remaining identity
transports `⟪p₀, D² p₀⟫ = ‖D p₀‖²`.

## Main results

* `norm_scaling_ground_eq_of_unitary_transport` — a scaling/grading unitary matches `‖D p₀‖`;
* `not_exists_unitary_transport` — hence a strict contraction forbids it;
* `norm_scaling_ground_eq_of_unitary_prolate_transport` — the two-parameter prolate version;
* `semilocal_normalizedSecondMoment_lt_archimedean` — the concrete strict contraction.
-/

noncomputable section

namespace RHTower

open scoped InnerProductSpace

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

/-- The ground state is transported up to a unimodular scalar. -/
theorem exists_unimodular_of_ground_transport {N₁ : H₁ →L[ℂ] H₁} {N₂ : H₂ →L[ℂ] H₂}
    {p₁ : H₁} {p₂ : H₂} (hp₁ : ‖p₁‖ = 1) (hp₂ : ‖p₂‖ = 1)
    (hN₁ : N₁ p₁ = 0)
    (hker : ∀ v : H₂, N₂ v = 0 → ∃ c : ℂ, v = c • p₂)
    (U : H₁ ≃ₗᵢ[ℂ] H₂) (hN : ∀ v, U (N₁ v) = N₂ (U v)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ U p₁ = c • p₂ := by
  have hzero : N₂ (U p₁) = 0 := by
    rw [← hN, hN₁, map_zero]
  obtain ⟨c, hc⟩ := hker _ hzero
  refine ⟨c, ?_, hc⟩
  have hnorm : ‖U p₁‖ = 1 := by rw [U.norm_map, hp₁]
  rw [hc, norm_smul, hp₂, mul_one] at hnorm
  exact hnorm

/-- **A scaling/grading unitary matches the first Jacobi coefficient.** -/
theorem norm_scaling_ground_eq_of_unitary_transport {D₁ N₁ : H₁ →L[ℂ] H₁}
    {D₂ N₂ : H₂ →L[ℂ] H₂} {p₁ : H₁} {p₂ : H₂} (hp₁ : ‖p₁‖ = 1) (hp₂ : ‖p₂‖ = 1)
    (hN₁ : N₁ p₁ = 0)
    (hker : ∀ v : H₂, N₂ v = 0 → ∃ c : ℂ, v = c • p₂)
    (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (hD : ∀ v, U (D₁ v) = D₂ (U v)) (hN : ∀ v, U (N₁ v) = N₂ (U v)) :
    ‖D₁ p₁‖ = ‖D₂ p₂‖ := by
  obtain ⟨c, hc1, hc⟩ := exists_unimodular_of_ground_transport hp₁ hp₂ hN₁ hker U hN
  calc ‖D₁ p₁‖ = ‖U (D₁ p₁)‖ := (U.norm_map _).symm
    _ = ‖D₂ (U p₁)‖ := by rw [hD]
    _ = ‖D₂ (c • p₂)‖ := by rw [hc]
    _ = ‖D₂ p₂‖ := by rw [map_smul, norm_smul, hc1, one_mul]

/-- **The transport no-go.**  A strict contraction of the first Jacobi coefficient rules out every
simultaneous scaling/grading unitary. -/
theorem not_exists_unitary_transport {D₁ N₁ : H₁ →L[ℂ] H₁}
    {D₂ N₂ : H₂ →L[ℂ] H₂} {p₁ : H₁} {p₂ : H₂} (hp₁ : ‖p₁‖ = 1) (hp₂ : ‖p₂‖ = 1)
    (hN₁ : N₁ p₁ = 0)
    (hker : ∀ v : H₂, N₂ v = 0 → ∃ c : ℂ, v = c • p₂)
    (hlt : ‖D₂ p₂‖ < ‖D₁ p₁‖) :
    ¬ ∃ U : H₁ ≃ₗᵢ[ℂ] H₂,
        (∀ v, U (D₁ v) = D₂ (U v)) ∧ (∀ v, U (N₁ v) = N₂ (U v)) := by
  rintro ⟨U, hD, hN⟩
  have := norm_scaling_ground_eq_of_unitary_transport hp₁ hp₂ hN₁ hker U hD hN
  linarith

/-! ### The two-parameter prolate version -/

/-- The formal prolate operator `-D² + λ² N`. -/
def prolateOp (D N : H₁ →L[ℂ] H₁) (lam : ℂ) : H₁ →L[ℂ] H₁ :=
  -(D.comp D) + (lam ^ 2) • N

/-- Two distinct prolate parameters recover the number-operator intertwining. -/
theorem number_transport_of_two_prolate {D₁ N₁ : H₁ →L[ℂ] H₁} {D₂ N₂ : H₂ →L[ℂ] H₂}
    {lam mu : ℂ} (hne : lam ^ 2 ≠ mu ^ 2) (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (hlam : ∀ v, U (prolateOp D₁ N₁ lam v) = prolateOp D₂ N₂ lam (U v))
    (hmu : ∀ v, U (prolateOp D₁ N₁ mu v) = prolateOp D₂ N₂ mu (U v)) :
    (∀ v, U (N₁ v) = N₂ (U v)) ∧ (∀ v, U (D₁ (D₁ v)) = D₂ (D₂ (U v))) := by
  have hN : ∀ v, U (N₁ v) = N₂ (U v) := by
    intro v
    have h1 := hlam v
    have h2 := hmu v
    simp only [prolateOp, add_apply, neg_apply,
      smul_apply, ContinuousLinearMap.comp_apply] at h1 h2
    rw [map_add, map_neg, map_smul] at h1 h2
    have key : (lam ^ 2 - mu ^ 2) • U (N₁ v) = (lam ^ 2 - mu ^ 2) • N₂ (U v) := by
      rw [sub_smul, sub_smul]
      linear_combination (norm := module) h1 - h2
    exact smul_right_injective _ (sub_ne_zero.mpr hne) key
  refine ⟨hN, fun v => ?_⟩
  have h1 := hlam v
  simp only [prolateOp, add_apply, neg_apply,
    smul_apply, ContinuousLinearMap.comp_apply] at h1
  rw [map_add, map_neg, map_smul, hN v] at h1
  have h2 : -U (D₁ (D₁ v)) = -(D₂ (D₂ (U v))) := add_right_cancel h1
  exact neg_injective h2

/-- **The two-parameter prolate transport also matches the first Jacobi coefficient.** -/
theorem norm_scaling_ground_eq_of_unitary_prolate_transport {D₁ N₁ : H₁ →L[ℂ] H₁}
    {D₂ N₂ : H₂ →L[ℂ] H₂} {p₁ : H₁} {p₂ : H₂} {lam mu : ℂ}
    (hp₁ : ‖p₁‖ = 1) (hp₂ : ‖p₂‖ = 1) (hN₁ : N₁ p₁ = 0)
    (hsa₁ : ∀ x y : H₁, ⟪D₁ x, y⟫_ℂ = ⟪x, D₁ y⟫_ℂ)
    (hsa₂ : ∀ x y : H₂, ⟪D₂ x, y⟫_ℂ = ⟪x, D₂ y⟫_ℂ)
    (hker : ∀ v : H₂, N₂ v = 0 → ∃ c : ℂ, v = c • p₂)
    (hne : lam ^ 2 ≠ mu ^ 2) (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (hlam : ∀ v, U (prolateOp D₁ N₁ lam v) = prolateOp D₂ N₂ lam (U v))
    (hmu : ∀ v, U (prolateOp D₁ N₁ mu v) = prolateOp D₂ N₂ mu (U v)) :
    ‖D₁ p₁‖ = ‖D₂ p₂‖ := by
  obtain ⟨hN, hDD⟩ := number_transport_of_two_prolate hne U hlam hmu
  obtain ⟨c, hc1, hc⟩ := exists_unimodular_of_ground_transport hp₁ hp₂ hN₁ hker U hN
  have hcc : (starRingEnd ℂ) c * c = 1 := by
    rw [RCLike.conj_mul, hc1]
    norm_num
  have hinner : (⟪p₁, D₁ (D₁ p₁)⟫_ℂ) = ⟪p₂, D₂ (D₂ p₂)⟫_ℂ := by
    have h1 : (⟪p₁, D₁ (D₁ p₁)⟫_ℂ) = ⟪U p₁, U (D₁ (D₁ p₁))⟫_ℂ := (U.inner_map_map _ _).symm
    rw [h1, hDD p₁, hc, map_smul, map_smul, inner_smul_left, inner_smul_right,
      ← mul_assoc, hcc, one_mul]
  have e₁ : (⟪p₁, D₁ (D₁ p₁)⟫_ℂ) = (‖D₁ p₁‖ : ℂ) ^ 2 := by
    rw [← hsa₁ p₁ (D₁ p₁), inner_self_eq_norm_sq_to_K]
    norm_cast
  have e₂ : (⟪p₂, D₂ (D₂ p₂)⟫_ℂ) = (‖D₂ p₂‖ : ℂ) ^ 2 := by
    rw [← hsa₂ p₂ (D₂ p₂), inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [e₁, e₂] at hinner
  have hreal : (‖D₁ p₁‖ : ℝ) ^ 2 = (‖D₂ p₂‖ : ℝ) ^ 2 := by exact_mod_cast hinner
  nlinarith [norm_nonneg (D₁ p₁), norm_nonneg (D₂ p₂)]

/-! ### The concrete semilocal contraction -/

/-- **The concrete strict contraction.**  The normalized semilocal first Jacobi coefficient is
strictly below the archimedean value `1/2`. -/
theorem semilocal_normalizedSecondMoment_lt_archimedean {n : ℕ} (p : Fin (n + 1) → ℕ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime) :
    semilocalFinitePrimeNormalizedSecondMoment p
      < semilocalArchimedeanJacobiCoefficient 0 ^ 2 := by
  have hsq := semilocalArchimedeanJacobiCoefficient_sq 0
  norm_num at hsq
  rw [hsq]
  exact semilocalFinitePrimeNormalizedSecondMoment_lt_half p hp hprime

end RHTower
