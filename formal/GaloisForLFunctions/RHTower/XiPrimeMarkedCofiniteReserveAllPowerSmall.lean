import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMQuarticIncidence

/-!
# Positive-scale cofinite K-RVM reserves with uniformly small power energies

Move the reciprocal-RVM diagonal past an arbitrary prime prefix and retain
the cofinal triangle cycle at a positive scale. Both pieces can be made
jointly small in Hilbert--Schmidt energy. Once that energy is at most one,
every positive power has no greater energy. This supplies all-order reserve
control without proving any source-to-carrier moment identity.
-/

namespace RHTower
noncomputable section

/-- Cofinite reciprocal diagonal plus a positively scalable cycle carrier. -/
def routeKVariableCofiniteReserve (N : ℕ) (δ : ℝ) :
    RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  routeKRVMTailOperator (routeKInitialPrimeFinset N) +
    (δ : ℂ) • routeKCofinalTriangleNuclearCarrierFrom N

/-- The variable reserve is Hilbert--Schmidt. -/
theorem routeKVariableCofiniteReserve_isHilbertSchmidt (N : ℕ) (δ : ℝ) :
    (routeKVariableCofiniteReserve N δ).IsHilbertSchmidt := by
  unfold routeKVariableCofiniteReserve
  exact (routeKRVMTailOperator_isHilbertSchmidt _).add
    ((routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt N).smul _)

/-- Real cycle scaling preserves self-adjointness. -/
theorem routeKVariableCofiniteReserve_isSelfAdjoint (N : ℕ) (δ : ℝ) :
    IsSelfAdjoint (routeKVariableCofiniteReserve N δ) := by
  unfold routeKVariableCofiniteReserve
  apply IsSelfAdjoint.add
  · exact routeKRVMTailOperator_isSelfAdjoint _
  · apply IsSelfAdjoint.smul
    · simp [IsSelfAdjoint]
    · exact routeKCofinalTriangleNuclearCarrierFrom_isSelfAdjoint N

private theorem hsNormSq_pow_succ_le_self_of_hsNormSq_le_one
    (T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (hT : T.IsHilbertSchmidt)
    (hsmall : ContinuousLinearMap.hsNormSq T ≤ 1) (n : ℕ) :
    ContinuousLinearMap.hsNormSq (T ^ (n + 1)) ≤
      ContinuousLinearMap.hsNormSq T := by
  have hop : ‖T‖ ^ (2 : ℕ) ≤ 1 := by
    have hdom := ContinuousLinearMap.opNorm_le_hsNorm hT
    have hhs : ContinuousLinearMap.hsNorm T ^ (2 : ℕ) =
        ContinuousLinearMap.hsNormSq T := by
      rw [ContinuousLinearMap.hsNorm,
        Real.sq_sqrt (ContinuousLinearMap.hsNormSq_nonneg T)]
    nlinarith [norm_nonneg T, ContinuousLinearMap.hsNorm_nonneg T]
  induction n with
  | zero => simp
  | succ n ih =>
      have hpowHS : (T ^ (n + 1)).IsHilbertSchmidt := by
        rw [pow_succ, ContinuousLinearMap.mul_def]
        exact hT.comp_left (T ^ n)
      have heq : T ^ (n + 1 + 1) = T ∘L T ^ (n + 1) := by
        change T ^ (n + 1 + 1) = T * T ^ (n + 1)
        rw [pow_succ']
      have hcomp := HTGeometry.hsNormSq_comp_left_le_opNorm hpowHS T
      have hprod : ‖T‖ ^ (2 : ℕ) *
          ContinuousLinearMap.hsNormSq (T ^ (n + 1)) ≤
          ContinuousLinearMap.hsNormSq (T ^ (n + 1)) := by
        have hnonneg := ContinuousLinearMap.hsNormSq_nonneg (T ^ (n + 1))
        nlinarith [mul_nonneg (sub_nonneg.mpr hop) hnonneg]
      rw [show n + 1 + 1 = n.succ + 1 by omega] at heq
      rw [heq]
      exact (hcomp.trans hprod).trans ih

/-- Every prime prefix admits a positive cycle scale and a later RVM tail
whose joint Hilbert--Schmidt energy is arbitrarily small. -/
theorem exists_routeKVariableCofiniteReserve_arbitrarilySmall
    {ε : ℝ} (hε : 0 < ε) (Nmin : ℕ) :
    ∃ N : ℕ, Nmin ≤ N ∧ ∃ δ : ℝ, 0 < δ ∧
      ContinuousLinearMap.hsNormSq (routeKVariableCofiniteReserve N δ) < ε := by
  obtain ⟨N, hN, htail⟩ :=
    exists_routeKRVM_initial_tail_energy_lt
      (div_pos hε (by norm_num : (0:ℝ) < 4)) Nmin
  obtain ⟨δ, hδ, hcycle⟩ :=
    exists_pos_scale_hsNormSq_smul_lt
      (routeKCofinalTriangleNuclearCarrierFrom N)
      (routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt N)
      (div_pos hε (by norm_num : (0:ℝ) < 4))
  refine ⟨N, hN, δ, hδ, ?_⟩
  have hle := ContinuousLinearMap.hsNormSq_add_le
    (routeKRVMTailOperator_isHilbertSchmidt (routeKInitialPrimeFinset N))
    ((routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt N).smul (δ : ℂ))
  change ContinuousLinearMap.hsNormSq (routeKVariableCofiniteReserve N δ) ≤
    2 * ContinuousLinearMap.hsNormSq
      (routeKRVMTailOperator (routeKInitialPrimeFinset N)) +
    2 * ContinuousLinearMap.hsNormSq
      ((δ : ℂ) • routeKCofinalTriangleNuclearCarrierFrom N) at hle
  linarith

/-- One cofinite reserve keeps the positive cycle while uniformly bounding
the Hilbert--Schmidt energy of every positive power. -/
theorem exists_routeKVariableCofiniteReserve_allPowerEnergiesSmall
    {ε : ℝ} (hε : 0 < ε) (Nmin : ℕ) :
    ∃ N : ℕ, Nmin ≤ N ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ, ContinuousLinearMap.hsNormSq
        ((routeKVariableCofiniteReserve N δ) ^ (n + 1)) < ε := by
  obtain ⟨N, hN, δ, hδ, hsmall⟩ :=
    exists_routeKVariableCofiniteReserve_arbitrarilySmall
      (lt_min hε zero_lt_one) Nmin
  refine ⟨N, hN, δ, hδ, fun n => ?_⟩
  have hε' : ContinuousLinearMap.hsNormSq
      (routeKVariableCofiniteReserve N δ) < ε :=
    lt_of_lt_of_le hsmall (min_le_left _ _)
  have hOne : ContinuousLinearMap.hsNormSq
      (routeKVariableCofiniteReserve N δ) ≤ 1 :=
    (lt_of_lt_of_le hsmall (min_le_right _ _)).le
  exact (hsNormSq_pow_succ_le_self_of_hsNormSq_le_one
    (routeKVariableCofiniteReserve N δ)
    (routeKVariableCofiniteReserve_isHilbertSchmidt N δ) hOne n).trans_lt hε'

end
end RHTower
