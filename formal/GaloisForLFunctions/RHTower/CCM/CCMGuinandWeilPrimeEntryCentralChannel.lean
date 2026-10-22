import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilPrimeEntryAtomicConnection

/-!
# Central-channel classification of the prime-entry connection

The Guinand--Weil prime-entry tangent is negative, but it has only one active direction.  This
file identifies that direction and the exact blind sector.  A tangent applied to coefficient
vector `v` depends only on `sum v`; hence its kernel is the zero-sum hyperplane and canonical
centering annihilates it.  The constant CCM boundary vector is its unique active direction.

For every finite nontrivial packet containing a genuine prime power, the cumulative connection has
strictly negative trace and rank exactly one.  Thus first-order prime-entry negativity lives only
in the central boundary channel.  Any RH-sensitive centered transport must create a transverse
coupling through a higher jet or through the completed polar--Gamma dynamics; scalar attenuation
of this first jet cannot do so.
-/

open scoped BigOperators

namespace RHTower

open Matrix

noncomputable section

/-- Remove the mean from a coefficient packet. -/
def ccmGuinandWeilCenterCoefficients (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) : Fin (2 * N + 1) → ℝ :=
  fun i => v i - (∑ j, v j) / (2 * N + 1 : ℕ)

/-- A single prime-entry tangent observes exactly the total coefficient mass. -/
theorem ccmGuinandWeilPrimeEntryRankOneTangent_mulVec_apply
    (k N : ℕ) (v : Fin (2 * N + 1) → ℝ) (i : Fin (2 * N + 1)) :
    (ccmGuinandWeilPrimeEntryRankOneTangent k N *ᵥ v) i =
      ccmGuinandWeilPrimeEntryMatrixRate k * ∑ j, v j := by
  simp only [ccmGuinandWeilPrimeEntryRankOneTangent, Matrix.mulVec, dotProduct,
    Matrix.smul_apply, Matrix.vecMulVec_apply, ccmConstantBoundary,
    smul_eq_mul, one_mul]
  rw [← Finset.mul_sum]
  ring

/-- **Exact single-event blind sector.**  For a genuine prime power, the tangent kernel is exactly
the zero-sum hyperplane. -/
theorem ccmGuinandWeilPrimeEntryRankOneTangent_mulVec_eq_zero_iff
    {k : ℕ} (hk : IsPrimePow k) (N : ℕ) (v : Fin (2 * N + 1) → ℝ) :
    ccmGuinandWeilPrimeEntryRankOneTangent k N *ᵥ v = 0 ↔ ∑ i, v i = 0 := by
  constructor
  · intro h
    have hi : ccmGuinandWeilPrimeEntryMatrixRate k * ∑ i, v i = 0 := by
      simpa [ccmGuinandWeilPrimeEntryRankOneTangent_mulVec_apply] using
        congrFun h (0 : Fin (2 * N + 1))
    exact (mul_eq_zero.mp hi).resolve_left
      (ccmGuinandWeilPrimeEntryMatrixRate_neg hk).ne
  · intro hv
    funext i
    rw [ccmGuinandWeilPrimeEntryRankOneTangent_mulVec_apply, hv, mul_zero]
    rfl

/-- Canonical mean subtraction lands in the zero-sum hyperplane. -/
theorem sum_ccmGuinandWeilCenterCoefficients
    (N : ℕ) (v : Fin (2 * N + 1) → ℝ) :
    ∑ i, ccmGuinandWeilCenterCoefficients N v i = 0 := by
  simp only [ccmGuinandWeilCenterCoefficients, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd : (2 * N + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Every single prime-entry first jet is annihilated by canonical coefficient centering. -/
theorem ccmGuinandWeilPrimeEntryRankOneTangent_centerCoefficients_eq_zero
    (k N : ℕ) (v : Fin (2 * N + 1) → ℝ) :
    ccmGuinandWeilPrimeEntryRankOneTangent k N *ᵥ
        ccmGuinandWeilCenterCoefficients N v = 0 := by
  funext i
  rw [ccmGuinandWeilPrimeEntryRankOneTangent_mulVec_apply,
    sum_ccmGuinandWeilCenterCoefficients, mul_zero]
  rfl

/-- The constant CCM boundary vector is the active eigendirection of a single event. -/
theorem ccmGuinandWeilPrimeEntryRankOneTangent_constantBoundary_eigen
    (k N : ℕ) :
    ccmGuinandWeilPrimeEntryRankOneTangent k N *ᵥ
        (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) =
      ((2 * N + 1 : ℕ) * ccmGuinandWeilPrimeEntryMatrixRate k) •
        (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) := by
  funext i
  rw [ccmGuinandWeilPrimeEntryRankOneTangent_mulVec_apply]
  simp [ccmConstantBoundary]
  ring

/-- Exact trace of a single prime-entry tangent. -/
theorem ccmGuinandWeilPrimeEntryRankOneTangent_trace
    (k N : ℕ) :
    Matrix.trace (ccmGuinandWeilPrimeEntryRankOneTangent k N) =
      (2 * N + 1 : ℕ) * ccmGuinandWeilPrimeEntryMatrixRate k := by
  simp [Matrix.trace, ccmGuinandWeilPrimeEntryRankOneTangent,
    Matrix.vecMulVec_apply, ccmConstantBoundary]

/-- Every genuine prime-power event has rank exactly one, strengthening the prior upper bound. -/
theorem ccmGuinandWeilPrimeEntryRankOneTangent_rank_eq_one
    {k : ℕ} (hk : IsPrimePow k) (N : ℕ) :
    (ccmGuinandWeilPrimeEntryRankOneTangent k N).rank = 1 := by
  apply le_antisymm
  · exact ccmGuinandWeilPrimeEntryRankOneTangent_rank_le_one k N
  · suffices 0 < (ccmGuinandWeilPrimeEntryRankOneTangent k N).rank by omega
    by_contra h
    have hrank : (ccmGuinandWeilPrimeEntryRankOneTangent k N).rank = 0 :=
      Nat.eq_zero_of_not_pos h
    have hrange :
        LinearMap.range
            (ccmGuinandWeilPrimeEntryRankOneTangent k N).mulVecLin = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      simpa [Matrix.rank] using hrank
    have hlin :
        (ccmGuinandWeilPrimeEntryRankOneTangent k N).mulVecLin = 0 :=
      LinearMap.range_eq_bot.mp hrange
    have he := DFunLike.congr_fun hlin
      (ccmConstantBoundary : Fin (2 * N + 1) → ℝ)
    have he0 :
        ccmGuinandWeilPrimeEntryRankOneTangent k N *ᵥ
            (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) = 0 := by
      simpa using he
    rw [ccmGuinandWeilPrimeEntryRankOneTangent_constantBoundary_eigen] at he0
    have hi := congrFun he0 (0 : Fin (2 * N + 1))
    simp [ccmConstantBoundary] at hi
    rcases hi with hi | hi
    · exact (by positivity : (2 * (N : ℝ) + 1) ≠ 0) hi
    · exact (ccmGuinandWeilPrimeEntryMatrixRate_neg hk).ne hi

/-- Every finite atomic connection still observes only total coefficient mass. -/
theorem ccmGuinandWeilPrimeEntryAtomicTangent_mulVec_apply
    (S : Finset ℕ) (N : ℕ) (v : Fin (2 * N + 1) → ℝ)
    (i : Fin (2 * N + 1)) :
    (ccmGuinandWeilPrimeEntryAtomicTangent S N *ᵥ v) i =
      ccmGuinandWeilPrimeEntryAtomicRate S * ∑ j, v j := by
  rw [ccmGuinandWeilPrimeEntryAtomicTangent_eq_rankOne]
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply,
    ccmConstantBoundary, smul_eq_mul, one_mul]
  rw [← Finset.mul_sum]
  ring

/-- A nontrivial finite packet containing a genuine prime power has strictly negative total rate. -/
theorem ccmGuinandWeilPrimeEntryAtomicRate_neg
    {S : Finset ℕ} (hS : ∀ k ∈ S, 1 < k)
    (hprime : ∃ k ∈ S, IsPrimePow k) :
    ccmGuinandWeilPrimeEntryAtomicRate S < 0 := by
  rw [ccmGuinandWeilPrimeEntryAtomicRate]
  have hlt :
      (∑ k ∈ S, ccmGuinandWeilPrimeEntryMatrixRate k) <
        ∑ _k ∈ S, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro k hk
      exact ccmGuinandWeilPrimeEntryMatrixRate_nonpos (hS k hk)
    · obtain ⟨k, hk, hkpow⟩ := hprime
      exact ⟨k, hk, ccmGuinandWeilPrimeEntryMatrixRate_neg hkpow⟩
  simpa using hlt

/-- **Exact aggregate blind sector.**  A nontrivial finite prime packet has kernel precisely the
zero-sum hyperplane. -/
theorem ccmGuinandWeilPrimeEntryAtomicTangent_mulVec_eq_zero_iff
    {S : Finset ℕ} (hS : ∀ k ∈ S, 1 < k)
    (hprime : ∃ k ∈ S, IsPrimePow k) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) :
    ccmGuinandWeilPrimeEntryAtomicTangent S N *ᵥ v = 0 ↔ ∑ i, v i = 0 := by
  constructor
  · intro h
    have hi : ccmGuinandWeilPrimeEntryAtomicRate S * ∑ i, v i = 0 := by
      simpa [ccmGuinandWeilPrimeEntryAtomicTangent_mulVec_apply] using
        congrFun h (0 : Fin (2 * N + 1))
    exact (mul_eq_zero.mp hi).resolve_left
      (ccmGuinandWeilPrimeEntryAtomicRate_neg hS hprime).ne
  · intro hv
    funext i
    rw [ccmGuinandWeilPrimeEntryAtomicTangent_mulVec_apply, hv, mul_zero]
    rfl

/-- The finite atomic connection has the same constant-boundary eigendirection. -/
theorem ccmGuinandWeilPrimeEntryAtomicTangent_constantBoundary_eigen
    (S : Finset ℕ) (N : ℕ) :
    ccmGuinandWeilPrimeEntryAtomicTangent S N *ᵥ
        (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) =
      ((2 * N + 1 : ℕ) * ccmGuinandWeilPrimeEntryAtomicRate S) •
        (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) := by
  funext i
  rw [ccmGuinandWeilPrimeEntryAtomicTangent_mulVec_apply]
  simp [ccmConstantBoundary]
  ring

/-- Exact trace of the finite atomic connection. -/
theorem ccmGuinandWeilPrimeEntryAtomicTangent_trace
    (S : Finset ℕ) (N : ℕ) :
    Matrix.trace (ccmGuinandWeilPrimeEntryAtomicTangent S N) =
      (2 * N + 1 : ℕ) * ccmGuinandWeilPrimeEntryAtomicRate S := by
  rw [ccmGuinandWeilPrimeEntryAtomicTangent_eq_rankOne]
  simp [Matrix.trace, Matrix.vecMulVec_apply, ccmConstantBoundary]

/-- Every nontrivial finite prime packet has strictly negative trace. -/
theorem ccmGuinandWeilPrimeEntryAtomicTangent_trace_neg
    {S : Finset ℕ} (hS : ∀ k ∈ S, 1 < k)
    (hprime : ∃ k ∈ S, IsPrimePow k) (N : ℕ) :
    Matrix.trace (ccmGuinandWeilPrimeEntryAtomicTangent S N) < 0 := by
  rw [ccmGuinandWeilPrimeEntryAtomicTangent_trace]
  exact mul_neg_of_pos_of_neg (by positivity)
    (ccmGuinandWeilPrimeEntryAtomicRate_neg hS hprime)

/-- Every nontrivial finite prime packet has rank exactly one.  Adding more entry events changes
only its scalar eigenvalue, never its active direction. -/
theorem ccmGuinandWeilPrimeEntryAtomicTangent_rank_eq_one
    {S : Finset ℕ} (hS : ∀ k ∈ S, 1 < k)
    (hprime : ∃ k ∈ S, IsPrimePow k) (N : ℕ) :
    (ccmGuinandWeilPrimeEntryAtomicTangent S N).rank = 1 := by
  apply le_antisymm
  · exact ccmGuinandWeilPrimeEntryAtomicTangent_rank_le_one S N
  · suffices 0 < (ccmGuinandWeilPrimeEntryAtomicTangent S N).rank by omega
    by_contra h
    have hrank : (ccmGuinandWeilPrimeEntryAtomicTangent S N).rank = 0 :=
      Nat.eq_zero_of_not_pos h
    have hrange :
        LinearMap.range
            (ccmGuinandWeilPrimeEntryAtomicTangent S N).mulVecLin = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      simpa [Matrix.rank] using hrank
    have hlin :
        (ccmGuinandWeilPrimeEntryAtomicTangent S N).mulVecLin = 0 :=
      LinearMap.range_eq_bot.mp hrange
    have he := DFunLike.congr_fun hlin
      (ccmConstantBoundary : Fin (2 * N + 1) → ℝ)
    have he0 :
        ccmGuinandWeilPrimeEntryAtomicTangent S N *ᵥ
            (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) = 0 := by
      simpa using he
    rw [ccmGuinandWeilPrimeEntryAtomicTangent_constantBoundary_eigen] at he0
    have hi := congrFun he0 (0 : Fin (2 * N + 1))
    simp [ccmConstantBoundary] at hi
    rcases hi with hi | hi
    · exact (by positivity : (2 * (N : ℝ) + 1) ≠ 0) hi
    · exact (ccmGuinandWeilPrimeEntryAtomicRate_neg hS hprime).ne hi

/-- **Central-channel obstruction.**  The complete finite atomic first jet vanishes after canonical
coefficient centering. -/
theorem ccmGuinandWeilPrimeEntryAtomicTangent_centerCoefficients_eq_zero
    (S : Finset ℕ) (N : ℕ) (v : Fin (2 * N + 1) → ℝ) :
    ccmGuinandWeilPrimeEntryAtomicTangent S N *ᵥ
        ccmGuinandWeilCenterCoefficients N v = 0 := by
  funext i
  rw [ccmGuinandWeilPrimeEntryAtomicTangent_mulVec_apply,
    sum_ccmGuinandWeilCenterCoefficients, mul_zero]
  rfl

end

end RHTower
