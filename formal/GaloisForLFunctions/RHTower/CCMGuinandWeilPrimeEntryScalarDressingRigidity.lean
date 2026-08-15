import GaloisForLFunctions.RHTower.CCMGuinandWeilPrimeEntryCentralChannel

/-!
# Scalar-dressing rigidity of the prime-entry connection

This file classifies every atomwise scalar dressing of the Guinand--Weil prime-entry first jet.
The dressing may depend arbitrarily on the integer index.  Nevertheless every dressed event remains
on the same constant-boundary outer product, so arbitrary finite dressed sums retain rank at most
one and annihilate all canonically centered coefficient packets.

For nonnegative dressings with at least one positive genuine prime-power weight, the dressed rate
and trace remain strictly negative, the rank is exactly one, and the kernel is still precisely the
zero-sum hyperplane.  Consequently no scalar attenuation--including a positive Julia attenuation
applied atomwise--can couple the entry first jet into the transverse centered CCM sector.  A viable
continuation must change direction, not merely magnitude.
-/

open scoped BigOperators

namespace RHTower

open Matrix

noncomputable section

/-- Scalar rate after arbitrary atomwise dressing. -/
def ccmGuinandWeilPrimeEntryDressedAtomicRate
    (dressing : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑ k ∈ S, dressing k * ccmGuinandWeilPrimeEntryMatrixRate k

/-- Matrix first jet after arbitrary atomwise scalar dressing. -/
def ccmGuinandWeilPrimeEntryDressedAtomicTangent
    (dressing : ℕ → ℝ) (S : Finset ℕ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ∑ k ∈ S, dressing k • ccmGuinandWeilPrimeEntryRankOneTangent k N

/-- **Dressing rigidity.**  Every finite atomwise scalar dressing factors through the same fixed
constant-boundary outer product. -/
theorem ccmGuinandWeilPrimeEntryDressedAtomicTangent_eq_rankOne
    (dressing : ℕ → ℝ) (S : Finset ℕ) (N : ℕ) :
    ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N =
      ccmGuinandWeilPrimeEntryDressedAtomicRate dressing S •
        Matrix.vecMulVec
          (ccmConstantBoundary : Fin (2 * N + 1) → ℝ)
          ccmConstantBoundary := by
  rw [ccmGuinandWeilPrimeEntryDressedAtomicTangent,
    ccmGuinandWeilPrimeEntryDressedAtomicRate]
  simp_rw [ccmGuinandWeilPrimeEntryRankOneTangent, smul_smul]
  rw [Finset.sum_smul]

/-- A dressed connection still observes only total coefficient mass. -/
theorem ccmGuinandWeilPrimeEntryDressedAtomicTangent_mulVec_apply
    (dressing : ℕ → ℝ) (S : Finset ℕ) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) (i : Fin (2 * N + 1)) :
    (ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N *ᵥ v) i =
      ccmGuinandWeilPrimeEntryDressedAtomicRate dressing S * ∑ j, v j := by
  rw [ccmGuinandWeilPrimeEntryDressedAtomicTangent_eq_rankOne]
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply,
    Matrix.vecMulVec_apply, ccmConstantBoundary, smul_eq_mul, one_mul]
  rw [← Finset.mul_sum]
  ring

/-- **Scalar-dressing no-go.**  Arbitrary atomwise scalar dressing cannot make the entry first jet
visible on canonically centered coefficient packets. -/
theorem ccmGuinandWeilPrimeEntryDressedAtomicTangent_centerCoefficients_eq_zero
    (dressing : ℕ → ℝ) (S : Finset ℕ) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) :
    ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N *ᵥ
        ccmGuinandWeilCenterCoefficients N v = 0 := by
  funext i
  rw [ccmGuinandWeilPrimeEntryDressedAtomicTangent_mulVec_apply,
    sum_ccmGuinandWeilCenterCoefficients, mul_zero]
  rfl

/-- Arbitrary atomwise scalar dressing cannot raise the connection above rank one. -/
theorem ccmGuinandWeilPrimeEntryDressedAtomicTangent_rank_le_one
    (dressing : ℕ → ℝ) (S : Finset ℕ) (N : ℕ) :
    (ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N).rank ≤ 1 := by
  rw [ccmGuinandWeilPrimeEntryDressedAtomicTangent_eq_rankOne]
  have heq :
      (ccmGuinandWeilPrimeEntryDressedAtomicRate dressing S •
          Matrix.vecMulVec
            (ccmConstantBoundary : Fin (2 * N + 1) → ℝ)
            (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) :
        Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ) =
        Matrix.vecMulVec
          (ccmGuinandWeilPrimeEntryDressedAtomicRate dressing S •
            (ccmConstantBoundary : Fin (2 * N + 1) → ℝ))
          (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) := by
    ext i j
    simp [Matrix.vecMulVec_apply, ccmConstantBoundary]
  rw [heq]
  exact Matrix.rank_vecMulVec_le _ _

/-- The dressed connection retains the constant CCM boundary eigendirection. -/
theorem ccmGuinandWeilPrimeEntryDressedAtomicTangent_constantBoundary_eigen
    (dressing : ℕ → ℝ) (S : Finset ℕ) (N : ℕ) :
    ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N *ᵥ
        (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) =
      ((2 * N + 1 : ℕ) *
          ccmGuinandWeilPrimeEntryDressedAtomicRate dressing S) •
        (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) := by
  funext i
  rw [ccmGuinandWeilPrimeEntryDressedAtomicTangent_mulVec_apply]
  simp [ccmConstantBoundary]
  ring

/-- Exact trace of an arbitrarily dressed finite connection. -/
theorem ccmGuinandWeilPrimeEntryDressedAtomicTangent_trace
    (dressing : ℕ → ℝ) (S : Finset ℕ) (N : ℕ) :
    Matrix.trace
        (ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N) =
      (2 * N + 1 : ℕ) *
        ccmGuinandWeilPrimeEntryDressedAtomicRate dressing S := by
  rw [ccmGuinandWeilPrimeEntryDressedAtomicTangent_eq_rankOne]
  simp [Matrix.trace, Matrix.vecMulVec_apply, ccmConstantBoundary]

/-- Nonnegative dressing with one active prime power preserves strict negative orientation. -/
theorem ccmGuinandWeilPrimeEntryDressedAtomicRate_neg
    {dressing : ℕ → ℝ} {S : Finset ℕ}
    (hS : ∀ k ∈ S, 1 < k) (hdressing : ∀ k ∈ S, 0 ≤ dressing k)
    (hactive : ∃ k ∈ S, IsPrimePow k ∧ 0 < dressing k) :
    ccmGuinandWeilPrimeEntryDressedAtomicRate dressing S < 0 := by
  rw [ccmGuinandWeilPrimeEntryDressedAtomicRate]
  have hlt :
      (∑ k ∈ S, dressing k * ccmGuinandWeilPrimeEntryMatrixRate k) <
        ∑ _k ∈ S, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro k hk
      exact mul_nonpos_of_nonneg_of_nonpos (hdressing k hk)
        (ccmGuinandWeilPrimeEntryMatrixRate_nonpos (hS k hk))
    · obtain ⟨k, hk, hkpow, hdresspos⟩ := hactive
      exact ⟨k, hk, mul_neg_of_pos_of_neg hdresspos
        (ccmGuinandWeilPrimeEntryMatrixRate_neg hkpow)⟩
  simpa using hlt

/-- With one positively dressed prime power, the dressed kernel remains exactly the zero-sum
hyperplane. -/
theorem ccmGuinandWeilPrimeEntryDressedAtomicTangent_mulVec_eq_zero_iff
    {dressing : ℕ → ℝ} {S : Finset ℕ}
    (hS : ∀ k ∈ S, 1 < k) (hdressing : ∀ k ∈ S, 0 ≤ dressing k)
    (hactive : ∃ k ∈ S, IsPrimePow k ∧ 0 < dressing k) (N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) :
    ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N *ᵥ v = 0 ↔
      ∑ i, v i = 0 := by
  constructor
  · intro h
    have hi : ccmGuinandWeilPrimeEntryDressedAtomicRate dressing S * ∑ i, v i = 0 := by
      simpa [ccmGuinandWeilPrimeEntryDressedAtomicTangent_mulVec_apply] using
        congrFun h (0 : Fin (2 * N + 1))
    exact (mul_eq_zero.mp hi).resolve_left
      (ccmGuinandWeilPrimeEntryDressedAtomicRate_neg hS hdressing hactive).ne
  · intro hv
    funext i
    rw [ccmGuinandWeilPrimeEntryDressedAtomicTangent_mulVec_apply, hv, mul_zero]
    rfl

/-- Nonnegative active dressing preserves strict negativity of the trace. -/
theorem ccmGuinandWeilPrimeEntryDressedAtomicTangent_trace_neg
    {dressing : ℕ → ℝ} {S : Finset ℕ}
    (hS : ∀ k ∈ S, 1 < k) (hdressing : ∀ k ∈ S, 0 ≤ dressing k)
    (hactive : ∃ k ∈ S, IsPrimePow k ∧ 0 < dressing k) (N : ℕ) :
    Matrix.trace
        (ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N) < 0 := by
  rw [ccmGuinandWeilPrimeEntryDressedAtomicTangent_trace]
  exact mul_neg_of_pos_of_neg (by positivity)
    (ccmGuinandWeilPrimeEntryDressedAtomicRate_neg hS hdressing hactive)

/-- Nonnegative active dressing preserves exact rank one. -/
theorem ccmGuinandWeilPrimeEntryDressedAtomicTangent_rank_eq_one
    {dressing : ℕ → ℝ} {S : Finset ℕ}
    (hS : ∀ k ∈ S, 1 < k) (hdressing : ∀ k ∈ S, 0 ≤ dressing k)
    (hactive : ∃ k ∈ S, IsPrimePow k ∧ 0 < dressing k) (N : ℕ) :
    (ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N).rank = 1 := by
  apply le_antisymm
  · exact ccmGuinandWeilPrimeEntryDressedAtomicTangent_rank_le_one dressing S N
  · suffices 0 <
        (ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N).rank by omega
    by_contra h
    have hrank :
        (ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N).rank = 0 :=
      Nat.eq_zero_of_not_pos h
    have hrange :
        LinearMap.range
            (ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N).mulVecLin = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      simpa [Matrix.rank] using hrank
    have hlin :
        (ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N).mulVecLin = 0 :=
      LinearMap.range_eq_bot.mp hrange
    have he := DFunLike.congr_fun hlin
      (ccmConstantBoundary : Fin (2 * N + 1) → ℝ)
    have he0 :
        ccmGuinandWeilPrimeEntryDressedAtomicTangent dressing S N *ᵥ
            (ccmConstantBoundary : Fin (2 * N + 1) → ℝ) = 0 := by
      simpa using he
    rw [ccmGuinandWeilPrimeEntryDressedAtomicTangent_constantBoundary_eigen] at he0
    have hi := congrFun he0 (0 : Fin (2 * N + 1))
    simp [ccmConstantBoundary] at hi
    rcases hi with hi | hi
    · exact (by positivity : (2 * (N : ℝ) + 1) ≠ 0) hi
    · exact (ccmGuinandWeilPrimeEntryDressedAtomicRate_neg
        hS hdressing hactive).ne hi

end

end RHTower
