import GaloisForLFunctions.HTGeometry.DifferentialOperatorCyclicDimension
import GaloisForLFunctions.RepresentationLifting.OperatorKernels.CompositionCokernel

/-!
# Filtered dimensions of cyclic differential-operator quotients

The first `n` operator coefficients have image dimension `min n (degree d)`
modulo a nonzero left multiple relation `d`. Thus the Hilbert function
stabilizes exactly at the order of the relation, and its kernel grows as
`n - degree d`. This is an exact one-variable instance of the filtered
dimension-difference argument in Zehavi, equations (26)–(28), arXiv:2611.18218.
-/

noncomputable section

open scoped Differential

namespace GaloisForLFunctions.RepresentationLifting.Filtered

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.DiffOp
open OperatorKernels

variable {K W : Type*} [Field K] [Differential K]
  [AddCommGroup W] [Module K W]

/-- Truncated coefficients followed by the cyclic quotient map. -/
def oreTruncatedQuotient (d : DiffOp K) (n : ℕ) :
    (Fin n → K) →ₗ[K] (DiffOp K ⧸ leftMultiples d) :=
  (leftMultiples d).mkQ.comp (truncLTLin n)

private theorem oreTruncatedQuotient_injective (d : DiffOp K) (n : ℕ)
    (h : d = 0 ∨ n ≤ DiffOp.degree d) :
    Function.Injective (oreTruncatedQuotient d n) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  have hm : truncLT c ∈ leftMultiples d :=
    (Submodule.Quotient.mk_eq_zero _).mp hc
  obtain ⟨q, hq⟩ := hm
  have hz : truncLT c = 0 := by
    rcases h with hd | hn
    · rw [hd, DiffOp.mul_zero'] at hq
      exact hq
    · by_cases hn0 : n = 0
      · subst n
        have hc0 : c = 0 := funext fun i => Fin.elim0 i
        rw [hc0, truncLT_zero]
      · by_contra ht
        have hq0 : q ≠ 0 := fun h => ht (by rw [hq, h, DiffOp.zero_mul'])
        have hd0 : d ≠ 0 := fun h => ht (by rw [hq, h, DiffOp.mul_zero'])
        have he : DiffOp.degree (truncLT c) = DiffOp.degree q + DiffOp.degree d := by
          rw [hq, DiffOp.degree_mul hq0 hd0]
        have hl := degree_truncLT_lt c (Nat.pos_of_ne_zero hn0)
        omega
  exact truncLT_injective (hz.trans truncLT_zero.symm)

private theorem oreTruncatedQuotient_surjective {d : DiffOp K} (hd : d ≠ 0)
    (n : ℕ) (hn : DiffOp.degree d ≤ n) :
    Function.Surjective (oreTruncatedQuotient d n) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H p =>
    obtain ⟨q, r, hqr, hr⟩ := exists_right_div hd p
    have ht : truncLT (fun i : Fin n => DiffOp.coeff r (i : ℕ)) = r := by
      rcases hr with hz | hl
      · rw [hz]
        have hf : (fun i : Fin n => DiffOp.coeff (0 : DiffOp K) (i : ℕ)) = 0 := by
          funext i
          exact DiffOp.coeff_zero _
        rw [hf, truncLT_zero]
      · exact truncLT_coeff r (lt_of_lt_of_le hl hn)
    refine ⟨fun i : Fin n => DiffOp.coeff r (i : ℕ), ?_⟩
    change (leftMultiples d).mkQ (truncLT _) = _
    rw [ht]
    refine (Submodule.Quotient.eq _).mpr ⟨-q, ?_⟩
    rw [hqr, neg_mul]
    abel

/-- The complete filtered Hilbert function, including the free quotient at `d = 0`. -/
theorem oreTruncatedQuotient_finrank_range (d : DiffOp K) (n : ℕ) :
    Module.finrank K (oreTruncatedQuotient d n).range =
      if d = 0 then n else min n (DiffOp.degree d) := by
  classical
  by_cases hd : d = 0
  · rw [if_pos hd, LinearMap.finrank_range_of_inj
      (oreTruncatedQuotient_injective d n (Or.inl hd))]
    simp
  · rw [if_neg hd]
    by_cases hn : n ≤ DiffOp.degree d
    · rw [min_eq_left hn, LinearMap.finrank_range_of_inj
        (oreTruncatedQuotient_injective d n (Or.inr hn))]
      simp
    · have hn' : DiffOp.degree d ≤ n := by omega
      rw [min_eq_right hn', LinearMap.range_eq_top.mpr
        (oreTruncatedQuotient_surjective hd n hn'), finrank_top,
        finrank_quotient_leftMultiples hd]

/-- The number of relations among the first `n` operator coefficients. -/
theorem oreTruncatedQuotient_finrank_ker (d : DiffOp K) (n : ℕ) :
    Module.finrank K (oreTruncatedQuotient d n).ker =
      if d = 0 then 0 else n - DiffOp.degree d := by
  classical
  have h := LinearMap.finrank_range_add_finrank_ker (oreTruncatedQuotient d n)
  rw [oreTruncatedQuotient_finrank_range] at h
  simp only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
  split_ifs at h ⊢ <;> omega

/-- Each unresolved coefficient relation contributes one full copy of the observation space. -/
theorem oreTruncatedQuotient_observation_defect [FiniteDimensional K W]
    (d : DiffOp K) (n : ℕ) :
    Module.finrank K (((Fin n → K) →ₗ[K] W) ⧸
      (precompose (W := W) (oreTruncatedQuotient d n)).range) =
      if d = 0 then 0 else Module.finrank K W * (n - DiffOp.degree d) := by
  classical
  rw [finrank_compositionCokernel, oreTruncatedQuotient_finrank_ker]
  split_ifs <;> simp

end GaloisForLFunctions.RepresentationLifting.Filtered

#print axioms GaloisForLFunctions.RepresentationLifting.Filtered.oreTruncatedQuotient_finrank_range
#print axioms GaloisForLFunctions.RepresentationLifting.Filtered.oreTruncatedQuotient_finrank_ker
#print axioms GaloisForLFunctions.RepresentationLifting.Filtered.oreTruncatedQuotient_observation_defect
