import GaloisForLFunctions.HTGeometry.CriticalObservationJacobianBlocks

/-!
# The reciprocal column of the observation Jacobian

`dY = -Y² dX` expresses the differential of a reciprocal coefficient as an antidiagonal convolution
of the differentials of the raw coefficients.  Reindexing that convolution through
`finSumFinEquiv` turns it into the reciprocal column of the observation Jacobian, completing the
factorization hypothesis `hvw`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial IsLocalRing KaehlerDifferential Polynomial

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

omit [IsAlgClosed K] [Fact (1 < m)] [Fact (1 < n)] in
theorem criticalRawDifferential_eq (t : Fin m ⊕ Fin n) :
    criticalRawDifferential K t
      = KaehlerDifferential.D K
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        ((criticalSourceRawPolynomialIntegral K (Fact.out : 0 < m)
          (Fact.out : 0 < n)).coeff ((finSumFinEquiv t : Fin (m + n)) : ℕ)) := by
  rw [criticalRawDifferential, criticalSourceRawPolynomialIntegral_coeff K Fact.out Fact.out
    ((finSumFinEquiv t : Fin (m + n)) : ℕ) (finSumFinEquiv t).isLt]

omit [IsAlgClosed K] [Fact (1 < m)] [Fact (1 < n)] in
theorem criticalObservationJacobian_apply_inl (t : Fin m ⊕ Fin n) (s : Fin m) :
    criticalObservationJacobian K t (Sum.inl s)
      = if ((finSumFinEquiv t : Fin (m + n)) : ℕ) ≤ n + (s : ℕ) then
          -((criticalSourceRecipPolynomialIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n) *
            criticalSourceRecipPolynomialIntegral K (Fact.out : 0 < m)
              (Fact.out : 0 < n)).coeff (n + (s : ℕ) - ((finSumFinEquiv t : Fin (m + n)) : ℕ)))
        else 0 := rfl

theorem criticalObservationJacobian_hvw_inl (s : Fin m) :
    KaehlerDifferential.D K
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (algebraMap
          (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (criticalObservationBlockCoord K (Sum.inl s)))
      = ∑ t : Fin m ⊕ Fin n,
          criticalObservationJacobian K t (Sum.inl s) • criticalRawDifferential K t := by
  classical
  set B := criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) with hB
  set g := criticalSourceRecipPolynomialIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n) with hg
  set f := criticalSourceRawPolynomialIntegral K (Fact.out : 0 < m) (Fact.out : 0 < n) with hf
  have hns : n + (s : ℕ) < m + n := by have := s.isLt; omega
  -- left-hand side
  have hL : KaehlerDifferential.D K B
      (algebraMap
        (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) B
        (criticalObservationBlockCoord K (Sum.inl s)))
      = -∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (A := ℕ) (n + (s : ℕ)) :
          Finset (ℕ × ℕ)), (g * g).coeff x.1 • KaehlerDifferential.D K B (f.coeff x.2) := by
    rw [criticalObservationBlockCoord]
    show KaehlerDifferential.D K B (algebraMap _ B
      (criticalObservationCoordSchur K (Sum.inr s))) = _
    rw [algebraMap_criticalObservationCoordSchur_inr K,
      ← criticalSourceRecipPolynomialIntegral_coeff K Fact.out Fact.out (n + (s : ℕ)) hns]
    exact D_criticalSourceRecipPolynomialIntegral_coeff K Fact.out Fact.out (n + (s : ℕ)) hns
  rw [hL]
  -- right-hand side
  have hR : ∑ t : Fin m ⊕ Fin n,
      criticalObservationJacobian K t (Sum.inl s) • criticalRawDifferential K t
      = ∑ k ∈ Finset.range (m + n),
        (if k ≤ n + (s : ℕ) then
          (-((g * g).coeff (n + (s : ℕ) - k))) • KaehlerDifferential.D K B (f.coeff k)
        else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => if k ≤ n + (s : ℕ) then
        (-((g * g).coeff (n + (s : ℕ) - k))) • KaehlerDifferential.D K B (f.coeff k) else 0)
      (m + n)]
    refine (Equiv.sum_comp finSumFinEquiv (fun k : Fin (m + n) =>
      if (k : ℕ) ≤ n + (s : ℕ) then
        (-((g * g).coeff (n + (s : ℕ) - (k : ℕ)))) •
          KaehlerDifferential.D K B (f.coeff (k : ℕ)) else 0)).symm.trans ?_ |>.symm
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [criticalObservationJacobian_apply_inl K t s, criticalRawDifferential_eq K t]
    by_cases hle : ((finSumFinEquiv t : Fin (m + n)) : ℕ) ≤ n + (s : ℕ)
    · rw [if_pos hle, if_pos hle]
    · rw [if_neg hle, if_neg hle, zero_smul]
  rw [hR]
  have hfilter : (Finset.range (m + n)).filter (fun k => k ≤ n + (s : ℕ))
      = Finset.range (n + (s : ℕ) + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hfilter]
  have hneg : ∀ k : ℕ,
      (-((g * g).coeff (n + (s : ℕ) - k))) • KaehlerDifferential.D K B (f.coeff k)
      = -((g * g).coeff (n + (s : ℕ) - k) • KaehlerDifferential.D K B (f.coeff k)) :=
    fun k => neg_smul _ _
  rw [Finset.sum_congr rfl fun k _ => hneg k, Finset.sum_neg_distrib]
  congr 1
  rw [← Finset.Nat.sum_antidiagonal_swap]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => (g * g).coeff b • KaehlerDifferential.D K B (f.coeff a)) (n + (s : ℕ))

end

end GaloisForLFunctions.HTGeometry
