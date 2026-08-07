import GaloisForLFunctions.HTGeometry.CriticalNormalClosureArcFieldFibre

/-!
# Integral lift of geometric sheets at the normal-closure arc place

Every actual geometric sheet is integral at the chosen extension of the common-scale place.  The
low coefficient blocks therefore descend from the normal-closure critical fibre to the critical
fibre over the chosen discrete valuation ring.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

private abbrev ArcValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcValuationRing K m n hm hn

theorem criticalGeometricSheetToArcFieldFibre_coefficients_mem
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalGeometricSheet K m n) :
    (∀ i : Fin m,
      (criticalGeometricSheetToArcFieldFibre K hm hn σ).1.1.coeff i ∈
        ArcValuationRing K m n hm hn) ∧
    ∀ j : Fin n,
      (criticalGeometricSheetToArcFieldFibre K hm hn σ).1.2.coeff j ∈
        ArcValuationRing K m n hm hn := by
  exact valuationSubring_criticalFibre_coefficients_mem
    (ArcValuationRing K m n hm hn) hm hn
    (criticalNormalClosureArcRawTail K hm hn)
    (criticalNormalClosureArcReciprocalTail K hm hn)
    (criticalNormalClosureArcRawTail_map_residue K hm hn)
    (criticalNormalClosureArcReciprocalTail_map_residue K hm hn)
    (criticalGeometricSheetToArcFieldFibre K hm hn σ)

/-- Lift a polynomial of degree below `d` whose coefficients lie in a valuation subring. -/
noncomputable def valuationSubringLowLift
    {L : Type*} [Field L] (O : ValuationSubring L)
    {d : ℕ} (A : L[X]) (hA : ∀ i : Fin d, A.coeff i ∈ O) : O[X] :=
  lowPolynomial fun i => ⟨A.coeff i, hA i⟩

theorem valuationSubringLowLift_map
    {L : Type*} [Field L] (O : ValuationSubring L)
    {d : ℕ} {A : L[X]} (hAdeg : A.degree < (d : ℕ))
    (hA : ∀ i : Fin d, A.coeff i ∈ O) :
    (valuationSubringLowLift O A hA).map O.subtype = A := by
  apply Polynomial.ext
  intro k
  by_cases hk : k < d
  · rw [Polynomial.coeff_map, valuationSubringLowLift, lowPolynomial_coeff, dif_pos hk]
    rfl
  · rw [Polynomial.coeff_map, valuationSubringLowLift, lowPolynomial_coeff, dif_neg hk,
      map_zero]
    exact ((Polynomial.degree_lt_iff_coeff_zero A d).mp hAdeg k
      (Nat.le_of_not_gt hk)).symm

/-- Every actual geometric sheet has an integral representative in the critical fibre of the
chosen arc DVR. -/
noncomputable def criticalGeometricSheetToArcFibre
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalGeometricSheet K m n →
      criticalFibre (ArcValuationRing K m n hm hn) m n
        (criticalNormalClosureArcRawTail K hm hn)
        (criticalNormalClosureArcReciprocalTail K hm hn) := by
  classical
  intro σ
  let p := criticalGeometricSheetToArcFieldFibre K hm hn σ
  let hmem := criticalGeometricSheetToArcFieldFibre_coefficients_mem K hm hn σ
  let Ahat : (ArcValuationRing K m n hm hn)[X] :=
    valuationSubringLowLift (ArcValuationRing K m n hm hn) p.1.1 hmem.1
  let Bhat : (ArcValuationRing K m n hm hn)[X] :=
    valuationSubringLowLift (ArcValuationRing K m n hm hn) p.1.2 hmem.2
  have hmapA : Ahat.map (ArcValuationRing K m n hm hn).subtype = p.1.1 :=
    valuationSubringLowLift_map (ArcValuationRing K m n hm hn) p.2.1 hmem.1
  have hmapB : Bhat.map (ArcValuationRing K m n hm hn).subtype = p.1.2 :=
    valuationSubringLowLift_map (ArcValuationRing K m n hm hn) p.2.2.1 hmem.2
  refine ⟨(Ahat, Bhat), lowPolynomial_degree_lt _, lowPolynomial_degree_lt _, ?_⟩
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  apply (ArcValuationRing K m n hm hn).subtype_injective
  have hpzero := (Polynomial.X_pow_dvd_iff.mp p.2.2.2) k hk
  have hmapDefect :
      (criticalLowProduct (criticalNormalClosureArcRawTail K hm hn)
          (criticalNormalClosureArcReciprocalTail K hm hn) Ahat Bhat - 1).map
          (ArcValuationRing K m n hm hn).subtype =
        criticalLowProduct
          ((criticalNormalClosureArcRawTail K hm hn).map
            (ArcValuationRing K m n hm hn).subtype)
          ((criticalNormalClosureArcReciprocalTail K hm hn).map
            (ArcValuationRing K m n hm hn).subtype)
          p.1.1 p.1.2 - 1 := by
    simp only [criticalLowProduct, Polynomial.map_sub, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_one, hmapA, hmapB]
  have hcoeff := congrArg (fun q : (criticalNormalClosure K m n)[X] => q.coeff k)
    hmapDefect
  rw [Polynomial.coeff_map] at hcoeff
  rw [hcoeff, hpzero, map_zero]

end

end GaloisForLFunctions.HTGeometry
