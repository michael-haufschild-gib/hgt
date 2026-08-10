import GaloisForLFunctions.HTGeometry.ProjectiveHorizonRamificationUniqueness
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonConormalPairing
import GaloisForLFunctions.HTGeometry.TruncatedCompatibilityFibre

/-!
# Rigidity of two critical fibre states with one shared tangent

This assembles the algebraic core of generic ramification-to-branch injectivity.  Two critical
fibre states with the same observed tails and the same coprime vertical tangent pair have an exact
low-degree syzygy.  The syzygy is a single cofactor multiple of that tangent.  The two inverse
identities and the marked reciprocal-tail coefficient then force the cofactor, hence both state
displacements, to vanish.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **Shared-coprime-tangent rigidity.**  Two states of one critical fibre carrying the same
coprime nonzero vertical tangent pair are equal. -/
theorem criticalFibre_eq_of_shared_coprime_tangent
    {K : Type*} [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m)
    {P Q : K[X]}
    (hPtail : (X : K[X]) ^ m ∣ P)
    (hQtail : (X : K[X]) ^ n ∣ Q)
    (hQn : Q.coeff n ≠ 0)
    (p q : criticalFibre K m n P Q)
    {U V : K[X]}
    (hUdegree : U.degree < (m : ℕ))
    (hVdegree : V.degree < (n : ℕ))
    (hU : U ≠ 0)
    (hcoprime : IsCoprime U V)
    (hpTangent : X ^ (m + n) ∣
      U * (p.1.2 + Q) + (p.1.1 + P) * V)
    (hqTangent : X ^ (m + n) ∣
      U * (q.1.2 + Q) + (q.1.1 + P) * V) :
    p = q := by
  let D : K[X] := q.1.1 - p.1.1
  let E : K[X] := q.1.2 - p.1.2
  have hDdegree : D.degree < (m : ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt q.2.1 p.2.1)
  have hEdegree : E.degree < (n : ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt q.2.2.1 p.2.2.1)
  have hsyzygyDvd : X ^ (m + n) ∣ D * V + E * U := by
    have hsub := dvd_sub hqTangent hpTangent
    convert hsub using 1
    simp only [D, E]
    ring
  have hsyzygyDegree : (D * V + E * U).degree < ((m + n : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact degree_mul_lt_of_lt_of_le hDdegree hVdegree.le
    · rw [show m + n = n + m from Nat.add_comm m n]
      exact degree_mul_lt_of_lt_of_le hEdegree hUdegree.le
  have hsyzygy : D * V + E * U = 0 :=
    eq_zero_of_dvd_of_degree_lt hsyzygyDvd hsyzygyDegree
  obtain ⟨C, hD, hE⟩ := exists_cofactor_of_syzygy hcoprime hU hsyzygy
  have hpInv : X ^ (m + n) ∣ (p.1.1 + P) * (p.1.2 + Q) - 1 :=
    (dvd_criticalLowProduct_sub_one_iff_mul_sub_one hPtail hQtail _ _).mp p.2.2.2
  have hqInv : X ^ (m + n) ∣ (q.1.1 + P) * (q.1.2 + Q) - 1 :=
    (dvd_criticalLowProduct_sub_one_iff_mul_sub_one hPtail hQtail _ _).mp q.2.2.2
  have hQcoeffP : (p.1.2 + Q).coeff n = Q.coeff n := by
    rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_degree_lt p.2.2.1, zero_add]
  have hQcoeffQ : (q.1.2 + Q).coeff n = Q.coeff n := by
    rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_degree_lt q.2.2.1, zero_add]
  have hsecond : p.1.2 + Q - C * V = q.1.2 + Q := by
    rw [show p.1.2 + Q - C * V = p.1.2 + Q + E by rw [hE]; ring]
    simp only [E]
    ring
  have hfirst : p.1.1 + P + C * U = q.1.1 + P := by
    rw [← hD]
    simp only [D]
    ring
  have hCUdegree : (C * U).natDegree < m := by
    rw [← hD]
    by_cases hDzero : D = 0
    · simp [hDzero, hm]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hDzero).mpr hDdegree
  have hCzero : C = 0 := by
    apply criticalHorizon_sharedConormal_displacement_eq_zero
      hU hCUdegree (hQcoeffP.trans_ne hQn)
      (by rw [hsecond, hQcoeffQ, hQcoeffP]) hpInv
    · rw [hfirst, hsecond]
      exact hqInv
    · exact hpTangent
  have hDzero : D = 0 := by rw [hD, hCzero, zero_mul]
  have hEzero : E = 0 := by rw [hE, hCzero, zero_mul, neg_zero]
  apply Subtype.ext
  apply Prod.ext
  · exact (sub_eq_zero.mp hDzero).symm
  · exact (sub_eq_zero.mp hEzero).symm

end GaloisForLFunctions.HTGeometry
