import GaloisForLFunctions.HTGeometry.ValuationCriticalFibreReduction
import GaloisForLFunctions.HTGeometry.PureFibreUnramified
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Injectivity of critical-fibre reduction over a DVR

Two critical-fibre points with the same pure residue factorisation coincide.  The proof lifts one
residue factorisation by the first point itself; this removes any need for a coefficient-field
section of the residue map.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

set_option maxHeartbeats 1000000

private theorem coeffMem_ker_of_map_eq_zero
    {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    {P : R[X]} (hP : P.map f = 0) : CoeffMem (RingHom.ker f) P := by
  intro i
  rw [RingHom.mem_ker]
  have h := congrArg (fun Q : T[X] => Q.coeff i) hP
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using h

private theorem natDegree_lt_of_degree_lt
    {R : Type*} [Semiring R] {d : ℕ} (hd : 0 < d)
    {P : R[X]} (hP : P.degree < (d : ℕ)) : P.natDegree < d := by
  by_cases hzero : P = 0
  · simpa [hzero] using hd
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).2 hP

/-- Reduction to the pure factorisation fibre is injective over a DVR whenever the pure polynomial
is separable in the residue field. -/
theorem criticalFibreResidueReduction_injective_of_dvr
    {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (US VS : S[X])
    (hUdiv : (X : S[X]) ^ m ∣ US) (hVdiv : (X : S[X]) ^ n ∣ VS)
    (hUS : US.map (IsLocalRing.residue S) =
      (X : (IsLocalRing.ResidueField S)[X]) ^ m)
    (hVS : VS.map (IsLocalRing.residue S) =
      (X : (IsLocalRing.ResidueField S)[X]) ^ n)
    (hchar : (m + n : IsLocalRing.ResidueField S) ≠ 0) :
    Function.Injective
      (criticalFibreResidueReduction (IsLocalRing.residue S) hm hn US VS hUS hVS) := by
  classical
  let ε : S →+* IsLocalRing.ResidueField S := IsLocalRing.residue S
  let red := criticalFibreResidueReduction ε hm hn US VS hUS hVS
  intro p q hpq
  change red p = red q at hpq
  have hfactorA : (p.1.1 + US).map ε = (q.1.1 + US).map ε := by
    have h := congrArg (fun z => (z.1.1 : (IsLocalRing.ResidueField S)[X])) hpq
    simpa only [red, criticalFibreResidueReduction_fst] using h
  have hfactorB : (p.1.2 + VS).map ε = (q.1.2 + VS).map ε := by
    have h := congrArg (fun z => (z.1.2 : (IsLocalRing.ResidueField S)[X])) hpq
    simpa only [red, criticalFibreResidueReduction_snd] using h
  have hresA : p.1.1.map ε = q.1.1.map ε := by
    rw [Polynomial.map_add, Polynomial.map_add] at hfactorA
    exact add_right_cancel hfactorA
  have hresB : p.1.2.map ε = q.1.2.map ε := by
    rw [Polynomial.map_add, Polynomial.map_add] at hfactorB
    exact add_right_cancel hfactorB
  let A : S[X] := X ^ m + p.1.1
  let B : S[X] := X ^ n + p.1.2
  let Γ : S[X] := US - X ^ m
  let Γ' : S[X] := VS - X ^ n
  let P' : S[X] := q.1.1 - p.1.1
  let Q' : S[X] := q.1.2 - p.1.2
  have hpAlow : p.1.1.degree < (m : ℕ) := p.2.1
  have hpBlow : p.1.2.degree < (n : ℕ) := p.2.2.1
  have hAmonic : A.Monic := by
    dsimp only [A]
    exact monic_X_pow_add hpAlow
  have hBmonic : B.Monic := by
    dsimp only [B]
    exact monic_X_pow_add hpBlow
  have hAdeg : A.natDegree = m := by
    dsimp only [A]
    calc
      (X ^ m + p.1.1).natDegree = (X ^ m : S[X]).natDegree :=
        Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow])
      _ = m := Polynomial.natDegree_X_pow m
  have hBdeg : B.natDegree = n := by
    dsimp only [B]
    calc
      (X ^ n + p.1.2).natDegree = (X ^ n : S[X]).natDegree :=
        Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow])
      _ = n := Polynomial.natDegree_X_pow n
  have hmapA : A.map ε = ((red p).1.1 : (IsLocalRing.ResidueField S)[X]) := by
    rw [criticalFibreResidueReduction_fst]
    dsimp only [A]
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_add, hUS]
    ring
  have hmapB : B.map ε = ((red p).1.2 : (IsLocalRing.ResidueField S)[X]) := by
    rw [criticalFibreResidueReduction_snd]
    dsimp only [B]
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_add, hVS]
    ring
  have hcopMap : IsCoprime (A.map ε) (B.map ε) := by
    rw [hmapA, hmapB]
    exact isCoprime_of_pureFactorisation (by simpa [Nat.cast_add] using hchar) (red p).2
  have hAmapdeg : (A.map ε).natDegree = A.natDegree := hAmonic.natDegree_map ε
  have hBmapdeg : (B.map ε).natDegree = B.natDegree := hBmonic.natDegree_map ε
  have hresultantMap :
      Polynomial.resultant (A.map ε) (B.map ε) =
        ε (Polynomial.resultant A B) := by
    simpa only [hAmapdeg, hBmapdeg] using
      (Polynomial.resultant_map_map A B A.natDegree B.natDegree ε)
  have hresResultant : ε (Polynomial.resultant A B) ≠ 0 := by
    rw [← hresultantMap]
    exact ((Polynomial.isUnit_resultant_iff_isCoprime (hAmonic.map ε)).2 hcopMap).ne_zero
  have hcop : IsCoprime A B := by
    apply (Polynomial.isUnit_resultant_iff_isCoprime hAmonic).1
    exact (IsLocalRing.residue_ne_zero_iff_isUnit (Polynomial.resultant A B)).1 hresResultant
  have hmapΓ : Γ.map ε = 0 := by
    dsimp only [Γ]
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, hUS, sub_self]
  have hmapΓ' : Γ'.map ε = 0 := by
    dsimp only [Γ']
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, hVS, sub_self]
  have hmapP' : P'.map ε = 0 := by
    dsimp only [P']
    rw [Polynomial.map_sub, hresA, sub_self]
  have hmapQ' : Q'.map ε = 0 := by
    dsimp only [Q']
    rw [Polynomial.map_sub, hresB, sub_self]
  have hΓ : CoeffMem (IsLocalRing.maximalIdeal S) Γ := by
    rw [← IsLocalRing.ker_residue]
    exact coeffMem_ker_of_map_eq_zero ε hmapΓ
  have hΓ' : CoeffMem (IsLocalRing.maximalIdeal S) Γ' := by
    rw [← IsLocalRing.ker_residue]
    exact coeffMem_ker_of_map_eq_zero ε hmapΓ'
  have hP' : CoeffMem (IsLocalRing.maximalIdeal S) P' := by
    rw [← IsLocalRing.ker_residue]
    exact coeffMem_ker_of_map_eq_zero ε hmapP'
  have hQ' : CoeffMem (IsLocalRing.maximalIdeal S) Q' := by
    rw [← IsLocalRing.ker_residue]
    exact coeffMem_ker_of_map_eq_zero ε hmapQ'
  have hpAdeg : p.1.1.natDegree < m := natDegree_lt_of_degree_lt hm p.2.1
  have hpBdeg : p.1.2.natDegree < n := natDegree_lt_of_degree_lt hn p.2.2.1
  have hqAdeg : q.1.1.natDegree < m := natDegree_lt_of_degree_lt hm q.2.1
  have hqBdeg : q.1.2.natDegree < n := natDegree_lt_of_degree_lt hn q.2.2.1
  have hP'deg : P'.natDegree < m := by
    exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hqAdeg hpAdeg)
  have hQ'deg : Q'.natDegree < n := by
    exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hqBdeg hpBdeg)
  have hfullpA : A + Γ + 0 = p.1.1 + US := by
    dsimp only [A, Γ]
    ring
  have hfullpB : B + Γ' + 0 = p.1.2 + VS := by
    dsimp only [B, Γ']
    ring
  have hfullqA : A + Γ + P' = q.1.1 + US := by
    dsimp only [A, Γ, P']
    ring
  have hfullqB : B + Γ' + Q' = q.1.2 + VS := by
    dsimp only [B, Γ', Q']
    ring
  have hpdvd : (X : S[X]) ^ (m + n) ∣
      inversionError (A + Γ + 0) (B + Γ' + 0) := by
    rw [hfullpA, hfullpB]
    exact (dvd_criticalLowProduct_sub_one_iff_mul_sub_one hUdiv hVdiv _ _).1 p.2.2.2
  have hqdvd : (X : S[X]) ^ (m + n) ∣
      inversionError (A + Γ + P') (B + Γ' + Q') := by
    rw [hfullqA, hfullqB]
    exact (dvd_criticalLowProduct_sub_one_iff_mul_sub_one hUdiv hVdiv _ _).1 q.2.2.2
  have hzeroMem : CoeffMem (IsLocalRing.maximalIdeal S) (0 : S[X]) := by
    intro i
    simp
  have huniq := deformed_factorisation_unique
    (IsLocalRing.maximalIdeal S) hm hn hAmonic hAdeg (le_of_eq hBdeg) hcop
    hΓ hΓ' hzeroMem hzeroMem hP' hQ'
    (by simpa using hm) (by simpa using hn) hP'deg hQ'deg hpdvd hqdvd
  apply Subtype.ext
  apply Prod.ext
  · exact (sub_eq_zero.mp huniq.1.symm).symm
  · exact (sub_eq_zero.mp huniq.2.symm).symm

end


end GaloisForLFunctions.HTGeometry
