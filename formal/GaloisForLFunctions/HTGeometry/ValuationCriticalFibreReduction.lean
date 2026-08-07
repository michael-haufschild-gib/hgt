import GaloisForLFunctions.HTGeometry.DeformedFibreUniqueness
import GaloisForLFunctions.HTGeometry.PureCriticalFactorizationAlgebra
import GaloisForLFunctions.HTGeometry.TruncatedCompatibilityFibre

/-!
# Residue reduction for critical fibres

This reduction requires only integral tails with pure residues.  Unlike the complete-adic lifting
structure, it does not assume a coefficient-field section of the residue map.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- A finite tail whose exponents all start at `m` is divisible by `X^m`. -/
theorem X_pow_dvd_shiftedFiniteTail
    {R : Type*} [CommRing R] (m : ℕ) {d : ℕ} (c : Fin d → R) :
    (X : R[X]) ^ m ∣ ∑ i : Fin d, C (c i) * X ^ (m + (i : ℕ)) := by
  classical
  refine Finset.dvd_sum fun i _ => ?_
  refine ⟨C (c i) * X ^ (i : ℕ), ?_⟩
  rw [pow_add]
  ring

/-- Reduction of an integral critical-fibre point to a pure monic factorisation. -/
noncomputable def criticalFibreResidueReduction
    {S k : Type*} [CommRing S] [Field k]
    {m n : ℕ} (ε : S →+* k) (hm : 0 < m) (hn : 0 < n)
    (US VS : S[X])
    (hUS : US.map ε = (X : k[X]) ^ m)
    (hVS : VS.map ε = (X : k[X]) ^ n) :
    criticalFibre S m n US VS →
      MonicFactorization (pureCriticalCyclicPolynomial (K := k) (m + n)) m n := by
  classical
  intro p
  let A : k[X] := (p.1.1 + US).map ε
  let B : k[X] := (p.1.2 + VS).map ε
  have hlowA : (p.1.1.map ε).degree < (m : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_map_le p.2.1
  have hlowB : (p.1.2.map ε).degree < (n : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_map_le p.2.2.1
  have hAeq : A = X ^ m + p.1.1.map ε := by
    dsimp only [A]
    rw [Polynomial.map_add, hUS]
    ring
  have hBeq : B = X ^ n + p.1.2.map ε := by
    dsimp only [B]
    rw [Polynomial.map_add, hVS]
    ring
  have hAmonic : A.Monic := by rw [hAeq]; exact monic_X_pow_add hlowA
  have hBmonic : B.Monic := by rw [hBeq]; exact monic_X_pow_add hlowB
  have hAdeg : A.natDegree = m := by
    rw [hAeq]
    calc
      (X ^ m + p.1.1.map ε).natDegree = (X ^ m : k[X]).natDegree :=
        Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow])
      _ = m := Polynomial.natDegree_X_pow m
  have hBdeg : B.natDegree = n := by
    rw [hBeq]
    calc
      (X ^ n + p.1.2.map ε).natDegree = (X ^ n : k[X]).natDegree :=
        Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow])
      _ = n := Polynomial.natDegree_X_pow n
  have hdvdMapped : (X : k[X]) ^ (m + n) ∣ A * B - 1 := by
    have h := Polynomial.map_dvd ε p.2.2.2
    have hcrit : (X : k[X]) ^ (m + n) ∣
        criticalLowProduct (X ^ m) (X ^ n) (p.1.1.map ε) (p.1.2.map ε) - 1 := by
      simpa only [criticalLowProduct, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_one,
        hUS, hVS] using h
    have hfull := (dvd_criticalLowProduct_sub_one_iff_mul_sub_one
      (dvd_refl ((X : k[X]) ^ m)) (dvd_refl ((X : k[X]) ^ n))
      (p.1.1.map ε) (p.1.2.map ε)).1 hcrit
    simpa only [A, B, Polynomial.map_add, hUS, hVS, add_comm] using hfull
  have hdvdDifference : (X : k[X]) ^ (m + n) ∣
      A * B - pureCriticalCyclicPolynomial (K := k) (m + n) := by
    rw [pureCriticalCyclicPolynomial]
    have heq : A * B - (1 + X ^ (m + n)) = (A * B - 1) - X ^ (m + n) := by ring
    rw [heq]
    exact dvd_sub hdvdMapped dvd_rfl
  have hprod : (A * B).IsMonicOfDegree (m + n) :=
    (show A.IsMonicOfDegree m from ⟨hAdeg, hAmonic⟩).mul
      (show B.IsMonicOfDegree n from ⟨hBdeg, hBmonic⟩)
  have htarget : (pureCriticalCyclicPolynomial (K := k) (m + n)).IsMonicOfDegree
      (m + n) :=
    ⟨pureCriticalCyclicPolynomial_natDegree (m + n),
      pureCriticalCyclicPolynomial_monic (by omega)⟩
  have hzero : A * B - pureCriticalCyclicPolynomial (K := k) (m + n) = 0 :=
    eq_zero_of_X_pow_dvd_of_natDegree_lt_of_commRing hdvdDifference
      (hprod.natDegree_sub_lt (by omega) htarget)
  exact ⟨(Polynomial.MonicDegreeEq.mk A hAmonic hAdeg,
      Polynomial.MonicDegreeEq.mk B hBmonic hBdeg), sub_eq_zero.mp hzero⟩

@[simp] theorem criticalFibreResidueReduction_fst
    {S k : Type*} [CommRing S] [Field k]
    {m n : ℕ} (ε : S →+* k) (hm : 0 < m) (hn : 0 < n)
    (US VS : S[X]) (hUS : US.map ε = (X : k[X]) ^ m)
    (hVS : VS.map ε = (X : k[X]) ^ n)
    (p : criticalFibre S m n US VS) :
    ((criticalFibreResidueReduction ε hm hn US VS hUS hVS p).1.1 : k[X]) =
      (p.1.1 + US).map ε := rfl

@[simp] theorem criticalFibreResidueReduction_snd
    {S k : Type*} [CommRing S] [Field k]
    {m n : ℕ} (ε : S →+* k) (hm : 0 < m) (hn : 0 < n)
    (US VS : S[X]) (hUS : US.map ε = (X : k[X]) ^ m)
    (hVS : VS.map ε = (X : k[X]) ^ n)
    (p : criticalFibre S m n US VS) :
    ((criticalFibreResidueReduction ε hm hn US VS hUS hVS p).1.2 : k[X]) =
      (p.1.2 + VS).map ε := rfl

end


end GaloisForLFunctions.HTGeometry
