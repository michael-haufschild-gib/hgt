import GaloisForLFunctions.HTGeometry.DeformedFibreUniqueness
import GaloisForLFunctions.HTGeometry.PureCriticalFactorizationAlgebra
import GaloisForLFunctions.HTGeometry.PureFibreUnramified
import GaloisForLFunctions.HTGeometry.TruncatedCompatibilityFibre

/-!
# Exact critical fibres over a complete adic deformation

This module isolates the local theorem behind the universal power-series computation.  A pair of
critical tails reducing to `X^m` and `X^n`, with all deformation coefficients in a complete
Hausdorff ideal, has exactly one lift of every pure factorisation of `1 + X^(m+n)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable (K S : Type*) [Field K] [CommRing S]

/-- Data of a critical adic deformation with residue field `K`. -/
structure CriticalAdicDeformation (m n : ℕ) where
  ideal : Ideal S
  residue : S →+* K
  constants : K →+* S
  residue_constants : residue.comp constants = RingHom.id K
  raw : S[X]
  reciprocal : S[X]
  ideal_eq_ker : ideal = RingHom.ker residue
  coeffMem_raw : CoeffMem ideal raw
  coeffMem_reciprocal : CoeffMem ideal reciprocal
  X_pow_dvd_raw : (X : S[X]) ^ m ∣ raw
  X_pow_dvd_reciprocal : (X : S[X]) ^ n ∣ reciprocal

namespace CriticalAdicDeformation

variable {K S} {m n : ℕ} (D : CriticalAdicDeformation K S m n)

noncomputable def rawTail : S[X] := X ^ m + D.raw

noncomputable def reciprocalTail : S[X] := X ^ n + D.reciprocal

theorem X_pow_dvd_rawTail : (X : S[X]) ^ m ∣ D.rawTail :=
  dvd_add dvd_rfl D.X_pow_dvd_raw

theorem X_pow_dvd_reciprocalTail : (X : S[X]) ^ n ∣ D.reciprocalTail :=
  dvd_add dvd_rfl D.X_pow_dvd_reciprocal

private theorem polynomial_map_eq_zero_of_coeffMem_ker
    {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T) {p : R[X]}
    (hp : CoeffMem (RingHom.ker f) p) : p.map f = 0 := by
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  exact (RingHom.mem_ker).1 (hp i)

theorem map_raw : D.raw.map D.residue = 0 := by
  apply polynomial_map_eq_zero_of_coeffMem_ker
  rw [← D.ideal_eq_ker]
  exact D.coeffMem_raw

theorem map_reciprocal : D.reciprocal.map D.residue = 0 := by
  apply polynomial_map_eq_zero_of_coeffMem_ker
  rw [← D.ideal_eq_ker]
  exact D.coeffMem_reciprocal

@[simp] theorem map_rawTail : D.rawTail.map D.residue = X ^ m := by
  rw [rawTail, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, D.map_raw, add_zero]

@[simp] theorem map_reciprocalTail : D.reciprocalTail.map D.residue = X ^ n := by
  rw [reciprocalTail, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    D.map_reciprocal, add_zero]

noncomputable def constantLift (p : S[X]) : S[X] :=
  (p.map D.residue).map D.constants

noncomputable def remainder (p : S[X]) : S[X] := p - D.constantLift p

@[simp] theorem map_constantLift (p : S[X]) : (D.constantLift p).map D.residue = p.map D.residue := by
  rw [constantLift, Polynomial.map_map, D.residue_constants]
  simp

theorem coeffMem_remainder (p : S[X]) : CoeffMem D.ideal (D.remainder p) := by
  rw [D.ideal_eq_ker]
  intro i
  rw [RingHom.mem_ker]
  rw [remainder, Polynomial.coeff_sub]
  have h := congrArg (fun q : K[X] => q.coeff i) (D.map_constantLift p)
  rw [Polynomial.coeff_map, Polynomial.coeff_map] at h
  rw [map_sub, h, sub_self]

theorem natDegree_remainder_lt {r : ℕ} (hr : 0 < r) {p : S[X]}
    (hp : p.degree < (r : ℕ)) : (D.remainder p).natDegree < r := by
  have hmap : (p.map D.residue).degree < (r : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_map_le hp
  have hlift : (D.constantLift p).degree < (r : ℕ) := by
    exact lt_of_le_of_lt Polynomial.degree_map_le hmap
  by_cases hzero : D.remainder p = 0
  · rw [hzero, Polynomial.natDegree_zero]
    exact hr
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).2
      (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hp hlift))

private theorem criticalFibre_dvd_inversionError
    (p : criticalFibre S m n D.rawTail D.reciprocalTail) :
    (X : S[X]) ^ (m + n) ∣
      inversionError (p.1.1 + D.rawTail) (p.1.2 + D.reciprocalTail) :=
  (dvd_criticalLowProduct_sub_one_iff_mul_sub_one D.X_pow_dvd_rawTail
    D.X_pow_dvd_reciprocalTail p.1.1 p.1.2).1 p.2.2.2

/-- Reduction of an adic critical-fibre point to the pure monic factorisation fibre. -/
noncomputable def reduction (hm : 0 < m) (hn : 0 < n) :
    criticalFibre S m n D.rawTail D.reciprocalTail →
      MonicFactorization (pureCriticalCyclicPolynomial (K := K) (m + n)) m n := by
  classical
  intro p
  let A : K[X] := (p.1.1 + D.rawTail).map D.residue
  let B : K[X] := (p.1.2 + D.reciprocalTail).map D.residue
  have hlowA : (p.1.1.map D.residue).degree < (m : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_map_le p.2.1
  have hlowB : (p.1.2.map D.residue).degree < (n : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_map_le p.2.2.1
  have hAeq : A = X ^ m + p.1.1.map D.residue := by
    dsimp only [A]
    rw [Polynomial.map_add, D.map_rawTail]
    ring
  have hBeq : B = X ^ n + p.1.2.map D.residue := by
    dsimp only [B]
    rw [Polynomial.map_add, D.map_reciprocalTail]
    ring
  have hAmonic : A.Monic := by rw [hAeq]; exact monic_X_pow_add hlowA
  have hBmonic : B.Monic := by rw [hBeq]; exact monic_X_pow_add hlowB
  have hAdeg : A.natDegree = m := by
    rw [hAeq]
    calc
      (X ^ m + p.1.1.map D.residue).natDegree = (X ^ m : K[X]).natDegree :=
        Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow])
      _ = m := Polynomial.natDegree_X_pow m
  have hBdeg : B.natDegree = n := by
    rw [hBeq]
    calc
      (X ^ n + p.1.2.map D.residue).natDegree = (X ^ n : K[X]).natDegree :=
        Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow])
      _ = n := Polynomial.natDegree_X_pow n
  have hdvdMapped : (X : K[X]) ^ (m + n) ∣ A * B - 1 := by
    have h := Polynomial.map_dvd D.residue (D.criticalFibre_dvd_inversionError p)
    simpa only [A, B, inversionError, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one] using h
  have hdvdDifference : (X : K[X]) ^ (m + n) ∣
      A * B - pureCriticalCyclicPolynomial (K := K) (m + n) := by
    rw [pureCriticalCyclicPolynomial]
    have heq : A * B - (1 + X ^ (m + n)) = (A * B - 1) - X ^ (m + n) := by ring
    rw [heq]
    exact dvd_sub hdvdMapped dvd_rfl
  have hprod : (A * B).IsMonicOfDegree (m + n) :=
    (show A.IsMonicOfDegree m from ⟨hAdeg, hAmonic⟩).mul
      (show B.IsMonicOfDegree n from ⟨hBdeg, hBmonic⟩)
  have htarget : (pureCriticalCyclicPolynomial (K := K) (m + n)).IsMonicOfDegree
      (m + n) :=
    ⟨pureCriticalCyclicPolynomial_natDegree (m + n),
      pureCriticalCyclicPolynomial_monic (by omega)⟩
  have hzero : A * B - pureCriticalCyclicPolynomial (K := K) (m + n) = 0 :=
    eq_zero_of_X_pow_dvd_of_natDegree_lt_of_commRing hdvdDifference
      (hprod.natDegree_sub_lt (by omega) htarget)
  exact ⟨(Polynomial.MonicDegreeEq.mk A hAmonic hAdeg,
      Polynomial.MonicDegreeEq.mk B hBmonic hBdeg), sub_eq_zero.mp hzero⟩

@[simp] theorem reduction_fst (hm : 0 < m) (hn : 0 < n)
    (p : criticalFibre S m n D.rawTail D.reciprocalTail) :
    ((D.reduction hm hn p).1.1 : K[X]) = (p.1.1 + D.rawTail).map D.residue := by
  rfl

@[simp] theorem reduction_snd (hm : 0 < m) (hn : 0 < n)
    (p : criticalFibre S m n D.rawTail D.reciprocalTail) :
    ((D.reduction hm hn p).1.2 : K[X]) = (p.1.2 + D.reciprocalTail).map D.residue := by
  rfl

theorem reduction_injective [Nontrivial S] [CharZero K] [IsHausdorff D.ideal S]
    (hm : 0 < m) (hn : 0 < n) : Function.Injective (D.reduction hm hn) := by
  classical
  intro p q hpq
  let A₀ : K[X] := (p.1.1 + D.rawTail).map D.residue
  let B₀ : K[X] := (p.1.2 + D.reciprocalTail).map D.residue
  let A : S[X] := A₀.map D.constants
  let B : S[X] := B₀.map D.constants
  let P : S[X] := D.remainder p.1.1
  let Q : S[X] := D.remainder p.1.2
  let P' : S[X] := D.remainder q.1.1
  let Q' : S[X] := D.remainder q.1.2
  have hA₀q : A₀ = (q.1.1 + D.rawTail).map D.residue := by
    change ((D.reduction hm hn p).1.1 : K[X]) = _
    rw [hpq]
    exact D.reduction_fst hm hn q
  have hB₀q : B₀ = (q.1.2 + D.reciprocalTail).map D.residue := by
    change ((D.reduction hm hn p).1.2 : K[X]) = _
    rw [hpq]
    exact D.reduction_snd hm hn q
  have hresA : p.1.1.map D.residue = q.1.1.map D.residue := by
    dsimp only [A₀] at hA₀q
    rw [Polynomial.map_add, Polynomial.map_add] at hA₀q
    exact add_right_cancel hA₀q
  have hresB : p.1.2.map D.residue = q.1.2.map D.residue := by
    dsimp only [B₀] at hB₀q
    rw [Polynomial.map_add, Polynomial.map_add] at hB₀q
    exact add_right_cancel hB₀q
  have hAmonic : A.Monic := by
    dsimp only [A]
    exact ((D.reduction hm hn p).1.1.monic).map D.constants
  have hAdeg : A.natDegree = m := by
    dsimp only [A]
    rw [Polynomial.natDegree_map D.constants]
    exact (D.reduction hm hn p).1.1.natDegree
  have hBdeg : B.natDegree ≤ n := by
    dsimp only [B]
    rw [Polynomial.natDegree_map D.constants]
    exact le_of_eq (D.reduction hm hn p).1.2.natDegree
  have hcop : IsCoprime A B := by
    dsimp only [A, B]
    exact (isCoprime_of_pureFactorisation
      (Nat.cast_ne_zero.2 (by omega : m + n ≠ 0))
      (D.reduction hm hn p).2).map (Polynomial.mapRingHom D.constants)
  have hPdeg : P.natDegree < m := D.natDegree_remainder_lt hm p.2.1
  have hQdeg : Q.natDegree < n := D.natDegree_remainder_lt hn p.2.2.1
  have hP'deg : P'.natDegree < m := D.natDegree_remainder_lt hm q.2.1
  have hQ'deg : Q'.natDegree < n := D.natDegree_remainder_lt hn q.2.2.1
  have hAform : A = X ^ m + D.constantLift p.1.1 := by
    dsimp only [A, A₀]
    rw [Polynomial.map_add, D.map_rawTail, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X]
    dsimp only [constantLift]
    ring
  have hBform : B = X ^ n + D.constantLift p.1.2 := by
    dsimp only [B, B₀]
    rw [Polynomial.map_add, D.map_reciprocalTail, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X]
    dsimp only [constantLift]
    ring
  have hAformq : A = X ^ m + D.constantLift q.1.1 := by
    rw [hAform]
    simpa only [constantLift] using congrArg
      (fun r : K[X] => (X : S[X]) ^ m + r.map D.constants) hresA
  have hBformq : B = X ^ n + D.constantLift q.1.2 := by
    rw [hBform]
    simpa only [constantLift] using congrArg
      (fun r : K[X] => (X : S[X]) ^ n + r.map D.constants) hresB
  have hfullAp : A + D.raw + P = p.1.1 + D.rawTail := by
    rw [hAform]
    dsimp only [P, remainder, rawTail]
    ring
  have hfullBp : B + D.reciprocal + Q = p.1.2 + D.reciprocalTail := by
    rw [hBform]
    dsimp only [Q, remainder, reciprocalTail]
    ring
  have hfullAq : A + D.raw + P' = q.1.1 + D.rawTail := by
    rw [hAformq]
    dsimp only [P', remainder, rawTail]
    ring
  have hfullBq : B + D.reciprocal + Q' = q.1.2 + D.reciprocalTail := by
    rw [hBformq]
    dsimp only [Q', remainder, reciprocalTail]
    ring
  have huniq : P = P' ∧ Q = Q' := by
    apply deformed_factorisation_unique D.ideal hm hn hAmonic hAdeg hBdeg hcop
      D.coeffMem_raw D.coeffMem_reciprocal
      (D.coeffMem_remainder p.1.1) (D.coeffMem_remainder p.1.2)
      (D.coeffMem_remainder q.1.1) (D.coeffMem_remainder q.1.2)
      hPdeg hQdeg hP'deg hQ'deg
    · rw [hfullAp, hfullBp]
      exact D.criticalFibre_dvd_inversionError p
    · rw [hfullAq, hfullBq]
      exact D.criticalFibre_dvd_inversionError q
  have hpfirst : p.1.1 = q.1.1 := by
    have h := huniq.1
    dsimp only [P, P', remainder] at h
    have hlift : D.constantLift p.1.1 = D.constantLift q.1.1 := by
      dsimp only [constantLift]
      rw [hresA]
    rw [hlift] at h
    exact sub_left_injective h
  have hpsecond : p.1.2 = q.1.2 := by
    have h := huniq.2
    dsimp only [Q, Q', remainder] at h
    have hlift : D.constantLift p.1.2 = D.constantLift q.1.2 := by
      dsimp only [constantLift]
      rw [hresB]
    rw [hlift] at h
    exact sub_left_injective h
  apply Subtype.ext
  exact Prod.ext hpfirst hpsecond

theorem reduction_surjective [Nontrivial S] [CharZero K] [IsAdicComplete D.ideal S]
    (hm : 0 < m) (hn : 0 < n) : Function.Surjective (D.reduction hm hn) := by
  classical
  intro r
  let A₀ : K[X] := (r.1.1 : K[X])
  let B₀ : K[X] := (r.1.2 : K[X])
  let A : S[X] := A₀.map D.constants
  let B : S[X] := B₀.map D.constants
  have hAmonic : A.Monic := r.1.1.monic.map D.constants
  have hBmonic : B.Monic := r.1.2.monic.map D.constants
  have hAdeg : A.natDegree = m := by
    dsimp only [A]
    rw [Polynomial.natDegree_map D.constants]
    exact r.1.1.natDegree
  have hBdeg : B.natDegree = n := by
    dsimp only [B]
    rw [Polynomial.natDegree_map D.constants]
    exact r.1.2.natDegree
  have hcop : IsCoprime A B :=
    (isCoprime_of_pureFactorisation
      (Nat.cast_ne_zero.2 (by omega : m + n ≠ 0)) r.2).map
        (Polynomial.mapRingHom D.constants)
  have hbase : (X : S[X]) ^ (m + n) ∣ inversionError A B := by
    have heq : inversionError A B = (X : S[X]) ^ (m + n) := by
      dsimp only [A, B, A₀, B₀, inversionError]
      rw [← Polynomial.map_mul, r.2, pureCriticalCyclicPolynomial,
        Polynomial.map_add, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X,
        add_sub_cancel_left]
    rw [heq]
  obtain ⟨P, Q, hPdeg, hQdeg, hPmem, hQmem, hdvd⟩ :=
    exists_deformed_factorisation D.ideal hm hn hAmonic hAdeg (le_of_eq hBdeg) hcop
      D.coeffMem_raw D.coeffMem_reciprocal hbase
  let lowA : S[X] := A - X ^ m + P
  let lowB : S[X] := B - X ^ n + Q
  have hAminus : (A - X ^ m).natDegree < m :=
    (show A.IsMonicOfDegree m from ⟨hAdeg, hAmonic⟩).natDegree_sub_lt
      (Nat.ne_of_gt hm)
      (show (X ^ m : S[X]).IsMonicOfDegree m from
        ⟨Polynomial.natDegree_X_pow m, Polynomial.monic_X_pow m⟩)
  have hBminus : (B - X ^ n).natDegree < n :=
    (show B.IsMonicOfDegree n from ⟨hBdeg, hBmonic⟩).natDegree_sub_lt
      (Nat.ne_of_gt hn)
      (show (X ^ n : S[X]).IsMonicOfDegree n from
        ⟨Polynomial.natDegree_X_pow n, Polynomial.monic_X_pow n⟩)
  have hlowAnat : lowA.natDegree < m := by
    dsimp only [lowA]
    exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt hAminus hPdeg)
  have hlowBnat : lowB.natDegree < n := by
    dsimp only [lowB]
    exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt hBminus hQdeg)
  have hlowAdeg : lowA.degree < (m : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hlowAnat)
  have hlowBdeg : lowB.degree < (n : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hlowBnat)
  have hfullA : lowA + D.rawTail = A + D.raw + P := by
    dsimp only [lowA, rawTail]
    ring
  have hfullB : lowB + D.reciprocalTail = B + D.reciprocal + Q := by
    dsimp only [lowB, reciprocalTail]
    ring
  have hfibre : (X : S[X]) ^ (m + n) ∣
      criticalLowProduct D.rawTail D.reciprocalTail lowA lowB - 1 := by
    apply (dvd_criticalLowProduct_sub_one_iff_mul_sub_one D.X_pow_dvd_rawTail
      D.X_pow_dvd_reciprocalTail lowA lowB).2
    rw [hfullA, hfullB]
    exact hdvd
  let z : criticalFibre S m n D.rawTail D.reciprocalTail :=
    ⟨(lowA, lowB), hlowAdeg, hlowBdeg, hfibre⟩
  refine ⟨z, ?_⟩
  have hPzero : P.map D.residue = 0 := by
    apply polynomial_map_eq_zero_of_coeffMem_ker
    rw [← D.ideal_eq_ker]
    exact hPmem
  have hQzero : Q.map D.residue = 0 := by
    apply polynomial_map_eq_zero_of_coeffMem_ker
    rw [← D.ideal_eq_ker]
    exact hQmem
  have hreduceA : (lowA + D.rawTail).map D.residue = A₀ := by
    rw [hfullA]
    dsimp only [A]
    rw [Polynomial.map_add, Polynomial.map_add, hPzero, add_zero, D.map_raw, add_zero,
      Polynomial.map_map, D.residue_constants]
    simp
  have hreduceB : (lowB + D.reciprocalTail).map D.residue = B₀ := by
    rw [hfullB]
    dsimp only [B]
    rw [Polynomial.map_add, Polynomial.map_add, hQzero, add_zero, D.map_reciprocal, add_zero,
      Polynomial.map_map, D.residue_constants]
    simp
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact hreduceA
  · apply Subtype.ext
    exact hreduceB

noncomputable def equivPureFactorization [Nontrivial S] [CharZero K]
    [IsAdicComplete D.ideal S]
    (hm : 0 < m) (hn : 0 < n) :
    criticalFibre S m n D.rawTail D.reciprocalTail ≃
      MonicFactorization (pureCriticalCyclicPolynomial (K := K) (m + n)) m n :=
  Equiv.ofBijective (D.reduction hm hn)
    ⟨D.reduction_injective hm hn, D.reduction_surjective hm hn⟩

theorem nat_card [Nontrivial S] [CharZero K] [IsAlgClosed K] [IsAdicComplete D.ideal S]
    (hm : 0 < m) (hn : 0 < n) :
    Nat.card (criticalFibre S m n D.rawTail D.reciprocalTail) =
      criticalHorizonMultiplicity m n := by
  rw [Nat.card_congr (D.equivPureFactorization hm hn)]
  exact nat_card_pureCriticalMonicFactorization (by omega)

end CriticalAdicDeformation

end GaloisForLFunctions.HTGeometry
