import GaloisForLFunctions.HTGeometry.AdicCriticalFibreExact
import GaloisForLFunctions.HTGeometry.CriticalFibreUpperBound
import GaloisForLFunctions.HTGeometry.PureCriticalFactorizationCount
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Upper bound for critical fibres over Hausdorff adic deformations

Completeness is needed to construct every deformed critical state, but not to exclude extra states.
The reduction map is injective over any Hausdorff adic deformation.  This file bounds its target
over an arbitrary characteristic-zero residue field by embedding every pure factorisation into an
algebraic closure, where the exact binomial count is already known.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- Scalar extension of a monic factorisation. -/
noncomputable def monicFactorizationMap
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    {P : K[X]} {m n : ℕ} :
    MonicFactorization P m n → MonicFactorization (P.map f) m n := fun q =>
  ⟨(q.1.1.map f, q.1.2.map f), by
    simpa only [MonicDegreeEq.map_coe, Polynomial.map_mul] using
      congrArg (Polynomial.map f) q.2⟩

/-- Scalar extension of monic factorisations is injective along an injective coefficient map. -/
theorem monicFactorizationMap_injective
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (hf : Function.Injective f) {P : K[X]} {m n : ℕ} :
    Function.Injective (monicFactorizationMap f :
      MonicFactorization P m n → MonicFactorization (P.map f) m n) := by
  intro q r hqr
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Polynomial.map_injective f hf
    exact congrArg (fun z => z.1.1.1) hqr
  · apply Subtype.ext
    apply Polynomial.map_injective f hf
    exact congrArg (fun z => z.1.2.1) hqr

/-- Scalar extension specialised to the pure critical polynomial. -/
noncomputable def pureCriticalMonicFactorizationMap
    {K L : Type*} [Field K] [Field L] (f : K →+* L) (m n : ℕ) :
    MonicFactorization (pureCriticalCyclicPolynomial (K := K) (m + n)) m n →
      MonicFactorization (pureCriticalCyclicPolynomial (K := L) (m + n)) m n := fun q =>
  ⟨(q.1.1.map f, q.1.2.map f), by
    have h := congrArg (Polynomial.map f) q.2
    simpa only [MonicDegreeEq.map_coe, Polynomial.map_mul,
      pureCriticalCyclicPolynomial, Polynomial.map_add, Polynomial.map_one,
      Polynomial.map_pow, Polynomial.map_X] using h⟩

theorem pureCriticalMonicFactorizationMap_injective
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (hf : Function.Injective f) (m n : ℕ) :
    Function.Injective (pureCriticalMonicFactorizationMap f m n) := by
  intro q r hqr
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Polynomial.map_injective f hf
    have h := congrArg (fun z => z.1.1.1) hqr
    exact h
  · apply Subtype.ext
    apply Polynomial.map_injective f hf
    have h := congrArg (fun z => z.1.2.1) hqr
    exact h

/-- The pure critical factorisation type is finite over every characteristic-zero field. -/
theorem finite_pureCriticalMonicFactorization
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hL : 0 < m + n) :
    Finite (MonicFactorization
      (pureCriticalCyclicPolynomial (K := K) (m + n)) m n) := by
  let A := AlgebraicClosure K
  letI : Finite {P : A[X] // P.Monic ∧
      P ∣ pureCriticalCyclicPolynomial (K := A) (m + n) ∧ P.natDegree = m} :=
    finite_monic_divisors (pureCriticalCyclicPolynomial_monic hL).ne_zero m
  letI : Finite (MonicFactorization
      (pureCriticalCyclicPolynomial (K := A) (m + n)) m n) :=
    Finite.of_injective
      (monicFactorizationEquivMonicDivisor
        (pureCriticalCyclicPolynomial_monic hL)
        (pureCriticalCyclicPolynomial_natDegree (m + n)))
      (monicFactorizationEquivMonicDivisor
        (pureCriticalCyclicPolynomial_monic hL)
        (pureCriticalCyclicPolynomial_natDegree (m + n))).injective
  exact Finite.of_injective
    (pureCriticalMonicFactorizationMap
      (algebraMap K (AlgebraicClosure K)) m n)
    (pureCriticalMonicFactorizationMap_injective _
      (algebraMap K (AlgebraicClosure K)).injective m n)

/-- Pure critical factorisations over any characteristic-zero field are bounded by the occupation
count.  Algebraic closure can add factorisations but cannot identify two existing ones. -/
theorem natCard_pureCriticalMonicFactorization_le
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hL : 0 < m + n) :
    Nat.card (MonicFactorization
      (pureCriticalCyclicPolynomial (K := K) (m + n)) m n) ≤
      criticalHorizonMultiplicity m n := by
  let mapFactorization := pureCriticalMonicFactorizationMap
    (algebraMap K (AlgebraicClosure K)) m n
  letI : Finite (MonicFactorization
      (pureCriticalCyclicPolynomial (K := AlgebraicClosure K) (m + n)) m n) :=
    finite_pureCriticalMonicFactorization (AlgebraicClosure K) hL
  have hinj : Function.Injective mapFactorization :=
    pureCriticalMonicFactorizationMap_injective _
      (algebraMap K (AlgebraicClosure K)).injective m n
  calc
    Nat.card (MonicFactorization
        (pureCriticalCyclicPolynomial (K := K) (m + n)) m n) ≤
        Nat.card (MonicFactorization
          (pureCriticalCyclicPolynomial (K := AlgebraicClosure K) (m + n)) m n) :=
      Nat.card_le_card_of_injective mapFactorization hinj
    _ = criticalHorizonMultiplicity m n :=
      nat_card_pureCriticalMonicFactorization hL

/-- **No-extra-branch theorem for Hausdorff adic deformations.**  Every critical state has a
distinct pure reduction, so the critical binomial multiplicity is an unconditional ceiling. -/
theorem CriticalAdicDeformation.nat_card_le
    {K S : Type*} [Field K] [CommRing S]
    {m n : ℕ} (D : CriticalAdicDeformation K S m n)
    [Nontrivial S] [CharZero K] [IsHausdorff D.ideal S]
    (hm : 0 < m) (hn : 0 < n) :
    Nat.card (criticalFibre S m n D.rawTail D.reciprocalTail) ≤
      criticalHorizonMultiplicity m n := by
  letI : Finite (MonicFactorization
      (pureCriticalCyclicPolynomial (K := K) (m + n)) m n) :=
    finite_pureCriticalMonicFactorization K (by omega)
  exact le_trans
    (Nat.card_le_card_of_injective (D.reduction hm hn) (D.reduction_injective hm hn))
    (natCard_pureCriticalMonicFactorization_le K (by omega))

end

end GaloisForLFunctions.HTGeometry
