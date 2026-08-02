import GaloisForLFunctions.HTGeometry.GenericPostcriticalEscape
import GaloisForLFunctions.HTGeometry.PostcriticalFiberSeparation
import GaloisForLFunctions.HTGeometry.PureFibreUnramified

/-!
# One postcritical reciprocal coefficient escapes the critical field

Over an algebraically closed field of characteristic zero the cyclic polynomial `1 + t^L` has two
distinct factorisations into a monic factor of degree `m` and a monic factor of degree `n`, with
different constant terms.  Feeding them to the deformation argument leaves the statement with no
hypotheses at all:

for the generic jet of horizon `L = m + n`, no rational function of the critical observation and the
new raw coefficient computes the first postcritical reciprocal coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

theorem monic_criticalHorizonLeftFactorFromRoots {m n : ℕ} (root : Fin (m + n) → K)
    (S : criticalHorizonOccupationStates m n) :
    (criticalHorizonLeftFactorFromRoots root S).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem monic_criticalHorizonRightFactorFromRoots {m n : ℕ} (root : Fin (m + n) → K)
    (S : criticalHorizonOccupationStates m n) :
    (criticalHorizonRightFactorFromRoots root S).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem natDegree_criticalHorizonLeftFactorFromRoots {m n : ℕ} (root : Fin (m + n) → K)
    (S : criticalHorizonOccupationStates m n) :
    (criticalHorizonLeftFactorFromRoots root S).natDegree = m := by
  classical
  rw [criticalHorizonLeftFactorFromRoots,
    Polynomial.natDegree_prod _ _ (fun i _ => Polynomial.X_sub_C_ne_zero (root i))]
  simp [S.2]

theorem natDegree_criticalHorizonRightFactorFromRoots {m n : ℕ} (root : Fin (m + n) → K)
    (S : criticalHorizonOccupationStates m n) :
    (criticalHorizonRightFactorFromRoots root S).natDegree = n := by
  classical
  rw [criticalHorizonRightFactorFromRoots,
    Polynomial.natDegree_prod _ _ (fun i _ => Polynomial.X_sub_C_ne_zero (root i))]
  have hcard : (S.1ᶜ).card = n := by
    rw [Finset.card_compl, S.2, Fintype.card_fin]
    omega
  simp [hcard]

/-- **Two factorisations of the cyclic polynomial with distinct constant terms.** -/
theorem exists_two_pureFactorisations (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∃ A₀ B₀ A₁ B₁ : K[X],
      A₀.Monic ∧ A₀.natDegree = m ∧ B₀.Monic ∧ B₀.natDegree = n ∧
      A₁.Monic ∧ A₁.natDegree = m ∧ B₁.Monic ∧ B₁.natDegree = n ∧
      IsCoprime A₀ B₀ ∧ IsCoprime A₁ B₁ ∧
      A₀ * B₀ = 1 + X ^ (m + n) ∧ A₁ * B₁ = 1 + X ^ (m + n) ∧
      A₀.coeff 0 ≠ A₁.coeff 0 := by
  obtain ⟨S, T, hS, hT, hne⟩ := exists_pureCriticalRootFactorPairs_coeff_zero_ne (K := K) hm hn
  set root := pureCriticalRootLabeling (K := K) (by omega : 0 < m + n) with hroot
  have hL : ((m + n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨criticalHorizonLeftFactorFromRoots root S, criticalHorizonRightFactorFromRoots root S,
    criticalHorizonLeftFactorFromRoots root T, criticalHorizonRightFactorFromRoots root T,
    monic_criticalHorizonLeftFactorFromRoots root S,
    natDegree_criticalHorizonLeftFactorFromRoots root S,
    monic_criticalHorizonRightFactorFromRoots root S,
    natDegree_criticalHorizonRightFactorFromRoots root S,
    monic_criticalHorizonLeftFactorFromRoots root T,
    natDegree_criticalHorizonLeftFactorFromRoots root T,
    monic_criticalHorizonRightFactorFromRoots root T,
    natDegree_criticalHorizonRightFactorFromRoots root T,
    isCoprime_of_pureFactorisation hL hS, isCoprime_of_pureFactorisation hL hT, hS, hT, hne⟩

/-- **One postcritical reciprocal coefficient escapes the critical field.**  For the generic jet of
horizon `L = m + n` over an algebraically closed field of characteristic zero, no rational function
of the critical observation and the new raw coefficient computes the first postcritical reciprocal
coefficient. -/
theorem postcritical_escapes_criticalField (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (P Q : MvPolynomial (Fin (n + 1) ⊕ Fin m) K) (hQ : Q ≠ 0) :
    genericRecip K (m + n) (m + n) * MvPolynomial.aeval (genericObservation K m n) Q
      ≠ MvPolynomial.aeval (genericObservation K m n) P := by
  obtain ⟨A₀, B₀, A₁, B₁, hA₀, hA₀deg, hB₀, hB₀deg, hA₁, hA₁deg, hB₁, hB₁deg,
      hcop₀, hcop₁, hfac₀, hfac₁, hsep⟩ := exists_two_pureFactorisations K hm hn
  exact genericPostcritical_not_rational hm hn hA₀ hA₀deg hB₀ hB₀deg hA₁ hA₁deg hB₁ hB₁deg
    hcop₀ hcop₁ hfac₀ hfac₁ hsep P Q hQ

end GaloisForLFunctions.HTGeometry
