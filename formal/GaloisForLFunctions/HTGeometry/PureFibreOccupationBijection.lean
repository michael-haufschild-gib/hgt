import GaloisForLFunctions.HTGeometry.OccupationFactorInjective

/-!
# Every pure factorisation comes from an occupation state

A monic factor of degree `m` of `1 + t^L` is the product of `X - r` over an `m`-element set of roots
of `1 + t^L`: the polynomial is separable, so its roots are distinct, and a monic divisor of a
product of distinct monic linear factors is the product over a subset of them.

With the injectivity of the passage from occupation states to factors, this identifies the pure
critical fibre with the `m`-element subsets of the roots — the fibre really has the critical binomial
multiplicity of points, not merely at most or at least that many.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Every monic divisor of the cyclic polynomial is a product over a subset of its roots.** -/
theorem exists_rootSubset_of_monic_dvd {m n : ℕ} (hL : 0 < m + n)
    {A : K[X]} (hA : A.Monic)
    (hdvd : A ∣ pureCriticalCyclicPolynomial (K := K) (m + n)) :
    ∃ S : Finset (Fin (m + n)), S.card = A.natDegree ∧
      ∏ i ∈ S, (X - C (pureCriticalRootLabeling (K := K) hL i)) = A := by
  classical
  set root := pureCriticalRootLabeling (K := K) hL with hroot
  have hinj : Function.Injective root := pureCriticalRootLabeling_injective hL
  -- the roots of the cyclic polynomial, as a finset
  set R : Finset K := Finset.univ.image root with hR
  have hRprod : ∏ a ∈ R, (X - C a) = pureCriticalCyclicPolynomial (K := K) (m + n) := by
    rw [hR, Finset.prod_image (fun i _ j _ h => hinj h)]
    exact pureCriticalRootLabeling_prod hL
  have hcycne : pureCriticalCyclicPolynomial (K := K) (m + n) ≠ 0 := by
    rw [pureCriticalCyclicPolynomial]
    exact one_add_X_pow_ne_zero hL
  have hRroots : (pureCriticalCyclicPolynomial (K := K) (m + n)).roots = R.val := by
    rw [← hRprod, Polynomial.roots_prod_X_sub_C]
  -- the factor's roots form a sub-multiset, hence a subset
  have hle : A.roots ≤ R.val := by
    rw [← hRroots]
    exact Polynomial.roots.le_of_dvd hcycne hdvd
  have hnodup : A.roots.Nodup := Multiset.nodup_of_le hle R.nodup
  have hsplit : A.Splits := IsAlgClosed.splits A
  have hAprod : A = (Multiset.map (fun r => X - C r) A.roots).prod :=
    Polynomial.Splits.eq_prod_roots_of_monic hsplit hA
  have hAfinset : A = ∏ r ∈ A.roots.toFinset, (X - C r) := by
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnodup]
    exact hAprod
  -- pull the root set back through the labelling
  set S : Finset (Fin (m + n)) := Finset.univ.filter (fun i => root i ∈ A.roots) with hS
  have himage : S.image root = A.roots.toFinset := by
    ext r
    constructor
    · intro hr
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hr
      exact Multiset.mem_toFinset.2 (Finset.mem_filter.1 hi).2
    · intro hr
      have hrR : r ∈ R := Multiset.mem_of_le hle (Multiset.mem_toFinset.1 hr)
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hrR
      exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i,
        Multiset.mem_toFinset.1 hr⟩, rfl⟩
  have hScard : S.card = A.natDegree := by
    have h1 : S.card = (S.image root).card := (Finset.card_image_of_injective S hinj).symm
    rw [h1, himage, Multiset.toFinset_card_of_nodup hnodup]
    have hcard := congrArg Polynomial.natDegree hAprod
    rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at hcard
    exact hcard.symm
  refine ⟨S, hScard, ?_⟩
  rw [hAfinset, ← himage, Finset.prod_image (fun i _ j _ h => hinj h)]

/-- **Every monic factor of the raw critical degree comes from an occupation state.** -/
theorem exists_occupationState_of_pureFactorisation {m n : ℕ} (hL : 0 < m + n)
    {A B : K[X]} (hA : A.Monic) (hAdeg : A.natDegree = m)
    (hfac : A * B = pureCriticalCyclicPolynomial (K := K) (m + n)) :
    ∃ S : criticalHorizonOccupationStates m n,
      criticalHorizonLeftFactorFromRoots (pureCriticalRootLabeling (K := K) hL) S = A := by
  obtain ⟨S, hScard, hSprod⟩ := exists_rootSubset_of_monic_dvd hL hA ⟨B, hfac.symm⟩
  exact ⟨⟨S, by rw [hScard, hAdeg]⟩, hSprod⟩

end GaloisForLFunctions.HTGeometry
