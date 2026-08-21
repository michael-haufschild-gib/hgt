import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.GaloisResolvent
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Rat.Denumerable

/-!
# Rational points off a hypersurface, and separating labels

A nonzero multivariate polynomial over a domain containing the rationals does not vanish at every
*rational* point: this is the standard induction on the number of variables, the one-variable step
being that a nonzero polynomial has finitely many roots.  Applied to the product of the linear
forms `∑_j k_j (β_{π j} - β_{ρ j})` over all pairs of distinct labellings, it produces a rational
label vector for which the labelled actions of a family of distinct elements are pairwise distinct.
-/

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open MvPolynomial

/-- A nonzero polynomial in finitely many variables over a domain containing `ℚ` has a rational
nonvanishing point. -/
theorem exists_ratPoint_fin {L : Type*} [CommRing L] [IsDomain L] (φ : ℚ →+* L) :
    ∀ (n : ℕ) (P : MvPolynomial (Fin n) L), P ≠ 0 →
      ∃ k : Fin n → ℚ, MvPolynomial.eval (fun j => φ (k j)) P ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro P hP
      refine ⟨Fin.elim0, ?_⟩
      have heq : (MvPolynomial.eval (fun j : Fin 0 => φ (Fin.elim0 j)))
          = (MvPolynomial.isEmptyAlgEquiv L (Fin 0)).toRingEquiv.toRingHom := by
        refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => i.elim0)
        simp only [MvPolynomial.eval_C, MvPolynomial.isEmptyAlgEquiv]
        exact (MvPolynomial.coeff_zero_C r).symm
      rw [heq]
      exact fun h => hP ((MvPolynomial.isEmptyAlgEquiv L (Fin 0)).toRingEquiv.injective
        (by simpa using h))
  | succ n ih =>
      intro P hP
      have hQne : MvPolynomial.finSuccEquiv L n P ≠ 0 := by
        intro h
        apply hP
        have h2 := congrArg (MvPolynomial.finSuccEquiv L n).symm h
        simpa using h2
      obtain ⟨k', hk'⟩ := ih ((MvPolynomial.finSuccEquiv L n P).coeff
        (MvPolynomial.finSuccEquiv L n P).natDegree) (Polynomial.leadingCoeff_ne_zero.mpr hQne)
      have hRne : Polynomial.map (MvPolynomial.eval (fun j => φ (k' j)))
          (MvPolynomial.finSuccEquiv L n P) ≠ 0 := by
        intro h
        apply hk'
        have h2 := congrArg
          (fun p => Polynomial.coeff p (MvPolynomial.finSuccEquiv L n P).natDegree) h
        simpa [Polynomial.coeff_map] using h2
      have hfin : {t : ℚ | Polynomial.eval (φ t)
          (Polynomial.map (MvPolynomial.eval (fun j => φ (k' j)))
            (MvPolynomial.finSuccEquiv L n P)) = 0}.Finite := by
        refine Set.Finite.of_finite_image ?_ (φ.injective.injOn)
        refine Set.Finite.subset (Polynomial.finite_setOf_isRoot hRne) ?_
        rintro x ⟨t, ht, rfl⟩
        exact ht
      obtain ⟨t, ht⟩ := ((Set.infinite_univ (α := ℚ)).sdiff hfin).nonempty
      refine ⟨(Fin.cons t k' : Fin (n + 1) → ℚ), ?_⟩
      have hfun : (fun j => φ ((Fin.cons t k' : Fin (n + 1) → ℚ) j))
          = (Fin.cons (φ t) (fun j => φ (k' j)) : Fin (n + 1) → L) := by
        funext j
        refine Fin.cases ?_ ?_ j <;> simp
      rw [hfun, MvPolynomial.eval_eq_eval_mv_eval']
      exact ht.2

/-- The same statement for an arbitrary finite index type. -/
theorem exists_ratPoint {σ : Type*} [Fintype σ] {L : Type*} [CommRing L] [IsDomain L]
    (φ : ℚ →+* L) {P : MvPolynomial σ L} (hP : P ≠ 0) :
    ∃ k : σ → ℚ, MvPolynomial.eval (fun j => φ (k j)) P ≠ 0 := by
  classical
  obtain ⟨k', hk'⟩ := exists_ratPoint_fin φ (Fintype.card σ)
    (MvPolynomial.rename (Fintype.equivFin σ) P)
    (fun h => hP (MvPolynomial.rename_injective ((Fintype.equivFin σ) : σ → Fin (Fintype.card σ))
      (Fintype.equivFin σ).injective (by simpa using h)))
  refine ⟨fun j => k' (Fintype.equivFin σ j), ?_⟩
  rw [MvPolynomial.eval_rename] at hk'
  exact hk'

/-- **A separating label vector.**  If the `β j` are pairwise distinct then some rational `k` makes
the labelled actions `∑_j k_j β_{π j}` pairwise distinct across all labellings. -/
theorem exists_separating_label {σ : Type*} [Fintype σ] [DecidableEq σ] {L : Type*} [Field L]
    (φ : ℚ →+* L) {β : σ → L} (hβ : Function.Injective β) :
    ∃ k : σ → ℚ, Function.Injective
      (fun π : Equiv.Perm σ => ∑ j, φ (k j) * β (π j)) := by
  classical
  have hfac : ∀ π ρ : Equiv.Perm σ, π ≠ ρ →
      (∑ j, MvPolynomial.C (β (π j) - β (ρ j)) * MvPolynomial.X j : MvPolynomial σ L) ≠ 0 := by
    intro π ρ hne h0
    obtain ⟨j, hj⟩ : ∃ j, π j ≠ ρ j := by
      by_contra hc
      exact hne (Equiv.ext (fun j => not_not.mp (fun h => hc ⟨j, h⟩)))
    have hcoeff : (∑ j', MvPolynomial.C (β (π j') - β (ρ j')) * MvPolynomial.X j' :
        MvPolynomial σ L).coeff (Finsupp.single j 1) = β (π j) - β (ρ j) := by
      rw [MvPolynomial.coeff_sum, Finset.sum_eq_single j]
      · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_pos rfl, mul_one]
      · intro j' _ hj'
        rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_neg, mul_zero]
        exact fun hh => hj' (Finsupp.single_left_injective one_ne_zero hh)
      · intro hmem
        exact absurd (Finset.mem_univ j) hmem
    have hz : β (π j) - β (ρ j) = 0 := by
      rw [← hcoeff, h0, MvPolynomial.coeff_zero]
    exact hj (hβ (sub_eq_zero.mp hz))
  have hBadne : (∏ pr ∈ (Finset.univ : Finset (Equiv.Perm σ)).offDiag,
      ∑ j, MvPolynomial.C (β (pr.1 j) - β (pr.2 j)) * MvPolynomial.X j : MvPolynomial σ L) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun pr hpr =>
      hfac pr.1 pr.2 (Finset.mem_offDiag.mp hpr).2.2
  obtain ⟨k, hk⟩ := exists_ratPoint φ hBadne
  refine ⟨k, fun π ρ h => ?_⟩
  by_contra hne
  apply hk
  rw [map_prod]
  refine Finset.prod_eq_zero (i := (π, ρ))
    (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hne⟩) ?_
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have hexp : ∀ j, (β (π j) - β (ρ j)) * φ (k j)
      = φ (k j) * β (π j) - φ (k j) * β (ρ j) := by
    intro j; ring
  rw [Finset.sum_congr rfl fun j _ => hexp j, Finset.sum_sub_distrib]
  simp only at h
  rw [h, sub_self]

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
