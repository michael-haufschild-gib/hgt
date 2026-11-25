import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.FiniteType

/-! A finite polynomial family is defined over a common Noetherian coefficient ring. -/

namespace GlobalTheory.SmoothDescent

/-- Adjoining the coefficients of finitely many polynomials to the integers
gives a Noetherian subalgebra over which every polynomial in the family lifts. -/
theorem exists_noetherian_polynomial_model {R σ I : Type*} [CommRing R] [Finite I]
    (p : I → MvPolynomial σ R) :
    ∃ (S : Subalgebra ℤ R) (_ : IsNoetherianRing S) (p₀ : I → MvPolynomial σ S),
      ∀ i, MvPolynomial.map S.val.toRingHom (p₀ i) = p i := by
  classical
  let T : Set R := ⋃ i, ((p i).coeffs : Set R)
  have hT : T.Finite := Set.finite_iUnion fun i => Finset.finite_toSet (p i).coeffs
  let S := Algebra.adjoin ℤ T
  have hfg : S.FG := ⟨hT.toFinset, congrArg (Algebra.adjoin ℤ) hT.coe_toFinset⟩
  haveI : Algebra.FiniteType ℤ S := (Subalgebra.fg_iff_finiteType S).1 hfg
  have h (i : I) : p i ∈ Set.range (MvPolynomial.map S.val.toRingHom) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro r hr
    exact ⟨⟨r, Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, hr⟩)⟩, rfl⟩
  choose p₀ hp using h
  exact ⟨S, Algebra.FiniteType.isNoetherianRing ℤ S, p₀, hp⟩

end GlobalTheory.SmoothDescent
