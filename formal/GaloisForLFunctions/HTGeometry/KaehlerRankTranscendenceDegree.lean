/-
# The cotangent rank of a field extension is its transcendence degree

mathlib carries the polynomial cotangent basis, the localization base change and formal étaleness of
a separable field extension, but not the consequence: in characteristic zero

```text
rank_kaehlerDifferential_eq_trdeg    ** dim_K Ω[K/k] = trdeg k K **
```

A transcendence basis splits the extension in two.  Over the purely transcendental part the
differentials are free on the basis — the rational function field is a localization of a polynomial
ring, and localization is formally étale.  The remaining part is algebraic, hence separable in
characteristic zero, hence formally étale, so it only extends scalars.

The degree-one case is the geometric input a defect-slope normal form consumes: a
transcendence-degree-one extension has a one-dimensional cotangent space, so every nonzero
differential is a basis and every other differential is a unique multiple of it.

Main results:
* `kaehlerBasisTransport` — a Kähler basis moves along an algebra isomorphism.
* `fractionRingMvPolynomialKaehlerBasis` — the differentials of a rational function field.
* `rank_kaehlerDifferential_eq_trdeg` — **the rank is the transcendence degree**.
* `exists_unique_smul_of_trdeg_eq_one` — **a unique slope in the degree-one case**.

The degree-one *finrank* statement itself is already corpus-owned as
`RHTower.finrank_kaehlerDifferential_eq_one_of_trdeg_eq_one`; what is new here is the general rank
identity at every transcendence degree, and the spanning consequence.
-/
import GaloisForLFunctions.HTGeometry.SeparableKaehlerBaseChange

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Transport

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The `S`-algebra structure on `T` carried by an isomorphism. -/
@[reducible] noncomputable def kaehlerAlgebraOfAlgEquiv (e : S ≃ₐ[R] T) : Algebra S T :=
  (e : S →+* T).toAlgebra

/-- The Kähler differentials of isomorphic algebras have bases of the same index type. -/
noncomputable def kaehlerBasisTransport (e : S ≃ₐ[R] T) {ι : Type*}
    (b : Module.Basis ι S (Ω[S⁄R])) : Module.Basis ι T (Ω[T⁄R]) := by
  letI : Algebra S T := kaehlerAlgebraOfAlgEquiv e
  haveI : IsScalarTower R S T := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    show algebraMap R T r = e (algebraMap R S r)
    rw [AlgEquiv.commutes]
  letI eS : S ≃ₐ[S] T := { e with commutes' := fun _ => rfl }
  haveI : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_equiv eS
  have hbc : IsBaseChange T (KaehlerDifferential.map R R S T) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale R S T
  exact (b.baseChange T).map hbc.equiv

end Transport

/-- The Kähler differentials of a rational function field are free on the variables. -/
noncomputable def fractionRingMvPolynomialKaehlerBasis (k : Type*) [Field k] (σ : Type*) :
    Module.Basis σ (FractionRing (MvPolynomial σ k)) Ω[FractionRing (MvPolynomial σ k)⁄k] := by
  have hbc : IsBaseChange (FractionRing (MvPolynomial σ k))
      (KaehlerDifferential.map k k (MvPolynomial σ k) (FractionRing (MvPolynomial σ k))) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (MvPolynomial σ k)) _ _).mp
      inferInstance
  exact ((KaehlerDifferential.mvPolynomialBasis k σ).baseChange
    (FractionRing (MvPolynomial σ k))).map hbc.equiv

universe u

/-- **The rank of the module of Kähler differentials is the transcendence degree.**  In
characteristic zero a transcendence basis splits the extension into a purely transcendental part,
whose differentials are free on the basis, and an algebraic part, which is separable and therefore
only extends scalars. -/
theorem rank_kaehlerDifferential_eq_trdeg (k K : Type u) [Field k] [Field K] [Algebra k K]
    [CharZero k] :
    Module.rank K (Ω[K⁄k]) = Algebra.trdeg k K := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : CharZero ↥(IntermediateField.adjoin k (Set.range (Subtype.val : s → K))) :=
    charZero_of_injective_algebraMap
      (algebraMap k ↥(IntermediateField.adjoin k (Set.range (Subtype.val : s → K)))).injective
  haveI : Algebra.IsAlgebraic
      ↥(IntermediateField.adjoin k (Set.range (Subtype.val : s → K))) K := hs.isAlgebraic_field
  have bF : Module.Basis ↥s
      ↥(IntermediateField.adjoin k (Set.range (Subtype.val : s → K)))
      Ω[↥(IntermediateField.adjoin k (Set.range (Subtype.val : s → K)))⁄k] :=
    kaehlerBasisTransport hs.1.aevalEquivField (fractionRingMvPolynomialKaehlerBasis k ↥s)
  have bK : Module.Basis ↥s K Ω[K⁄k] :=
    (bF.baseChange K).map
      (kaehlerBaseChangeOfIsAlgebraic k
        ↥(IntermediateField.adjoin k (Set.range (Subtype.val : s → K))) K)
  rw [← bK.mk_eq_rank'']
  have hcard := hs.lift_cardinalMk_eq_trdeg
  simpa using hcard

/-- **A transcendence-degree-one extension has a one-dimensional cotangent space.**  This is the
geometric input a defect-slope normal form consumes: any nonzero differential is a basis. -/
theorem rank_kaehlerDifferential_eq_one_of_trdeg_eq_one (k K : Type u) [Field k] [Field K]
    [Algebra k K] [CharZero k] (h : Algebra.trdeg k K = 1) :
    Module.rank K (Ω[K⁄k]) = 1 := by
  rw [rank_kaehlerDifferential_eq_trdeg, h]

/-- **Every nonzero differential of a transcendence-degree-one extension spans.** -/
theorem exists_unique_smul_of_trdeg_eq_one (k K : Type u) [Field k] [Field K]
    [Algebra k K] [CharZero k] (h : Algebra.trdeg k K = 1)
    {e : Ω[K⁄k]} (he : e ≠ 0) (f : Ω[K⁄k]) :
    ∃! c : K, f = c • e := by
  classical
  have hrank := rank_kaehlerDifferential_eq_one_of_trdeg_eq_one k K h
  haveI : Module.Finite K (Ω[K⁄k]) := by
    refine Module.finite_of_rank_eq_one hrank
  have hspan : Submodule.span K ({e} : Set (Ω[K⁄k])) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have hone : Module.finrank K (Ω[K⁄k]) = 1 := by
      rw [Module.finrank, hrank]
      simp
    rw [hone, finrank_span_singleton he]
  obtain ⟨c, hc⟩ : ∃ c : K, f = c • e := by
    have hf : f ∈ Submodule.span K ({e} : Set (Ω[K⁄k])) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [Submodule.mem_span_singleton] at hf
    obtain ⟨c, hc⟩ := hf
    exact ⟨c, hc.symm⟩
  refine ⟨c, hc, fun d hd => ?_⟩
  have hsub : (d - c) • e = 0 := by
    rw [sub_smul, ← hd, ← hc, sub_self]
  rcases smul_eq_zero.mp hsub with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 he

end

end GaloisForLFunctions.HTGeometry
