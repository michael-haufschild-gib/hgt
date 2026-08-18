import Mathlib.SetTheory.Cardinal.Subfield
import GaloisForLFunctions.HTGeometry.PolynomialSubfieldDescent
import GaloisForLFunctions.HTGeometry.ComplexSplitFibresDiscriminant
import GaloisForLFunctions.HTGeometry.AlgebraicPointDescent
import GaloisForLFunctions.HTGeometry.DomainAlgHomRankOne
import GaloisForLFunctions.HTGeometry.CountableFieldComplexEmbedding

/-!
# Algebraic simple connectedness of the affine line over an arbitrary algebraically closed field

Over any algebraically closed field `K` of characteristic zero, a domain that is finite free over
`K[X]` and whose discriminant is a unit has rank one: the affine line has no nontrivial connected
finite étale cover.  Unlike `AffineLineSimplyConnected`, no monogenic model is assumed, so this is
the form an abstract étale cover can be fed to.

The complex case is `ComplexSplitFibresDiscriminant`.  The transfer has three ingredients, each in
its own module:

* `PolynomialSubfieldDescent` — the structure constants of a basis have countably many
  coefficients, so they lie in a countable subfield `F ⊆ K`; the `F[X]`-span of the basis is an
  `F[X]`-subalgebra `B₀`, free with the same basis, whose base change to `K[X]` is `B` and whose
  discriminant is still a unit;
* `CountableFieldComplexEmbedding` — `F` embeds into `ℂ`, so `ℂ[X] ⊗ B₀` is a finite free
  `ℂ[X]`-algebra with unit discriminant, hence admits a `ℂ[X]`-algebra map to `ℂ[X]`;
* `AlgebraicPointDescent` — Zariski's lemma pulls that map back from `ℂ[X]` to `K[X]`, since the
  finitely many coefficients involved generate a finitely generated `F`-subalgebra of `ℂ`.

The base change of the pulled-back map along `K[X] ⊗[F[X]] B₀ ≅ B` is a `K[X]`-algebra map
`B → K[X]`, and `DomainAlgHomRankOne` turns it into the rank-one conclusion.
-/


namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped TensorProduct

set_option maxHeartbeats 3200000

/-- A polynomial all of whose coefficients descend is itself a descended polynomial. -/
theorem mem_range_map_of_coeff_mem_range {E K : Type*} [Field E] [Field K] (φ : E →+* K)
    (p : K[X]) (h : ∀ d, p.coeff d ∈ Set.range φ) :
    p ∈ Set.range (Polynomial.map φ) := by
  have : p ∈ Polynomial.lifts φ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact h
  obtain ⟨q, hq⟩ := this
  exact ⟨q, hq⟩

/-- **A finite free étale algebra over the affine line admits a section, over any algebraically
closed field of characteristic zero.**

The proof descends the algebra to a countable subfield `F` of `K` carrying the structure constants,
embeds `F` into `ℂ`, uses the complex covering-space theorem to produce a `ℂ[X]`-algebra map out of
the base change, and pulls that map back to `K[X]` by Zariski's lemma. -/
theorem nonempty_algHom_of_isUnit_discr_algClosed {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {B : Type*} [CommRing B] [Algebra K[X] B]
    [Module.Free K[X] B] [Module.Finite K[X] B] {n : ℕ} (hn : 1 ≤ n)
    (e : Module.Basis (Fin n) K[X] B) (hd : IsUnit (Algebra.discr K[X] e)) :
    Nonempty (B →ₐ[K[X]] K[X]) := by
  classical
  set S : Set K :=
    Set.range (fun p : (Fin n × Fin n × Fin n) × ℕ =>
      (e.repr (e p.1.1 * e p.1.2.1) p.1.2.2).coeff p.2) ∪
    Set.range (fun p : Fin n × ℕ => (e.repr 1 p.1).coeff p.2) with hS
  have hScount : S.Countable := (Set.countable_range _).union (Set.countable_range _)
  set F : Subfield K := Subfield.closure S with hF
  haveI hFcount : Countable F :=
    Cardinal.mk_le_aleph0_iff.mp
      ((Subfield.cardinalMk_closure_le_max S).trans (max_le hScount.le_aleph0 le_rfl))
  haveI : CharZero F := by infer_instance
  letI algFK : Algebra F K := inferInstance
  letI algFXKX : Algebra F[X] K[X] := (Polynomial.mapRingHom (algebraMap F K)).toAlgebra
  have hFXKX : ∀ q : F[X], algebraMap F[X] K[X] q = q.map (algebraMap F K) := fun _ => rfl
  letI algFXB : Algebra F[X] B :=
    ((algebraMap K[X] B).comp (algebraMap F[X] K[X])).toAlgebra
  haveI towerFXKXB : IsScalarTower F[X] K[X] B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap F[X] K[X]) := by
    intro a b hab
    rw [hFXKX, hFXKX] at hab
    exact Polynomial.map_injective _ (algebraMap F K).injective hab
  have hmemF : ∀ x ∈ S, x ∈ F := fun x hx => Subfield.subset_closure hx
  have hrange : ∀ x : K, x ∈ F → x ∈ Set.range (algebraMap F K) := by
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  have hmul : ∀ i j k, e.repr (e i * e j) k ∈ Set.range (algebraMap F[X] K[X]) := by
    intro i j k
    have hco : ∀ d, (e.repr (e i * e j) k).coeff d ∈ Set.range (algebraMap F K) := by
      intro d
      refine hrange _ (hmemF _ ?_)
      exact Or.inl ⟨((i, j, k), d), rfl⟩
    obtain ⟨q, hq⟩ := mem_range_map_of_coeff_mem_range (algebraMap F K) _ hco
    exact ⟨q, by rw [hFXKX]; exact hq⟩
  have hone : ∀ k, e.repr 1 k ∈ Set.range (algebraMap F[X] K[X]) := by
    intro k
    have hco : ∀ d, (e.repr 1 k).coeff d ∈ Set.range (algebraMap F K) := by
      intro d
      refine hrange _ (hmemF _ ?_)
      exact Or.inr ⟨(k, d), rfl⟩
    obtain ⟨q, hq⟩ := mem_range_map_of_coeff_mem_range (algebraMap F K) _ hco
    exact ⟨q, by rw [hFXKX]; exact hq⟩
  set B₀ := descentSubalgebra e hmul hone with hB₀
  set e₀ := descentBasis e hinj hmul hone with he₀
  haveI : Module.Free F[X] B₀ := Module.Free.of_basis e₀
  haveI : Module.Finite F[X] B₀ := Module.Finite.of_basis e₀
  have hd₀ : IsUnit (Algebra.discr F[X] e₀) := by
    refine isUnit_of_isUnit_map (algebraMap F K) ?_
    have := discr_descentBasis e hinj hmul hone
    rw [hFXKX] at this
    rw [this]
    exact hd
  obtain ⟨φ⟩ := nonempty_ringHom_complex_of_countable F
  letI algFC : Algebra F ℂ := φ.toAlgebra
  letI algFXCX : Algebra F[X] ℂ[X] := (Polynomial.mapRingHom φ).toAlgebra
  have hFXCX : ∀ q : F[X], algebraMap F[X] ℂ[X] q = q.map φ := fun _ => rfl
  have hdC : IsUnit (Algebra.discr ℂ[X]
      ((e₀.baseChange ℂ[X]) : Module.Basis (Fin n) ℂ[X] (ℂ[X] ⊗[F[X]] B₀))) := by
    rw [discr_baseChange F[X] ℂ[X] B₀ e₀]
    exact hd₀.map (algebraMap F[X] ℂ[X])
  obtain ⟨ψ⟩ := nonempty_algHom_of_isUnit_discr hn (e₀.baseChange ℂ[X]) hdC
  set ψ₀ : B₀ →+* ℂ[X] :=
    (ψ : (ℂ[X] ⊗[F[X]] B₀) →ₐ[ℂ[X]] ℂ[X]).toRingHom.comp
      (Algebra.TensorProduct.includeRight : B₀ →ₐ[F[X]] (ℂ[X] ⊗[F[X]] B₀)).toRingHom with hψ₀
  have hcomm : ∀ q : F[X], ψ₀ (algebraMap F[X] B₀ q) = q.map (algebraMap F ℂ) := by
    intro q
    show ψ ((Algebra.TensorProduct.includeRight : B₀ →ₐ[F[X]] (ℂ[X] ⊗[F[X]] B₀))
      (algebraMap F[X] B₀ q)) = q.map (algebraMap F ℂ)
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F[X] ℂ[X] (ℂ[X] ⊗[F[X]] B₀),
      AlgHom.commutes]
    rfl
  have hgen : ∀ a : B₀, ∃ c : Fin n → F[X], a = ∑ i, algebraMap F[X] B₀ (c i) * e₀ i := by
    intro a
    refine ⟨fun i => e₀.repr a i, ?_⟩
    conv_lhs => rw [← e₀.sum_repr a]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.smul_def]
  obtain ⟨Ψ, hΨ⟩ := exists_ringHom_descent (E := F) (K := K) (Ω := ℂ)
    (algebraMap F[X] B₀) ψ₀ hcomm e₀ hgen
  have hcommK : ∀ q : F[X], Ψ (algebraMap F[X] B₀ q) = algebraMap F[X] K[X] q := by
    intro q
    rw [hΨ q, hFXKX]
  set Ψ' : B₀ →ₐ[F[X]] K[X] := { Ψ with commutes' := hcommK } with hΨ'
  set Θ' : K[X] ⊗[F[X]] B₀ →ₐ[K[X]] K[X] := AlgHom.liftEquiv F[X] K[X] B₀ K[X] Ψ' with hΘ'
  set Θ : B →ₐ[K[X]] K[X] :=
    Θ'.comp (descentBaseChangeEquiv e hinj hmul hone).symm.toAlgHom with hΘ
  exact ⟨Θ⟩

/-- **Algebraic simple connectedness of the affine line, general base field.**  Over any
algebraically closed field of characteristic zero, a domain that is finite free over `K[X]` with
unit discriminant has rank one.  Equivalently: the affine line has no nontrivial connected finite
étale cover, with no monogenicity assumption. -/
theorem rank_eq_one_of_isUnit_discr_algClosed {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra K[X] B]
    [Module.Free K[X] B] [Module.Finite K[X] B] {n : ℕ} (hn : 1 ≤ n)
    (e : Module.Basis (Fin n) K[X] B) (hd : IsUnit (Algebra.discr K[X] e)) : n = 1 :=
  (nonempty_algHom_of_isUnit_discr_algClosed hn e hd).elim (fun Θ => rank_eq_one_of_algHom e Θ)

end GaloisForLFunctions.HTGeometry
