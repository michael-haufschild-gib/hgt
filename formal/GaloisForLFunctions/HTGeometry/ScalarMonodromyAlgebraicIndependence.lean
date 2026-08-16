import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots

/-!
# Unbounded scalar monodromy obstructs algebraic dependence

Continuation of a germ along a loop is an algebra automorphism of the ambient germ algebra fixing
the coefficient field pointwise. This file records the resulting finite-degree obstruction in
purely algebraic form.

Let `A` be a domain over a field `L`, let `F : A` be nonzero and let `B` be an `L`-subalgebra of
`A`. Assume that for every `N` there is an `L`-algebra automorphism `σ` of `A` fixing `B`
pointwise with

`σ F = ξ • F`,

where the powers `ξ ^ 0, …, ξ ^ (m - 1)` are pairwise distinct for some `m > N`. Then `F` is
transcendental over `B`: an algebraic relation of degree `d` would be satisfied by the `m > d`
distinct elements `ξ ^ k • F`.

Applied to `B = L[G]` for a second germ `G` fixed by every such automorphism, this gives algebraic
independence of the pair `(G, F)` over `L`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

section Iterate

variable {L A : Type*} [CommSemiring L] [CommSemiring A] [Algebra L A]

/-- Iterating a scalar monodromy automorphism multiplies the moved germ by the corresponding power
of the multiplier. -/
theorem algEquiv_pow_apply_of_scalar (σ : A ≃ₐ[L] A) (ξ : L) (F : A)
    (hF : σ F = algebraMap L A ξ * F) (k : ℕ) :
    (σ ^ k) F = algebraMap L A ξ ^ k * F := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : (σ ^ (k + 1)) F = (σ ^ k) (σ F) := by
        rw [pow_succ]
        rfl
      rw [hstep, hF, map_mul, (σ ^ k).commutes, ih]
      ring

/-- An element fixed by an automorphism is fixed by all of its powers. -/
theorem algEquiv_pow_apply_of_fixed (σ : A ≃ₐ[L] A) (b : A) (hb : σ b = b) (k : ℕ) :
    (σ ^ k) b = b := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : (σ ^ (k + 1)) b = (σ ^ k) (σ b) := by
        rw [pow_succ]
        rfl
      rw [hstep, hb, ih]

end Iterate

section Transcendence

variable {L A : Type*} [Field L] [CommRing A] [IsDomain A] [Algebra L A]

/--
**Scalar-monodromy transcendence.** If arbitrarily many pairwise distinct scalar multipliers are
realized on `F` by algebra automorphisms fixing the subalgebra `B` pointwise, then `F` is
transcendental over `B`.
-/
theorem transcendental_of_unbounded_scalar_monodromy
    (B : Subalgebra L A) (F : A) (hF : F ≠ 0)
    (hmono : ∀ N : ℕ, ∃ (m : ℕ) (ξ : L) (σ : A ≃ₐ[L] A),
      N < m ∧ (∀ i j : ℕ, i < m → j < m → ξ ^ i = ξ ^ j → i = j) ∧
      σ F = algebraMap L A ξ * F ∧ ∀ b : A, b ∈ B → σ b = b) :
    Transcendental B F := by
  rw [transcendental_iff]
  intro p hp
  obtain ⟨m, ξ, σ, hm, hdist, hσF, hσB⟩ := hmono p.natDegree
  have hcomp : ∀ k : ℕ,
      ((σ ^ k : A ≃ₐ[L] A) : A →+* A).comp (algebraMap (↥B) A) = (algebraMap (↥B) A) := by
    intro k
    refine RingHom.ext fun b => ?_
    exact algEquiv_pow_apply_of_fixed σ (b : A) (hσB (b : A) b.2) k
  have hroot : ∀ k : ℕ,
      Polynomial.eval₂ (algebraMap (↥B) A) (algebraMap L A ξ ^ k * F) p = 0 := by
    intro k
    have hzero : Polynomial.eval₂ (algebraMap (↥B) A) F p = 0 := by
      simpa [Polynomial.aeval_def] using hp
    have hFk : ((σ ^ k : A ≃ₐ[L] A) : A →+* A) F = algebraMap L A ξ ^ k * F :=
      algEquiv_pow_apply_of_scalar σ ξ F hσF k
    have hmap := Polynomial.hom_eval₂ p (algebraMap (↥B) A)
      ((σ ^ k : A ≃ₐ[L] A) : A →+* A) F
    rw [hzero, hcomp k, hFk] at hmap
    simpa using hmap.symm
  have hinj : Function.Injective fun k : Fin m => algebraMap L A ξ ^ (k : ℕ) * F := by
    intro i j hij
    simp only at hij
    have hpow : algebraMap L A ξ ^ (i : ℕ) = algebraMap L A ξ ^ (j : ℕ) :=
      mul_right_cancel₀ hF hij
    have hL : (algebraMap L A) (ξ ^ (i : ℕ)) = (algebraMap L A) (ξ ^ (j : ℕ)) := by
      simpa [map_pow] using hpow
    exact Fin.ext (hdist i j i.2 j.2 ((algebraMap L A).injective hL))
  have hdeg : (p.map (algebraMap (↥B) A)).natDegree < Fintype.card (Fin m) := by
    have hle := Polynomial.natDegree_map_le (f := (algebraMap (↥B) A)) (p := p)
    simpa using lt_of_le_of_lt hle hm
  have hmapzero : p.map (algebraMap (↥B) A) = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p.map (algebraMap (↥B) A)) hinj
      (fun k => by simpa [Polynomial.eval_map] using hroot (k : ℕ)) hdeg
  refine Polynomial.ext fun n => ?_
  have hcoeff : (algebraMap (↥B) A) (p.coeff n) = 0 := by
    have h0 := congrArg (fun q => Polynomial.coeff q n) hmapzero
    simpa [Polynomial.coeff_map] using h0
  have hinjB : Function.Injective (algebraMap (↥B) A) := fun a b hab => Subtype.ext hab
  have hzero : p.coeff n = 0 := hinjB (by simpa using hcoeff)
  simpa using hzero

end Transcendence

section Pair

variable {L A : Type*} [Field L] [CommRing A] [IsDomain A] [Algebra L A]

/-- Reindexing equivalence between `Option (Fin 1)` and `Fin 2`. -/
def optionFinOneEquivFinTwo : Option (Fin 1) ≃ Fin 2 where
  toFun o := o.elim 1 fun _ => 0
  invFun i := if i = 0 then some 0 else none
  left_inv := by decide
  right_inv := by decide

/--
**Unbounded one-coordinate monodromy obstructs algebraic dependence.** If `G` is transcendental
over `L` and arbitrarily many pairwise distinct scalar multipliers are realized on the nonzero
germ `F` by algebra automorphisms fixing `G`, then `G` and `F` are algebraically independent
over `L`.
-/
theorem algebraicIndependent_pair_of_unbounded_scalar_monodromy
    (F G : A) (hF : F ≠ 0) (hG : Transcendental L G)
    (hmono : ∀ N : ℕ, ∃ (m : ℕ) (ξ : L) (σ : A ≃ₐ[L] A),
      N < m ∧ (∀ i j : ℕ, i < m → j < m → ξ ^ i = ξ ^ j → i = j) ∧
      σ F = algebraMap L A ξ * F ∧ σ G = G) :
    AlgebraicIndependent L ![G, F] := by
  classical
  have hxIndep : AlgebraicIndependent L ![G] :=
    (algebraicIndependent_iff_transcendental (x := G)).mpr hG
  have hrange : Set.range (![G] : Fin 1 → A) = {G} := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      rfl
    · rintro rfl
      exact ⟨0, rfl⟩
  have hTrans : Transcendental (Algebra.adjoin L (Set.range (![G] : Fin 1 → A))) F := by
    refine transcendental_of_unbounded_scalar_monodromy
      (Algebra.adjoin L (Set.range (![G] : Fin 1 → A))) F hF ?_
    intro N
    obtain ⟨m, ξ, σ, hm, hdist, hσF, hσG⟩ := hmono N
    refine ⟨m, ξ, σ, hm, hdist, hσF, ?_⟩
    intro b hb
    refine Algebra.adjoin_induction (p := fun x _ => σ x = x) (fun y hy => ?_)
      (fun r => σ.commutes r)
      (fun y z _ _ hy hz => by rw [map_add, hy, hz])
      (fun y z _ _ hy hz => by rw [map_mul, hy, hz]) hb
    rw [hrange] at hy
    rw [Set.mem_singleton_iff.mp hy]
    exact hσG
  have hopt : AlgebraicIndependent L fun o : Option (Fin 1) => o.elim F ![G] :=
    (hxIndep.option_iff_transcendental F).mpr hTrans
  have hcomp : (![G, F] ∘ optionFinOneEquivFinTwo) = fun o : Option (Fin 1) => o.elim F ![G] := by
    funext o
    cases o with
    | none => rfl
    | some i =>
        fin_cases i
        rfl
  exact (algebraicIndependent_equiv' optionFinOneEquivFinTwo hcomp).mp hopt

end Pair

end GaloisForLFunctions.HTGeometry
