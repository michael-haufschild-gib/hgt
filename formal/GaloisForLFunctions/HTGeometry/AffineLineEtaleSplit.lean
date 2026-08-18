import GaloisForLFunctions.HTGeometry.SectionQuotientSplit
import GaloisForLFunctions.HTGeometry.AffineLineSimplyConnectedEtale
import Mathlib.Algebra.Algebra.Prod

/-!
# Every finite étale algebra over the affine line is split

Over an algebraically closed field `E` of characteristic zero, a finite free `E[X]`-algebra of rank
`n` whose discriminant is a unit is isomorphic to `E[X]ⁿ`:

```text
nonempty_algEquiv_pi_of_isUnit_discr :
    IsUnit (Algebra.discr E[X] e)  →  Nonempty (B ≃ₐ[E[X]] (Fin n → E[X]))
```

The proof is an induction on the rank.  `AffineLineSimplyConnectedEtale` supplies a section, whose
idempotent splits off a copy of the base (`SectionQuotientSplit`); the complementary quotient is
again finite free with unit discriminant, of rank one less, and the induction closes.

This is the strongest form of the algebraic simple connectedness of the affine line: not merely
"connected covers are trivial" but "all covers are split".  It is what the multivariable induction
consumes, because the derivation lifting `d/dw` becomes the componentwise `d/dw` after this
splitting, hence locally nilpotent.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

/-- Peeling the first coordinate off a finite product of copies of the base. -/
noncomputable def finSuccProdAlgEquiv (A : Type*) [CommRing A] (n : ℕ) :
    (Fin (n + 1) → A) ≃ₐ[A] A × (Fin n → A) :=
  AlgEquiv.ofBijective
    (AlgHom.prod (Pi.evalAlgHom A (fun _ : Fin (n + 1) => A) 0)
      (AlgHom.pi (fun i : Fin n => Pi.evalAlgHom A (fun _ : Fin (n + 1) => A) i.succ)))
    (by
      constructor
      · intro f g h
        funext i
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exact congrArg Prod.fst h
        · exact congrFun (congrArg Prod.snd h) j
      · rintro ⟨a, v⟩
        refine ⟨Fin.cons a v, ?_⟩
        apply Prod.ext
        · simp
        · funext j
          simp)

/-- The trivial algebra is the empty product. -/
noncomputable def emptyAlgEquiv (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Subsingleton B] : B ≃ₐ[A] (Fin 0 → A) :=
  { toFun := fun _ => 0
    invFun := fun _ => 0
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _
    map_mul' := fun _ _ => Subsingleton.elim _ _
    map_add' := fun _ _ => Subsingleton.elim _ _
    commutes' := fun _ => Subsingleton.elim _ _ }

universe u

theorem nonempty_algEquiv_pi_of_isUnit_discr (E : Type*) [Field E] [CharZero E] [IsAlgClosed E] :
    ∀ (n : ℕ) {B : Type u} [CommRing B] [Algebra E[X] B] [Module.Free E[X] B]
      [Module.Finite E[X] B] (e : Module.Basis (Fin n) E[X] B),
      IsUnit (Algebra.discr E[X] e) → Nonempty (B ≃ₐ[E[X]] (Fin n → E[X])) := by
  intro n
  induction n with
  | zero =>
      intro B _ _ _ _ e _
      haveI : Subsingleton B := by
        constructor
        intro x y
        have hx := e.sum_repr x
        have hy := e.sum_repr y
        simp only [Finset.univ_eq_empty, Finset.sum_empty] at hx hy
        rw [← hx, ← hy]
      exact ⟨emptyAlgEquiv E[X] B⟩
  | succ n ih =>
      intro B _ _ _ _ e hd
      obtain ⟨ψ⟩ := nonempty_algHom_of_isUnit_discr_algClosed (n := n + 1) (by omega) e hd
      obtain ⟨e', hd'⟩ := exists_basis_sectionQuot e hd ψ
      haveI := finite_sectionQuot e hd ψ
      haveI := torsionFree_sectionQuot e hd ψ
      haveI : Module.Free E[X] (sectionQuot e ψ) := Module.free_of_finite_type_torsion_free'
      obtain ⟨Φ⟩ := ih e' hd'
      exact ⟨(sectionProdEquiv e hd ψ).trans
        ((AlgEquiv.prodCongr AlgEquiv.refl Φ).trans (finSuccProdAlgEquiv E[X] n).symm)⟩

end GaloisForLFunctions.HTGeometry
