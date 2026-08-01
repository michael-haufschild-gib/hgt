import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Data.Finite.Perm
import GaloisForLFunctions.HTGeometry.InvariantFractions

/-!
# The symmetric group acts on a polynomial ring by permuting the variables

Mathlib defines a symmetric polynomial as one invariant under `rename` by every permutation, but does
not record that this is a group action.  It is, and it is faithful as soon as the coefficients are
nontrivial, so the symmetric polynomials are the fixed points of a faithful action of the symmetric
group by ring automorphisms — the setting in which a fixed field is Galois with the acting group as
its Galois group.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u v

variable {σ : Type v} {R : Type u} [CommSemiring R]

/-- **Permuting the variables is an action of the symmetric group by ring automorphisms.** -/
noncomputable instance permMulSemiringAction :
    MulSemiringAction (Equiv.Perm σ) (MvPolynomial σ R) where
  smul e p := rename e p
  one_smul p := by
    show rename (⇑(1 : Equiv.Perm σ)) p = p
    simp
  mul_smul e f p := by
    show rename (⇑(e * f)) p = rename e (rename f p)
    rw [rename_rename]
    rfl
  smul_zero e := map_zero (rename (⇑e))
  smul_add e p q := map_add (rename (⇑e)) p q
  smul_one e := map_one (rename (⇑e))
  smul_mul e p q := map_mul (rename (⇑e)) p q

theorem perm_smul_def (e : Equiv.Perm σ) (p : MvPolynomial σ R) : e • p = rename e p := rfl

@[simp] theorem perm_smul_X (e : Equiv.Perm σ) (i : σ) :
    e • (X i : MvPolynomial σ R) = X (e i) := by
  rw [perm_smul_def, rename_X]

/-- **The action is faithful.** -/
instance permFaithfulSMul [Nontrivial R] : FaithfulSMul (Equiv.Perm σ) (MvPolynomial σ R) where
  eq_of_smul_eq_smul {e f} h := by
    refine Equiv.ext (fun i => ?_)
    have := h (X i)
    rw [perm_smul_X, perm_smul_X] at this
    exact X_injective this

/-- **The symmetric polynomials are exactly the fixed points of the action.** -/
theorem mem_symmetricSubalgebra_iff_smul_eq (p : MvPolynomial σ R) :
    p ∈ MvPolynomial.symmetricSubalgebra σ R ↔ ∀ e : Equiv.Perm σ, e • p = p := Iff.rfl

/-! ## The discriminant of the generic polynomial -/

/-- The product of all differences of distinct variables: the discriminant of the polynomial whose
roots are the variables, up to sign. -/
noncomputable def discrProd (K : Type u) [CommRing K] (m : ℕ) : MvPolynomial (Fin m) K :=
  ∏ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 ≠ p.2),
    (MvPolynomial.X p.1 - MvPolynomial.X p.2)

/-- **The discriminant is symmetric.**  A permutation permutes the ordered pairs of distinct indices
among themselves. -/
theorem isSymmetric_discrProd (K : Type u) [CommRing K] (m : ℕ) :
    (discrProd K m).IsSymmetric := by
  classical
  intro e
  rw [discrProd, map_prod]
  refine Finset.prod_nbij' (fun p => (e p.1, e p.2)) (fun p => (e.symm p.1, e.symm p.2))
    (fun p hp => ?_) (fun p hp => ?_) (fun p _ => by simp) (fun p _ => by simp) (fun p hp => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact fun hc => hp (e.injective hc)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact fun hc => hp (e.symm.injective hc)
  · rw [map_sub, MvPolynomial.rename_X, MvPolynomial.rename_X]

/-! ## The action on the field of rational functions -/

section FractionField

variable (K : Type u) [Field K] (m : ℕ)

/-- The symmetric group acts on the field of rational functions in finitely many variables. -/
noncomputable local instance permFractionAction :
    MulSemiringAction (Equiv.Perm (Fin m)) (FractionRing (MvPolynomial (Fin m) K)) :=
  IsFractionRing.mulSemiringAction (Equiv.Perm (Fin m)) (MvPolynomial (Fin m) K)
    (FractionRing (MvPolynomial (Fin m) K))

local instance permFractionDistrib :
    SMulDistribClass (Equiv.Perm (Fin m)) (MvPolynomial (Fin m) K)
      (FractionRing (MvPolynomial (Fin m) K)) :=
  IsFractionRing.smulDistribClass (Equiv.Perm (Fin m)) (MvPolynomial (Fin m) K)
    (FractionRing (MvPolynomial (Fin m) K))

local instance permFractionFaithful :
    FaithfulSMul (Equiv.Perm (Fin m)) (FractionRing (MvPolynomial (Fin m) K)) :=
  IsFractionRing.faithfulSMul (Equiv.Perm (Fin m)) (MvPolynomial (Fin m) K)
    (FractionRing (MvPolynomial (Fin m) K))

/-- **The field of rational functions is Galois over its symmetric part, with the symmetric group as
Galois group.**  This is the universal-polynomial statement the rank-one monodromy argument uses:
the splitting field of the generic polynomial of degree `m` has Galois group `S_m`. -/
theorem isGalois_symmetricFixedField :
    IsGalois (FixedPoints.subfield (Equiv.Perm (Fin m))
        (FractionRing (MvPolynomial (Fin m) K)))
      (FractionRing (MvPolynomial (Fin m) K)) :=
  inferInstance

/-- **The degree of the rational function field over its symmetric part is `m!`.** -/
theorem finrank_over_symmetricFixedField :
    Module.finrank (FixedPoints.subfield (Equiv.Perm (Fin m))
        (FractionRing (MvPolynomial (Fin m) K)))
      (FractionRing (MvPolynomial (Fin m) K)) = Nat.factorial m := by
  rw [FixedPoints.finrank_eq_card, Fintype.card_perm, Fintype.card_fin]

/-- **And its Galois group is the symmetric group itself.** -/
noncomputable def symmetricGaloisEquiv :
    Equiv.Perm (Fin m) ≃ (FractionRing (MvPolynomial (Fin m) K) →ₐ[FixedPoints.subfield
      (Equiv.Perm (Fin m)) (FractionRing (MvPolynomial (Fin m) K))]
      FractionRing (MvPolynomial (Fin m) K)) :=
  FixedPoints.toAlgHomEquiv _ _

/-- **The fixed field of the symmetric group is the field of symmetric rational functions.**  A
rational function invariant under permuting the variables is a ratio of symmetric polynomials, and
conversely. -/
theorem smul_eq_self_iff_ratio_isSymmetric (x : FractionRing (MvPolynomial (Fin m) K)) :
    (∀ g : Equiv.Perm (Fin m), g • x = x) ↔
      ∃ a b : MvPolynomial (Fin m) K, a.IsSymmetric ∧ b.IsSymmetric ∧ b ≠ 0 ∧
        x = algebraMap (MvPolynomial (Fin m) K) (FractionRing (MvPolynomial (Fin m) K)) a
          / algebraMap (MvPolynomial (Fin m) K) (FractionRing (MvPolynomial (Fin m) K)) b := by
  constructor
  · intro hx
    exact exists_invariant_ratio x hx
  · rintro ⟨a, b, ha, hb, hb0, rfl⟩
    intro g
    have hdiv : ∀ u v : FractionRing (MvPolynomial (Fin m) K), g • (u / v) = (g • u) / (g • v) :=
      fun u v => map_div₀ (MulSemiringAction.toRingEquiv _ _ g) u v
    rw [hdiv, smul_algebraMap_eq, smul_algebraMap_eq, perm_smul_def, perm_smul_def, ha g, hb g]

end FractionField

end GaloisForLFunctions.HTGeometry
