import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating
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

@[simp] theorem perm_smul_X_mv (e : Equiv.Perm σ) (i : σ) :
    e • (X i : MvPolynomial σ R) = X (e i) := by
  rw [perm_smul_def, rename_X]

/-- **The action is faithful.** -/
instance permFaithfulSMul [Nontrivial R] : FaithfulSMul (Equiv.Perm σ) (MvPolynomial σ R) where
  eq_of_smul_eq_smul {e f} h := by
    refine Equiv.ext (fun i => ?_)
    have := h (X i)
    rw [perm_smul_X_mv, perm_smul_X_mv] at this
    exact X_injective this

/-- **The symmetric polynomials are exactly the fixed points of the action.** -/
theorem mem_symmetricSubalgebra_iff_smul_eq (p : MvPolynomial σ R) :
    p ∈ MvPolynomial.symmetricSubalgebra σ R ↔ ∀ e : Equiv.Perm σ, e • p = p := Iff.rfl

/-! ## The sign as a product over inversions -/

/-- **The sign of a permutation of `Fin n` is its inversion count.**  Mathlib defines `signAux` as
the product over pairs and `sign` through a different route, and does not record that they agree. -/
theorem sign_eq_signAux {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign σ = Equiv.Perm.signAux σ := by
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · rw [map_one, Equiv.Perm.signAux_one]
  · intro f x y hxy ih
    rw [map_mul, Equiv.Perm.sign_swap hxy, ih, Equiv.Perm.signAux_mul,
      Equiv.Perm.signAux_swap hxy]

/-- The Vandermonde product: the product of the differences of the variables over all pairs in
decreasing order.  Its square is the discriminant. -/
noncomputable def vandermonde (K : Type u) [CommRing K] (n : ℕ) : MvPolynomial (Fin n) K :=
  ∏ x ∈ Equiv.Perm.finPairsLT n, (MvPolynomial.X x.1 - MvPolynomial.X x.2)

/-- Reordering a pair after applying a permutation. -/
def orderPair {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Σ _ : Fin n, Fin n) : Σ _ : Fin n, Fin n :=
  if σ x.2 < σ x.1 then ⟨σ x.1, σ x.2⟩ else ⟨σ x.2, σ x.1⟩

theorem orderPair_mem {n : ℕ} (σ : Equiv.Perm (Fin n)) {x : Σ _ : Fin n, Fin n}
    (hx : x ∈ Equiv.Perm.finPairsLT n) : orderPair σ x ∈ Equiv.Perm.finPairsLT n := by
  rw [Equiv.Perm.mem_finPairsLT] at hx ⊢
  rw [orderPair]
  by_cases h : σ x.2 < σ x.1
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    exact lt_of_le_of_ne (not_lt.1 h) (fun hc => absurd (σ.injective hc) hx.ne')

theorem orderPair_orderPair {n : ℕ} (σ : Equiv.Perm (Fin n)) {x : Σ _ : Fin n, Fin n}
    (hx : x ∈ Equiv.Perm.finPairsLT n) : orderPair σ⁻¹ (orderPair σ x) = x := by
  rw [Equiv.Perm.mem_finPairsLT] at hx
  by_cases h : σ x.2 < σ x.1
  · have hin : orderPair σ x = ⟨σ x.1, σ x.2⟩ := by rw [orderPair, if_pos h]
    rw [hin, orderPair]
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [if_pos hx]
  · have hin : orderPair σ x = ⟨σ x.2, σ x.1⟩ := by rw [orderPair, if_neg h]
    rw [hin, orderPair]
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [if_neg (asymm hx)]

/-- The product of the pairwise signs is the sign of the permutation. -/
theorem prod_sign_cast {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∏ x ∈ Equiv.Perm.finPairsLT n, (if σ x.1 ≤ σ x.2 then (-1 : R) else 1)
      = ((Equiv.Perm.sign σ : ℤ) : R) := by
  rw [sign_eq_signAux, Equiv.Perm.signAux]
  push_cast
  refine Finset.prod_congr rfl (fun x _ => ?_)
  by_cases h : σ x.1 ≤ σ x.2 <;> simp [h]

/-- **The Vandermonde product transforms by the sign.**  Renaming the variables along a permutation
multiplies it by the sign of that permutation: it is fixed by the even permutations and negated by
the odd ones. -/
theorem rename_vandermonde (K : Type u) [CommRing K] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.rename σ (vandermonde K n)
      = ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n) K) * vandermonde K n := by
  classical
  rw [vandermonde, map_prod]
  have hfactor : ∀ x ∈ Equiv.Perm.finPairsLT n,
      MvPolynomial.rename σ (MvPolynomial.X x.1 - MvPolynomial.X x.2)
        = (if σ x.1 ≤ σ x.2 then (-1 : MvPolynomial (Fin n) K) else 1)
          * (MvPolynomial.X (orderPair σ x).1 - MvPolynomial.X (orderPair σ x).2) := by
    intro x hx
    rw [Equiv.Perm.mem_finPairsLT] at hx
    rw [map_sub, MvPolynomial.rename_X, MvPolynomial.rename_X, orderPair]
    by_cases h : σ x.2 < σ x.1
    · rw [if_pos h, if_neg (not_le.2 h), one_mul]
    · have hne : σ x.1 ≠ σ x.2 := fun hc => absurd (σ.injective hc) hx.ne'
      rw [if_neg h, if_pos (le_of_lt (lt_of_le_of_ne (not_lt.1 h) hne))]
      ring
  rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib, prod_sign_cast]
  congr 1
  refine Finset.prod_nbij' (orderPair σ) (orderPair σ⁻¹) (fun x hx => orderPair_mem σ hx)
    (fun y hy => orderPair_mem σ⁻¹ hy) (fun x hx => orderPair_orderPair σ hx)
    (fun y hy => by simpa using orderPair_orderPair σ⁻¹ hy) (fun x _ => rfl)

/-- **The Vandermonde product is nonzero.** -/
theorem vandermonde_ne_zero (K : Type u) [CommRing K] [IsDomain K] (n : ℕ) :
    vandermonde K n ≠ 0 := by
  rw [vandermonde]
  refine Finset.prod_ne_zero_iff.2 (fun x hx => ?_)
  rw [Equiv.Perm.mem_finPairsLT] at hx
  intro hc
  exact absurd (MvPolynomial.X_injective (sub_eq_zero.1 hc)) hx.ne'

/-- **It is fixed by the even permutations.** -/
theorem rename_vandermonde_of_mem_alternating (K : Type u) [CommRing K] {n : ℕ}
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ alternatingGroup (Fin n)) :
    MvPolynomial.rename σ (vandermonde K n) = vandermonde K n := by
  rw [rename_vandermonde, Equiv.Perm.mem_alternatingGroup.1 hσ]
  simp

/-- **Its square is symmetric.** -/
theorem isSymmetric_vandermonde_sq (K : Type u) [CommRing K] (n : ℕ) :
    ((vandermonde K n) ^ (2 : ℕ)).IsSymmetric := by
  intro e
  rw [map_pow, rename_vandermonde, mul_pow, ← Int.cast_pow]
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> rw [h] <;> simp

/-- **But it is not itself symmetric.**  So it generates a proper extension of the symmetric
functions, of degree two: the discriminant subfield. -/
theorem not_isSymmetric_vandermonde (K : Type u) [CommRing K] [IsDomain K] {n : ℕ} (hn : 2 ≤ n)
    (h2 : (2 : K) ≠ 0) : ¬ (vandermonde K n).IsSymmetric := by
  intro hsym
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hs := hsym (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩)
  rw [rename_vandermonde, Equiv.Perm.sign_swap hne] at hs
  have hzero : (2 : MvPolynomial (Fin n) K) * vandermonde K n = 0 := by
    have : ((-1 : ℤ) : MvPolynomial (Fin n) K) * vandermonde K n = vandermonde K n := by
      simpa using hs
    rw [Int.cast_neg, Int.cast_one, neg_mul, one_mul] at this
    linear_combination -this
  rcases mul_eq_zero.1 hzero with h | h
  · exact h2 (MvPolynomial.C_eq_zero.1 (by rw [map_ofNat]; exact h))
  · exact vandermonde_ne_zero K n h

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

/-- **The discriminant of the generic polynomial is nonzero**: the generic polynomial is separable,
its roots being independent variables. -/
theorem discrProd_ne_zero (K : Type u) [CommRing K] [IsDomain K] (m : ℕ) :
    discrProd K m ≠ 0 := by
  classical
  rw [discrProd]
  refine Finset.prod_ne_zero_iff.2 (fun p hp => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  intro hc
  exact hp (MvPolynomial.X_injective (sub_eq_zero.1 hc))

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
noncomputable def symmetricFixedFieldGaloisEquiv :
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
