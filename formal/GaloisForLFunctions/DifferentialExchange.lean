import GaloisForLFunctions.DifferentialPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Partial evaluation of differential polynomials and the differential Steinitz exchange

The differential-transcendence matroid needs the exchange property.  Its mechanism is a *partial*
evaluation of a two-family differential polynomial: substitute the jets of the right family `y` into
the right variables and keep the left variables `X` formal, landing in the differential polynomial
ring in the left variables over `K`.

The construction factors as the isomorphism splitting the left/right variables followed by
`MvPolynomial.map` of the jet evaluation at `y`; hence it is injective exactly when `y` is
differentially transcendental (the jet evaluation is injective).  This injectivity is the crux: a
nonzero two-family relation stays nonzero after substituting a differentially transcendental `y`.
-/

namespace GaloisForLFunctions

open MvPolynomial

variable {L R k K : Type*} [CommRing k] [CommRing K] [Algebra k K] [Differential K]

/-- Split the left and right jet variables: `k{L ⊔ R}` as differential polynomials in the left
variables with coefficients differential polynomials in the right variables. -/
noncomputable def diffPolySumSplit (L R k : Type*) [CommRing k] :
    DifferentialPolynomial (L ⊕ R) k ≃ₐ[k]
      MvPolynomial (L × ℕ) (DifferentialPolynomial R k) :=
  (MvPolynomial.renameEquiv k (Equiv.sumProdDistrib L R ℕ)).trans
    (MvPolynomial.sumAlgEquiv k (L × ℕ) (R × ℕ))

/-- Partial evaluation: substitute the right variables with the jets of `y`, keep the left variables
formal. -/
noncomputable def diffPolyEvalRight (y : R → K) :
    DifferentialPolynomial (L ⊕ R) k →+* DifferentialPolynomial L K :=
  (MvPolynomial.map (differentialPolynomialEval (C := k) y).toRingHom).comp
    (diffPolySumSplit L R k).toRingHom

/-- When `y` is differentially transcendental, substituting it into the right variables is injective:
a nonzero two-family relation cannot vanish. -/
theorem diffPolyEvalRight_injective (y : R → K) (hy : DifferentialIndependent k y) :
    Function.Injective (diffPolyEvalRight (L := L) (k := k) y) := by
  have hmap : Function.Injective
      ⇑(MvPolynomial.map (σ := L × ℕ) (differentialPolynomialEval (C := k) y).toRingHom) := by
    apply MvPolynomial.map_injective
    intro a b hab
    exact hy hab
  have hsplit : Function.Injective ⇑(diffPolySumSplit L R k).toRingHom :=
    (diffPolySumSplit L R k).injective
  rw [diffPolyEvalRight, RingHom.coe_comp]
  exact hmap.comp hsplit

theorem diffPolySumSplit_X_inl (i : L) (n : ℕ) :
    diffPolySumSplit L R k (MvPolynomial.X (Sum.inl i, n)) = MvPolynomial.X (i, n) := by
  simp only [diffPolySumSplit, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
    Equiv.sumProdDistrib_apply_left]
  simp [sumAlgEquiv, sumRingEquiv, mvPolynomialEquivMvPolynomial, sumToIter_Xl]

theorem diffPolySumSplit_X_inr (j : R) (n : ℕ) :
    diffPolySumSplit L R k (MvPolynomial.X (Sum.inr j, n)) =
      MvPolynomial.C (MvPolynomial.X (j, n)) := by
  simp only [diffPolySumSplit, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
    Equiv.sumProdDistrib_apply_right]
  simp [sumAlgEquiv, sumRingEquiv, mvPolynomialEquivMvPolynomial, sumToIter_Xr]

theorem diffPolySumSplit_C (c : k) :
    diffPolySumSplit L R k (MvPolynomial.C c) = MvPolynomial.C (MvPolynomial.C c) := by
  simp only [diffPolySumSplit, AlgEquiv.trans_apply, renameEquiv_apply, rename_C]
  simp [sumAlgEquiv, sumRingEquiv, mvPolynomialEquivMvPolynomial, sumToIter_C]

@[simp] theorem diffPolyEvalRight_X_inl (y : R → K) (i : L) (n : ℕ) :
    diffPolyEvalRight (k := k) y (MvPolynomial.X (Sum.inl i, n)) = MvPolynomial.X (i, n) := by
  show (MvPolynomial.map _) (diffPolySumSplit L R k (MvPolynomial.X (Sum.inl i, n))) = _
  rw [diffPolySumSplit_X_inl, map_X]

@[simp] theorem diffPolyEvalRight_X_inr (y : R → K) (j : R) (n : ℕ) :
    diffPolyEvalRight (L := L) (k := k) y (MvPolynomial.X (Sum.inr j, n)) =
      MvPolynomial.C (differentialJet n (y j)) := by
  show (MvPolynomial.map _) (diffPolySumSplit L R k (MvPolynomial.X (Sum.inr j, n))) = _
  rw [diffPolySumSplit_X_inr, map_C]
  congr 1
  simp [differentialPolynomialEval]

@[simp] theorem diffPolyEvalRight_C (y : R → K) (c : k) :
    diffPolyEvalRight (L := L) (k := k) y (MvPolynomial.C c) =
      MvPolynomial.C (algebraMap k K c) := by
  show (MvPolynomial.map _) (diffPolySumSplit L R k (MvPolynomial.C c)) = _
  rw [diffPolySumSplit_C, map_C]
  congr 1
  simp [differentialPolynomialEval]

/-- Evaluating the surviving left variables at `x` after substituting `y` recovers the full
evaluation of the two-family relation at `(x, y)`. -/
theorem diffPolyEvalRight_eval (x : L → K) (y : R → K) (P : DifferentialPolynomial (L ⊕ R) k) :
    differentialPolynomialEval (C := K) x (diffPolyEvalRight (k := k) y P) =
      differentialPolynomialEval (C := k) (Sum.elim x y) P := by
  have hring :
      ((differentialPolynomialEval (C := K) x).toRingHom.comp
          (diffPolyEvalRight (L := L) (k := k) y)) =
        (differentialPolynomialEval (C := k) (Sum.elim x y)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [differentialPolynomialEval]
    · rintro ⟨a | a, n⟩ <;>
        simp [differentialPolynomialEval_X]
  exact RingHom.congr_fun hring P

end GaloisForLFunctions
