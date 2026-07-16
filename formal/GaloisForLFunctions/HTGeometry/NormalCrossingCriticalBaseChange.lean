import GaloisForLFunctions.HTGeometry.NormalCrossingMinimalizationDescent

/-!
# Normal-crossing derived critical base change

Restricting the rank-`r+2` normal-crossing gradient to a rank-`r+1` source face retains the
normal derivative.  Algebraically the restricted presentation is the lower coface presentation
augmented by the full product.  Although that terminal generator is classically redundant, an
invertible change of presentation turns it into an explicit zero generator.

This is the degree-one certificate for the derived base-change law: the restricted higher
criticalization is the lower criticalization with one exterior excess direction.  The different
source-labelled eliminations are different splittings of this canonical rank-one defect.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.VeroneseIdeal
open MvPolynomial Finset

noncomputable section

variable {F : Type*} [Field F]

/-- Change coordinates from the restricted higher-rank gradient presentation to the lower-rank
coface presentation plus a terminal zero generator, using the `i`th factorization
`f = X_i m_i`. -/
def cofacePresentationUntwistLinearMap (r : ℕ) (i : Fin (r + 1)) :
    (Option (Fin (r + 1)) → MvPolynomial (Fin (r + 1)) F) →ₗ[
      MvPolynomial (Fin (r + 1)) F]
    (Option (Fin (r + 1)) → MvPolynomial (Fin (r + 1)) F) where
  toFun a
    | none => a none
    | some j => if j = i then a (some j) + a none * X i else a (some j)
  map_add' a b := by
    funext j
    cases j with
    | none => rfl
    | some j =>
        by_cases hji : j = i <;>
          simp [hji, add_mul, add_assoc, add_left_comm, add_comm]
  map_smul' c a := by
    funext j
    cases j with
    | none => rfl
    | some j =>
        by_cases hji : j = i <;>
          simp [hji, mul_add, mul_assoc]

/-- The inverse coordinate change, restoring the redundant full-product generator. -/
def cofacePresentationTwistLinearMap (r : ℕ) (i : Fin (r + 1)) :
    (Option (Fin (r + 1)) → MvPolynomial (Fin (r + 1)) F) →ₗ[
      MvPolynomial (Fin (r + 1)) F]
    (Option (Fin (r + 1)) → MvPolynomial (Fin (r + 1)) F) where
  toFun a
    | none => a none
    | some j => if j = i then a (some j) - a none * X i else a (some j)
  map_add' a b := by
    funext j
    cases j with
    | none => rfl
    | some j =>
        by_cases hji : j = i <;>
          simp [hji, add_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
  map_smul' c a := by
    funext j
    cases j with
    | none => rfl
    | some j =>
        by_cases hji : j = i <;>
          simp [hji, mul_sub, mul_assoc]

/-- The restricted higher-rank presentation is linearly equivalent to the lower presentation
with one zero generator.  The equivalence is source-labelled because choosing `i` chooses one
factorization of the full product. -/
def cofacePresentationUntwist (r : ℕ) (i : Fin (r + 1)) :
    (Option (Fin (r + 1)) → MvPolynomial (Fin (r + 1)) F) ≃ₗ[
      MvPolynomial (Fin (r + 1)) F]
    (Option (Fin (r + 1)) → MvPolynomial (Fin (r + 1)) F) :=
  LinearEquiv.ofLinear
    (cofacePresentationUntwistLinearMap (F := F) r i)
    (cofacePresentationTwistLinearMap (F := F) r i)
    (by
      ext a j
      cases j with
      | none => rfl
      | some j => by_cases hji : j = i <;> simp [cofacePresentationUntwistLinearMap,
          cofacePresentationTwistLinearMap, hji])
    (by
      ext a j
      cases j with
      | none => rfl
      | some j => by_cases hji : j = i <;> simp [cofacePresentationUntwistLinearMap,
          cofacePresentationTwistLinearMap, hji])

/-- Relation map for the lower coface presentation augmented by a terminal zero generator. -/
def splitAugmentedCofaceRelation (r : ℕ)
    (a : Option (Fin (r + 1)) → MvPolynomial (Fin (r + 1)) F) :
    MvPolynomial (Fin (r + 1)) F :=
  ∑ j, a (some j) * cofaceMonomial r j

/-- **Critical base-change splitting theorem.**  Untwisting carries the restricted higher-rank
gradient relation to the lower-rank coface relation plus an invisible terminal coordinate.  This
is the generator-level isomorphism underlying the Koszul splitting
`K(m_0,...,m_r,f) ≅ K(m_0,...,m_r,0)`. -/
theorem splitAugmentedCofaceRelation_untwist (r : ℕ) (i : Fin (r + 1))
    (a : Option (Fin (r + 1)) → MvPolynomial (Fin (r + 1)) F) :
    splitAugmentedCofaceRelation r (cofacePresentationUntwist r i a) =
      augmentedCofaceRelation r a := by
  have hextra :
      (∑ j, if j = i then a none * X i * cofaceMonomial r j else 0) =
        a none * X i * cofaceMonomial r i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [splitAugmentedCofaceRelation, augmentedCofaceRelation]
  calc
    (∑ j, (cofacePresentationUntwist r i a) (some j) * cofaceMonomial r j) =
        ∑ j, (a (some j) * cofaceMonomial r j +
          if j = i then a none * X i * cofaceMonomial r j else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hji : j = i <;>
              simp [cofacePresentationUntwist, cofacePresentationUntwistLinearMap,
                hji, add_mul]
    _ = (∑ j, a (some j) * cofaceMonomial r j) +
        ∑ j, if j = i then a none * X i * cofaceMonomial r j else 0 := by
          rw [Finset.sum_add_distrib]
    _ = (∑ j, a (some j) * cofaceMonomial r j) +
        a none * X i * cofaceMonomial r i := by
          rw [hextra]
    _ = a none * normalCrossingPolynomial r +
        ∑ j, a (some j) * cofaceMonomial r j := by
          rw [mul_assoc, X_mul_cofaceMonomial, normalCrossingPolynomial]
          ring

/-- A source-labelled elimination is sent to the same terminal zero direction under its own
untwisting.  Thus eliminations are splittings of one common exterior excess line. -/
theorem cofacePresentationUntwist_elimination (r : ℕ) (i : Fin (r + 1)) :
    cofacePresentationUntwist (F := F) r i (cofaceElimination r i) =
      Pi.single none 1 := by
  funext j
  cases j with
  | none => simp [cofacePresentationUntwist, cofacePresentationUntwistLinearMap,
      cofaceElimination]
  | some j =>
      by_cases hji : j = i <;>
        simp [cofacePresentationUntwist, cofacePresentationUntwistLinearMap,
          cofaceElimination, hji]

/-- The terminal direction of the split presentation has zero boundary. -/
theorem splitAugmentedCofaceRelation_terminal_zero (r : ℕ) :
    splitAugmentedCofaceRelation (F := F) r (Pi.single none 1) = 0 := by
  simp [splitAugmentedCofaceRelation]

end

end GaloisForLFunctions.HTGeometry
