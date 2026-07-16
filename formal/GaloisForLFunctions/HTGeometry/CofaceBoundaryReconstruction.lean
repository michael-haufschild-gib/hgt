import GaloisForLFunctions.HTGeometry.SquarefreeVeroneseIdeal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Coface boundary reconstruction

The weighted star boundary matrix presents the codimension-two squarefree Veronese constraint.
This module computes every signed maximal minor, proves that the minors reconstruct the full
Veronese ideal, and packages exactness, origin-minimality, absence of higher syzygies, and the
free ranks `(1, r+1, r)` in one positive-order certificate.
-/

namespace GaloisForLFunctions.VeroneseIdeal

open MvPolynomial Finset Matrix
open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F]

def cofaceBoundaryMatrix (r : ℕ) :
    Matrix (Fin (r + 1)) (Fin r) (MvPolynomial (Fin (r + 1)) F) :=
  fun i j => Fin.cases (-X 0) (fun q => if q = j then X q.succ else 0) i

theorem cofaceBoundaryMatrix_mulVec (r : ℕ)
    (b : Fin r → MvPolynomial (Fin (r + 1)) F) :
    (cofaceBoundaryMatrix r).mulVec b = cofaceBoundary r b := by
  funext i
  refine Fin.cases ?_ (fun q => ?_) i
  · simp only [cofaceBoundaryMatrix, cofaceBoundary, Matrix.mulVec, dotProduct,
      Fin.cases_zero, Finset.mul_sum]
  · simp [cofaceBoundaryMatrix, cofaceBoundary, Matrix.mulVec, dotProduct]

def cofaceMinorRow (r : ℕ) : Fin (r + 1) → Fin r → Fin (r + 1) :=
  Fin.cases Fin.succ (fun q i => if i = q then 0 else i.succ)

theorem cofaceMinorRow_injective (r : ℕ) (k : Fin (r + 1)) :
    Function.Injective (cofaceMinorRow r k) := by
  refine Fin.cases ?_ (fun q => ?_) k
  · exact Fin.succ_injective r
  · intro i j hij
    by_cases hi : i = q
    · subst i
      by_cases hj : j = q
      · exact hj.symm
      · exfalso
        have hval := congrArg Fin.val hij
        simp [cofaceMinorRow, hj] at hval
    · by_cases hj : j = q
      · subst j
        exfalso
        have hval := congrArg Fin.val hij
        simp [cofaceMinorRow, hi] at hval
      · simp only [cofaceMinorRow, Fin.cases_succ, if_neg hi, if_neg hj] at hij
        exact Fin.succ_injective r hij

theorem cofaceMinorRow_ne (r : ℕ) (k : Fin (r + 1)) (i : Fin r) :
    cofaceMinorRow r k i ≠ k := by
  refine Fin.cases ?_ (fun q => ?_) k
  · simp [cofaceMinorRow]
  · by_cases hi : i = q
    · subst i
      intro h
      have hval := congrArg Fin.val h
      simp [cofaceMinorRow] at hval
    · simp [cofaceMinorRow, hi]

def cofaceBoundaryMaximalMinor (r : ℕ) (k : Fin (r + 1)) :
    MvPolynomial (Fin (r + 1)) F :=
  Matrix.det ((cofaceBoundaryMatrix r).submatrix (cofaceMinorRow r k) id)

@[simp] theorem cofaceBoundaryMinorMatrix_zero (r : ℕ) (i j : Fin r) :
    (cofaceBoundaryMatrix (F := F) r).submatrix (cofaceMinorRow r 0) id i j =
      if i = j then X i.succ else 0 := by
  simp [cofaceBoundaryMatrix, cofaceMinorRow]

@[simp] theorem cofaceBoundaryMinorMatrix_succ (r : ℕ) (q i j : Fin r) :
    (cofaceBoundaryMatrix (F := F) r).submatrix (cofaceMinorRow r q.succ) id i j =
      if i = q then -X 0 else if i = j then X i.succ else 0 := by
  by_cases hi : i = q <;> simp [cofaceBoundaryMatrix, cofaceMinorRow, hi]

theorem cofaceBoundaryMaximalMinor_zero (r : ℕ) :
    cofaceBoundaryMaximalMinor (F := F) r 0 = cofaceMonomial r 0 := by
  rw [cofaceBoundaryMaximalMinor]
  have hmatrix :
      (cofaceBoundaryMatrix (F := F) r).submatrix (cofaceMinorRow r 0) id =
        Matrix.diagonal (fun i : Fin r => X i.succ) := by
    apply Matrix.ext
    intro i j
    rw [cofaceBoundaryMinorMatrix_zero]
    simp [Matrix.diagonal_apply]
  rw [hmatrix, Matrix.det_diagonal]
  apply mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := F) (0 : Fin (r + 1)))
  rw [X_mul_cofaceMonomial]
  rw [Fin.prod_univ_succ]

theorem cofaceBoundaryMaximalMinor_succ (r : ℕ) (q : Fin r) :
    cofaceBoundaryMaximalMinor (F := F) r q.succ = -cofaceMonomial r q.succ := by
  rw [cofaceBoundaryMaximalMinor, Matrix.det_apply']
  rw [Finset.sum_eq_single 1]
  · simp only [Equiv.Perm.coe_one, id_eq, Equiv.Perm.sign_one, Units.val_one,
      Int.cast_one, one_mul]
    have hdiag :
        (∏ x, (cofaceBoundaryMatrix (F := F) r).submatrix
          (cofaceMinorRow r q.succ) id x x) =
        ∏ x : Fin r, if x = q then -X 0 else X x.succ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [cofaceBoundaryMinorMatrix_succ]
      simp
    rw [hdiag]
    rw [Finset.prod_ite]
    simp only [Finset.filter_eq', Finset.mem_univ, if_true]
    apply mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := F) q.succ)
    rw [mul_neg, X_mul_cofaceMonomial]
    rw [show (∏ x ∈ (Finset.univ : Finset (Fin r)) with ¬x = q, X x.succ) =
        ∏ x ∈ (Finset.univ : Finset (Fin r)).erase q, X x.succ by
          congr 1
          ext x
          simp [and_comm]]
    simp only [Finset.prod_singleton]
    have hprodall :
        (X q.succ : MvPolynomial (Fin (r + 1)) F) *
            ∏ x ∈ (Finset.univ : Finset (Fin r)).erase q,
              (X x.succ : MvPolynomial (Fin (r + 1)) F) =
          ∏ x : Fin r, (X x.succ : MvPolynomial (Fin (r + 1)) F) := by
      exact Finset.mul_prod_erase (Finset.univ : Finset (Fin r))
        (fun x : Fin r => (X x.succ : MvPolynomial (Fin (r + 1)) F))
        (Finset.mem_univ q)
    calc
      X q.succ * (-X 0 * ∏ x ∈ (Finset.univ : Finset (Fin r)).erase q, X x.succ) =
          -X 0 * (X q.succ *
            ∏ x ∈ (Finset.univ : Finset (Fin r)).erase q, X x.succ) := by ring
      _ = -X 0 * ∏ x : Fin r, X x.succ := by rw [hprodall]
      _ = -∏ j : Fin (r + 1), X j := by
        rw [Fin.prod_univ_succ]
        ring
  · intro sigma hsigma hne
    have hmove : ∃ i : Fin r, sigma i ≠ i := by
      by_contra h
      push Not at h
      exact hne (Equiv.ext h)
    obtain ⟨i, hi⟩ := hmove
    have hprod : ∏ j, (cofaceBoundaryMatrix (F := F) r).submatrix
        (cofaceMinorRow r q.succ) id (sigma j) j = 0 := by
      rw [Finset.prod_eq_zero_iff]
      by_cases hiq : sigma i = q
      · have hi_ne_q : i ≠ q := by
          intro h
          exact hi (h ▸ hiq)
        have hsigq : sigma q ≠ q := by
          intro hq
          exact hi_ne_q (sigma.injective (hiq.trans hq.symm))
        refine ⟨q, Finset.mem_univ q, ?_⟩
        change (cofaceBoundaryMatrix (F := F) r).submatrix
          (cofaceMinorRow r q.succ) id (sigma q) q = 0
        rw [cofaceBoundaryMinorMatrix_succ]
        simp [hsigq]
      · refine ⟨i, Finset.mem_univ i, ?_⟩
        change (cofaceBoundaryMatrix (F := F) r).submatrix
          (cofaceMinorRow r q.succ) id (sigma i) i = 0
        rw [cofaceBoundaryMinorMatrix_succ]
        simp [hiq, hi]
    rw [hprod, mul_zero]
  · simp

end

end GaloisForLFunctions.VeroneseIdeal

namespace GaloisForLFunctions.VeroneseIdeal

open MvPolynomial Finset Matrix
open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F]

/-- The ideal of maximal minors of the weighted coface boundary matrix. -/
def cofaceBoundaryMaximalMinorIdeal (r : ℕ) :
    Ideal (MvPolynomial (Fin (r + 1)) F) :=
  Ideal.span (Set.range (cofaceBoundaryMaximalMinor (F := F) r))

/-- The maximal minors recover exactly the normal-crossing Jacobian ideal. -/
theorem cofaceBoundaryMaximalMinorIdeal_eq_normalCrossingJacobianIdeal (r : ℕ) :
    cofaceBoundaryMaximalMinorIdeal (F := F) r =
      normalCrossingJacobianIdeal (F := F) r := by
  apply le_antisymm
  · rw [cofaceBoundaryMaximalMinorIdeal]
    refine Ideal.span_le.2 ?_
    rintro P ⟨k, rfl⟩
    refine Fin.cases ?_ (fun q => ?_) k
    · rw [cofaceBoundaryMaximalMinor_zero, ← pderiv_normalCrossingPolynomial]
      exact Ideal.subset_span ⟨0, rfl⟩
    · rw [cofaceBoundaryMaximalMinor_succ]
      apply (normalCrossingJacobianIdeal (F := F) r).neg_mem_iff.2
      rw [← pderiv_normalCrossingPolynomial]
      exact Ideal.subset_span ⟨q.succ, rfl⟩
  · rw [normalCrossingJacobianIdeal]
    refine Ideal.span_le.2 ?_
    rintro P ⟨k, rfl⟩
    change pderiv k (normalCrossingPolynomial (F := F) r) ∈ _
    rw [pderiv_normalCrossingPolynomial]
    refine Fin.cases ?_ (fun q => ?_) k
    · rw [← cofaceBoundaryMaximalMinor_zero]
      exact Ideal.subset_span ⟨0, rfl⟩
    · rw [← neg_neg (cofaceMonomial (F := F) r q.succ),
        ← cofaceBoundaryMaximalMinor_succ]
      exact (cofaceBoundaryMaximalMinorIdeal (F := F) r).neg_mem_iff.2
        (Ideal.subset_span ⟨q.succ, rfl⟩)

/-- **Maximal-minor reconstruction.** The maximal minors of the coface boundary matrix generate
exactly the squarefree degree-`r` Veronese ideal. -/
theorem cofaceBoundaryMaximalMinorIdeal_eq_veroneseIdeal (r : ℕ) :
    cofaceBoundaryMaximalMinorIdeal (F := F) r =
      veroneseIdeal F (Fin (r + 1)) r := by
  rw [cofaceBoundaryMaximalMinorIdeal_eq_normalCrossingJacobianIdeal,
    normalCrossingJacobianIdeal_eq_veroneseIdeal]

/-- The face coefficients generate exactly the squarefree Veronese ideal. -/
theorem cofaceMonomialIdeal_eq_veroneseIdeal (r : ℕ) :
    Ideal.span (Set.range (cofaceMonomial (F := F) r)) =
      veroneseIdeal F (Fin (r + 1)) r := by
  rw [← normalCrossingJacobianIdeal_eq_veroneseIdeal,
    normalCrossingJacobianIdeal]
  congr 1
  ext P
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, pderiv_normalCrossingPolynomial r i⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, (pderiv_normalCrossingPolynomial r i).symm⟩

/-- Membership in the constraint ideal is equivalent to being an actual value of the relation
map, not merely to belonging to an abstract span. -/
theorem mem_veroneseIdeal_iff_exists_cofaceRelation (r : ℕ)
    (P : MvPolynomial (Fin (r + 1)) F) :
    P ∈ veroneseIdeal F (Fin (r + 1)) r ↔
      ∃ a : Fin (r + 1) → MvPolynomial (Fin (r + 1)) F,
        cofaceRelation r a = P := by
  rw [← cofaceMonomialIdeal_eq_veroneseIdeal]
  constructor
  · intro hP
    refine Submodule.span_induction (p := fun x _ =>
      ∃ a : Fin (r + 1) → MvPolynomial (Fin (r + 1)) F,
        cofaceRelation r a = x) ?_ ?_ ?_ ?_ hP
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      refine ⟨fun j => if j = i then 1 else 0, ?_⟩
      simp [cofaceRelation]
    · exact ⟨0, by simp [cofaceRelation]⟩
    · rintro x y hx hy ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨fun i => a i + b i, ?_⟩
      calc
        cofaceRelation r (fun i => a i + b i) =
            cofaceRelation r a + cofaceRelation r b := by
          simp [cofaceRelation, add_mul, Finset.sum_add_distrib]
        _ = x + y := by rw [ha, hb]
    · rintro c x hx ⟨a, ha⟩
      refine ⟨fun i => c * a i, ?_⟩
      calc
        cofaceRelation r (fun i => c * a i) = c * cofaceRelation r a := by
          simp [cofaceRelation, mul_assoc, Finset.mul_sum]
        _ = c • x := by rw [ha, smul_eq_mul]
  · rintro ⟨a, rfl⟩
    rw [cofaceRelation]
    apply Ideal.sum_mem
    intro i hi
    apply Ideal.mul_mem_left
    exact Ideal.subset_span ⟨i, rfl⟩

/-- The image of the relation map is precisely the squarefree constraint ideal. -/
theorem range_cofaceRelation (r : ℕ) :
    Set.range (cofaceRelation (F := F) r) =
      (veroneseIdeal F (Fin (r + 1)) r : Set (MvPolynomial (Fin (r + 1)) F)) := by
  ext P
  rw [Set.mem_range, SetLike.mem_coe, mem_veroneseIdeal_iff_exists_cofaceRelation]

/-- Evaluation at the normal-crossing origin. -/
def cofaceOrigin (r : ℕ) : MvPolynomial (Fin (r + 1)) F →+* F :=
  eval₂Hom (RingHom.id F) (fun _ => 0)

/-- Every entry of the boundary matrix vanishes at the normal-crossing origin. -/
theorem cofaceOrigin_boundaryMatrix (r : ℕ) (i : Fin (r + 1)) (j : Fin r) :
    cofaceOrigin (F := F) r (cofaceBoundaryMatrix r i j) = 0 := by
  refine Fin.cases ?_ (fun q => ?_) i
  · simp [cofaceOrigin, cofaceBoundaryMatrix]
  · by_cases hq : q = j <;> simp [cofaceOrigin, cofaceBoundaryMatrix, hq]

/-- In positive order, every face coefficient of the relation map vanishes at the origin. -/
theorem cofaceOrigin_cofaceMonomial (r : ℕ) (hr : 0 < r) (i : Fin (r + 1)) :
    cofaceOrigin (F := F) r (cofaceMonomial r i) = 0 := by
  rw [cofaceMonomial, map_prod]
  have hcard : (Finset.univ.erase i : Finset (Fin (r + 1))).card = r := by simp
  have hnonempty : (Finset.univ.erase i : Finset (Fin (r + 1))).Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact hr
  obtain ⟨j, hj⟩ := hnonempty
  exact Finset.prod_eq_zero hj (by simp [cofaceOrigin])

/-- The ranks of the three free terms in the coface complex are `(1, r+1, r)`. -/
theorem cofaceBoundaryComplex_bettiRanks (r : ℕ) :
    Fintype.card (Fin 1) = 1 ∧
      Fintype.card (Fin (r + 1)) = r + 1 ∧
        Fintype.card (Fin r) = r := by
  simp

/-- A concrete certificate for the positive-order minimal length-two coface resolution. -/
structure CofaceBoundaryResolutionCertificate (r : ℕ) : Prop where
  positiveOrder : 0 < r
  boundaryInjective : Function.Injective (cofaceBoundary (F := F) r)
  middleExact : ∀ a, cofaceRelation r a = 0 ↔
    ∃ b : Fin r → MvPolynomial (Fin (r + 1)) F, a = cofaceBoundary r b
  relationImage : Set.range (cofaceRelation (F := F) r) =
    (veroneseIdeal F (Fin (r + 1)) r : Set (MvPolynomial (Fin (r + 1)) F))
  maximalMinorReconstruction : cofaceBoundaryMaximalMinorIdeal (F := F) r =
    veroneseIdeal F (Fin (r + 1)) r
  boundaryMinimal : ∀ i j, cofaceOrigin (F := F) r (cofaceBoundaryMatrix r i j) = 0
  relationMinimal : ∀ i, cofaceOrigin (F := F) r (cofaceMonomial r i) = 0
  bettiRanks : Fintype.card (Fin 1) = 1 ∧
    Fintype.card (Fin (r + 1)) = r + 1 ∧ Fintype.card (Fin r) = r

/-- **Codimension-two boundary reconstruction.** For every positive order, the coface presentation
is exact, has no higher syzygy, is minimal at the origin, and is reconstructed by its maximal
minors with free ranks `(1, r+1, r)`. -/
theorem cofaceBoundaryResolutionCertificate (r : ℕ) (hr : 0 < r) :
    CofaceBoundaryResolutionCertificate (F := F) r where
  positiveOrder := hr
  boundaryInjective := cofaceBoundary_injective r
  middleExact := cofaceRelation_eq_zero_iff r
  relationImage := range_cofaceRelation r
  maximalMinorReconstruction := cofaceBoundaryMaximalMinorIdeal_eq_veroneseIdeal r
  boundaryMinimal := cofaceOrigin_boundaryMatrix r
  relationMinimal := cofaceOrigin_cofaceMonomial r hr
  bettiRanks := cofaceBoundaryComplex_bettiRanks r

end

end GaloisForLFunctions.VeroneseIdeal
