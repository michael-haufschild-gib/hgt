import GaloisForLFunctions.HTGeometry.DifferentialClosureClosed
import GaloisForLFunctions.HTGeometry.MvPolynomialTotalDerivation
import GaloisForLFunctions.HTGeometry.MatrixLogarithmicDerivative
import GaloisForLFunctions.HTGeometry.DifferentialFieldSolution

/-!
# Linear differential systems have invertible solutions over a differentially closed field

Prescribing `δX_{ij} = ∑ₖ A_{ik} X_{kj}` on the polynomial ring in the entries of a generic matrix
makes that matrix a solution of `δY = A·Y`, and its determinant is a nonzero polynomial, so the
fraction field of the coordinate ring is a differential field extension carrying an invertible
solution.  The system saying "`Y` solves the equation and its determinant is invertible" is a finite
differential system over the base, so differential closedness brings a solution back into the field
itself.

Differential closedness is also extended here to an arbitrary finite set of indeterminates, by
renaming along a bijection with a standard one.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

universe u v

variable {C : Type u} [Field C] [Algebra ℚ C] [Differential C]

/-- **Differential closedness for an arbitrary finite set of indeterminates.** -/
theorem IsDifferentiallyClosed.exists_point_finite [IsDifferentiallyClosed C] {ι : Type v}
    [Finite ι]
    (T : Finset (DifferentialPolynomial ι C)) (E : DiffFieldExt C) (z : ι → E.carrier)
    (hz : ∀ p ∈ T, differentialPolynomialEvalOver (K := C) z p = 0) :
    ∃ y : ι → C, ∀ p ∈ T, differentialPolynomialEvalOver (K := C) y p = 0 := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  set eU : ι ≃ ULift.{u} (Fin n) := e.trans Equiv.ulift.symm with heU
  have hsol : ∀ q ∈ T.image (differentialRename (K := C) eU),
      differentialPolynomialEvalOver (K := C) (fun v => z (eU.symm v)) q = 0 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    rw [differentialPolynomialEvalOver_differentialRename]
    have hfun : (fun i => z (eU.symm (eU i))) = z := by
      funext i
      rw [Equiv.symm_apply_apply]
    rw [hfun]
    exact hz p hp
  obtain ⟨y, hy⟩ := IsDifferentiallyClosed.exists_point (C := C)
    (T.image (differentialRename (K := C) eU)) E (fun v => z (eU.symm v)) hsol
  refine ⟨fun i => y (eU i), ?_⟩
  intro p hp
  have hval := hy _ (Finset.mem_image_of_mem (differentialRename (K := C) eU) hp)
  rw [differentialPolynomialEvalOver_differentialRename] at hval
  exact hval

variable {m : ℕ}

/-- The coordinate ring of the linear system `δY = A·Y`. -/
@[reducible] def systemCoordDifferential (A : Matrix (Fin m) (Fin m) C) :
    Differential (MvPolynomial (Fin m × Fin m) C) :=
  ⟨mvTotalDerivation (fun p : Fin m × Fin m =>
    ∑ k : Fin m, MvPolynomial.C (A p.1 k) * MvPolynomial.X (k, p.2))⟩

/-- The generic matrix of indeterminates. -/
def linearSystemGenericMatrix : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) C) :=
  Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (Fin m × Fin m) C)

omit [Algebra ℚ C] in
theorem matrixDeriv_linearSystemGenericMatrix (A : Matrix (Fin m) (Fin m) C) :
    letI := systemCoordDifferential A
    matrixDeriv (linearSystemGenericMatrix (C := C) (m := m))
      = (A.map (MvPolynomial.C : C → MvPolynomial (Fin m × Fin m) C)) * linearSystemGenericMatrix := by
  letI := systemCoordDifferential A
  refine Matrix.ext fun i j => ?_
  rw [matrixDeriv_apply, Matrix.mul_apply]
  show mvTotalDerivation (fun p : Fin m × Fin m =>
    ∑ k : Fin m, MvPolynomial.C (A p.1 k) * MvPolynomial.X (k, p.2))
      (MvPolynomial.X ((i, j) : Fin m × Fin m) : MvPolynomial (Fin m × Fin m) C) = _
  rw [mvTotalDerivation_X]
  exact Finset.sum_congr rfl fun k _ => rfl

omit [Algebra ℚ C] [Differential C] in
theorem det_linearSystemGenericMatrix_ne_zero : (linearSystemGenericMatrix (C := C) (m := m)).det ≠ 0 := by
  classical
  intro hzero
  set ev : MvPolynomial (Fin m × Fin m) C →+* C :=
    (MvPolynomial.eval (fun p : Fin m × Fin m => if p.1 = p.2 then (1 : C) else 0)) with hev
  have hval : ev (linearSystemGenericMatrix (C := C) (m := m)).det = 0 := by
    rw [hzero, map_zero]
  rw [RingHom.map_det, RingHom.mapMatrix_apply] at hval
  have hone : (linearSystemGenericMatrix (C := C) (m := m)).map ev = (1 : Matrix (Fin m) (Fin m) C) := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.one_apply]
    show ev (MvPolynomial.X (i, j)) = _
    rw [hev]
    show MvPolynomial.eval _ (MvPolynomial.X (i, j)) = _
    rw [MvPolynomial.eval_X]
  rw [hone, Matrix.det_one] at hval
  exact one_ne_zero hval

attribute [local instance] Classical.propDecidable

/-- The differential polynomials cutting out an invertible solution of `δY = A·Y`. -/
def fundamentalSystem (A : Matrix (Fin m) (Fin m) C) :
    Finset (DifferentialPolynomial ((Fin m × Fin m) ⊕ Unit) C) :=
  (Finset.univ.image (fun p : Fin m × Fin m =>
      (MvPolynomial.X ((Sum.inl p : (Fin m × Fin m) ⊕ Unit), 1) -
        ∑ k : Fin m, MvPolynomial.C (A p.1 k)
          * MvPolynomial.X ((Sum.inl (k, p.2) : (Fin m × Fin m) ⊕ Unit), 0) :
        DifferentialPolynomial ((Fin m × Fin m) ⊕ Unit) C)))
    ∪ {(MvPolynomial.X ((Sum.inr () : (Fin m × Fin m) ⊕ Unit), 0)
        * (Matrix.of fun i j =>
            MvPolynomial.X ((Sum.inl (i, j) : (Fin m × Fin m) ⊕ Unit), 0)).det
        - 1 : DifferentialPolynomial ((Fin m × Fin m) ⊕ Unit) C)}

variable {M : Type*} [CommRing M] [Algebra C M] [Differential M]

omit [Algebra ℚ C] [Differential C] in
theorem eval_fundamentalSystem_iff (A : Matrix (Fin m) (Fin m) C)
    (y : ((Fin m × Fin m) ⊕ Unit) → M) :
    (∀ p ∈ fundamentalSystem A, differentialPolynomialEvalOver (K := C) y p = 0) ↔
      ((∀ p : Fin m × Fin m, Differential.deriv (y (Sum.inl p))
          = ∑ k : Fin m, algebraMap C M (A p.1 k) * y (Sum.inl (k, p.2)))
        ∧ y (Sum.inr ()) * (Matrix.of fun i j => y (Sum.inl (i, j))).det = 1) := by
  have hdetmap : differentialPolynomialEvalOver (K := C) y
      (Matrix.of fun i j =>
        MvPolynomial.X ((Sum.inl (i, j) : (Fin m × Fin m) ⊕ Unit), 0)).det
      = (Matrix.of fun i j => y (Sum.inl (i, j))).det := by
    show ((differentialPolynomialEvalOver (K := C) y :
        DifferentialPolynomial ((Fin m × Fin m) ⊕ Unit) C →ₐ[C] M) :
          DifferentialPolynomial ((Fin m × Fin m) ⊕ Unit) C →+* M)
        (Matrix.of fun i j =>
          MvPolynomial.X ((Sum.inl (i, j) : (Fin m × Fin m) ⊕ Unit), 0)).det = _
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply]
    show differentialPolynomialEvalOver (K := C) y
      (MvPolynomial.X ((Sum.inl (i, j) : (Fin m × Fin m) ⊕ Unit), 0)) = _
    rw [differentialPolynomialEvalOver_X, differentialJet_zero]
    rfl
  constructor
  · intro h
    constructor
    · intro p
      have hp := h _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ p)))
      rw [map_sub, map_sum, differentialPolynomialEvalOver_X, differentialJet_succ,
        differentialJet_zero, sub_eq_zero] at hp
      rw [hp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, differentialPolynomialEvalOver_C, differentialPolynomialEvalOver_X,
        differentialJet_zero]
    · have hp := h _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      rw [map_sub, map_mul, map_one, differentialPolynomialEvalOver_X, differentialJet_zero,
        sub_eq_zero] at hp
      rw [← hp, hdetmap]
  · rintro ⟨hode, hdet⟩ p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
      rw [map_sub, map_sum, differentialPolynomialEvalOver_X, differentialJet_succ,
        differentialJet_zero, sub_eq_zero, hode q]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, differentialPolynomialEvalOver_C, differentialPolynomialEvalOver_X,
        differentialJet_zero]
    · rw [Finset.mem_singleton] at hp
      subst hp
      rw [map_sub, map_mul, map_one, differentialPolynomialEvalOver_X, differentialJet_zero,
        sub_eq_zero]
      rw [hdetmap]
      exact hdet

/-- **A linear differential system has an invertible solution over a differentially closed
field.**  The generic solution lives in the fraction field of the coordinate ring of the system, so
the system is consistent; differential closedness brings the solution back into the field. -/
theorem exists_fundamentalMatrix [IsDifferentiallyClosed C] (A : Matrix (Fin m) (Fin m) C) :
    ∃ P : Matrix (Fin m) (Fin m) C, IsUnit P.det ∧ matrixDeriv P = A * P := by
  classical
  letI : Differential (MvPolynomial (Fin m × Fin m) C) := systemCoordDifferential A
  letI : Differential (FractionRing (MvPolynomial (Fin m × Fin m) C)) :=
    fractionRingDifferential (MvPolynomial (Fin m × Fin m) C)
  letI : Algebra C (FractionRing (MvPolynomial (Fin m × Fin m) C)) :=
    ((algebraMap (MvPolynomial (Fin m × Fin m) C)
      (FractionRing (MvPolynomial (Fin m × Fin m) C))).comp
      (algebraMap C (MvPolynomial (Fin m × Fin m) C))).toAlgebra
  letI : Algebra ℚ (FractionRing (MvPolynomial (Fin m × Fin m) C)) :=
    ((algebraMap C (FractionRing (MvPolynomial (Fin m × Fin m) C))).comp
      (algebraMap ℚ C)).toAlgebra
  have halgL : ∀ a : C, algebraMap C (FractionRing (MvPolynomial (Fin m × Fin m) C)) a
      = algebraMap (MvPolynomial (Fin m × Fin m) C)
        (FractionRing (MvPolynomial (Fin m × Fin m) C))
        (algebraMap C (MvPolynomial (Fin m × Fin m) C) a) := fun _ => rfl
  have hcompat : ∀ a : C,
      Differential.deriv (algebraMap C (FractionRing (MvPolynomial (Fin m × Fin m) C)) a)
        = algebraMap C (FractionRing (MvPolynomial (Fin m × Fin m) C)) (Differential.deriv a) := by
    intro a
    rw [halgL, halgL, fractionRingDifferential_algebraMap]
    congr 1
    show mvTotalDerivation _ (MvPolynomial.C a) = MvPolynomial.C (Differential.deriv a)
    rw [mvTotalDerivation_C]
  set gen : Matrix (Fin m) (Fin m) (FractionRing (MvPolynomial (Fin m × Fin m) C)) :=
    Matrix.of fun i j => algebraMap (MvPolynomial (Fin m × Fin m) C)
      (FractionRing (MvPolynomial (Fin m × Fin m) C))
      (MvPolynomial.X ((i, j) : Fin m × Fin m)) with hgen
  have hdetgen : gen.det ≠ 0 := by
    have hmap : gen.det = algebraMap (MvPolynomial (Fin m × Fin m) C)
        (FractionRing (MvPolynomial (Fin m × Fin m) C))
        (linearSystemGenericMatrix (C := C) (m := m)).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
      congr 1
    rw [hmap]
    intro hzero
    exact det_linearSystemGenericMatrix_ne_zero (C := C) (m := m)
      ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp hzero)
  set z : ((Fin m × Fin m) ⊕ Unit) → FractionRing (MvPolynomial (Fin m × Fin m) C) :=
    fun v => match v with
      | Sum.inl p => gen p.1 p.2
      | Sum.inr _ => (gen.det)⁻¹ with hz
  have hzsol : ∀ p ∈ fundamentalSystem A,
      differentialPolynomialEvalOver (K := C) z p = 0 := by
    refine (eval_fundamentalSystem_iff A z).mpr ⟨?_, ?_⟩
    · intro p
      show Differential.deriv (gen p.1 p.2) = _
      rw [hgen]
      show Differential.deriv (algebraMap (MvPolynomial (Fin m × Fin m) C) _
        (MvPolynomial.X ((p.1, p.2) : Fin m × Fin m))) = _
      rw [fractionRingDifferential_algebraMap]
      show algebraMap (MvPolynomial (Fin m × Fin m) C) _
        (mvTotalDerivation _ (MvPolynomial.X ((p.1, p.2) : Fin m × Fin m))) = _
      rw [mvTotalDerivation_X, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul]
      rfl
    · show (gen.det)⁻¹ * (Matrix.of fun i j => gen i j).det = 1
      have hof : (Matrix.of fun i j => gen i j) = gen := rfl
      rw [hof, inv_mul_cancel₀ hdetgen]
  obtain ⟨y, hy⟩ := IsDifferentiallyClosed.exists_point_finite (C := C)
    (ι := ((Fin m × Fin m) ⊕ Unit)) (fundamentalSystem A)
    (⟨FractionRing (MvPolynomial (Fin m × Fin m) C), hcompat⟩ : DiffFieldExt C) z hzsol
  obtain ⟨hode, hdet⟩ := (eval_fundamentalSystem_iff A y).mp hy
  refine ⟨Matrix.of fun i j => y (Sum.inl (i, j)), ?_, ?_⟩
  · refine isUnit_iff_exists_inv.mpr ⟨y (Sum.inr ()), ?_⟩
    rw [mul_comm]
    exact hdet
  · refine Matrix.ext fun i j => ?_
    rw [matrixDeriv_apply, Matrix.mul_apply]
    show Differential.deriv (y (Sum.inl (i, j))) = _
    rw [hode (i, j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    show algebraMap C C (A i k) * y (Sum.inl (k, j)) = _
    rw [Algebra.algebraMap_self]
    rfl

end

end GaloisForLFunctions.HTGeometry
