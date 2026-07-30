import GaloisForLFunctions.HTGeometry.ComplexAffineAlgebraicStratification
import GaloisForLFunctions.HTGeometry.RegularLevelSetLinearEquiv
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Regular stratification in arbitrary finite coordinates

This module transports affine algebraic sets between any finite coordinate type and canonical
`Fin` coordinates.  It supplies the zero-codimension regular stratification used before a global
Hausdorff-dimension bound upgrades every stratum to its actual codimension.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

def finitePiCongrLeftContinuousLinearEquiv
    {σ τ : Type*} [Fintype σ] [Fintype τ] (e : σ ≃ τ) :
    (σ → ℂ) ≃L[ℝ] (τ → ℂ) :=
  (LinearEquiv.piCongrLeft ℝ (fun _ : τ ↦ ℂ) e).toContinuousLinearEquiv

@[simp] theorem finitePiCongrLeftContinuousLinearEquiv_apply
    {σ τ : Type*} [Fintype σ] [Fintype τ] (e : σ ≃ τ)
    (x : σ → ℂ) (j : τ) :
    finitePiCongrLeftContinuousLinearEquiv e x j = x (e.symm j) := by
  simp [finitePiCongrLeftContinuousLinearEquiv, LinearEquiv.piCongrLeft,
    LinearEquiv.piCongrLeft']

@[simp] theorem finitePiCongrLeftContinuousLinearEquiv_symm_apply
    {σ τ : Type*} [Fintype σ] [Fintype τ] (e : σ ≃ τ)
    (y : τ → ℂ) (i : σ) :
    (finitePiCongrLeftContinuousLinearEquiv e).symm y i = y (e i) := by
  simp [finitePiCongrLeftContinuousLinearEquiv, LinearEquiv.piCongrLeft,
    LinearEquiv.piCongrLeft']

theorem IsComplexAffineAlgebraicSet.image_finitePiCongrLeft
    {σ τ : Type*} [Fintype σ] [Fintype τ]
    {S : Set (σ → ℂ)} (hS : IsComplexAffineAlgebraicSet S)
    (e : σ ≃ τ) :
    IsComplexAffineAlgebraicSet (finitePiCongrLeftContinuousLinearEquiv e '' S) := by
  obtain ⟨I, rfl⟩ := hS
  let E := MvPolynomial.renameEquiv ℂ e
  let J : Ideal (MvPolynomial τ ℂ) := I.map E
  refine ⟨J, ?_⟩
  ext y
  rw [MvPolynomial.mem_zeroLocus_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ p hp
    change p ∈ I.map E at hp
    obtain ⟨q, hq, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective E E.surjective).mp hp
    rw [MvPolynomial.mem_zeroLocus_iff] at hx
    simpa [E, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
      Function.comp_def] using hx q hq
  · intro hy
    refine ⟨(finitePiCongrLeftContinuousLinearEquiv e).symm y, ?_, by simp⟩
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro p hp
    have hEp : E p ∈ J := Ideal.mem_map_of_mem E hp
    have := hy (E p) hEp
    simpa [E, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
      Function.comp_def] using! this

/-- Every complex affine algebraic set in an arbitrary finite coordinate type has a finite
regular stratification, before imposing any positive global codimension bound. -/
theorem complexAffineAlgebraicSet_finiteRegularStratification_zero
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (S : Set (σ → ℂ)) (hS : IsComplexAffineAlgebraicSet S) :
    Nonempty (FiniteRegularStratification S 0) := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let E := finitePiCongrLeftContinuousLinearEquiv e
  have hSfinSet : IsComplexAffineAlgebraicSet (E '' S) :=
    hS.image_finitePiCongrLeft e
  have hSfin : IsComplexAffineAlgebraic (E '' S) := hSfinSet
  obtain ⟨strata⟩ :=
    complexAffineAlgebraic_finiteRegularStratification_zero (E '' S) hSfin
  refine ⟨?_⟩
  have himage : E.symm '' (E '' S) = S := by
    ext x
    simp
  simpa only [himage] using strata.image_continuousLinearEquiv E.symm

theorem vanishingIdeal_image_finitePiCongrLeft
    {σ τ : Type*} [Fintype σ] [Fintype τ]
    (S : Set (σ → ℂ)) (e : σ ≃ τ) :
    MvPolynomial.vanishingIdeal ℂ (finitePiCongrLeftContinuousLinearEquiv e '' S) =
      (MvPolynomial.vanishingIdeal ℂ S).map (MvPolynomial.renameEquiv ℂ e) := by
  let E := MvPolynomial.renameEquiv ℂ e
  ext p
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  constructor
  · intro hp
    let q := E.symm p
    have hq : q ∈ MvPolynomial.vanishingIdeal ℂ S := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro x hx
      have hpx := hp (finitePiCongrLeftContinuousLinearEquiv e x) ⟨x, hx, rfl⟩
      have hfun : finitePiCongrLeftContinuousLinearEquiv e x =
          fun j ↦ x (e.symm j) := by
        funext j
        simp
      simpa [q, E, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
        Function.comp_def, hfun] using hpx
    have hEq : E q = p := E.apply_symm_apply p
    exact hEq ▸ Ideal.mem_map_of_mem E hq
  · intro hp y hy
    obtain ⟨q, hq, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective E E.surjective).mp hp
    obtain ⟨x, hx, rfl⟩ := hy
    rw [MvPolynomial.mem_vanishingIdeal_iff] at hq
    simpa [E, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
      Function.comp_def] using hq x hx

/-- A Krull-dimension drop gives the corresponding finite positive-codimension stratification in
any finite coordinate type. -/
theorem complexAffineAlgebraicSet_finiteRegularStratification_of_krullDim
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    {c : ℕ} (S : Set (σ → ℂ)) (hS : IsComplexAffineAlgebraicSet S)
    (hdim : ringKrullDim
        ((MvPolynomial σ ℂ) ⧸ MvPolynomial.vanishingIdeal ℂ S) + c ≤
      (Fintype.card σ : WithBot ℕ∞)) :
    Nonempty (FiniteRegularStratification S (2 * c)) := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let E := finitePiCongrLeftContinuousLinearEquiv e
  let R := MvPolynomial.renameEquiv ℂ e
  let I := MvPolynomial.vanishingIdeal ℂ S
  let J := MvPolynomial.vanishingIdeal ℂ (E '' S)
  have hJ : J = I.map R := vanishingIdeal_image_finitePiCongrLeft S e
  let Q : ((MvPolynomial σ ℂ) ⧸ I) ≃+*
      ((MvPolynomial (Fin (Fintype.card σ)) ℂ) ⧸ J) :=
    Ideal.quotientEquiv I J R hJ
  have hdimEq : ringKrullDim ((MvPolynomial σ ℂ) ⧸ I) =
      ringKrullDim ((MvPolynomial (Fin (Fintype.card σ)) ℂ) ⧸ J) := Q.ringKrullDim
  have hdimFin : ringKrullDim
        ((MvPolynomial (Fin (Fintype.card σ)) ℂ) ⧸
          MvPolynomial.vanishingIdeal ℂ (E '' S)) + c ≤
      (Fintype.card σ : WithBot ℕ∞) := by
    simpa only [I, J, hdimEq] using hdim
  have hSfinSet : IsComplexAffineAlgebraicSet (E '' S) := hS.image_finitePiCongrLeft e
  have hSfin : IsComplexAffineAlgebraic (E '' S) := hSfinSet
  obtain ⟨strata⟩ := complexAffineAlgebraic_finiteRegularStratification_of_krullDim
    (E '' S) hSfin hdimFin
  refine ⟨?_⟩
  have himage : E.symm '' (E '' S) = S := by
    ext x
    simp
  simpa only [himage] using strata.image_continuousLinearEquiv E.symm

end

end GaloisForLFunctions.HTGeometry
