import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneSums
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-! Dimension is additive on finite sums of Weil–Deligne classes.
The characteristic polynomials and determinants multiply. -/

noncomputable section

open NumberField IsDedekindDomain Module Polynomial
open WindowedLandauTheory.ConjugateSelfDual

namespace GlobalTheory.WeilDeligne.WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A v}

@[simp] theorem charpoly_zero (σ : Weil h) : (lpZero (h := h)).charpoly σ = 1 := by
  rw [lpZero, lpUnr, charpoly_mk,
    ← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℂ (Fin 0))]
  exact Matrix.charpoly_isEmpty

@[simp] theorem detChar_zero : (lpZero (h := h)).detChar = 1 := by
  rw [lpZero, lpUnr, detChar_mk]
  apply MonoidHom.ext
  intro σ
  apply Units.ext
  exact LinearMap.det_eq_one_of_subsingleton _

theorem lpDim_sumList (l : List (WD h)) : (sumList l).lpDim = (l.map lpDim).sum := by
  induction l with
  | nil => exact lpDim_zero
  | cons x l ih =>
    change (x.lpSum (sumList l)).lpDim = x.lpDim + (l.map lpDim).sum
    rw [lpDim_sum, ih]

theorem charpoly_sumList (l : List (WD h)) (σ : Weil h) :
    (sumList l).charpoly σ = (l.map fun x => x.charpoly σ).prod := by
  induction l with
  | nil => exact charpoly_zero σ
  | cons x l ih =>
    change (x.lpSum (sumList l)).charpoly σ = x.charpoly σ * (l.map fun x => x.charpoly σ).prod
    rw [charpoly_sum, ih]

theorem detChar_sumList (l : List (WD h)) :
    (sumList l).detChar = (l.map detChar).prod := by
  induction l with
  | nil => exact detChar_zero
  | cons x l ih =>
    change (x.lpSum (sumList l)).detChar = x.detChar * (l.map detChar).prod
    rw [detChar_sum, ih]

/-- The product of the Weil eigenvalues is the determinant. -/
theorem detChar_eq_prod_roots (x : WD h) (σ : Weil h) :
    (x.detChar σ : ℂ) = (x.charpoly σ).roots.prod := by
  refine WD.ind (fun n a => ?_) x
  rw [detChar_mk, charpoly_mk]
  exact Module.End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _)

end GlobalTheory.WeilDeligne.WD

#print axioms GlobalTheory.WeilDeligne.WD.charpoly_sumList
#print axioms GlobalTheory.WeilDeligne.WD.detChar_eq_prod_roots
