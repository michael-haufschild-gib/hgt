import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialEvaluation
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Hasse detection for multivariable polynomial systems

For a fixed global point, every multivariable polynomial equation holds globally exactly when it
holds after scalar extension to every completion. This is a local--global detection statement for
global points of affine polynomial systems, not a descent theorem for independently chosen local
points.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u w

/-- Evaluation of a multivariable polynomial at a specified number-field point vanishes exactly
when its scalar-extended evaluation vanishes at every completion. -/
theorem numberFieldMvPolynomial_eval_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {σ : Type w}
    (p : MvPolynomial σ K) (x : σ → K) :
    MvPolynomial.eval x p = 0 ↔ ∀ v : NumberFieldPlace K,
      MvPolynomial.eval (fun i => placeEmbedding K v (x i)) (p.map (placeEmbedding K v)) = 0 := by
  constructor
  · intro h v
    change MvPolynomial.eval ((placeEmbedding K v) ∘ x) (p.map (placeEmbedding K v)) = 0
    rw [← MvPolynomial.map_eval, h, map_zero]
  · intro h
    apply (placeEmbedding K (witnessPlace K)).injective
    simp only [map_zero]
    rw [MvPolynomial.map_eval]
    exact h (witnessPlace K)

/-- Evaluation of a multivariable polynomial at a specified point of `F(t)` vanishes exactly
when its scalar-extended evaluation vanishes at every completion. -/
theorem rationalFunctionMvPolynomial_eval_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] {σ : Type w}
    (p : MvPolynomial σ (RatFunc F)) (x : σ → RatFunc F) :
    MvPolynomial.eval x p = 0 ↔ ∀ v : RationalFunctionPlace F,
      MvPolynomial.eval (fun i => rationalFunctionPlaceEmbedding F v (x i))
        (p.map (rationalFunctionPlaceEmbedding F v)) = 0 := by
  constructor
  · intro h v
    change MvPolynomial.eval ((rationalFunctionPlaceEmbedding F v) ∘ x)
      (p.map (rationalFunctionPlaceEmbedding F v)) = 0
    rw [← MvPolynomial.map_eval, h, map_zero]
  · intro h
    apply (rationalFunctionPlaceEmbedding F .infinite).injective
    simp only [map_zero]
    rw [MvPolynomial.map_eval]
    exact h .infinite

/-- A specified number-field point solves an arbitrary system of multivariable polynomial
equations exactly when its image solves every scalar-extended equation at every completion. -/
theorem numberFieldMvPolynomialSystem_eval_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {σ : Type w} {ι : Type*}
    (P : ι → MvPolynomial σ K) (x : σ → K) :
    (∀ i, MvPolynomial.eval x (P i) = 0) ↔ ∀ v : NumberFieldPlace K, ∀ i,
      MvPolynomial.eval (fun j => placeEmbedding K v (x j))
        (MvPolynomial.map (placeEmbedding K v) (P i)) = 0 := by
  constructor
  · intro h v i
    exact (numberFieldMvPolynomial_eval_eq_zero_iff_forall_place K (P i) x).mp (h i) v
  · intro h i
    exact (numberFieldMvPolynomial_eval_eq_zero_iff_forall_place K (P i) x).mpr (fun v => h v i)

/-- A specified point of `F(t)` solves an arbitrary system of multivariable polynomial equations
exactly when its image solves every scalar-extended equation at every completion. -/
theorem rationalFunctionMvPolynomialSystem_eval_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] {σ : Type w} {ι : Type*}
    (P : ι → MvPolynomial σ (RatFunc F)) (x : σ → RatFunc F) :
    (∀ i, MvPolynomial.eval x (P i) = 0) ↔ ∀ v : RationalFunctionPlace F, ∀ i,
      MvPolynomial.eval (fun j => rationalFunctionPlaceEmbedding F v (x j))
        (MvPolynomial.map (rationalFunctionPlaceEmbedding F v) (P i)) = 0 := by
  constructor
  · intro h v i
    exact (rationalFunctionMvPolynomial_eval_eq_zero_iff_forall_place F (P i) x).mp (h i) v
  · intro h i
    exact (rationalFunctionMvPolynomial_eval_eq_zero_iff_forall_place F (P i) x).mpr
      (fun v => h v i)

end GaloisForLFunctions.HTGeometry.ABHN
