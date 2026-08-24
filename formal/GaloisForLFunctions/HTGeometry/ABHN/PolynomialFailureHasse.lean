import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialEvaluation
import GaloisForLFunctions.HTGeometry.ABHN.HasseMvPolynomialEvaluation
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialIdentity

/-!
# Polynomial failures at every completion

Injective place embeddings reflect polynomial values and polynomial identities.  A fixed point
which fails an equation or system globally fails it at every completion, and a nonzero polynomial
remains nonzero after every completed coefficient extension.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u w

/-- Nonvanishing of a polynomial at a fixed number-field point persists everywhere. -/
theorem numberFieldPolynomial_eval_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (p : Polynomial K) (x : K) :
    p.eval x ≠ 0 ↔ ∀ v : NumberFieldPlace K,
      (p.map (placeEmbedding K v)).eval (placeEmbedding K v x) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (numberFieldPolynomial_eval_eq_zero_iff_exists_place K p x)

/-- Nonvanishing of a polynomial at a fixed `F(t)`-point persists everywhere. -/
theorem rationalFunctionPolynomial_eval_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (p : Polynomial (RatFunc F)) (x : RatFunc F) :
    p.eval x ≠ 0 ↔ ∀ v : RationalFunctionPlace F,
      (p.map (rationalFunctionPlaceEmbedding F v)).eval
        (rationalFunctionPlaceEmbedding F v x) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionPolynomial_eval_eq_zero_iff_exists_place F p x)

/-- Failure of a multivariable equation at a number-field point persists everywhere. -/
theorem numberFieldMvPolynomial_eval_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {σ : Type w}
    (p : MvPolynomial σ K) (x : σ → K) :
    MvPolynomial.eval x p ≠ 0 ↔ ∀ v : NumberFieldPlace K,
      MvPolynomial.eval (fun i => placeEmbedding K v (x i))
        (p.map (placeEmbedding K v)) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMvPolynomial_eval_eq_zero_iff_exists_place K p x)

/-- Failure of a multivariable equation at an `F(t)`-point persists everywhere. -/
theorem rationalFunctionMvPolynomial_eval_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] {σ : Type w}
    (p : MvPolynomial σ (RatFunc F)) (x : σ → RatFunc F) :
    MvPolynomial.eval x p ≠ 0 ↔ ∀ v : RationalFunctionPlace F,
      MvPolynomial.eval (fun i => rationalFunctionPlaceEmbedding F v (x i))
        (p.map (rationalFunctionPlaceEmbedding F v)) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMvPolynomial_eval_eq_zero_iff_exists_place F p x)

/-- Failure of a fixed number-field point to solve a polynomial system persists everywhere. -/
theorem numberFieldMvPolynomialSystem_not_eval_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {σ : Type w} {ι : Type*}
    (P : ι → MvPolynomial σ K) (x : σ → K) :
    ¬ (∀ i, MvPolynomial.eval x (P i) = 0) ↔ ∀ v : NumberFieldPlace K,
      ¬ (∀ i, MvPolynomial.eval (fun j => placeEmbedding K v (x j))
        (MvPolynomial.map (placeEmbedding K v) (P i)) = 0) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMvPolynomialSystem_eval_eq_zero_iff_exists_place K P x)

/-- Failure of a fixed `F(t)`-point to solve a polynomial system persists everywhere. -/
theorem rationalFunctionMvPolynomialSystem_not_eval_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] {σ : Type w} {ι : Type*}
    (P : ι → MvPolynomial σ (RatFunc F)) (x : σ → RatFunc F) :
    ¬ (∀ i, MvPolynomial.eval x (P i) = 0) ↔ ∀ v : RationalFunctionPlace F,
      ¬ (∀ i, MvPolynomial.eval (fun j => rationalFunctionPlaceEmbedding F v (x j))
        (MvPolynomial.map (rationalFunctionPlaceEmbedding F v) (P i)) = 0) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMvPolynomialSystem_eval_eq_zero_iff_exists_place F P x)

/-- A nonzero number-field polynomial remains nonzero at every completion. -/
theorem numberFieldPolynomial_map_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (p : Polynomial K) :
    p ≠ 0 ↔ ∀ v : NumberFieldPlace K, p.map (placeEmbedding K v) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (numberFieldPolynomial_map_eq_zero_iff_exists_place K p)

/-- A nonzero number-field multivariable polynomial remains nonzero at every completion. -/
theorem numberFieldMvPolynomial_map_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {σ : Type w} (p : MvPolynomial σ K) :
    p ≠ 0 ↔ ∀ v : NumberFieldPlace K,
      MvPolynomial.map (placeEmbedding K v) p ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (numberFieldMvPolynomial_map_eq_zero_iff_exists_place K p)

/-- A nonzero `F(t)`-polynomial remains nonzero at every completion. -/
theorem rationalFunctionPolynomial_map_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (p : Polynomial (RatFunc F)) :
    p ≠ 0 ↔ ∀ v : RationalFunctionPlace F,
      p.map (rationalFunctionPlaceEmbedding F v) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionPolynomial_map_eq_zero_iff_exists_place F p)

/-- A nonzero `F(t)`-multivariable polynomial remains nonzero at every completion. -/
theorem rationalFunctionMvPolynomial_map_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] {σ : Type w}
    (p : MvPolynomial σ (RatFunc F)) :
    p ≠ 0 ↔ ∀ v : RationalFunctionPlace F,
      MvPolynomial.map (rationalFunctionPlaceEmbedding F v) p ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionMvPolynomial_map_eq_zero_iff_exists_place F p)

end GaloisForLFunctions.HTGeometry.ABHN
