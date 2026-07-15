import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Injective diagonal scaling over an integral domain

Coordinatewise substitution `Xᵢ ↦ cᵢ Xᵢ` is injective whenever every `cᵢ` is nonzero and the
coefficient ring is an integral domain.  The proof embeds the coefficient ring in its fraction
field, where reciprocal scaling is an explicit inverse.  The domain-level form is needed when the
scales are themselves nonconstant polynomials.
-/

namespace GaloisForLFunctions

noncomputable section

def mvPolynomialDiagonalScaleRing {R : Type*} [CommRing R] {σ : Type*}
    (c : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.bind₁ (fun i => MvPolynomial.C (c i) * MvPolynomial.X i)

theorem mvPolynomialDiagonalScaleRing_inv_apply
    {K : Type*} [Field K] {σ : Type*}
    (c : σ → K) (hc : ∀ i, c i ≠ 0) (P : MvPolynomial σ K) :
    mvPolynomialDiagonalScaleRing (fun i => (c i)⁻¹)
      (mvPolynomialDiagonalScaleRing c P) = P := by
  rw [mvPolynomialDiagonalScaleRing, mvPolynomialDiagonalScaleRing,
    MvPolynomial.bind₁_bind₁]
  have hg : (fun i => MvPolynomial.bind₁
      (fun j => MvPolynomial.C ((c j)⁻¹) * MvPolynomial.X j)
      (MvPolynomial.C (c i) * MvPolynomial.X i)) = MvPolynomial.X := by
    funext i
    simp only [map_mul, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_X_right]
    rw [← mul_assoc, ← MvPolynomial.C_mul]
    simp [hc i]
  rw [hg, MvPolynomial.bind₁_X_left]
  rfl

theorem mvPolynomialDiagonalScaleRing_ne_zero_field
    {K : Type*} [Field K] {σ : Type*}
    (c : σ → K) (hc : ∀ i, c i ≠ 0)
    {P : MvPolynomial σ K} (hP : P ≠ 0) :
    mvPolynomialDiagonalScaleRing c P ≠ 0 := by
  intro h
  have hzero := congrArg (mvPolynomialDiagonalScaleRing (fun i => (c i)⁻¹)) h
  rw [mvPolynomialDiagonalScaleRing_inv_apply c hc P] at hzero
  simp at hzero
  exact hP hzero

theorem map_mvPolynomialDiagonalScaleRing
    {R S : Type*} [CommRing R] [CommRing S] {σ : Type*}
    (f : R →+* S) (c : σ → R) (P : MvPolynomial σ R) :
    MvPolynomial.map f (mvPolynomialDiagonalScaleRing c P) =
      mvPolynomialDiagonalScaleRing (fun i => f (c i)) (MvPolynomial.map f P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [mvPolynomialDiagonalScaleRing]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, MvPolynomial.map_X, mvPolynomialDiagonalScaleRing,
        MvPolynomial.bind₁_X_right, MvPolynomial.map_C]
      change (MvPolynomial.map f) (mvPolynomialDiagonalScaleRing c P) *
          (MvPolynomial.C (f (c i)) * MvPolynomial.X i) =
        mvPolynomialDiagonalScaleRing (fun i => f (c i)) (MvPolynomial.map f P) *
          (MvPolynomial.C (f (c i)) * MvPolynomial.X i)
      rw [hP]

/-- Diagonal scaling by nonzero elements of an integral domain preserves nonzero polynomials. -/
theorem mvPolynomialDiagonalScaleRing_ne_zero
    {R : Type*} [CommRing R] [IsDomain R] {σ : Type*}
    (c : σ → R) (hc : ∀ i, c i ≠ 0)
    {P : MvPolynomial σ R} (hP : P ≠ 0) :
    mvPolynomialDiagonalScaleRing c P ≠ 0 := by
  let f : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective R (FractionRing R)
  have hmapP : MvPolynomial.map f P ≠ 0 := by
    intro h
    apply hP
    apply MvPolynomial.map_injective f hf
    simpa using h
  have hc' : ∀ i, f (c i) ≠ 0 := by
    intro i h
    exact hc i (hf (by simpa using h))
  intro hzero
  have hmap := congrArg (MvPolynomial.map f) hzero
  rw [map_mvPolynomialDiagonalScaleRing] at hmap
  have hscaled := mvPolynomialDiagonalScaleRing_ne_zero_field
    (fun i => f (c i)) hc' hmapP
  exact hscaled (by simpa using hmap)

end

end GaloisForLFunctions
