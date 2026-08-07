import GaloisForLFunctions.HTGeometry.LaurentCriticalFibreIntegrality
import GaloisForLFunctions.HTGeometry.ShiftedVariablesIndependent

/-!
# Algebraic independence along a common formal scale

Multiplying an independent constant family by one formal variable preserves independence over the
smaller base field.  The key point is elementary: the scaled family first lives in a polynomial
ring, where evaluation of the formal variable at `1` recovers the original family.  Injective
embeddings then carry independence to power series and Laurent series.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped LaurentSeries

/-- Evaluation at `1`, viewed over a smaller coefficient field. -/
noncomputable def polynomialEvalOneAlgHom
    (K E : Type*) [Field K] [Field E] [Algebra K E] : E[X] →ₐ[K] E where
  toRingHom := Polynomial.evalRingHom 1
  commutes' k := by simp

/-- Polynomial inclusion into power series, viewed over a smaller coefficient field. -/
noncomputable def polynomialToPowerSeriesAlgHom
    (K E : Type*) [Field K] [Field E] [Algebra K E] : E[X] →ₐ[K] PowerSeries E where
  toRingHom := Polynomial.coeToPowerSeries.ringHom
  commutes' k := by simp [PowerSeries.algebraMap_apply]

theorem polynomialToPowerSeriesAlgHom_injective
    (K E : Type*) [Field K] [Field E] [Algebra K E] :
    Function.Injective (polynomialToPowerSeriesAlgHom K E) := by
  intro p q hpq
  apply Polynomial.ext
  intro k
  have h := congrArg (PowerSeries.coeff k) hpq
  simpa [polynomialToPowerSeriesAlgHom] using h

/-- Power-series inclusion into Laurent series, over the smaller base field. -/
noncomputable def powerSeriesToLaurentAlgHom
    (K E : Type*) [Field K] [Field E] [Algebra K E] : PowerSeries E →ₐ[K] E⸨X⸩ where
  toRingHom := algebraMap (PowerSeries E) E⸨X⸩
  commutes' _ := rfl

theorem powerSeriesToLaurentAlgHom_injective
    (K E : Type*) [Field K] [Field E] [Algebra K E] :
    Function.Injective (powerSeriesToLaurentAlgHom K E) :=
  powerSeriesToLaurent_injective E

/-- Common multiplication by the polynomial variable preserves independence. -/
theorem algebraicIndependent_polynomial_commonScale
    {K E I : Type*} [Field K] [Field E] [Algebra K E]
    {x : I → E} (hx : AlgebraicIndependent K x) :
    AlgebraicIndependent K (fun i => (X : E[X]) * C (x i)) := by
  apply AlgebraicIndependent.of_comp (polynomialEvalOneAlgHom K E)
  simpa [Function.comp_def, polynomialEvalOneAlgHom] using hx

/-- Common multiplication by `T` preserves independence in `E[[T]]`. -/
theorem algebraicIndependent_powerSeriesDeformParam
    {K E I : Type*} [Field K] [Field E] [Algebra K E]
    {x : I → E} (hx : AlgebraicIndependent K x) :
    AlgebraicIndependent K (fun i => powerSeriesDeformParam (x i)) := by
  have hpoly := algebraicIndependent_polynomial_commonScale hx
  have hmap := hpoly.map'
    (polynomialToPowerSeriesAlgHom_injective K E)
  have hfun :
      (polynomialToPowerSeriesAlgHom K E) ∘ (fun i => (X : E[X]) * C (x i)) =
        fun i => powerSeriesDeformParam (x i) := by
    funext i
    change (((X : E[X]) * C (x i) : E[X]) : PowerSeries E) =
      PowerSeries.X * PowerSeries.C (x i)
    simpa using (mul_comm (PowerSeries.C (x i)) PowerSeries.X)
  rw [← hfun]
  exact hmap

/-- Common multiplication by `T` preserves independence in `E((T))`. -/
theorem algebraicIndependent_laurentDeformParam
    {K E I : Type*} [Field K] [Field E] [Algebra K E]
    {x : I → E} (hx : AlgebraicIndependent K x) :
    AlgebraicIndependent K
      (fun i => algebraMap (PowerSeries E) E⸨X⸩ (powerSeriesDeformParam (x i))) := by
  have hpower := algebraicIndependent_powerSeriesDeformParam hx
  have hmap := hpower.map' (powerSeriesToLaurentAlgHom_injective K E)
  change AlgebraicIndependent K
    (fun i => powerSeriesToLaurentAlgHom K E (powerSeriesDeformParam (x i)))
  exact hmap

/-- Constant family joining raw and reciprocal deformation directions. -/
def criticalDirectionConstants
    {E : Type*} {m n : ℕ} (u : Fin n → E) (v : Fin m → E) : Fin n ⊕ Fin m → E :=
  Sum.elim u v

/-- Affine shift contributed by the two leading monomials. -/
def criticalObservationShift
    (K : Type*) [Field K] {m n : ℕ} : Fin n ⊕ Fin m → K
  | Sum.inl i => if (i : ℕ) = 0 then 1 else 0
  | Sum.inr j => if (j : ℕ) = 0 then 1 else 0

/-- Critical observation coordinates on the power-series generic direction. -/
noncomputable def powerSeriesCriticalObservation
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    {m n : ℕ} (u : Fin n → E) (v : Fin m → E) :
    Fin n ⊕ Fin m → PowerSeries E := fun i =>
  powerSeriesDeformParam (criticalDirectionConstants u v i) +
    algebraMap K (PowerSeries E) (criticalObservationShift K i)

/-- Critical observation coordinates on the Laurent generic direction. -/
noncomputable def laurentCriticalObservation
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    {m n : ℕ} (u : Fin n → E) (v : Fin m → E) :
    Fin n ⊕ Fin m → E⸨X⸩ := fun i =>
  algebraMap (PowerSeries E) E⸨X⸩ (powerSeriesCriticalObservation K E u v i)

theorem algebraicIndependent_powerSeriesCriticalObservation
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    {m n : ℕ} {u : Fin n → E} {v : Fin m → E}
    (h : AlgebraicIndependent K (criticalDirectionConstants u v)) :
    AlgebraicIndependent K (powerSeriesCriticalObservation K E u v) := by
  exact algebraicIndependent_add_const
    (algebraicIndependent_powerSeriesDeformParam h) (criticalObservationShift K)

theorem algebraicIndependent_laurentCriticalObservation
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    {m n : ℕ} {u : Fin n → E} {v : Fin m → E}
    (h : AlgebraicIndependent K (criticalDirectionConstants u v)) :
    AlgebraicIndependent K (laurentCriticalObservation K E u v) := by
  have hpower := algebraicIndependent_powerSeriesCriticalObservation h
  have hmap := hpower.map' (powerSeriesToLaurentAlgHom_injective K E)
  change AlgebraicIndependent K
    (fun i => powerSeriesToLaurentAlgHom K E (powerSeriesCriticalObservation K E u v i))
  exact hmap

end GaloisForLFunctions.HTGeometry
