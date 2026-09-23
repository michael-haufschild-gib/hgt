import GaloisForLFunctions.HTGeometry.TwoCylinderDifferential
import GaloisForLFunctions.HTGeometry.TwoCylinderTranslationAction

/-!
# The two-cylinder embedding is a differential embedding

The two cylinder coordinates `u₁ = exp(l₀ z)` and `u₂ = exp(l₁ z)` of an incommensurate period pair
generate a copy of `ℂ(u₁)(u₂)` inside the global meromorphic field.  Differentiation in `z` does not
fix the coefficient field `ℂ(u₁)`, so the derivation it induces on `ℂ(u₁)(u₂)` is the total
two-cylinder derivation: the coefficients move by the first cylinder's Euler operator and the
variable by its own.

The polynomial case is the total derivative of a polynomial value, and the general case follows by
differentiating `y · s = p`, where the nonvanishing of the embedded denominator cancels the common
factor.  This makes the two-cylinder field a differential subfield of the meromorphic field, which
is what the differential Ostrowski criterion needs as its base.
-/

open Filter Set Topology Polynomial
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance tmDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance tmComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring (Set.univ : Set ℂ)) := (constToAnalytic Set.univ).toAlgebra

local instance tmComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance tmDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

variable {l : Fin 2 → ℂ}

theorem twoCylinderEmbed_algebraMap_polynomial (hl : LinearIndependent ℚ l)
    (p : Polynomial (RatFunc ℂ)) :
    twoCylinderEmbed hl (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p)
      = Polynomial.eval₂ (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ]
            meroField (Set.univ : Set ℂ)).toRingHom (physicalExponentialMero (l 1)) p := by
  have hone : (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p)
      = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p /
        algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (1 : Polynomial (RatFunc ℂ)) := by
    rw [map_one]
    exact (div_one (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p)).symm
  rw [hone, twoCylinderEmbed_div, Polynomial.eval₂_one, div_one]

theorem twoCylinderEmbed_coeff (hl : LinearIndependent ℚ l) (c : RatFunc ℂ) :
    twoCylinderEmbed hl (algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) c)
      = cylinderEmbed hl 0 c := by
  rw [algebraMap_ratFunc_eq_polynomialC, twoCylinderEmbed_algebraMap_polynomial,
    Polynomial.eval₂_C]
  rfl

theorem twoCylinderEmbed_X (hl : LinearIndependent ℚ l) :
    twoCylinderEmbed hl (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) Polynomial.X)
      = physicalExponentialMero (l 1) := by
  rw [twoCylinderEmbed_algebraMap_polynomial, Polynomial.eval₂_X]


theorem coeffDeriv_map_cylinderEmbed (hl : LinearIndependent ℚ l) (p : Polynomial (RatFunc ℂ)) :
    letI := cylinderDifferential (l 0)
    coeffDeriv (p.map (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ]
        meroField (Set.univ : Set ℂ)).toRingHom)
      = (coeffDeriv p).map (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ]
          meroField (Set.univ : Set ℂ)).toRingHom := by
  letI := cylinderDifferential (l 0)
  refine Polynomial.ext fun n => ?_
  rw [coeffDeriv_coeff, Polynomial.coeff_map, Polynomial.coeff_map, coeffDeriv_coeff,
    cylinderDifferential_deriv]
  exact meroFieldDeriv_cylinderEmbed hl 0 _

/-- **The derivative of a polynomial in the second cylinder coordinate.** -/
theorem meroFieldDeriv_eval₂_twoCylinder (hl : LinearIndependent ℚ l)
    (p : Polynomial (RatFunc ℂ)) :
    letI := cylinderDifferential (l 0)
    (Polynomial.eval₂ (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ]
        meroField (Set.univ : Set ℂ)).toRingHom (physicalExponentialMero (l 1)) p)′
      = Polynomial.eval₂ (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ]
            meroField (Set.univ : Set ℂ)).toRingHom (physicalExponentialMero (l 1))
          (coeffDeriv p)
        + algebraMap ℂ (meroField (Set.univ : Set ℂ)) (l 1) * physicalExponentialMero (l 1)
          * Polynomial.eval₂ (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ]
              meroField (Set.univ : Set ℂ)).toRingHom (physicalExponentialMero (l 1))
              (Polynomial.derivative p) := by
  letI := cylinderDifferential (l 0)
  set iota : RatFunc ℂ →+* meroField (Set.univ : Set ℂ) :=
    (cylinderEmbed hl 0 : RatFunc ℂ →ₐ[ℂ] meroField (Set.univ : Set ℂ)).toRingHom with hiota
  set u2 : meroField (Set.univ : Set ℂ) := physicalExponentialMero (l 1) with hu2
  rw [← Polynomial.eval_map (f := iota), ← Polynomial.eval_map (f := iota),
    ← Polynomial.eval_map (f := iota), deriv_eval, coeffDeriv_map_cylinderEmbed hl,
    Polynomial.derivative_map, hu2, physicalExponentialMero_deriv]
  ring

theorem meroDeriv_leibniz (x y : meroField (Set.univ : Set ℂ)) :
    (x * y)′ = x * y′ + y * x′ := by
  letI : Algebra ℤ (meroField (Set.univ : Set ℂ)) := Ring.toIntAlgebra _
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]

theorem meroDeriv_div (a b : meroField (Set.univ : Set ℂ)) (hb : b ≠ 0) :
    (a / b)′ = (a′ * b - a * b′) / b ^ (2 : ℕ) :=
  leibniz_div (fun x : meroField (Set.univ : Set ℂ) => x′) meroDeriv_leibniz hb

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The two-cylinder embedding is a differential embedding.**  Differentiation in `z` corresponds
on `ℂ(u₁)(u₂)` to the two-cylinder derivation: the coefficient field moves by the first cylinder's
Euler operator and the second coordinate by its own. -/
theorem meroFieldDeriv_twoCylinderEmbed (hl : LinearIndependent ℚ l) (y : RatFunc (RatFunc ℂ)) :
    letI := cylinderDifferential (l 0)
    (twoCylinderEmbed hl y)′
      = twoCylinderEmbed hl (twoCylDerivation (algebraMap ℂ (RatFunc ℂ) (l 1)) y) := by
  letI := cylinderDifferential (l 0)
  set LAM : RatFunc ℂ := algebraMap ℂ (RatFunc ℂ) (l 1) with hLAM
  have hpoly : ∀ p : Polynomial (RatFunc ℂ),
      (twoCylinderEmbed hl (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p))′
        = twoCylinderEmbed hl (twoCylDerivation LAM
            (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p)) := by
    intro p
    rw [twoCylinderEmbed_algebraMap_polynomial, meroFieldDeriv_eval₂_twoCylinder,
      twoCylDerivation_algebraMap, map_add, map_mul, map_mul]
    simp only [twoCylinderEmbed_algebraMap_polynomial, twoCylinderEmbed_coeff,
      Polynomial.eval₂_X]
    rw [hLAM, show cylinderEmbed hl 0 (algebraMap ℂ (RatFunc ℂ) (l 1))
        = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (l 1) from (cylinderEmbed hl 0).commutes _]
  refine RatFunc.induction_on
    (P := fun y => (twoCylinderEmbed hl y)′
      = twoCylinderEmbed hl (twoCylDerivation LAM y)) y ?_
  intro p s hs
  set P : RatFunc (RatFunc ℂ) :=
    algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p with hP
  set S : RatFunc (RatFunc ℂ) :=
    algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) s with hS
  have hs1 : S ≠ 0 := RatFunc.algebraMap_ne_zero hs
  have hs0 : twoCylinderEmbed hl S ≠ 0 := fun h =>
    hs1 (twoCylinderEmbed_injective hl (by rw [h, map_zero]))
  have hyS : P / S * S = P := div_mul_cancel₀ P hs1
  have hDS : twoCylinderEmbed hl (twoCylDerivation LAM S) = (twoCylinderEmbed hl S)′ :=
    (hpoly s).symm
  have hDP : twoCylinderEmbed hl (twoCylDerivation LAM P) = (twoCylinderEmbed hl P)′ :=
    (hpoly p).symm
  have hDside : twoCylinderEmbed hl (P / S) * twoCylinderEmbed hl (twoCylDerivation LAM S)
      + twoCylinderEmbed hl S * twoCylinderEmbed hl (twoCylDerivation LAM (P / S))
      = twoCylinderEmbed hl (twoCylDerivation LAM P) := by
    have h := congrArg (twoCylDerivation LAM) hyS
    rw [twoCylDerivation_leibniz] at h
    have h2 := congrArg (twoCylinderEmbed hl) h
    rw [map_add, map_mul (twoCylinderEmbed hl), map_mul (twoCylinderEmbed hl)] at h2
    exact h2
  have hTside : twoCylinderEmbed hl (P / S) * (twoCylinderEmbed hl S)′
      + twoCylinderEmbed hl S * (twoCylinderEmbed hl (P / S))′
      = (twoCylinderEmbed hl P)′ := by
    have h := congrArg (twoCylinderEmbed hl) hyS
    rw [map_mul (twoCylinderEmbed hl)] at h
    have h2 : (twoCylinderEmbed hl (P / S) * twoCylinderEmbed hl S)′
        = (twoCylinderEmbed hl P)′ := by rw [h]
    rw [meroDeriv_leibniz] at h2
    exact h2
  refine mul_left_cancel₀ hs0 ?_
  rw [hDS, hDP] at hDside
  linear_combination hTside - hDside

end

end GaloisForLFunctions.HTGeometry
