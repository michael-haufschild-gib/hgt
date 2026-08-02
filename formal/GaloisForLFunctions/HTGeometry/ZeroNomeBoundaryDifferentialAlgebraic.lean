import GaloisForLFunctions.HTGeometry.LocalAnalyticExponentialClock
import GaloisForLFunctions.HTGeometry.RelativeTwoShiftGaugeCharacterization
import GaloisForLFunctions.HTGeometry.MeromorphicMultipleEllipticGamma
import GaloisForLFunctions.HTGeometry.DifferentialIndependence
import GaloisForLFunctions.HTGeometry.EllipticGammaParityDegeneration

/-!
# The zero-nome boundary is differentially algebraic

The boundary `1 - x` of the zero-nome degeneration satisfies the first-order relation
`y' = 2πi·y - 2πi`, and its inverse satisfies `u' = 2πi·u² - 2πi·u`.  Either relation is an
algebraic differential equation over the constants, so both are differentially algebraic.

This is the differential-algebra half of the flatness statement: the hypertranscendental fibres of
the reciprocal family cannot equal their boundary.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-- An element satisfying a quadratic first-order differential relation over the base is
differentially algebraic over it. -/
theorem differentialAlgebraicOver_of_deriv_quadratic {F K : Type*} [CommRing F] [Nontrivial F]
    [CommRing K] [Algebra F K] [Differential K] {y : K} {c₀ c₁ c₂ : F}
    (h : y′ = algebraMap F K c₂ * y ^ 2 + algebraMap F K c₁ * y + algebraMap F K c₀) :
    DifferentialAlgebraicOver F y := by
  classical
  intro hindep
  set Q : MvPolynomial (Unit × ℕ) F :=
    MvPolynomial.X ((), 1)
      - (MvPolynomial.C c₂ * MvPolynomial.X ((), 0) ^ 2
        + MvPolynomial.C c₁ * MvPolynomial.X ((), 0) + MvPolynomial.C c₀) with hQ
  have hval : (MvPolynomial.aeval fun p : Unit × ℕ => differentialJet p.2 y) Q = 0 := by
    rw [hQ]
    simp only [map_sub, map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    rw [differentialJet_zero, differentialJet_succ, differentialJet_zero, h]
    ring
  have hzero : Q = 0 := hindep (by rw [hval, map_zero])
  have hcoeff : Q.coeff (Finsupp.single ((), 1) 1) = 1 := by
    have hne : (Finsupp.single (((), 0) : Unit × ℕ) 1)
        ≠ (Finsupp.single (((), 1) : Unit × ℕ) 1) := by
      intro hEq
      have := congrArg (fun f => f ((), 1)) hEq
      simp at this
    have hne2 : (Finsupp.single (((), 0) : Unit × ℕ) 2)
        ≠ (Finsupp.single (((), 1) : Unit × ℕ) 1) := by
      intro hEq
      have := congrArg (fun f => f ((), 1)) hEq
      simp at this
    have hne0 : (0 : Unit × ℕ →₀ ℕ) ≠ (Finsupp.single (((), 1) : Unit × ℕ) 1) := by
      intro hEq
      have := congrArg (fun f => f ((), 1)) hEq
      simp at this
    have hpow : (MvPolynomial.X (((), 0) : Unit × ℕ) : MvPolynomial (Unit × ℕ) F) ^ 2
        = MvPolynomial.monomial (Finsupp.single (((), 0) : Unit × ℕ) 2) 1 := by
      rw [MvPolynomial.X_pow_eq_monomial]
    rw [hQ, hpow]
    simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, MvPolynomial.coeff_C,
      MvPolynomial.coeff_monomial, hne, hne0, hne2]
  rw [hzero, MvPolynomial.coeff_zero] at hcoeff
  exact zero_ne_one hcoeff

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

/-- The linear phase `2πi·z` is entire. -/
theorem phaseLinear : AnalyticOnNhd ℂ (fun z : ℂ => 2 * (Real.pi : ℂ) * Complex.I * z)
    (Set.univ : Set ℂ) := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact (differentiable_const _).mul differentiable_id

/-- The coordinate `x = exp(2πi z)`, as an analytic germ. -/
def coordinateAnalytic : analyticSubring (Set.univ : Set ℂ) :=
  analyticExponentialElement (fun z : ℂ => 2 * (Real.pi : ℂ) * Complex.I * z) phaseLinear

theorem analyticSubringDeriv_phaseLinear :
    analyticSubringDeriv (U := (Set.univ : Set ℂ)) isOpen_univ
        (analyticFunctionElement (fun z : ℂ => 2 * (Real.pi : ℂ) * Complex.I * z) phaseLinear)
      = constToAnalytic Set.univ (2 * (Real.pi : ℂ) * Complex.I) := by
  apply Subtype.ext
  change ((deriv (fun z : ℂ => 2 * (Real.pi : ℂ) * Complex.I * z) : ℂ → ℂ)
      : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
    = ((fun _ : ℂ => 2 * (Real.pi : ℂ) * Complex.I : ℂ → ℂ) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
  rw [Germ.coe_eq]
  refine eventually_principal.mpr fun z _ => ?_
  simp

theorem analyticSubringDeriv_coordinateAnalytic :
    analyticSubringDeriv (U := (Set.univ : Set ℂ)) isOpen_univ coordinateAnalytic
      = constToAnalytic Set.univ (2 * (Real.pi : ℂ) * Complex.I) * coordinateAnalytic := by
  rw [coordinateAnalytic, analyticSubringDeriv_analyticExponentialElement,
    analyticSubringDeriv_phaseLinear]
  ring

/-- The zero-nome boundary `1 - x`, as an analytic germ. -/
def zeroNomeAnalytic : analyticSubring (Set.univ : Set ℂ) := 1 - coordinateAnalytic

theorem analyticSubringDeriv_zeroNomeAnalytic :
    analyticSubringDeriv (U := (Set.univ : Set ℂ)) isOpen_univ zeroNomeAnalytic
      = constToAnalytic Set.univ (2 * (Real.pi : ℂ) * Complex.I) * zeroNomeAnalytic
        - constToAnalytic Set.univ (2 * (Real.pi : ℂ) * Complex.I) := by
  have hone : analyticSubringDeriv (U := (Set.univ : Set ℂ)) isOpen_univ 1 = 0 := by
    have h := analyticSubringDeriv_constToAnalytic 1
    rwa [map_one] at h
  have hsum : zeroNomeAnalytic + coordinateAnalytic = 1 := by
    rw [zeroNomeAnalytic]
    ring
  have hD := congrArg (analyticSubringDeriv (U := (Set.univ : Set ℂ)) isOpen_univ) hsum
  rw [analyticSubringDeriv_add, hone] at hD
  have hneg : analyticSubringDeriv (U := (Set.univ : Set ℂ)) isOpen_univ zeroNomeAnalytic
      = -analyticSubringDeriv (U := (Set.univ : Set ℂ)) isOpen_univ coordinateAnalytic :=
    eq_neg_of_add_eq_zero_left hD
  have hcoord : coordinateAnalytic = 1 - zeroNomeAnalytic := by
    rw [zeroNomeAnalytic]
    ring
  rw [hneg, analyticSubringDeriv_coordinateAnalytic, hcoord]
  ring

/-- The zero-nome boundary in the meromorphic differential field. -/
def zeroNomeMero : meroField (Set.univ : Set ℂ) :=
  algebraMap (analyticSubring Set.univ) (meroField Set.univ) zeroNomeAnalytic

/-- **The zero-nome boundary satisfies a first-order algebraic differential equation.** -/
theorem deriv_zeroNomeMero :
    (zeroNomeMero)′
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (2 * (Real.pi : ℂ) * Complex.I) * zeroNomeMero
        - algebraMap ℂ (meroField (Set.univ : Set ℂ)) (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [zeroNomeMero, meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ
    Set.univ_nonempty, analyticSubringDeriv_zeroNomeAnalytic, map_sub, map_mul]
  rfl

/-- **The zero-nome boundary is differentially algebraic.** -/
theorem differentialAlgebraicOver_zeroNomeMero :
    DifferentialAlgebraicOver ℂ zeroNomeMero := by
  refine differentialAlgebraicOver_of_deriv_quadratic
    (c₂ := 0) (c₁ := 2 * (Real.pi : ℂ) * Complex.I)
    (c₀ := -(2 * (Real.pi : ℂ) * Complex.I)) ?_
  rw [deriv_zeroNomeMero, map_zero, map_neg]
  ring

end

end GaloisForLFunctions.HTGeometry
