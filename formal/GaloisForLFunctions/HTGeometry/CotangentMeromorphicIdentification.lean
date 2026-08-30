import GaloisForLFunctions.HTGeometry.IncommensuratePeriodMeromorphicModel
import GaloisForLFunctions.HTGeometry.CylinderCoordinateEulerBridge

/-!
# The embedded cotangent model is the genuine meromorphic cotangent

The increments of the double-sine functional equations are the cotangent terms
`a_j(z) = (π/ω_j) cot(π z/ω_j)`, which are the logarithmic derivatives of the order-one multiple
sines `2 sin(π z/ω_j)`.  On the cylinder coordinate `u = exp(2πi z/ω_j)` they are the values of the
rational model `cotModel` against which the orbit-balance obstruction is proved.

This module makes that identification exact inside the global meromorphic field.  The cotangent is
built as a genuine meromorphic germ `cotMero a = cos(a z)/sin(a z)`, and

```text
cylinderEmbed_cotModel :        ι (i (X+1)/(X-1))            = cot (a z),
cylinderEmbed_cotModel_period : ι ((iπ/ω) (X+1)/(X-1))       = (π/ω) cot(π z/ω),
```

where `ι` is the cylinder embedding with coordinate `exp(2 i a z)`.  The proof cross-multiplies to
an identity of entire germs and evaluates pointwise, where it is the exponential identity
`i (e^{2iw}+1) sin w = cos w (e^{2iw}-1)`.

Consequently the increment appearing in the double-sine step equation is literally the embedded
`cotModel`, so the character obstruction, the Euler-operator jets and the orbit-balance argument all
apply to the genuine meromorphic cotangent rather than to a formal stand-in.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance cotDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance cotComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring (Set.univ : Set ℂ)) := (constToAnalytic Set.univ).toAlgebra

local instance cotComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

theorem analyticOnNhd_sin_linear (a : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => Complex.sin (a * z)) Set.univ := by
  have h : (fun z : ℂ => Complex.sin (a * z))
      = fun z : ℂ => (Complex.exp (-(a * z) * Complex.I) - Complex.exp (a * z * Complex.I))
          * (Complex.I / 2) := by
    funext z
    rw [Complex.sin, mul_div_assoc]
  rw [h]
  exact (((analyticOnNhd_const.mul analyticOnNhd_id).neg.mul analyticOnNhd_const).cexp.sub
    ((analyticOnNhd_const.mul analyticOnNhd_id).mul analyticOnNhd_const).cexp).mul
    analyticOnNhd_const

theorem analyticOnNhd_cos_linear (a : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => Complex.cos (a * z)) Set.univ := by
  have h : (fun z : ℂ => Complex.cos (a * z))
      = fun z : ℂ => (Complex.exp (a * z * Complex.I) + Complex.exp (-(a * z) * Complex.I))
          * (1 / 2 : ℂ) := by
    funext z
    rw [Complex.cos, mul_one_div]
  rw [h]
  exact ((((analyticOnNhd_const.mul analyticOnNhd_id).mul analyticOnNhd_const).cexp).add
    (((analyticOnNhd_const.mul analyticOnNhd_id).neg.mul analyticOnNhd_const).cexp)).mul
    analyticOnNhd_const

/-- `z ↦ sin (a z)` as a global analytic germ. -/
def sinAnalytic (a : ℂ) : analyticSubring (Set.univ : Set ℂ) :=
  univAnalytic (fun z : ℂ => Complex.sin (a * z)) (analyticOnNhd_sin_linear a)

/-- `z ↦ cos (a z)` as a global analytic germ. -/
def cosAnalytic (a : ℂ) : analyticSubring (Set.univ : Set ℂ) :=
  univAnalytic (fun z : ℂ => Complex.cos (a * z)) (analyticOnNhd_cos_linear a)

@[simp] theorem analyticEvalAtUniv_sinAnalytic (z a : ℂ) :
    analyticEvalAtUniv z (sinAnalytic a) = Complex.sin (a * z) := rfl

@[simp] theorem analyticEvalAtUniv_cosAnalytic (z a : ℂ) :
    analyticEvalAtUniv z (cosAnalytic a) = Complex.cos (a * z) := rfl

/-- The meromorphic cotangent `z ↦ cot (a z)`. -/
def cotMero (a : ℂ) : meroField (Set.univ : Set ℂ) :=
  algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) (cosAnalytic a) /
    algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) (sinAnalytic a)

theorem sinAnalytic_ne_zero {a : ℂ} (ha : a ≠ 0) : sinAnalytic a ≠ 0 := by
  intro hzero
  have hval := congrArg (analyticEvalAtUniv ((Real.pi : ℂ) / (2 * a))) hzero
  rw [analyticEvalAtUniv_sinAnalytic, map_zero] at hval
  rw [show a * ((Real.pi : ℂ) / (2 * a)) = (Real.pi : ℂ) / 2 by field_simp] at hval
  simp at hval

theorem physicalExponentialMero_sub_one_ne_zero {a : ℂ} (ha : a ≠ 0) :
    physicalExponentialMero (2 * Complex.I * a) - 1 ≠ 0 := by
  intro hzero
  have hA : physicalExponentialAnalytic (2 * Complex.I * a) - 1 = 0 := by
    apply IsFractionRing.injective (analyticSubring (Set.univ : Set ℂ))
      (meroField (Set.univ : Set ℂ))
    rw [map_sub, map_one, map_zero]
    exact hzero
  have hval := congrArg (analyticEvalAtUniv ((Real.pi : ℂ) / (2 * a))) hA
  rw [map_sub, map_one, map_zero, analyticEvalAtUniv_physicalExponentialAnalytic] at hval
  rw [show 2 * Complex.I * a * ((Real.pi : ℂ) / (2 * a)) = (Real.pi : ℂ) * Complex.I by
    field_simp] at hval
  rw [Complex.exp_pi_mul_I] at hval
  norm_num at hval

theorem physicalExponentialMero_def (lam : ℂ) :
    physicalExponentialMero lam = algebraMap (analyticSubring (Set.univ : Set ℂ))
      (meroField Set.univ) (physicalExponentialAnalytic lam) := rfl

/-- The pointwise cotangent identity in the cylinder coordinate. -/
theorem cot_cylinder_pointwise (a z : ℂ) :
    Complex.I * (Complex.exp (2 * Complex.I * a * z) + 1) * Complex.sin (a * z)
      = Complex.cos (a * z) * (Complex.exp (2 * Complex.I * a * z) - 1) := by
  have hp : Complex.exp (2 * Complex.I * a * z) = Complex.exp (a * z * Complex.I) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    exact congrArg Complex.exp (by push_cast; ring)
  have hneg : Complex.exp (-(a * z) * Complex.I) = (Complex.exp (a * z * Complex.I))⁻¹ := by
    rw [← Complex.exp_neg]
    exact congrArg Complex.exp (by ring)
  have hne : Complex.exp (a * z * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  rw [Complex.sin, Complex.cos, hneg, hp]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The embedded cotangent model is the genuine meromorphic cotangent.**  Under the cylinder
embedding with coordinate `u = exp(2 i a z)`, the rational model `i (X+1)/(X-1)` is the
meromorphic function `cot (a z)`. -/
theorem cylinderEmbed_cotModel {l : Fin 2 → ℂ} (hl : LinearIndependent ℚ l) (j : Fin 2)
    {a : ℂ} (ha : a ≠ 0) (hlj : l j = 2 * Complex.I * a) :
    cylinderEmbed hl j (cotModel Complex.I) = cotMero a := by
  have hu : physicalExponentialMero (l j) = physicalExponentialMero (2 * Complex.I * a) := by
    rw [hlj]
  have hden : physicalExponentialMero (l j) - 1 ≠ 0 := by
    rw [hu]
    exact physicalExponentialMero_sub_one_ne_zero ha
  have hsin : algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (sinAnalytic a) ≠ 0 := by
    intro hzero
    exact sinAnalytic_ne_zero ha (IsFractionRing.injective
      (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
      (by simpa using hzero))
  have hnum : cylinderEmbed hl j (cotModel Complex.I)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) Complex.I
          * (physicalExponentialMero (l j) + 1) / (physicalExponentialMero (l j) - 1) := by
    rw [cotModel, map_div₀, cylinderEmbed_polynomial, cylinderEmbed_polynomial]
    simp only [map_mul, Polynomial.aeval_C, map_add, Polynomial.aeval_X,
      linFac, map_sub, map_one]
  rw [hnum, cotMero, div_eq_div_iff hden hsin]
  have hgerm : (constToAnalytic Set.univ Complex.I
        * (physicalExponentialAnalytic (l j) + 1) * sinAnalytic a)
      = cosAnalytic a * (physicalExponentialAnalytic (l j) - 1) := by
    refine analyticSubring_ext fun z => ?_
    simp only [map_mul, map_add, map_sub, map_one, analyticEvalAtUniv_physicalExponentialAnalytic,
      analyticEvalAtUniv_sinAnalytic, analyticEvalAtUniv_cosAnalytic]
    rw [show analyticEvalAtUniv z (constToAnalytic Set.univ Complex.I) = Complex.I from rfl, hlj]
    exact cot_cylinder_pointwise a z
  have hmap := congrArg (algebraMap (analyticSubring (Set.univ : Set ℂ))
    (meroField (Set.univ : Set ℂ))) hgerm
  simp only [map_mul, map_add, map_sub, map_one] at hmap
  rw [show algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (constToAnalytic Set.univ Complex.I)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) Complex.I from rfl] at hmap
  simp only [← physicalExponentialMero_def] at hmap
  linear_combination hmap

theorem cotModel_mul_left {K : Type*} [Field K] (c d : K) :
    cotModel (c * d) = algebraMap K (RatFunc K) c * cotModel d := by
  rw [cotModel, cotModel, algebraMap_ratFunc_eq_polynomialC, ← mul_div_assoc, ← map_mul]
  congr 2
  rw [Polynomial.C_mul]
  ring

/-- **The card's cotangent increment is the embedded cotangent model.**  With the cylinder
coordinate `u = exp(2πi z/ω)`, the rational model `(iπ/ω)(X+1)/(X-1)` is the meromorphic function
`(π/ω) cot(π z/ω)` — the logarithmic derivative of the order-one multiple sine `2 sin(π z/ω)`. -/
theorem cylinderEmbed_cotModel_period {l : Fin 2 → ℂ} (hl : LinearIndependent ℚ l) (j : Fin 2)
    {ω : ℂ} (hω : ω ≠ 0) (hlj : l j = 2 * (Real.pi : ℂ) * Complex.I / ω) :
    cylinderEmbed hl j (cotModel ((Real.pi : ℂ) / ω * Complex.I))
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) ((Real.pi : ℂ) / ω)
        * cotMero ((Real.pi : ℂ) / ω) := by
  have hpi : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ha : ((Real.pi : ℂ) / ω) ≠ 0 := div_ne_zero hpi hω
  have hlj' : l j = 2 * Complex.I * ((Real.pi : ℂ) / ω) := by
    rw [hlj]
    field_simp
  rw [cotModel_mul_left, map_mul, cylinderEmbed_cotModel hl j ha hlj', AlgHom.commutes]

end

end GaloisForLFunctions.HTGeometry
