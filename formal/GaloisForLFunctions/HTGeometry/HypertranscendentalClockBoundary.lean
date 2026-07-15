import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import GaloisForLFunctions.HTGeometry.HypertranscendentalHorizonFunctionField
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# The clock-observable boundary of a hypertranscendental source

The derivation is used here as an algebraic clock: it tests which observables remain visible at a
fixed finite jet resolution.  It is not interpreted as time and does not propagate the source by
a flow.

The first exact ingredient is rational coordinate rigidity.  On the one-variable function field
`K(t)` in characteristic zero, the kernel of the coordinate derivation is exactly `K`.  Thus a
rational observable cannot depend on a boundary coordinate while hiding that dependence from the
coordinate derivative.  This excludes the only possible rational cancellation in the proposed
one-layer clock-boundary law.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

/-- The coordinate derivation `d/dt` on the rational function field `K(t)`. -/
def ratFuncCoordinateDerivation (K : Type*) [Field K] :
    Derivation K (RatFunc K) (RatFunc K) :=
  GaloisForLFunctions.fractionRingDerivation
    (Polynomial.mkDerivation K (1 : RatFunc K))

/-- The rational coordinate derivation extends the formal derivative on `K[t]`. -/
@[simp]
theorem ratFuncCoordinateDerivation_algebraMap
    {K : Type*} [Field K] (p : K[X]) :
    ratFuncCoordinateDerivation K (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) p.derivative := by
  rw [ratFuncCoordinateDerivation,
    GaloisForLFunctions.fractionRingDerivation_algebraMap,
    Polynomial.mkDerivation_apply]
  rw [Algebra.smul_def, mul_one]

/-- Quotient-rule formula exposing the unique coordinate-boundary coefficient of a rational
observable. -/
theorem ratFuncCoordinateDerivation_apply
    {K : Type*} [Field K] (z : RatFunc K) :
    ratFuncCoordinateDerivation K z =
      (algebraMap K[X] (RatFunc K) z.denom)⁻¹ ^ 2 *
        (algebraMap K[X] (RatFunc K) z.denom *
            algebraMap K[X] (RatFunc K) z.num.derivative -
          algebraMap K[X] (RatFunc K) z.num *
            algebraMap K[X] (RatFunc K) z.denom.derivative) := by
  conv_lhs => rw [← RatFunc.num_div_denom z]
  rw [Derivation.leibniz_div,
    ratFuncCoordinateDerivation_algebraMap,
    ratFuncCoordinateDerivation_algebraMap]
  simp only [smul_eq_mul]

/-- Vanishing of the coordinate derivative gives the reduced numerator-denominator Wronskian
identity. -/
theorem ratFuncCoordinateDerivation_eq_zero_cross
    {K : Type*} [Field K] (z : RatFunc K)
    (hz : ratFuncCoordinateDerivation K z = 0) :
    z.denom * z.num.derivative - z.num * z.denom.derivative = 0 := by
  have hden : algebraMap K[X] (RatFunc K) z.denom ≠ 0 :=
    fun hzero => RatFunc.denom_ne_zero z
      (IsFractionRing.injective K[X] (RatFunc K) (by simpa using hzero))
  rw [← RatFunc.num_div_denom z] at hz
  rw [Derivation.leibniz_div,
    ratFuncCoordinateDerivation_algebraMap,
    ratFuncCoordinateDerivation_algebraMap] at hz
  simp only [smul_eq_mul] at hz
  have hcrossF :
      algebraMap K[X] (RatFunc K) z.denom *
          algebraMap K[X] (RatFunc K) z.num.derivative -
        algebraMap K[X] (RatFunc K) z.num *
          algebraMap K[X] (RatFunc K) z.denom.derivative = 0 :=
    (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 (inv_ne_zero hden))
  exact IsFractionRing.injective K[X] (RatFunc K)
    (by simpa only [map_sub, map_mul, map_zero] using hcrossF)

/-- Over a field, a polynomial which divides its own derivative has zero derivative. -/
theorem polynomial_derivative_eq_zero_of_dvd_self
    {K : Type*} [Field K] {p : K[X]} (h : p ∣ p.derivative) :
    p.derivative = 0 := by
  by_contra hp'
  have hdeg : p.natDegree ≠ 0 := by
    intro hpdeg
    exact hp' (Polynomial.derivative_of_natDegree_zero hpdeg)
  exact (not_lt_of_ge (Polynomial.natDegree_le_of_dvd h hp'))
    (Polynomial.natDegree_derivative_lt hdeg)

/-- If a rational coordinate derivative vanishes, its reduced numerator is constant. -/
theorem ratFuncCoordinateDerivation_num_derivative_eq_zero
    {K : Type*} [Field K] (z : RatFunc K)
    (hz : ratFuncCoordinateDerivation K z = 0) :
    z.num.derivative = 0 := by
  have hcross := ratFuncCoordinateDerivation_eq_zero_cross z hz
  have heq : z.denom * z.num.derivative = z.num * z.denom.derivative :=
    sub_eq_zero.mp hcross
  have hdiv : z.num ∣ z.num.derivative * z.denom := by
    refine ⟨z.denom.derivative, ?_⟩
    calc
      z.num.derivative * z.denom = z.denom * z.num.derivative := mul_comm _ _
      _ = z.num * z.denom.derivative := heq
  exact polynomial_derivative_eq_zero_of_dvd_self
    ((RatFunc.isCoprime_num_denom z).dvd_of_dvd_mul_right hdiv)

/-- If a rational coordinate derivative vanishes, its normalized denominator is constant. -/
theorem ratFuncCoordinateDerivation_denom_derivative_eq_zero
    {K : Type*} [Field K] (z : RatFunc K)
    (hz : ratFuncCoordinateDerivation K z = 0) :
    z.denom.derivative = 0 := by
  have hcross := ratFuncCoordinateDerivation_eq_zero_cross z hz
  have heq : z.denom * z.num.derivative = z.num * z.denom.derivative :=
    sub_eq_zero.mp hcross
  have hdiv : z.denom ∣ z.denom.derivative * z.num := by
    refine ⟨z.num.derivative, ?_⟩
    calc
      z.denom.derivative * z.num = z.num * z.denom.derivative := mul_comm _ _
      _ = z.denom * z.num.derivative := heq.symm
  exact polynomial_derivative_eq_zero_of_dvd_self
    ((RatFunc.isCoprime_num_denom z).symm.dvd_of_dvd_mul_right hdiv)

/-- **Rational coordinate rigidity.**  In characteristic zero the constants of the coordinate
derivation on `K(t)` are exactly the coefficient field `K`. -/
theorem ratFuncCoordinateDerivation_eq_zero_iff
    {K : Type*} [Field K] [CharZero K] (z : RatFunc K) :
    ratFuncCoordinateDerivation K z = 0 ↔
      ∃ c : K, z = algebraMap K (RatFunc K) c := by
  constructor
  · intro hz
    have hp : z.num = Polynomial.C (z.num.coeff 0) :=
      Polynomial.eq_C_of_derivative_eq_zero
        (ratFuncCoordinateDerivation_num_derivative_eq_zero z hz)
    have hq : z.denom = Polynomial.C (z.denom.coeff 0) :=
      Polynomial.eq_C_of_derivative_eq_zero
        (ratFuncCoordinateDerivation_denom_derivative_eq_zero z hz)
    let a := z.num.coeff 0
    let b := z.denom.coeff 0
    refine ⟨a / b, ?_⟩
    calc
      z = algebraMap K[X] (RatFunc K) z.num /
          algebraMap K[X] (RatFunc K) z.denom :=
        (RatFunc.num_div_denom z).symm
      _ = algebraMap K[X] (RatFunc K) (Polynomial.C a) /
          algebraMap K[X] (RatFunc K) (Polynomial.C b) := by
        rw [hp, hq]
      _ = algebraMap K (RatFunc K) a / algebraMap K (RatFunc K) b := by
        congr 1
      _ = algebraMap K (RatFunc K) (a / b) :=
        (map_div₀ (algebraMap K (RatFunc K)) a b).symm
  · rintro ⟨c, rfl⟩
    exact Derivation.map_algebraMap _ _

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial
open scoped Differential

/-- Evaluating a polynomial in `t` stays in the simple transcendental field generated by `t`. -/
theorem polynomial_aeval_mem_adjoin_simple
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (P : IntermediateField F E) (t : E) (p : P[X]) :
    Polynomial.aeval t p ∈ IntermediateField.adjoin P {t} := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact IntermediateField.add_mem _ hp hq
  | monomial n a =>
      rw [Polynomial.aeval_monomial]
      exact IntermediateField.mul_mem _
        (IntermediateField.algebraMap_mem _ a)
        ((IntermediateField.adjoin P {t}).toSubfield.pow_mem
          (IntermediateField.subset_adjoin P {t} (Set.mem_singleton t)) n)

/-- If coefficient derivatives lie in `P(t)`, then the coefficient part of differentiating a
polynomial evaluation also lies in `P(t)`. -/
theorem coefficientDerivativeEval_mem_adjoin_simple
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (P : IntermediateField F E) (t : E)
    (hP : ∀ a : P, (a.1)′ ∈ IntermediateField.adjoin P {t})
    (p : P[X]) :
    PolynomialModule.eval t
        (((Differential.deriv : Derivation ℤ E E).compAlgebraMap P).mapCoeffs p) ∈
      IntermediateField.adjoin P {t} := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      change PolynomialModule.eval t
        ((show PolynomialModule E E from
            ((Differential.deriv : Derivation ℤ E E).compAlgebraMap P).mapCoeffs p) +
          (show PolynomialModule E E from
            ((Differential.deriv : Derivation ℤ E E).compAlgebraMap P).mapCoeffs q)) ∈
        IntermediateField.adjoin P {t}
      rw [LinearMap.map_add]
      exact IntermediateField.add_mem _ hp hq
  | monomial n a =>
      rw [Derivation.mapCoeffs_monomial]
      change PolynomialModule.eval t
        (PolynomialModule.single E n ((a.1)′)) ∈ IntermediateField.adjoin P {t}
      rw [PolynomialModule.eval_single, smul_eq_mul]
      exact IntermediateField.mul_mem _
        ((IntermediateField.adjoin P {t}).toSubfield.pow_mem
          (IntermediateField.subset_adjoin P {t} (Set.mem_singleton t)) n)
        (hP a)

/-- A fresh transcendental coordinate cannot carry a nonzero coefficient back into its base
field. -/
theorem transcendental_mul_mem_base_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (P : IntermediateField F E) (u : E) (hu : Transcendental P u) (b : P) :
    b.1 * u ∈ P ↔ b = 0 := by
  constructor
  · intro hbu
    by_contra hb
    have hbval : b.1 ≠ 0 := by
      intro hb0
      exact hb (Subtype.ext hb0)
    have hu_mem : u ∈ P := by
      have hinv : (b.1)⁻¹ ∈ P := IntermediateField.inv_mem P b.2
      have hprod := IntermediateField.mul_mem P hinv hbu
      simpa [hbval] using hprod
    apply hu
    rw [show u = algebraMap P E (⟨u, hu_mem⟩ : P) from rfl]
    exact isAlgebraic_algebraMap (R := P) (A := E) ⟨u, hu_mem⟩
  · rintro rfl
    simp

/-- **Rank-one clock-boundary theorem.**  Let `P(t)` be a simple transcendental observable
extension.  Suppose differentiating coefficients of `P` stays in `P(t)`, while `t'` is
transcendental over `P(t)`.  Then an observable in `P(t)` has derivative in `P(t)` exactly when it
already belongs to `P`.

This is the abstract one-layer erosion law.  It permits an arbitrary coefficient derivation, so
all closure failure is localized in the single fresh coordinate `t'`; there is no bulk leakage. -/
theorem simpleTranscendental_clock_internal_iff
    {F E : Type*} [Field F] [Field E] [CharZero E] [Algebra F E] [Differential E]
    (P : IntermediateField F E) (t z : E)
    (ht : Transcendental P t)
    (hP : ∀ a : P, (a.1)′ ∈ IntermediateField.adjoin P {t})
    (htop : Transcendental (IntermediateField.adjoin P {t}) t′)
    (hz : z ∈ IntermediateField.adjoin P {t}) :
    z′ ∈ IntermediateField.adjoin P {t} ↔ z ∈ P := by
  let Q : IntermediateField P E := IntermediateField.adjoin P {t}
  let e : RatFunc P ≃ₐ[P] Q := RatFunc.algEquivOfTranscendental t ht
  let w : RatFunc P := e.symm ⟨z, hz⟩
  have hew : e w = (⟨z, hz⟩ : Q) := e.apply_symm_apply _
  have hzrepr : z = Polynomial.aeval t w.num / Polynomial.aeval t w.denom := by
    have happ := RatFunc.algEquivOfTranscendental_apply t ht w
    have hval := happ
    have hewval := congrArg Subtype.val hew
    rw [hewval] at hval
    exact hval
  constructor
  · intro hz'
    let A : E := Polynomial.aeval t w.num
    let B : E := Polynomial.aeval t w.denom
    let Ac : E := PolynomialModule.eval t
      (((Differential.deriv : Derivation ℤ E E).compAlgebraMap P).mapCoeffs w.num)
    let Bc : E := PolynomialModule.eval t
      (((Differential.deriv : Derivation ℤ E E).compAlgebraMap P).mapCoeffs w.denom)
    let boundary : E := B⁻¹ ^ 2 *
      (B * Polynomial.aeval t w.num.derivative -
        A * Polynomial.aeval t w.denom.derivative)
    let internal : E := B⁻¹ ^ 2 * (B * Ac - A * Bc)
    have hnum := Derivation.apply_aeval_eq
      (Differential.deriv : Derivation ℤ E E) t w.num
    have hden := Derivation.apply_aeval_eq
      (Differential.deriv : Derivation ℤ E E) t w.denom
    have hclock : z′ = internal + boundary * t′ := by
      rw [hzrepr, Derivation.leibniz_div, hnum, hden]
      simp only [smul_eq_mul]
      dsimp only [A, B, Ac, Bc, boundary, internal]
      ring
    have hA : A ∈ Q := polynomial_aeval_mem_adjoin_simple P t w.num
    have hBmem : B ∈ Q := polynomial_aeval_mem_adjoin_simple P t w.denom
    have hA' : Polynomial.aeval t w.num.derivative ∈ Q :=
      polynomial_aeval_mem_adjoin_simple P t w.num.derivative
    have hB' : Polynomial.aeval t w.denom.derivative ∈ Q :=
      polynomial_aeval_mem_adjoin_simple P t w.denom.derivative
    have hAc : Ac ∈ Q := coefficientDerivativeEval_mem_adjoin_simple P t hP w.num
    have hBc : Bc ∈ Q := coefficientDerivativeEval_mem_adjoin_simple P t hP w.denom
    have hBinv2 : B⁻¹ ^ (2 : ℕ) ∈ Q :=
      Q.toSubfield.pow_mem (IntermediateField.inv_mem Q hBmem) 2
    have hboundary : boundary ∈ Q := by
      exact IntermediateField.mul_mem Q hBinv2
        (IntermediateField.sub_mem Q
          (IntermediateField.mul_mem Q hBmem hA')
          (IntermediateField.mul_mem Q hA hB'))
    have hinternal : internal ∈ Q := by
      exact IntermediateField.mul_mem Q hBinv2
        (IntermediateField.sub_mem Q
          (IntermediateField.mul_mem Q hBmem hAc)
          (IntermediateField.mul_mem Q hA hBc))
    let boundaryQ : Q := ⟨boundary, hboundary⟩
    have hboundary_top : boundary * t′ ∈ Q := by
      have hsub : z′ - internal ∈ Q := IntermediateField.sub_mem Q hz' hinternal
      rw [hclock] at hsub
      simpa only [add_sub_cancel_left] using hsub
    have hboundary_zero : boundary = 0 := by
      have hqzero : boundaryQ = 0 :=
        (transcendental_mul_mem_base_iff Q t′ htop boundaryQ).mp hboundary_top
      exact congrArg Subtype.val hqzero
    have hB : B ≠ 0 := by
      intro hzero
      apply RatFunc.denom_ne_zero w
      apply (transcendental_iff_injective.mp ht)
      simpa only [map_zero] using hzero
    have hcrossEval :
        B * Polynomial.aeval t w.num.derivative -
          A * Polynomial.aeval t w.denom.derivative = 0 := by
      exact (mul_eq_zero.mp hboundary_zero).resolve_left
        (pow_ne_zero 2 (inv_ne_zero hB))
    have hcross :
        w.denom * w.num.derivative - w.num * w.denom.derivative = 0 := by
      apply (transcendental_iff_injective.mp ht)
      simpa only [map_sub, map_mul, map_zero, A, B] using hcrossEval
    have hwzero : ratFuncCoordinateDerivation P w = 0 := by
      rw [ratFuncCoordinateDerivation_apply]
      have hmapcross :
          algebraMap P[X] (RatFunc P) w.denom *
              algebraMap P[X] (RatFunc P) w.num.derivative -
            algebraMap P[X] (RatFunc P) w.num *
              algebraMap P[X] (RatFunc P) w.denom.derivative = 0 := by
        simpa only [map_sub, map_mul, map_zero] using
          congrArg (algebraMap P[X] (RatFunc P)) hcross
      rw [hmapcross, mul_zero]
    obtain ⟨c, hc⟩ := (ratFuncCoordinateDerivation_eq_zero_iff w).mp hwzero
    have hewc : e (algebraMap P (RatFunc P) c) = (⟨z, hz⟩ : Q) := by
      rw [← hc]
      exact hew
    have hval := congrArg Subtype.val hewc
    have hcomm := congrArg Subtype.val (e.commutes c)
    have hcz : c.1 = z := by
      calc
        c.1 = (algebraMap P Q c).1 := rfl
        _ = (e (algebraMap P (RatFunc P) c)).1 := hcomm.symm
        _ = z := hval
    rw [← hcz]
    exact c.2
  · intro hzP
    exact hP ⟨z, hzP⟩

end

end GaloisForLFunctions.HTGeometry
