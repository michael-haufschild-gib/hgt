import GaloisForLFunctions.RHTower.CCMArchimedeanQuantizedCalculus
import GaloisForLFunctions.RHTower.FieldOneFiniteStageConnesMarcolliLocalRatio

/-!
# Literal one-prime Connes--Consani source defect

This file constructs the source-faithful operator appearing in Connes--Consani's one-prime
quasi-inner theorem.  Its symbol is the literal product of the archimedean Gamma scattering ratio
and the finite Euler ratio, acting by multiplication on spectral `L²(ℝ)`.  The operator

`(1 - P) M_(rho_infinity rho_p) P`

is then defined using the existing literal Hardy projection.  This is the concrete source object
to which the residue decomposition must be compared; no compactness or ideal property is assumed.
-/

noncomputable section

open Complex MeasureTheory

namespace RHTower

/-- Literal product `rho_infinity rho_p` on the critical-line spectral coordinate. -/
def connesConsaniOnePrimeScatteringSymbol (p : Nat.Primes) (t : ℝ) : ℂ :=
  ccmArchimedeanScatteringPhase t *
    GaloisForLFunctions.RHTower.primeRatio p t

theorem continuous_connesConsaniOnePrimeScatteringSymbol (p : Nat.Primes) :
    Continuous (connesConsaniOnePrimeScatteringSymbol p) := by
  exact ccmArchimedeanScatteringPhase_hasTemperateGrowth.1.continuous.mul
    (GaloisForLFunctions.RHTower.continuous_primeRatio p)

theorem norm_connesConsaniOnePrimeScatteringSymbol
    (p : Nat.Primes) (t : ℝ) :
    ‖connesConsaniOnePrimeScatteringSymbol p t‖ = 1 := by
  rw [connesConsaniOnePrimeScatteringSymbol, norm_mul,
    norm_ccmArchimedeanScatteringPhase]
  unfold GaloisForLFunctions.RHTower.primeRatio
  rw [GaloisForLFunctions.RHTower.norm_primeLocalRatio
    (GaloisForLFunctions.RHTower.abs_primeRadius_lt_one p)]
  simp

/-- Source symbol written as the quotient of literal archimedean and finite local factors. -/
theorem connesConsaniOnePrimeScatteringSymbol_eq_localFactorProduct
    (p : Nat.Primes) (t : ℝ) :
    connesConsaniOnePrimeScatteringSymbol p t =
      GaloisForLFunctions.RHTower.archRatio t *
        (primeEulerFactor (p : ℝ) t / primeEulerFactor (p : ℝ) (-t)) := by
  rw [connesConsaniOnePrimeScatteringSymbol,
    GaloisForLFunctions.RHTower.archRatio_eq_ccmArchimedeanScatteringPhase,
    GaloisForLFunctions.RHTower.primeRatio_eq_localLFactor_ratio p p.prop.one_lt]

/-- The literal one-prime product as a measurable unit-modulus `L²` phase. -/
def connesConsaniOnePrimeScatteringPhase (p : Nat.Primes) :
    GaloisForLFunctions.RHTower.UnitModulusL2Phase ℝ (volume : Measure ℝ) where
  toFun := connesConsaniOnePrimeScatteringSymbol p
  aestronglyMeasurable :=
    (continuous_connesConsaniOnePrimeScatteringSymbol p).aestronglyMeasurable
  norm_eq_one := Filter.Eventually.of_forall
    (norm_connesConsaniOnePrimeScatteringSymbol p)

/-- Unitary multiplication by the source product `rho_infinity rho_p`. -/
def connesConsaniOnePrimeScatteringUnitary (p : Nat.Primes) :
    SoninL2 ≃ₗᵢ[ℂ] SoninL2 :=
  (connesConsaniOnePrimeScatteringPhase p).mulUnitary

/-- Bounded-operator realization of the one-prime source multiplier. -/
def connesConsaniOnePrimeScatteringMultiplier (p : Nat.Primes) :
    SoninL2 →L[ℂ] SoninL2 :=
  (connesConsaniOnePrimeScatteringUnitary p).toLinearIsometry.toContinuousLinearMap

theorem connesConsaniOnePrimeScatteringMultiplier_ae
    (p : Nat.Primes) (f : SoninL2) :
    connesConsaniOnePrimeScatteringMultiplier p f =ᵐ[volume]
      fun t => connesConsaniOnePrimeScatteringSymbol p t * f t :=
  (connesConsaniOnePrimeScatteringPhase p).mulUnitary_ae f

/-- The finite local ratio alone as a measurable unit-modulus phase. -/
def connesConsaniPrimeScatteringPhase (p : Nat.Primes) :
    GaloisForLFunctions.RHTower.UnitModulusL2Phase ℝ (volume : Measure ℝ) where
  toFun := GaloisForLFunctions.RHTower.primeRatio p
  aestronglyMeasurable :=
    (GaloisForLFunctions.RHTower.continuous_primeRatio p).aestronglyMeasurable
  norm_eq_one := Filter.Eventually.of_forall fun t => by
    unfold GaloisForLFunctions.RHTower.primeRatio
    exact GaloisForLFunctions.RHTower.norm_primeLocalRatio
      (GaloisForLFunctions.RHTower.abs_primeRadius_lt_one p) _ _

/-- Unitary multiplication by the finite local ratio `rho_p`. -/
def connesConsaniPrimeScatteringUnitary (p : Nat.Primes) :
    SoninL2 ≃ₗᵢ[ℂ] SoninL2 :=
  (connesConsaniPrimeScatteringPhase p).mulUnitary

/-- Bounded-operator realization of multiplication by `rho_p`. -/
def connesConsaniPrimeScatteringMultiplier (p : Nat.Primes) :
    SoninL2 →L[ℂ] SoninL2 :=
  (connesConsaniPrimeScatteringUnitary p).toLinearIsometry.toContinuousLinearMap

theorem connesConsaniPrimeScatteringMultiplier_ae
    (p : Nat.Primes) (f : SoninL2) :
    connesConsaniPrimeScatteringMultiplier p f =ᵐ[volume]
      fun t => GaloisForLFunctions.RHTower.primeRatio p t * f t :=
  (connesConsaniPrimeScatteringPhase p).mulUnitary_ae f

/-- The source product multiplier is literally the product of its two local multipliers. -/
theorem connesConsaniOnePrimeScatteringMultiplier_eq_mul
    (p : Nat.Primes) :
    connesConsaniOnePrimeScatteringMultiplier p =
      ccmArchimedeanScatteringL2Multiplier *
        connesConsaniPrimeScatteringMultiplier p := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [
    connesConsaniOnePrimeScatteringMultiplier_ae p f,
    ccmArchimedeanScatteringL2Multiplier_ae
      (connesConsaniPrimeScatteringMultiplier p f),
    connesConsaniPrimeScatteringMultiplier_ae p f]
    with t hsource harch hprime
  rw [hsource]
  change connesConsaniOnePrimeScatteringSymbol p t * f t =
    (ccmArchimedeanScatteringL2Multiplier
      (connesConsaniPrimeScatteringMultiplier p f) : SoninL2) t
  rw [harch, hprime, connesConsaniOnePrimeScatteringSymbol]
  ring

/-- Archimedean Hardy defect `(1-P) M_(rho_infinity) P`. -/
def connesConsaniArchimedeanSourceDefect : SoninL2 →L[ℂ] SoninL2 :=
  (1 - ccmHardyProjection) *
    ccmArchimedeanScatteringL2Multiplier * ccmHardyProjection

/-- Finite-place Hardy defect `(1-P) M_(rho_p) P`. -/
def connesConsaniPrimeSourceDefect (p : Nat.Primes) : SoninL2 →L[ℂ] SoninL2 :=
  (1 - ccmHardyProjection) *
    connesConsaniPrimeScatteringMultiplier p * ccmHardyProjection

/-- Literal source Hardy defect `(1-P) M_(rho_infinity rho_p) P`. -/
def connesConsaniOnePrimeSourceDefect (p : Nat.Primes) :
    SoninL2 →L[ℂ] SoninL2 :=
  (1 - ccmHardyProjection) *
    connesConsaniOnePrimeScatteringMultiplier p * ccmHardyProjection

/-- Exact block-product decomposition of the literal source defect.  The second term is where the
finite-place noncompact block is regularized by the archimedean factor. -/
theorem connesConsaniOnePrimeSourceDefect_eq_blockProduct
    (p : Nat.Primes) :
    connesConsaniOnePrimeSourceDefect p =
      connesConsaniArchimedeanSourceDefect *
          connesConsaniPrimeScatteringMultiplier p * ccmHardyProjection +
        (1 - ccmHardyProjection) * ccmArchimedeanScatteringL2Multiplier *
          connesConsaniPrimeSourceDefect p := by
  rw [connesConsaniOnePrimeSourceDefect,
    connesConsaniOnePrimeScatteringMultiplier_eq_mul,
    connesConsaniArchimedeanSourceDefect,
    connesConsaniPrimeSourceDefect]
  noncomm_ring

/-- The source defect only sees the Hardy input component. -/
theorem connesConsaniOnePrimeSourceDefect_mul_hardyProjection
    (p : Nat.Primes) :
    connesConsaniOnePrimeSourceDefect p * ccmHardyProjection =
      connesConsaniOnePrimeSourceDefect p := by
  have hP := ccmHardyProjection_idempotent
  rw [isIdempotentElem_iff] at hP
  unfold connesConsaniOnePrimeSourceDefect
  rw [mul_assoc, hP]

/-- The source defect lands in the orthogonal anti-Hardy component. -/
theorem one_sub_hardyProjection_mul_connesConsaniOnePrimeSourceDefect
    (p : Nat.Primes) :
    (1 - ccmHardyProjection) * connesConsaniOnePrimeSourceDefect p =
      connesConsaniOnePrimeSourceDefect p := by
  have hP := ccmHardyProjection_idempotent
  rw [isIdempotentElem_iff] at hP
  have hPc :
      (1 - ccmHardyProjection) * (1 - ccmHardyProjection) =
        1 - ccmHardyProjection := by
    calc
      (1 - ccmHardyProjection) * (1 - ccmHardyProjection) =
          1 - ccmHardyProjection - ccmHardyProjection +
            ccmHardyProjection * ccmHardyProjection := by noncomm_ring
      _ = 1 - ccmHardyProjection := by rw [hP]; module
  unfold connesConsaniOnePrimeSourceDefect
  simp only [← mul_assoc, hPc]

/-- The Hardy projection annihilates the output of the source defect. -/
theorem hardyProjection_mul_connesConsaniOnePrimeSourceDefect
    (p : Nat.Primes) :
    ccmHardyProjection * connesConsaniOnePrimeSourceDefect p = 0 := by
  have hP := ccmHardyProjection_idempotent
  rw [isIdempotentElem_iff] at hP
  unfold connesConsaniOnePrimeSourceDefect
  rw [← mul_assoc]
  have hz : ccmHardyProjection * (1 - ccmHardyProjection) = 0 := by
    rw [mul_sub, mul_one, hP, sub_self]
  calc
    ccmHardyProjection *
          ((1 - ccmHardyProjection) *
            connesConsaniOnePrimeScatteringMultiplier p) *
        ccmHardyProjection =
        (ccmHardyProjection * (1 - ccmHardyProjection)) *
          connesConsaniOnePrimeScatteringMultiplier p * ccmHardyProjection := by
      simp only [mul_assoc]
    _ = 0 := by rw [hz, zero_mul, zero_mul]

end RHTower
