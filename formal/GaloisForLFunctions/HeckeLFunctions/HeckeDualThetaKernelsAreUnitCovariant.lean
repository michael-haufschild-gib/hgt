import GaloisForLFunctions.HeckeLFunctions.HeckeFourierCoefficientsAreInverseHeckeValues
import GaloisForLFunctions.HeckeLFunctions.HeckeThetaAveragesOverTheUnitDomain

/-!
# Unit covariance of the actual dual Hecke kernel

Finite Fourier covariance and the global finite/sign relation cancel the
archimedean parity factor under simultaneous multiplication by a unit and
translation by its place logarithms. In the negative coordinates of the
dual average, the resulting log-lattice translation has a positive sign.
-/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open scoped Classical
namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry HTGeometry.IntegerLatticePoisson

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)
  {b : Ideal (𝓞 K)} (hb : b ⊔ 𝔪.fin = ⊤) (hb0 : b ≠ ⊥)
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
local notation "Jdual" => FractionalIdeal.dual ℤ ℚ ((𝔪.fin * b : Ideal (𝓞 K)) : FI)

/-- The actual finite Fourier coefficient times the archimedean parity kernel. -/
def heckeDualThetaKernel (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ)
    (t : ℝ) (a : K) : ℂ :=
  finiteHeckeFourierCoefficient 𝔪 hb ψ a * heckeParityKernel 𝔪 ψ y t a

/-- Unit-log scaling contributes exactly the infinite sign character to the parity kernel. -/
theorem heckeParityKernel_unit (ψ : HeckeCharacter 𝔪) (y : InfinitePlace K → ℝ)
    (u : (𝓞 K)ˣ) (t : ℝ) (a : K) :
    heckeParityKernel 𝔪 ψ (y + numberFieldUnitPlaceLogEmbeddings u) t (((u : 𝓞 K) : K) * a) =
      (infiniteSignCharacter 𝔪 ψ
        (signAtInf 𝔪 (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)) : ℂ) *
          heckeParityKernel 𝔪 ψ y t a := by
  simp only [heckeParityKernel, parityGaussian, parityMonomial_heckeCoordinateParity,
    gaussianKernel_eq_ofReal]
  rw [heckeRealMonomial_unit, norm_sq_numberFieldPlaceScale_unit,
    ← infiniteSignCharacter_eq_prod, mul_assoc]

/-- On global units the reciprocal finite factor cancels the actual parity sign. -/
theorem inverse_finite_mul_infinite_globalUnit (ψ : HeckeCharacter 𝔪) (u : (𝓞 K)ˣ) :
    (finiteResidueCharacter 𝔪 ψ (reduce 𝔪 (globalUnitPrimeTo 𝔪 u)) : ℂ)⁻¹ *
      (infiniteSignCharacter 𝔪 ψ
        (signAtInf 𝔪 (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)) : ℂ) = 1 := by
  have h := congrArg (fun z : ℂˣ => (z : ℂ)) (finite_mul_infinite_globalUnit 𝔪 ψ u)
  simp only [Units.val_mul, Units.val_one] at h
  have hs := infiniteSignCharacter_sq 𝔪 ψ
    (signAtInf 𝔪 (Units.map (algebraMap (𝓞 K) K).toMonoidHom u))
  have heq : (finiteResidueCharacter 𝔪 ψ (reduce 𝔪 (globalUnitPrimeTo 𝔪 u)) : ℂ) =
      (infiniteSignCharacter 𝔪 ψ
        (signAtInf 𝔪 (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)) : ℂ) := by
    apply mul_right_cancel₀ (Units.ne_zero (infiniteSignCharacter 𝔪 ψ
      (signAtInf 𝔪 (Units.map (algebraMap (𝓞 K) K).toMonoidHom u))))
    exact h.trans (by simpa only [pow_two] using hs.symm)
  rw [heq, inv_mul_cancel₀ (Units.ne_zero _)]

include hb0

/-- Finite Fourier covariance cancels parity signs under a simultaneous global-unit scaling. -/
theorem heckeDualThetaKernel_unit (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (y : InfinitePlace K → ℝ)
    (u : (𝓞 K)ˣ) (t : ℝ) (a : Jdual) :
    heckeDualThetaKernel 𝔪 hb ψ (y + numberFieldUnitPlaceLogEmbeddings u) t
        (((u : 𝓞 K) : K) * (a : K)) =
      heckeDualThetaKernel 𝔪 hb ψ y t (a : K) := by
  have hF := finiteHeckeFourierCoefficient_mul_primeTo 𝔪 hb hb0 ψ hψ
    (globalUnitPrimeTo 𝔪 u) a (heckeTraceFrequencyMul 𝔪 (u : 𝓞 K) a) rfl
  change finiteHeckeFourierCoefficient 𝔪 hb ψ (((u : 𝓞 K) : K) * (a : K)) = _ at hF
  rw [heckeDualThetaKernel, hF, heckeParityKernel_unit]
  calc
    _ = ((finiteResidueCharacter 𝔪 ψ (reduce 𝔪 (globalUnitPrimeTo 𝔪 u)) : ℂ)⁻¹ *
          (infiniteSignCharacter 𝔪 ψ
            (signAtInf 𝔪 (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)) : ℂ)) *
        (finiteHeckeFourierCoefficient 𝔪 hb ψ (a : K) * heckeParityKernel 𝔪 ψ y t (a : K)) := by
      ring
    _ = _ := by rw [inverse_finite_mul_infinite_globalUnit, one_mul]; rfl

/-- Multiplication of a frequency by a unit translates positive log coordinates by its negative log. -/
theorem heckeDualThetaKernel_unit_as_logTranslate (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (x : logSpace K)
    (u : (𝓞 K)ˣ) (t : ℝ) (a : Jdual) :
    heckeDualThetaKernel 𝔪 hb ψ (numberFieldWeightedLogProfile x) t
        (((u : 𝓞 K) : K) * (a : K)) =
      heckeDualThetaKernel 𝔪 hb ψ
        (numberFieldWeightedLogProfile (x - Units.logEmbedding K (Additive.ofMul u))) t (a : K) := by
  have h := heckeDualThetaKernel_unit 𝔪 hb hb0 ψ hψ
    (numberFieldWeightedLogProfile (x - Units.logEmbedding K (Additive.ofMul u))) u t a
  have hp : numberFieldWeightedLogProfile (x - Units.logEmbedding K (Additive.ofMul u)) +
      numberFieldUnitPlaceLogEmbeddings u = numberFieldWeightedLogProfile x := by
    rw [map_sub, numberFieldWeightedLogProfile_logEmbedding, sub_add_cancel]
  rw [hp] at h
  exact h

/-- The actual dual average uses negative coordinates, hence unit multiplication translates by plus. -/
theorem heckeDualThetaKernel_unit_as_negativeLogTranslate (ψ : HeckeCharacter 𝔪)
    (hψ : heckeFiniteConductor 𝔪 ψ = 𝔪.fin) (x : logSpace K)
    (u : (𝓞 K)ˣ) (t : ℝ) (a : Jdual) :
    heckeDualThetaKernel 𝔪 hb ψ (-numberFieldWeightedLogProfile x) t
        (((u : 𝓞 K) : K) * (a : K)) =
      heckeDualThetaKernel 𝔪 hb ψ
        (-numberFieldWeightedLogProfile (x + Units.logEmbedding K (Additive.ofMul u))) t (a : K) := by
  have h := heckeDualThetaKernel_unit_as_logTranslate 𝔪 hb hb0 ψ hψ (-x) u t a
  simpa only [map_neg, show -x - Units.logEmbedding K (Additive.ofMul u) =
    -(x + Units.logEmbedding K (Additive.ofMul u)) by abel] using h

end GaloisForLFunctions.HeckeLFunctions

#print axioms GaloisForLFunctions.HeckeLFunctions.heckeDualThetaKernel_unit
#print axioms GaloisForLFunctions.HeckeLFunctions.heckeDualThetaKernel_unit_as_negativeLogTranslate
