import GaloisForLFunctions.RHTower.FieldOneFiniteStageConnesMarcolliCoinvariants
import GaloisForLFunctions.RHTower.FieldOneFiniteStageSelfDualHaar
import GaloisForLFunctions.RHTower.FieldOneSemilocalStageRestrictionWeyl
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Connes--Marcolli finite-stage additive Fourier core

This file constructs the literal additive character and Fourier integral used
in Connes--Marcolli Lemma 2.33.  The transform acts on the actual finite-stage
Bruhat--Schwartz realization, and its covariance is proved by Haar change of
variables along the actual diagonal `S`-unit action.

The remaining Plancherel step requires the self-dual normalization of the
nonarchimedean Haar factors; it is not postulated here.
-/

open scoped TensorProduct algebraMap

namespace GaloisForLFunctions.RHTower

noncomputable section

open Function IsDedekindDomain MeasureTheory MeasureTheory.Measure

/-- Exact conductor of the transported standard character at every rational
finite place. -/
theorem fieldOneFiniteAdeleLocalUnitCharacter_eq_zero_iff
    (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    fieldOneFiniteAdeleLocalUnitCharacter v x = 0 ↔
      x ∈ v.adicCompletionIntegers ℚ := by
  letI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  change
    fieldOnePadicStandardUnitAddCircleCharacter
        (Rat.HeightOneSpectrum.primesEquiv v)
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x) = 0 ↔ _
  rw [fieldOnePadicStandardUnitAddCircleCharacter_eq_zero_iff]
  constructor
  · intro hx
    obtain ⟨z, hz, hzx⟩ :=
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).surjOn hx
    have : z = x :=
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective hzx
    simpa [this] using hz
  · intro hx
    change
      Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v)
    exact
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hx

/-- The local finite-stage character is locally constant on every rational
nonarchimedean completion. -/
theorem fieldOneFiniteAdeleLocalUnitCharacter_isLocallyConstant
    (v : HeightOneSpectrum ℤ) :
    IsLocallyConstant (fieldOneFiniteAdeleLocalUnitCharacter v) := by
  letI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  change IsLocallyConstant (fun x =>
    fieldOnePadicStandardUnitAddCircleCharacter
      (Rat.HeightOneSpectrum.primesEquiv v)
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v x))
  exact
    (fieldOnePadicStandardUnitAddCircleCharacter_isLocallyConstant
      (Rat.HeightOneSpectrum.primesEquiv v)).comp_continuous
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).continuous

/-- Each local summand in the finite-stage character is continuous. -/
theorem fieldOneFiniteStageLocalTerm_continuous
    (S : Finset (HeightOneSpectrum ℤ))
    (v : HeightOneSpectrum ℤ) :
    Continuous (fun x : FieldOneFiniteStageAdele S =>
      fieldOneFiniteStageLocalTerm S x v) := by
  classical
  by_cases hv : v ∈ S
  · let w : ↑S := ⟨v, hv⟩
    have hprojection : Continuous (fun x : FieldOneFiniteStageAdele S => x.2 w) :=
      (continuous_apply w).comp continuous_snd
    have hlocal : IsLocallyConstant
        (fun x : FieldOneFiniteStageAdele S =>
          fieldOneFiniteAdeleLocalUnitCharacter v (x.2 w)) :=
      (fieldOneFiniteAdeleLocalUnitCharacter_isLocallyConstant v).comp_continuous
        hprojection
    simpa only [fieldOneFiniteStageLocalTerm, dif_pos hv] using hlocal.continuous
  · simp only [fieldOneFiniteStageLocalTerm, dif_neg hv]
    exact continuous_const

/-- The source additive-circle character on `A_S` is continuous. -/
theorem fieldOneFiniteStageUnitCharacter_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageUnitCharacter S) := by
  change Continuous (fun x : FieldOneFiniteStageAdele S =>
    -((x.1 : ℝ) : UnitAddCircle) +
      ∑ v ∈ S, fieldOneFiniteStageLocalTerm S x v)
  exact
    (((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst).neg).add
      (continuous_finsetSum S fun v _ =>
        fieldOneFiniteStageLocalTerm_continuous S v)

/-- Circle-valued source character used by the Fourier integral. -/
def fieldOneFiniteStageCircleAddChar
    (S : Finset (HeightOneSpectrum ℤ)) :
    AddChar (FieldOneFiniteStageAdele S) Circle :=
  AddCircle.toCircle_addChar.compAddMonoidHom <|
    fieldOneFiniteStageUnitCharacter S

/-- The complex source character is continuous. -/
theorem fieldOneFiniteStageCircleAddChar_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageCircleAddChar S) := by
  change Continuous (fun x =>
    AddCircle.toCircle (fieldOneFiniteStageUnitCharacter S x))
  exact AddCircle.continuous_toCircle.comp
    (fieldOneFiniteStageUnitCharacter_continuous S)

/-- Every literal finite-stage Bruhat--Schwartz realization is additively
Haar-integrable. -/
theorem fieldOneFiniteStageBruhatEval_integrable
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    Integrable (fieldOneFiniteStageBruhatEval S x)
      (fieldOneFiniteStageSelfDualAddHaar S) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [fieldOneFiniteStageBruhatEval]
  | tmul f phi =>
      have hphi : Integrable
          (phi.1 : FieldOneFiniteStageFinitePart S → ℂ)
          (Measure.pi fun v : ↑S =>
            fieldOneLocalSelfDualAddHaar v.1) :=
        phi.1.continuous.integrable_of_hasCompactSupport phi.2
      change Integrable
        (fun a : FieldOneFiniteStageAdele S => f a.1 * phi.1 a.2)
        ((volume : Measure ℝ).prod
          (Measure.pi fun v : ↑S =>
            fieldOneLocalSelfDualAddHaar v.1))
      exact Integrable.mul_prod f.integrable hphi
  | add x y hx hy =>
      exact (hx.add hy).congr (Filter.Eventually.of_forall fun a => by
        simp [fieldOneFiniteStageBruhatEval])

/-- Literal additive Fourier transform of a finite-stage Bruhat--Schwartz
vector, with the source character and the explicit additive Haar measure. -/
def fieldOneFiniteStageBruhatFourierEval
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    FieldOneFiniteStageAdele S → ℂ :=
  Fourier.fourierIntegral
    (fieldOneFiniteStageCircleAddChar S)
    (fieldOneFiniteStageSelfDualAddHaar S)
    (fieldOneFiniteStageBruhatEval S x)

theorem fieldOneFiniteStageBruhatFourierEval_apply
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S)
    (w : FieldOneFiniteStageAdele S) :
    fieldOneFiniteStageBruhatFourierEval S x w =
      ∫ a, fieldOneFiniteStageCircleAddChar S (-(a * w)) •
          fieldOneFiniteStageBruhatEval S x a
          ∂fieldOneFiniteStageSelfDualAddHaar S :=
  rfl

/-- Fourier transforms of literal Bruhat--Schwartz vectors are continuous. -/
theorem fieldOneFiniteStageBruhatFourierEval_continuous
    (S : Finset (HeightOneSpectrum ℤ))
    (x : FieldOneFiniteStageBruhatSchwartz S) :
    Continuous (fieldOneFiniteStageBruhatFourierEval S x) := by
  exact VectorFourier.fourierIntegral_continuous
    (fieldOneFiniteStageCircleAddChar_continuous S)
    (continuous_fst.mul continuous_snd)
    (fieldOneFiniteStageBruhatEval_integrable S x)

/-- The literal Fourier transform is complex-linear on the Bruhat tensor
core. -/
def fieldOneFiniteStageBruhatFourierLinear
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageBruhatSchwartz S →ₗ[ℂ]
      (FieldOneFiniteStageAdele S → ℂ) where
  toFun := fieldOneFiniteStageBruhatFourierEval S
  map_add' x y := by
    change VectorFourier.fourierIntegral
        (fieldOneFiniteStageCircleAddChar S)
        (fieldOneFiniteStageSelfDualAddHaar S)
        (LinearMap.mul _ _)
        (fieldOneFiniteStageBruhatEval S (x + y)) = _
    rw [map_add]
    exact VectorFourier.fourierIntegral_add
      (fieldOneFiniteStageCircleAddChar_continuous S)
      (continuous_fst.mul continuous_snd)
      (fieldOneFiniteStageBruhatEval_integrable S x)
      (fieldOneFiniteStageBruhatEval_integrable S y)
  map_smul' c x := by
    change Fourier.fourierIntegral
        (fieldOneFiniteStageCircleAddChar S)
        (fieldOneFiniteStageSelfDualAddHaar S)
        (fieldOneFiniteStageBruhatEval S (c • x)) =
      c • Fourier.fourierIntegral
        (fieldOneFiniteStageCircleAddChar S)
        (fieldOneFiniteStageSelfDualAddHaar S)
        (fieldOneFiniteStageBruhatEval S x)
    rw [map_smul]
    exact Fourier.fourierIntegral_const_smul
      (fieldOneFiniteStageCircleAddChar S)
      (fieldOneFiniteStageSelfDualAddHaar S)
      (fieldOneFiniteStageBruhatEval S x) c

end

end GaloisForLFunctions.RHTower
