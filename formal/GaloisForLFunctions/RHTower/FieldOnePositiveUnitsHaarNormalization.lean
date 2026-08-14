import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassInvariantL2
import GaloisForLFunctions.RHTower.FieldOnePositiveUnitsLogHaar
import GaloisForLFunctions.RHTower.EvenL2LogUnitary
import GaloisForLFunctions.RHTower.HardyTitchmarshEulerConcrete
import GaloisForLFunctions.HTGeometry.WeightedDensityL2

/-!
# Common Haar normalization for `w_∞` and `w_S`

The archimedean logarithmic model naturally uses the pushforward of Lebesgue
measure under `exp`, while the literal finite-stage source unitary uses the
canonical Haar measure on positive units.  These Haar measures differ by the
strictly positive Haar scalar.  This file constructs the exact density
unitary between them and hence the source-normalized archimedean unitary

`w_∞ : L²(ℝ)^ev ≃ L²(ℝ_+^*, d*u)`

with precisely the same target and Haar normalization as the literal `w_S`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory MeasureTheory.Measure IsDedekindDomain
open scoped NNReal

/-- Constant Radon--Nikodym weight from logarithmic Haar to canonical Haar. -/
def fieldOnePositiveUnitsHaarLogWeight (_ : ℝ≥0ˣ) : ℝ :=
  haarScalarFactor fieldOnePositiveUnitsHaarMeasure
    fieldOnePositiveUnitsLogHaarMeasure

theorem fieldOnePositiveUnitsHaar_eq_withDensity :
    fieldOnePositiveUnitsHaarMeasure =
      fieldOnePositiveUnitsLogHaarMeasure.withDensity
        (GaloisForLFunctions.HTGeometry.realDensity
          fieldOnePositiveUnitsHaarLogWeight) := by
  rw [fieldOnePositiveUnitsHaar_eq_smul_logHaar]
  change _ = fieldOnePositiveUnitsLogHaarMeasure.withDensity
    (fun _ => ENNReal.ofReal
      (haarScalarFactor fieldOnePositiveUnitsHaarMeasure
        fieldOnePositiveUnitsLogHaarMeasure : ℝ))
  rw [MeasureTheory.withDensity_const]
  simp

theorem fieldOnePositiveUnitsHaarLogWeight_measurable :
    Measurable fieldOnePositiveUnitsHaarLogWeight :=
  measurable_const

theorem fieldOnePositiveUnitsHaarLogWeight_pos (x : ℝ≥0ˣ) :
    0 < fieldOnePositiveUnitsHaarLogWeight x :=
  fieldOnePositiveUnitsHaar_logScalar_pos

/-- Exact unitary from canonical positive-unit Haar to logarithmic Haar. -/
def fieldOnePositiveUnitsHaarToLogUnitary :
    FieldOnePositiveUnitsL2 ≃ₗᵢ[ℂ]
      Lp ℂ 2 fieldOnePositiveUnitsLogHaarMeasure := by
  change Lp ℂ 2 fieldOnePositiveUnitsHaarMeasure ≃ₗᵢ[ℂ]
    Lp ℂ 2 fieldOnePositiveUnitsLogHaarMeasure
  rw [fieldOnePositiveUnitsHaar_eq_withDensity]
  exact GaloisForLFunctions.HTGeometry.weightedDensityUnitary
    fieldOnePositiveUnitsHaarLogWeight
    fieldOnePositiveUnitsHaarLogWeight_measurable
    fieldOnePositiveUnitsHaarLogWeight_pos

/-- Pullback by `exp` between positive-unit logarithmic Haar and Lebesgue L². -/
def fieldOnePositiveUnitsLogPullbackUnitary :
    Lp ℂ 2 fieldOnePositiveUnitsLogHaarMeasure ≃ₗᵢ[ℂ]
      Lp (α := ℝ) ℂ 2 :=
  RHTower.MellinL2.lpCompMeasurePreservingEquiv
    fieldOnePositiveUnitsExpHomeomorph.toMeasurableEquiv
    fieldOnePositiveUnitsExp_measurePreserving

/-- Source-normalized archimedean `w_∞`, with exactly the target used by the
literal finite-stage `w_S`. -/
def fieldOneEvenToPositiveUnitsHaarUnitary :
    RHTower.evenSubspace ≃ₗᵢ[ℂ] FieldOnePositiveUnitsL2 :=
  RHTower.logEvenUnitary.trans
    (fieldOnePositiveUnitsLogPullbackUnitary.symm.trans
      fieldOnePositiveUnitsHaarToLogUnitary.symm)

/-! ## Finite Euler factor in the source-normalized archimedean model -/

/-- Rational prime below a finite place of `ℚ`. -/
def fieldOneFinitePlacePrime (v : HeightOneSpectrum ℤ) : ℕ :=
  ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ)

theorem fieldOneFinitePlacePrime_prime (v : HeightOneSpectrum ℤ) :
    Nat.Prime (fieldOneFinitePlacePrime v) := by
  exact (Rat.HeightOneSpectrum.primesEquiv v).property

theorem fieldOneFinitePlacePrime_real_gt_one (v : HeightOneSpectrum ℤ) :
    1 < (fieldOneFinitePlacePrime v : ℝ) := by
  exact_mod_cast (fieldOneFinitePlacePrime_prime v).one_lt

/-- The factor `1-p⁻¹ ²⁻ⁱˢ` attached to one place, acting on even
archimedean `L²`.  `evenPrimeLocalFactor` is its exact dilation operator. -/
def fieldOneFiniteStageThetaEulerTerm (S : Finset (HeightOneSpectrum ℤ))
    (v : {v : HeightOneSpectrum ℤ // v ∈ S}) :
    RHTower.evenSubspace →L[ℂ] RHTower.evenSubspace :=
  RHTower.evenPrimeLocalFactor (fieldOneFinitePlacePrime v.1 : ℝ)
    (fieldOneFinitePlacePrime_real_gt_one v.1)

/-- Finite Euler product `∏_{v∈S}(1-p_v⁻¹ ²⁻ⁱˢ)` as a concrete bounded
operator, without assuming any spectral nonvanishing hypothesis. -/
def fieldOneFiniteStageThetaEulerOperator
    (S : Finset (HeightOneSpectrum ℤ)) :
    RHTower.evenSubspace →L[ℂ] RHTower.evenSubspace :=
  (S.attach.toList.map (fieldOneFiniteStageThetaEulerTerm S)).prod

theorem fieldOneFiniteStageThetaEulerTerm_isUnit
    (S : Finset (HeightOneSpectrum ℤ))
    (v : {v : HeightOneSpectrum ℤ // v ∈ S}) :
    IsUnit (fieldOneFiniteStageThetaEulerTerm S v) := by
  unfold fieldOneFiniteStageThetaEulerTerm
  apply RHTower.evenPrimeLocalFactor_isUnit

theorem fieldOneFiniteStageThetaEulerOperator_isUnit
    (S : Finset (HeightOneSpectrum ℤ)) :
    IsUnit (fieldOneFiniteStageThetaEulerOperator S) := by
  unfold fieldOneFiniteStageThetaEulerOperator
  apply List.prod_isUnit
  intro T hT
  rw [List.mem_map] at hT
  obtain ⟨v, hv, rfl⟩ := hT
  exact fieldOneFiniteStageThetaEulerTerm_isUnit S v

/-- Explicit bounded inverse of the finite Euler product. -/
def fieldOneFiniteStageThetaEulerResolvent
    (S : Finset (HeightOneSpectrum ℤ)) :
    RHTower.evenSubspace →L[ℂ] RHTower.evenSubspace :=
  ↑((fieldOneFiniteStageThetaEulerOperator_isUnit S).unit⁻¹)

theorem fieldOneFiniteStageThetaEulerOperator_mul_resolvent
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageThetaEulerOperator S *
        fieldOneFiniteStageThetaEulerResolvent S = 1 := by
  let u := (fieldOneFiniteStageThetaEulerOperator_isUnit S).unit
  change (u : RHTower.evenSubspace →L[ℂ] RHTower.evenSubspace) *
      (↑(u⁻¹) : RHTower.evenSubspace →L[ℂ] RHTower.evenSubspace) = 1
  exact Units.mul_inv u

theorem fieldOneFiniteStageThetaEulerResolvent_mul_operator
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageThetaEulerResolvent S *
        fieldOneFiniteStageThetaEulerOperator S = 1 := by
  let u := (fieldOneFiniteStageThetaEulerOperator_isUnit S).unit
  change (↑(u⁻¹) : RHTower.evenSubspace →L[ℂ] RHTower.evenSubspace) *
      (u : RHTower.evenSubspace →L[ℂ] RHTower.evenSubspace) = 1
  exact Units.inv_mul u

/-- Unconditional bounded automorphism realizing the finite Euler multiplier
in equation (57) of Connes--Consani--Moscovici. -/
def fieldOneFiniteStageThetaEulerEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    RHTower.evenSubspace ≃L[ℂ] RHTower.evenSubspace :=
  ContinuousLinearEquiv.mk
    { toFun := fieldOneFiniteStageThetaEulerOperator S
      invFun := fieldOneFiniteStageThetaEulerResolvent S
      left_inv := by
        intro f
        have h := congrArg
          (fun T : RHTower.evenSubspace →L[ℂ] RHTower.evenSubspace => T f)
          (fieldOneFiniteStageThetaEulerResolvent_mul_operator S)
        simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
      right_inv := by
        intro f
        have h := congrArg
          (fun T : RHTower.evenSubspace →L[ℂ] RHTower.evenSubspace => T f)
          (fieldOneFiniteStageThetaEulerOperator_mul_resolvent S)
        simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
      map_add' := (fieldOneFiniteStageThetaEulerOperator S).map_add
      map_smul' := (fieldOneFiniteStageThetaEulerOperator S).map_smul }
    (fieldOneFiniteStageThetaEulerOperator S).continuous
    (fieldOneFiniteStageThetaEulerResolvent S).continuous

/-- Regard a Hilbert-space unitary as a bounded linear equivalence. -/
def fieldOneUnitaryToContinuousLinearEquiv
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (e : E ≃ₗᵢ[ℂ] F) : E ≃L[ℂ] F :=
  ContinuousLinearEquiv.mk e.toLinearEquiv e.continuous e.symm.continuous

/-- Candidate whole-`L²` theta transport obtained from the exact finite Euler
operator, the source-normalized `w_∞`, and the literal finite-stage `w_S`.
This is deliberately called a transport until its action on the Bruhat core is
identified with the literal tensor `σ_S ⊗ f`. -/
def fieldOneFiniteStageThetaTransportEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    RHTower.evenSubspace ≃L[ℂ]
      fieldOneFiniteStageClassModuleOneInvariantSubmodule S :=
  (fieldOneFiniteStageThetaEulerEquiv S).trans
    ((fieldOneUnitaryToContinuousLinearEquiv
      fieldOneEvenToPositiveUnitsHaarUnitary).trans
      (fieldOneUnitaryToContinuousLinearEquiv
        (fieldOneFiniteStageSourceUnitary S).symm))

/-- Exact equation-(57) transport identity.  The theorem is unconditional;
the remaining literal-core theorem must show that this transport is CCM's
`σ_S ⊗ f` map rather than merely an isomorphic model. -/
theorem fieldOneFiniteStageSourceUnitary_thetaTransport
    (S : Finset (HeightOneSpectrum ℤ)) (f : RHTower.evenSubspace) :
    fieldOneFiniteStageSourceUnitary S
        (fieldOneFiniteStageThetaTransportEquiv S f) =
      fieldOneEvenToPositiveUnitsHaarUnitary
        (fieldOneFiniteStageThetaEulerOperator S f) := by
  simp [fieldOneFiniteStageThetaTransportEquiv,
    fieldOneUnitaryToContinuousLinearEquiv,
    fieldOneFiniteStageThetaEulerEquiv]

end

end GaloisForLFunctions.RHTower
