import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPhaseTemperate
import GaloisForLFunctions.RHTower.UnitModulusL2Multiplier
import GaloisForLFunctions.RHTower.TraceClassCyclicity

/-!
# Literal CCM archimedean phase operator product

This file closes the operator-ideal part of Connes--Consani, Proposition 7(iv).  It packages the
literal Gamma scattering phase as a unitary `L²` multiplier, proves its exact multiplication law
with Schwartz symbols, proves the source differential identity

`M_g [H,M_u] = [H,M_{ug}] - [H,M_g] M_u`,

and deduces that `M_g (1/2) M_{u^*}[H,M_u]` is an infinitesimal of every order, hence Schatten one
and trace class.  No phase regularity, trace-ideal, or representation hypothesis is assumed.
-/

noncomputable section

open Complex MeasureTheory
open scoped ENNReal InnerProductSpace Real SchwartzMap

namespace RHTower

private abbrev UnitPhase :=
  GaloisForLFunctions.RHTower.UnitModulusL2Phase

/-- The literal Gamma scattering phase, packaged as a measurable unit-modulus phase on Lebesgue
`L²(ℝ)`. -/
def ccmArchimedeanScatteringUnitPhase :
    UnitPhase ℝ (volume : Measure ℝ) where
  toFun := ccmArchimedeanScatteringPhase
  aestronglyMeasurable :=
    ccmArchimedeanScatteringPhase_hasTemperateGrowth.1.continuous.aestronglyMeasurable
  norm_eq_one :=
    Filter.Eventually.of_forall norm_ccmArchimedeanScatteringPhase

/-- Unitary multiplication by the literal archimedean scattering phase. -/
def ccmArchimedeanScatteringL2Unitary : SoninL2 ≃ₗᵢ[ℂ] SoninL2 :=
  ccmArchimedeanScatteringUnitPhase.mulUnitary

/-- Bounded-operator realization of the scattering-phase unitary. -/
def ccmArchimedeanScatteringL2Multiplier : SoninL2 →L[ℂ] SoninL2 :=
  ccmArchimedeanScatteringL2Unitary.toLinearIsometry.toContinuousLinearMap

theorem ccmArchimedeanScatteringL2Multiplier_ae (x : SoninL2) :
    ccmArchimedeanScatteringL2Multiplier x =ᵐ[volume]
      fun t => ccmArchimedeanScatteringPhase t * x t :=
  ccmArchimedeanScatteringUnitPhase.mulUnitary_ae x

/-- Bounded multiplication by the pointwise conjugate scattering phase `u_infinity^*`. -/
def ccmArchimedeanScatteringConjL2Multiplier : SoninL2 →L[ℂ] SoninL2 :=
  ccmArchimedeanScatteringUnitPhase.conj.mulUnitary.toLinearIsometry.toContinuousLinearMap

theorem ccmArchimedeanScatteringConjL2Multiplier_ae (x : SoninL2) :
    ccmArchimedeanScatteringConjL2Multiplier x =ᵐ[volume]
      fun t => star (ccmArchimedeanScatteringPhase t) * x t :=
  ccmArchimedeanScatteringUnitPhase.conj.mulUnitary_ae x

/-- Multiplying a Schwartz symbol by `u_infinity` and then realizing it on `L²` is composition
with the literal phase multiplier. -/
theorem ccmSchwartzMultiplier_scatteringPhaseMul_eq_phase_mul
    (g : 𝓢(ℝ, ℂ)) :
    ccmSchwartzMultiplier (ccmArchimedeanScatteringPhaseMul g) =
      ccmArchimedeanScatteringL2Multiplier * ccmSchwartzMultiplier g := by
  apply ContinuousLinearMap.ext
  intro x
  change ccmSchwartzMultiplier (ccmArchimedeanScatteringPhaseMul g) x =
    ccmArchimedeanScatteringL2Multiplier (ccmSchwartzMultiplier g x)
  apply Lp.ext
  filter_upwards [
    ccmSchwartzMultiplier_coeFn (ccmArchimedeanScatteringPhaseMul g) x,
    ccmArchimedeanScatteringL2Multiplier_ae (ccmSchwartzMultiplier g x),
    ccmSchwartzMultiplier_coeFn g x]
    with t hleft hphase hg
  rw [hleft, hphase, hg, ccmArchimedeanScatteringPhaseMul_apply]
  ring

/-- Pointwise commutativity gives the reverse operator ordering needed by the source Leibniz
identity. -/
theorem ccmSchwartzMultiplier_scatteringPhaseMul_eq_mul_phase
    (g : 𝓢(ℝ, ℂ)) :
    ccmSchwartzMultiplier (ccmArchimedeanScatteringPhaseMul g) =
      ccmSchwartzMultiplier g * ccmArchimedeanScatteringL2Multiplier := by
  apply ContinuousLinearMap.ext
  intro x
  change ccmSchwartzMultiplier (ccmArchimedeanScatteringPhaseMul g) x =
    ccmSchwartzMultiplier g (ccmArchimedeanScatteringL2Multiplier x)
  apply Lp.ext
  filter_upwards [
    ccmSchwartzMultiplier_coeFn (ccmArchimedeanScatteringPhaseMul g) x,
    ccmSchwartzMultiplier_coeFn g (ccmArchimedeanScatteringL2Multiplier x),
    ccmArchimedeanScatteringL2Multiplier_ae x]
    with t hleft hg hphase
  rw [hleft, hg, hphase, ccmArchimedeanScatteringPhaseMul_apply]
  ring

/-- Every Schwartz multiplier commutes with the bounded conjugate phase multiplier. -/
theorem ccmSchwartzMultiplier_mul_scatteringConj_eq_comm
    (g : 𝓢(ℝ, ℂ)) :
    ccmSchwartzMultiplier g * ccmArchimedeanScatteringConjL2Multiplier =
      ccmArchimedeanScatteringConjL2Multiplier * ccmSchwartzMultiplier g := by
  apply ContinuousLinearMap.ext
  intro x
  change ccmSchwartzMultiplier g (ccmArchimedeanScatteringConjL2Multiplier x) =
    ccmArchimedeanScatteringConjL2Multiplier (ccmSchwartzMultiplier g x)
  apply Lp.ext
  filter_upwards [
    ccmSchwartzMultiplier_coeFn g (ccmArchimedeanScatteringConjL2Multiplier x),
    ccmArchimedeanScatteringConjL2Multiplier_ae x,
    ccmArchimedeanScatteringConjL2Multiplier_ae (ccmSchwartzMultiplier g x),
    ccmSchwartzMultiplier_coeFn g x]
    with t hleft hconj hright hg
  rw [hleft, hconj, hright, hg]
  ring

/-- Quantized differential of the bounded scattering phase `[H,M_u]`. -/
def ccmArchimedeanScatteringL2QuantizedDifferential :
    SoninL2 →L[ℂ] SoninL2 :=
  ccmHardyInvolution * ccmArchimedeanScatteringL2Multiplier -
    ccmArchimedeanScatteringL2Multiplier * ccmHardyInvolution

/-- Exact Connes--Consani source identity
`M_g d u = d(g u) - d(g) M_u`. -/
theorem ccmSchwartzMultiplier_mul_scatteringQuantizedDifferential
    (g : 𝓢(ℝ, ℂ)) :
    ccmSchwartzMultiplier g * ccmArchimedeanScatteringL2QuantizedDifferential =
      ccmQuantizedDifferential (ccmArchimedeanScatteringPhaseMul g) -
        ccmQuantizedDifferential g * ccmArchimedeanScatteringL2Multiplier := by
  unfold ccmArchimedeanScatteringL2QuantizedDifferential ccmQuantizedDifferential
  rw [ccmSchwartzMultiplier_scatteringPhaseMul_eq_mul_phase]
  noncomm_ring

/-- The exact spectral product `M_g[H,M_u]` is an infinitesimal of every order. -/
theorem ccmSchwartzMultiplier_mul_scatteringQuantizedDifferential_isInfinitesimalOfInfiniteOrder
    (g : 𝓢(ℝ, ℂ)) :
    IsInfinitesimalOfInfiniteOrder
      (ccmSchwartzMultiplier g * ccmArchimedeanScatteringL2QuantizedDifferential) := by
  rw [ccmSchwartzMultiplier_mul_scatteringQuantizedDifferential]
  exact
    (ccmQuantizedDifferential_isInfinitesimalOfInfiniteOrder
      (ccmArchimedeanScatteringPhaseMul g)).sub
      ((ccmQuantizedDifferential_isInfinitesimalOfInfiniteOrder g).comp_right
        ccmArchimedeanScatteringL2Multiplier)

/-- Literal spectral operator `1/2 M_{u^*}[H,M_u]` from Proposition 7(iv). -/
def ccmArchimedeanScatteringLogDifferential : SoninL2 →L[ℂ] SoninL2 :=
  (1 / 2 : ℂ) •
    (ccmArchimedeanScatteringConjL2Multiplier *
      ccmArchimedeanScatteringL2QuantizedDifferential)

/-- The source test multiplier can be moved through `M_{u^*}` before applying the differential. -/
theorem ccmSchwartzMultiplier_mul_scatteringLogDifferential
    (g : 𝓢(ℝ, ℂ)) :
    ccmSchwartzMultiplier g * ccmArchimedeanScatteringLogDifferential =
      (1 / 2 : ℂ) •
        (ccmArchimedeanScatteringConjL2Multiplier *
          (ccmSchwartzMultiplier g *
            ccmArchimedeanScatteringL2QuantizedDifferential)) := by
  unfold ccmArchimedeanScatteringLogDifferential
  rw [mul_smul_comm]
  congr 1
  rw [← mul_assoc, ccmSchwartzMultiplier_mul_scatteringConj_eq_comm,
    mul_assoc]

/-- **Connes--Consani Proposition 7(iv), operator-ideal conclusion, strengthened.**  For every
Schwartz Mellin symbol, the literal tested logarithmic phase differential is an infinitesimal of
every order. -/
theorem ccmSchwartzMultiplier_mul_scatteringLogDifferential_isInfinitesimalOfInfiniteOrder
    (g : 𝓢(ℝ, ℂ)) :
    IsInfinitesimalOfInfiniteOrder
      (ccmSchwartzMultiplier g * ccmArchimedeanScatteringLogDifferential) := by
  rw [ccmSchwartzMultiplier_mul_scatteringLogDifferential]
  exact
    ((ccmSchwartzMultiplier_mul_scatteringQuantizedDifferential_isInfinitesimalOfInfiniteOrder g).comp_left
      ccmArchimedeanScatteringConjL2Multiplier).smul (1 / 2 : ℂ)

/-- The literal source operator is Schatten one. -/
theorem ccmSchwartzMultiplier_mul_scatteringLogDifferential_memSchattenClass_one
    (g : 𝓢(ℝ, ℂ)) :
    MemSchattenClass 1
      (ccmSchwartzMultiplier g * ccmArchimedeanScatteringLogDifferential) :=
  (ccmSchwartzMultiplier_mul_scatteringLogDifferential_isInfinitesimalOfInfiniteOrder g).memSchattenClass_one

/-- The literal source operator is trace class in the Hilbert--Schmidt-factorization sense. -/
theorem ccmSchwartzMultiplier_mul_scatteringLogDifferential_isTraceClass
    (g : 𝓢(ℝ, ℂ)) :
    (ccmSchwartzMultiplier g *
      ccmArchimedeanScatteringLogDifferential).IsTraceClass :=
  (ccmSchwartzMultiplier_mul_scatteringLogDifferential_memSchattenClass_one g).one_isTraceClass

end RHTower
