import GaloisForLFunctions.RHTower.ChiRamanujanMovingLabelRows
/-!
# Full growing labelled near-pole source

The original completed source has its full joint logarithmic near-pole limit,
retaining both label exclusions, the allowed first/second coincidence and both
original coprime cofactors. Exact collision assembly, actual row limits,
vanishing collision moments, Mertens normalization and the unlabelled joint
cofactor law discharge every ingredient. Convergence is pointwise in fixed
nonzero complex displacements. Physical Mellin transfer and signed axes
cancellation are not consequences asserted by this module.
-/

open scoped BigOperators Topology
open Filter MeasureTheory
noncomputable section
namespace RHTower.BAGTrace

private theorem growing_masked_response_eq (u v : ℂ) (N : ℕ) :
    criticalMaskedMellinResponse (Sieve.primeSubtypeLE N)
      (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ)) =
    criticalMellinResponseRow 0 u v N*criticalMellinResponseRow 1 u v N*criticalMellinResponseRow 2 u v N+
    criticalMellinResponseRow 2 u v N*criticalMellinCollisionMoment 0 u v N-
    criticalMellinResponseRow 0 u v N*criticalMellinCollisionMoment 1 u v N-
    criticalMellinResponseRow 1 u v N*criticalMellinCollisionMoment 2 u v N+
    criticalMellinCollisionMoment 3 u v N := by
  simpa [criticalMellinResponseRow,criticalMellinCollisionMoment,criticalMellinResponse] using
    criticalMaskedMellinResponse_expansion (Sieve.primeSubtypeLE N)
      (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ))

/-- The complete masked labelled response has its growing logarithmic cubic limit;
all pair and triple collisions have been included and proved negligible. -/
theorem criticalMaskedMellinResponse_logScale_tendsto (u v : ℂ) :
    Tendsto (fun N : ℕ => criticalMaskedMellinResponse (Sieve.primeSubtypeLE N)
      (1+u/(Real.log N : ℂ)) (1+v/(Real.log N : ℂ))/(Real.log N : ℂ)^3) atTop
      (𝓝 ((∫ t in (0 : ℝ)..1,criticalMellinResponseLeading 0 u v t)*
        (∫ t in (0 : ℝ)..1,criticalMellinResponseLeading 1 u v t)*
        (∫ t in (0 : ℝ)..1,criticalMellinResponseLeading 2 u v t))) := by
  have ha := criticalMellinResponseRow_tendsto 0 u v
  have hb := criticalMellinResponseRow_tendsto 1 u v
  have hc := criticalMellinResponseRow_tendsto 2 u v
  have hd0 := criticalMellinCollisionMoment_tendsto 0 u v
  have hd1 := criticalMellinCollisionMoment_tendsto 1 u v
  have hd2 := criticalMellinCollisionMoment_tendsto 2 u v
  have hd3 := criticalMellinCollisionMoment_tendsto 3 u v
  have h := (((((ha.mul hb).mul hc).add ((hc.mul hd0).mul criticalLogScaleInv_tendsto_zero)).sub
    ((ha.mul hd1).mul criticalLogScaleInv_tendsto_zero)).sub
    ((hb.mul hd2).mul criticalLogScaleInv_tendsto_zero)).add (hd3.mul (criticalLogScaleInv_tendsto_zero.pow 2))
  simp only [mul_zero,zero_mul,add_zero,sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [growing_masked_response_eq]
  have hlog : (Real.log N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  field_simp

/-- Full original growing labelled source, both original coprime cofactors,
and both moving pole factors: the complete joint near-pole law. -/
theorem criticalCompletedConeEuler_logScale_tendsto (u v : ℂˣ) :
    Tendsto (fun N : ℕ => ((u : ℂ)/(Real.log N : ℂ))*((v : ℂ)/(Real.log N : ℂ))*
      criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
        (1+(u : ℂ)/(Real.log N : ℂ)) (1+(v : ℂ)/(Real.log N : ℂ))) atTop
      (𝓝 ((Real.exp (-Real.eulerMascheroniConstant) : ℂ)^3 *
        ((∫ t in (0 : ℝ)..1,criticalMellinResponseLeading 0 u v t)*
         (∫ t in (0 : ℝ)..1,criticalMellinResponseLeading 1 u v t)*
         (∫ t in (0 : ℝ)..1,criticalMellinResponseLeading 2 u v t)) *
        Complex.exp ((∫ t in (0 : ℝ)..1,criticalEulerProfile u t)+
          (∫ t in (0 : ℝ)..1,criticalEulerProfile v t)-
          (∫ t in (0 : ℝ)..1,criticalEulerProfile ((u : ℂ)-(v : ℂ)) t)-
          (∫ t in (0 : ℝ)..1,criticalEulerProfile ((v : ℂ)-(u : ℂ)) t)))) := by
  have h := ((criticalPrimeNormalization_logScale_tendsto.pow 3).mul
    (criticalMaskedMellinResponse_logScale_tendsto u v)).mul
    (criticalMovingCompletedTrace_tendsto u v)
  apply h.congr'
  filter_upwards [criticalCompletedConeEuler_moving_response u v,eventually_ge_atTop 2] with N hN hN2
  rw [hN]
  have hlog : (Real.log N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  field_simp

end RHTower.BAGTrace
