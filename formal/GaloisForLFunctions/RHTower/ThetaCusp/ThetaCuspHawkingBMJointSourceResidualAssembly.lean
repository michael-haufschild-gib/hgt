import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceResidualCoefficients
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceCutoffCommutator
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointResponse

/-! The entire derived cusp residual is admitted and has an actual constructed joint wave response. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore D4BMGlobalAngularResponse
noncomputable section

private theorem separated_memLp {f : ℝ → ℂ} {g : UpperHalfPlane → ℂ}
    (hf : MemLp f 2 radialMeasure) (hg : MemLp g 2 D4BMModularCore.measure) :
    MemLp (fun p : ℝ × UpperHalfPlane => f p.1*g p.2) 2
      (radialMeasure.prod D4BMModularCore.measure) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × UpperHalfPlane => f p.1*g p.2)
      (radialMeasure.prod D4BMModularCore.measure) :=
    (hf.aestronglyMeasurable.aemeasurable.comp_fst.mul
      hg.aestronglyMeasurable.aemeasurable.comp_snd).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf).mul_prod
    ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
  simpa only [norm_mul,mul_pow] using hi

/-- The complete residual of the explicit full-source lift and all three cut-off principal responses. -/
def cuspResidualForcing (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (p : ℝ × UpperHalfPlane) : ℂ :=
  reducedCoefficient (physicalRate q branch) w a T p.1*squareResidual q (coordinates p.2)+
    ∑ i : Fin 3, cutoffRadialCoefficient q branch w a T i p.1*
      cutoffCommutator (principalExponent q i) (coordinates p.2)

/-- Full joint source admission: native squared-scalar remainder and every cutoff commutator
are retained, with no angular or radial L² premise supplied. -/
theorem cuspResidualForcing_memLp (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) :
    MemLp (cuspResidualForcing q branch w a T) 2 (radialMeasure.prod D4BMModularCore.measure) := by
  have hmain := separated_memLp (reducedCoefficient_memLp (physicalRate q branch) w a T
    (principalChamber_re_pos hw)) (squareResidual_memLp q)
  have hsum := memLp_finsetSum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    separated_memLp (cutoffRadialCoefficient_memLp q branch w a T hw i)
      (cutoffCommutator_memLp (principalExponent q i)))
  exact hmain.add hsum

/-- Actual forcing vector defined from the complete derived residual function. -/
def cuspResidualVector (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) : SpatialSpace :=
  (cuspResidualForcing_memLp q branch w a T hw).toLp (cuspResidualForcing q branch w a T)

theorem cuspResidualVector_ae (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) :
    cuspResidualVector q branch w a T hw =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      cuspResidualForcing q branch w a T :=
  (cuspResidualForcing_memLp q branch w a T hw).coeFn_toLp

/-- Constructed joint response to the actual full cusp residual, at independent frequency. -/
def cuspResidualResponse (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) : jointDomain :=
  jointWaveResponse w (principalChamber_re_pos hw) (cuspResidualVector q branch w a T hw)

theorem cuspResidualResponse_spec (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) :
    JointWaveSolution w (cuspResidualVector q branch w a T hw) (cuspResidualResponse q branch w a T hw) :=
  jointWaveResponse_spec w (principalChamber_re_pos hw) _

/-- Actual operator-domain response to the complete source residual, with the source vector proved admissible. -/
theorem cuspResidualResponse_operator (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) :
    ∃ hmem : jointEmbedding (cuspResidualResponse q branch w a T hw) ∈ jointEnergyOperator.domain,
      jointEnergyOperator ⟨jointEmbedding (cuspResidualResponse q branch w a T hw),hmem⟩ +
        (w^(2 : ℕ)-1) • jointEmbedding (cuspResidualResponse q branch w a T hw) = cuspResidualVector q branch w a T hw :=
  jointWaveResponse_operator w (principalChamber_re_pos hw) _

/-- Quantitative frequency control for the admitted full residual response. -/
theorem cuspResidualResponse_bound (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) :
    ‖jointEmbedding (cuspResidualResponse q branch w a T hw)‖ ≤
      ‖cuspResidualVector q branch w a T hw‖/(w.re*‖w‖) :=
  jointWaveResponse_scalar_bound w (principalChamber_re_pos hw) _

end
end RHTower.D4BMJointSource
