import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.LimitLaw.FiniteLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.PhysicalLimit
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-! # Weak limits of the energy and signed pair gap in a frozen Gaussian path -/
open MeasureTheory ProbabilityTheory Filter Finset Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section

/-- Energy normalized by the square root of the number of sites. -/
def scaledEnergy {n : ℕ} (u : PathShell n) (i : Fin (n+2)→Bool) :=
  (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues i/sqrt (n+2:ℕ)

/-- Signed gap between two uniformly and independently sampled energy indices. -/
def scaledGap {n : ℕ} (u : PathShell n) (p : (Fin (n+2)→Bool)×(Fin (n+2)→Bool)) :=
  scaledEnergy u p.1-scaledEnergy u p.2

private theorem scaled_trace {n : ℕ} (u : PathShell n) (s : ℝ) :
    energyCharacteristic (scaledEnergy u) s = shellTrace u (-s/sqrt (n+2:ℕ)) := by
  rw [shellTrace_eq_energyCharacteristic]
  unfold energyCharacteristic
  congr 1
  apply sum_congr rfl
  intro i _
  congr 2
  dsimp only [scaledEnergy]
  push_cast
  ring

private theorem characteristic_limit {v : NNReal} (s : ℝ) :
    charFun (gaussianReal 0 v) s=(exp (-((v:ℝ)*s^2/2)):ℂ) := by
  rw [charFun_gaussianReal,Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Uniform eigenline sampling gives a Gaussian energy of variance twelve.
Independent sampling of two lines gives a Gaussian signed gap of variance
twenty-four. Both weak limits hold on the same full-measure set. -/
theorem gaussian_energy_and_gap_laws :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      Tendsto (fun n => listLaw (scaledEnergy (pathPauliDisorderShell ω n))) atTop
        (𝓝 ⟨gaussianReal 0 12,inferInstance⟩) ∧
      Tendsto (fun n => listLaw (scaledGap (pathPauliDisorderShell ω n))) atTop
        (𝓝 ⟨gaussianReal 0 24,inferInstance⟩) := by
  filter_upwards [gaussian_scaled_characteristic] with ω hw
  let u (n : ℕ) := pathPauliDisorderShell ω n
  have h (s : ℝ) : Tendsto (fun n => energyCharacteristic (scaledEnergy (u n)) s)
      atTop (𝓝 (exp (-6*s^2):ℂ)) := by
    simpa only [scaled_trace,neg_sq,u] using hw (-s)
  constructor
  · apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro s
    simp only [charFun_listLaw,ProbabilityMeasure.coe_mk,characteristic_limit,NNReal.coe_ofNat]
    convert h s using 2
    congr 2
    ring
  · apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro s
    simp only [charFun_listLaw,ProbabilityMeasure.coe_mk,characteristic_limit,NNReal.coe_ofNat]
    have hh := (h s).mul (h (-s))
    simp only [neg_sq,←Complex.ofReal_mul,←exp_add] at hh
    rw [show -6*s^2 + -6*s^2= -(24*s^2/2) by ring] at hh
    exact hh.congr fun n => (gap_characteristic (scaledEnergy (u n)) s).symm

#print axioms gaussian_energy_and_gap_laws
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
