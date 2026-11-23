import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.QuadraticReading
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RelativeGibbs.ExteriorPaths
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.IndependentOmissions
import GaloisForLFunctions.HTGeometry.SchattenOneBanach

/-! # Connected spectra of independent arithmetic-progression omissions -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set ContinuousLinearMap

variable {r : ℕ}

private theorem lane_ne (u : Fin r → MissingWave) (i : Fin r) : laneWaves u i ≠ 0 :=
  fun h => missingWave_ne_zero (u i) ((extendModes (progression i)).injective (h.trans (map_zero _).symm))

private theorem lane_orth (u : Fin r → MissingWave) (i j : Fin r) (h : i ≠ j) :
    inner ℂ (laneWaves u i) (laneWaves u j) = 0 := extendModes_orthogonal (progression_separate h) _ _

def laneSpectrum (u : Fin r → MissingWave) : SpectralBand r :=
  physicalSpectrum (omitFamily (laneWaves u)) (missingDimension_family (lane_ne u) (lane_orth u))
    (laneFamily_conserves u)

theorem lane_quadratic (u : Fin r → MissingWave) :
    relativeReading quadraticResponse (laneSpectrum u) = ∑ i, lineLoss (laneWaves u i) := by
  rw [laneSpectrum,quadratic_physicalReading]
  apply traceLoss_family (lane_ne u) (lane_orth u)
  intro i j hij
  obtain ⟨a,ha⟩ := heat_extendModes (progression i) (u i).val
  obtain ⟨b,hb⟩ := heat_extendModes (progression j) (u j).val
  change inner ℂ (criticalOperator (extendModes (progression i) _)) (criticalOperator (extendModes (progression j) _)) = 0
  rw [ha,hb]
  exact extendModes_orthogonal (progression_separate hij) a b

theorem continuous_laneSpectrum (r : ℕ) : Continuous (laneSpectrum (r := r)) := by
  have hw (i : Fin r) : Continuous (fun u : Fin r → MissingWave => laneWaves u i) :=
    (extendModes (progression i)).continuous.comp (continuous_subtype_val.comp (continuous_apply i))
  have hc (i : Fin r) : Continuous (fun u : Fin r → MissingWave => lineCorrection (laneWaves u i)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hroot := ContinuousAt.comp (f := fun w : Fin r → MissingWave => laneWaves w i) (x := u)
      (continuousAt_omitted_root (lane_ne u i)) (hw i).continuousAt
    exact continuousAt_const.sub (hroot.pow 2)
  have hB : Continuous (fun u : Fin r → MissingWave => (projected (omitFamily (laneWaves u)))^2) := by
    have he := funext (fun u : Fin r → MissingWave => family_square (lane_ne u) (lane_orth u))
    rw [he]
    exact continuous_const.sub (continuous_finsetSum _ (fun i _ => hc i))
  apply continuous_pi
  intro i
  exact ((_root_.RHTower.approxNumber_lipschitz i).continuous.comp hB).subtype_mk _

theorem lane_reading_mem (f : SpectralResponse) (u : Fin r → MissingWave) :
    relativeReading f (laneSpectrum u) ∈ responseAtRank f r :=
  ⟨omitFamily (laneWaves u),missingDimension_family (lane_ne u) (lane_orth u),laneFamily_conserves u,rfl⟩

def laneSpectra (r : ℕ) : Set (SpectralBand r) := range (laneSpectrum (r := r))

theorem laneSpectra_preconnected (r : ℕ) : IsPreconnected (laneSpectra r) :=
  isPreconnected_range (continuous_laneSpectrum r)

#print axioms continuous_laneSpectrum
#print axioms laneSpectra_preconnected

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
