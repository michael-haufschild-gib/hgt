import GaloisForLFunctions.HTGeometry.PlasmaDischargePhotoelectricLaws
import GaloisForLFunctions.RHTower.MobiusIncidenceKMSEntropyProduction
import GaloisForLFunctions.RHTower.SoninEulerFiniteL2Lower
import GaloisForLFunctions.RHTower.ProjectiveWaterFillingOptimizer
import GaloisForLFunctions.RHTower.CCM.CCMPrimeSourceGroundIncidence

/-!
# Corpus bridges for plasma, discharge, and photoelectric laws

Closed specializations identify existing RHTower structures with mechanical forms from
`PlasmaDischargePhotoelectricLaws`:

* finite-incidence inverse temperature is normalized Bjerrum length;
* singleton reciprocal-scale `L²` norm is Debye length;
* positive projective water-filling data satisfy a Debye-like reciprocal-screening balance;
* finite-incidence Boltzmann attenuation is Townsend gain with negative coefficient;
* one-coordinate Weil energy is Einstein photoelectric energy, and existing Weil affinity gives
  exact work-function mixing.

These are algebraic identifications, not physical interpretations of original RHTower objects.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- Corpus inverse temperature becomes Bjerrum length after positive log-coordinate
normalization. -/
theorem finiteIncidenceInverseTemperature_eq_bjerrumLength
    (couplingLog thermalLog : ℝ) :
    _root_.RHTower.finiteIncidenceInverseTemperature
        (Real.exp couplingLog) (Real.exp thermalLog) =
      bjerrumLength couplingLog thermalLog := by
  unfold _root_.RHTower.finiteIncidenceInverseTemperature bjerrumLength
  apply (div_eq_iff (Real.exp_ne_zero thermalLog)).2
  rw [← Real.exp_add]
  exact congrArg Real.exp (by ring)

/-- Existing singleton reciprocal-scale norm is exactly Debye inverse-square-root scale. -/
theorem finiteReciprocalScaleL2Norm_singleton_eq_debyeLength
    (mediumLog chargeDensityLog : ℝ) :
    _root_.RHTower.finiteReciprocalScaleL2Norm
        (fun _ : Fin 1 => Real.exp (chargeDensityLog - mediumLog)) =
      debyeLength mediumLog chargeDensityLog := by
  unfold _root_.RHTower.finiteReciprocalScaleL2Norm debyeLength
  congr 1
  simp only [Fin.sum_univ_one]
  rw [← Real.exp_neg]
  exact congrArg Real.exp (by ring)

/-- Existing reverse-water-filling identity becomes a closed reciprocal-screening mass balance
when weights and level use positive logarithmic coordinates. -/
theorem debyeProjectiveReciprocalMass_exp
    {d : ℕ} (weightLog : Fin d → ℝ) (pivot : Fin d) (levelLog : ℝ) :
    (∑ j, if j = pivot then 0 else
        Real.exp (weightLog j) /
          _root_.RHTower.projectiveWaterScale
            (fun i => Real.exp (weightLog i)) pivot (Real.exp levelLog) j) =
      _root_.RHTower.projectiveWaterMass
        (fun i => Real.exp (weightLog i)) pivot (Real.exp levelLog) := by
  exact _root_.RHTower.projectiveWaterScale_reciprocalMass
    (fun i => Real.exp (weightLog i)) pivot (Real.exp levelLog)
    (fun j => (Real.exp_pos _).le) (Real.exp_pos _)

/-- Finite-incidence Boltzmann factor is Townsend exponential gain with negative ionization
coefficient. Successor labels make imported positivity premises internal. -/
theorem finiteIncidenceBoltzmannWeight_eq_townsendGain
    {α : Type*} (sigmaLog epsilonLog : ℝ) (label : α → ℕ) (i : α) :
    townsendGain
        (-_root_.RHTower.finiteIncidenceInverseTemperature
          (Real.exp sigmaLog) (Real.exp epsilonLog))
        (_root_.RHTower.finiteIncidenceEnergy
          (Real.exp epsilonLog) (fun j => label j + 1) i) =
      ((label i + 1 : ℕ) : ℝ) ^ (-Real.exp sigmaLog) := by
  unfold townsendGain
  exact _root_.RHTower.exp_neg_inverseTemperature_mul_energy
    (Real.exp_pos _) (Real.exp_pos _) (fun _ => Nat.zero_lt_succ _) i

/-- One-coordinate coefficient-pointed Weil energy is photoelectric kinetic energy. -/
theorem weilEnergy_unit_eq_photoelectricKineticEnergy
    (planck workFunction frequency : ℝ) :
    weilEnergy (fun _ : Unit => planck * frequency)
        (fun _ : Fin 1 => fun _ : Unit => 1)
        (fun _ : Fin 1 => workFunction) () =
      photoelectricKineticEnergy planck workFunction frequency := by
  simp [weilEnergy, photoelectricKineticEnergy]

/-- Existing Weil-energy affinity gives exact affine mixing of photoelectric work functions. -/
theorem photoelectricKineticEnergy_affine_workFunction
    (planck frequency work₁ work₂ t : ℝ) :
    photoelectricKineticEnergy planck
        (t * work₁ + (1 - t) * work₂) frequency =
      t * photoelectricKineticEnergy planck work₁ frequency +
        (1 - t) * photoelectricKineticEnergy planck work₂ frequency := by
  simpa [weilEnergy, photoelectricKineticEnergy] using
    (weilEnergy_affine
      (q := fun _ : Unit => planck * frequency)
      (V := fun _ : Fin 1 => fun _ : Unit => 1)
      (b₁ := fun _ : Fin 1 => work₁)
      (b₂ := fun _ : Fin 1 => work₂) t ())

end GaloisForLFunctions.RHTower
