import GaloisForLFunctions.SurfaceOfSpecZ.TheArchimedeanSelfEnergyIsLogarithmic
import GaloisForLFunctions.RHTower.WeilArchimedeanExactForm
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The Green damping on smooth probes

The divergent coefficient of the archimedean Green energy is the actual L² mass of
the probe. Its finite part is minus the Lévy energy. This identifies the continuum
normalization before coupling it to an arithmetic torsion form.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open SurfaceOfSpecZ _root_.RHTower
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm

/-- The archimedean Green energy of a real probe. -/
def smoothGreenEnergy (r : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ u, archDamped r u * autocorr f u

/-- The autocorrelation deficit is the integrable Lévy jump energy, on the whole line. -/
theorem smoothGreen_deficit (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Integrable (fun u => archProfile |u| * (autocorr f 0 - autocorr f u)) ∧
      (∫ u, archProfile |u| * (autocorr f 0 - autocorr f u)) = levyEnergy f := by
  let F : ℝ → ℝ := fun u => archProfile u * (autocorr f 0 - autocorr f u)
  have heq (u : ℝ) : F u =
      (1 / 2 : ℝ) * (archLevyDensity u * ∫ v, (f v - f (v + u)) ^ 2) := by
    rw [ArchimedeanAnomaly.integral_sub_shift_sq hfc hf.continuous]
    change archLevyDensity u * (autocorr f 0 - autocorr f u) = _
    ring
  have hF : IntegrableOn F (Ioi 0) := by
    have hi : IntegrableOn
        (fun u => (1 / 2 : ℝ) * (archLevyDensity u * ∫ v, (f v - f (v + u)) ^ 2))
        (Ioi 0) := (integrableOn_levyIntegrand hf hfc).const_mul (1 / 2 : ℝ)
    exact hi.congr_fun (fun u _ => (heq u).symm) measurableSet_Ioi
  have hpos : IntegrableOn (fun u => F |u|) (Ioi 0) :=
    hF.congr_fun (fun u hu => by rw [abs_of_pos hu]) measurableSet_Ioi
  have hneg : IntegrableOn (fun u => F |u|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun u : ℝ => -u := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have hall : Integrable (fun u => F |u|) := by
    have h := hneg.union hpos
    rwa [Iic_union_Ioi, integrableOn_univ] at h
  have heven : (fun u => F |u|) =
      (fun u => archProfile |u| * (autocorr f 0 - autocorr f u)) := by
    funext u
    dsimp only [F]
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_nonpos hu, autocorr_neg]
  constructor
  · rwa [← heven]
  · rw [← heven, integral_comp_abs]
    simp_rw [heq]
    rw [integral_const_mul]
    change 2 * (1 / 2 * levyEnergy f) = levyEnergy f
    ring

/-- Removing exactly the L² self-energy leaves minus the Lévy energy. -/
theorem tendsto_smoothGreenEnergy_sub_mass (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Tendsto (fun r => smoothGreenEnergy r f - (∫ u, f u ^ 2) * selfEnergy r)
      (𝓝[<] 1) (𝓝 (-levyEnergy f)) := by
  have hcorr : Integrable (autocorr f) :=
    (continuous_autocorr hf hfc).integrable_of_hasCompactSupport (hasCompactSupport_autocorr hfc)
  have hmax (u : ℝ) : autocorr f u ≤ autocorr f 0 := by
    have h : (0 : ℝ) ≤ ∫ v, (f v - f (v + u)) ^ 2 :=
      integral_nonneg (fun v : ℝ => sq_nonneg (f v - f (v + u)))
    rw [ArchimedeanAnomaly.integral_sub_shift_sq hfc hf.continuous] at h
    linarith
  have hdef := smoothGreen_deficit f hf hfc
  have h := tendsto_renormalized_selfEnergy hcorr hmax hdef.1
  rw [hdef.2] at h
  have hzero : autocorr f 0 = ∫ u, f u ^ 2 := by simp [autocorr, pow_two]
  simpa only [smoothGreenEnergy, hzero] using h

end GaloisForLFunctions.HyperbolicArakelovTheory

#print axioms GaloisForLFunctions.HyperbolicArakelovTheory.tendsto_smoothGreenEnergy_sub_mass
