import GaloisForLFunctions.RHTower.CHMDFoldedTemporalSpectrum
import GaloisForLFunctions.RHTower.CHMDTemporalCoefficientCalculus

/-!
# The sole temporal atom of a finite folded source

Splitting the pole-density tail at the spatial base point isolates its
explicit pole oscillation. All remaining terms have zero positive-frequency
cosine coefficients. No arithmetic limit is exchanged with this observation.
-/

open MeasureTheory Filter Set Topology
open scoped Real

namespace RHTower.CHMDChebyshevTransport

open RHTower.CHMDLightCone RHTower.CHMDStage22 GaloisForLFunctions.HTGeometry

noncomputable section

theorem chmdPrimeKernel_hasTemporalCoefficient (s : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    HasTemporalCoefficient (fun y => chmdPrimeKernel y s) lam 0 :=
  ⟨measurable_chmdPrimeKernel_time s, ⟨4 / π, fun y => abs_chmdPrimeKernel_le y s⟩,
    chmdPrimeKernel_temporalCoefficient_zero s hlam⟩

theorem conjugatedKernel_hasTemporalCoefficient (s : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    HasTemporalCoefficient (fun y => conjugatedKernel y s) lam 0 := by
  have h := (chmdPrimeKernel_hasTemporalCoefficient s hlam).const_mul (Real.exp (-(s / 2)))
  simpa only [conjugatedKernel, mul_zero] using h

theorem poleShadow_hasTemporalCoefficient {lam : ℝ} (hlam : 0 < lam) :
    HasTemporalCoefficient poleShadow lam 0 := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      chmdPrimeKernel p.1 p.2 * Real.exp (-(p.2 / 2))) :=
    measurable_chmdPrimeKernel_joint.mul (by fun_prop)
  refine ⟨?_, ⟨8 / π, abs_poleShadow_le⟩, poleShadow_temporalCoefficient_zero hlam⟩
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem remainderFold_hasTemporalCoefficient (v : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    HasTemporalCoefficient (fun y => remainderFold y v) lam 0 := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      ccmPrimeDeficitDilationRemainder p.2 * conjugatedLaplacian p.1 (p.2 + v)) :=
    (measurable_ccmPrimeDeficitDilationRemainder.comp measurable_snd).mul
      (measurable_conjugatedLaplacian_joint.comp
        (measurable_fst.prodMk (measurable_snd.add measurable_const)))
  exact ⟨hm.stronglyMeasurable.integral_prod_right'.measurable,
    ⟨7 * laplacianBound * Real.exp (-(v / 2)), fun y => abs_remainderFold_le y v⟩,
    remainderFold_temporalCoefficient_zero v hlam⟩

/-- The finite spatial portion of the pole-density integral. -/
def poleDensityHead (v y : ℝ) : ℝ :=
  ∫ s in Ioc (0 : ℝ) v, chmdPrimeKernel y s * Real.exp (s / 2)

theorem poleDensityHead_hasTemporalCoefficient (v : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    HasTemporalCoefficient (poleDensityHead v) lam 0 := by
  have hm : Measurable (fun p : ℝ × ℝ => chmdPrimeKernel p.1 p.2 * Real.exp (p.2 / 2)) :=
    measurable_chmdPrimeKernel_joint.mul (by fun_prop)
  have hi : IntegrableOn (fun s : ℝ => (4 / π) * Real.exp (s / 2)) (Ioc (0 : ℝ) v) :=
    (show Continuous (fun s : ℝ => (4 / π) * Real.exp (s / 2)) by fun_prop).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hb : ∀ y s, |chmdPrimeKernel y s * Real.exp (s / 2)| ≤ (4 / π) * Real.exp (s / 2) := by
    intro y s
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (abs_chmdPrimeKernel_le y s) (Real.exp_pos _).le
  have h := HasTemporalCoefficient.of_integral hm hi hb (lam := lam) (L := fun _ => 0)
    (Eventually.of_forall fun s => by
      have h := (chmdPrimeKernel_hasTemporalCoefficient s hlam).const_mul (Real.exp (s / 2))
      have h' := h.congr (fun y => mul_comm _ _)
      simpa only [mul_zero] using h'.limit)
  change HasTemporalCoefficient
    (fun y => ∫ s in Ioc (0 : ℝ) v, chmdPrimeKernel y s * Real.exp (s / 2)) lam 0
  simpa only [integral_zero] using h

theorem integral_poleDensity_tail_eq (y : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    (∫ s in Ioi v, chmdPrimeKernel y s * Real.exp (s / 2)) =
      chmdPoleWave y - poleShadow y - poleDensityHead v y := by
  have hi := integrable_chmdPrimeKernel_mul_exp_half y
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (a := (0 : ℝ)) (b := v) hi.integrableOn hi.integrableOn
  rw [intervalIntegral.integral_of_le hv] at hsplit
  have hp := chmdPoleWave_eq_integral_Ioi_add_poleShadow y
  change (∫ s in Ioi v, chmdPrimeKernel y s * Real.exp (s / 2)) =
    chmdPoleWave y - poleShadow y -
      ∫ s in Ioc (0 : ℝ) v, chmdPrimeKernel y s * Real.exp (s / 2)
  linarith

theorem chmdPoleWave_hasTemporalCoefficient {lam : ℝ} (hlam : 0 < lam) :
    HasTemporalCoefficient chmdPoleWave lam
      (if Real.sqrt (7 / 4 : ℝ) = lam then 1 / Real.cos (1 / 4 : ℝ) ^ 2 else 0) := by
  classical
  have hp : 0 < Real.sqrt (7 / 4 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h : HasTemporalCoefficient
      (fun y => Real.cos (Real.sqrt (7 / 4 : ℝ) * y)) lam
      (if Real.sqrt (7 / 4 : ℝ) = lam then (1 / 2 : ℝ) else 0) :=
    ⟨by fun_prop, ⟨1, fun y => Real.abs_cos_le_one _⟩,
      temporalCosineAverage_cos_tendsto hp hlam⟩
  have h' := (h.const_mul (2 / Real.cos (1 / 4 : ℝ) ^ 2)).congr (g := chmdPoleWave)
    (fun y => by rw [chmdPoleWave_eq, mul_comm (Real.sqrt (7 / 4 : ℝ)) y])
  convert h' using 1
  split_ifs <;> ring

/-- The exact temporal atom of one folded source, with every bounded remainder retained. -/
theorem mobiusFold_hasTemporalCoefficient {v lam : ℝ} (hv : 0 ≤ v) (hlam : 0 < lam) :
    HasTemporalCoefficient (fun y => mobiusFold y v) lam
      (if Real.sqrt (7 / 4 : ℝ) = lam then
        (Real.eulerMascheroniConstant + 1) * Real.exp (-v) / Real.cos (1 / 4 : ℝ) ^ 2 else 0) := by
  classical
  have htail := ((chmdPoleWave_hasTemporalCoefficient hlam).sub
    (poleShadow_hasTemporalCoefficient hlam)).sub (poleDensityHead_hasTemporalCoefficient v hlam)
  have h := ((conjugatedKernel_hasTemporalCoefficient v hlam).const_mul mobiusWaveConstant).add
    ((htail.const_mul (Real.exp (-v))).const_mul (Real.eulerMascheroniConstant + 1))
  have h' := (h.add (remainderFold_hasTemporalCoefficient v hlam)).congr
    (g := fun y => mobiusFold y v) (fun y => by
    rw [mobiusFold_eq y hv, integral_poleDensity_tail_eq y hv])
  convert h' using 1
  split_ifs <;> ring

theorem finite_mobiusFold_hasTemporalCoefficient_zero {ι : Type*}
    (s : Finset ι) (a v : ι → ℝ)
    (hs : ∀ i ∈ s, 0 ≤ v i) {lam : ℝ} (hlam : 0 < lam)
    (hne : Real.sqrt (7 / 4 : ℝ) ≠ lam) :
    HasTemporalCoefficient (fun y => ∑ i ∈ s, a i * mobiusFold y (v i)) lam 0 := by
  have h := HasTemporalCoefficient.finset_sum s (c := fun _ => (0 : ℝ))
    (fun i hi => by
      have h := (mobiusFold_hasTemporalCoefficient (hs i hi) hlam).const_mul (a i)
      simpa only [if_neg hne, mul_zero] using h)
  simpa only [Finset.sum_const_zero] using h

end

end RHTower.CHMDChebyshevTransport
