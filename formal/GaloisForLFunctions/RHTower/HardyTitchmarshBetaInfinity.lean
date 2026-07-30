import GaloisForLFunctions.RHTower.L2MellinUnitary
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace RHTower

/-- The critical-line argument `1/2 + i s`. -/
def criticalLineArgument (s : ℝ) : ℂ := (1 / 2 : ℂ) + Complex.I * (s : ℂ)

/-- The archimedean Euler factor on the critical line. -/
def archimedeanEulerFactor (s : ℝ) : ℂ :=
  Complex.Gammaℝ (criticalLineArgument s)

theorem criticalLineArgument_re (s : ℝ) : (criticalLineArgument s).re = 1 / 2 := by
  simp [criticalLineArgument]

theorem archimedeanEulerFactor_ne_zero (s : ℝ) : archimedeanEulerFactor s ≠ 0 := by
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  rw [criticalLineArgument_re]
  norm_num

theorem archimedeanEulerFactor_continuous : Continuous archimedeanEulerFactor := by
  rw [continuous_iff_continuousAt]
  intro s
  have harg : ContinuousAt criticalLineArgument s := by
    change ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ)) s
    fun_prop
  have hinv : ContinuousAt (fun z : ℂ => (Complex.Gammaℝ z)⁻¹)
      (criticalLineArgument s) :=
    Complex.differentiable_Gammaℝ_inv.continuous.continuousAt
  have hne : (Complex.Gammaℝ (criticalLineArgument s))⁻¹ ≠ 0 :=
    inv_ne_zero (archimedeanEulerFactor_ne_zero s)
  have hcont := (hinv.comp' harg).inv₀ hne
  have hfun :
      (fun x : ℝ => (Complex.Gammaℝ (criticalLineArgument x))⁻¹)⁻¹ =
        archimedeanEulerFactor := by
    funext x
    simp [archimedeanEulerFactor]
  rw [hfun] at hcont
  exact hcont

/-- The critical-line density `|E_infinity(s)|^{-2}`. -/
def archimedeanEulerWeight (s : ℝ) : ℝ≥0 := (‖archimedeanEulerFactor s‖₊)⁻¹ ^ 2

theorem archimedeanEulerWeight_ne_zero (s : ℝ) : archimedeanEulerWeight s ≠ 0 := by
  exact pow_ne_zero _ (inv_ne_zero (nnnorm_ne_zero_iff.mpr (archimedeanEulerFactor_ne_zero s)))

theorem archimedeanEulerWeight_continuous : Continuous archimedeanEulerWeight := by
  rw [continuous_iff_continuousAt]
  intro s
  exact ((archimedeanEulerFactor_continuous.continuousAt.nnnorm).inv₀
    (nnnorm_ne_zero_iff.mpr (archimedeanEulerFactor_ne_zero s))).pow 2

theorem archimedeanEulerWeight_measurable : Measurable archimedeanEulerWeight :=
  archimedeanEulerWeight_continuous.measurable

/-- Lebesgue measure weighted by `|E_infinity|^{-2}`. -/
def archimedeanWeightedMeasure : Measure ℝ :=
  (volume : Measure ℝ).withDensity fun s => (archimedeanEulerWeight s : ℝ≥0∞)

abbrev SpectralL2 := Lp (α := ℝ) ℂ 2
abbrev ArchimedeanWeightedL2 := Lp (α := ℝ) ℂ 2 archimedeanWeightedMeasure

theorem archimedeanEulerWeight_mul_norm_sq (s : ℝ) (z : ℂ) :
    (archimedeanEulerWeight s : ℝ) * ‖archimedeanEulerFactor s * z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [norm_mul]
  change ‖archimedeanEulerFactor s‖⁻¹ ^ 2 *
      (‖archimedeanEulerFactor s‖ * ‖z‖) ^ 2 = ‖z‖ ^ 2
  field_simp [norm_ne_zero_iff.mpr (archimedeanEulerFactor_ne_zero s)]

theorem norm_archimedeanEulerFactor_inv_mul_sq (s : ℝ) (z : ℂ) :
    ‖(archimedeanEulerFactor s)⁻¹ * z‖ ^ 2 =
      (archimedeanEulerWeight s : ℝ) * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_inv]
  change (‖archimedeanEulerFactor s‖⁻¹ * ‖z‖) ^ 2 =
    ‖archimedeanEulerFactor s‖⁻¹ ^ 2 * ‖z‖ ^ 2
  ring

theorem archimedeanWeightedMeasure_absolutelyContinuous :
    archimedeanWeightedMeasure ≪ (volume : Measure ℝ) := by
  exact withDensity_absolutelyContinuous _ _

theorem volume_absolutelyContinuous_archimedeanWeightedMeasure :
    (volume : Measure ℝ) ≪ archimedeanWeightedMeasure := by
  unfold archimedeanWeightedMeasure
  apply withDensity_absolutelyContinuous'
  · exact archimedeanEulerWeight_measurable.coe_nnreal_ennreal.aemeasurable
  · filter_upwards with s
    exact_mod_cast archimedeanEulerWeight_ne_zero s

theorem memLp_archimedeanEulerFactor_mul (f : SpectralL2) :
    MemLp (fun s => archimedeanEulerFactor s * f s) 2 archimedeanWeightedMeasure := by
  rw [memLp_two_iff_integrable_sq_norm]
  · unfold archimedeanWeightedMeasure
    rw [integrable_withDensity_iff_integrable_smul (E := ℝ)
      archimedeanEulerWeight_measurable]
    have hf : Integrable (fun s => ‖f s‖ ^ 2) (volume : Measure ℝ) :=
      (memLp_two_iff_integrable_sq_norm (Lp.memLp f).1).mp (Lp.memLp f)
    have hfun :
        (fun s => archimedeanEulerWeight s • ‖archimedeanEulerFactor s * f s‖ ^ 2) =
          fun s => ‖f s‖ ^ 2 := by
      funext s
      simpa [NNReal.smul_def] using archimedeanEulerWeight_mul_norm_sq s (f s)
    rw [hfun]
    exact hf
  · exact archimedeanEulerFactor_continuous.aestronglyMeasurable.mul
      (AEStronglyMeasurable.mono_ac archimedeanWeightedMeasure_absolutelyContinuous
        (Lp.memLp f).1)

theorem memLp_archimedeanEulerFactor_inv_mul (g : ArchimedeanWeightedL2) :
    MemLp (fun s => (archimedeanEulerFactor s)⁻¹ * g s) 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq_norm]
  · have hgWeighted : Integrable (fun s => ‖g s‖ ^ 2) archimedeanWeightedMeasure :=
      (memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).mp (Lp.memLp g)
    unfold archimedeanWeightedMeasure at hgWeighted
    rw [integrable_withDensity_iff_integrable_smul (E := ℝ)
      archimedeanEulerWeight_measurable] at hgWeighted
    have hfun :
        (fun s => ‖(archimedeanEulerFactor s)⁻¹ * g s‖ ^ 2) =
          fun s => archimedeanEulerWeight s • ‖g s‖ ^ 2 := by
      funext s
      simpa [NNReal.smul_def] using norm_archimedeanEulerFactor_inv_mul_sq s (g s)
    rw [hfun]
    exact hgWeighted
  · exact (archimedeanEulerFactor_continuous.inv₀ archimedeanEulerFactor_ne_zero).aestronglyMeasurable.mul
      (AEStronglyMeasurable.mono_ac volume_absolutelyContinuous_archimedeanWeightedMeasure
        (Lp.memLp g).1)

theorem archimedeanEulerWeight_mul_enorm_rpow_two (s : ℝ) (z : ℂ) :
    (archimedeanEulerWeight s : ℝ≥0∞) *
        ‖archimedeanEulerFactor s * z‖ₑ ^ (2 : ℝ) =
      ‖z‖ₑ ^ (2 : ℝ) := by
  simp only [archimedeanEulerWeight, enorm_eq_nnnorm, ENNReal.rpow_two, nnnorm_mul]
  have h0 : (‖archimedeanEulerFactor s‖₊ : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast nnnorm_ne_zero_iff.mpr (archimedeanEulerFactor_ne_zero s)
  have hnn : ‖archimedeanEulerFactor s‖₊ ≠ 0 :=
    nnnorm_ne_zero_iff.mpr (archimedeanEulerFactor_ne_zero s)
  have htop : (‖archimedeanEulerFactor s‖₊ : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  push_cast
  rw [ENNReal.coe_inv hnn]
  rw [← mul_pow, ← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]

/-- Multiplication by `E_infinity` as a point of the weighted `L²` space. -/
def betaInfinityAux (f : SpectralL2) : ArchimedeanWeightedL2 :=
  (memLp_archimedeanEulerFactor_mul f).toLp _

theorem betaInfinityAux_ae (f : SpectralL2) :
    betaInfinityAux f =ᵐ[archimedeanWeightedMeasure]
      fun s => archimedeanEulerFactor s * f s :=
  (memLp_archimedeanEulerFactor_mul f).coeFn_toLp

/-- Multiplication by `E_infinity^{-1}` as a point of ordinary spectral `L²`. -/
def betaInfinityInvAux (g : ArchimedeanWeightedL2) : SpectralL2 :=
  (memLp_archimedeanEulerFactor_inv_mul g).toLp _

theorem betaInfinityInvAux_ae (g : ArchimedeanWeightedL2) :
    betaInfinityInvAux g =ᵐ[volume]
      fun s => (archimedeanEulerFactor s)⁻¹ * g s :=
  (memLp_archimedeanEulerFactor_inv_mul g).coeFn_toLp

theorem betaInfinityAux_add (f g : SpectralL2) :
    betaInfinityAux (f + g) = betaInfinityAux f + betaInfinityAux g := by
  apply Lp.ext
  have hinput := archimedeanWeightedMeasure_absolutelyContinuous.ae_eq (Lp.coeFn_add f g)
  filter_upwards [betaInfinityAux_ae (f + g), betaInfinityAux_ae f,
    betaInfinityAux_ae g, hinput,
    Lp.coeFn_add (betaInfinityAux f) (betaInfinityAux g)] with s hsum hf hg hin hout
  rw [hsum, hout, hin]
  change archimedeanEulerFactor s * (f s + g s) =
    betaInfinityAux f s + betaInfinityAux g s
  rw [hf, hg]
  ring

theorem betaInfinityAux_smul (c : ℂ) (f : SpectralL2) :
    betaInfinityAux (c • f) = c • betaInfinityAux f := by
  apply Lp.ext
  have hinput := archimedeanWeightedMeasure_absolutelyContinuous.ae_eq (Lp.coeFn_smul c f)
  filter_upwards [betaInfinityAux_ae (c • f), betaInfinityAux_ae f,
    hinput, Lp.coeFn_smul c (betaInfinityAux f)] with s hcf hf hin hout
  rw [hcf, hout, hin]
  change archimedeanEulerFactor s * (c * f s) = c * betaInfinityAux f s
  rw [hf]
  ring

theorem eLpNorm_archimedeanEulerFactor_mul (f : SpectralL2) :
    eLpNorm (fun s => archimedeanEulerFactor s * f s) 2 archimedeanWeightedMeasure =
      eLpNorm (fun s => f s) 2 (volume : Measure ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  unfold archimedeanWeightedMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable (volume : Measure ℝ)
    archimedeanEulerWeight_measurable.coe_nnreal_ennreal
    (Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  apply lintegral_congr
  intro s
  simpa only [Pi.mul_apply] using
    archimedeanEulerWeight_mul_enorm_rpow_two s (f s)

theorem norm_betaInfinityAux (f : SpectralL2) : ‖betaInfinityAux f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (betaInfinityAux_ae f),
    eLpNorm_archimedeanEulerFactor_mul]

def betaInfinityLinear : SpectralL2 →ₗ[ℂ] ArchimedeanWeightedL2 where
  toFun := betaInfinityAux
  map_add' := betaInfinityAux_add
  map_smul' c f := by
    simpa using betaInfinityAux_smul c f

def betaInfinityIsometry : SpectralL2 →ₗᵢ[ℂ] ArchimedeanWeightedL2 where
  __ := betaInfinityLinear
  norm_map' := norm_betaInfinityAux

/-- The concrete archimedean factor `beta_infinity : f ↦ E_infinity f`. -/
def betaInfinityUnitary : SpectralL2 ≃ₗᵢ[ℂ] ArchimedeanWeightedL2 where
  __ := betaInfinityIsometry
  invFun := betaInfinityInvAux
  left_inv f := by
    change betaInfinityInvAux (betaInfinityAux f) = f
    apply Lp.ext
    have hbeta := volume_absolutelyContinuous_archimedeanWeightedMeasure.ae_eq
      (betaInfinityAux_ae f)
    filter_upwards [betaInfinityInvAux_ae (betaInfinityAux f), hbeta] with s hout hin
    rw [hout, hin, ← mul_assoc, inv_mul_cancel₀ (archimedeanEulerFactor_ne_zero s), one_mul]
  right_inv g := by
    change betaInfinityAux (betaInfinityInvAux g) = g
    apply Lp.ext
    have hinv := archimedeanWeightedMeasure_absolutelyContinuous.ae_eq
      (betaInfinityInvAux_ae g)
    filter_upwards [betaInfinityAux_ae (betaInfinityInvAux g), hinv] with s hout hin
    rw [hout, hin, ← mul_assoc, mul_inv_cancel₀ (archimedeanEulerFactor_ne_zero s), one_mul]

theorem betaInfinityUnitary_ae (f : SpectralL2) :
    betaInfinityUnitary f =ᵐ[archimedeanWeightedMeasure]
      fun s => archimedeanEulerFactor s * f s :=
  betaInfinityAux_ae f

theorem betaInfinityUnitary_symm_ae (g : ArchimedeanWeightedL2) :
    betaInfinityUnitary.symm g =ᵐ[volume]
      fun s => (archimedeanEulerFactor s)⁻¹ * g s :=
  betaInfinityInvAux_ae g

/-- The prime phase multiplier on the archimedean-weighted spectral line. -/
def weightedMellinCharacterMulUnitary (p : ℝ) :
    ArchimedeanWeightedL2 ≃ₗᵢ[ℂ] ArchimedeanWeightedL2 :=
  betaInfinityUnitary.symm.trans
    ((MellinL2.mellinCharacterMulUnitary p).trans betaInfinityUnitary)

/-- `beta_infinity` intertwines the ordinary and archimedean-weighted prime phases. -/
theorem betaInfinity_intertwines_mellinCharacter (p : ℝ) (f : SpectralL2) :
    weightedMellinCharacterMulUnitary p (betaInfinityUnitary f) =
      betaInfinityUnitary (MellinL2.mellinCharacterMulUnitary p f) := by
  simp [weightedMellinCharacterMulUnitary]

/-- The conjugated weighted phase is still pointwise multiplication by `p^(i s)`. -/
theorem weightedMellinCharacterMulUnitary_ae (p : ℝ) (g : ArchimedeanWeightedL2) :
    weightedMellinCharacterMulUnitary p g =ᵐ[archimedeanWeightedMeasure]
      fun s => MellinL2.mellinCharacter p s * g s := by
  change betaInfinityUnitary
      (MellinL2.mellinCharacterMulUnitary p (betaInfinityUnitary.symm g))
    =ᵐ[archimedeanWeightedMeasure] _
  have hphase := archimedeanWeightedMeasure_absolutelyContinuous.ae_eq
    (MellinL2.mellinCharacterMulUnitary_ae p (betaInfinityUnitary.symm g))
  have hinv := archimedeanWeightedMeasure_absolutelyContinuous.ae_eq
    (betaInfinityUnitary_symm_ae g)
  filter_upwards [betaInfinityUnitary_ae
    (MellinL2.mellinCharacterMulUnitary p (betaInfinityUnitary.symm g)),
    hphase, hinv] with s hout hphase hinv
  rw [hout, hphase, hinv]
  field_simp [archimedeanEulerFactor_ne_zero s]

/-- The inverse weighted phase is pointwise multiplication by `p^(-i s)`. -/
theorem weightedMellinCharacterMulUnitary_symm_ae
    (p : ℝ) (g : ArchimedeanWeightedL2) :
    (weightedMellinCharacterMulUnitary p).symm g =ᵐ[archimedeanWeightedMeasure]
      fun s => (MellinL2.mellinCharacter p s)⁻¹ * g s := by
  have h := weightedMellinCharacterMulUnitary_ae p
    ((weightedMellinCharacterMulUnitary p).symm g)
  rw [(weightedMellinCharacterMulUnitary p).apply_symm_apply] at h
  filter_upwards [h] with s hs
  rw [hs]
  field_simp [MellinL2.mellinCharacter]

end RHTower
