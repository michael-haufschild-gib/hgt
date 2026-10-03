import GaloisForLFunctions.RHTower.PMRamanujanBandSpectralEscape

/-!
# Uniform separation on the literal logarithmic band carrier

The actual critical Mellin vector equals sqrt(2*pi) times one fixed unitary
applied to the actual logarithmic source vector. This exact vector identity
transports the common cofinal separation radius to every fixed physical L2
profile. The source norm is the original complete reciprocal-weight energy.
The small-positive-damping energy upper bound remains open.
-/

open MeasureTheory Set Complex Filter Topology FourierTransform
noncomputable section
namespace RHTower

/-- The actual critical-line transform with its scalar normalization removed. -/
def pmRamanujanCriticalMellinUnitary : SoninL2 ≃ₗᵢ[ℂ] SoninL2 :=
  fourierUnitary.trans (dilationUnitary ((2*Real.pi)⁻¹) (by positivity))

theorem pmRamanujanBandMellinVector_eq_unitary (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X) :
    pmRamanujanBandMellinVector ε X Y hX =
      (Real.sqrt (2*Real.pi) : ℂ) •
        pmRamanujanCriticalMellinUnitary (pmRamanujanBandLogVector ε X Y hX) := by
  let g := pmRamanujanBandLogVector ε X Y hX
  have hrep : (g : ℝ → ℂ) =ᵐ[volume] pmRamanujanBandLogSource ε X Y :=
    (memLp_pmRamanujanBandLogSource ε hX).coeFn_toLp
  have hint : Integrable (g : ℝ → ℂ) :=
    (integrable_pmRamanujanBandLogSource ε hX).congr hrep.symm
  have hf : (fourierUnitary g : ℝ → ℂ) =ᵐ[volume]
      FourierTransform.fourier (pmRamanujanBandLogSource ε X Y) := by
    refine (GaloisForLFunctions.HTGeometry.coeFn_fourierTransform_eq_fourierIntegral
      g hint).trans ?_
    exact Filter.Eventually.of_forall (fun τ => Real.fourier_congr_ae hrep τ)
  have hκ : 0 < 2*Real.pi := by positivity
  have hfc := hf.comp_tendsto
    (realMul_quasiMeasurePreserving ((2*Real.pi)⁻¹) (inv_pos.mpr hκ).ne').tendsto_ae
  have hd := dilation_ae ((2*Real.pi)⁻¹) (inv_pos.mpr hκ) (fourierUnitary g)
  have hs := Lp.coeFn_smul (Real.sqrt (2*Real.pi) : ℂ) (pmRamanujanCriticalMellinUnitary g)
  have hm := (memLp_pmRamanujanBandMellinTrace ε hX (Y := Y)).coeFn_toLp
  have hroot : (Real.sqrt (2*Real.pi) : ℂ) * (Real.sqrt ((2*Real.pi)⁻¹) : ℂ) = 1 := by
    exact_mod_cast sqrt_mul_sqrt_inv (2*Real.pi) hκ
  ext1
  filter_upwards [hm,hs,hd,hfc] with τ hm hs hd hf
  change (pmRamanujanBandMellinVector ε X Y hX : ℝ → ℂ) τ = _ at hm
  rw [hm,hs]
  change pmRamanujanBandMellinTrace ε X Y τ =
    (Real.sqrt (2*Real.pi) : ℂ) *
      dilation ((2*Real.pi)⁻¹) (inv_pos.mpr hκ) (fourierUnitary g) τ
  rw [hd]
  simp only [Function.comp_apply] at hf
  rw [hf,← mul_assoc,hroot,one_mul,pmRamanujanBandMellinTrace_eq_fourier ε hX]
  simp only [div_eq_mul_inv,mul_comm]

/-- The complete band in the original logarithmic spatial Hilbert carrier. -/
def pmRamanujanNaturalBandLogVector (ε X : ℝ) : SoninL2 :=
  if hX : 1 ≤ ⌊X⌋₊ then pmRamanujanBandLogVector ε ⌊X⌋₊ ⌊2*X⌋₊ hX else 0

def pmRamanujanNormalizedBandLogVector (ε X : ℝ) : SoninL2 :=
  ((X^ε : ℝ) : ℂ) • pmRamanujanNaturalBandLogVector ε X

theorem pmRamanujanNormalizedBandMellinVector_eq_unitary (ε X : ℝ) :
    pmRamanujanNormalizedBandMellinVector ε X =
      (Real.sqrt (2*Real.pi) : ℂ) •
        pmRamanujanCriticalMellinUnitary (pmRamanujanNormalizedBandLogVector ε X) := by
  unfold pmRamanujanNormalizedBandMellinVector pmRamanujanNormalizedBandLogVector
    pmRamanujanNaturalBandMellinVector pmRamanujanNaturalBandLogVector
  split_ifs with h
  · rw [pmRamanujanBandMellinVector_eq_unitary ε h,map_smul]
    exact smul_comm _ _ _
  · simp

theorem exists_uniform_pmRamanujanBandPhysical_separation {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ G : SoninL2, ∀ B : ℝ,
      ∃ X : ℝ, B ≤ X ∧ c ≤ ‖pmRamanujanNormalizedBandLogVector ε X-G‖ := by
  obtain ⟨c,hc,h⟩ := exists_uniform_pmRamanujanBandProfile_separation hε
  have hκ : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨c/Real.sqrt (2*Real.pi),div_pos hc hκ,?_⟩
  intro G B
  obtain ⟨X,hX,hd⟩ := h ((Real.sqrt (2*Real.pi) : ℂ) • pmRamanujanCriticalMellinUnitary G) B
  refine ⟨X,hX,?_⟩
  rw [pmRamanujanNormalizedBandMellinVector_eq_unitary,← smul_sub,← map_sub,norm_smul,
    pmRamanujanCriticalMellinUnitary.norm_map,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hκ] at hd
  exact (div_le_iff₀ hκ).mpr (by simpa only [mul_comm] using hd)

theorem not_tendsto_pmRamanujanNormalizedBandLogVector {ε : ℝ} (hε : 0 < ε)
    (G : SoninL2) :
    ¬ Tendsto (pmRamanujanNormalizedBandLogVector ε) atTop (𝓝 G) := by
  intro hlim
  obtain ⟨c,hc,h⟩ := exists_uniform_pmRamanujanBandPhysical_separation hε
  obtain ⟨B,hB⟩ := Metric.tendsto_atTop.mp hlim c hc
  obtain ⟨X,hX,hsep⟩ := h G B
  exact (not_lt_of_ge hsep) (by simpa only [dist_eq_norm] using hB X hX)

end RHTower
