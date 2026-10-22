import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonPreimage
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusFourierCommutator

/-!
# Poisson boundaries lie in the kernel of the commutator

On a Poisson boundary both halves of the commutator collapse to the boundary function: the
canonical preimage of `Z f` is `f` itself, and the preimage of the exchanged collar `J(Zf) = Z(ℱf)`
is `ℱ f`.  The commutator is therefore the difference between the distributional Fourier transform
of `f` and the classical one, which is zero.

This is the boundary inclusion `Z(H_∩) ⊆ ker 𝔖_μ` of the exact-kernel theorem.

* `deningerL1Distribution_congr` : the `L¹` distribution only sees the almost-everywhere class.
* `deningerPreimageDistribution_poissonSource` : **`E f_{Zf} = f` as a distribution.**
* `deningerMobiusCommutator_poissonSource` : **`𝔖_μ(Zf) = 0`.**
-/

namespace RHTower

open MeasureTheory SchwartzMap FourierTransform GaloisForLFunctions

noncomputable section

/-- The `L¹` distribution only sees the almost-everywhere class of its density. -/
theorem deningerL1Distribution_congr {F G : ℝ → ℂ} (hF : Integrable F) (hG : Integrable G)
    (hFG : F =ᵐ[volume] G) : deningerL1Distribution hF = deningerL1Distribution hG := by
  ext g
  rw [deningerL1Distribution_apply, deningerL1Distribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [hFG] with x hx
  rw [hx]

/-- The `L¹` distribution of a Schwartz function is its canonical distribution. -/
theorem deningerL1Distribution_schwartz (f : 𝓢(ℝ, ℂ)) (hf : Integrable (f : ℝ → ℂ)) :
    deningerL1Distribution hf = (f : 𝓢'(ℝ, ℂ)) := by
  ext g
  rw [deningerL1Distribution_apply, SchwartzMap.coe_apply]

/-- **The even extension of the preimage of a Poisson boundary is the boundary**, away from the
origin — and hence almost everywhere. -/
theorem deningerEvenPreimage_poissonSource_ae (h : DeningerMeyerCap) :
    deningerEvenPreimage ((deningerPoissonSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))
      =ᵐ[volume] (((h : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
  have hnull : (volume : Measure ℝ) {(0 : ℝ)} = 0 := by simp
  filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx
  have hx0 : x ≠ 0 := by
    intro hcon
    exact hx (by rw [hcon]; exact Set.mem_singleton _)
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · rw [deningerEvenPreimage_of_neg _ hneg,
      deningerMobiusPreimage_poissonSource h (by linarith)]
    exact deningerMeyerCap_even h.2 x
  · rw [deningerEvenPreimage_of_pos _ hpos, deningerMobiusPreimage_poissonSource h hpos]

/-- **The preimage distribution of a Poisson boundary is the boundary.** -/
theorem deningerPreimageDistribution_poissonSource (h : DeningerMeyerCap) :
    deningerPreimageDistribution (deningerPoissonSource h)
      = ((((h : DeningerMeyerCap) : 𝓢(ℝ, ℂ))) : 𝓢'(ℝ, ℂ)) := by
  rw [deningerPreimageDistribution,
    deningerL1Distribution_congr _ (SchwartzMap.integrable ((h : DeningerMeyerCap) : 𝓢(ℝ, ℂ)))
      (deningerEvenPreimage_poissonSource_ae h)]
  exact deningerL1Distribution_schwartz _ _

/-- **Poisson boundaries lie in the kernel of the commutator.**  On a boundary the commutator is
the difference between the distributional and the classical Fourier transform of the same Schwartz
function. -/
theorem deningerMobiusCommutator_poissonSource (h : DeningerMeyerCap) :
    deningerMobiusCommutator (deningerPoissonSource h) = 0 := by
  rw [deningerMobiusCommutator, deningerCollarExchange_poissonSource,
    deningerPreimageDistribution_poissonSource, deningerPreimageDistribution_poissonSource,
    deningerMeyerCapFourier_coe, sub_eq_zero]
  have hfour : GaloisForLFunctions.fourierSCLM ((h : DeningerMeyerCap) : 𝓢(ℝ, ℂ))
      = 𝓕 ((h : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) := rfl
  rw [hfour]
  exact TemperedDistribution.fourier_toTemperedDistributionCLM_eq _

/-- **The boundary inclusion `Z(H_∩) ⊆ ker 𝔖_μ`.** -/
theorem deningerPoissonRange_subset_commutatorKernel :
    Set.range deningerPoissonSource
      ⊆ {h : DeningerExpSchwartz | deningerMobiusCommutator h = 0} := by
  rintro _ ⟨f, rfl⟩
  exact deningerMobiusCommutator_poissonSource f

end

end RHTower
