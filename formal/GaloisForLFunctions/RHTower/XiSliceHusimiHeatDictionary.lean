import GaloisForLFunctions.RHTower.XiSliceHusimiZero
import GaloisForLFunctions.RHTower.ThetaCuspSchwartzFourierXi
import GaloisForLFunctions.RHTower.DeBruijnNewmanNonnegative
import GaloisForLFunctions.RHTower.XiCosineShiftDefectDisks

/-!
# Husimi zeros are zeros of the backward heat flow

The Husimi density of the height-averaged slice (`XiSliceHusimiPositivity`) is
`|V_σ(s,t)|²`, with `V_σ(s,t) = e^{−s²/(2σ²)} B_σ(s + iσ²t)` (`gaborAmp_eq_bargmann`).  This file
identifies the Bargmann function `B_σ` with the de Bruijn–Newman deformation of `Ξ` at the negative
heat time `−1/(2σ²)`.

* `thetaCuspFullSource_eq_riemannKernelReal`: the theta source of the Husimi lane is the kernel of
  the de Bruijn–Newman lane.  Both have Fourier transform `Ξ(2π·)`, and Fourier inversion applies.
* `thetaBargmann_eq_riemannHeat`: `B_σ(w) = H_{−1/(2σ²)}(iw/σ²)`.
* `gaborAmp_eq_zero_iff_riemannHeat`: `V_σ(s,t) = 0 ⟺ H_{−1/(2σ²)}(is/σ² − t) = 0`.
* `husimiZeros_offAxis_infinite`: at every resolution `σ`, the Husimi density has infinitely many
  zeros with `s ≠ 0`.  This is Newman's theorem (`riemannHeat_neg_nonreal_zeros_infinite`)
  transported through the dictionary.

So the Husimi zero set at resolution `σ` is the zero set of the backward heat flow at time
`1/(2σ²)`, placed at `(s,t) = (σ² Im z, −Re z)`.  WD's uncertainty threshold (`XiSliceHusimiZero`)
and the de Bruijn–Newman constant are one object.
-/

open Complex MeasureTheory Real
open scoped FourierTransform

namespace RHTower

noncomputable section

open DeBruijn

/-- **The two theta kernels coincide.** -/
theorem thetaCuspFullSource_eq_riemannKernelReal (u : ℝ) :
    thetaCuspFullSource u = riemannKernelReal u := by
  set f₂ : ℝ → ℂ := fun x => (riemannKernelReal x : ℂ) with hf₂
  have hf₂c : Continuous f₂ := Complex.continuous_ofReal.comp riemannKernel_superExp.continuous
  have hf₂i : Integrable f₂ := by
    simpa [hf₂] using riemannKernel_superExp.integrable 0
  have hFeq : 𝓕 f₂ = 𝓕 (fun x : ℝ => thetaCuspSchwartz x) := by
    funext ξ
    have h1 := fourier_thetaCuspSchwartz_scaled (2 * Real.pi * ξ)
    rw [show 2 * Real.pi * ξ / (2 * Real.pi) = ξ by field_simp] at h1
    change 𝓕 f₂ ξ = 𝓕 (fun x : ℝ => thetaCuspSchwartz x) ξ
    rw [show 𝓕 (fun x : ℝ => thetaCuspSchwartz x) ξ = (𝓕 thetaCuspSchwartz) ξ from rfl]
    rw [h1, Real.fourier_real_eq_integral_exp_smul]
    have h2 := congrFun cosTransform_riemannKernel_eq_XiC (-(2 * Real.pi * ξ : ℝ) : ℂ)
    rw [XiC_neg'] at h2
    rw [← h2]
    unfold cosTransform
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hf₂, smul_eq_mul]
    rw [mul_comm]
    congr 1
    push_cast
    ring
  have hinv₂ := hf₂c.fourierInv_fourier_eq hf₂i (by
    rw [hFeq]; exact (𝓕 thetaCuspSchwartz).integrable)
  have hinv₁ := thetaCuspSchwartz.continuous.fourierInv_fourier_eq thetaCuspSchwartz.integrable
    (𝓕 thetaCuspSchwartz).integrable
  have h := congrFun hinv₂ u
  rw [hFeq] at h
  have h' := congrFun hinv₁ u
  have hval : (riemannKernelReal u : ℂ) = (thetaCuspFullSource u : ℂ) := by
    rw [← thetaCuspSchwartz_apply]
    exact h.symm.trans h'
  exact_mod_cast hval.symm

/-- **The Bargmann function is the backward heat flow:** `B_σ(w) = H_{−1/(2σ²)}(iw/σ²)`. -/
theorem thetaBargmann_eq_riemannHeat {σ : ℝ} (hσ : 0 < σ) (w : ℂ) :
    thetaBargmann σ w = riemannHeat (-(1 / (2 * σ ^ 2))) (I * w / σ ^ 2) := by
  unfold thetaBargmann riemannHeat cosTransform
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hσ0 : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  simp only [dampedThetaSource, thetaCuspFullSource_eq_riemannKernelReal]
  rw [mul_comm]
  congr 2
  · congr 1
    ring
  · field_simp
    ring_nf
    rw [I_sq]
    ring

/-- **Husimi zeros are backward-heat zeros.** -/
theorem gaborAmp_eq_zero_iff_riemannHeat {σ : ℝ} (hσ : 0 < σ) (t s : ℝ) :
    gaborAmp thetaCuspFullSource σ t s = 0 ↔
      riemannHeat (-(1 / (2 * σ ^ 2))) (I * ((s : ℂ) + I * ((σ ^ 2 * t : ℝ) : ℂ)) / σ ^ 2) = 0 := by
  rw [gaborAmp_eq_bargmann hσ, thetaBargmann_eq_riemannHeat hσ, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (ofReal_ne_zero.mpr (Real.exp_pos _).ne')
    · exact h
  · exact Or.inr

/-- **Infinitely many off-axis Husimi zeros at every resolution** (Newman's theorem through the
dictionary). -/
theorem husimiZeros_offAxis_infinite {σ : ℝ} (hσ : 0 < σ) :
    {p : ℝ × ℝ | gaborAmp thetaCuspFullSource σ p.2 p.1 = 0 ∧ p.1 ≠ 0}.Infinite := by
  have hτ : 0 < 1 / (2 * σ ^ 2) := by positivity
  have hN := riemannHeat_neg_nonreal_zeros_infinite hτ
  have hσ2 : σ ^ 2 ≠ 0 := by positivity
  set φ : ℂ → ℝ × ℝ := fun z => (σ ^ 2 * z.im, -z.re) with hφ
  have hinj : Set.InjOn φ {z : ℂ | riemannHeat (-(1 / (2 * σ ^ 2))) z = 0 ∧ z.im ≠ 0} := by
    intro z₁ _ z₂ _ h
    simp only [hφ, Prod.mk.injEq] at h
    apply Complex.ext
    · linarith [h.2]
    · exact mul_left_cancel₀ hσ2 h.1
  refine (hN.image hinj).mono ?_
  rintro _ ⟨z, ⟨hz, hzim⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [gaborAmp_eq_zero_iff_riemannHeat hσ]
    have e : I * (((σ ^ 2 * z.im : ℝ) : ℂ) + I * ((σ ^ 2 * -z.re : ℝ) : ℂ)) / (σ ^ 2 : ℂ) =
        ((z.re : ℂ) + z.im * I) := by
      have hσ1 : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
      push_cast
      field_simp
      ring_nf
      rw [I_sq]
      ring
    simp only [hφ]
    rw [e, Complex.re_add_im]
    exact hz
  · simp only [hφ]
    exact mul_ne_zero hσ2 hzim

end

end RHTower
