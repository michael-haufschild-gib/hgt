import GaloisForLFunctions.RHTower.MobiusThetaNativeSecondCollar
import GaloisForLFunctions.RHTower.MobiusThetaNativeMellinExtraction
import GaloisForLFunctions.RHTower.Deninger.DeningerAdiabaticGaussianBoundaryParity
import GaloisForLFunctions.RHTower.XiEndpointCompletedValue

/-!
# Survival of the original native source boundary

At each fixed Mellin parameter `s`, the unchanged order-zero native source has
`m * M(h_m)(s) → 1/2`. Absolute admission follows from the existing native theta
source formula. Every genuine Poisson boundary vanishes at each actual zeta
divisor, so the native source is outside the Poisson range at cofinal depths.

The exact commutator kernel then excludes equality of the entire original Gamma
endpoint and Euler transgression. A Schwartz test detects the complete native
boundary with every finite prime prefix retained; the cofinal depth condition is
independent of that prefix. At every actual Xi divisor, the native reading at
`m*rho` remains zero while the fixed reading at `rho` is eventually nonzero.

This concerns the complete linear distribution. The fixed-zeta-parameter detector
used here is different from the native conormal reading at `m*rho`. No equality
or nonvanishing assertion about the selected quadratic degree-six reader, and no
RH conclusion, follows from this module.
-/

open Complex Filter Topology MeasureTheory
open scoped SchwartzMap

namespace RHTower

noncomputable section

def mobiusThetaNativeFixedMellinParameter (s : ℂ) (m : ℕ+) : ℂ :=
  I / 2 - I * (s / (m : ℂ))

theorem mobiusThetaNativeFixedMellinParameter_centered (s : ℂ) (m : ℕ+) :
    (m : ℂ) * mobiusThetaCenteredParameter
      (mobiusThetaNativeFixedMellinParameter s m) = s := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
  dsimp [mobiusThetaNativeFixedMellinParameter, mobiusThetaCenteredParameter]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem tendsto_mobiusThetaNativeFixedMellinParameter (s : ℂ) :
    Tendsto (mobiusThetaNativeFixedMellinParameter s) atTop (𝓝 (I / 2)) := by
  have hnat : Tendsto (fun m : ℕ+ => (m : ℕ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (⟨b + 1, Nat.succ_pos b⟩ : ℕ+)] with m hm
    exact (Nat.le_succ b).trans (show b + 1 ≤ (m : ℕ) from hm)
  have hinvR : Tendsto (fun m : ℕ+ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hnat)
  have hinvC : Tendsto (fun m : ℕ+ => (m : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp hinvR
  have hdiv : Tendsto (fun m : ℕ+ => s / (m : ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinvC.const_mul s
  change Tendsto (fun m : ℕ+ => I / 2 - I * (s / (m : ℂ))) atTop (𝓝 (I / 2))
  simpa only [mul_zero, sub_zero] using
    tendsto_const_nhds.sub (hdiv.const_mul I)

theorem mobiusThetaNativeFixedMellinParameter_admitted (s : ℂ) :
    ∀ᶠ m : ℕ+ in atTop, |(mobiusThetaNativeFixedMellinParameter s m).im| < 1 := by
  have ht := ((continuous_abs.comp Complex.continuous_im).tendsto (I / 2)).comp
    (tendsto_mobiusThetaNativeFixedMellinParameter s)
  exact (tendsto_order.1 ht).2 1 (by norm_num)

/-- The original source retains its exact fixed Mellin reading and absolute admission. -/
theorem mobiusThetaNativeFixedMellin_data (s : ℂ) :
    ∀ᶠ m : ℕ+ in atTop,
      Integrable (fun t : ℝ => Complex.exp (s * (t : ℂ)) *
        mobiusThetaNativeCollarSource 0 m t) ∧
      deningerMeyerStrongLogMellin (mobiusThetaNativeCollarSource 0 m) s =
        (m : ℂ)⁻¹ * XiC (mobiusThetaNativeFixedMellinParameter s m) := by
  filter_upwards [mobiusThetaNativeFixedMellinParameter_admitted s] with m hm
  have h := mobiusThetaNativeCollarSource_mellin_data 0 m hm
  rw [mobiusThetaNativeFixedMellinParameter_centered] at h
  simpa only [iteratedDeriv_zero, deningerMeyerStrongLogMellin,
    deningerMeyerStrongLogMellinJet, pow_zero, one_mul] using h

/-- The nonzero endpoint is recovered from the unchanged native source at every fixed parameter. -/
theorem tendsto_mobiusThetaNativeFixedMellin_scaled (s : ℂ) :
    Tendsto (fun m : ℕ+ => (m : ℂ) *
      deningerMeyerStrongLogMellin (mobiusThetaNativeCollarSource 0 m) s)
      atTop (𝓝 (1 / 2)) := by
  have ht := (XiC_differentiable.continuous.tendsto (I / 2)).comp
    (tendsto_mobiusThetaNativeFixedMellinParameter s)
  rw [XiC_I_half_eq] at ht
  apply ht.congr'
  filter_upwards [mobiusThetaNativeFixedMellin_data s] with m hm
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
  rw [hm.2, ← mul_assoc, mul_inv_cancel₀ hm0, one_mul]
  rfl

theorem mobiusThetaNativeFixedMellin_ne_zero_cofinal (s : ℂ) :
    ∀ᶠ m : ℕ+ in atTop,
      deningerMeyerStrongLogMellin (mobiusThetaNativeCollarSource 0 m) s ≠ 0 := by
  have h := (tendsto_mobiusThetaNativeFixedMellin_scaled s).eventually_ne
    (by norm_num : (1 / 2 : ℂ) ≠ 0)
  filter_upwards [h] with m hm
  intro hz
  apply hm
  rw [hz, mul_zero]

/-- At the original native parameter the order-zero source still reads the actual Xi zero. -/
theorem mobiusThetaNativeMellin_at_native_divisor (rho : XiDivisorSupport) (m : ℕ+) :
    Integrable (fun t : ℝ => Complex.exp (((m : ℂ) * (rho : ℂ)) * (t : ℂ)) *
      mobiusThetaNativeCollarSource 0 m t) ∧
    deningerMeyerStrongLogMellin (mobiusThetaNativeCollarSource 0 m)
      ((m : ℂ) * (rho : ℂ)) = 0 := by
  have h := mobiusThetaNativeCollarSource_mellin_data 0 m
    (abs_im_xiSpectralPointSupport_lt_one rho)
  simpa only [mobiusThetaCenteredParameter_xiSpectralPointSupport,
    iteratedDeriv_zero, XiC_xiSpectralPointSupport_eq_zero, mul_zero,
    deningerMeyerStrongLogMellin, deningerMeyerStrongLogMellinJet,
    pow_zero, one_mul] using h

/-- Native Xi vanishing and a nonzero fixed-zeta reading coexist on the same original source. -/
theorem mobiusThetaNativeMellin_two_scales (rho : XiDivisorSupport) :
    ∀ᶠ m : ℕ+ in atTop,
      deningerMeyerStrongLogMellin (mobiusThetaNativeCollarSource 0 m)
        ((m : ℂ) * (rho : ℂ)) = 0 ∧
      deningerMeyerStrongLogMellin (mobiusThetaNativeCollarSource 0 m)
        (rho : ℂ) ≠ 0 := by
  filter_upwards [mobiusThetaNativeFixedMellin_ne_zero_cofinal (rho : ℂ)] with m hm
  exact ⟨(mobiusThetaNativeMellin_at_native_divisor rho m).2, hm⟩

/-- Every actual Xi divisor detects failure of Poisson-range membership at cofinal native depths. -/
theorem mobiusThetaNativeMeyerSource_not_poisson_cofinal (rho : XiDivisorSupport) :
    ∀ᶠ m : ℕ+ in atTop,
      DeningerMeyerSource.toSource (mobiusThetaNativeMeyerSource 0 m) ∉
        Set.range deningerPoissonSource := by
  have hζ : riemannZeta (rho : ℂ) = 0 := by
    simpa only [iteratedDeriv_zero] using
      iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity rho
        (xiSupportMultiplicity_pos rho)
  filter_upwards [mobiusThetaNativeFixedMellin_ne_zero_cofinal (rho : ℂ)] with m hm
  rintro ⟨f, hf⟩
  have hz := deningerMeyerStrongLogMellin_boundary_zero_at_zeta_zero f
    (xi_divisor_support_re_mem_open_unit rho).1 (xiDivisorSupport_ne_one rho) hζ
  rw [← deningerPoissonSource_coe_eq_strongLogSum, hf] at hz
  exact hm hz

/-- The entire original Gamma-minus-Euler boundary cannot vanish at cofinal native depths. -/
theorem mobiusThetaNativeGamma_ne_transgression_cofinal (rho : XiDivisorSupport) :
    ∀ᶠ m : ℕ+ in atTop,
      deningerAdiabaticGammaBoundary (mobiusThetaNativeMeyerSource 0 m) ≠
        deningerAdiabaticGreenStokesTransgression (mobiusThetaNativeMeyerSource 0 m) := by
  filter_upwards [mobiusThetaNativeMeyerSource_not_poisson_cofinal rho] with m hm
  exact fun h => hm ((deningerAdiabaticGamma_eq_transgression_iff_poisson _).1 h)

/-- The same surviving distribution includes every finite prime prefix. -/
theorem mobiusThetaNativeFullBoundary_add_prefix_ne_zero_cofinal
    (rho : XiDivisorSupport) (p : ℕ) :
    ∀ᶠ m : ℕ+ in atTop,
      mobiusThetaNativeFullCollarBoundary 0 p m +
        mobiusThetaNativePrefixBoundary 0 p m ≠ 0 := by
  filter_upwards [mobiusThetaNativeGamma_ne_transgression_cofinal rho] with m hm
  intro hz
  rw [mobiusThetaNativeFullCollarBoundary_eq_commutator_sub_prefix,
    sub_add_cancel] at hz
  have h := XI_BV_GREEN_STOKES_STRICT_DESCENT (mobiusThetaNativeMeyerSource 0 m)
  rw [hz] at h
  exact hm (sub_eq_zero.mp h.symm)

/-- A genuine Schwartz test detects the original complete boundary at cofinal depths. -/
theorem mobiusThetaNativeFullBoundary_detected_cofinal
    (rho : XiDivisorSupport) (p : ℕ) :
    ∀ᶠ m : ℕ+ in atTop, ∃ φ : 𝓢(ℝ, ℂ),
      mobiusThetaNativeFullCollarBoundary 0 p m φ +
        mobiusThetaNativePrefixBoundary 0 p m φ ≠ 0 := by
  filter_upwards [mobiusThetaNativeFullBoundary_add_prefix_ne_zero_cofinal rho p] with m hm
  by_contra h
  push Not at h
  apply hm
  ext φ
  exact h φ

/-- Complete native boundaries survive at cofinal depths, uniformly over the retained prefix. -/
theorem mobiusThetaNativeFullBoundary_survives :
    ∀ᶠ m : ℕ+ in atTop, ∀ p : ℕ, ∃ φ : 𝓢(ℝ, ℂ),
      mobiusThetaNativeFullCollarBoundary 0 p m φ +
        mobiusThetaNativePrefixBoundary 0 p m φ ≠ 0 := by
  filter_upwards [mobiusThetaNativeGamma_ne_transgression_cofinal
    (Classical.arbitrary XiDivisorSupport)] with m hm
  intro p
  by_contra hzero
  push Not at hzero
  have hz : mobiusThetaNativeFullCollarBoundary 0 p m +
      mobiusThetaNativePrefixBoundary 0 p m = 0 := by
    ext φ
    exact hzero φ
  rw [mobiusThetaNativeFullCollarBoundary_eq_commutator_sub_prefix,
    sub_add_cancel] at hz
  have h := XI_BV_GREEN_STOKES_STRICT_DESCENT (mobiusThetaNativeMeyerSource 0 m)
  rw [hz] at h
  exact hm (sub_eq_zero.mp h.symm)

end
end RHTower
