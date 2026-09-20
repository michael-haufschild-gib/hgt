import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiCarrierArithmeticDensity
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiZeroFunctionL2

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-!
# Local carrier-density obstruction at real Xi nodes

The exact Suzuki carrier becomes zero along every punctured real
neighborhood of a spectral Xi divisor, including a multiple divisor.  Its
literal totalized density, however, is `1 / 4` at a simultaneous zero of Xi
and its derivative.  Therefore the literal density cannot supply a
continuous Cayley/Hankel symbol at such a node.  This is a local obstruction:
an RG-HF compactness argument must use a justified a.e. representative and
separate endpoint regularity, rather than silently treating the totalized
symbol as continuous.
-/

theorem tendsto_suzukiXiZeroCarrier_at_real_spectral_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    Tendsto (fun x : ℝ ↦ suzukiXiZeroCarrier (x : ℂ))
      (𝓝[≠] (zetaSpectralCoordinate rho.1).re) (𝓝 0) := by
  let alpha := zetaSpectralCoordinate rho.1
  have halpha : ((alpha.re : ℝ) : ℂ) = alpha := by
    apply Complex.ext
    · simp
    · simpa [alpha] using hrho.symm
  obtain ⟨h, hh, heq⟩ :=
    eventuallyEq_suzukiXiZeroFunctionFormula_regularization rho
  let F : ℂ → ℂ := suzukiXiZeroFunctionRegularization rho h
  have hF : Tendsto F (𝓝 alpha) (𝓝 (F alpha)) :=
    (analyticAt_suzukiXiZeroFunctionRegularization rho hh).continuousAt.tendsto
  have hnormal : (suzukiXiZeroNormalization rho : ℂ) ≠ 0 := by
    have hm : 0 < (analyticZetaZeroMultiplicity rho : ℝ) := by
      exact_mod_cast analyticZetaZeroMultiplicity_positive rho
    exact_mod_cast (Real.sqrt_pos.2 (div_pos hm Real.pi_pos)).ne'
  have hprod : Tendsto (fun z : ℂ ↦
      (z - alpha) * (F z / (suzukiXiZeroNormalization rho : ℂ)))
      (𝓝 alpha) (𝓝 0) := by
    have hsub : Tendsto (fun z : ℂ ↦ z - alpha) (𝓝 alpha) (𝓝 0) := by
      have hid : Tendsto (fun z : ℂ ↦ z) (𝓝 alpha) (𝓝 alpha) :=
        tendsto_id
      have hconst : Tendsto (fun _ : ℂ ↦ alpha) (𝓝 alpha) (𝓝 alpha) :=
        tendsto_const_nhds
      simpa only [sub_self] using hid.sub hconst
    have hquot : Tendsto (fun z : ℂ ↦
        F z / (suzukiXiZeroNormalization rho : ℂ))
        (𝓝 alpha) (𝓝 (F alpha / (suzukiXiZeroNormalization rho : ℂ))) :=
      hF.div_const _
    convert hsub.mul hquot using 1
    all_goals simp
  have hcoe : Tendsto (fun x : ℝ ↦ (x : ℂ))
      (𝓝[≠] alpha.re) (𝓝 alpha) := by
    have hbase : Tendsto (fun x : ℝ ↦ (x : ℂ))
        (𝓝 alpha.re) (𝓝 ((alpha.re : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto
    simpa [halpha] using hbase.mono_left nhdsWithin_le_nhds
  have hprodReal : Tendsto (fun x : ℝ ↦
      ((x : ℂ) - alpha) *
        (F (x : ℂ) / (suzukiXiZeroNormalization rho : ℂ)))
      (𝓝[≠] alpha.re) (𝓝 0) :=
    hprod.comp hcoe
  have heq' : ∀ᶠ z in 𝓝 alpha, z ≠ alpha →
      suzukiXiZeroFunctionFormula rho z = F z := by
    change ∀ᶠ z in 𝓝[≠] zetaSpectralCoordinate rho.1,
      suzukiXiZeroFunctionFormula rho z =
        suzukiXiZeroFunctionRegularization rho h z at heq
    have heqWithin : ∀ᶠ z in 𝓝[≠] alpha,
        suzukiXiZeroFunctionFormula rho z = F z := by
      simpa [alpha, F] using heq
    rw [eventually_nhdsWithin_iff] at heqWithin
    exact heqWithin
  have hformula : ∀ᶠ x : ℝ in 𝓝[≠] alpha.re,
      suzukiXiZeroFunctionFormula rho (x : ℂ) = F (x : ℂ) := by
    have hself : ∀ᶠ x : ℝ in 𝓝[≠] alpha.re, x ≠ alpha.re :=
      self_mem_nhdsWithin
    filter_upwards [hcoe.eventually heq', hself] with x hx hxa
    apply hx
    intro hcomplex
    apply hxa
    have hre := congrArg Complex.re hcomplex
    simpa using hre
  have hcarrier : ∀ᶠ x : ℝ in 𝓝[≠] alpha.re,
      suzukiXiZeroCarrier (x : ℂ) =
        ((x : ℂ) - alpha) *
          (F (x : ℂ) / (suzukiXiZeroNormalization rho : ℂ)) := by
    have hself : ∀ᶠ x : ℝ in 𝓝[≠] alpha.re, x ≠ alpha.re :=
      self_mem_nhdsWithin
    filter_upwards [hformula, hself] with x hformula hxa
    have hden : (x : ℂ) - alpha ≠ 0 := by
      intro hzero
      apply hxa
      have heq : (x : ℂ) = alpha := sub_eq_zero.mp hzero
      have hre := congrArg Complex.re heq
      simpa using hre
    have hden' : (x : ℂ) - zetaSpectralCoordinate rho.1 ≠ 0 := by
      simpa [alpha] using hden
    change suzukiXiZeroCarrier (x : ℂ) =
      ((x : ℂ) - zetaSpectralCoordinate rho.1) *
        (F (x : ℂ) / (suzukiXiZeroNormalization rho : ℂ))
    rw [← hformula]
    unfold suzukiXiZeroFunctionFormula
    field_simp [hden', hnormal]
  exact hprodReal.congr' (hcarrier.mono fun _ hx ↦ hx.symm)

theorem tendsto_suzukiXiRealAxisCarrierDensity_at_real_spectral_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    Tendsto suzukiXiRealAxisCarrierDensity
      (𝓝[≠] (zetaSpectralCoordinate rho.1).re) (𝓝 0) := by
  change Tendsto (fun x : ℝ ↦ ‖suzukiXiZeroCarrier (x : ℂ)‖ ^ 2)
    (𝓝[≠] (zetaSpectralCoordinate rho.1).re) (𝓝 0)
  have hcarrier : Tendsto (fun x : ℝ ↦ suzukiXiZeroCarrier (x : ℂ))
      (𝓝[≠] (zetaSpectralCoordinate rho.1).re) (𝓝 0) :=
    tendsto_suzukiXiZeroCarrier_at_real_spectral_zero rho hrho
  have hnorm : Continuous (fun z : ℂ ↦ ‖z‖ ^ 2) :=
    continuous_norm.pow 2
  have hnormSq : Tendsto (fun z : ℂ ↦ ‖z‖ ^ 2)
      (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) := by
    simpa using
      (show ContinuousAt (fun z : ℂ ↦ ‖z‖ ^ 2) (0 : ℂ) from
        hnorm.continuousAt).tendsto
  exact hnormSq.comp hcarrier

theorem not_continuousAt_suzukiXiRealAxisCarrierDensity_of_real_multiple_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0)
    (hE : suzukiXiEValue (zetaSpectralCoordinate rho.1) = 0) :
    ¬ ContinuousAt suzukiXiRealAxisCarrierDensity
      (zetaSpectralCoordinate rho.1).re := by
  intro hcontinuous
  have hactual : Tendsto suzukiXiRealAxisCarrierDensity
      (𝓝[≠] (zetaSpectralCoordinate rho.1).re)
      (𝓝 (suzukiXiRealAxisCarrierDensity
        (zetaSpectralCoordinate rho.1).re)) :=
    hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hpunctured : Tendsto suzukiXiRealAxisCarrierDensity
      (𝓝[≠] (zetaSpectralCoordinate rho.1).re) (𝓝 0) :=
    tendsto_suzukiXiRealAxisCarrierDensity_at_real_spectral_zero rho hrho
  have hzero : suzukiXiRealAxisCarrierDensity
      (zetaSpectralCoordinate rho.1).re = 0 :=
    tendsto_nhds_unique hactual hpunctured
  have halpha : (((zetaSpectralCoordinate rho.1).re : ℝ) : ℂ) =
      zetaSpectralCoordinate rho.1 := by
    apply Complex.ext
    · simp
    · simpa using hrho.symm
  have hEreal : suzukiXiEValue
      (((zetaSpectralCoordinate rho.1).re : ℝ) : ℂ) = 0 := by
    rw [halpha]
    exact hE
  have hquarter := suzukiXiRealAxisCarrierDensity_eq_quarter_of_E_eq_zero
    (zetaSpectralCoordinate rho.1).re hEreal
  rw [hzero] at hquarter
  norm_num at hquarter

/-- The exact one-point repair which replaces a literal totalized value by
the punctured carrier-density limit. -/
def suzukiXiRealAxisCarrierDensityRemovablePatch (a x : ℝ) : ℝ :=
  if x = a then 0 else suzukiXiRealAxisCarrierDensity x

/-- A one-point repair leaves the Lebesgue `L²` symbol unchanged. -/
theorem ae_eq_suzukiXiRealAxisCarrierDensityRemovablePatch
    (a : ℝ) :
    suzukiXiRealAxisCarrierDensityRemovablePatch a =ᵐ[volume]
      suzukiXiRealAxisCarrierDensity := by
  have hne : ∀ᵐ x : ℝ, x ≠ a := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with x hx
  unfold suzukiXiRealAxisCarrierDensityRemovablePatch
  rw [if_neg hx]

/-- The one-point repaired density is continuous at every real spectral Xi
divisor.  Thus a real multiple zero obstructs continuity of the literal
totalized symbol, but not the local construction of a removable `L²`
representative. -/
theorem continuousAt_suzukiXiRealAxisCarrierDensityRemovablePatch_at_real_spectral_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im = 0) :
    ContinuousAt
      (suzukiXiRealAxisCarrierDensityRemovablePatch
        (zetaSpectralCoordinate rho.1).re)
      (zetaSpectralCoordinate rho.1).re := by
  rw [continuousAt_iff_punctured_nhds]
  have hvalue : suzukiXiRealAxisCarrierDensityRemovablePatch
      (zetaSpectralCoordinate rho.1).re
      (zetaSpectralCoordinate rho.1).re = 0 := by
    simp [suzukiXiRealAxisCarrierDensityRemovablePatch]
  rw [hvalue]
  have hlimit :=
    tendsto_suzukiXiRealAxisCarrierDensity_at_real_spectral_zero rho hrho
  have hEq : ∀ᶠ x : ℝ in 𝓝[≠] (zetaSpectralCoordinate rho.1).re,
      suzukiXiRealAxisCarrierDensityRemovablePatch
          (zetaSpectralCoordinate rho.1).re x =
        suzukiXiRealAxisCarrierDensity x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [mem_compl_iff, mem_singleton_iff] at hx
    unfold suzukiXiRealAxisCarrierDensityRemovablePatch
    rw [if_neg hx]
  exact hlimit.congr' (hEq.mono fun _ hx ↦ hx.symm)

end

end RiemannGaussian
