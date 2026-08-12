import GaloisForLFunctions.RHTower.SuzukiAbelDifferenceRenormalization
import GaloisForLFunctions.RHTower.SuzukiAbelExponentialTail
import GaloisForLFunctions.RHTower.SuzukiFinitePartTranslationBridge
import GaloisForLFunctions.RHTower.SuzukiHlogDenseFormCore
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Suzuki equation (2.6): finite part equals logarithmic Fourier energy

This module closes Suzuki's published equation (2.6) on the literal restricted Weil core.  The
paper's formal transform of `|x|⁻¹ 1_{|x|>ε}` is not an ordinary Lebesgue Fourier transform.
Instead, we use Abel damping, prove the physical finite-part limit, and identify it with the
already established Abel-to-logarithmic Fourier limit.  The final theorem has no analytic
hypotheses: aperture positivity, smoothness, and strict support are intrinsic data.
-/

open Complex Filter MeasureTheory Set intervalIntegral
open FourierTransform
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Complex Schwartz realization of a literal real restricted-Weil source. -/
def suzukiRestrictedWeilSchwartz {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    SchwartzMap ℝ ℂ :=
  _root_.RHTower.suzukiRealTestSchwartz u u.smooth u.hasCompactSupport

@[simp] theorem suzukiRestrictedWeilSchwartz_apply {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) (x : ℝ) :
    suzukiRestrictedWeilSchwartz u x = (u x : ℂ) := rfl

private theorem norm_sq_schwartzDifference_eq_real {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) (h x : ℝ) :
    ‖_root_.RHTower.schwartzTranslationDifference
      (suzukiRestrictedWeilSchwartz u) h x‖ ^ 2 = (u x - u (x + h)) ^ 2 := by
  rw [_root_.RHTower.schwartzTranslationDifference,
    suzukiRestrictedWeilSchwartz_apply, suzukiRestrictedWeilSchwartz_apply,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem integral_norm_sq_schwartzDifference_eq_real {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) (h : ℝ) :
    (∫ x : ℝ, ‖_root_.RHTower.schwartzTranslationDifference
      (suzukiRestrictedWeilSchwartz u) h x‖ ^ 2) =
        suzukiRealTranslationDifferenceEnergy u h := by
  unfold suzukiRealTranslationDifferenceEnergy
  refine integral_congr_ae (ae_of_all _ fun x => norm_sq_schwartzDifference_eq_real u h x)

private theorem integral_fourierNormSq_restrictedWeilSchwartz_eq_mass {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) :
    (∫ xi : ℝ, ‖𝓕 (suzukiRestrictedWeilSchwartz u : ℝ → ℂ) xi‖ ^ 2) =
      ∫ x : ℝ, u x ^ 2 := by
  let f := suzukiRestrictedWeilSchwartz u
  have hp := GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq
    f.integrable (SchwartzMap.memLp f 2 (volume : Measure ℝ))
  calc
    (∫ xi : ℝ, ‖𝓕 (suzukiRestrictedWeilSchwartz u : ℝ → ℂ) xi‖ ^ 2) =
        ∫ x : ℝ, ‖suzukiRestrictedWeilSchwartz u x‖ ^ 2 := by simpa [f] using hp
    _ = ∫ x : ℝ, u x ^ 2 := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem restrictedWeil_mass_nonneg {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    0 ≤ ∫ x : ℝ, u x ^ 2 := integral_nonneg fun _ => sq_nonneg _

private theorem restrictedWeil_abelKernel_nonneg {a delta h : ℝ}
    (u : SuzukiRestrictedWeilCore a) (hh : 0 < h) :
    0 ≤ Real.exp (-(delta * h)) *
      (suzukiRealTranslationDifferenceEnergy u h / h) := by
  have hD : 0 ≤ suzukiRealTranslationDifferenceEnergy u h :=
    integral_nonneg fun x => sq_nonneg _
  exact mul_nonneg (Real.exp_pos _).le (div_nonneg hD hh.le)

private theorem integrableOn_restrictedWeil_abelKernel
    (A : _root_.RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1)
    {delta : ℝ} (hdelta : 0 < delta) :
    IntegrableOn (fun h : ℝ => Real.exp (-(delta * h)) *
      (suzukiRealTranslationDifferenceEnergy u h / h)) (Ioi 0) := by
  let R : ℝ := 2 * A.1
  have hR : 0 < R := by dsimp [R]; linarith [A.property]
  have hq : IntervalIntegrable
      (fun h : ℝ => suzukiRealTranslationDifferenceEnergy u h / h)
      volume 0 R := by
    simpa [R] using suzukiRealTranslationDifferenceQuotient_intervalIntegrable A u
  have hqIoc : IntegrableOn
      (fun h : ℝ => suzukiRealTranslationDifferenceEnergy u h / h) (Ioc 0 R) := by
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le] at hq
  have hinter : IntegrableOn (fun h : ℝ => Real.exp (-(delta * h)) *
      (suzukiRealTranslationDifferenceEnergy u h / h)) (Ioc 0 R) := by
    apply hqIoc.bdd_mul
    · exact (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith [hdelta, hh.1])
  have hbase : IntegrableOn (fun h : ℝ => Real.exp (-(delta * h))) (Ioi R) := by
    simpa using integrableOn_exp_mul_Ioi (show -delta < 0 by linarith) R
  have htailBase : IntegrableOn (fun h : ℝ => Real.exp (-(delta * h)) / h) (Ioi R) := by
    have hinvExp : IntegrableOn (fun h : ℝ => h⁻¹ * Real.exp (-(delta * h))) (Ioi R) := by
      apply hbase.bdd_mul (c := R⁻¹)
      · exact measurable_inv.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
        rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hR.trans hh)]
        exact (inv_le_inv₀ (hR.trans hh) hR).2 hh.le
    exact hinvExp.congr_fun (fun h _ => by
      simp only [div_eq_mul_inv]
      ring) measurableSet_Ioi
  have htail : IntegrableOn (fun h : ℝ => Real.exp (-(delta * h)) *
      (suzukiRealTranslationDifferenceEnergy u h / h)) (Ioi R) := by
    have hscaled : IntegrableOn
        (fun h : ℝ => (2 * ∫ x : ℝ, u x ^ 2) *
          (Real.exp (-(delta * h)) / h)) (Ioi R) :=
      htailBase.const_mul (2 * ∫ x : ℝ, u x ^ 2)
    apply hscaled.congr_fun _ measurableSet_Ioi
    intro h hh
    dsimp
    rw [suzukiRealTranslationDifferenceEnergy_eq_two_mass_of_two_aperture_le A u
      (show 2 * A.1 ≤ h by simpa [R] using hh.le)]
    ring
  have hcover : Ioi (0 : ℝ) = Ioc 0 R ∪ Ioi R := by
    ext h
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hh
      rcases le_total h R with hle | hge
      · exact Or.inl ⟨hh, hle⟩
      · rcases hge.lt_or_eq with hgt | rfl
        · exact Or.inr hgt
        · exact Or.inl ⟨hh, le_rfl⟩
    · rintro (hh | hh)
      · exact hh.1
      · exact hR.trans hh
  rw [hcover]
  exact hinter.union htail

private theorem abelPhysicalEnergyR_eq_real_translation_integral
    (A : _root_.RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1)
    {delta : ℝ} (hdelta : 0 < delta) :
    _root_.RHTower.abelSchwartzPhysicalEnergyR delta
      (suzukiRestrictedWeilSchwartz u) =
      ∫ h in Ioi (0 : ℝ), Real.exp (-(delta * h)) *
        (suzukiRealTranslationDifferenceEnergy u h / h) := by
  let f := suzukiRestrictedWeilSchwartz u
  let K : ℝ → ℝ := fun h => Real.exp (-(delta * h)) *
    (suzukiRealTranslationDifferenceEnergy u h / h)
  have hK : IntegrableOn K (Ioi 0) := integrableOn_restrictedWeil_abelKernel A u hdelta
  have hKnn : ∀ᵐ h : ℝ ∂volume.restrict (Ioi 0), 0 ≤ K h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact restrictedWeil_abelKernel_nonneg u hh
  have hinner (h : ℝ) :
      (∫⁻ x : ℝ, ENNReal.ofReal
        (‖_root_.RHTower.schwartzTranslationDifference f h x‖ ^ 2)) =
        ENNReal.ofReal (suzukiRealTranslationDifferenceEnergy u h) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (_root_.RHTower.integrable_norm_sq_schwartzTranslationDifference f h)
      (ae_of_all _ fun x => sq_nonneg _),
      integral_norm_sq_schwartzDifference_eq_real]
  have hphysical : _root_.RHTower.abelSchwartzPhysicalEnergyL delta f =
      ∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal (K h) := by
    unfold _root_.RHTower.abelSchwartzPhysicalEnergyL
    refine setLIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
    rw [hinner]
    have hh0 : 0 ≤ h := hh.le
    have hw : 0 ≤ Real.exp (-(delta * h)) / h :=
      div_nonneg (Real.exp_pos _).le hh0
    have hD : 0 ≤ suzukiRealTranslationDifferenceEnergy u h :=
      integral_nonneg fun x => sq_nonneg _
    rw [← ENNReal.ofReal_mul hw]
    apply congrArg ENNReal.ofReal
    dsimp [K]
    ring
  unfold _root_.RHTower.abelSchwartzPhysicalEnergyR
  rw [hphysical, ← ofReal_integral_eq_lintegral_ofReal hK hKnn]
  exact ENNReal.toReal_ofReal (integral_nonneg_of_ae hKnn)

private theorem restrictedWeil_abelIntegral_split
    (A : _root_.RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1)
    {delta : ℝ} (hdelta : 0 < delta) :
    (∫ h in Ioi (0 : ℝ), Real.exp (-(delta * h)) *
        (suzukiRealTranslationDifferenceEnergy u h / h)) =
      (∫ h in (0 : ℝ)..(2 * A.1), Real.exp (-(delta * h)) *
        (suzukiRealTranslationDifferenceEnergy u h / h)) +
      ∫ h in Ioi (2 * A.1), Real.exp (-(delta * h)) *
        (suzukiRealTranslationDifferenceEnergy u h / h) := by
  let K : ℝ → ℝ := fun h => Real.exp (-(delta * h)) *
    (suzukiRealTranslationDifferenceEnergy u h / h)
  let R : ℝ := 2 * A.1
  have hR : 0 < R := by dsimp [R]; linarith [A.property]
  have hK := integrableOn_restrictedWeil_abelKernel A u hdelta
  have hIoc : IntegrableOn K (Ioc 0 R) :=
    hK.mono_set fun _ hh => hh.1
  have hIoi : IntegrableOn K (Ioi R) :=
    hK.mono_set fun _ hh => hR.trans hh
  have hdisj : Disjoint (Ioc (0 : ℝ) R) (Ioi R) := by
    rw [Set.disjoint_left]
    intro h hhIoc hhIoi
    exact (not_lt_of_ge hhIoc.2) hhIoi
  have hunion : Ioc (0 : ℝ) R ∪ Ioi R = Ioi 0 := by
    ext h
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (hh | hh)
      · exact hh.1
      · exact hR.trans hh
    · intro hh
      rcases le_total h R with hle | hge
      · exact Or.inl ⟨hh, hle⟩
      · rcases hge.lt_or_eq with hgt | rfl
        · exact Or.inr hgt
        · exact Or.inl ⟨hh, le_rfl⟩
  have hsplit := integral_union_ae hdisj.aedisjoint
    measurableSet_Ioi.nullMeasurableSet hIoc hIoi
  rw [hunion] at hsplit
  change (∫ h in Ioi (0 : ℝ), K h) =
    (∫ h in (0 : ℝ)..R, K h) + ∫ h in Ioi R, K h
  rw [intervalIntegral.integral_of_le hR.le]
  exact hsplit

private theorem restrictedWeil_abelTail_eq
    (A : _root_.RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1)
    (delta : ℝ) :
    (∫ h in Ioi (2 * A.1), Real.exp (-(delta * h)) *
        (suzukiRealTranslationDifferenceEnergy u h / h)) =
      (2 * ∫ x : ℝ, u x ^ 2) *
        ∫ h in Ioi (2 * A.1), Real.exp (-(delta * h)) / h := by
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
  rw [suzukiRealTranslationDifferenceEnergy_eq_two_mass_of_two_aperture_le A u hh.le]
  ring

private theorem tendsto_restrictedWeil_abelInterior_nhdsGT_zero
    (A : _root_.RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    Tendsto (fun delta : ℝ =>
      ∫ h in (0 : ℝ)..(2 * A.1), Real.exp (-(delta * h)) *
        (suzukiRealTranslationDifferenceEnergy u h / h))
      (𝓝[>] 0)
      (𝓝 (∫ h in (0 : ℝ)..(2 * A.1),
        suzukiRealTranslationDifferenceEnergy u h / h)) := by
  let R : ℝ := 2 * A.1
  let q : ℝ → ℝ := fun h => suzukiRealTranslationDifferenceEnergy u h / h
  have hR : 0 < R := by dsimp [R]; linarith [A.property]
  have hq : IntervalIntegrable q volume 0 R := by
    simpa [q, R] using suzukiRealTranslationDifferenceQuotient_intervalIntegrable A u
  have hqIoc : IntegrableOn q (Ioc 0 R) := by
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le] at hq
  have hmeas : ∀ᶠ delta : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (fun h : ℝ => Real.exp (-(delta * h)) * q h)
        (volume.restrict (uIoc 0 R)) := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    have hK := integrableOn_restrictedWeil_abelKernel A u hdelta
    have hKIoc : IntegrableOn (fun h : ℝ => Real.exp (-(delta * h)) * q h)
        (Ioc 0 R) := by
      exact hK.mono_set fun _ hh => hh.1
    simpa [uIoc_of_le hR.le] using hKIoc.aestronglyMeasurable
  have hbound : ∀ᶠ delta : ℝ in 𝓝[>] 0,
      ∀ᵐ h : ℝ ∂volume, h ∈ uIoc 0 R →
        ‖Real.exp (-(delta * h)) * q h‖ ≤ q h := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    filter_upwards with h
    intro hh
    rw [uIoc_of_le hR.le] at hh
    have hD : 0 ≤ suzukiRealTranslationDifferenceEnergy u h :=
      integral_nonneg fun x => sq_nonneg _
    have hq0 : 0 ≤ q h := div_nonneg hD hh.1.le
    have hexp0 : 0 ≤ Real.exp (-(delta * h)) := (Real.exp_pos _).le
    have hprod : 0 ≤ delta * h := mul_nonneg hdelta.le hh.1.le
    have hexple : Real.exp (-(delta * h)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hprod)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hexp0 hq0)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hexple hq0
  have hlim : ∀ᵐ h : ℝ ∂volume, h ∈ uIoc 0 R →
      Tendsto (fun delta : ℝ => Real.exp (-(delta * h)) * q h)
        (𝓝[>] 0) (𝓝 (q h)) := by
    filter_upwards with h
    intro _hh
    have hz : Tendsto (fun delta : ℝ => -(delta * h)) (𝓝[>] 0) (𝓝 0) := by
      have hfull : Tendsto (fun delta : ℝ => -(delta * h)) (𝓝 0) (𝓝 (-(0 * h))) :=
        (tendsto_id.mul_const h).neg
      simpa using hfull.mono_left nhdsWithin_le_nhds
    have he : Tendsto (fun delta : ℝ => Real.exp (-(delta * h)))
        (𝓝[>] 0) (𝓝 1) := by
      simpa only [Function.comp_def, Real.exp_zero] using
        Real.continuous_exp.continuousAt.tendsto.comp hz
    simpa using he.mul_const (q h)
  simpa [R, q] using
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝[>] (0 : ℝ)) (F := fun delta h => Real.exp (-(delta * h)) * q h)
      (f := q) (bound := q) hmeas hbound hq hlim

/-- Physical Abel finite part tends to Suzuki's interval finite part minus Euler's constant times
the source mass. -/
theorem tendsto_suzukiRestrictedWeilPhysicalRenormalization_nhdsGT_zero
    (A : _root_.RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    Tendsto (fun delta : ℝ =>
      (1 / 2 : ℝ) * _root_.RHTower.abelSchwartzPhysicalEnergyR delta
        (suzukiRestrictedWeilSchwartz u) +
      Real.log delta * (∫ x : ℝ, u x ^ 2))
      (𝓝[>] 0)
      (𝓝 (suzukiFinitePartEnergy A.1 u -
        Real.eulerMascheroniConstant * (∫ x : ℝ, u x ^ 2))) := by
  let R : ℝ := 2 * A.1
  let M : ℝ := ∫ x : ℝ, u x ^ 2
  let I : ℝ → ℝ := fun delta =>
    ∫ h in (0 : ℝ)..R, Real.exp (-(delta * h)) *
      (suzukiRealTranslationDifferenceEnergy u h / h)
  let T : ℝ → ℝ := fun delta =>
    ∫ h in Ioi R, Real.exp (-(delta * h)) / h
  have hR : 0 < R := by dsimp [R]; linarith [A.property]
  have hI : Tendsto I (𝓝[>] 0)
      (𝓝 (∫ h in (0 : ℝ)..R, suzukiRealTranslationDifferenceEnergy u h / h)) := by
    simpa [I, R] using tendsto_restrictedWeil_abelInterior_nhdsGT_zero A u
  have hT : Tendsto (fun delta : ℝ => T delta + Real.log delta)
      (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant - Real.log R)) := by
    simpa [T] using _root_.RHTower.tendsto_scaled_exp_tail_add_log_nhdsGT_zero
      (⟨R, hR⟩ : {R : ℝ // 0 < R})
  have hsum := hI.const_mul (1 / 2 : ℝ) |>.add (hT.const_mul M)
  have hcongr : (fun delta : ℝ =>
      (1 / 2 : ℝ) * _root_.RHTower.abelSchwartzPhysicalEnergyR delta
        (suzukiRestrictedWeilSchwartz u) + Real.log delta * M) =ᶠ[𝓝[>] 0]
      fun delta => (1 / 2 : ℝ) * I delta + M * (T delta + Real.log delta) := by
    filter_upwards [self_mem_nhdsWithin] with delta hdelta
    rw [abelPhysicalEnergyR_eq_real_translation_integral A u hdelta,
      restrictedWeil_abelIntegral_split A u hdelta,
      restrictedWeil_abelTail_eq A u delta]
    dsimp [I, T, R]
    ring
  have hlimit := hsum.congr' hcongr.symm
  convert hlimit using 1
  rw [suzukiFinitePartEnergy_eq_translationDifference A u]
  dsimp [M, R]
  ring

private theorem integrable_suzukiLogFourierSpectralDensity
    (f : SchwartzMap ℝ ℂ) :
    Integrable (_root_.RHTower.suzukiLogFourierSpectralDensity f) := by
  refine (_root_.RHTower.integrable_abs_log_fourierSpectralDensity f).mono'
    (((Real.measurable_log.comp
      ((measurable_const.mul measurable_id).abs)).mul
        ((GaloisForLFunctions.RHTower.continuous_fourier_of_integrable
          f.integrable).norm.measurable.pow_const 2)).aestronglyMeasurable) ?_
  filter_upwards with xi
  simp only [_root_.RHTower.suzukiLogFourierSpectralDensity, Real.norm_eq_abs,
    abs_mul, abs_pow, abs_norm]
  exact le_rfl

/-- Suzuki's finite-part formula before combining the Euler term into the Fourier integrand.
This is equation (2.6), obtained by uniqueness of the physical and spectral Abel limits. -/
theorem suzukiFinitePartEnergy_eq_logFourier_add_eulerMass
    (A : _root_.RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    suzukiFinitePartEnergy A.1 u =
      (∫ xi : ℝ, _root_.RHTower.suzukiLogFourierSpectralDensity
        (suzukiRestrictedWeilSchwartz u) xi) +
      Real.eulerMascheroniConstant * (∫ x : ℝ, u x ^ 2) := by
  let f := suzukiRestrictedWeilSchwartz u
  have hfourier :=
    _root_.RHTower.tendsto_suzukiAbelRenormalizedDifferenceEnergy_nhdsGT_zero f
  have hphysical :=
    tendsto_suzukiRestrictedWeilPhysicalRenormalization_nhdsGT_zero A u
  have henergy (delta : ℝ) :
      _root_.RHTower.suzukiAbelRenormalizedDifferenceEnergy delta f =
        (1 / 2 : ℝ) * _root_.RHTower.abelSchwartzPhysicalEnergyR delta f +
        Real.log delta * (∫ x : ℝ, u x ^ 2) := by
    rw [_root_.RHTower.suzukiAbelRenormalizedDifferenceEnergy,
      integral_fourierNormSq_restrictedWeilSchwartz_eq_mass]
  have hphysical' := hphysical.congr'
    (Eventually.of_forall fun delta => (henergy delta).symm)
  have huniq := tendsto_nhds_unique hfourier hphysical'
  dsimp only [f] at huniq
  linarith

/-- Suzuki equation (2.6) on the literal restricted Weil core.  All support, regularity, and
aperture conditions are intrinsic to the two inputs; there are no analytic premises. -/
theorem suzukiFinitePartEnergy_eq_logFourier
    (A : _root_.RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    suzukiFinitePartEnergy A.1 u =
      ∫ xi : ℝ, (Real.log (|2 * Real.pi * xi|) + Real.eulerMascheroniConstant) *
        ‖𝓕 (suzukiRestrictedWeilSchwartz u : ℝ → ℂ) xi‖ ^ 2 := by
  let f := suzukiRestrictedWeilSchwartz u
  have hbase := suzukiFinitePartEnergy_eq_logFourier_add_eulerMass A u
  have hlog : Integrable (_root_.RHTower.suzukiLogFourierSpectralDensity f) :=
    integrable_suzukiLogFourierSpectralDensity f
  have hmass := _root_.RHTower.integrable_fourierNormSq_schwartz f
  calc
    suzukiFinitePartEnergy A.1 u =
        (∫ xi : ℝ, _root_.RHTower.suzukiLogFourierSpectralDensity f xi) +
          Real.eulerMascheroniConstant * (∫ x : ℝ, u x ^ 2) := by
      simpa only [f] using hbase
    _ = (∫ xi : ℝ, _root_.RHTower.suzukiLogFourierSpectralDensity f xi) +
          Real.eulerMascheroniConstant *
            (∫ xi : ℝ, ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2) := by
      rw [integral_fourierNormSq_restrictedWeilSchwartz_eq_mass]
    _ = ∫ xi : ℝ, _root_.RHTower.suzukiLogFourierSpectralDensity f xi +
          Real.eulerMascheroniConstant * ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      exact (MeasureTheory.integral_add hlog
        (hmass.const_mul Real.eulerMascheroniConstant)).symm
    _ = ∫ xi : ℝ, (Real.log (|2 * Real.pi * xi|) + Real.eulerMascheroniConstant) *
          ‖𝓕 (suzukiRestrictedWeilSchwartz u : ℝ → ℂ) xi‖ ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall fun xi => ?_)
      dsimp [f, _root_.RHTower.suzukiLogFourierSpectralDensity]
      ring

/-- Literal finite-part block form of Suzuki equation (2.6). -/
theorem suzukiWeilFinitePartBlock_eq_logFourier
    (A : _root_.RHTower.SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1) :
    weilFinitePartBlock A.1 u u =
      ∫ xi : ℝ, (Real.log (|2 * Real.pi * xi|) + Real.eulerMascheroniConstant) *
        ‖𝓕 (suzukiRestrictedWeilSchwartz u : ℝ → ℂ) xi‖ ^ 2 := by
  rw [suzukiWeilFinitePartBlock_eq_energy,
    suzukiFinitePartEnergy_eq_logFourier]

end GaloisForLFunctions.RHTower
