import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaRootEndpoints
import GaloisForLFunctions.RHTower.XiSourceBoundaryOrientationConservation

/-!
# Hedenmalm root flux faithfully reads the reflected modular charge

At every zero of the completed theta transform in the strip `|Im z| < 1`, the quantile-root
energy is strictly positive: a vanishing energy would force the root mode to vanish identically
on the open unit interval, while the pinned root differential equation forces derivative `-1`
at any interior zero of the mode.  The unconditional root-flux identity then expresses the
ordered-correlation flux as `-1/2` times the reflected Riemann source entropy times that energy,
so flux neutrality, entropy neutrality, and reality of the spectral point are equivalent.  The
flux loses none of the transverse modular charge; it is a faithful reader, not an independent
neutral trace.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile

noncomputable section

/-- Quantile-root energy of the theta system at a spectral point. -/
def hedenmalmRootQuantileEnergy (z : ℂ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1, quantileSpeed thetaSource t * ‖rootH thetaSource z t‖ ^ (2 : ℕ)

/-- Ordered-correlation root flux of the theta system at a spectral point. -/
def hedenmalmRootOrderedFlux (z : ℂ) : ℝ :=
  (∫ t in Ioo (0 : ℝ) 1, -(rootH thetaSource z t)).re

/-- **Strict quantile-root energy.**  At a completed-transform zero in the strip, the root
energy cannot vanish: the mode would vanish identically on the open interval, while the pinned
root equation forces derivative `-1` at an interior zero of the mode. -/
theorem hedenmalmRootQuantileEnergy_pos {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    0 < hedenmalmRootQuantileEnergy z := by
  have hend := rootModeEndpoints_thetaSource hz hzero
  have htail := hasShiftedTail_thetaSource hz
  set g : ℝ → ℝ := fun t => quantileSpeed thetaSource t * ‖rootH thetaSource z t‖ ^ (2 : ℕ) with hg
  have hnonneg : ∀ t, 0 ≤ g t := fun t =>
    mul_nonneg (quantileSpeed_pos thetaSource t).le (sq_nonneg _)
  have hge : 0 ≤ hedenmalmRootQuantileEnergy z :=
    setIntegral_nonneg measurableSet_Ioo fun t _ => hnonneg t
  rcases hge.lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  -- the a.e. vanishing forced by a zero integral of a nonnegative integrand
  have hae : g =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] 0 := by
    have hiff := MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae
      (μ := volume) (s := Ioo (0 : ℝ) 1) (f := g)
      (Filter.Eventually.of_forall fun t => hnonneg t) hend.integrableEnergy
    exact hiff.mp heq.symm
  have hnull : volume ({t | g t ≠ 0} ∩ Ioo (0 : ℝ) 1) = 0 := by
    have h := (ae_restrict_iff' measurableSet_Ioo).mp hae
    rw [MeasureTheory.ae_iff] at h
    refine measure_mono_null ?_ h
    intro t ⟨htne, htIoo⟩
    simp only [Set.mem_setOf_eq]
    intro hcontra
    exact htne (hcontra htIoo)
  -- interior continuity upgrades a.e. vanishing to pointwise vanishing
  have hcont : ContinuousOn g (Ioo (0 : ℝ) 1) :=
    (continuousOn_quantileSpeed thetaSource).mul
      ((continuousOn_rootH thetaSource htail).norm.pow 2)
  have hzero_on : ∀ t ∈ Ioo (0 : ℝ) 1, g t = 0 := by
    by_contra hex
    push Not at hex
    obtain ⟨t₀, ht₀, hgt₀⟩ := hex
    have hca : ContinuousAt g t₀ := hcont.continuousAt (isOpen_Ioo.mem_nhds ht₀)
    have hgpos : 0 < g t₀ := lt_of_le_of_ne (hnonneg t₀) (Ne.symm hgt₀)
    have hev : {t : ℝ | 0 < g t} ∈ nhds t₀ := hca (Ioi_mem_nhds hgpos)
    obtain ⟨U, hUsub, hUopen, hUmem⟩ := mem_nhds_iff.mp hev
    set V := U ∩ Ioo (0 : ℝ) 1 with hV
    have hVopen : IsOpen V := hUopen.inter isOpen_Ioo
    have hVne : V.Nonempty := ⟨t₀, hUmem, ht₀⟩
    have hVsub : V ⊆ {t | g t ≠ 0} ∩ Ioo (0 : ℝ) 1 := by
      rintro t ⟨htU, htIoo⟩
      exact ⟨(hUsub htU).ne', htIoo⟩
    have hVpos : 0 < volume V := hVopen.measure_pos volume hVne
    exact absurd (measure_mono_null hVsub hnull) hVpos.ne'
  -- the root mode vanishes on the interval
  have hH0 : ∀ t ∈ Ioo (0 : ℝ) 1, rootH thetaSource z t = 0 := by
    intro t ht
    have hgt := hzero_on t ht
    have hq := quantileSpeed_pos thetaSource t
    have hsq : ‖rootH thetaSource z t‖ ^ (2 : ℕ) = 0 := by
      by_contra hne
      have hpos : 0 < ‖rootH thetaSource z t‖ ^ (2 : ℕ) :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      nlinarith [hgt]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    exact norm_eq_zero.mp this
  -- the pinned equation forces derivative `-1` at the interior zero
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hloc : rootH thetaSource z =ᶠ[nhds (1 / 2 : ℝ)] fun _ => 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hhalf] with t ht
    exact hH0 t ht
  have hd0 : HasDerivAt (rootH thetaSource z) 0 (1 / 2 : ℝ) :=
    (hasDerivAt_const (1 / 2 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hloc
  have hd1 := hasDerivAt_rootH_ode thetaSource htail hhalf
  rw [hH0 _ hhalf, mul_zero, zero_sub] at hd1
  have hcontra := hd1.unique hd0
  norm_num at hcontra

/-- The root-flux identity in energy notation: `F(z) = -Im z · E(z)`. -/
theorem hedenmalmRootOrderedFlux_eq {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    hedenmalmRootOrderedFlux z = -(z.im) * hedenmalmRootQuantileEnergy z :=
  rootFlux_identity_thetaSource hz hzero

/-- Reflected source entropy at the physical spectral parameter: `R(1/2 + i z) = 2 Im z`. -/
theorem riemannReflectedSourceEntropy_half_add_I_mul (z : ℂ) :
    riemannReflectedSourceEntropy (1 / 2 + Complex.I * z) = 2 * z.im := by
  rw [riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  have h12 : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by
    norm_num [Complex.div_re, Complex.normSq]
  simp only [sourceCayleyTransverseRate, Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, h12]
  ring

/-- **Faithful modular-charge law.**  The ordered-correlation flux is exactly `-1/2` times the
reflected Riemann source entropy times the strictly positive quantile-root energy. -/
theorem hedenmalmRootOrderedFlux_eq_neg_half_entropy_mul_energy {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    hedenmalmRootOrderedFlux z =
      -(1 / 2) * riemannReflectedSourceEntropy (1 / 2 + Complex.I * z) *
        hedenmalmRootQuantileEnergy z := by
  rw [hedenmalmRootOrderedFlux_eq hz hzero, riemannReflectedSourceEntropy_half_add_I_mul]
  ring

/-- Flux neutrality is entropy neutrality. -/
theorem hedenmalmRootOrderedFlux_eq_zero_iff_entropy {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    hedenmalmRootOrderedFlux z = 0 ↔
      riemannReflectedSourceEntropy (1 / 2 + Complex.I * z) = 0 := by
  have hE := hedenmalmRootQuantileEnergy_pos hz hzero
  rw [hedenmalmRootOrderedFlux_eq_neg_half_entropy_mul_energy hz hzero]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · norm_num at h3
      · exact h4
    · exact absurd h2 hE.ne'
  · intro h
    rw [h]
    ring

/-- Entropy neutrality at the physical parameter is reality of the spectral point. -/
theorem riemannReflectedSourceEntropy_eq_zero_iff_im (z : ℂ) :
    riemannReflectedSourceEntropy (1 / 2 + Complex.I * z) = 0 ↔ z.im = 0 := by
  rw [riemannReflectedSourceEntropy_half_add_I_mul]
  constructor <;> intro h <;> linarith

/-- **Flux neutrality, entropy neutrality, and spectral reality are equivalent.** -/
theorem hedenmalmRootOrderedFlux_eq_zero_iff_im {z : ℂ} (hz : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    hedenmalmRootOrderedFlux z = 0 ↔ z.im = 0 := by
  rw [hedenmalmRootOrderedFlux_eq_zero_iff_entropy hz hzero,
    riemannReflectedSourceEntropy_eq_zero_iff_im]

end

end HedenmalmThetaSource

end RHTower
