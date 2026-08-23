import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullMirrorCouplingWindingEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullMirrorKreinCayleyEndpoint
import GaloisForLFunctions.HTGeometry.EntireMultiplicityFactor

/-!
# Adaptive Hawking clocks for the full theta-mirror Krein--Cayley S-matrix

The full nonlinear Davies--Fulling mirror already mixes every tilted sector at arbitrarily weak
finite coupling.  That fact is unconditional and cannot be the RH producer.  The source-faithful
quantity which still distinguishes sectors is the first nonzero coupling order `m` of the exact
eikonal amplitude.

This module proves the corresponding dynamical classification.  After the exact full-mirror
Bogoliubov block is put in its unique bosonic Krein--Cayley chart, its disk intensity has a finite
strictly positive limit on the sector-dependent clock `lambda ^ (-2*m)`.  Thus every physical
sector has an adaptive scattering clock, including sectors dark on the ordinary Davies clock.
RH is exactly synchronization of all these clocks at the quadratic exponent `2`.

This is compatible with the resonance-theory phenomenon proved by Cornean--Jensen--Nenciu
(`arXiv:1311.7502`): when the ordinary Fermi-golden-rule constant vanishes, metastable decay can
move from order `epsilon^2` to order `epsilon^4`.  The literature result motivates the clock
interpretation; the all-order theta-mirror statement below is derived internally from the exact
eikonal coupling continuation.

**[LOCAL-RESEARCH] [BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]**
This does not prove RH.  It replaces the false producer “finite-coupling mixing” by the sharp
remaining producer: theta backreaction must synchronize every source-labelled sector to the
standard quadratic Hawking clock, equivalently exclude all higher coupling-order jumps.
-/

open Complex Real Filter Topology

noncomputable section

namespace RHTower

/-! ## Exact eikonal adaptive clock -/

/-- Squared eikonal response after removal of its exact first nonzero coupling power. -/
def thetaCuspHawkingFullMirrorEikonalAdaptiveClockRate
    (a total : ℝ) (ha : |a| < 1) (lambda : ℝ) : ℝ :=
  let m := thetaCuspHawkingFullMirrorSectorCouplingOrder a total ha
  Complex.normSq
    ((((lambda : ℂ) ^ m)⁻¹) *
      thetaCuspHawkingEikonalCouplingEntire a ha total (lambda : ℂ))

/-- Every exact theta-mirror eikonal sector has a finite strictly positive rate after rescaling by
its own first nonzero coupling order. -/
theorem exists_pos_tendsto_thetaCuspHawkingFullMirrorEikonalAdaptiveClockRate
    (a total : ℝ) (ha : |a| < 1) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto
        (thetaCuspHawkingFullMirrorEikonalAdaptiveClockRate a total ha)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  let m := thetaCuspHawkingFullMirrorSectorCouplingOrder a total ha
  let F := thetaCuspHawkingEikonalCouplingEntire a ha total
  have hF : ∀ z, AnalyticAt ℂ F z := fun z =>
    thetaCuspHawkingEikonalCouplingEntire_analyticOnNhd
      a ha total z (Set.mem_univ z)
  have hord : analyticOrderAt F 0 = (m : ℕ∞) :=
    analyticOrderAt_thetaCuspHawkingEikonalCouplingEntire_zero a total ha
  obtain ⟨g, hg, hg0, hfactor⟩ :=
    exists_entire_factor_of_analyticOrderAt_eq hF 0 m hord
  refine ⟨Complex.normSq (g 0), Complex.normSq_pos.mpr hg0, ?_⟩
  have hg_tendsto : Tendsto (fun lambda : ℝ => g (lambda : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) := by
    have hofReal : Tendsto (fun lambda : ℝ => (lambda : ℂ))
        (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := Complex.continuous_ofReal.tendsto 0
    exact ((hg 0).continuousAt.tendsto.comp hofReal).mono_left nhdsWithin_le_nhds
  have hnorm : Tendsto (fun lambda : ℝ => Complex.normSq (g (lambda : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (Complex.normSq (g 0))) := by
    simpa [Complex.normSq_eq_norm_sq] using hg_tendsto.norm.pow 2
  apply hnorm.congr'
  filter_upwards [self_mem_nhdsWithin] with lambda hlambda
  have hlambda0 : lambda ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hlambda)
  have hpow : ((lambda : ℂ) ^ m) ≠ 0 :=
    pow_ne_zero m (Complex.ofReal_ne_zero.mpr hlambda0)
  rw [thetaCuspHawkingFullMirrorEikonalAdaptiveClockRate]
  rw [show thetaCuspHawkingFullMirrorSectorCouplingOrder a total ha = m by rfl]
  rw [show thetaCuspHawkingEikonalCouplingEntire a ha total (lambda : ℂ) =
      F (lambda : ℂ) by rfl, hfactor]
  simp [hpow]

/-! ## Physical Bogoliubov and Krein--Cayley adaptive clock -/

/-- In a positive balanced sector the exact Bogoliubov pair coefficient is the normalized entire
eikonal response evaluated at physical coupling `lambda * omega / 2`. -/
theorem thetaCuspHawkingFullMirrorBogoliubovBeta_eq_eikonalCouplingEntire
    (a lambda omega : ℝ) (ha : |a| < 1) (homega : omega ≠ 0) :
    thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        thetaCuspHawkingEikonalCouplingEntire a ha omega
          ((lambda * (omega / 2) : ℝ) : ℂ) := by
  rw [thetaCuspHawkingFullMirrorBogoliubovBeta,
    thetaCuspHawkingBalancedFullMirrorAmplitude,
    thetaCuspHawkingFullMirrorAmplitude_eq_eikonalFourier a ha,
    ← thetaCuspHawkingEikonalCouplingEntire_ofReal a ha]
  push_cast
  field_simp [homega, Real.pi_ne_zero]
  ring_nf

/-- Canonical Krein--Cayley disk intensity after removal of the exact sector-dependent physical
coupling power. -/
def thetaCuspHawkingFullMirrorKreinCayleyAdaptiveClockRate
    (a omega : ℝ) (ha : |a| < 1) (lambda : ℝ) : ℝ :=
  let m := thetaCuspHawkingFullMirrorSectorCouplingOrder a omega ha
  let t := lambda * (omega / 2)
  Complex.normSq
    ((((t : ℂ) ^ m)⁻¹) *
      thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega)

/-- Away from zero coupling, the normalized expression is literally the physical Krein--Cayley
disk intensity divided by the adaptive clock power. -/
theorem thetaCuspHawkingFullMirrorKreinCayleyAdaptiveClockRate_eq_div
    (a omega : ℝ) (ha : |a| < 1)
    {lambda : ℝ} (hlambda : lambda ≠ 0) (homega : omega ≠ 0) :
    thetaCuspHawkingFullMirrorKreinCayleyAdaptiveClockRate a omega ha lambda =
      Complex.normSq
          (thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate a lambda omega) /
        (lambda * (omega / 2)) ^
          (2 * thetaCuspHawkingFullMirrorSectorCouplingOrder a omega ha) := by
  let m := thetaCuspHawkingFullMirrorSectorCouplingOrder a omega ha
  have ht : lambda * (omega / 2) ≠ 0 :=
    mul_ne_zero hlambda (div_ne_zero homega (by norm_num))
  have hnormpow :
      Complex.normSq (((lambda * (omega / 2) : ℝ) : ℂ) ^ m) =
        (lambda * (omega / 2)) ^ (2 * m) := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, pow_two]
    rw [← mul_pow, pow_mul]
    congr 1
    simpa [pow_two] using sq_abs (lambda * (omega / 2))
  rw [thetaCuspHawkingFullMirrorKreinCayleyAdaptiveClockRate]
  rw [show thetaCuspHawkingFullMirrorSectorCouplingOrder a omega ha = m by rfl]
  rw [Complex.normSq_mul, Complex.normSq_inv, hnormpow]
  simp only [div_eq_mul_inv]
  rw [mul_comm]

/-- **Adaptive full S-matrix clock.** Every positive-frequency theta-mirror sector has a finite
strictly positive canonical Krein--Cayley disk rate on its own `lambda ^ (-2*m)` clock. -/
theorem exists_pos_tendsto_thetaCuspHawkingFullMirrorKreinCayleyAdaptiveClockRate
    (a omega : ℝ) (ha : |a| < 1) (homega : 0 < omega) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto
        (thetaCuspHawkingFullMirrorKreinCayleyAdaptiveClockRate a omega ha)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  let m := thetaCuspHawkingFullMirrorSectorCouplingOrder a omega ha
  let F := thetaCuspHawkingEikonalCouplingEntire a ha omega
  have hF : ∀ z, AnalyticAt ℂ F z := fun z =>
    thetaCuspHawkingEikonalCouplingEntire_analyticOnNhd
      a ha omega z (Set.mem_univ z)
  have hord : analyticOrderAt F 0 = (m : ℕ∞) :=
    analyticOrderAt_thetaCuspHawkingEikonalCouplingEntire_zero a omega ha
  obtain ⟨g, hg, hg0, hfactor⟩ :=
    exists_entire_factor_of_analyticOrderAt_eq hF 0 m hord
  let c : ℂ := (((1 / (2 * Real.pi) : ℝ) : ℂ))
  let leading : ℂ := c * g 0 / 2
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr <|
    div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hleading : leading ≠ 0 :=
    div_ne_zero (mul_ne_zero hc hg0) (by norm_num)
  refine ⟨Complex.normSq leading, Complex.normSq_pos.mpr hleading, ?_⟩
  have ht : Tendsto (fun lambda : ℝ => ((lambda * (omega / 2) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hreal : Tendsto (fun lambda : ℝ => lambda * (omega / 2))
        (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have hconst : Tendsto (fun _ : ℝ => omega / 2)
          (𝓝 (0 : ℝ)) (𝓝 (omega / 2)) := tendsto_const_nhds
      simpa using tendsto_id.mul hconst
    have hfull := (Complex.continuous_ofReal.tendsto 0).comp hreal
    exact hfull.mono_left nhdsWithin_le_nhds
  have hg_tendsto : Tendsto
      (fun lambda : ℝ => g (((lambda * (omega / 2) : ℝ) : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) := (hg 0).continuousAt.tendsto.comp ht
  have hbeta : Tendsto
      (fun lambda : ℝ => thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hFt : Tendsto
        (fun lambda : ℝ => F (((lambda * (omega / 2) : ℝ) : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      convert (hF 0).continuousAt.tendsto.comp ht using 1
      · funext lambda
        push_cast
        rfl
      · simp [F, thetaCuspHawkingEikonalCouplingEntire_zero]
    have hcT : Tendsto (fun _ : ℝ => c) (𝓝[>] (0 : ℝ)) (𝓝 c) :=
      tendsto_const_nhds
    have hscaled : Tendsto
        (fun lambda : ℝ => c * F (((lambda * (omega / 2) : ℝ) : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hcT.mul hFt
    apply hscaled.congr'
    filter_upwards with lambda
    simpa [c, F] using
      (thetaCuspHawkingFullMirrorBogoliubovBeta_eq_eikonalCouplingEntire
        a lambda omega ha homega.ne').symm
  have hnumber : Tendsto
      (fun lambda : ℝ => thetaCuspHawkingFullMirrorBogoliubovNumber a lambda omega)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [thetaCuspHawkingFullMirrorBogoliubovNumber] using hbeta.norm.pow 2
  have hgain : Tendsto
      (fun lambda : ℝ => thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
    have hadd := hone.add hnumber
    have hadd' : Tendsto
        (fun lambda : ℝ =>
          1 + thetaCuspHawkingFullMirrorBogoliubovNumber a lambda omega)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by simpa using hadd
    have hsqrt := (Real.continuous_sqrt.tendsto 1).comp hadd'
    change Tendsto
      (fun lambda : ℝ => Real.sqrt
        (1 + thetaCuspHawkingFullMirrorBogoliubovNumber a lambda omega))
      (𝓝[>] (0 : ℝ)) (𝓝 1)
    convert hsqrt using 1
    · funext lambda
      rfl
    · norm_num
  have hden : Tendsto
      (fun lambda : ℝ =>
        ((thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1 : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℂ)) := by
    convert Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hgain.add_const 1) using 1
    · funext lambda
      push_cast
      simp
    · norm_num
  have hnormalized : Tendsto
      (fun lambda : ℝ =>
        c * g (((lambda * (omega / 2) : ℝ) : ℂ)) /
          ((thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1 : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 leading) := by
    have hcT : Tendsto (fun _ : ℝ => c) (𝓝[>] (0 : ℝ)) (𝓝 c) :=
      tendsto_const_nhds
    convert (hcT.mul hg_tendsto).div hden (by norm_num) using 1
    funext lambda
    simp
  have hrate : Tendsto
      (fun lambda : ℝ => Complex.normSq
        (c * g (((lambda * (omega / 2) : ℝ) : ℂ)) /
          ((thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1 : ℝ) : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (Complex.normSq leading)) := by
    exact Complex.continuous_normSq.continuousAt.tendsto.comp hnormalized
  apply hrate.congr'
  filter_upwards [self_mem_nhdsWithin] with lambda hlambda
  have hlambda0 : lambda ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hlambda)
  have ht0 : lambda * (omega / 2) ≠ 0 :=
    mul_ne_zero hlambda0 (div_ne_zero homega.ne' (by norm_num))
  let tc : ℂ := ((lambda * (omega / 2) : ℝ) : ℂ)
  have hpow : tc ^ m ≠ 0 :=
    pow_ne_zero m (Complex.ofReal_ne_zero.mpr ht0)
  simp only [thetaCuspHawkingFullMirrorKreinCayleyAdaptiveClockRate]
  rw [show thetaCuspHawkingFullMirrorSectorCouplingOrder a omega ha = m by rfl]
  rw [thetaCuspHawkingFullMirrorBogoliubovCayleyCoordinate,
    thetaCuspHawkingFullMirrorBogoliubovBeta_eq_eikonalCouplingEntire
      a lambda omega ha homega.ne']
  rw [show thetaCuspHawkingEikonalCouplingEntire a ha omega
      ((lambda * (omega / 2) : ℝ) : ℂ) =
        F ((lambda * (omega / 2) : ℝ) : ℂ) by rfl, hfactor]
  change Complex.normSq
      (c * g tc /
        ((thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1 : ℝ) : ℂ)) =
    Complex.normSq
      ((tc ^ m)⁻¹ *
        ((c * ((tc - 0) ^ m * g tc)) /
          ((thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega + 1 : ℝ) : ℂ)))
  apply congrArg Complex.normSq
  rw [sub_zero]
  field_simp [hpow]

/-! ## Clock synchronization and RH -/

/-- Intensity exponent of the sector-dependent full-mirror scattering clock. -/
def thetaCuspHawkingFullMirrorKreinCayleyClockExponent
    (a total : ℝ) (ha : |a| < 1) : ℕ :=
  2 * thetaCuspHawkingFullMirrorSectorCouplingOrder a total ha

/-- Every positive physical sector admits a finite positive adaptive Krein--Cayley rate. -/
def ThetaCuspHawkingFullMirrorEverySectorHasAdaptiveKreinCayleyClock : Prop :=
  ∀ (a omega : ℝ) (ha : |a| < 1), 0 < omega →
    ∃ L : ℝ, 0 < L ∧
      Tendsto
        (thetaCuspHawkingFullMirrorKreinCayleyAdaptiveClockRate a omega ha)
        (𝓝[>] (0 : ℝ)) (𝓝 L)

/-- Full nonlinear theta-mirror scattering activates every positive tilted sector after its exact
sector-dependent clock is used.  This statement is unconditional. -/
theorem thetaCuspHawkingFullMirrorEverySectorHasAdaptiveKreinCayleyClock :
    ThetaCuspHawkingFullMirrorEverySectorHasAdaptiveKreinCayleyClock := by
  intro a omega ha homega
  exact exists_pos_tendsto_thetaCuspHawkingFullMirrorKreinCayleyAdaptiveClockRate
    a omega ha homega

/-- All source-labelled sectors share the standard quadratic Hawking clock. -/
def ThetaCuspHawkingFullMirrorUniversalQuadraticKreinCayleyClock : Prop :=
  ∀ (a total : ℝ) (ha : |a| < 1), a ≠ 0 →
    thetaCuspHawkingFullMirrorKreinCayleyClockExponent a total ha = 2

/-- **Adaptive-clock Hawking endpoint.** Every sector has an adaptive full-scattering clock
unconditionally.  RH is exactly absence of clock dispersion: every noncentral tilted sector has
the common quadratic exponent selected by the ordinary Davies weak-coupling limit. -/
theorem riemannHypothesis_iff_thetaCuspHawkingFullMirrorUniversalQuadraticKreinCayleyClock :
    RiemannHypothesis ↔
      ThetaCuspHawkingFullMirrorUniversalQuadraticKreinCayleyClock := by
  rw [riemannHypothesis_iff_thetaCuspHawkingFullMirrorNoOrderJump]
  constructor
  · intro h a total ha hane
    simp [thetaCuspHawkingFullMirrorKreinCayleyClockExponent,
      h a total ha hane]
  · intro h a total ha hane
    have hexp := h a total ha hane
    simp only [thetaCuspHawkingFullMirrorKreinCayleyClockExponent] at hexp
    omega

end RHTower
