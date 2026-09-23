import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullMirrorEikonalOrderEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingArakiWoodsDaviesMixingEndpoint

/-!
# Full theta-mirror weak-coupling dilation and least coupling order

This endpoint closes provenance gap between exact Davies--Fulling mirror scattering and preceding
Hawking Araki--Woods/Davies resonance generator. For genuine nonlinear mirror amplitude

`M_a(lambda; outgoing, incoming)
  = -2 incoming * Fourier (exp (-i lambda outgoing k_a) - 1)`,

dominated differentiation at `lambda = 0` gives source-derived Born carrier exactly:

`M_a'(0) = 2 i outgoing incoming XiC(outgoing + incoming + a i)`.

Consequently, coupling-normalized exact transition probability converges to Born probability;
fixed-total-frequency shell of this derivative equals prior Hawking shell density. Thermal doubling
then gives existing KMS width and actual Davies population mixing criterion. This is a derivation
from full scattering, not a postulated scalar Cayley completion.

Finite-coupling dynamics does not select principal channel alone. Every sector has some nonzero
finite eikonal jet unconditionally. We therefore define least nonzero coupling order. It equals one
exactly when principal Xi/Born carrier is nonzero; RH is exactly absence of order jumps across all
noncentral tilted sectors. Thus source-faithful conclusion is:

* `[PAPER-PROVED] [LEAN-PROVED]` full scattering selects Davies/Born dynamics in weak-coupling
  tangent limit;
* `[PAPER-PROVED] [LEAN-PROVED]` all exact sectors mix at some finite coupling order;
* `[RH-EQUIVALENT]` every noncentral tilted sector mixes already at principal order;
* `[FALSIFIED]` KMS or full finite-coupling scattering by itself forces principal-order mixing.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

namespace RHTower

private def weakIntegrand (a total t v : ℝ) : ℂ :=
  Complex.exp (((-total * v : ℝ) : ℂ) * Complex.I) *
    thetaCuspHawkingEikonalPhaseDefect a t v

private def weakDerivIntegrand (a total t v : ℝ) : ℂ :=
  Complex.exp (((-total * v : ℝ) : ℂ) * Complex.I) *
    (Complex.exp (Complex.I * ((-t * thetaCuspTiltedSource a v : ℝ) : ℂ)) *
      (Complex.I * ((-thetaCuspTiltedSource a v : ℝ) : ℂ)))

private theorem hasDerivAt_weakIntegrand (a total t v : ℝ) :
    HasDerivAt (fun q : ℝ => weakIntegrand a total q v)
      (weakDerivIntegrand a total t v) t := by
  let base : ℂ := Complex.exp (((-total * v : ℝ) : ℂ) * Complex.I)
  let rate : ℂ := Complex.I * ((-thetaCuspTiltedSource a v : ℝ) : ℂ)
  have hq : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 t :=
    (hasDerivAt_id t).ofReal_comp
  have hphase : HasDerivAt (fun q : ℝ => Complex.exp ((q : ℂ) * rate))
      (Complex.exp ((t : ℂ) * rate) * rate) t := by
    simpa using (hq.mul_const rate).cexp
  have hdefect : HasDerivAt
      (fun q : ℝ => Complex.exp ((q : ℂ) * rate) - 1)
      (Complex.exp ((t : ℂ) * rate) * rate) t :=
    hphase.sub_const 1
  have hmain := hdefect.const_mul base
  have hphaseEq :
      (fun q : ℝ => thetaCuspHawkingEikonalPhaseDefect a q v) =
        fun q : ℝ => Complex.exp ((q : ℂ) * rate) - 1 := by
    funext q
    unfold thetaCuspHawkingEikonalPhaseDefect
    congr 2
    dsimp [rate]
    push_cast
    ring_nf
  have hderivEq :
      weakDerivIntegrand a total t v =
        base * (Complex.exp ((t : ℂ) * rate) * rate) := by
    unfold weakDerivIntegrand
    dsimp [base, rate]
    congr 2
    · congr 1
      push_cast
      ring
  change HasDerivAt
    (fun q : ℝ => base * thetaCuspHawkingEikonalPhaseDefect a q v)
    (weakDerivIntegrand a total t v) t
  have hfunEq :
      (fun q : ℝ => base * thetaCuspHawkingEikonalPhaseDefect a q v) =
        fun q : ℝ => base * (Complex.exp ((q : ℂ) * rate) - 1) := by
    funext q
    rw [congrFun hphaseEq q]
  rw [hfunEq, hderivEq]
  exact hmain

private theorem norm_weakDerivIntegrand (a total t v : ℝ) :
    ‖weakDerivIntegrand a total t v‖ = thetaCuspTiltedSource a v := by
  rw [weakDerivIntegrand, norm_mul, Complex.norm_exp]
  have hbase :
      ((((-total * v : ℝ) : ℂ) * Complex.I)).re = 0 := by simp
  rw [hbase, Real.exp_zero, one_mul, norm_mul, Complex.norm_exp]
  have hphase :
      (Complex.I * ((-t * thetaCuspTiltedSource a v : ℝ) : ℂ)).re = 0 := by simp
  rw [hphase, Real.exp_zero, one_mul, norm_mul, norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_pos (by
      unfold thetaCuspTiltedSource
      exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all v))]

private theorem integrable_weakMajor (a : ℝ) (ha : |a| < 1) :
    Integrable (thetaCuspTiltedSource a) := by
  let source : 𝓢(ℝ, ℝ) := thetaCuspTiltedSchwartzReal a ha
  exact source.integrable

theorem hasDerivAt_thetaCuspHawkingEikonalFourier_zero
    (a : ℝ) (ha : |a| < 1) (total : ℝ) :
    HasDerivAt (fun t : ℝ => thetaCuspHawkingEikonalFourier a t total)
      (-Complex.I * XiC ((total : ℂ) + (a : ℂ) * Complex.I)) 0 := by
  have hmajor : Integrable (thetaCuspTiltedSource a) := integrable_weakMajor a ha
  have hbase : Integrable (fun v : ℝ => weakIntegrand a total 0 v) := by
    simp [weakIntegrand, thetaCuspHawkingEikonalPhaseDefect]
  have hderivMeas : AEStronglyMeasurable (fun v : ℝ => weakDerivIntegrand a total 0 v) := by
    apply Continuous.aestronglyMeasurable
    have hk : Continuous (thetaCuspTiltedSource a) :=
      (contDiff_thetaCuspTiltedSource a).continuous
    unfold weakDerivIntegrand
    fun_prop
  have hdom : ∀ᵐ v : ℝ, ∀ t ∈ (Set.univ : Set ℝ),
      ‖weakDerivIntegrand a total t v‖ ≤ thetaCuspTiltedSource a v := by
    filter_upwards with v
    intro t _
    rw [norm_weakDerivIntegrand]
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t v => weakIntegrand a total t v)
    (F' := fun t v => weakDerivIntegrand a total t v)
    (x₀ := (0 : ℝ)) (s := Set.univ) (bound := thetaCuspTiltedSource a)
    (by simp)
    (Filter.Eventually.of_forall fun t => by
      apply Continuous.aestronglyMeasurable
      have hk : Continuous (thetaCuspTiltedSource a) :=
        (contDiff_thetaCuspTiltedSource a).continuous
      unfold weakIntegrand thetaCuspHawkingEikonalPhaseDefect
      fun_prop)
    hbase hderivMeas hdom hmajor
    (by
      filter_upwards with v
      intro t _
      exact hasDerivAt_weakIntegrand a total t v)
  have hfun : (fun t : ℝ => thetaCuspHawkingEikonalFourier a t total) =
      fun t : ℝ => ∫ v : ℝ, weakIntegrand a total t v := by
    funext t
    rw [thetaCuspHawkingEikonalFourier,
      Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with v
    simp only [smul_eq_mul]
    unfold weakIntegrand
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]
  have hjet : (∫ v : ℝ, weakDerivIntegrand a total 0 v) =
      -Complex.I * XiC ((total : ℂ) + (a : ℂ) * Complex.I) := by
    rw [← fourier_thetaCuspTiltedSchwartz_scaled ha total,
      SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with v
    simp only [smul_eq_mul]
    rw [weakDerivIntegrand]
    have hphase :
        Complex.exp (Complex.I * ((-(0 : ℝ) * thetaCuspTiltedSource a v : ℝ) : ℂ)) = 1 := by simp
    rw [hphase, one_mul]
    rw [thetaCuspTiltedSchwartz_apply]
    have hexp :
        Complex.exp (((-total * v : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((-2 * Real.pi * v * (total / (2 * Real.pi)) : ℝ) : ℂ) *
            Complex.I) := by
      congr 1
      push_cast
      field_simp [Real.pi_ne_zero]
    rw [hexp]
    rw [thetaCuspTiltedSource]
    push_cast
    ring_nf
  rw [hfun, ← hjet]
  exact hresult.2

/-- Exact full-mirror coupling tangent is the source-derived tilted Born numerator. -/
theorem hasDerivAt_thetaCuspHawkingFullMirrorAmplitude_zero
    (a : ℝ) (ha : |a| < 1) (outgoing incoming : ℝ) :
    HasDerivAt
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorAmplitude a lambda outgoing incoming)
      (thetaCuspTiltedMovingMirrorBornRaw a ha outgoing incoming) 0 := by
  have heik := hasDerivAt_thetaCuspHawkingEikonalFourier_zero
    a ha (incoming + outgoing)
  have hinner : HasDerivAt (fun lambda : ℝ => lambda * outgoing) outgoing 0 := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id (0 : ℝ)).mul_const outgoing
  have heik' : HasDerivAt
      (fun t : ℝ =>
        thetaCuspHawkingEikonalFourier a t (incoming + outgoing))
      (-Complex.I * XiC ((incoming + outgoing : ℝ) + a * Complex.I))
      (0 * outgoing) := by
    simpa only [zero_mul] using heik
  have hcomp : HasDerivAt
      (fun lambda : ℝ =>
        thetaCuspHawkingEikonalFourier a (lambda * outgoing)
          (incoming + outgoing))
      ((-Complex.I * XiC ((incoming + outgoing : ℝ) + a * Complex.I)) * outgoing)
      0 := by
    simpa [Function.comp_def, mul_comm] using
      (HasFDerivAt.comp 0 heik'.hasFDerivAt
        hinner.hasFDerivAt).hasDerivAt
  have hscaled := HasDerivAt.const_mul (((-2 * incoming : ℝ) : ℂ)) hcomp
  have hfun :
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorAmplitude a lambda outgoing incoming) =
      fun lambda : ℝ =>
        ((-2 * incoming : ℝ) : ℂ) *
          thetaCuspHawkingEikonalFourier a (lambda * outgoing)
            (incoming + outgoing) := by
    funext lambda
    exact thetaCuspHawkingFullMirrorAmplitude_eq_eikonalFourier
      a ha lambda outgoing incoming
  rw [hfun]
  have hvalue :
      (((-2 * incoming : ℝ) : ℂ) *
          ((-Complex.I * XiC ((incoming + outgoing : ℝ) + a * Complex.I)) *
            outgoing)) =
        thetaCuspTiltedMovingMirrorBornRaw a ha outgoing incoming := by
    rw [thetaCuspTiltedMovingMirrorBornRaw_eq_XiC ha]
    push_cast
    ring_nf
  exact hvalue ▸ hscaled

/-- Coupling-normalized transition probability of the exact nonlinear theta mirror. -/
def thetaCuspHawkingFullMirrorBornScaledPairProbability
    (a lambda outgoing incoming : ℝ) : ℝ :=
  Complex.normSq
      (thetaCuspHawkingFullMirrorAmplitude a lambda outgoing incoming) /
    lambda ^ (2 : ℕ)

/-- Exact weak-coupling selection: normalized full-mirror probability converges to Born
probability, despite all nonlinear eikonal channels at finite coupling. -/
theorem tendsto_thetaCuspHawkingFullMirrorBornScaledPairProbability
    (a : ℝ) (ha : |a| < 1) (outgoing incoming : ℝ) :
    Tendsto
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorBornScaledPairProbability
          a lambda outgoing incoming)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (Complex.normSq
        (thetaCuspTiltedMovingMirrorBornRaw a ha outgoing incoming))) := by
  have hderiv := hasDerivAt_thetaCuspHawkingFullMirrorAmplitude_zero
    a ha outgoing incoming
  have hzero : thetaCuspHawkingFullMirrorAmplitude a 0 outgoing incoming = 0 := by
    rw [thetaCuspHawkingFullMirrorAmplitude_eq_eikonalFourier a ha]
    rw [thetaCuspHawkingEikonalFourier, Real.fourier_real_eq_integral_exp_smul]
    simp [thetaCuspHawkingEikonalPhaseDefect]
  have hslope := hderiv.tendsto_slope_zero
  have hslope' :
      Tendsto
        (fun lambda : ℝ =>
          thetaCuspHawkingFullMirrorAmplitude a lambda outgoing incoming /
            (lambda : ℂ))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (thetaCuspTiltedMovingMirrorBornRaw a ha outgoing incoming)) := by
    simpa [hzero, div_eq_inv_mul, smul_eq_mul] using hslope
  have hnorm := Complex.continuous_normSq.continuousAt.tendsto.comp hslope'
  change Tendsto
    (fun lambda : ℝ => Complex.normSq
      (thetaCuspHawkingFullMirrorAmplitude a lambda outgoing incoming /
        (lambda : ℂ)))
    (nhdsWithin (0 : ℝ) {0}ᶜ)
    (nhds (Complex.normSq
      (thetaCuspTiltedMovingMirrorBornRaw a ha outgoing incoming))) at hnorm
  simpa [thetaCuspHawkingFullMirrorBornScaledPairProbability,
    Complex.normSq_div, Complex.normSq_ofReal, pow_two] using hnorm

/-- Fixed-total-frequency right-channel energy formed from the exact mirror's coupling
derivative, before identifying that derivative with the Born carrier. -/
def thetaCuspHawkingFullMirrorWeakCouplingRightEnergyShellDensity
    (a w : ℝ) : ℝ :=
  ∫ u in 0..w,
    Complex.normSq
        (deriv
          (fun lambda : ℝ =>
            thetaCuspHawkingFullMirrorAmplitude a lambda u (w - u)) 0) /
      (16 * Real.pi ^ (2 : ℕ) * (w - u))

/-- Source-faithful shell weld: the coupling tangent of exact nonlinear scattering is
exactly the shell density used by the Hawking Araki--Woods dilation. -/
theorem thetaCuspHawkingFullMirrorWeakCouplingRightEnergyShellDensity_eq
    (a : ℝ) (ha : |a| < 1) (w : ℝ) :
    thetaCuspHawkingFullMirrorWeakCouplingRightEnergyShellDensity a w =
      thetaCuspHawkingTiltedBornRightEnergyShellDensity a w := by
  rw [thetaCuspHawkingFullMirrorWeakCouplingRightEnergyShellDensity,
    thetaCuspHawkingTiltedBornRightEnergyShellDensity]
  apply intervalIntegral.integral_congr
  intro u _hu
  change
    Complex.normSq
        (deriv
          (fun lambda : ℝ =>
            thetaCuspHawkingFullMirrorAmplitude a lambda u (w - u)) 0) /
        (16 * Real.pi ^ (2 : ℕ) * (w - u)) =
      Complex.normSq
          (thetaCuspHawkingTiltedBornPairKernel a
            (u : ℂ) ((w - u : ℝ) : ℂ)) /
        (16 * Real.pi ^ (2 : ℕ) * (w - u))
  rw [(hasDerivAt_thetaCuspHawkingFullMirrorAmplitude_zero
    a ha u (w - u)).deriv]
  rw [← thetaCuspHawkingTiltedBornPairKernel_real_eq_raw ha]

/-- Exact thermal-width formula with input written as the full mirror's weak-coupling
shell rather than a postulated form factor. -/
theorem thetaCuspHawkingKMSResonanceWidth_eq_fullMirrorWeakCouplingShell
    (kappa a omega : ℝ) (ha : |a| < 1) :
    thetaCuspHawkingKMSResonanceWidth kappa a omega =
      2 * Real.pi *
        ((1 + thetaCuspHawkingKMSBoltzmannRatio kappa omega) /
          (1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega)) *
        thetaCuspHawkingFullMirrorWeakCouplingRightEnergyShellDensity a omega := by
  rw [thetaCuspHawkingFullMirrorWeakCouplingRightEnergyShellDensity_eq a ha]
  unfold thetaCuspHawkingKMSResonanceWidth thetaCuspHawkingKMSUpShell
    thetaCuspHawkingKMSDownShell
  ring

/-- Actual Hawking Davies-sector mixing is equivalent to positivity of the shell obtained
by differentiating the full nonlinear mirror scattering amplitude. -/
theorem thetaCuspHawkingDaviesSectorMixes_iff_fullMirrorWeakCouplingShell_pos
    {kappa a omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega)
    (ha : |a| < 1) :
    ThetaCuspHawkingDaviesSectorMixes kappa a omega ↔
      0 < thetaCuspHawkingFullMirrorWeakCouplingRightEnergyShellDensity a omega := by
  rw [thetaCuspHawkingDaviesSectorMixes_iff_width_pos hkappa homega,
    thetaCuspHawkingKMSResonanceWidth_eq_fullMirrorWeakCouplingShell
      kappa a omega ha]
  have hratio :
      0 < (1 + thetaCuspHawkingKMSBoltzmannRatio kappa omega) /
        (1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega) := by
    apply div_pos
    · have hq := thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega
      linarith
    · exact sub_pos.mpr
        (thetaCuspHawkingKMSBoltzmannRatio_lt_one hkappa homega)
  exact mul_pos_iff_of_pos_left
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) hratio)

/-- Every physical, noncentral tilted full-mirror weak-coupling shell is bright. -/
def ThetaCuspHawkingFullMirrorWeakCouplingShellMixing : Prop :=
  ∀ (a omega : ℝ), 0 < omega → |a| < 1 → a ≠ 0 →
    0 < thetaCuspHawkingFullMirrorWeakCouplingRightEnergyShellDensity a omega

/-- Full-mirror tangent-shell mixing is exactly genuine Hawking Araki--Woods/Davies
resonance-sector mixing. -/
theorem fullMirrorWeakCouplingShellMixing_iff_arakiWoodsDaviesMixing :
    ThetaCuspHawkingFullMirrorWeakCouplingShellMixing ↔
      ThetaCuspHawkingArakiWoodsDaviesMixing := by
  constructor
  · intro h kappa a omega hkappa homega ha hane
    exact (thetaCuspHawkingDaviesSectorMixes_iff_fullMirrorWeakCouplingShell_pos
      hkappa homega ha).2 (h a omega homega ha hane)
  · intro h a omega homega ha hane
    exact (thetaCuspHawkingDaviesSectorMixes_iff_fullMirrorWeakCouplingShell_pos
      (kappa := 1) (by norm_num) homega ha).1
        (h 1 a omega (by norm_num) homega ha hane)

/-- Source-faithful weak-coupling endpoint: RH is equivalent to mixing only after exact
mirror scattering is differentiated, shell-integrated, thermally doubled, and evolved by
the Davies resonance generator. -/
theorem riemannHypothesis_iff_thetaCuspHawkingFullMirrorWeakCouplingShellMixing :
    RiemannHypothesis ↔ ThetaCuspHawkingFullMirrorWeakCouplingShellMixing :=
  riemannHypothesis_iff_thetaCuspHawkingArakiWoodsDaviesMixing.trans
    fullMirrorWeakCouplingShellMixing_iff_arakiWoodsDaviesMixing.symm

/-- First coupling derivative written directly as the entire Hawking pair carrier. -/
theorem deriv_thetaCuspHawkingFullMirrorAmplitude_zero_eq_pairKernel
    (a : ℝ) (ha : |a| < 1) (outgoing incoming : ℝ) :
    deriv
        (fun lambda : ℝ =>
          thetaCuspHawkingFullMirrorAmplitude a lambda outgoing incoming) 0 =
      thetaCuspHawkingTiltedBornPairKernel a
        (outgoing : ℂ) (incoming : ℂ) := by
  rw [(hasDerivAt_thetaCuspHawkingFullMirrorAmplitude_zero
    a ha outgoing incoming).deriv]
  exact (thetaCuspHawkingTiltedBornPairKernel_real_eq_raw
    ha outgoing incoming).symm

/-- Least nonzero coupling-jet order in one exact eikonal scattering sector. -/
noncomputable def thetaCuspHawkingFullMirrorSectorCouplingOrder
    (a w : ℝ) (ha : |a| < 1) : ℕ :=
  Nat.find (thetaCuspHawkingAllOrderSectorJetMixing a w ha)

theorem thetaCuspHawkingFullMirrorSectorCouplingOrder_spec
    (a w : ℝ) (ha : |a| < 1) :
    1 ≤ thetaCuspHawkingFullMirrorSectorCouplingOrder a w ha ∧
      thetaCuspTiltedPowerMoment a
        (thetaCuspHawkingFullMirrorSectorCouplingOrder a w ha) w ≠ 0 :=
  Nat.find_spec (thetaCuspHawkingAllOrderSectorJetMixing a w ha)

/-- Every positive jet below the least coupling order vanishes. -/
theorem thetaCuspHawkingFullMirrorSectorCouplingOrder_lower_eq_zero
    (a w : ℝ) (ha : |a| < 1) (n : ℕ)
    (hnpos : 1 ≤ n)
    (hn : n < thetaCuspHawkingFullMirrorSectorCouplingOrder a w ha) :
    thetaCuspTiltedPowerMoment a n w = 0 := by
  by_contra hne
  exact (Nat.find_min
    (thetaCuspHawkingAllOrderSectorJetMixing a w ha) hn) ⟨hnpos, hne⟩

/-- Coupling order is one exactly when the source-derived principal Hawking channel is bright. -/
theorem thetaCuspHawkingFullMirrorSectorCouplingOrder_eq_one_iff
    (a w : ℝ) (ha : |a| < 1) :
    thetaCuspHawkingFullMirrorSectorCouplingOrder a w ha = 1 ↔
      thetaCuspTiltedPowerMoment a 1 w ≠ 0 := by
  constructor
  · intro horder
    have hspec := thetaCuspHawkingFullMirrorSectorCouplingOrder_spec a w ha
    simpa [horder] using hspec.2
  · intro hprincipal
    apply Nat.le_antisymm
    · exact Nat.find_min'
        (thetaCuspHawkingAllOrderSectorJetMixing a w ha)
        ⟨by omega, hprincipal⟩
    · exact (thetaCuspHawkingFullMirrorSectorCouplingOrder_spec a w ha).1

/-- No noncentral tilted sector undergoes a nonlinear coupling-order jump. -/
def ThetaCuspHawkingFullMirrorNoOrderJump : Prop :=
  ∀ (a w : ℝ) (ha : |a| < 1), a ≠ 0 →
    thetaCuspHawkingFullMirrorSectorCouplingOrder a w ha = 1

theorem fullMirrorNoOrderJump_iff_principalSectorMixing :
    ThetaCuspHawkingFullMirrorNoOrderJump ↔
      ThetaCuspHawkingPrincipalSectorMixing := by
  constructor
  · intro h a w ha hane
    exact (thetaCuspHawkingFullMirrorSectorCouplingOrder_eq_one_iff
      a w ha).1 (h a w ha hane)
  · intro h a w ha hane
    exact (thetaCuspHawkingFullMirrorSectorCouplingOrder_eq_one_iff
      a w ha).2 (h a w ha hane)

/-- RH is exactly absence of coupling-order jumps in every noncentral tilted sector of the
actual full mirror.  Finite-order coupling itself is unconditional. -/
theorem riemannHypothesis_iff_thetaCuspHawkingFullMirrorNoOrderJump :
    RiemannHypothesis ↔ ThetaCuspHawkingFullMirrorNoOrderJump :=
  riemannHypothesis_iff_principalSectorMixing.trans
    fullMirrorNoOrderJump_iff_principalSectorMixing.symm

end RHTower
