import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerFiniteXiJetPacket
import GaloisForLFunctions.RHTower.XiLogDerivNonholonomic
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Full Xi jet admission boundary for literal Meyer cohomology

Literal all-weight Meyer cohomology realizes every finite Xi divisor jet
packet, but it does not realize the unrestricted product of all Xi divisor
jets.  This module proves the negative half of that sharp boundary.

For `0 ≤ σ ≤ 1`, integration by parts in the logarithmic Fourier model gives
the uniform strip estimate

`|τ| ‖M_g(σ + iτ)‖ ≤ ∫ exp |t| (‖g(t)‖ + ‖g'(t)‖) dt`.

Local finiteness and infinitude of the actual Xi divisor then provide a
sequence of divisor points with imaginary parts escaping to infinity.  Every
literal Meyer Mellin transform tends to zero on this sequence.  Hence the
constant unit packet in the unrestricted product of all multiplicity jets is
not source-admissible.

Together with `DeningerMeyerFiniteXiJetPacket`, this is an exact
finite-synthesis/infinite-admission wall.  It rules out a raw product packet
space as the target of an arithmetic comparison; any faithful full divisor
completion must retain the decay forced by the literal Meyer source.

All results are unconditional.  No RH, simplicity, positivity, trace,
numerical computation, inverse Mellin theorem, or global synthesis premise is
used.
-/

open Complex Filter Function Set Topology MeasureTheory
open scoped Classical FourierTransform

namespace RHTower

noncomputable section

/-- Exponentially weighted logarithmic source profile on a vertical line. -/
def deningerMeyerWeightedLogProfile
    (sigma : ℝ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (sigma * t) : ℂ) * g t

theorem hasDerivAt_deningerMeyerWeightedLogProfile
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (sigma t : ℝ) :
    HasDerivAt (deningerMeyerWeightedLogProfile sigma g)
      ((sigma : ℂ) * (Real.exp (sigma * t) : ℂ) * g t +
        (Real.exp (sigma * t) : ℂ) * deriv g t) t := by
  have hexp :
      HasDerivAt (fun u : ℝ => Real.exp (sigma * u))
        (Real.exp (sigma * t) * sigma) t :=
    (Real.hasDerivAt_exp (sigma * t)).comp t
      (by
        convert (hasDerivAt_id t).const_mul sigma using 1 <;>
          simp)
  have hexpC :
      HasDerivAt
        (fun u : ℝ => (Real.exp (sigma * u) : ℂ))
        ((Real.exp (sigma * t) * sigma : ℝ) : ℂ) t :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hexp
  have hgderiv : HasDerivAt g (deriv g t) t :=
    (hg.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  convert hexpC.mul hgderiv using 1 <;>
    try rfl
  push_cast
  ring

theorem integrable_deningerMeyerWeightedLogProfile
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (sigma : ℝ) :
    Integrable (deningerMeyerWeightedLogProfile sigma g) := by
  have h :=
    integrable_deningerMeyerStrongLogMellinJet
      hg 0 (sigma : ℂ)
  apply h.congr
  filter_upwards with t
  simp only [deningerMeyerWeightedLogProfile,
    deningerMeyerStrongLogMellinJet, pow_zero, one_mul,
    Complex.ofReal_mul, Complex.ofReal_exp]

theorem integrable_deriv_deningerMeyerWeightedLogProfile
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (sigma : ℝ) :
    Integrable (deriv (deningerMeyerWeightedLogProfile sigma g)) := by
  have hformula :
      deriv (deningerMeyerWeightedLogProfile sigma g) =
        fun t =>
          (sigma : ℂ) * (Real.exp (sigma * t) : ℂ) * g t +
            (Real.exp (sigma * t) : ℂ) * deriv g t := by
    funext t
    exact
      (hasDerivAt_deningerMeyerWeightedLogProfile
        hg sigma t).deriv
  rw [hformula]
  apply Integrable.add
  · simpa only [deningerMeyerWeightedLogProfile, mul_assoc] using
      (integrable_deningerMeyerWeightedLogProfile hg sigma).const_mul
        (sigma : ℂ)
  · exact
      integrable_deningerMeyerWeightedLogProfile hg.deriv sigma

/--
On a vertical line, the logarithmic Mellin transform is the Fourier transform
of the corresponding exponentially weighted profile.
-/
theorem deningerMeyerStrongLogMellin_eq_fourier_weighted
    (g : DeningerMeyerStrongLogTarget)
    (sigma tau : ℝ) :
    deningerMeyerStrongLogMellin g
        ((sigma : ℂ) + (tau : ℂ) * Complex.I) =
      FourierTransform.fourier
        (deningerMeyerWeightedLogProfile sigma g)
        (-tau / (2 * Real.pi)) := by
  rw [deningerMeyerStrongLogMellin,
    Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  rw [deningerMeyerStrongLogMellinJet]
  simp only [pow_zero, one_mul, smul_eq_mul,
    deningerMeyerWeightedLogProfile]
  rw [Complex.ofReal_exp]
  rw [show
      Complex.exp
            (((-2 * Real.pi * t *
                (-tau / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) *
          (Complex.exp ((sigma * t : ℝ) : ℂ) *
            (g : ℝ → ℂ) t) =
        (Complex.exp
            (((-2 * Real.pi * t *
                (-tau / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((sigma * t : ℝ) : ℂ)) *
            (g : ℝ → ℂ) t by ring]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

/--
One integrable function controls the first integration-by-parts estimate
uniformly throughout the closed critical strip.
-/
def deningerMeyerVerticalMellinMajorant
    (g : ℝ → ℂ) (t : ℝ) : ℝ :=
  Real.exp |t| * (‖g t‖ + ‖deriv g t‖)

theorem integrable_deningerMeyerVerticalMellinMajorant
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g) :
    Integrable (deningerMeyerVerticalMellinMajorant g) := by
  have hg0 :=
    integrable_deningerMeyerStrongLogAbsMoment hg 0 1
  have hg1 :=
    integrable_deningerMeyerStrongLogAbsMoment hg.deriv 0 1
  have hg0' :
      Integrable (fun t : ℝ => Real.exp |t| * ‖g t‖) := by
    simpa only [pow_zero, one_mul, one_mul] using hg0
  have hg1' :
      Integrable (fun t : ℝ =>
        Real.exp |t| * ‖deriv g t‖) := by
    simpa only [pow_zero, one_mul, one_mul] using hg1
  apply (hg0'.add hg1').congr
  filter_upwards with t
  simp only [deningerMeyerVerticalMellinMajorant, Pi.add_apply]
  ring

theorem norm_deriv_deningerMeyerWeightedLogProfile_le_majorant
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    {sigma : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (t : ℝ) :
    ‖deriv (deningerMeyerWeightedLogProfile sigma g) t‖ ≤
      deningerMeyerVerticalMellinMajorant g t := by
  rw [(hasDerivAt_deningerMeyerWeightedLogProfile hg sigma t).deriv]
  have hsigmaAbs : |sigma| ≤ 1 := by
    rw [abs_of_nonneg hsigma0]
    exact hsigma1
  have hst : sigma * t ≤ |t| := by
    calc
      sigma * t ≤ |sigma * t| := le_abs_self _
      _ = |sigma| * |t| := abs_mul _ _
      _ ≤ 1 * |t| :=
        mul_le_mul_of_nonneg_right hsigmaAbs (abs_nonneg t)
      _ = |t| := one_mul _
  have hexp :
      Real.exp (sigma * t) ≤ Real.exp |t| :=
    Real.exp_le_exp.mpr hst
  rw [deningerMeyerVerticalMellinMajorant]
  calc
    ‖(sigma : ℂ) * (Real.exp (sigma * t) : ℂ) * g t +
        (Real.exp (sigma * t) : ℂ) * deriv g t‖ ≤
      ‖(sigma : ℂ) * (Real.exp (sigma * t) : ℂ) * g t‖ +
        ‖(Real.exp (sigma * t) : ℂ) * deriv g t‖ :=
      norm_add_le _ _
    _ = |sigma| * Real.exp (sigma * t) * ‖g t‖ +
        Real.exp (sigma * t) * ‖deriv g t‖ := by
      simp only [norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp |t| * ‖g t‖ +
        Real.exp |t| * ‖deriv g t‖ := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc
          |sigma| * Real.exp (sigma * t) ≤
              1 * Real.exp (sigma * t) :=
            mul_le_mul_of_nonneg_right
              hsigmaAbs (Real.exp_pos _).le
          _ = Real.exp (sigma * t) := one_mul _
          _ ≤ Real.exp |t| := hexp
      · exact
          mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
    _ = Real.exp |t| * (‖g t‖ + ‖deriv g t‖) := by
      ring

/--
Uniform first-order vertical-strip decay for every literal Meyer source.
-/
theorem abs_im_mul_norm_deningerMeyerStrongLogMellin_le
    (g : DeningerMeyerStrongLogTarget)
    {sigma : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (tau : ℝ) :
    |tau| *
        ‖deningerMeyerStrongLogMellin g
          ((sigma : ℂ) + (tau : ℂ) * Complex.I)‖ ≤
      ∫ t : ℝ, deningerMeyerVerticalMellinMajorant g t := by
  let w : ℝ := -tau / (2 * Real.pi)
  have hweighted :
      Integrable (deningerMeyerWeightedLogProfile sigma g) :=
    integrable_deningerMeyerWeightedLogProfile g.property sigma
  have hweightedDiff :
      Differentiable ℝ
        (deningerMeyerWeightedLogProfile sigma g) :=
    fun t =>
      (hasDerivAt_deningerMeyerWeightedLogProfile
        g.property sigma t).differentiableAt
  have hweightedDeriv :
      Integrable
        (deriv (deningerMeyerWeightedLogProfile sigma g)) :=
    integrable_deriv_deningerMeyerWeightedLogProfile
      g.property sigma
  have hfour :=
    congrFun
      (Real.fourier_deriv hweighted hweightedDiff hweightedDeriv)
      w
  have hscalar :
      ((2 * Real.pi * Complex.I * w : ℂ)) =
        (-tau : ℂ) * Complex.I := by
    dsimp only [w]
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hscalar] at hfour
  have hfourBound :
      ‖FourierTransform.fourier
          (deriv (deningerMeyerWeightedLogProfile sigma g)) w‖ ≤
        ∫ t : ℝ,
          ‖deriv (deningerMeyerWeightedLogProfile sigma g) t‖ :=
    by
      simpa only [Real.fourier_real_eq,
        Fourier.fourierIntegral_def] using
        (Fourier.norm_fourierIntegral_le_integral_norm
          Real.fourierChar MeasureTheory.volume
          (deriv (deningerMeyerWeightedLogProfile sigma g)) w)
  calc
    |tau| *
        ‖deningerMeyerStrongLogMellin g
          ((sigma : ℂ) + (tau : ℂ) * Complex.I)‖ =
      ‖(-tau : ℂ) * Complex.I *
        FourierTransform.fourier
          (deningerMeyerWeightedLogProfile sigma g) w‖ := by
        rw [deningerMeyerStrongLogMellin_eq_fourier_weighted]
        dsimp only [w]
        simp only [norm_mul, Complex.norm_real,
          Real.norm_eq_abs, norm_neg, Complex.norm_I,
          mul_one]
    _ = ‖FourierTransform.fourier
        (deriv (deningerMeyerWeightedLogProfile sigma g)) w‖ := by
      rw [hfour]
      rfl
    _ ≤ ∫ t : ℝ,
          ‖deriv (deningerMeyerWeightedLogProfile sigma g) t‖ :=
      hfourBound
    _ ≤
        ∫ t : ℝ, deningerMeyerVerticalMellinMajorant g t := by
      apply integral_mono
      · exact hweightedDeriv.norm
      · exact
          integrable_deningerMeyerVerticalMellinMajorant g.property
      · intro t
        exact
          norm_deriv_deningerMeyerWeightedLogProfile_le_majorant
            g.property hsigma0 hsigma1 t

theorem deningerMeyerStrongLogMellin_tendsto_zero_of_vertical_escape
    (g : DeningerMeyerStrongLogTarget)
    (z : ℕ → ℂ)
    (hre0 : ∀ n, 0 ≤ (z n).re)
    (hre1 : ∀ n, (z n).re ≤ 1)
    (him : Tendsto (fun n => |(z n).im|) atTop atTop) :
    Tendsto
      (fun n => deningerMeyerStrongLogMellin g (z n))
      atTop (𝓝 0) := by
  let C : ℝ :=
    ∫ t : ℝ, deningerMeyerVerticalMellinMajorant g t
  have hupper :
      Tendsto
        (fun n => C / |(z n).im|) atTop (𝓝 0) := by
    have hinv :
        Tendsto
          (fun n => |(z n).im|⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp him
    have hconst :
        Tendsto (fun _ : ℕ => C) atTop (𝓝 C) :=
      tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_zero] using
      hconst.mul hinv
  have hnorm :
      Tendsto
        (fun n => ‖deningerMeyerStrongLogMellin g (z n)‖)
        atTop (𝓝 0) := by
    apply squeeze_zero'
      (g := fun n => C / |(z n).im|)
    · exact Eventually.of_forall fun n => norm_nonneg _
    · filter_upwards [him.eventually (eventually_gt_atTop 0)]
        with n hn
      have hbound :=
        abs_im_mul_norm_deningerMeyerStrongLogMellin_le
          g (hre0 n) (hre1 n) (z n).im
      rw [Complex.re_add_im] at hbound
      apply (le_div_iff₀ hn).mpr
      simpa only [C, mul_comm] using hbound
    · exact hupper
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- Actual Xi divisor points in every bounded norm ball form a finite set. -/
theorem xiDivisorSupport_norm_le_finite
    (R : ℝ) :
    Set.Finite
      {rho : XiDivisorSupport | ‖(rho : ℂ)‖ ≤ R} := by
  let d : ℂ → ℤ :=
    MeromorphicOn.divisor xi Set.univ
  have hlocal : LocallyFiniteSupport d := by
    intro z
    exact
      (MeromorphicOn.divisor xi Set.univ).supportLocallyFiniteWithinDomain'
        z (Set.mem_univ z)
  have hfinite :
      (Metric.closedBall (0 : ℂ) R ∩ d.support).Finite :=
    hlocal.finite_inter_support_of_isCompact
      (ProperSpace.isCompact_closedBall (0 : ℂ) R)
  have hinj :
      Function.Injective
        (fun rho : XiDivisorSupport => (rho : ℂ)) := by
    intro rho tau h
    exact Subtype.ext h
  have hpre :
      ((fun rho : XiDivisorSupport => (rho : ℂ)) ⁻¹'
        (Metric.closedBall (0 : ℂ) R ∩ d.support)).Finite :=
    hfinite.preimage (Set.injOn_of_injective hinj)
  apply hpre.subset
  intro rho hrho
  change ‖(rho : ℂ)‖ ≤ R at hrho
  constructor
  · simpa only [Metric.mem_closedBall, dist_zero_right]
      using hrho
  · simpa only [d] using rho.property

theorem exists_xiDivisorSupport_norm_gt
    (R : ℝ) :
    ∃ rho : XiDivisorSupport, R < ‖(rho : ℂ)‖ := by
  by_contra h
  push Not at h
  have hfinite :=
    xiDivisorSupport_norm_le_finite R
  have hall :
      {rho : XiDivisorSupport | ‖(rho : ℂ)‖ ≤ R} =
        Set.univ :=
    Set.eq_univ_of_forall h
  have hunivFinite :
      (Set.univ : Set XiDivisorSupport).Finite := by
    rw [← hall]
    exact hfinite
  exact Set.infinite_univ hunivFinite

/--
Every positive superlevel set of the literal Meyer transform on the actual Xi
divisor is finite.  Thus the zeroth Xi-jet trace has a canonical `c₀`-type
admission law, stronger than decay along one selected sequence.
-/
theorem deningerMeyerStrongLogMellin_xiSupport_superlevel_finite
    (g : DeningerMeyerStrongLogTarget)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Set.Finite
      {rho : XiDivisorSupport |
        epsilon ≤
          ‖deningerMeyerStrongLogMellin g (rho : ℂ)‖} := by
  let C : ℝ :=
    ∫ t : ℝ, deningerMeyerVerticalMellinMajorant g t
  have hC : 0 ≤ C := by
    apply integral_nonneg
    intro t
    exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg (norm_nonneg _) (norm_nonneg _))
  apply
    (xiDivisorSupport_norm_le_finite
      (C / epsilon + 1)).subset
  intro rho hrho
  change ‖(rho : ℂ)‖ ≤ C / epsilon + 1
  have hre :=
    xi_divisor_support_re_mem_open_unit rho
  have hreAbs : |(rho : ℂ).re| < 1 := by
    rw [abs_of_pos hre.1]
    exact hre.2
  have hbound :=
    abs_im_mul_norm_deningerMeyerStrongLogMellin_le
      g hre.1.le hre.2.le (rho : ℂ).im
  rw [Complex.re_add_im] at hbound
  have him :
      |(rho : ℂ).im| ≤ C / epsilon := by
    apply (le_div_iff₀ hepsilon).2
    calc
      |(rho : ℂ).im| * epsilon ≤
          |(rho : ℂ).im| *
            ‖deningerMeyerStrongLogMellin g (rho : ℂ)‖ :=
        mul_le_mul_of_nonneg_left hrho (abs_nonneg _)
      _ ≤ C := by
        simpa only [C] using hbound
  have hnorm :=
    Complex.norm_le_abs_re_add_abs_im (rho : ℂ)
  linarith

/-- A chosen sequence of actual Xi divisor points escaping every norm ball. -/
noncomputable def deningerMeyerXiVerticalEscape
    (n : ℕ) : XiDivisorSupport :=
  Classical.choose
    (exists_xiDivisorSupport_norm_gt (n + 2))

theorem deningerMeyerXiVerticalEscape_norm_gt
    (n : ℕ) :
    (n : ℝ) + 2 <
      ‖(deningerMeyerXiVerticalEscape n : ℂ)‖ :=
  Classical.choose_spec
    (exists_xiDivisorSupport_norm_gt (n + 2))

theorem deningerMeyerXiVerticalEscape_abs_im_gt
    (n : ℕ) :
    (n : ℝ) + 1 <
      |(deningerMeyerXiVerticalEscape n : ℂ).im| := by
  have hnorm := deningerMeyerXiVerticalEscape_norm_gt n
  have hre :=
    xi_divisor_support_re_mem_open_unit
      (deningerMeyerXiVerticalEscape n)
  have hreAbs :
      |(deningerMeyerXiVerticalEscape n : ℂ).re| < 1 := by
    rw [abs_of_pos hre.1]
    exact hre.2
  have hnormLe :=
    Complex.norm_le_abs_re_add_abs_im
      (deningerMeyerXiVerticalEscape n : ℂ)
  linarith

theorem deningerMeyerXiVerticalEscape_abs_im_tendsto_atTop :
    Tendsto
      (fun n =>
        |(deningerMeyerXiVerticalEscape n : ℂ).im|)
      atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨n, hn⟩ := exists_nat_gt b
  refine ⟨n, ?_⟩
  intro m hm
  have him := deningerMeyerXiVerticalEscape_abs_im_gt m
  have hnm : (n : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  linarith

theorem deningerMeyerStrongLogMellin_tendsto_zero_on_xiVerticalEscape
    (g : DeningerMeyerStrongLogTarget) :
    Tendsto
      (fun n =>
        deningerMeyerStrongLogMellin g
          (deningerMeyerXiVerticalEscape n : ℂ))
      atTop (𝓝 0) := by
  apply
    deningerMeyerStrongLogMellin_tendsto_zero_of_vertical_escape
      g (fun n => (deningerMeyerXiVerticalEscape n : ℂ))
  · intro n
    exact
      (xi_divisor_support_re_mem_open_unit
        (deningerMeyerXiVerticalEscape n)).1.le
  · intro n
    exact
      (xi_divisor_support_re_mem_open_unit
        (deningerMeyerXiVerticalEscape n)).2.le
  · exact deningerMeyerXiVerticalEscape_abs_im_tendsto_atTop

/-- Unrestricted product of every actual Xi divisor jet coordinate. -/
abbrev DeningerMeyerFullXiJetPacket :=
  (rho : XiDivisorSupport) →
    DeningerArithmeticJetIndex rho → ℂ

/-- Simultaneous evaluation into the unrestricted full Xi jet product. -/
def deningerMeyerFullXiJetPacketLM :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ]
      DeningerMeyerFullXiJetPacket :=
  LinearMap.pi fun rho =>
    LinearMap.pi
      (deningerMeyerXiSupportJetEvaluationLM rho)

@[simp]
theorem deningerMeyerFullXiJetPacketLM_apply
    (u : DeningerMeyerStrongLogCohomology)
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    deningerMeyerFullXiJetPacketLM u rho k =
      deningerMeyerXiSupportJetEvaluationLM rho k u :=
  rfl

/-- The constant unit coordinate in the unrestricted divisor product. -/
def deningerMeyerFullXiJetUnitPacket :
    DeningerMeyerFullXiJetPacket :=
  fun _ _ => 1

/--
The unrestricted unit packet is not represented by any literal Meyer class.
-/
theorem deningerMeyerFullXiJetUnitPacket_not_mem_range :
    deningerMeyerFullXiJetUnitPacket ∉
      LinearMap.range deningerMeyerFullXiJetPacketLM := by
  rintro ⟨u, hu⟩
  obtain ⟨g, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (LinearMap.range deningerMeyerStrongLogSumLM) u
  have hvalues :
      (fun n =>
        deningerMeyerStrongLogMellin g
          (deningerMeyerXiVerticalEscape n : ℂ)) =
        fun _ : ℕ => (1 : ℂ) := by
    funext n
    let k0 :
        DeningerArithmeticJetIndex
          (deningerMeyerXiVerticalEscape n) :=
      ⟨0, xiSupportMultiplicity_pos
        (deningerMeyerXiVerticalEscape n)⟩
    have hcoord :=
      congrFun
        (congrFun hu (deningerMeyerXiVerticalEscape n)) k0
    simpa only [
      deningerMeyerFullXiJetPacketLM_apply,
      deningerMeyerXiSupportJetEvaluationLM_mk,
      deningerMeyerFullXiJetUnitPacket,
      k0,
      deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
      iteratedDeriv_zero] using hcoord
  have honeZero :
      Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 0) := by
    rw [← hvalues]
    exact
      deningerMeyerStrongLogMellin_tendsto_zero_on_xiVerticalEscape
        g
  have honeOne :
      Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have : (0 : ℂ) = 1 :=
    tendsto_nhds_unique honeZero honeOne
  norm_num at this

/--
The full unrestricted actual-Xi jet evaluation map is not surjective.
-/
theorem deningerMeyerFullXiJetPacketLM_not_surjective :
    ¬ Function.Surjective deningerMeyerFullXiJetPacketLM := by
  intro hsurj
  exact
    deningerMeyerFullXiJetUnitPacket_not_mem_range
      (hsurj deningerMeyerFullXiJetUnitPacket)

end

end RHTower
