import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullMirrorValueMixingEndpoint

/-!
# Standard-clock selection for the full theta-cusp Hawking mirror

The exact Davies--Fulling numerator has nonlinear coupling channels.  Feeding that numerator into
the conservative Hawking KMS collision therefore makes every fixed tilted sector mix at some
arbitrarily weak nonzero coupling, even when its Born coefficient vanishes.  This is the coherent
multi-step effect behind the full-mirror order-jump no-go.

The weak-coupling clock distinguishes direct and indirect channels.  For the exact eikonal-fed
Cayley collision, let `T(lambda)` be its transition amplitude and divide the one-collision
probability by `lambda^2`.  This is the standard van Hove/Davies collision rate.  The exact limit is

`|T(lambda)|^2 / lambda^2  ->  (omega^4 / 4) |XiC(omega + a i)|^2`.

Thus the Cayley denominator and every nonlinear eikonal channel disappear only after the full
finite-coupling collision has been built.  A sector whose first nonzero coherent path has order
`m > 1` mixes at fixed coupling but freezes on the common `lambda^(-2)` Hawking clock, since its
rate has order `lambda^(2*m-2)`.  This is the source-faithful distinction between graph
connectivity and a direct interaction edge suggested by short-time quantum-walk asymptotics.

The resulting endpoint is not the false claim that the raw full-mirror amplitude is itself a
Cayley S-matrix.  It says that the exact eikonal-fed conservative dilation has a canonical tangent
semigroup.  RH is equivalent to nondegenerate limiting relaxation of every positive-frequency,
noncentral tilted sector on this one standard clock.

The scaling is the repeated-interaction weak-coupling regime of Attal--Joye
(`arXiv:math-ph/0501012`).  Higher-order Fermi-golden-rule channels can live on slower clocks; this
file proves that the standard Hawking/Davies clock excludes them rather than pretending they do
not exist.
-/

open Complex Real Filter Topology

noncomputable section

namespace RHTower

/-- Transition probability per unit standard van-Hove time for the exact eikonal-fed Cayley
collision.  The punctured limit at zero coupling is the physical object; Lean's value at zero is
harmless. -/
def thetaCuspHawkingFullMirrorCayleyVanHoveRate
    (a lambda omega : ℝ) : ℝ :=
  Complex.normSq
      (thetaCuspHawkingFullMirrorCayleyTransition a lambda omega) /
    lambda ^ 2

theorem thetaCuspHawkingFullMirrorCayleyVanHoveRate_nonneg
    (a lambda omega : ℝ) :
    0 ≤ thetaCuspHawkingFullMirrorCayleyVanHoveRate a lambda omega := by
  exact div_nonneg (Complex.normSq_nonneg _) (sq_nonneg lambda)

/-- Exact theta-source coefficient selected by the common `lambda^(-2)` Hawking clock. -/
def thetaCuspHawkingFullMirrorVanHoveLimitRate
    (a omega : ℝ) : ℝ :=
  omega ^ 4 / 4 *
    Complex.normSq (XiC ((omega : ℂ) + (a : ℂ) * Complex.I))

theorem thetaCuspHawkingFullMirrorVanHoveLimitRate_nonneg
    (a omega : ℝ) :
    0 ≤ thetaCuspHawkingFullMirrorVanHoveLimitRate a omega := by
  unfold thetaCuspHawkingFullMirrorVanHoveLimitRate
  have hpow : 0 ≤ omega ^ 4 := by
    rw [show omega ^ 4 = (omega ^ 2) ^ 2 by ring]
    exact sq_nonneg _
  exact mul_nonneg (div_nonneg hpow (by norm_num))
    (Complex.normSq_nonneg _)

/-- Balanced first variation of the exact mirror has precisely the stated van-Hove rate. -/
theorem normSq_thetaCuspTiltedMovingMirrorBornRaw_balanced_eq_vanHoveLimitRate
    (a : ℝ) (ha : |a| < 1) (omega : ℝ) :
    Complex.normSq
        (thetaCuspTiltedMovingMirrorBornRaw a ha (omega / 2) (omega / 2)) =
      thetaCuspHawkingFullMirrorVanHoveLimitRate a omega := by
  rw [thetaCuspTiltedMovingMirrorBornRaw_eq_XiC ha]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]
  norm_num [Complex.normSq_apply,
    thetaCuspHawkingFullMirrorVanHoveLimitRate]
  all_goals
    ring_nf
    simp

/-- **[PROVED] Exact full-collision van-Hove selection.**  Construct the complete nonlinear
eikonal-fed conservative collision first, then take its standard weak-coupling rate.  Its limit is
the squared direct theta/Xi interaction coefficient; the Cayley denominator and all indirect
higher coupling paths vanish in the limit. -/
theorem tendsto_thetaCuspHawkingFullMirrorCayleyVanHoveRate
    (a : ℝ) (ha : |a| < 1) (omega : ℝ) :
    Tendsto
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorCayleyVanHoveRate a lambda omega)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (thetaCuspHawkingFullMirrorVanHoveLimitRate a omega)) := by
  let A : ℝ → ℂ := fun lambda =>
    thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega
  let j : ℝ → ℝ := fun lambda =>
    thetaCuspHawkingFullMirrorCayleyLoad a lambda omega
  have hscaled :=
    tendsto_thetaCuspHawkingFullMirrorBornScaledPairProbability
      a ha (omega / 2) (omega / 2)
  have hA0 : A 0 = 0 := by
    dsimp [A, thetaCuspHawkingBalancedFullMirrorAmplitude]
    rw [thetaCuspHawkingFullMirrorAmplitude_eq_eikonalFourier a ha]
    rw [thetaCuspHawkingEikonalFourier,
      Real.fourier_real_eq_integral_exp_smul]
    simp [thetaCuspHawkingEikonalPhaseDefect]
  have hAcont : ContinuousAt A 0 := by
    exact (hasDerivAt_thetaCuspHawkingFullMirrorAmplitude_zero
      a ha (omega / 2) (omega / 2)).continuousAt
  have hjcont : ContinuousAt j 0 := by
    have hn : ContinuousAt (fun lambda => Complex.normSq (A lambda)) 0 := by
      simpa [Function.comp_def] using
        Complex.continuous_normSq.continuousAt.comp_of_eq hAcont rfl
    change ContinuousAt (fun lambda => Complex.normSq (A lambda) / 4) 0
    exact hn.div_const 4
  have hj0 : j 0 = 0 := by
    change Complex.normSq (A 0) / 4 = 0
    rw [hA0]
    norm_num
  have hj : Tendsto j (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hbase : Tendsto j (𝓝[≠] (0 : ℝ)) (𝓝 (j 0)) :=
      hjcont.tendsto.mono_left inf_le_left
    simpa only [hj0] using hbase
  have hden : Tendsto (fun lambda : ℝ => (1 + j lambda) ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa using (hj.const_add 1).pow 2
  have hquot := hscaled.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hfun :
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorCayleyVanHoveRate a lambda omega) =
        fun lambda : ℝ =>
          thetaCuspHawkingFullMirrorBornScaledPairProbability
              a lambda (omega / 2) (omega / 2) /
            (1 + j lambda) ^ 2 := by
    funext lambda
    rw [thetaCuspHawkingFullMirrorCayleyVanHoveRate,
      thetaCuspHawkingFullMirrorCayleyTransition,
      thetaCuspHawkingFullMirrorBornScaledPairProbability]
    change Complex.normSq
        (thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega /
          (((1 + j lambda : ℝ) : ℂ))) / lambda ^ 2 = _
    rw [Complex.normSq_div, Complex.normSq_ofReal]
    rw [show thetaCuspHawkingFullMirrorAmplitude a lambda
        (omega / 2) (omega / 2) =
          thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega by rfl]
    rw [pow_two]
    ring
  rw [hfun]
  have hquot0 : Tendsto
      ((fun lambda : ℝ =>
          thetaCuspHawkingFullMirrorBornScaledPairProbability
            a lambda (omega / 2) (omega / 2)) /
        (fun lambda : ℝ => (1 + j lambda) ^ 2))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (Complex.normSq
        (thetaCuspTiltedMovingMirrorBornRaw a ha (omega / 2) (omega / 2)))) := by
    simpa only [div_one] using hquot
  have hquot1 : Tendsto
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorBornScaledPairProbability
            a lambda (omega / 2) (omega / 2) /
          (1 + j lambda) ^ 2)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (Complex.normSq
        (thetaCuspTiltedMovingMirrorBornRaw a ha (omega / 2) (omega / 2)))) := by
    convert hquot0 using 1
    funext lambda
    rfl
  rw [normSq_thetaCuspTiltedMovingMirrorBornRaw_balanced_eq_vanHoveLimitRate
    a ha omega] at hquot1
  exact hquot1

/-- A positive-frequency sector has nonzero limiting Hawking rate exactly when its direct
theta/Xi interaction edge is present. -/
theorem thetaCuspHawkingFullMirrorVanHoveLimitRate_pos_iff
    {a omega : ℝ} (homega : 0 < omega) :
    0 < thetaCuspHawkingFullMirrorVanHoveLimitRate a omega ↔
      XiC ((omega : ℂ) + (a : ℂ) * Complex.I) ≠ 0 := by
  rw [thetaCuspHawkingFullMirrorVanHoveLimitRate]
  have hfac : 0 < omega ^ 4 / 4 := by positivity
  constructor
  · intro hpos hXi
    rw [hXi, Complex.normSq_zero, mul_zero] at hpos
    linarith
  · intro hXi
    exact mul_pos hfac (Complex.normSq_pos.mpr hXi)

/-- **[PROVED NO-GO] Higher coherent paths freeze on the standard Hawking clock.**  If the direct
theta/Xi coefficient is dark, the exact nonperturbative Cayley collision may still mix at every
small nonzero coupling, but its transition probability per unit `lambda^(-2)` time tends to zero. -/
theorem tendsto_thetaCuspHawkingFullMirrorCayleyVanHoveRate_zero_of_XiC_eq_zero
    (a : ℝ) (ha : |a| < 1) (omega : ℝ)
    (hXi : XiC ((omega : ℂ) + (a : ℂ) * Complex.I) = 0) :
    Tendsto
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorCayleyVanHoveRate a lambda omega)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have h := tendsto_thetaCuspHawkingFullMirrorCayleyVanHoveRate a ha omega
  simpa [thetaCuspHawkingFullMirrorVanHoveLimitRate, hXi] using h

/-- Limiting transverse population flow selected by the exact full collision on the standard
van-Hove clock. -/
def thetaCuspHawkingFullMirrorVanHoveDeviationFlow
    (a omega t c : ℝ) : ℝ :=
  Real.exp
      (-thetaCuspHawkingFullMirrorVanHoveLimitRate a omega * t) * c

/-- The Poissonized exact-collision flow converges pointwise to the source-selected van-Hove
semigroup. -/
theorem tendsto_thetaCuspHawkingFullMirrorCayleyVanHoveDeviationFlow
    (a : ℝ) (ha : |a| < 1) (omega t c : ℝ) :
    Tendsto
      (fun lambda : ℝ =>
        Real.exp
            (-thetaCuspHawkingFullMirrorCayleyVanHoveRate
              a lambda omega * t) * c)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (thetaCuspHawkingFullMirrorVanHoveDeviationFlow
        a omega t c)) := by
  have hrate :=
    tendsto_thetaCuspHawkingFullMirrorCayleyVanHoveRate a ha omega
  have hcont : ContinuousAt
      (fun rate : ℝ => Real.exp (-rate * t) * c)
      (thetaCuspHawkingFullMirrorVanHoveLimitRate a omega) := by
    fun_prop
  simpa [thetaCuspHawkingFullMirrorVanHoveDeviationFlow,
    Function.comp_def] using
    hcont.tendsto.comp hrate

/-- Limiting relaxation of one tilted sector on the common Hawking/Davies clock. -/
def ThetaCuspHawkingFullMirrorVanHoveSectorMixes
    (a omega : ℝ) : Prop :=
  ∀ c : ℝ,
    Tendsto
      (fun t : ℝ =>
        thetaCuspHawkingFullMirrorVanHoveDeviationFlow a omega t c)
      atTop (𝓝 0)

theorem thetaCuspHawkingFullMirrorVanHoveSectorMixes_iff_rate_pos
    (a omega : ℝ) :
    ThetaCuspHawkingFullMirrorVanHoveSectorMixes a omega ↔
      0 < thetaCuspHawkingFullMirrorVanHoveLimitRate a omega := by
  constructor
  · intro hmix
    have hnonneg :=
      thetaCuspHawkingFullMirrorVanHoveLimitRate_nonneg a omega
    rcases hnonneg.eq_or_lt with hzero | hpos
    · have hzero' :
          thetaCuspHawkingFullMirrorVanHoveLimitRate a omega = 0 := hzero.symm
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) := by
        simpa [thetaCuspHawkingFullMirrorVanHoveDeviationFlow, hzero'] using
          hmix 1
      have hone : (1 : ℝ) = 0 := tendsto_const_nhds_iff.mp hconst
      norm_num at hone
    · exact hpos
  · intro hrate c
    have hscale : Tendsto
        (fun t : ℝ =>
          thetaCuspHawkingFullMirrorVanHoveLimitRate a omega * t)
        atTop atTop :=
      Filter.Tendsto.const_mul_atTop hrate tendsto_id
    have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
    simpa [thetaCuspHawkingFullMirrorVanHoveDeviationFlow] using
      hexp.mul_const c

theorem thetaCuspHawkingFullMirrorVanHoveSectorMixes_iff_XiC_ne_zero
    {a omega : ℝ} (homega : 0 < omega) :
    ThetaCuspHawkingFullMirrorVanHoveSectorMixes a omega ↔
      XiC ((omega : ℂ) + (a : ℂ) * Complex.I) ≠ 0 := by
  rw [thetaCuspHawkingFullMirrorVanHoveSectorMixes_iff_rate_pos,
    thetaCuspHawkingFullMirrorVanHoveLimitRate_pos_iff homega]

/-- Every positive-frequency, noncentral tilted sector relaxes on the same standard
`lambda^(-2)` Hawking clock.  Unlike finite-coupling mixing, this excludes delayed higher-order
channels. -/
def ThetaCuspHawkingFullMirrorStandardClockMixing : Prop :=
  ∀ (a omega : ℝ), 0 < omega → |a| < 1 → a ≠ 0 →
    ThetaCuspHawkingFullMirrorVanHoveSectorMixes a omega

/-- **[BRIDGE] [NOVELTY UNVERIFIED] Full-mirror standard-clock endpoint.**  RH is equivalent to
nondegenerate limiting relaxation of every noncentral tilted sector after the exact nonlinear
theta-mirror numerator has been Cayley-completed, KMS-dilated, and put on the common van-Hove
clock.  Generic finite-coupling mixing is insufficient; common-clock mixing keeps exactly the
direct theta/Xi edge. -/
theorem riemannHypothesis_iff_thetaCuspHawkingFullMirrorStandardClockMixing :
    RiemannHypothesis ↔ ThetaCuspHawkingFullMirrorStandardClockMixing := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro hreal a omega homega _ha hane
    rw [thetaCuspHawkingFullMirrorVanHoveSectorMixes_iff_XiC_ne_zero homega]
    intro hXi
    have him := hreal ((omega : ℂ) + (a : ℂ) * Complex.I) hXi
    exact hane (by simpa using him)
  · intro hmix z hz
    by_contra hzim
    have hzre : z.re ≠ 0 := by
      intro hre
      have hform : z = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hre]
      rw [hform] at hz
      exact XiC_ne_zero_of_imaginary z.im hz
    have hstrip := xiC_zero_im_mem_openHalf hz
    have ha : |z.im| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    rcases lt_or_gt_of_ne hzre with hneg | hpos
    · have hsector := hmix (-z.im) (-z.re) (by linarith)
          (by simpa using ha) (neg_ne_zero.mpr hzim)
      have hXiNe :=
        (thetaCuspHawkingFullMirrorVanHoveSectorMixes_iff_XiC_ne_zero
          (by linarith)).1 hsector
      apply hXiNe
      have harg :
          (((-z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * Complex.I) = -z := by
        apply Complex.ext <;> simp
      rw [harg, XiC_even]
      exact hz
    · have hsector := hmix z.im z.re hpos ha hzim
      have hXiNe :=
        (thetaCuspHawkingFullMirrorVanHoveSectorMixes_iff_XiC_ne_zero
          hpos).1 hsector
      apply hXiNe
      have harg : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := by
        apply Complex.ext <;> simp
      rwa [harg]

end RHTower
