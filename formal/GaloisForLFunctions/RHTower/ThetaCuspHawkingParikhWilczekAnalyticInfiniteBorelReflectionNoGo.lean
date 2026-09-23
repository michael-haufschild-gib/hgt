import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekFiniteBandBorelReflectionNoGo
import GaloisForLFunctions.HTGeometry.GammaVerticalPolynomialDecay
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1
import GaloisForLFunctions.RHTower.ReesAnalyticQuasianalyticity
import GaloisForLFunctions.RHTower.SoninOneSidedPacket
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelDifferentialSystemCoupled

/-!
# Analytic infinite-row Borel reflection no-go for Parikh--Wilczek

The first-winding PW grades are `Gamma(s+2k)/(k!)^(2 : ℕ)`.  A source-independent countable grade row
whose generating kernel is regular at zero has critical-line logarithmic profile

`g_A(u) = exp(u/2-exp(u)) A(exp(2u))`.

Exact production of the functional-equation partner `Gamma(1-s)` requires this profile to have the
same Fourier transform as

`g_R(u) = exp(-u/2-exp(-u))`.

`L^(1 : ℕ)` Fourier uniqueness and continuity classify the kernel pointwise:

`x exp(-x) A(x^(2 : ℕ)) = exp(-1/x)`.

Thus the germ `F(z)=z exp(-z) A(z^(2 : ℕ))` is forced to equal `exp(-1/x)` on the positive ray.  Its
values on `x=exp(-h)` are `exp(-exp(h))`, flat beyond every perturbative grade.  Analytic Rees
quasianalyticity forces an analytic germ with those samples to vanish locally, contradicting their
strict positivity.

This kills every regular, source-independent infinite PW grade resummation in the chain

`PW Borel tower -> FE partner -> Xi-zero partner balance -> Deninger Ward cancellation -> RH`.

The sharp positive survivor is exact: reflection needs a nonzero all-orders-flat reciprocal-energy
sector.  A successor must therefore use a divergent/transseries resummation, a reflected nonlocal
channel, or spectral/source feedback.  No Xi divisor, RH premise, numerical computation, or added
axiom occurs.

`[NEW] [CLASSIFICATION] [NO-GO] [PW-B ROUTE KILL] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex MeasureTheory Filter Set Topology Asymptotics
open scoped FourierTransform

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- Logarithmic critical-line profile of a PW grade-generating multiplier. -/
def schwarzschildParikhWilczekInfiniteBorelLogProfile
    (A : ℂ → ℂ) (u : ℝ) : ℂ :=
  expShiftC (1 / 2) u * A (Real.exp (2 * u) : ℂ)

/-- Logarithmic profile of the functional-equation-reflected Gamma leg. -/
def schwarzschildParikhWilczekReflectedGammaLogProfile (u : ℝ) : ℂ :=
  expShiftC (1 / 2) (-u)

/-- A source-independent infinite PW grade resummation which is regular at zero and realizes
Gamma reflection on the critical line. -/
structure PWAnalyticInfiniteBorelReflectionData where
  multiplier : ℂ → ℂ
  analyticAt_zero : AnalyticAt ℂ multiplier 0
  continuous : Continuous multiplier
  integrable_logProfile :
    Integrable (schwarzschildParikhWilczekInfiniteBorelLogProfile multiplier)
  reflects : ∀ ξ : ℝ,
    𝓕 (schwarzschildParikhWilczekInfiniteBorelLogProfile multiplier) ξ =
      𝓕 schwarzschildParikhWilczekReflectedGammaLogProfile ξ

theorem continuous_schwarzschildParikhWilczekInfiniteBorelLogProfile
    (D : PWAnalyticInfiniteBorelReflectionData) :
    Continuous (schwarzschildParikhWilczekInfiniteBorelLogProfile D.multiplier) := by
  unfold schwarzschildParikhWilczekInfiniteBorelLogProfile
  apply Continuous.mul (contDiff_expShiftC (1 / 2)).continuous
  exact D.continuous.comp
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)))

theorem continuous_schwarzschildParikhWilczekReflectedGammaLogProfile :
    Continuous schwarzschildParikhWilczekReflectedGammaLogProfile := by
  unfold schwarzschildParikhWilczekReflectedGammaLogProfile
  exact (contDiff_expShiftC (1 / 2)).continuous.comp continuous_neg

theorem integrable_schwarzschildParikhWilczekReflectedGammaLogProfile :
    Integrable schwarzschildParikhWilczekReflectedGammaLogProfile := by
  have h := integrable_iteratedDeriv_expShiftC (σ := 1 / 2) (by norm_num) 0
  rw [iteratedDeriv_zero] at h
  change Integrable (fun u : ℝ => expShiftC (1 / 2) (-u))
  exact h.comp_neg

/-- The target profile is exactly the reflected Gamma value on the critical line. -/
theorem fourier_schwarzschildParikhWilczekReflectedGammaLogProfile (ξ : ℝ) :
    𝓕 schwarzschildParikhWilczekReflectedGammaLogProfile ξ =
      Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
  change 𝓕 (fun u : ℝ => expShiftC (1 / 2) (-u)) ξ = _
  rw [fourier_comp_neg]
  have h := fourier_expShiftC (σ := 1 / 2) (by norm_num) (2 * Real.pi * ξ)
  have hfreq : -(2 * Real.pi * ξ) / (2 * Real.pi) = -ξ := by
    field_simp [Real.pi_ne_zero]
  rw [hfreq] at h
  exact h

/-- Fourier uniqueness classifies every exact infinite reflection kernel pointwise. -/
theorem PWAnalyticInfiniteBorelReflectionData.logProfile_eq
    (D : PWAnalyticInfiniteBorelReflectionData) (u : ℝ) :
    schwarzschildParikhWilczekInfiniteBorelLogProfile D.multiplier u =
      schwarzschildParikhWilczekReflectedGammaLogProfile u := by
  have hae := HTGeometry.ae_eq_of_fourierIntegral_eq
    D.integrable_logProfile
    integrable_schwarzschildParikhWilczekReflectedGammaLogProfile D.reflects
  exact eq_at_of_ae_eq_of_continuousAt hae
    (continuous_schwarzschildParikhWilczekInfiniteBorelLogProfile D).continuousAt
    continuous_schwarzschildParikhWilczekReflectedGammaLogProfile.continuousAt

/-- Exact positive-ray kernel forced by reflection. -/
theorem PWAnalyticInfiniteBorelReflectionData.forced_kernel
    (D : PWAnalyticInfiniteBorelReflectionData) (u : ℝ) :
    Complex.exp (u : ℂ) * Complex.exp (-((Real.exp u : ℝ) : ℂ)) *
        D.multiplier ((Real.exp (2 * u) : ℝ) : ℂ) =
      Complex.exp (-((Real.exp (-u) : ℝ) : ℂ)) := by
  have h := D.logProfile_eq u
  rw [schwarzschildParikhWilczekInfiniteBorelLogProfile,
    schwarzschildParikhWilczekReflectedGammaLogProfile,
    expShiftC, expShift] at h
  simp only [expShiftC, expShift] at h
  norm_num at h ⊢
  have h' :
      Complex.exp ((u : ℂ) / 2 - Complex.exp (u : ℂ)) *
          D.multiplier (Complex.exp (2 * (u : ℂ))) =
        Complex.exp (-(u : ℂ) / 2 - Complex.exp (-(u : ℂ))) := by
    convert h using 1 <;> ring_nf
  have hexp :
      Complex.exp ((u : ℂ) + -Complex.exp (u : ℂ)) =
        Complex.exp ((u : ℂ) / 2) *
          Complex.exp ((u : ℂ) / 2 - Complex.exp (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    Complex.exp (u : ℂ) * Complex.exp (-Complex.exp (u : ℂ)) *
          D.multiplier (Complex.exp (2 * (u : ℂ))) =
        Complex.exp ((u : ℂ) / 2) *
          (Complex.exp ((u : ℂ) / 2 - Complex.exp (u : ℂ)) *
            D.multiplier (Complex.exp (2 * (u : ℂ)))) := by
              nth_rewrite 1 [← Complex.exp_add]
              rw [hexp]
              ring
    _ = Complex.exp ((u : ℂ) / 2) *
          Complex.exp (-(u : ℂ) / 2 - Complex.exp (-(u : ℂ))) := by
            rw [h']
    _ = Complex.exp (-Complex.exp (-(u : ℂ))) := by
      rw [← Complex.exp_add]
      congr 2
      ring_nf

/-- Analytic germ whose positive-ray values are forced to be the nonperturbative reciprocal
exponential. -/
def schwarzschildParikhWilczekForcedFlatBorelGerm
    (A : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * Complex.exp (-z) * A (z ^ (2 : ℕ))

theorem PWAnalyticInfiniteBorelReflectionData.analyticAt_forcedFlatBorelGerm
    (D : PWAnalyticInfiniteBorelReflectionData) :
    AnalyticAt ℂ (schwarzschildParikhWilczekForcedFlatBorelGerm D.multiplier) 0 := by
  unfold schwarzschildParikhWilczekForcedFlatBorelGerm
  have hsq : AnalyticAt ℂ (fun z : ℂ => z ^ (2 : ℕ)) 0 := by fun_prop
  have houter : AnalyticAt ℂ D.multiplier ((fun z : ℂ => z ^ (2 : ℕ)) 0) := by
    simpa using D.analyticAt_zero
  have hcomp : AnalyticAt ℂ (fun z : ℂ => D.multiplier (z ^ (2 : ℕ))) 0 := by
    exact AnalyticAt.comp (x := (0 : ℂ)) houter hsq
  exact (analyticAt_id.mul analyticAt_id.neg.cexp').mul hcomp

/-- The exact forced germ is `exp(-1/x)` on the positive exponential scale. -/
theorem PWAnalyticInfiniteBorelReflectionData.forcedFlatBorelGerm_exp_neg
    (D : PWAnalyticInfiniteBorelReflectionData) (h : ℝ) :
    schwarzschildParikhWilczekForcedFlatBorelGerm D.multiplier
        (Real.exp (-h) : ℂ) =
      (Real.exp (-Real.exp h) : ℂ) := by
  have hk := D.forced_kernel (-h)
  rw [schwarzschildParikhWilczekForcedFlatBorelGerm]
  norm_num at hk ⊢
  have hpow : Complex.exp (-(h : ℂ)) ^ (2 : ℕ) = Complex.exp (-(2 * (h : ℂ))) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  rw [hpow]
  exact hk

/-- The reflected kernel is flat beyond every analytic PW grade. -/
theorem PWAnalyticInfiniteBorelReflectionData.forcedFlatBorelGerm_reesAllOrdersFlat
    (D : PWAnalyticInfiniteBorelReflectionData) :
    ReesAllOrdersFlat atTop (fun h : ℝ => Real.exp (-h))
      (fun h : ℝ =>
        ‖schwarzschildParikhWilczekForcedFlatBorelGerm D.multiplier
          (Real.exp (-h) : ℂ)‖) := by
  have htarget :
      ReesAllOrdersFlat atTop (fun h : ℝ => Real.exp (-h))
        (fun h : ℝ => Real.exp (-Real.exp h)) := by
    intro N
    have hbase := (expDecay_reesAllOrdersFlat_atTop (c := 1) (by norm_num)) N
    have hcomp := hbase.comp_tendsto Real.tendsto_exp_atTop
    apply hcomp.congr'
    · filter_upwards [] with h
      simp only [Function.comp_apply]
      congr 1
      ring
    · filter_upwards [] with h
      simp only [Function.comp_apply]
      rw [← Real.exp_neg]
  have hnorm (h : ℝ) :
      ‖schwarzschildParikhWilczekForcedFlatBorelGerm D.multiplier
          (Real.exp (-h) : ℂ)‖ = Real.exp (-Real.exp h) := by
    rw [D.forcedFlatBorelGerm_exp_neg]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  intro N
  exact (htarget N).congr' (Eventually.of_forall fun h => (hnorm h).symm)
    EventuallyEq.rfl

/-- **PW-B analytic infinite-row route kill.** No regular source-independent countable grade
resummation can supply the reflected Gamma leg. -/
theorem no_PWAnalyticInfiniteBorelReflectionData :
    IsEmpty PWAnalyticInfiniteBorelReflectionData := by
  refine ⟨fun D => ?_⟩
  let F : ℂ → ℂ :=
    schwarzschildParikhWilczekForcedFlatBorelGerm D.multiplier
  have hF : AnalyticAt ℂ F 0 := D.analyticAt_forcedFlatBorelGerm
  have hflat :
      ReesAllOrdersFlat atTop (fun h : ℝ => Real.exp (-h))
        (fun h : ℝ => ‖F (Real.exp (-h) : ℂ)‖) :=
    D.forcedFlatBorelGerm_reesAllOrdersFlat
  have htop : analyticOrderAt F 0 = ⊤ := by
    have hiff := reesAllOrdersFlat_normedAnalyticShiftMultiplier_iff
      (q := 1) (by norm_num) hF
    apply hiff.mp
    change ReesAllOrdersFlat atTop (fun h : ℝ => Real.exp (-1 * h))
      (fun h : ℝ => ‖F (Real.exp (-1 * h) : ℂ)‖)
    simpa only [neg_mul, one_mul] using hflat
  have hzero :
      (fun h : ℝ => ‖F (Real.exp (-h) : ℂ)‖) =ᶠ[atTop] 0 := by
    have htend : Tendsto (fun h : ℝ => Real.exp (-h)) atTop (nhds 0) := by
      exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    exact analyticNormAlongScale_eventually_eq_zero_of_order_eq_top htend htop
  obtain ⟨h, hh⟩ := hzero.exists
  have hpositive : 0 < ‖F (Real.exp (-h) : ℂ)‖ := by
    dsimp only [F]
    rw [D.forcedFlatBorelGerm_exp_neg]
    exact norm_pos_iff.mpr (ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  have hh' : ‖F (Real.exp (-h) : ℂ)‖ = 0 := by simpa using hh
  rw [hh'] at hpositive
  exact (lt_irrefl 0) hpositive

/-- Route-level proposition for a regular infinite PW-B reflection producer. -/
def SchwarzschildParikhWilczekAnalyticInfiniteBorelReflectionProducer : Prop :=
  Nonempty PWAnalyticInfiniteBorelReflectionData

theorem not_schwarzschildParikhWilczekAnalyticInfiniteBorelReflectionProducer :
    ¬ SchwarzschildParikhWilczekAnalyticInfiniteBorelReflectionProducer := by
  rintro ⟨D⟩
  exact no_PWAnalyticInfiniteBorelReflectionData.false D

end

end RHTower
