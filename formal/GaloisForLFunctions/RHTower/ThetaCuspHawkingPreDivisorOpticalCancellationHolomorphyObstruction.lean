import GaloisForLFunctions.RHTower.ThetaCuspHawkingMovingHorizonAIMETemporalOpticalTriangle
import GaloisForLFunctions.RHTower.ExtendedSoninOrderDrop

/-!
# Pre-divisor optical-cancellation holomorphy obstruction

The unique positive scalar susceptibility which closes the moving-horizon/AIME optical triangle on
an Xi fibre has an exact source-global pre-divisor extension across the open critical strip. Every
factor is evaluated before zero selection: the two reflected horizon shifts, third-mass cross
numerator, and theta-mirror AIME denominator. Specialization at an Xi copy recovers the existing
physical susceptibility coefficient-for-coefficient.

This pre-divisor profile depends only on the horizontal coordinate and is nonconstant. A separate
strip identity theorem proves that every holomorphic function agreeing with any horizontal profile
on the connected open strip is constant. Consequently no holomorphic scalar coefficient can equal
the physical optical cancellation profile throughout the pre-divisor strip.

This does not exclude interpolation on the discrete Xi divisor. It proves the sharp regularity
boundary: a source-global scalar completion which tracks the exact optical cancellation must be
singular, antiholomorphic/non-holomorphic, support-discontinuous, or replaced by operator-valued
data.

`[NEW] [PRE-DIVISOR] [OPTICAL TRIANGLE] [HOLOMORPHY OBSTRUCTION] [SINGULARITY BOUNDARY] [LEAN-PROVED]`
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- Whole-strip version of the first reflected-real-pair horizon angular shift. -/
def d4PreDivisorHorizonAngularShift (x : ℝ) : ℝ :=
  x * (3 - x)

/-- Whole-strip version of the reflected horizon angular shift. -/
def d4PreDivisorReflectedHorizonAngularShift (x : ℝ) : ℝ :=
  (1 - x) * (2 + x)

/-- Pre-divisor moving-horizon third-mass reflection susceptibility, before selecting an Xi zero. -/
def d4PreDivisorEventHorizonThirdMassReflectionSusceptibility (x : ℝ) : ℝ :=
  let A := d4PreDivisorHorizonAngularShift x
  let B := d4PreDivisorReflectedHorizonAngularShift x
  648 * d4EventHorizonThirdMassParityCrossNumerator A B / (A ^ 3 * B ^ 3)

/-- Pre-divisor theta-mirror AIME denominator. -/
def d4PreDivisorThetaMirrorAIMEDenominator (x : ℝ) : ℝ :=
  x * (1 - x) * (2 - x) * (3 - x) * (x + 1) * (x + 2)

/-- Unique pre-divisor scalar susceptibility required to cancel the moving-horizon defect against
the chiral AIME kernel. -/
def d4PreDivisorOpticalCancellationSusceptibility (x : ℝ) : ℝ :=
  d4PreDivisorEventHorizonThirdMassReflectionSusceptibility x *
    d4PreDivisorThetaMirrorAIMEDenominator x / 12

/-- The whole-strip cancellation susceptibility specializes coefficient-for-coefficient to the
existing physical Xi-fibre susceptibility. -/
theorem d4PreDivisorOpticalCancellationSusceptibility_at_xi
    (q : XiZeroCopy) :
    d4PreDivisorOpticalCancellationSusceptibility (q.1 : ℂ).re =
      d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q := by
  rw [d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility]
  unfold d4PreDivisorOpticalCancellationSusceptibility
    d4PreDivisorEventHorizonThirdMassReflectionSusceptibility
    d4PreDivisorThetaMirrorAIMEDenominator
    d4PreDivisorHorizonAngularShift d4PreDivisorReflectedHorizonAngularShift
    d4BMXiEventHorizonThirdMassReflectionSusceptibility
    d4BMXiThetaMirrorAIMEDenominator
  dsimp only
  rw [d4BMXiHorizonAngularShift_eq,
    d4BMXiHorizonAngularShift_reflect_eq]

/-- The exact pre-divisor cancellation profile is nonconstant at two interior strip points. -/
theorem d4PreDivisorOpticalCancellationSusceptibility_quarter_ne_half :
    d4PreDivisorOpticalCancellationSusceptibility (1 / 4) ≠
      d4PreDivisorOpticalCancellationSusceptibility (1 / 2) := by
  norm_num [d4PreDivisorOpticalCancellationSusceptibility,
    d4PreDivisorEventHorizonThirdMassReflectionSusceptibility,
    d4PreDivisorThetaMirrorAIMEDenominator,
    d4PreDivisorHorizonAngularShift, d4PreDivisorReflectedHorizonAngularShift,
    d4EventHorizonThirdMassParityCrossNumerator]

/-- Strip identity rigidity for horizontal profiles. A holomorphic function agreeing with a
function of `Re z` throughout the open critical strip is constant there. The proof uses vertical
zeros accumulating at one point, then the analytic identity theorem on the preconnected strip. -/
theorem analyticOnNhd_openCriticalStrip_constant_of_eq_realProfile
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re ∧ z.re < 1})
    (g : ℝ → ℂ)
    (hfg : ∀ z : ℂ, z ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} → f z = g z.re) :
    ∀ x ∈ {z : ℂ | 0 < z.re ∧ z.re < 1},
      ∀ y ∈ {z : ℂ | 0 < z.re ∧ z.re < 1}, f x = f y := by
  intro x hx
  let H : ℂ → ℂ := fun z => f z - f x
  have hHan : AnalyticOnNhd ℂ H {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    hf.sub analyticOnNhd_const
  let u : ℕ → ℂ := fun m => x + Complex.I * ((1 : ℝ) / (m + 1) : ℝ)
  have hutend : Tendsto u atTop (nhds x) := by
    have hzero : Tendsto (fun m : ℕ => ((1 : ℝ) / (m + 1) : ℝ))
        atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcast : Tendsto
        (fun m : ℕ => (((1 : ℝ) / (m + 1) : ℝ) : ℂ)) atTop (nhds 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp hzero
    have hmul : Tendsto
        (fun m : ℕ => Complex.I * (((1 : ℝ) / (m + 1) : ℝ) : ℂ))
        atTop (nhds 0) := by
      simpa using hcast.const_mul Complex.I
    simpa [u] using hmul.const_add x
  have hune : ∀ m : ℕ, u m ≠ x := by
    intro m hm
    have hzero : Complex.I * (((1 : ℝ) / (m + 1) : ℝ) : ℂ) = 0 := by
      simpa [u] using sub_eq_zero.mpr hm
    rcases mul_eq_zero.mp hzero with hI | hdiv
    · exact Complex.I_ne_zero hI
    · have hpos : (0 : ℝ) < (1 : ℝ) / (m + 1) := by positivity
      have : (1 : ℝ) / (m + 1) = 0 := by exact_mod_cast hdiv
      linarith
  have hure : ∀ m : ℕ, (u m).re = x.re := by
    intro m
    simp [u]
  have humem : ∀ m : ℕ, u m ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    intro m
    simpa [hure m] using hx
  have hHzero : ∀ m : ℕ, H (u m) = 0 := by
    intro m
    change f (u m) - f x = 0
    rw [hfg (u m) (humem m), hfg x hx, hure m, sub_self]
  have hfrequently : ∃ᶠ z in nhdsWithin x {x}ᶜ, H z = 0 := by
    have htendWithin : Tendsto u atTop (nhdsWithin x {x}ᶜ) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hutend
        (Eventually.of_forall hune)
    exact htendWithin.frequently (Frequently.of_forall hHzero)
  have hHeq := hHan.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_criticalStrip hx hfrequently
  intro y hy
  have hyzero : H y = 0 := hHeq hy
  change f y - f x = 0 at hyzero
  exact (sub_eq_zero.mp hyzero).symm

/-- No holomorphic scalar coefficient on the full pre-divisor open critical strip can track the
unique physical optical-triangle cancellation susceptibility. -/
theorem not_exists_holomorphic_preDivisorOpticalCancellationSusceptibility :
    ¬ ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re ∧ z.re < 1} ∧
        ∀ z : ℂ, z ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} →
          f z = (d4PreDivisorOpticalCancellationSusceptibility z.re : ℂ) := by
  rintro ⟨f, hf, hprofile⟩
  have hconst := analyticOnNhd_openCriticalStrip_constant_of_eq_realProfile f hf
    (fun x => (d4PreDivisorOpticalCancellationSusceptibility x : ℂ)) hprofile
    ((1 / 4 : ℝ) : ℂ) (by norm_num) ((1 / 2 : ℝ) : ℂ) (by norm_num)
  rw [hprofile _ (by norm_num), hprofile _ (by norm_num)] at hconst
  have hreal := congrArg Complex.re hconst
  norm_num at hreal
  exact d4PreDivisorOpticalCancellationSusceptibility_quarter_ne_half hreal

end

end RHTower
