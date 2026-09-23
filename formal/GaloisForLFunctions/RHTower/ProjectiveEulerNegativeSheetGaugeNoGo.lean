import GaloisForLFunctions.HTGeometry.ExponentZeroIsodivisorialContinuation
import GaloisForLFunctions.RHTower.ProjectiveEulerCanonicalPolarity
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# Projective-Euler negative-sheet gauge no-go

The all-negative Helson source continues canonically as `ζ(2s) / ζ(s)`. Every source-faithful
exponent-zero Euler gauge is a holomorphic unit on the positive half-plane, so it preserves and
reflects pointwise analyticity and preserves the complete signed divisor. Consequently the
canonical or gauged sheet is pole-free on `1/2 < Re(s) < 1` exactly under RH; even existence of one
admissibly gauged pole-free sheet is equivalent to RH.

The strongest positive survivor is a local cancellation classification: any analytic multiplier
that cancels a right-half negative-sheet pole must vanish at that zeta zero, hence cannot be a
projective unit. This closes the PEP gauge chamber rather than leaving a stronger hidden premise.
-/

noncomputable section

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

/-- The canonical all-negative Euler sheet is holomorphic on the strict right critical strip. -/
def CanonicalNegativeEulerSheetPoleFreeRightStrip : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
    AnalyticAt ℂ canonicalNegativeEulerSheet s

/-- Pole-freeness of the all-negative sheet after an exponent-zero Euler gauge. -/
def ExponentZeroGaugeCanonicalNegativeEulerSheetPoleFreeRightStrip
    (eta omega : PrimePhase Nat.Primes) : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
    AnalyticAt ℂ
      (exponentZeroGaugeContinuedSource eta omega canonicalNegativeEulerSheet) s

/-- Multiplication by any analytic unit preserves and reflects pointwise analyticity. -/
theorem analyticAt_mul_analyticUnit_iff
    (u f : ℂ → ℂ) {z : ℂ} (hu : AnalyticAt ℂ u z) (hune : u z ≠ 0) :
    AnalyticAt ℂ (fun w => u w * f w) z ↔ AnalyticAt ℂ f z := by
  constructor
  · intro hprod
    have hquot := hprod.div hu hune
    apply hquot.congr
    filter_upwards [hu.continuousAt.eventually_ne hune] with w hw
    simp [hw]
  · intro hf
    exact hu.mul hf

/-- Multiplication by an exponent-zero Euler gauge preserves and reflects pointwise analyticity. -/
theorem analyticAt_exponentZeroGaugeContinuedSource_iff
    (eta omega : PrimePhase Nat.Primes)
    (homega : IsExponentZeroEulerGauge natPrimeSize omega)
    (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ positiveHalfPlane) :
    AnalyticAt ℂ (exponentZeroGaugeContinuedSource eta omega f) z ↔
      AnalyticAt ℂ f z := by
  have hu : AnalyticAt ℂ (exponentZeroEulerGaugeUnit eta omega) z :=
    analyticAt_exponentZeroEulerGaugeUnit eta omega homega hz
  have hune : exponentZeroEulerGaugeUnit eta omega z ≠ 0 :=
    exponentZeroEulerGaugeUnit_ne_zero eta omega homega hz
  change AnalyticAt ℂ (fun w => exponentZeroEulerGaugeUnit eta omega w * f w) z ↔ _
  exact analyticAt_mul_analyticUnit_iff (exponentZeroEulerGaugeUnit eta omega) f hu hune

/-- A right-half zeta zero is never a removable singularity of the all-negative sheet. -/
theorem not_analyticAt_canonicalNegativeEulerSheet_of_right_half_zeta_zero
    (ρ : ℂ) (hhalf : 1 / 2 ≤ ρ.re) (hzero : riemannZeta ρ = 0) :
    ¬ AnalyticAt ℂ canonicalNegativeEulerSheet ρ := by
  intro hana
  have hpole := canonicalNegativeEulerSheet_has_pole_at_right_half_zeta_zero ρ hhalf hzero
  have hnonneg : (0 : WithTop ℤ) ≤
      meromorphicOrderAt canonicalNegativeEulerSheet ρ := by
    rw [hana.meromorphicOrderAt_eq]
    induction analyticOrderAt canonicalNegativeEulerSheet ρ with
    | top => simp
    | coe n => simp
  have hnotTop : meromorphicOrderAt canonicalNegativeEulerSheet ρ ≠ ⊤ := by
    intro htop
    rw [htop] at hpole
    simp at hpole
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hnotTop
  have hnnonneg : (0 : ℤ) ≤ n := by
    rw [← hn] at hnonneg
    exact_mod_cast hnonneg
  rw [← hn, WithTop.untop₀_coe] at hpole
  omega

/-- Pole-freeness of the canonical all-negative sheet on the strict right strip is exactly RH. -/
theorem canonicalNegativeEulerSheetPoleFreeRightStrip_iff_riemannHypothesis :
    CanonicalNegativeEulerSheetPoleFreeRightStrip ↔ RiemannHypothesis := by
  constructor
  · intro hpoleFree
    apply _root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro s hlo hhi hzero
    exact not_analyticAt_canonicalNegativeEulerSheet_of_right_half_zeta_zero
      s hlo.le hzero (hpoleFree s hlo hhi)
  · intro hRH s hlo hhi
    have hden_ne : riemannZeta s ≠ 0 :=
      (_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mp hRH)
        s hlo hhi
    have hs1 : s ≠ 1 := by
      intro h
      subst s
      norm_num at hhi
    have h2s1 : 2 * s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
    have hnum : AnalyticAt ℂ (fun z : ℂ => riemannZeta (2 * z)) s :=
      (_root_.RHTower.analyticAt_riemannZeta_primeShiftResidueClosability h2s1).comp (by fun_prop)
    have hden : AnalyticAt ℂ riemannZeta s :=
      _root_.RHTower.analyticAt_riemannZeta_primeShiftResidueClosability hs1
    change AnalyticAt ℂ (fun z : ℂ => riemannZeta (2 * z) / riemannZeta z) s
    exact hnum.div hden hden_ne

/-- No exponent-zero source-faithful gauge changes the RH-strength pole-free condition. -/
theorem exponentZeroGaugeCanonicalNegativeEulerSheetPoleFreeRightStrip_iff_riemannHypothesis
    (eta omega : PrimePhase Nat.Primes)
    (homega : IsExponentZeroEulerGauge natPrimeSize omega) :
    ExponentZeroGaugeCanonicalNegativeEulerSheetPoleFreeRightStrip eta omega ↔
      RiemannHypothesis := by
  rw [← canonicalNegativeEulerSheetPoleFreeRightStrip_iff_riemannHypothesis]
  constructor
  · intro hgauge s hlo hhi
    apply (analyticAt_exponentZeroGaugeContinuedSource_iff eta omega homega
      canonicalNegativeEulerSheet ?_).mp
    · exact hgauge s hlo hhi
    · exact (show 0 < s.re by linarith)
  · intro hcanonical s hlo hhi
    apply (analyticAt_exponentZeroGaugeContinuedSource_iff eta omega homega
      canonicalNegativeEulerSheet ?_).mpr
    · exact hcanonical s hlo hhi
    · exact (show 0 < s.re by linarith)

/-- Even existence of one exponent-zero gauged pole-free negative sheet is exactly RH. -/
theorem exists_exponentZeroGaugeCanonicalNegativeEulerSheetPoleFreeRightStrip_iff_rh :
    (∃ eta omega : PrimePhase Nat.Primes,
      IsExponentZeroEulerGauge natPrimeSize omega ∧
        ExponentZeroGaugeCanonicalNegativeEulerSheetPoleFreeRightStrip eta omega) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨eta, omega, homega, hpoleFree⟩
    exact
      (exponentZeroGaugeCanonicalNegativeEulerSheetPoleFreeRightStrip_iff_riemannHypothesis
        eta omega homega).mp hpoleFree
  · intro hRH
    have hone : IsExponentZeroEulerGauge natPrimeSize (1 : PrimePhase Nat.Primes) :=
      isWeightedEulerGauge_one (exponentZeroWeight natPrimeSize)
    exact ⟨1, 1, hone,
      (exponentZeroGaugeCanonicalNegativeEulerSheetPoleFreeRightStrip_iff_riemannHypothesis
        1 1 hone).mpr hRH⟩

/-- Every exponent-zero gauge preserves the full opposite zeta-divisor multiplicity. -/
theorem exponentZeroGaugeCanonicalNegativeEulerSheet_divisor_polarity
    (eta omega : PrimePhase Nat.Primes)
    (homega : IsExponentZeroEulerGauge natPrimeSize omega)
    (ρ : ℂ) (hhalf : 1 / 2 ≤ ρ.re) (hzero : riemannZeta ρ = 0) :
    (meromorphicOrderAt
      (exponentZeroGaugeContinuedSource eta omega canonicalNegativeEulerSheet) ρ).untop₀ =
        -(meromorphicOrderAt riemannZeta ρ).untop₀ := by
  rw [meromorphicOrderAt_exponentZeroGaugeContinuedSource_eq eta omega homega
    canonicalNegativeEulerSheet (show 0 < ρ.re by linarith)]
  exact canonicalNegativeEulerSheet_divisor_polarity ρ hhalf hzero

/-- Every analytic multiplier that cancels a right-half negative-sheet pole must itself vanish. -/
theorem analyticMultiplier_eq_zero_of_cancels_canonicalNegativeEulerSheet_pole
    (u : ℂ → ℂ) (ρ : ℂ) (hhalf : 1 / 2 ≤ ρ.re) (hzero : riemannZeta ρ = 0)
    (hu : AnalyticAt ℂ u ρ)
    (hcancel : AnalyticAt ℂ (fun z => u z * canonicalNegativeEulerSheet z) ρ) :
    u ρ = 0 := by
  by_contra hune
  have hsheet : AnalyticAt ℂ canonicalNegativeEulerSheet ρ :=
    (analyticAt_mul_analyticUnit_iff u canonicalNegativeEulerSheet hu hune).mp hcancel
  exact not_analyticAt_canonicalNegativeEulerSheet_of_right_half_zeta_zero
    ρ hhalf hzero hsheet

end GaloisForLFunctions.RHTower
