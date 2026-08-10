import GaloisForLFunctions.RHTower.XiMassTimelikeGlancingResidualCriterion
import GaloisForLFunctions.RHTower.XiMassCriticalIntegerFace

/-!
# Non-diagonal Deninger cross-current realization of the critical Xi-mass cone

The mass spectral density is not intrinsically diagonal.  It has a canonical factorization into
two unequal half-density factors: one carries the vertical phase and one carries only real
damping.  Their conjugate product is exactly the original mass test.  Consequently the Route T
Fourier profile is an unsquared spectral cross-correlation amplitude.

This module then forms the finite symmetric von-Mangoldt current of that cross amplitude at the
critical half-density.  It is exactly twice the Route T prime-atom cone, so its height-uniform
boundedness is unconditionally equivalent to RH.  No positivity, diagonalization, asymptotic
expansion, or numerical computation is used.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Spectral half carrying both half of the real damping and the full vertical phase. -/
def xiMassSpectralCrossLeft (a sigma u : ℝ) (z : ℂ) : ℂ :=
  xiMassAnalyticTest a (((sigma / 2 : ℝ) : ℂ) + (u : ℂ) * I) z

/-- Conjugate-oriented spectral half carrying the other half of the real damping.  The
conjugation is placed here so that the standard cross-correlation multiplier is `left * conj right`.
-/
def xiMassSpectralCrossRight (a sigma : ℝ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (xiMassAnalyticTest a ((sigma / 2 : ℝ) : ℂ) z)

/-- Canonical non-diagonal spectral cross density. -/
def xiMassSpectralCrossDensity (a sigma u : ℝ) (z : ℂ) : ℂ :=
  xiMassSpectralCrossLeft a sigma u z *
    (starRingEnd ℂ) (xiMassSpectralCrossRight a sigma z)

/-- Multiplication of mass tests adds their spectral damping parameters. -/
theorem xiMassAnalyticTest_mul
    (a : ℝ) (tau upsilon z : ℂ) :
    xiMassAnalyticTest a tau z * xiMassAnalyticTest a upsilon z =
      xiMassAnalyticTest a (tau + upsilon) z := by
  rw [xiMassAnalyticTest, xiMassAnalyticTest, xiMassAnalyticTest,
    ← Complex.exp_add]
  congr 1
  ring

/-- **Exact unequal-half factorization.**  The cross density recovers the complete mass test
before any Fourier transform or prime summation. -/
theorem xiMassSpectralCrossDensity_eq_xiMassAnalyticTest
    (a sigma u : ℝ) (z : ℂ) :
    xiMassSpectralCrossDensity a sigma u z =
      xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I) z := by
  simp only [xiMassSpectralCrossDensity, xiMassSpectralCrossLeft,
    xiMassSpectralCrossRight, starRingEnd_self_apply]
  rw [xiMassAnalyticTest_mul]
  apply congrArg (fun tau : ℂ => xiMassAnalyticTest a tau z)
  push_cast
  ring

/-- Fourier amplitude of the canonical spectral cross density. -/
def xiMassSpectralCrossProfile (a sigma u h : ℝ) : ℂ :=
  stripFourier (xiMassSpectralCrossDensity a sigma u) (h : ℂ)

/-- Route T's mass Fourier profile is exactly the unsquared cross amplitude. -/
theorem xiMassSpectralCrossProfile_eq_stripFourier
    (a sigma u h : ℝ) :
    xiMassSpectralCrossProfile a sigma u h =
      stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ) := by
  unfold xiMassSpectralCrossProfile
  congr 1
  funext z
  exact xiMassSpectralCrossDensity_eq_xiMassAnalyticTest a sigma u z

/-- The cross amplitude retains the even mass orientation. -/
theorem xiMassSpectralCrossProfile_neg
    (a sigma u h : ℝ) :
    xiMassSpectralCrossProfile a sigma u (-h) =
      xiMassSpectralCrossProfile a sigma u h := by
  rw [xiMassSpectralCrossProfile_eq_stripFourier,
    xiMassSpectralCrossProfile_eq_stripFourier]
  simpa only [Complex.ofReal_neg] using
    stripFourier_xiMassAnalyticTest_neg a sigma u h

/-- Finite symmetric Deninger-style von-Mangoldt cross current in the rounded Route T cone.  The
arithmetic coefficient carries critical half-density; the profile remains unsquared. -/
def xiMassCriticalDeningerCrossCurrentCone
    (a sigma d u : ℝ) : ℂ :=
  let H := d * u / (d - 1 / 2)
  let M := ⌊Real.exp H⌋₊
  ∑ k ∈ Finset.range (M - 1),
    ((ArithmeticFunction.vonMangoldt (k + 2) : ℝ) : ℂ) *
      (Real.exp (-Real.log ((k : ℝ) + 2) / 2) : ℂ) *
      (xiMassSpectralCrossProfile a sigma u (Real.log ((k : ℝ) + 2)) +
        xiMassSpectralCrossProfile a sigma u (-Real.log ((k : ℝ) + 2)))

/-- **Exact cross-current weld.**  Symmetric non-diagonal current equals twice the Route T
prime-power cone, with no remainder or limiting passage. -/
theorem xiMassCriticalDeningerCrossCurrentCone_eq_two_mul_primeAtomConeSum
    (a sigma d u : ℝ) :
    xiMassCriticalDeningerCrossCurrentCone a sigma d u =
      2 * xiMassCriticalPrimeAtomConeSum a sigma d u := by
  simp only [xiMassCriticalDeningerCrossCurrentCone,
    xiMassCriticalPrimeAtomConeSum, xiMassCriticalDampedFourierProfile]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [xiMassSpectralCrossProfile_neg,
    xiMassSpectralCrossProfile_eq_stripFourier]
  ring

/-- Height-uniform boundedness of the finite critical cross current. -/
def XiMassCriticalDeningerCrossCurrentConeLineBound
    (a sigma d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassCriticalDeningerCrossCurrentCone a sigma d u‖ ≤ C

/-- Cross-current boundedness is exactly prime-atom boundedness. -/
theorem xiMassCriticalDeningerCrossCurrentConeLineBound_iff_primeAtomCone
    (a sigma d : ℝ) :
    XiMassCriticalDeningerCrossCurrentConeLineBound a sigma d ↔
      XiMassCriticalPrimeAtomConeLineBound a sigma d := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun u hu => ?_⟩
    have h := hC u hu
    rw [xiMassCriticalDeningerCrossCurrentCone_eq_two_mul_primeAtomConeSum,
      norm_mul, Complex.norm_ofNat] at h
    have htwo : ‖xiMassCriticalPrimeAtomConeSum a sigma d u‖ ≤
        2 * ‖xiMassCriticalPrimeAtomConeSum a sigma d u‖ := by
      nlinarith [norm_nonneg (xiMassCriticalPrimeAtomConeSum a sigma d u)]
    exact htwo.trans h
  · rintro ⟨C, hC⟩
    refine ⟨2 * C, fun u hu => ?_⟩
    rw [xiMassCriticalDeningerCrossCurrentCone_eq_two_mul_primeAtomConeSum,
      norm_mul, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (hC u hu) (by norm_num)

/-- **C35 capstone.**  The canonical non-diagonal critical Deninger cross current is an exact RH
criterion for every legal Route T parameter choice. -/
theorem riemannHypothesis_iff_xiMassCriticalDeningerCrossCurrentConeLineBound
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    RiemannHypothesis ↔
      XiMassCriticalDeningerCrossCurrentConeLineBound a sigma d := by
  exact (riemannHypothesis_iff_xiMassCriticalPrimeAtomConeLineBound
    hhalf hca hsigma hdhalf hda).trans
      (xiMassCriticalDeningerCrossCurrentConeLineBound_iff_primeAtomCone
        a sigma d).symm

end

end RHTower
