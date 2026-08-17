import GaloisForLFunctions.RHTower.XiMassJetAnalyticTest
import GaloisForLFunctions.RHTower.XiMassCausticJetTraceCriterion
import GaloisForLFunctions.RHTower.XiMassPrefixQuadratureDefect
import GaloisForLFunctions.RHTower.XiMassAnnulusShellSplit

/-!
# The jet-modified source side

The jet-modified test evaluated at a spectral point is exactly the jet-weighted multiplier of the
mass-shifted family, so the spectral sum of the modified test is the weighted trace of `(22.5)`.
On the arithmetic side the modified prime atoms and the modified continuum profile are the base
objects with `stripFourier (xiMassJetAnalyticTest a N τ)` in place of the base profile, and they
obey the same uniform vertical bounds with the explicit jet constant.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-! ## The spectral side -/

/-- **The jet-modified test at a spectral point is the jet-weighted multiplier.** -/
theorem xiMassJetAnalyticTest_spectralPoint_eq {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) (τ : ℂ)
    (q : XiZeroCopy) :
    xiMassJetAnalyticTest a N τ (xiSpectralPoint q)
      = (xiMassFamily ha.le).termW (xiMassCausticJetWeight ha N) τ q := by
  rw [xiMassJetAnalyticTest, HTGeometry.AbstractSpectralFamily.termW,
    xiMassAnalyticSqrt_spectralPoint_eq ha.le, xiMassAnalyticTest_spectralPoint_eq ha.le,
    xiMassCausticJetWeight_toFun]

theorem summable_norm_xiMassJetAnalyticTest_spectralPoint {a : ℝ} (ha : 1 / 2 < a) (N : ℕ)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun q : XiZeroCopy => ‖xiMassJetAnalyticTest a N τ (xiSpectralPoint q)‖) := by
  simpa only [xiMassJetAnalyticTest_spectralPoint_eq ha N τ] using
    (xiMassFamily ha.le).summable_norm_termW (xiMassCausticJetWeight ha N) hτ

/-- **(22.5, spectral side) The spectral sum of the jet-modified test is the weighted trace.** -/
theorem tsum_xiMassJetAnalyticTest_spectralPoint_eq_traceWC {a : ℝ} (ha : 1 / 2 < a) (N : ℕ)
    (τ : ℂ) :
    (∑' q : XiZeroCopy, xiMassJetAnalyticTest a N τ (xiSpectralPoint q))
      = (xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N) τ := by
  unfold HTGeometry.AbstractSpectralFamily.traceWC
  exact tsum_congr (xiMassJetAnalyticTest_spectralPoint_eq ha N τ)

/-! ## The arithmetic side -/

/-- The jet-modified centred prime atom. -/
def xiMassJetCenteredPrimeAtom (a : ℝ) (N : ℕ) (τ : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (1 / 2 : ℂ) n *
    stripFourier (xiMassJetAnalyticTest a N τ) (Real.log n : ℂ)

/-- The jet-modified growing continuum profile. -/
def xiMassJetGrowingFourierProfile (a : ℝ) (N : ℕ) (sigma u h : ℝ) : ℂ :=
  (Real.exp (h / 2) : ℂ) *
    stripFourier (xiMassJetAnalyticTest a N ((sigma : ℂ) + u * I)) (h : ℂ)

/-- The jet-modified damped continuum profile. -/
def xiMassJetDampedFourierProfile (a : ℝ) (N : ℕ) (sigma u h : ℝ) : ℂ :=
  (Real.exp (-h / 2) : ℂ) *
    stripFourier (xiMassJetAnalyticTest a N ((sigma : ℂ) + u * I)) (h : ℂ)

/-- The jet-modified prefix quadrature defect at an integer cutoff. -/
def xiMassJetPrefixQuadratureDefect (a : ℝ) (N : ℕ) (sigma u : ℝ) (M : ℕ) : ℂ :=
  (∑ k ∈ conePrimeIndex M,
      xiMassJetCenteredPrimeAtom a N ((sigma : ℂ) + (u : ℂ) * I) (k + 2))
    - ∫ h in (0 : ℝ)..Real.log ((M : ℝ) + 1), xiMassJetGrowingFourierProfile a N sigma u h

theorem norm_xiMassJetCenteredPrimeAtom_le_verticalBound {a sigma u : ℝ} {p : ℕ} {N : ℕ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hp : p.Prime) :
    ‖xiMassJetCenteredPrimeAtom a N ((sigma : ℂ) + (u : ℂ) * I) p‖
      ≤ Real.log p * xiMassJetVerticalBound a N sigma := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hpow : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (by norm_num)
  have hpow0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by linarith) _
  rw [xiMassJetCenteredPrimeAtom, norm_mul, norm_lseriesTerm_vonMangoldt_prime hp]
  have hF := norm_stripFourier_xiMassJetAnalyticTest_vertical_le ha hsigma N u (Real.log p)
  have hMnn := xiMassJetVerticalBound_nonneg a N sigma
  have hstep : Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ))
      * ‖stripFourier (xiMassJetAnalyticTest a N ((sigma : ℂ) + (u : ℂ) * I))
          ((Real.log p : ℝ) : ℂ)‖
      ≤ Real.log p * 1 * xiMassJetVerticalBound a N sigma := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hlog) hF (norm_nonneg _) ?_
    exact mul_nonneg hlog (by norm_num)
  simpa using hstep

theorem norm_xiMassJetGrowingFourierProfile_le {a sigma u h : ℝ} {N : ℕ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) :
    ‖xiMassJetGrowingFourierProfile a N sigma u h‖
      ≤ Real.exp (h / 2) * xiMassJetVerticalBound a N sigma := by
  rw [xiMassJetGrowingFourierProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (norm_stripFourier_xiMassJetAnalyticTest_vertical_le ha hsigma N u h) (Real.exp_pos _).le

theorem norm_xiMassJetDampedFourierProfile_le {a sigma u h : ℝ} {N : ℕ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) :
    ‖xiMassJetDampedFourierProfile a N sigma u h‖
      ≤ Real.exp (-h / 2) * xiMassJetVerticalBound a N sigma := by
  rw [xiMassJetDampedFourierProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (norm_stripFourier_xiMassJetAnalyticTest_vertical_le ha hsigma N u h) (Real.exp_pos _).le

/-- The growing profile is the damped profile times the full exponential. -/
theorem xiMassJetGrowingFourierProfile_eq {a : ℝ} (N : ℕ) (sigma u h : ℝ) :
    xiMassJetGrowingFourierProfile a N sigma u h
      = xiMassJetDampedFourierProfile a N sigma u h * ((Real.exp h : ℝ) : ℂ) := by
  have hexp : Real.exp (-h / 2) * Real.exp h = Real.exp (h / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [xiMassJetGrowingFourierProfile, xiMassJetDampedFourierProfile, ← hexp]
  push_cast
  ring

end

end RHTower
