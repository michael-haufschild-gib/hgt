import GaloisForLFunctions.RHTower.XiHeatCassiniWoldDeningerPhysicalObserverWall
import GaloisForLFunctions.RHTower.XiMassBottomPrimeAtomization

/-!
# Half-strip realization of the Route-T physical observer

Multiplication of a mass Fourier profile at prime frequency `h = log p` by `sqrt(p)=exp(h/2)`
is exactly translation of its integration contour down by `i/2`.  Every legal Route-T aperture
has `a > 1/2`, so this physical half-density shift lies strictly inside the analytic mass strip.

Consequently the unbounded Fisher deconvolution found in the Deninger boundary chart is not an
extrinsic coefficient: after it pairs with the Fisher square root, it is the canonical lower
half-strip boundary value of the same mass test.  This is an exact joint-pairing identity, not a
norm estimate.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Mass Fourier profile evaluated on a lower horizontal contour of depth `c`. -/
def xiHeatCassiniPrimeMassLowerShiftProfile
    (a c : ℝ) (τ : ℂ) (p : Nat.Primes) : ℂ :=
  ∫ x : ℝ,
    xiMassAnalyticTest a τ ((x : ℂ) - (c : ℂ) * Complex.I) *
      Complex.exp (-(Complex.I * (Real.log (p : ℝ) : ℂ) * (x : ℂ)))

/-- Exact Fourier covariance under every legal lower strip translation. -/
theorem xiHeatCassiniPrimeMassLowerShiftProfile_eq_exp_mul
    {a c : ℝ} (hc : 0 ≤ c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (p : Nat.Primes) :
    xiHeatCassiniPrimeMassLowerShiftProfile a c τ p =
      Complex.exp (((c * Real.log (p : ℝ) : ℝ) : ℂ)) *
        xiHeatCassiniPrimeMassFourierProfile a τ p := by
  let w : ℝ := Real.log (p : ℝ)
  let F : ℂ → ℂ := fun z =>
    xiMassAnalyticTest a τ z *
      Complex.exp (-(Complex.I * (w : ℂ) * z))
  have hdiff : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ F z := by
    intro z hz
    have ha : 0 < a := lt_of_le_of_lt (abs_nonneg z.im) (lt_of_le_of_lt hz hca)
    have hmem : z ∈ xiMassStrip a := lt_of_le_of_lt hz hca
    exact (hasDerivAt_xiMassAnalyticTest ha τ hmem).differentiableAt.mul (by fun_prop)
  have hbound : ∀ z : ℂ, |z.im| ≤ c →
      ‖F z‖ ≤
        Real.exp ((|τ.im| + |w|) * c) *
          Real.exp (-(τ.re * |z.re|)) := by
    intro z hz
    exact norm_xiMassFourierKernel_le hca hτ w hz
  have hshift := integral_horizontal_shift_neg_of_decay
    (F := F) hc hτ hdiff hbound
  have hpoint (x : ℝ) :
      F ((x : ℂ) - (c : ℂ) * Complex.I) =
        Complex.exp (((-(c * w) : ℝ) : ℂ)) *
          (xiMassAnalyticTest a τ ((x : ℂ) - (c : ℂ) * Complex.I) *
            Complex.exp (-(Complex.I * (w : ℂ) * (x : ℂ)))) := by
    dsimp only [F]
    have hphase :
        Complex.exp (-(Complex.I * (w : ℂ) *
            ((x : ℂ) - (c : ℂ) * Complex.I))) =
          Complex.exp (((-(c * w) : ℝ) : ℂ)) *
            Complex.exp (-(Complex.I * (w : ℂ) * (x : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hphase]
    ring
  have hleft :
      (∫ x : ℝ, F ((x : ℂ) - (c : ℂ) * Complex.I)) =
        Complex.exp (((-(c * w) : ℝ) : ℂ)) *
          xiHeatCassiniPrimeMassLowerShiftProfile a c τ p := by
    calc
      (∫ x : ℝ, F ((x : ℂ) - (c : ℂ) * Complex.I)) =
          ∫ x : ℝ,
            Complex.exp (((-(c * w) : ℝ) : ℂ)) *
              (xiMassAnalyticTest a τ ((x : ℂ) - (c : ℂ) * Complex.I) *
                Complex.exp (-(Complex.I * (w : ℂ) * (x : ℂ)))) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = Complex.exp (((-(c * w) : ℝ) : ℂ)) *
          xiHeatCassiniPrimeMassLowerShiftProfile a c τ p := by
        rw [integral_const_mul]
        rfl
  have hright :
      (∫ x : ℝ, F (x : ℂ)) =
        xiHeatCassiniPrimeMassFourierProfile a τ p := by
    rfl
  rw [hleft, hright] at hshift
  have hinv :
      Complex.exp (((c * w : ℝ) : ℂ)) *
          Complex.exp (((-(c * w) : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    norm_num
  calc
    xiHeatCassiniPrimeMassLowerShiftProfile a c τ p =
        1 * xiHeatCassiniPrimeMassLowerShiftProfile a c τ p := by rw [one_mul]
    _ = (Complex.exp (((c * w : ℝ) : ℂ)) *
          Complex.exp (((-(c * w) : ℝ) : ℂ))) *
            xiHeatCassiniPrimeMassLowerShiftProfile a c τ p := by rw [hinv]
    _ = Complex.exp (((c * w : ℝ) : ℂ)) *
          (Complex.exp (((-(c * w) : ℝ) : ℂ)) *
            xiHeatCassiniPrimeMassLowerShiftProfile a c τ p) := by ring
    _ = Complex.exp (((c * w : ℝ) : ℂ)) *
          xiHeatCassiniPrimeMassFourierProfile a τ p := by rw [hshift]
    _ = Complex.exp (((c * Real.log (p : ℝ) : ℝ) : ℂ)) *
          xiHeatCassiniPrimeMassFourierProfile a τ p := by rfl

/-- **Critical half-shift law.**  Lower contour depth `1/2` restores exactly the physical
prime half-density. -/
theorem xiHeatCassiniPrimeMassLowerHalfShiftProfile_eq
    {a : ℝ} (ha : 1 / 2 < a) {τ : ℂ} (hτ : 0 < τ.re)
    (p : Nat.Primes) :
    xiHeatCassiniPrimeMassLowerShiftProfile a (1 / 2) τ p =
      ((Real.sqrt (p : ℝ) : ℝ) : ℂ) *
        xiHeatCassiniPrimeMassFourierProfile a τ p := by
  rw [xiHeatCassiniPrimeMassLowerShiftProfile_eq_exp_mul
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) ha hτ]
  congr 1
  rw [← Complex.ofReal_exp]
  congr 1
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [show (1 / 2 : ℝ) * Real.log (p : ℝ) =
      Real.log (p : ℝ) / 2 by ring,
    ← Real.log_sqrt hp.le, Real.exp_log (Real.sqrt_pos.mpr hp)]

/-- Ordered physical mass profile is exactly the legal lower-half-strip boundary value. -/
theorem xiHeatCassiniPrimeMassLowerHalfShiftProfile_nthPrime_eq_ordered
    {a : ℝ} (ha : 1 / 2 < a) {τ : ℂ} (hτ : 0 < τ.re)
    (N : ℕ) :
    xiHeatCassiniPrimeMassLowerShiftProfile
        a (1 / 2) τ (nthPrimeSubtype N) =
      xiHeatCassiniOrderedPrimeHalfDensityProfile a τ N := by
  rw [xiHeatCassiniPrimeMassLowerHalfShiftProfile_eq ha hτ]
  rfl

/-- The centered residual terminal flux is an exact lower-half-strip joint pairing, with no
standalone multiplicative-height coefficient. -/
theorem xiHeatCassiniOrderedWoldResidualTerminalFlux_eq_lowerHalfShift
    {a : ℝ} (ha : 1 / 2 < a) {τ : ℂ} (hτ : 0 < τ.re)
    (N : ℕ) :
    xiHeatCassiniOrderedWoldResidualTerminalFlux a τ N =
      xiHeatCassiniPrimeMassLowerShiftProfile
          a (1 / 2) τ (nthPrimeSubtype N) *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy (nthPrimeSubtype N) := by
  rw [xiHeatCassiniOrderedWoldResidualTerminalFlux,
    xiHeatCassiniPrimeMassLowerHalfShiftProfile_nthPrime_eq_ordered ha hτ,
    xiHeatCassiniPrimeWoldResidualLogDiscrepancy_nthPrime]

/-- Reflection-odd Hodge observation lands directly on the legal lower-half-strip residual. -/
theorem xiHeatCassiniWoldActivationFisherOddPhysicalHodgeAtom_eq_lowerHalfShift
    {a : ℝ} (ha : 1 / 2 < a) {τ : ℂ} (hτ : 0 < τ.re)
    (N : ℕ) :
    xiHeatCassiniWoldActivationFisherOddPhysicalHodgeAtom
        a τ (nthPrimeSubtype N) =
      2 * Complex.I *
        (xiHeatCassiniPrimeMassLowerShiftProfile
            a (1 / 2) τ (nthPrimeSubtype N) *
          xiHeatCassiniPrimeWoldResidualLogDiscrepancy (nthPrimeSubtype N)) := by
  rw [xiHeatCassiniWoldActivationFisherOddPhysicalHodgeAtom_nthPrime_eq,
    xiHeatCassiniOrderedWoldResidualTerminalFlux_eq_lowerHalfShift ha hτ]

end


end RHTower
