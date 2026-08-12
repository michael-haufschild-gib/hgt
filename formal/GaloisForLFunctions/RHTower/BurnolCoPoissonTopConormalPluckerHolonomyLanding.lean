import GaloisForLFunctions.RHTower.BurnolCoPoissonTopConormalPluckerMetricBridge
import GaloisForLFunctions.RHTower.FrankensteinPluckerXiHilbertAdmission
import GaloisForLFunctions.RHTower.HedenmalmGammaSewnBurnolHolonomyMassShell

/-!
# Burnol top-conormal landing in the Route-P physical holonomy

The multiplicity-exact Burnol top conormal already recovers every prime coefficient of the
Route-P horizontal carrier.  This module identifies that coefficient with a second, genuinely
Hilbert-geometric source object: the normalized finite bilateral aperture holonomy of the actual
co-Poisson quotient at the same Xi zero and prime dilation.

For a right-half Xi divisor copy `q` and prime `p`, the three quantities are exactly

`top-conormal reflected mass - forward mass`

`= Route-P Gamma Bockstein`

`= - Fisher(p) * normalized Burnol holonomy(p)`.

Thus P's admitted physical detector is the coefficient-faithful image of the orientation of the
actual finite Sonine aperture defect.  The identity also rules out treating the remaining source
term as an independent Gamma scalar: it must reverse this concrete Fourier-odd holonomy before
positive Pluecker completion.
-/

open Complex Real

noncomputable section
namespace RHTower

/-- Every Xi divisor support point is an actual zeta zero in the open critical strip. -/
theorem riemannZeta_eq_zero_of_xiZeroCopy (q : XiZeroCopy) :
    riemannZeta (q.1 : ℂ) = 0 := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hne1 : (q.1 : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  exact (xi_eq_zero_iff hstrip.1 hne1).mp
    (xi_eq_zero_of_mem_divisor_support q.1)

/-- On an actual right-half Xi fibre, normalized finite Burnol holonomy is the reciprocal
centered prime character.  The formula is independent of aperture after normalization. -/
theorem burnolCoPoissonNormalizedHolonomy_xiZeroCopy_eq_character
    (q : XiZeroCopy) (hq : 1 / 2 < (q.1 : ℂ).re)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (p : Nat.Primes) :
    burnolCoPoissonNormalizedHolonomy (w := (q.1 : ℂ)) (r := (p : ℝ))
        hq (xi_divisor_support_re_mem_open_unit q.1).2 ha
        (by exact_mod_cast p.2.one_lt) =
      (p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1 -
        (p : ℝ) ^ (-primeDepthBVWoldXiCenteredRate q.1) := by
  have hhi : (q.1 : ℂ).re < 1 := (xi_divisor_support_re_mem_open_unit q.1).2
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hb : 0 < (p : ℝ)⁻¹ * a := mul_pos (inv_pos.mpr hp0) ha
  have hann : BurnolCoPoissonAnnihilatorPoint (q.1 : ℂ) ((p : ℝ)⁻¹ * a) hq hhi hb :=
    burnolCoPoissonAnnihilatorPoint_of_riemannZeta_eq_zero hq hhi hb
      (riemannZeta_eq_zero_of_xiZeroCopy q)
  have hk : burnolExtendedSoninEvaluationVector (q.1 : ℂ) a hq hhi ha ≠ 0 :=
    burnolExtendedSoninEvaluationVector_ne_zero hq hhi ha ha1
  rw [burnolCoPoissonNormalizedHolonomy_eq_of_annihilator hq hhi ha hp1 hann hk,
    primeDepthBVWoldXiCenteredRate]
  ring_nf

/-- **Primewise conormal/holonomy identity.**  On an actual right-half Xi fibre, the signed
Route-P coefficient is the negative Fisher multiple of the normalized finite Burnol holonomy.
No divisor enumeration, simple-zero premise, or fitted scalar enters. -/
theorem sourceZeroHorizontalPrimeCarrier_eq_neg_fisher_mul_burnolHolonomy
    (q : XiZeroCopy) (hq : 1 / 2 < (q.1 : ℂ).re)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (p : Nat.Primes) :
    sourceZeroHorizontalPrimeCarrier q p =
      -primeActivationOccupancyFisherDensity p *
        burnolCoPoissonNormalizedHolonomy (w := (q.1 : ℂ)) (r := (p : ℝ))
          hq (xi_divisor_support_re_mem_open_unit q.1).2 ha
          (by exact_mod_cast p.2.one_lt) := by
  rw [burnolCoPoissonNormalizedHolonomy_xiZeroCopy_eq_character q hq ha ha1,
    sourceZeroHorizontalPrimeCarrier, primeGammaCofinalBocksteinCoefficient,
    primeActivationOccupancyFisherTwist, primeActivationOccupancyFisherTwist,
    primeDepthBVWoldXiCenteredRate]
  ring_nf

/-- The literal multiplicity-complete top-conormal metric is the same normalized finite-holonomy
orientation, with the forced Fisher sign. -/
theorem burnolActualConormalMetricImbalance_eq_neg_fisher_mul_burnolHolonomy
    (q : XiZeroCopy) (hq : 1 / 2 < (q.1 : ℂ).re)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (p : Nat.Primes) :
    burnolActualConormalMetricImbalance q p =
      -primeActivationOccupancyFisherDensity p *
        burnolCoPoissonNormalizedHolonomy (w := (q.1 : ℂ)) (r := (p : ℝ))
          hq (xi_divisor_support_re_mem_open_unit q.1).2 ha
          (by exact_mod_cast p.2.one_lt) := by
  rw [burnolActualConormalMetricImbalance_eq_sourceZeroHorizontalPrimeCarrier]
  exact sourceZeroHorizontalPrimeCarrier_eq_neg_fisher_mul_burnolHolonomy
    q hq ha ha1 p

namespace HedenmalmThetaSource

/-- Every lower physical Pluecker coordinate is the fixed positive reporter applied to the
Fisher-weighted negative Burnol holonomy at its actual prime label. -/
theorem frankensteinXiLowerPrimeCarrier_eq_neg_burnolHolonomy
    (q : XiZeroCopy) (hq : 1 / 2 < (q.1 : ℂ).re)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (e n : ℕ) :
    frankensteinXiLowerPrimeCarrier q e n =
      -(frankensteinPluckerLowerVertexReporter e 1 4 n : ℂ) *
        (primeActivationOccupancyFisherDensity (nthPrimeSubtype n) : ℂ) *
          (burnolCoPoissonNormalizedHolonomy (w := (q.1 : ℂ))
            (r := ((nthPrimeSubtype n : Nat.Primes) : ℝ))
            hq (xi_divisor_support_re_mem_open_unit q.1).2 ha
            (by exact_mod_cast (nthPrimeSubtype n).2.one_lt) : ℂ) := by
  rw [frankensteinXiLowerPrimeCarrier,
    sourceZeroHorizontalPrimeCarrier_eq_neg_fisher_mul_burnolHolonomy q hq ha ha1]
  push_cast
  ring

/-- Upper reporter chart has the identical literal Burnol-holonomy source coefficient. -/
theorem frankensteinXiUpperPrimeCarrier_eq_neg_burnolHolonomy
    (q : XiZeroCopy) (hq : 1 / 2 < (q.1 : ℂ).re)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (e n : ℕ) :
    frankensteinXiUpperPrimeCarrier q e n =
      -(frankensteinPluckerUpperVertexReporter e 4 1 n : ℂ) *
        (primeActivationOccupancyFisherDensity (nthPrimeSubtype n) : ℂ) *
          (burnolCoPoissonNormalizedHolonomy (w := (q.1 : ℂ))
            (r := ((nthPrimeSubtype n : Nat.Primes) : ℝ))
            hq (xi_divisor_support_re_mem_open_unit q.1).2 ha
            (by exact_mod_cast (nthPrimeSubtype n).2.one_lt) : ℂ) := by
  rw [frankensteinXiUpperPrimeCarrier,
    sourceZeroHorizontalPrimeCarrier_eq_neg_fisher_mul_burnolHolonomy q hq ha ha1]
  push_cast
  ring

end HedenmalmThetaSource
end RHTower
