import GaloisForLFunctions.RHTower.SuzukiChebyshevMassErrorEulerianBridge
import GaloisForLFunctions.RHTower.SuzukiMangoldtMacroscopicPrimeBlock
import GaloisForLFunctions.RHTower.SuzukiExplicitScrewRegularKernel
import GaloisForLFunctions.RHTower.RiemannGaussian.ScrewTransport

/-!
# Literal prime coordinate shared by Suzuki flank transport and SP-E current

At an aligned width-five Suzuki apex, each Mangoldt log-Haar atom times its sampled flank height
is exactly a nonnegative kernel applied to the same `Λ(p) / sqrt p` atom that enters the Eulerian
form of the corrected Chebyshev mass-error current. Thus the macroscopic source block and SP-E
current have a literal common atomic coordinate; any remaining obstruction is signed cancellation
among these atoms and their continuum increments, not a normalization mismatch.
-/

namespace RHTower

noncomputable section

/-- An aligned width-five source sample is exactly a positive kernel of the literal screw atom. -/
theorem mangoldtLogHaarAtomMass_mul_suzukiMangoldtFiveAlignedSample_eq
    {n p : ℕ} (hn : 5 ≤ n) (hp : 5 ≤ p) :
    mangoldtLogHaarAtomMass p *
        suzukiRectangularPositiveArchSampleChannel (Real.log 5)
          (suzukiMangoldtFiveApexAperture n) (mangoldtLogHaarNode p) =
      2 * GaloisForLFunctions.RHTower.screwPrimeWeight p *
        max 0 (Real.log 5 - |Real.log ((p : ℝ) / (n : ℝ))|) := by
  rw [suzukiMangoldtFiveAlignedApex_sample_eq hn hp]
  unfold mangoldtLogHaarAtomMass GaloisForLFunctions.RHTower.screwPrimeWeight
  have hpR : (0 : ℝ) < p := by positivity
  have hsqrt : Real.sqrt (p : ℝ) * Real.sqrt p = p :=
    Real.mul_self_sqrt hpR.le
  have hsqrtSq : Real.sqrt (p : ℝ) ^ (2 : ℕ) = p := by
    rw [pow_two]
    exact hsqrt
  field_simp [hpR.ne', (Real.sqrt_pos.mpr hpR).ne']
  rw [hsqrtSq]

/-- Reindexing the Suzuki event schedule recovers the literal screw atom. -/
theorem suzukiPrimeWeight_pred_eq_screwPrimeWeight
    {p : ℕ} (hp : 2 ≤ p) :
    RiemannGaussian.suzukiPrimeWeight (p - 2) =
      GaloisForLFunctions.RHTower.screwPrimeWeight p := by
  unfold RiemannGaussian.suzukiPrimeWeight
    GaloisForLFunctions.RHTower.screwPrimeWeight
  have hindex : p - 2 + 2 = p := by omega
  rw [hindex]

/-- The aligned flank atom is exactly a positive kernel of the SP-E Eulerian prime increment. -/
theorem mangoldtLogHaarAtomMass_mul_suzukiMangoldtFiveAlignedSample_eq_suzukiPrimeWeight
    {n p : ℕ} (hn : 5 ≤ n) (hp : 5 ≤ p) :
    mangoldtLogHaarAtomMass p *
        suzukiRectangularPositiveArchSampleChannel (Real.log 5)
          (suzukiMangoldtFiveApexAperture n) (mangoldtLogHaarNode p) =
      2 * RiemannGaussian.suzukiPrimeWeight (p - 2) *
        max 0 (Real.log 5 - |Real.log ((p : ℝ) / (n : ℝ))|) := by
  rw [mangoldtLogHaarAtomMass_mul_suzukiMangoldtFiveAlignedSample_eq hn hp,
    suzukiPrimeWeight_pred_eq_screwPrimeWeight (by omega)]

end

end RHTower
