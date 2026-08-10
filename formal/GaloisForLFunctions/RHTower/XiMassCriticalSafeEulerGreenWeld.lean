import GaloisForLFunctions.RHTower.XiMassCriticalPrimeTailGreenStokes
import GaloisForLFunctions.RHTower.XiMassCriticalOutgoingOpenCore

/-!
# Fixed Weil / safe Euler / zero-rate Green triangle

The fixed critical Weil pairing, the absolutely convergent bottom Euler-line integral, and the
source-fixed zero-rate prime-tail Green current are three exact presentations of one scalar.
This closes a missing cross-route identification: the pre-divisor measure and Green formulations
land in the already formalized joint mass/Dirichlet pairing before any norm is taken.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Shifted centered Euler atom equals the fixed-Weil natural-coordinate atom. -/
theorem xiMassCenteredPrimeAtom_add_two_eq_criticalHalfDensityPrimeAtomNat
    (a sigma u : ℝ) (k : ℕ) :
    xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) (k + 2) =
      xiMassCriticalHalfDensityPrimeAtomNat a sigma u k := by
  rw [xiMassCenteredPrimeAtom,
    ← criticalMellinAtomWeight_cast_eq_lSeriesTerm_half (by omega),
    xiMassCriticalHalfDensityPrimeAtomNat,
    xiMassCriticalDampedFourierProfile]
  have hx : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hpow : ((k : ℝ) + 2) ^ (-1 / 2 : ℝ) =
      Real.exp (-Real.log ((k : ℝ) + 2) / 2) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [criticalMellinAtomWeight]
  push_cast
  rw [hpow, Complex.ofReal_exp]
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- Complete fixed-Weil series is exactly the complete centered bottom-Euler atom series. -/
theorem tsum_xiMassCenteredPrimeAtom_eq_criticalHalfDensityCrossSeries
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma)
    (u : ℝ) :
    (∑' n : ℕ, xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) n) =
      xiMassCriticalHalfDensityCrossSeries a sigma u := by
  have htau : 0 < (((sigma : ℂ) + (u : ℂ) * I)).re := by simpa using hsigma
  have hsum := summable_xiMassCenteredPrimeAtom hhalf hca htau
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hzero : (∑ n ∈ Finset.range 2,
      xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) n) = 0 := by
    have h0 : xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) 0 = 0 := by
      simp [xiMassCenteredPrimeAtom, LSeries.term_zero]
    have h1 : xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) 1 = 0 := by
      rw [xiMassCenteredPrimeAtom, LSeries.term_of_ne_zero one_ne_zero]
      simp [ArithmeticFunction.vonMangoldt_apply_one]
    norm_num [Finset.sum_range_succ, h0, h1]
  rw [hzero, zero_add] at hsplit
  rw [← hsplit, xiMassCriticalHalfDensityCrossSeries_eq_tsum_primeAtomNat]
  exact tsum_congr fun k =>
    xiMassCenteredPrimeAtom_add_two_eq_criticalHalfDensityPrimeAtomNat a sigma u k

/-- **C40 safe-line weld.**  Fixed critical Weil pairing is literally the legal bottom Euler
integral, where the von-Mangoldt Dirichlet series converges absolutely. -/
theorem xiMassCriticalHalfDensityWeilPairing_eq_bottomPrimeIntegral
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma)
    (u : ℝ) :
    xiMassCriticalHalfDensityWeilPairing a sigma u =
      xiMassBottomPrimeIntegral a c ((sigma : ℂ) + (u : ℂ) * I) := by
  rw [xiMassCriticalHalfDensityWeilPairing_eq_crossSeries (lt_trans hhalf hca) hsigma,
    xiMassBottomPrimeIntegral,
    integral_xiMassBottomPrimeIntegrand_eq_tsum_centeredAtom hhalf hca (by simpa using hsigma),
    tsum_xiMassCenteredPrimeAtom_eq_criticalHalfDensityCrossSeries hhalf hca hsigma]

/-- The bottom Euler integral is the negative source-fixed Green current. -/
theorem xiMassBottomPrimeIntegral_eq_neg_primeTailGreenCurrent
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma)
    (u : ℝ) :
    xiMassBottomPrimeIntegral a c ((sigma : ℂ) + (u : ℂ) * I) =
      -xiMassCriticalPrimeTailGreenCurrent a sigma u := by
  rw [← xiMassCriticalHalfDensityWeilPairing_eq_bottomPrimeIntegral
      hhalf hca hsigma u,
    xiMassCriticalHalfDensityWeilPairing_eq_neg_primeTailGreenCurrent
      (lt_trans hhalf hca) hsigma]

/-- RH is equivalent to height-uniform boundedness of one safe Euler-line integral. -/
theorem riemannHypothesis_iff_xiMassBottomPrimeIntegralLineBound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
        ‖xiMassBottomPrimeIntegral a c ((sigma : ℂ) + (u : ℂ) * I)‖ ≤ C := by
  let d : ℝ := (a + 1 / 2) / 2
  have hdhalf : 1 / 2 < d := by dsimp only [d]; linarith
  have hda : d < a := by dsimp only [d]; linarith
  rw [riemannHypothesis_iff_xiMassCriticalHalfDensityWeilPairingLineBound
    hhalf hca hsigma hdhalf hda]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun u hu => by
      rw [← xiMassCriticalHalfDensityWeilPairing_eq_bottomPrimeIntegral hhalf hca hsigma]
      exact hC u hu⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun u hu => by
      rw [xiMassCriticalHalfDensityWeilPairing_eq_bottomPrimeIntegral hhalf hca hsigma]
      exact hC u hu⟩

end

end RHTower
