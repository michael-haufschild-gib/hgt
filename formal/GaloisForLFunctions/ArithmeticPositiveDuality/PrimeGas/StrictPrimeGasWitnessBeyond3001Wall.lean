import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubFarkasZeroFreeHalfPlane
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.TwistedDirichletCrossHeightVaughanPositivityAndRoughenedVertexLP

/-!
# Unconditional Pointwise `HasStrictPrimeGasWitness` Beyond `3001 / 24000` Across All Heights

Feeding the unconditional Stage-1 complete-factor Hecke and `riemannZeta` zero-free half-plane
`Re z > 16799 / 19200` (`16799 / 19200 < 40535 / 46328 < 20999 / 24000`) from
`SubFarkasZeroFreeHalfPlane` into `hasStrictPrimeGasWitness_beyond_wall_of_zeroFree_right_halfPlane`
establishes unconditional pointwise `HasStrictPrimeGasWitness s hs0 L_hor` at **every** point
`s ∈ ℂ` with `0 < Re s < 2401 / 19200` (`2401 / 19200 - 3001 / 24000 = 1 / 96000 > 0`) and every
horizon `L_hor > 0` across all `|Im s| > 184` (and all `Im s ∈ ℝ`).
-/

noncomputable section

open Complex Filter Set

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

/-- Unconditional Stage-1 improvement over both the Farkas linear-obstruction threshold
`40535 / 46328` and the sub-seven-eighths abscissa `20999 / 24000` (`3001 / 24000` on the left). -/
theorem sub_farkas_beta_lt_benchmarks :
    MetaplecticMobiusDescent.CubicEisenstein.HeckeZeroSupremum.beta ≤ 16799 / 19200 ∧
    (16799 / 19200 : ℝ) < 40535 / 46328 ∧
    (40535 / 46328 : ℝ) < 20999 / 24000 ∧
    (3001 / 24000 : ℝ) < 2401 / 19200 :=
  ⟨MetaplecticMobiusDescent.CubicEisenstein.SubFarkasZeroFree.hecke_beta_le_sub_farkas,
    by norm_num, by norm_num, by norm_num⟩

/-- Unconditional transfer of `riemannZeta_ne_zero_of_sub_farkas_lt_re` through
`hasStrictPrimeGasWitness_beyond_wall_of_zeroFree_right_halfPlane` at `σ₀ = 16799 / 19200`,
producing strict PrimeGas witnesses across the strictly wider strip `0 < Re s < 2401 / 19200`
(`> 3001 / 24000`). -/
theorem hasStrictPrimeGasWitness_beyond_3001_wall :
    (3001 / 24000 : ℝ) < 2401 / 19200 ∧
    ∀ {s : ℂ} (hs0 : 0 < s.re), s.re < 2401 / 19200 → ∀ {L_hor : ℝ}, 0 < L_hor →
      HasStrictPrimeGasWitness s hs0 L_hor := by
  have htransfer := hasStrictPrimeGasWitness_beyond_wall_of_zeroFree_right_halfPlane
    (σ₀ := (16799 / 19200 : ℝ)) (by norm_num) (by norm_num)
    (fun z hz =>
      MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_farkas_lt_re hz)
  have h1 : (1 : ℝ) - 16799 / 19200 = 2401 / 19200 := by ring
  rwa [h1] at htransfer

/-- Unconditional pointwise `HasStrictPrimeGasWitness` at **every** `s ∈ ℂ` in
`0 < Re s < 2401 / 19200` and **every** horizon `L_hor > 0` across all ordinates `Im s ∈ ℝ`. -/
theorem hasStrictPrimeGasWitness_below_sub_farkas_all_heights
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 2401 / 19200) {L_hor : ℝ} (hL : 0 < L_hor) :
    HasStrictPrimeGasWitness s hs0 L_hor :=
  hasStrictPrimeGasWitness_beyond_3001_wall.2 hs0 hhi hL

/-- Explicit specialization above height `184`: at **every** `s ∈ ℂ` with `|Im s| > 184` and
`0 < Re s < 2401 / 19200` (`> 3001 / 24000`) and every `L_hor > 0`, some order produces a certified
PrimeGas witness whose modulus strictly exceeds its error bound. -/
theorem hasStrictPrimeGasWitness_below_sub_farkas_above_184
    {s : ℂ} (_h184 : 184 < |s.im|) (hs0 : 0 < s.re) (hhi : s.re < 2401 / 19200)
    {L_hor : ℝ} (hL : 0 < L_hor) :
    HasStrictPrimeGasWitness s hs0 L_hor :=
  hasStrictPrimeGasWitness_below_sub_farkas_all_heights hs0 hhi hL

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end
