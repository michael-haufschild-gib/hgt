/-
# Scaling Bourgain's Taylor phases back to `(N₀+m)^(3/2)` and `(N₀+m)^(1/2)`

`BourgainTaylorRemainders` proves the dimensionless Taylor identities.  This
file introduces the phase normalization used in the paper and restores the
physical scales `N₀` and `M`.  The two capstones are exact versions of
Bourgain (2.18)--(2.19), with `q=M/N₀` and `m=Mt`.
-/
import GaloisForLFunctions.RHTower.BourgainTaylorRemainders

namespace RHTower

noncomputable section

/-- Cubic phase in the sign and scale convention of Bourgain (2.18). -/
def bourgainCubicTaylorPhase (q t : ℝ) : ℝ :=
  -(1 / 16 : ℝ) * bourgainNormalizedCubicRemainder q t

/-- Quartic phase in the sign and scale convention of Bourgain (2.19). -/
def bourgainQuarticTaylorPhase (q t : ℝ) : ℝ :=
  -(1 / 64 : ℝ) * bourgainNormalizedQuarticRemainder q t

/-- Dimensionless exact form of Bourgain (2.18). -/
theorem bourgainAffineRpow_three_halves_taylor_raw
    {q t : ℝ} (hq : q ≠ 0) :
    bourgainAffineRpow q (3 / 2 : ℝ) t =
      bourgainThreeHalvesTaylorPolynomial q t +
        q ^ (3 : ℕ) * bourgainCubicTaylorPhase q t := by
  rw [bourgainAffineRpow_three_halves_taylor hq]
  unfold bourgainCubicTaylorPhase
  ring

/-- Dimensionless exact form of Bourgain (2.19). -/
theorem bourgainAffineRpow_half_taylor_raw
    {q t : ℝ} (hq : q ≠ 0) :
    bourgainAffineRpow q (1 / 2 : ℝ) t =
      bourgainHalfTaylorPolynomial q t -
        q ^ (3 : ℕ) * bourgainCubicTaylorPhase q t +
        q ^ (4 : ℕ) * bourgainQuarticTaylorPhase q t := by
  rw [bourgainAffineRpow_half_taylor hq]
  unfold bourgainCubicTaylorPhase bourgainQuarticTaylorPhase
  ring

private theorem add_mul_eq_scale_mul
    {N₀ M t : ℝ} (hN₀ : N₀ ≠ 0) :
    N₀ + M * t = N₀ * (1 + (M / N₀) * t) := by
  field_simp

/-- Physical-scale exact version of Bourgain (2.18), before mechanically
distributing the outer factor `N₀^(3/2)`. -/
theorem bourgain_scaled_three_halves_taylor
    {N₀ M t : ℝ} (hN₀ : 0 < N₀) (hM : 0 < M)
    (ht : 0 ≤ t) :
    (N₀ + M * t) ^ (3 / 2 : ℝ) =
      N₀ ^ (3 / 2 : ℝ) *
        (bourgainThreeHalvesTaylorPolynomial (M / N₀) t +
          (M / N₀) ^ (3 : ℕ) *
            bourgainCubicTaylorPhase (M / N₀) t) := by
  have hq : M / N₀ ≠ 0 := div_ne_zero hM.ne' hN₀.ne'
  have hfactor : N₀ + M * t = N₀ * (1 + (M / N₀) * t) :=
    add_mul_eq_scale_mul hN₀.ne'
  have hsecond : 0 ≤ 1 + (M / N₀) * t := by positivity
  rw [hfactor, Real.mul_rpow hN₀.le hsecond]
  change N₀ ^ (3 / 2 : ℝ) *
      bourgainAffineRpow (M / N₀) (3 / 2 : ℝ) t = _
  rw [bourgainAffineRpow_three_halves_taylor_raw hq]

/-- Physical-scale exact version of Bourgain (2.19), before mechanically
distributing the outer factor `N₀^(1/2)`. -/
theorem bourgain_scaled_half_taylor
    {N₀ M t : ℝ} (hN₀ : 0 < N₀) (hM : 0 < M)
    (ht : 0 ≤ t) :
    (N₀ + M * t) ^ (1 / 2 : ℝ) =
      N₀ ^ (1 / 2 : ℝ) *
        (bourgainHalfTaylorPolynomial (M / N₀) t -
          (M / N₀) ^ (3 : ℕ) *
            bourgainCubicTaylorPhase (M / N₀) t +
          (M / N₀) ^ (4 : ℕ) *
            bourgainQuarticTaylorPhase (M / N₀) t) := by
  have hq : M / N₀ ≠ 0 := div_ne_zero hM.ne' hN₀.ne'
  have hfactor : N₀ + M * t = N₀ * (1 + (M / N₀) * t) :=
    add_mul_eq_scale_mul hN₀.ne'
  have hsecond : 0 ≤ 1 + (M / N₀) * t := by positivity
  rw [hfactor, Real.mul_rpow hN₀.le hsecond]
  change N₀ ^ (1 / 2 : ℝ) *
      bourgainAffineRpow (M / N₀) (1 / 2 : ℝ) t = _
  rw [bourgainAffineRpow_half_taylor_raw hq]

end

end RHTower
