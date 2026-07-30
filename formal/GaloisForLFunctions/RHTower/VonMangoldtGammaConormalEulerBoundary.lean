import GaloisForLFunctions.RHTower.VonMangoldtGammaJuliaBianchiJointGram
import GaloisForLFunctions.RHTower.SoninSemilocalFluxSource
import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureDyadicProjection

/-!
# The Gamma conormal forces a height-localized Euler boundary current

Evaluating the complete factorial Gamma conormal on a raw prime-log jet multiplies its zeroth
coordinate by `(m - 1) / log m`.  This raw compression is not the source-Julia Hilbert coordinate.
There is a unique diagonal renormalization which makes the complete conormal evaluate to one,
namely `log m / (m - 1)`.  After this correction the boundary coordinate is exactly the damped
square-root von Mangoldt amplitude.

On a prime-power valuation coordinate `n = p^(e+1)`, adding the physical height phase gives the
explicit source vector

`sqrt(log p / n * exp(-u log n)) * exp(-i t log n / 2)`.

This module proves the compression and uniqueness laws, identifies the zero-phase vector with the
existing source-Julia amplitude, and defines its finite pairing with the cubically normalized true
aperture innovation.  It does not prove the conjectural response-signature identity or its
all-rank passive limit.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Complete real factorial-conormal compression of the raw power jet at rate `L`. -/
def gammaFactorialPowerCompression (L : ℝ) : ℝ :=
  ∑' n : ℕ, L ^ n / ((n + 1).factorial : ℝ)

/-- The factorial-tail conormal is the divided exponential increment. -/
theorem gammaFactorialPowerCompression_eq_exp_sub_div
    {L : ℝ} (hL : L ≠ 0) :
    gammaFactorialPowerCompression L = (Real.exp L - 1) / L := by
  let e : ℕ → ℝ := fun n => L ^ n / (n.factorial : ℝ)
  have hexp : HasSum e (Real.exp L) := by
    simpa [e, Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp L)
  have htail : HasSum (fun n => e (n + 1)) (Real.exp L - 1) := by
    have h := (hasSum_nat_add_iff' (f := e) 1).mpr hexp
    simpa [e] using h
  have hscaled := htail.mul_left L⁻¹
  have hscaled' : HasSum
      (fun n : ℕ => L ^ n / ((n + 1).factorial : ℝ))
      ((Real.exp L - 1) / L) := by
    have hterm : (fun n : ℕ => L⁻¹ * e (n + 1)) =
        fun n : ℕ => L ^ n / ((n + 1).factorial : ℝ) := by
      funext n
      dsimp [e]
      rw [Nat.factorial_succ]
      push_cast
      field_simp [hL]
      ring
    have hlimit : L⁻¹ * (Real.exp L - 1) = (Real.exp L - 1) / L := by
      rw [div_eq_mul_inv, mul_comm]
    rw [hterm, hlimit] at hscaled
    exact hscaled
  exact hscaled'.tsum_eq

/-- At one Euler coordinate the raw conormal amplification is `(m-1)/log m`. -/
theorem gammaFactorialPowerCompression_log
    {m : ℝ} (hm : 1 < m) :
    gammaFactorialPowerCompression (Real.log m) =
      (m - 1) / Real.log m := by
  rw [gammaFactorialPowerCompression_eq_exp_sub_div
    (ne_of_gt (Real.log_pos hm)), Real.exp_log (by positivity)]

/-- Source-forced diagonal correction of the raw Gamma conormal on an Euler coordinate. -/
def gammaEulerBoundaryRenormalization (m : ℝ) : ℝ :=
  Real.log m / (m - 1)

/-- The corrected complete conormal evaluates to one. -/
theorem gammaEulerBoundaryRenormalization_mul_compression
    {m : ℝ} (hm : 1 < m) :
    gammaEulerBoundaryRenormalization m *
        gammaFactorialPowerCompression (Real.log m) = 1 := by
  rw [gammaEulerBoundaryRenormalization,
    gammaFactorialPowerCompression_log hm]
  field_simp [ne_of_gt (Real.log_pos hm), ne_of_gt (sub_pos.mpr hm)]

/-- **Uniqueness of Euler boundary renormalization.** Any scalar correction which sends the
complete factorial-conormal compression to one is the source factor `log m / (m-1)`. -/
theorem gammaEulerBoundaryRenormalization_unique
    {m r : ℝ} (hm : 1 < m)
    (hr : r * gammaFactorialPowerCompression (Real.log m) = 1) :
    r = gammaEulerBoundaryRenormalization m := by
  rw [gammaFactorialPowerCompression_log hm] at hr
  rw [gammaEulerBoundaryRenormalization]
  have hlog : Real.log m ≠ 0 := ne_of_gt (Real.log_pos hm)
  have hm1 : m - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hm)
  field_simp [hlog] at hr
  field_simp [hm1]
  exact hr

/-- Raw complete Gamma-conormal compression of one damped von Mangoldt--Bianchi coordinate. -/
def vonMangoldtGammaCompressedBoundaryCoordinate (x : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt
      (ArithmeticFunction.vonMangoldt m / (m : ℝ) *
        Real.exp (-x * Real.log m)) *
    gammaFactorialPowerCompression (Real.log m)

/-- The coordinate after applying the forced Euler boundary renormalization. -/
def vonMangoldtGammaRenormalizedBoundaryCoordinate (x : ℝ) (m : ℕ) : ℝ :=
  gammaEulerBoundaryRenormalization m *
    vonMangoldtGammaCompressedBoundaryCoordinate x m

/-- The renormalized complete Gamma compression is exactly the damped square-root Euler source. -/
theorem vonMangoldtGammaRenormalizedBoundaryCoordinate_eq
    {x : ℝ} {m : ℕ} (hm : 2 ≤ m) :
    vonMangoldtGammaRenormalizedBoundaryCoordinate x m =
      Real.sqrt
        (ArithmeticFunction.vonMangoldt m / (m : ℝ) *
          Real.exp (-x * Real.log m)) := by
  have hm' : (1 : ℝ) < m := by exact_mod_cast hm
  unfold vonMangoldtGammaRenormalizedBoundaryCoordinate
  rw [vonMangoldtGammaCompressedBoundaryCoordinate]
  calc
    gammaEulerBoundaryRenormalization ↑m *
          (Real.sqrt
              (ArithmeticFunction.vonMangoldt m / ↑m *
                Real.exp (-x * Real.log ↑m)) *
            gammaFactorialPowerCompression (Real.log ↑m)) =
        Real.sqrt
            (ArithmeticFunction.vonMangoldt m / ↑m *
              Real.exp (-x * Real.log ↑m)) *
          (gammaEulerBoundaryRenormalization ↑m *
            gammaFactorialPowerCompression (Real.log ↑m)) := by ring
    _ = _ := by rw [gammaEulerBoundaryRenormalization_mul_compression hm']; simp

/-- At zero damping the boundary is literally the existing source-Julia square-root amplitude. -/
theorem vonMangoldtGammaRenormalizedBoundaryCoordinate_zero
    {m : ℕ} (hm : 2 ≤ m) :
    (vonMangoldtGammaRenormalizedBoundaryCoordinate 0 m : ℂ) =
      finiteVonMangoldtDepthOneAmplitude m := by
  rw [vonMangoldtGammaRenormalizedBoundaryCoordinate_eq hm]
  simp [finiteVonMangoldtDepthOneAmplitude]

/-- Prime-power coordinate represented by one valuation pair. -/
def xiGammaEulerValuationNat (pe : Nat.Primes × ℕ) : ℕ :=
  pe.1 ^ (pe.2 + 1)

/-- The source-defined height-localized Euler boundary vector forced by Gamma renormalization. -/
def xiGammaEulerHeightBoundaryFeature
    (u t : ℝ) (pe : Nat.Primes × ℕ) : ℂ :=
  let n := xiGammaEulerValuationNat pe
  let density := Real.log pe.1 / (n : ℝ) * Real.exp (-u * Real.log n)
  (Real.sqrt density : ℂ) *
    Complex.exp (-(((t * Real.log n / 2 : ℝ) : ℂ) * Complex.I))

/-- The squared magnitude is exactly the damped von Mangoldt prime-power density. -/
theorem normSq_xiGammaEulerHeightBoundaryFeature
    {u t : ℝ} (pe : Nat.Primes × ℕ) :
    Complex.normSq (xiGammaEulerHeightBoundaryFeature u t pe) =
      Real.log pe.1 / (xiGammaEulerValuationNat pe : ℝ) *
        Real.exp (-u * Real.log (xiGammaEulerValuationNat pe)) := by
  have hp : (1 : ℝ) ≤ pe.1 := by
    exact_mod_cast pe.1.property.one_le
  have hn : (0 : ℝ) ≤ xiGammaEulerValuationNat pe := by positivity
  have hdensity :
      0 ≤ Real.log pe.1 / (xiGammaEulerValuationNat pe : ℝ) *
        Real.exp (-u * Real.log (xiGammaEulerValuationNat pe)) := by
    positivity
  rw [xiGammaEulerHeightBoundaryFeature, Complex.normSq_mul,
    Complex.normSq_ofReal]
  have hphase :
      Complex.normSq
          (Complex.exp
            (-(((t * Real.log (xiGammaEulerValuationNat pe) / 2 : ℝ) : ℂ) *
              Complex.I))) = 1 := by
    have hexp :
        Complex.exp
            (-(((t * Real.log (xiGammaEulerValuationNat pe) / 2 : ℝ) : ℂ) *
              Complex.I)) =
          Complex.exp
            (((-(t * Real.log (xiGammaEulerValuationNat pe) / 2) : ℝ) : ℂ) *
              Complex.I) := by
      congr 1
      push_cast
      ring
    rw [hexp, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  rw [hphase, mul_one, Real.mul_self_sqrt hdensity]

/-- At zero phase, the height boundary is the renormalized complete Gamma compression. -/
theorem xiGammaEulerHeightBoundaryFeature_zero_eq_renormalizedCoordinate
    {u : ℝ} (pe : Nat.Primes × ℕ)
    (hn : 2 ≤ xiGammaEulerValuationNat pe) :
    xiGammaEulerHeightBoundaryFeature u 0 pe =
      (vonMangoldtGammaRenormalizedBoundaryCoordinate u
        (xiGammaEulerValuationNat pe) : ℂ) := by
  rw [vonMangoldtGammaRenormalizedBoundaryCoordinate_eq hn]
  simp [xiGammaEulerHeightBoundaryFeature, xiGammaEulerValuationNat,
    vonMangoldt_prime_pow_succ_eq_log]

/-- Cubically normalized true-aperture innovation coordinate. -/
def xiMobiusCubicNormalizedInnovationFeature
    (h a : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  (h * Real.sqrt h)⁻¹ *
    xiMobiusContinuousApertureDyadicInnovationFeature h a pe

/-- Finite section of the explicit Euler-boundary current on the normalized true aperture. -/
def finiteXiGammaEulerApertureBoundaryCurrent
    (s : Finset (Nat.Primes × ℕ)) (u t h a : ℝ) : ℂ :=
  ∑ pe ∈ s,
    star (xiGammaEulerHeightBoundaryFeature u t pe) *
      (xiMobiusCubicNormalizedInnovationFeature h a pe : ℂ)

end

end RHTower
