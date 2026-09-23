import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIBlock
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicGlobalFrequencyAssembly

/-!
# Menon's Case-I estimate for the genuine harmonic block product

This is the product-only form of the Case-I estimate.  Route T bounds the prime polynomial and
reciprocal Halasz--Montgomery bounds the common cofactor polynomial.  No moving-support error is
inserted here: the complete ladder discrepancy is paid once by `MenonHarmonicLadderError`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- One Case-I genuine block product, without duplicating the global moving-support defect. -/
theorem exists_setIntegral_normSq_harmonicProduct_geom_le_scaled_HM :
    ∃ A delta Ctot tau0 : ℝ, 0 < delta ∧ 0 < Ctot ∧ 2 ≤ tau0 ∧
      ∀ (P : Finset ℕ) (A0 B0 j : ℕ)
          (Q eta W D t0 sigma Lx q mu xmin Hmaj : ℝ)
          (E : Set ℝ),
        0 < Q → 0 ≤ eta →
        1 ≤ ⌊Q * (1 + eta) ^ j⌋₊ →
        (∀ p, p ∈ geomBlock P Q (1 + eta) j ↔
          (p.Prime ∧ ⌊Q * (1 + eta) ^ j⌋₊ < p ∧
            p ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)) →
        1 ≤ A0 →
        1 ≤ ⌈(A0 : ℝ) / ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ →
        1 ≤ ⌊(B0 : ℝ) / (Q * (1 + eta) ^ j)⌋₊ →
        1 ≤ W → 1 ≤ D → 0 < t0 →
        Real.log (max ((⌊Q * (1 + eta) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) ≤ Lx →
        0 ≤ q → q ≤ Real.log (max ((⌊Q * (1 + eta) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) →
        0 ≤ mu → mu ≤ min delta (routeTWidthPolylogLower A sigma) / 2 →
        0 < xmin → xmin ≤ max ((⌊Q * (1 + eta) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1 →
        1 / t0 + Real.log (3 * |sigma| / 2) / routeTWidthPolylogLower A sigma ≤ Hmaj →
        MeasurableSet E → E ⊆ Set.Icc (-W) W →
        (∀ w ∈ E, tau0 ≤ |(-(2 * Real.pi * w))|) →
        (∀ w ∈ E, 16 * Real.pi / 3 ≤ |(-(2 * Real.pi * w))|) →
        (∀ w ∈ E, t0 ≤ |(-(2 * Real.pi * w))|) →
        (∀ w ∈ E, |(-(2 * Real.pi * w))| ≤ |sigma|) →
        (∫ w in E,
          ‖harmonicPrimeBlockPoly
              (geomBlock P Q (1 + eta) j) w *
            logPoly (harmonicRamareCofactorCoeff P)
              (geomCofactorBlockAt A0 B0 Q eta j) w‖ ^ (2 : ℕ))
          ≤ menonHarmonicProductCostVolume P A0 B0 Q eta W
              (harmonicCaseIBlockMajorant Ctot D Lx Hmaj mu q t0 xmin
                ⌊Q * (1 + eta) ^ j⌋₊ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
              (volume.real E) j := by
  obtain ⟨A, delta, Ctot, tau0, hdelta, hCtot, htau0, hroute⟩ :=
    exists_norm_harmonicPrimeBlockPoly_scaled_le
  refine ⟨A, delta, Ctot, tau0, hdelta, hCtot, htau0, ?_⟩
  intro P A0 B0 j Q eta W D t0 sigma Lx q mu xmin Hmaj E hQpos heta hblock
    hblockRange hA0 hleft hright hW hD ht0 hLx hq0 hq hmu0 hmu hxmin
    hxminBlock hHmaj hEm hEs hfreq hfreq16 hfreq0 hfreqTop
  have hstep : (1 : ℝ) ≤ 1 + eta := by linarith
  have hQnonneg : 0 ≤ Q := hQpos.le
  have habR : Q * (1 + eta) ^ j ≤ Q * (1 + eta) ^ (j + 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hstep (Nat.le_succ j)) hQnonneg
  have hab : ⌊Q * (1 + eta) ^ j⌋₊ ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊ :=
    Nat.floor_mono habR
  have hpoint : ∀ w ∈ E,
      ‖harmonicPrimeBlockPoly
          (geomBlock P Q (1 + eta) j) w‖
        ≤ harmonicCaseIBlockMajorant Ctot D Lx Hmaj mu q t0 xmin
            ⌊Q * (1 + eta) ^ j⌋₊ ⌊Q * (1 + eta) ^ (j + 1)⌋₊ := by
    intro w hw
    have hraw := hroute (geomBlock P Q (1 + eta) j)
      ⌊Q * (1 + eta) ^ j⌋₊ ⌊Q * (1 + eta) ^ (j + 1)⌋₊ D w
      hblock hab hblockRange hD (hfreq w hw)
    let xb : ℝ := max ((⌊Q * (1 + eta) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1
    have hxb1 : 1 ≤ xb := le_max_right _ _
    have hxb0 : 0 < xb := lt_of_lt_of_le zero_lt_one hxb1
    have hmuWidth := routeTWidthPolylogLower_antitone
      (A := A) (τ := -(2 * Real.pi * w)) (σ := sigma) (hfreqTop w hw)
    have hmuw : mu ≤ min delta (routeTWidthPolylogLower A (-(2 * Real.pi * w))) / 2 := by
      have hmin : min delta (routeTWidthPolylogLower A sigma)
          ≤ min delta (routeTWidthPolylogLower A (-(2 * Real.pi * w))) :=
        le_min (min_le_left _ _) (le_trans (min_le_right _ _) hmuWidth)
      linarith
    have hrel := relScaledEnvelope_le_uniform
      (A := A) (delta := delta) (Ctot := Ctot) (D := D)
      (τ := -(2 * Real.pi * w)) (x := xb) hCtot.le (by linarith)
      (hfreq16 w hw) hxb1 ht0 (hfreq0 w hw) (hfreqTop w hw)
      (by simpa [xb] using hLx) hq0 (by simpa [xb] using hq) hmu0 hmuw
      hxmin (by simpa [xb] using hxminBlock) hHmaj
    have hscaled : scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w)) xb
        ≤ xb * relScaledMajorant Ctot D Lx Hmaj mu q t0 xmin := by
      rw [scaledTwistEnvelope_eq_mul hxb0]
      exact mul_le_mul_of_nonneg_left hrel (by linarith)
    rw [harmonicCaseIBlockMajorant]
    dsimp only [xb] at hscaled
    have hfac : 0 ≤ 4 / Real.log 2 := by positivity
    have hadd : scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w))
          (max ((⌊Q * (1 + eta) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) + 7 * Real.exp 9
        ≤ max ((⌊Q * (1 + eta) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1
            * relScaledMajorant Ctot D Lx Hmaj mu q t0 xmin + 7 * Real.exp 9 := by
      linarith
    exact hraw.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hadd hfac) (by positivity))
  exact setIntegral_normSq_harmonicProduct_geom_le_HM
    (P := P) (A₀ := A0) (B₀ := B0) (Q := Q) (eta := eta)
    (W := W) (V := harmonicCaseIBlockMajorant Ctot D Lx Hmaj mu q t0 xmin
      ⌊Q * (1 + eta) ^ j⌋₊ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    hW j hleft hright hEm hEs hpoint

end

end RHTower.Sieve
