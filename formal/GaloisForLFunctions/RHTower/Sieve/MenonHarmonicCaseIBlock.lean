import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareLadderOnHM
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimeScaledBound
import GaloisForLFunctions.RHTower.Sieve.AnnulusRelBound

/-!
# Unconditional scaled Case-I block for Menon's harmonic Ramare ladder

Route T supplies the pointwise harmonic-prime saving on a full geometric prime block.  The
reciprocal Halasz--Montgomery theorem supplies the cofactor mean square on the same measurable
frequency set.  This file combines those two premise-free arithmetic inputs without changing the
block endpoints or the moving-support error.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Uniform Route-T envelope for one harmonic geometric prime block. -/
def harmonicCaseIBlockMajorant
    (Ctot D Lx Hmaj mu q t0 xmin : ℝ) (a b : ℕ) : ℝ :=
  ((4 / Real.log 2) *
      (max (b : ℝ) 1 * relScaledMajorant Ctot D Lx Hmaj mu q t0 xmin
        + 7 * Real.exp 9)) / ((a + 1 : ℕ) : ℝ)

/-- One Case-I block of Menon's harmonic Ramare ladder, with the Route-T prime estimate and the
reciprocal Halasz--Montgomery cofactor estimate both inserted. -/
theorem exists_setIntegral_normSq_harmonicRamareBlock_geom_le_scaled_HM :
    ∃ A delta Ctot tau0 : ℝ, 0 < delta ∧ 0 < Ctot ∧ 2 ≤ tau0 ∧
      ∀ (z0 z A0 B0 L j : ℕ) (Q eta W D t0 sigma Lx q mu xmin Hmaj : ℝ)
          (E : Set ℝ),
        1 ≤ z0 → Q = (z0 : ℝ) → 0 ≤ eta → j + 1 ≤ L →
        z = ⌊Q * (1 + eta) ^ L⌋₊ →
        1 ≤ ⌊Q * (1 + eta) ^ j⌋₊ →
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
          ‖harmonicRamareBlock (primesRange z0 z) (Finset.Icc A0 B0)
            (geomBlock (primesRange z0 z) Q (1 + eta) j) w‖ ^ 2)
          ≤ 2 * (harmonicCaseIBlockMajorant Ctot D Lx Hmaj mu q t0 xmin
                ⌊Q * (1 + eta) ^ j⌋₊ ⌊Q * (1 + eta) ^ (j + 1)⌋₊) ^ 2 *
              ((2 * Real.pi)⁻¹ *
                (hmMassRecip ⌊(B0 : ℝ) / (Q * (1 + eta) ^ j)⌋₊
                    (2 * Real.pi * W) (2 * Real.pi * volume.real E) *
                  ((1 / (⌈(A0 : ℝ) /
                    ((Q * (1 + eta) ^ j) * (1 + eta))⌉₊ : ℝ)) ^ 2 *
                    ((harmonicGeomCofactorBlock A0 B0 Q eta j).card : ℝ))))
            + 2 * harmonicPrimeMass
                (geomBlock (primesRange z0 z) Q (1 + eta) j) ^ 2 *
                harmonicCofactorSupportError A0 B0 Q eta W j := by
  obtain ⟨A, delta, Ctot, tau0, hdelta, hCtot, htau0, hroute⟩ :=
    exists_norm_harmonicPrimeBlockPoly_scaled_le
  refine ⟨A, delta, Ctot, tau0, hdelta, hCtot, htau0, ?_⟩
  intro z0 z A0 B0 L j Q eta W D t0 sigma Lx q mu xmin Hmaj E hz0 hQ heta hj hz
    hblock hA0 hleft hright hW hD ht0 hLx hq0 hq hmu0 hmu hxmin hxminBlock hHmaj
    hEm hEs hfreq hfreq16 hfreq0 hfreqTop
  have hQpos : 0 < Q := by
    rw [hQ]
    exact_mod_cast (Nat.zero_lt_of_lt hz0)
  have hstep : (1 : ℝ) ≤ 1 + eta := by linarith
  have hQnonneg : 0 ≤ Q := hQpos.le
  have habR : Q * (1 + eta) ^ j ≤ Q * (1 + eta) ^ (j + 1) := by
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hstep (Nat.le_succ j)) hQnonneg
  have hab : ⌊Q * (1 + eta) ^ j⌋₊ ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊ :=
    Nat.floor_mono habR
  have hprimeSet : ∀ p ∈ primesRange z0 z, p.Prime := by
    intro p hp
    exact (mem_primesRange.1 hp).1
  have hblockRange : ∀ p,
      p ∈ geomBlock (primesRange z0 z) Q (1 + eta) j ↔
        (p.Prime ∧ ⌊Q * (1 + eta) ^ j⌋₊ < p ∧
          p ≤ ⌊Q * (1 + eta) ^ (j + 1)⌋₊) :=
    fun p => mem_geomBlock_primesRange heta hQ hj hz p
  have hpoint : ∀ w ∈ E,
      ‖harmonicPrimeBlockPoly
          (geomBlock (primesRange z0 z) Q (1 + eta) j) w‖
        ≤ harmonicCaseIBlockMajorant Ctot D Lx Hmaj mu q t0 xmin
            ⌊Q * (1 + eta) ^ j⌋₊ ⌊Q * (1 + eta) ^ (j + 1)⌋₊ := by
    intro w hw
    have hraw := hroute (geomBlock (primesRange z0 z) Q (1 + eta) j)
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
    exact hraw.trans (by
      rw [harmonicCaseIBlockMajorant]
      dsimp only [xb] at hscaled
      have hfac : 0 ≤ 4 / Real.log 2 := by positivity
      have hadd : scaledTwistEnvelope A delta Ctot D (-(2 * Real.pi * w))
            (max ((⌊Q * (1 + eta) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) + 7 * Real.exp 9
          ≤ max ((⌊Q * (1 + eta) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1
              * relScaledMajorant Ctot D Lx Hmaj mu q t0 xmin + 7 * Real.exp 9 := by
        linarith
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hadd hfac)
        (by positivity))
  exact setIntegral_normSq_harmonicRamareBlock_geom_le_HM
    (P := primesRange z0 z) (A₀ := A0) (B₀ := B0) (Q := Q) (eta := eta)
    (W := W) (V := harmonicCaseIBlockMajorant Ctot D Lx Hmaj mu q t0 xmin
      ⌊Q * (1 + eta) ^ j⌋₊ ⌊Q * (1 + eta) ^ (j + 1)⌋₊)
    hA0 hQpos heta hW j hprimeSet hleft hright hEm hEs hpoint

end

end RHTower.Sieve

