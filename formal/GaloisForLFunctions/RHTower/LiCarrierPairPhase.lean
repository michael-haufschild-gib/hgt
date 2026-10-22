import GaloisForLFunctions.RHTower.LiCarrierPairGeometry
import GaloisForLFunctions.RHTower.WindowBudget
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCayleyPhaseLift
import GaloisForLFunctions.HTGeometry.HausdorffCDDPhaseKernel

/-!
# Phase and band positivity of critical-line Li pairs

The Li coordinate at height `gamma > 0` has the exact phase
`2 arctan (1 / (2 gamma))`.  Existing sharp elementary arctangent bounds then put the degree-`n`
phase in a fixed cosine chamber whenever `gamma` lies between `n` and `3n`.  This supplies a
uniform positive contribution for the arithmetic-progression block used by the carrier lower
bound.
-/

namespace RHTower

noncomputable section

/-- Principal positive phase of the critical-line Li coordinate at height `gamma`. -/
def liCarrierPhase (gamma : ℝ) : ℝ :=
  2 * Real.arctan (1 / (2 * gamma))

/-- Exact polar representation of the critical-line Li coordinate. -/
theorem liCarrierCoordinate_eq_exp_phase {gamma : ℝ} (hgamma : 0 < gamma) :
    liCarrierCoordinate gamma =
      Complex.exp ((liCarrierPhase gamma : ℝ) * Complex.I) := by
  have hgamma0 : gamma ≠ 0 := ne_of_gt hgamma
  have hexpRe :
      (Complex.exp ((liCarrierPhase gamma : ℝ) * Complex.I)).re =
        Real.cos (liCarrierPhase gamma) := by
    rw [Complex.exp_ofReal_mul_I]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, zero_mul, mul_zero, add_zero, sub_zero]
  have hexpIm :
      (Complex.exp ((liCarrierPhase gamma : ℝ) * Complex.I)).im =
        Real.sin (liCarrierPhase gamma) := by
    rw [Complex.exp_ofReal_mul_I]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
  rw [liCarrierCoordinate,
    liMobiusCoordinate_realPart_height (beta := (1 / 2 : ℝ)) hgamma0]
  apply Complex.ext
  · rw [hexpRe]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, liCarrierPhase]
    rw [Real.cos_two_mul, GaloisForLFunctions.RHTower.cos_arctan_sq]
    have hden : gamma ≠ 0 := ne_of_gt hgamma
    field_simp [hden]
    ring
  · rw [hexpIm]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.I_re, zero_mul, mul_one, zero_add, Complex.ofReal_re,
      liCarrierPhase]
    rw [Real.sin_two_mul, mul_assoc,
      GaloisForLFunctions.RHTower.sin_arctan_mul_cos_arctan]
    have hden : gamma ≠ 0 := ne_of_gt hgamma
    field_simp [hden]
    ring

/-- The carrier phase is positive at every positive height. -/
theorem liCarrierPhase_pos {gamma : ℝ} (hgamma : 0 < gamma) :
    0 < liCarrierPhase gamma := by
  unfold liCarrierPhase
  exact mul_pos (by norm_num) (Real.arctan_pos.mpr (by positivity))

/-- Elementary upper phase bound `theta_gamma ≤ 1/gamma`. -/
theorem liCarrierPhase_le_inv {gamma : ℝ} (hgamma : 0 < gamma) :
    liCarrierPhase gamma ≤ 1 / gamma := by
  unfold liCarrierPhase
  have h := GaloisForLFunctions.HTGeometry.arctan_le_self
    (show 0 ≤ 1 / (2 * gamma) by positivity)
  calc
    2 * Real.arctan (1 / (2 * gamma)) ≤ 2 * (1 / (2 * gamma)) := by linarith
    _ = 1 / gamma := by field_simp

/-- Elementary lower phase bound `1/(2 gamma) ≤ theta_gamma` above height `1/2`. -/
theorem inv_two_mul_le_liCarrierPhase {gamma : ℝ}
    (hgamma : 0 < gamma) (hgammaHalf : 1 / 2 ≤ gamma) :
    1 / (2 * gamma) ≤ liCarrierPhase gamma := by
  unfold liCarrierPhase
  have hx0 : 0 ≤ 1 / (2 * gamma) := by positivity
  have hx1 : 1 / (2 * gamma) ≤ 1 := by
    rw [div_le_one (by positivity : 0 < 2 * gamma)]
    linarith
  have h := arctan_ge_half_self hx0 hx1
  linarith

/-- Exact cosine form of the paired Li contribution. -/
theorem liCarrierPairContribution_eq_cos {n : ℕ} {gamma : ℝ}
    (hgamma : 0 < gamma) :
    liCarrierPairContribution n gamma =
      2 - 2 * Real.cos ((n : ℝ) * liCarrierPhase gamma) := by
  have hexp : (n : ℂ) * ((liCarrierPhase gamma : ℂ) * Complex.I) =
      ((((n : ℝ) * liCarrierPhase gamma : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  have hexpRe :
      (Complex.exp ((((n : ℝ) * liCarrierPhase gamma : ℝ) : ℂ) * Complex.I)).re =
        Real.cos ((n : ℝ) * liCarrierPhase gamma) := by
    rw [Complex.exp_ofReal_mul_I]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, zero_mul, mul_zero, add_zero, sub_zero]
  rw [liCarrierPairContribution_eq_two_sub_two_re (ne_of_gt hgamma),
    liCarrierCoordinate_eq_exp_phase hgamma, ← Complex.exp_nat_mul, hexp,
    hexpRe]

/-- On the height band `n ≤ gamma ≤ 3n`, the degree-`n` phase lies in `[1/6,1]`. -/
theorem liCarrierPhase_band {n : ℕ} {gamma : ℝ} (hn : 1 ≤ n)
    (hlower : (n : ℝ) ≤ gamma) (hupper : gamma ≤ 3 * (n : ℝ)) :
    1 / 6 ≤ (n : ℝ) * liCarrierPhase gamma ∧
      (n : ℝ) * liCarrierPhase gamma ≤ 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hgamma : 0 < gamma := lt_of_lt_of_le hnpos hlower
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hphaseLower := inv_two_mul_le_liCarrierPhase hgamma
    ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans (hnone.trans hlower))
  have hphaseUpper := liCarrierPhase_le_inv hgamma
  constructor
  · have hdiv : 1 / 6 ≤ (n : ℝ) * (1 / (2 * gamma)) := by
      have hbase : 1 / 6 ≤ (n : ℝ) / (2 * gamma) := by
        rw [le_div_iff₀ (by positivity : 0 < 2 * gamma)]
        nlinarith
      simpa [div_eq_mul_inv, one_div] using hbase
    exact hdiv.trans (mul_le_mul_of_nonneg_left hphaseLower hnpos.le)
  · calc
      (n : ℝ) * liCarrierPhase gamma ≤ (n : ℝ) * (1 / gamma) :=
        mul_le_mul_of_nonneg_left hphaseUpper hnpos.le
      _ ≤ 1 := by
        have hbase : (n : ℝ) / gamma ≤ 1 := (div_le_one hgamma).2 hlower
        simpa [div_eq_mul_inv, one_div] using hbase

/-- Uniform positive floor for a degree-`n` pair in the band `n ≤ gamma ≤ 3n`. -/
theorem liCarrierPairContribution_lower_on_band {n : ℕ} {gamma : ℝ}
    (hn : 1 ≤ n) (hlower : (n : ℝ) ≤ gamma)
    (hupper : gamma ≤ 3 * (n : ℝ)) :
    2 - 2 * Real.cos (1 / 6) ≤ liCarrierPairContribution n gamma := by
  have hgamma : 0 < gamma := lt_of_lt_of_le (by exact_mod_cast hn) hlower
  obtain ⟨hphaseLower, hphaseUpper⟩ := liCarrierPhase_band hn hlower hupper
  have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hcos : Real.cos ((n : ℝ) * liCarrierPhase gamma) ≤ Real.cos (1 / 6) := by
    exact Real.antitoneOn_cos
      ⟨by norm_num, by linarith⟩
      ⟨by linarith, hphaseUpper.trans hpi⟩ hphaseLower
  rw [liCarrierPairContribution_eq_cos hgamma]
  linarith

/-- Every positive-degree pair is strictly positive once its height is at least the degree. -/
theorem liCarrierPairContribution_pos_of_degree_le_height {n : ℕ} {gamma : ℝ}
    (hn : 1 ≤ n) (hgamma : 0 < gamma) (hdegree : (n : ℝ) ≤ gamma) :
    0 < liCarrierPairContribution n gamma := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hphasePos : 0 < (n : ℝ) * liCarrierPhase gamma :=
    mul_pos hnpos (liCarrierPhase_pos hgamma)
  have hphaseUpper : (n : ℝ) * liCarrierPhase gamma ≤ 1 := by
    calc
      (n : ℝ) * liCarrierPhase gamma ≤ (n : ℝ) * (1 / gamma) :=
        mul_le_mul_of_nonneg_left (liCarrierPhase_le_inv hgamma) hnpos.le
      _ ≤ 1 := by
        have hbase : (n : ℝ) / gamma ≤ 1 := (div_le_one hgamma).2 hdegree
        simpa [div_eq_mul_inv, one_div] using hbase
  have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hcos : Real.cos ((n : ℝ) * liCarrierPhase gamma) < 1 := by
    have hlt := Real.strictAntiOn_cos
      (Set.mem_Icc.mpr ⟨by norm_num, Real.pi_pos.le⟩)
      (Set.mem_Icc.mpr ⟨hphasePos.le, hphaseUpper.trans hpi⟩) hphasePos
    simpa using hlt
  rw [liCarrierPairContribution_eq_cos hgamma]
  linarith

/-- The uniform band floor is strictly positive. -/
theorem two_sub_two_cos_one_sixth_pos :
    0 < 2 - 2 * Real.cos (1 / 6) := by
  have hpos : (0 : ℝ) < 1 / 6 := by norm_num
  have hltpi : (1 / 6 : ℝ) < Real.pi := by nlinarith [Real.pi_gt_three]
  have hlt := Real.strictAntiOn_cos
    (Set.mem_Icc.mpr ⟨by norm_num, Real.pi_pos.le⟩)
    (Set.mem_Icc.mpr ⟨hpos.le, hltpi.le⟩) hpos
  rw [Real.cos_zero] at hlt
  linarith

end

end RHTower
