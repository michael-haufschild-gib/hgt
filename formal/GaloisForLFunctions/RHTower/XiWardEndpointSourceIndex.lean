import GaloisForLFunctions.RHTower.PrimeArchExactOffLineQuartetAccretivity
import GaloisForLFunctions.RHTower.XiThermalOffLineChargeSelfCubicBound
import GaloisForLFunctions.RHTower.XiWardDiagonalQuantumHeightCapUniversalityLaw
import GaloisForLFunctions.RHTower.XiWardInfinitesimalDefectIndexQuantization

/-!
# Endpoint-source control of the quantized Xi Ward index

The infinitesimal Ward law assigns the same mass `8π` to every strict-right
Xi Schwarz pair.  The completed prime--Gamma endpoint source supplies a
second, nonconstant coordinate: the positive endpoint cross charge of that
same divisor orbit.

Weighting one Ward packet by its endpoint charge joins the two constructions
at the atomic level.  The resulting packet is bounded by the total off-line
source charge, vanishes only when the orbit is absent, and inherits the
source-produced zero-height exclusion.  The same sharpened height floor gives
the best currently certified upper cap for the unweighted diagonal Ward
energy.
-/

open Complex MeasureTheory Real
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Endpoint source weight carried by the strict-right representative of one
off-line FE--Schwarz quartet. -/
def xiEndpointWardPairWeight (q : XiRightUpperZeroCopy) : ℝ :=
  xiEndpointCrossCharge q.1.1

theorem xiEndpointWardPairWeight_pos (q : XiRightUpperZeroCopy) :
    0 < xiEndpointWardPairWeight q := by
  have hlower := endpoint_cross_term_re_ge_inv_one_add_im_sq q.1.1
  exact (by positivity :
    0 < 1 / ((q.1.1.1 : ℂ).im ^ 2 + 1)).trans_le hlower

theorem xiRightUpperZeroCopy_offLine (q : XiRightUpperZeroCopy) :
    (q.1.1.1 : ℂ).re ≠ 1 / 2 := by
  have hright := xiRightCenteredZero_re_pos q.1
  rw [xiRightCenteredZero, I_mul_xiSpectralPoint] at hright
  simp only [Complex.sub_re] at hright
  norm_num at hright
  linarith

theorem xiZeroCopyReflectEquiv_rho (q : XiZeroCopy) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := by
  have h := congrArg (fun z : ℂ => I * z) (xiSpectralPoint_reflect q)
  change I * xiSpectralPoint (xiZeroCopyReflectEquiv q) =
    I * (-xiSpectralPoint q) at h
  rw [I_mul_xiSpectralPoint] at h
  rw [show I * (-xiSpectralPoint q) =
      -(I * xiSpectralPoint q) by ring, I_mul_xiSpectralPoint] at h
  linear_combination h

theorem xiEndpointCrossCharge_reflect (q : XiZeroCopy) :
    xiEndpointCrossCharge (xiZeroCopyReflectEquiv q) =
      xiEndpointCrossCharge q := by
  rw [xiEndpointCrossCharge, xiEndpointCrossCharge,
    endpoint_cross_term_re_eq, endpoint_cross_term_re_eq,
    xiZeroCopyReflectEquiv_rho]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

theorem xiEndpointOffLineSet_reflect (q : XiZeroCopy)
    (h : (q.1 : ℂ).re ≠ 1 / 2) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≠ 1 / 2 := by
  rw [xiZeroCopyReflectEquiv_rho]
  simp only [Complex.sub_re, Complex.one_re]
  intro heq
  apply h
  linarith

theorem xiEndpointOffLineChargeTerm_quadrupleEmbed
    (p : (Bool × Bool) × XiRightUpperZeroCopy) :
    xiEndpointOffLineChargeTerm (xiWardQuadrupleEmbed p) =
      xiEndpointWardPairWeight p.2 := by
  obtain ⟨⟨c, r⟩, q⟩ := p
  have hqoff := xiRightUpperZeroCopy_offLine q
  cases c <;> cases r
  · simpa [xiWardQuadrupleEmbed, xiWardQuadPart,
      xiEndpointWardPairWeight] using
      xiEndpointOffLineChargeTerm_eq q.1.1 hqoff
  · rw [xiWardQuadrupleEmbed, xiWardQuadPart,
      xiEndpointOffLineChargeTerm_eq _ (xiEndpointOffLineSet_reflect q.1.1 hqoff),
      xiEndpointCrossCharge_reflect]
    rfl
  · rw [xiWardQuadrupleEmbed, xiWardQuadPart,
      xiEndpointOffLineChargeTerm_eq _ (xiEndpointOffLineSet_conj q.1.1 hqoff),
      xiEndpointCrossCharge_conj]
    rfl
  · rw [xiWardQuadrupleEmbed, xiWardQuadPart,
      xiEndpointOffLineChargeTerm_eq _
        (xiEndpointOffLineSet_lineConj q.1.1 hqoff),
      xiEndpointCrossCharge_lineConj]
    rfl

theorem summable_xiEndpointWardPairWeight :
    Summable xiEndpointWardPairWeight := by
  have hinj : Function.Injective
      (fun q : XiRightUpperZeroCopy => (q.1.1 : XiZeroCopy)) := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  exact summable_xiEndpointCrossCharge.comp_injective hinj

/-- Four endpoint-weight copies of every strict-right pair inject into the
complete off-line endpoint charge. -/
theorem four_mul_tsum_xiEndpointWardPairWeight_le_offLineCharge :
    4 * ∑' q : XiRightUpperZeroCopy, xiEndpointWardPairWeight q ≤
      xiEndpointOffLineCharge := by
  have hslice : ∀ i : Bool × Bool,
      (fun q : XiRightUpperZeroCopy =>
        xiEndpointOffLineChargeTerm (xiWardQuadrupleEmbed (i, q))) =
      xiEndpointWardPairWeight :=
    fun i => funext fun q =>
      xiEndpointOffLineChargeTerm_quadrupleEmbed (i, q)
  have hFsummable : Summable
      (fun p : (Bool × Bool) × XiRightUpperZeroCopy =>
        xiEndpointOffLineChargeTerm (xiWardQuadrupleEmbed p)) := by
    refine (summable_prod_of_nonneg ?_).mpr ⟨?_, ?_⟩
    · intro p
      exact xiEndpointOffLineChargeTerm_nonneg _
    · intro i
      rw [hslice i]
      exact summable_xiEndpointWardPairWeight
    · apply Summable.of_finite
  have htsum :
      ∑' p : (Bool × Bool) × XiRightUpperZeroCopy,
          xiEndpointOffLineChargeTerm (xiWardQuadrupleEmbed p) =
        4 * ∑' q : XiRightUpperZeroCopy, xiEndpointWardPairWeight q := by
    rw [hFsummable.tsum_prod' (fun i => by
      rw [hslice i]
      exact summable_xiEndpointWardPairWeight)]
    have hinner : ∀ i : Bool × Bool,
        ∑' q : XiRightUpperZeroCopy,
            xiEndpointOffLineChargeTerm (xiWardQuadrupleEmbed (i, q)) =
          ∑' q : XiRightUpperZeroCopy, xiEndpointWardPairWeight q :=
      fun i => by rw [hslice i]
    rw [tsum_fintype, Finset.sum_congr rfl (fun i _ => hinner i),
      Finset.sum_const, nsmul_eq_mul]
    norm_num
  have hcomp :
      ∑' p : (Bool × Bool) × XiRightUpperZeroCopy,
          xiEndpointOffLineChargeTerm (xiWardQuadrupleEmbed p) ≤
        ∑' q : XiZeroCopy, xiEndpointOffLineChargeTerm q :=
    Summable.tsum_le_tsum_of_inj xiWardQuadrupleEmbed
      xiWardQuadrupleEmbed_injective
      (fun q _ => xiEndpointOffLineChargeTerm_nonneg q)
      (fun _ => le_rfl)
      hFsummable summable_xiEndpointOffLineChargeTerm
  rw [htsum] at hcomp
  exact hcomp

/-- Source-weighted infinitesimal Julia-defect density of one strict-right
Schwarz pair. -/
def xiEndpointWeightedWardPairDensity
    (q : XiRightUpperZeroCopy) (t : ℝ) : ℝ :=
  xiEndpointWardPairWeight q *
    (2 * (xiAntiCausalWardSchwarzPairResponse q
      ((1 / 2 : ℂ) + I * (t : ℂ))).re)

theorem xiEndpointWeightedWardPairDensity_nonneg
    (q : XiRightUpperZeroCopy) (t : ℝ) :
    0 ≤ xiEndpointWeightedWardPairDensity q t := by
  have hprofile :
      0 ≤ 2 * (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
    rw [re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq]
    have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by
      linarith [xiRightCenteredZero_re_pos q.1]
    have h₁ := lorentzian_nonneg hx
      (t + (xiRightCenteredZero q.1).im)
    have h₂ := lorentzian_nonneg hx
      (t + -(xiRightCenteredZero q.1).im)
    nlinarith
  exact mul_nonneg (xiEndpointWardPairWeight_pos q).le hprofile

/-- **Atomic source-weighted index law.**  The weighted Julia-defect mass of
one strict-right quartet is exactly its endpoint source weight times the
universal quantum `8π`. -/
theorem lintegral_xiEndpointWeightedWardPairDensity
    (q : XiRightUpperZeroCopy) :
    ∫⁻ t : ℝ, ENNReal.ofReal
        (xiEndpointWeightedWardPairDensity q t) =
      ENNReal.ofReal
        ((8 * π) * xiEndpointWardPairWeight q) := by
  let f : ℝ → ℝ := fun t =>
    2 * (xiAntiCausalWardSchwarzPairResponse q
      ((1 / 2 : ℂ) + I * (t : ℂ))).re
  have hw : 0 ≤ xiEndpointWardPairWeight q :=
    (xiEndpointWardPairWeight_pos q).le
  have hf : ∀ t, 0 ≤ f t := by
    intro t
    change 0 ≤ 2 * (xiAntiCausalWardSchwarzPairResponse q
      ((1 / 2 : ℂ) + I * (t : ℂ))).re
    rw [re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq]
    have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by
      linarith [xiRightCenteredZero_re_pos q.1]
    have h₁ := lorentzian_nonneg hx
      (t + (xiRightCenteredZero q.1).im)
    have h₂ := lorentzian_nonneg hx
      (t + -(xiRightCenteredZero q.1).im)
    nlinarith
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (f t) := by
    exact ENNReal.continuous_ofReal.measurable.comp
      ((re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_continuous q).const_mul 2).measurable
  simp_rw [xiEndpointWeightedWardPairDensity, ENNReal.ofReal_mul hw]
  rw [MeasureTheory.lintegral_const_mul'
    (ENNReal.ofReal (xiEndpointWardPairWeight q)) _ (by simp)]
  rw [lintegral_infinitesimalDefect_xiAntiCausalWardSchwarzPair_eulerEdge]
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 8 * π)]
  ring

/-- Every weighted `8π` packet fits inside `2π` times the complete off-line
endpoint source charge. -/
theorem xiEndpointWeightedWardPairMass_le_offLineCharge
    (q : XiRightUpperZeroCopy) :
    (8 * π) * xiEndpointWardPairWeight q ≤
      (2 * π) * xiEndpointOffLineCharge := by
  have hqoff : (q.1.1.1 : ℂ).re ≠ 1 / 2 := by
    have hright := xiRightCenteredZero_re_pos q.1
    rw [xiRightCenteredZero, I_mul_xiSpectralPoint] at hright
    simp only [Complex.sub_re] at hright
    norm_num at hright
    linarith
  have hcharge :=
    four_mul_xiEndpointCrossCharge_le_offLineCharge q.1.1 hqoff
  have hpi : 0 < 2 * π := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcharge hpi.le
  dsimp only [xiEndpointWardPairWeight]
  nlinarith

/-- The exact quartet source budget sharpens the upper cap on every local
diagonal Ward packet. -/
theorem xiPairGramTerm_diag_lt_exactQuartetHeightCap
    (q : XiRightUpperZeroCopy) :
    xiPairGramTerm q q < 8 * π * (15907 / 7907 : ℝ) := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hstrip := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by
    linarith
  have hx1 : (xiRightCenteredZero q.1).re + 1 / 2 < 1 := by
    linarith
  have hqoff : (q.1.1.1 : ℂ).re ≠ 1 / 2 := by
    rw [xiRightCenteredZero, I_mul_xiSpectralPoint] at hre
    simp only [Complex.sub_re] at hre
    norm_num at hre
    linarith
  have hb0 :=
    xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq
      q.1.1 hqoff
  have hb :
      7907 / 93 < (xiRightCenteredZero q.1).im ^ 2 := by
    rw [xiRightCenteredZero, I_mul_xiSpectralPoint]
    norm_num [Complex.sub_im]
    exact hb0
  have hinv :
      1 / ((xiRightCenteredZero q.1).re + 1 / 2) < 2 := by
    rw [div_lt_iff₀ hx]
    nlinarith
  have hden : 0 <
      ((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
        (xiRightCenteredZero q.1).im ^ 2 := by
    positivity
  have hsecond :
      ((xiRightCenteredZero q.1).re + 1 / 2) /
          (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
            (xiRightCenteredZero q.1).im ^ 2) <
        93 / 7907 := by
    rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 7907)]
    nlinarith [sq_nonneg ((xiRightCenteredZero q.1).re + 1 / 2)]
  rw [xiPairGramTerm_diag_eq]
  have hadd := add_lt_add hinv hsecond
  have hmul := mul_lt_mul_of_pos_left hadd
    (show 0 < 8 * π by positivity)
  norm_num at hmul ⊢
  exact hmul

/-- **Endpoint-source/Ward atomic law.**  Every strict-right Xi quartet has
one exact `8π` Ward index, a strictly positive source-weighted packet bounded
by the total off-line endpoint charge, squared height above `7907/93`, and a
diagonal Ward energy in the sharpened universal band. -/
theorem xiWardEndpointSource_atomicLaw
    (q : XiRightUpperZeroCopy) :
    (∫⁻ t : ℝ, ENNReal.ofReal
        (2 * (xiAntiCausalWardSchwarzPairResponse q
          ((1 / 2 : ℂ) + I * (t : ℂ))).re) =
      ENNReal.ofReal (8 * π)) ∧
    0 < xiEndpointWardPairWeight q ∧
    (8 * π) * xiEndpointWardPairWeight q ≤
      (2 * π) * xiEndpointOffLineCharge ∧
    7907 / 93 < (xiRightCenteredZero q.1).im ^ 2 ∧
    8 * π < xiPairGramTerm q q ∧
    xiPairGramTerm q q < 8 * π * (15907 / 7907 : ℝ) := by
  have hqoff : (q.1.1.1 : ℂ).re ≠ 1 / 2 := by
    have hre := xiRightCenteredZero_re_pos q.1
    rw [xiRightCenteredZero, I_mul_xiSpectralPoint] at hre
    simp only [Complex.sub_re] at hre
    norm_num at hre
    linarith
  have hb0 :=
    xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq
      q.1.1 hqoff
  have hb :
      7907 / 93 < (xiRightCenteredZero q.1).im ^ 2 := by
    rw [xiRightCenteredZero, I_mul_xiSpectralPoint]
    norm_num [Complex.sub_im]
    exact hb0
  exact ⟨
    lintegral_infinitesimalDefect_xiAntiCausalWardSchwarzPair_eulerEdge q,
    xiEndpointWardPairWeight_pos q,
    xiEndpointWeightedWardPairMass_le_offLineCharge q,
    hb,
    (xiWard_diagonalQuantum_heightCapUniversality q).1,
    xiPairGramTerm_diag_lt_exactQuartetHeightCap q⟩

end

end RHTower
