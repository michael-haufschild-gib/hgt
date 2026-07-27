import GaloisForLFunctions.RHTower.DeningerDivisorFlow
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

/-- Multiplicity-exact off-line Xi divisor. -/
abbrev XiOffLineZeroCopy :=
  {q : XiZeroCopy // (q.1 : ℂ).re ≠ 1 / 2}

/-- The four quadrant copies of every strict-right upper representative,
viewed as the complete off-line divisor. -/
def xiWardQuadrupleEmbedOffLine
    (p : (Bool × Bool) × XiRightUpperZeroCopy) : XiOffLineZeroCopy :=
  ⟨xiWardQuadrupleEmbed p, by
    intro hon
    have hzero :=
      xiEndpointOffLineChargeTerm_eq_zero (xiWardQuadrupleEmbed p) hon
    have hpos : 0 <
        xiEndpointOffLineChargeTerm (xiWardQuadrupleEmbed p) := by
      rw [xiEndpointOffLineChargeTerm_quadrupleEmbed]
      exact xiEndpointWardPairWeight_pos p.2
    linarith⟩

theorem xiWardQuadrupleEmbedOffLine_injective :
    Function.Injective xiWardQuadrupleEmbedOffLine := by
  intro p p' h
  apply xiWardQuadrupleEmbed_injective
  exact congrArg Subtype.val h

theorem xiWardQuadrupleEmbedOffLine_surjective :
    Function.Surjective xiWardQuadrupleEmbedOffLine := by
  intro r
  let z : ℂ := I * xiSpectralPoint r.1
  have hzre : z.re ≠ 0 := by
    change (I * xiSpectralPoint r.1).re ≠ 0
    rw [I_mul_xiSpectralPoint]
    simp only [Complex.sub_re]
    intro hzero
    apply r.2
    norm_num at hzero ⊢
    linarith
  by_cases hpos : 0 < z.re
  · let qr : XiRightZeroCopy := ⟨r.1, hpos⟩
    cases hpair : xiRightSchwarzPairEquiv.symm qr with
    | inl q =>
        refine ⟨((false, false), q), ?_⟩
        apply Subtype.ext
        change q.1.1 = r.1
        have heq := congrArg xiRightSchwarzPairEquiv hpair
        have hright : q.1 = qr := by simpa using heq.symm
        exact congrArg Subtype.val hright
    | inr q =>
        refine ⟨((true, false), q), ?_⟩
        apply Subtype.ext
        change xiZeroCopyConjEquiv q.1.1 = r.1
        have heq := congrArg xiRightSchwarzPairEquiv hpair
        have hright : xiRightZeroCopyConjEquiv q.1 = qr := by
          simpa using heq.symm
        exact congrArg (fun x : XiRightZeroCopy => x.1) hright
  · have hneg : z.re < 0 := by
      have hnonpos := not_lt.mp hpos
      exact lt_of_le_of_ne hnonpos hzre
    have hreflect : 0 <
        (I * xiSpectralPoint (xiZeroCopyReflectEquiv r.1)).re := by
      rw [xiSpectralPoint_reflect]
      rw [show I * (-xiSpectralPoint r.1) =
        -(I * xiSpectralPoint r.1) by ring]
      rw [Complex.neg_re]
      exact neg_pos.mpr hneg
    let qr : XiRightZeroCopy :=
      ⟨xiZeroCopyReflectEquiv r.1, hreflect⟩
    cases hpair : xiRightSchwarzPairEquiv.symm qr with
    | inl q =>
        refine ⟨((false, true), q), ?_⟩
        apply Subtype.ext
        change xiZeroCopyReflectEquiv q.1.1 = r.1
        have heq := congrArg xiRightSchwarzPairEquiv hpair
        have hright : q.1 = qr := by simpa using heq.symm
        have hbase :
            q.1.1 = xiZeroCopyReflectEquiv r.1 :=
          congrArg Subtype.val hright
        rw [hbase, xiZeroCopyReflectEquiv_apply_apply]
    | inr q =>
        refine ⟨((true, true), q), ?_⟩
        apply Subtype.ext
        change xiZeroCopyLineConjEquiv q.1.1 = r.1
        have heq := congrArg xiRightSchwarzPairEquiv hpair
        have hright : xiRightZeroCopyConjEquiv q.1 = qr := by
          simpa using heq.symm
        have hbase :
            xiZeroCopyConjEquiv q.1.1 =
              xiZeroCopyReflectEquiv r.1 :=
          congrArg (fun x : XiRightZeroCopy => x.1) hright
        rw [xiZeroCopyLineConjEquiv, Equiv.trans_apply, hbase,
          xiZeroCopyReflectEquiv_apply_apply]

/-- Exact quadrant parametrization of the complete off-line Xi divisor. -/
def xiWardQuadrupleOffLineEquiv :
    (Bool × Bool) × XiRightUpperZeroCopy ≃ XiOffLineZeroCopy :=
  Equiv.ofBijective xiWardQuadrupleEmbedOffLine
    ⟨xiWardQuadrupleEmbedOffLine_injective,
      xiWardQuadrupleEmbedOffLine_surjective⟩

theorem summable_xiEndpointWardPairWeight :
    Summable xiEndpointWardPairWeight := by
  have hinj : Function.Injective
      (fun q : XiRightUpperZeroCopy => (q.1.1 : XiZeroCopy)) := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  exact summable_xiEndpointCrossCharge.comp_injective hinj

/-- The off-line endpoint charge is the sum over the literal off-line
multiplicity-copy subtype. -/
theorem xiEndpointOffLineCharge_eq_tsum_offLine :
    xiEndpointOffLineCharge =
      ∑' q : XiOffLineZeroCopy, xiEndpointCrossCharge q.1 := by
  rw [xiEndpointOffLineCharge, xiEndpointOffLineChargeTerm]
  change
    (∑' q : XiZeroCopy,
      xiEndpointOffLineSet.indicator xiEndpointCrossCharge q) =
    ∑' q : {q : XiZeroCopy // q ∈ xiEndpointOffLineSet},
      xiEndpointCrossCharge q.1
  rw [tsum_subtype]

theorem xiEndpointCrossCharge_quadrupleOffLineEquiv
    (p : (Bool × Bool) × XiRightUpperZeroCopy) :
    xiEndpointCrossCharge (xiWardQuadrupleOffLineEquiv p).1 =
      xiEndpointWardPairWeight p.2 := by
  have hterm :=
    xiEndpointOffLineChargeTerm_quadrupleEmbed p
  rw [xiEndpointOffLineChargeTerm_eq
    (xiWardQuadrupleEmbed p)
    (xiWardQuadrupleEmbedOffLine p).2] at hterm
  exact hterm

/-- **Exact source/index orbit identity.**  The complete off-line endpoint
charge is four times the source weight carried by the canonical strict-right
upper representatives. -/
theorem xiEndpointOffLineCharge_eq_four_mul_rightUpper :
    xiEndpointOffLineCharge =
      4 * ∑' q : XiRightUpperZeroCopy, xiEndpointWardPairWeight q := by
  rw [xiEndpointOffLineCharge_eq_tsum_offLine,
    ← xiWardQuadrupleOffLineEquiv.tsum_eq
      (fun q : XiOffLineZeroCopy => xiEndpointCrossCharge q.1)]
  have hsumProd : Summable
      (fun p : (Bool × Bool) × XiRightUpperZeroCopy =>
        xiEndpointWardPairWeight p.2) := by
    exact (summable_prod_of_nonneg (fun p =>
      (xiEndpointWardPairWeight_pos p.2).le)).mpr
      ⟨fun _ => summable_xiEndpointWardPairWeight, Summable.of_finite⟩
  calc
    (∑' p : (Bool × Bool) × XiRightUpperZeroCopy,
        xiEndpointCrossCharge (xiWardQuadrupleOffLineEquiv p).1) =
        ∑' p : (Bool × Bool) × XiRightUpperZeroCopy,
          xiEndpointWardPairWeight p.2 := by
      apply tsum_congr
      exact xiEndpointCrossCharge_quadrupleOffLineEquiv
    _ = ∑' i : Bool × Bool,
          ∑' q : XiRightUpperZeroCopy, xiEndpointWardPairWeight q := by
      rw [hsumProd.tsum_prod' (fun _ => summable_xiEndpointWardPairWeight)]
    _ = 4 * ∑' q : XiRightUpperZeroCopy,
          xiEndpointWardPairWeight q := by
      rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul]
      norm_num

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

/-- Global endpoint-weighted Ward index.  Each strict-right quartet contributes
its endpoint weight times the universal quantum `8π`. -/
def xiEndpointWeightedWardIndex : ℝ :=
  (8 * π) * ∑' q : XiRightUpperZeroCopy, xiEndpointWardPairWeight q

/-- **Exact endpoint-source/Ward conversion law.**  The global
source-weighted `8π` Ward index is exactly `2π` times the complete off-line
endpoint charge. -/
theorem xiEndpointWeightedWardIndex_eq_twoPi_offLineCharge :
    xiEndpointWeightedWardIndex =
      (2 * π) * xiEndpointOffLineCharge := by
  rw [xiEndpointWeightedWardIndex,
    xiEndpointOffLineCharge_eq_four_mul_rightUpper]
  ring

theorem xiEndpointWeightedWardIndex_nonneg :
    0 ≤ xiEndpointWeightedWardIndex := by
  exact mul_nonneg (by positivity) (tsum_nonneg fun q =>
    (xiEndpointWardPairWeight_pos q).le)

/-- The global weighted Ward index fits inside `2π` times the complete
off-line endpoint source charge. -/
theorem xiEndpointWeightedWardIndex_le_offLineCharge :
    xiEndpointWeightedWardIndex ≤
      (2 * π) * xiEndpointOffLineCharge := by
  exact xiEndpointWeightedWardIndex_eq_twoPi_offLineCharge.le

theorem xiEndpointWeightedWardIndex_le_completedCurvature :
    xiEndpointWeightedWardIndex ≤
      (2 * π) * xiEndpointCompletedCurvature := by
  rw [xiEndpointWeightedWardIndex_eq_twoPi_offLineCharge]
  exact mul_le_mul_of_nonneg_left
    xiEndpointOffLineCharge_le_curvature (by positivity)

/-- Explicit unconditional cap on the complete source-weighted Ward index. -/
theorem xiEndpointWeightedWardIndex_lt_ninetyThreePi_over_thousand :
    xiEndpointWeightedWardIndex < 93 * π / 1000 := by
  have hC := xiEndpointCompletedCurvature_lt_ninetyThree_over_twoThousand
  have hle := xiEndpointWeightedWardIndex_le_completedCurvature
  have hmul := mul_lt_mul_of_pos_left hC (show 0 < 2 * π by positivity)
  nlinarith

/-- Every off-line quartet forces the global weighted Ward index to pay one
full `8π` packet after multiplication by its height denominator. -/
theorem eightPi_le_xiEndpointWeightedWardIndex_mul_one_add_height_sq
    (q : XiRightUpperZeroCopy) :
    8 * π ≤ xiEndpointWeightedWardIndex *
      ((xiRightCenteredZero q.1).im ^ 2 + 1) := by
  have hqoff := xiRightUpperZeroCopy_offLine q
  have hfour :=
    four_le_offLineCharge_mul_one_add_im_sq q.1.1 hqoff
  have hmul := mul_le_mul_of_nonneg_left hfour
    (show 0 ≤ 2 * π by positivity)
  calc
    8 * π = (2 * π) * 4 := by ring
    _ ≤ (2 * π) *
        (xiEndpointOffLineCharge * ((q.1.1.1 : ℂ).im ^ 2 + 1)) := hmul
    _ = ((2 * π) * xiEndpointOffLineCharge) *
        ((q.1.1.1 : ℂ).im ^ 2 + 1) := by ring
    _ = xiEndpointWeightedWardIndex *
        ((q.1.1.1 : ℂ).im ^ 2 + 1) := by
      rw [xiEndpointWeightedWardIndex_eq_twoPi_offLineCharge]
    _ = xiEndpointWeightedWardIndex *
        ((xiRightCenteredZero q.1).im ^ 2 + 1) := by
      rw [xiRightCenteredZero, I_mul_xiSpectralPoint]
      norm_num [Complex.sub_im]

/-- The source-weighted Ward index vanishes exactly on RH. -/
theorem xiEndpointWeightedWardIndex_eq_zero_iff_rh :
    xiEndpointWeightedWardIndex = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    have hsum :
        ∑' q : XiRightUpperZeroCopy, xiEndpointWardPairWeight q = 0 := by
      rw [xiEndpointWeightedWardIndex] at hzero
      nlinarith [pi_pos]
    by_contra hnot
    obtain ⟨q⟩ :=
      nonempty_xiRightUpperZeroCopy_of_not_riemannHypothesis hnot
    have hle := summable_xiEndpointWardPairWeight.le_tsum q
      (fun j _ => (xiEndpointWardPairWeight_pos j).le)
    rw [hsum] at hle
    linarith [xiEndpointWardPairWeight_pos q]
  · intro hRH
    rw [xiEndpointWeightedWardIndex]
    have hfun : xiEndpointWardPairWeight = fun _ => 0 := by
      funext q
      exact False.elim
        (xiRightUpperZeroCopy_offLine q
          (xi_divisor_support_re_eq_half_of_rh hRH q.1.1.1))
    rw [hfun, tsum_zero, mul_zero]

theorem xiEndpointWeightedWardIndex_pos_iff_not_rh :
    0 < xiEndpointWeightedWardIndex ↔ ¬RiemannHypothesis := by
  constructor
  · intro hpos hRH
    have hzero := xiEndpointWeightedWardIndex_eq_zero_iff_rh.mpr hRH
    linarith
  · intro hnot
    exact lt_of_le_of_ne xiEndpointWeightedWardIndex_nonneg
      (fun hzero => hnot
        (xiEndpointWeightedWardIndex_eq_zero_iff_rh.mp hzero.symm))

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

/-- Complete endpoint-weighted Ward density, summed over canonical
strict-right upper representatives. -/
def xiEndpointWeightedWardDensity (t : ℝ) : ENNReal :=
  ∑' q : XiRightUpperZeroCopy,
    ENNReal.ofReal (xiEndpointWeightedWardPairDensity q t)

/-- **Global weighted Ward integral law.**  The integral of the complete
source-weighted Julia-defect density is the endpoint-weighted Ward index. -/
theorem lintegral_xiEndpointWeightedWardDensity :
    ∫⁻ t : ℝ, xiEndpointWeightedWardDensity t =
      ENNReal.ofReal xiEndpointWeightedWardIndex := by
  have hqmeas : ∀ q : XiRightUpperZeroCopy,
      AEMeasurable (fun t : ℝ =>
        ENNReal.ofReal (xiEndpointWeightedWardPairDensity q t)) := by
    intro q
    apply Measurable.aemeasurable
    apply ENNReal.continuous_ofReal.measurable.comp
    have hcont :=
      (re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_continuous q).const_mul 2
    exact (hcont.const_mul (xiEndpointWardPairWeight q)).measurable
  change
    (∫⁻ t : ℝ, ∑' q : XiRightUpperZeroCopy,
      ENNReal.ofReal (xiEndpointWeightedWardPairDensity q t)) =
      ENNReal.ofReal xiEndpointWeightedWardIndex
  rw [MeasureTheory.lintegral_tsum hqmeas]
  rw [tsum_congr lintegral_xiEndpointWeightedWardPairDensity]
  have hnn : ∀ q : XiRightUpperZeroCopy,
      0 ≤ (8 * π) * xiEndpointWardPairWeight q := by
    intro q
    exact mul_nonneg (by positivity) (xiEndpointWardPairWeight_pos q).le
  have hsum : Summable (fun q : XiRightUpperZeroCopy =>
      (8 * π) * xiEndpointWardPairWeight q) :=
    summable_xiEndpointWardPairWeight.mul_left (8 * π)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum,
    tsum_mul_left, xiEndpointWeightedWardIndex]

/-- The off-line endpoint charge can be recovered exactly from the weighted
Ward index. -/
theorem xiEndpointOffLineCharge_eq_weightedWardIndex_div_twoPi :
    xiEndpointOffLineCharge =
      xiEndpointWeightedWardIndex / (2 * π) := by
  rw [xiEndpointWeightedWardIndex_eq_twoPi_offLineCharge]
  field_simp

/-- Cubic thermal budget written solely in the endpoint-weighted Ward
coordinate. -/
def xiEndpointWeightedWardCubicBudget : ℝ :=
  4 *
    ((xiEndpointWeightedWardIndex / (2 * π)) /
      (4 - xiEndpointWeightedWardIndex / (2 * π))) ^ 3

/-- The Ward-index cubic budget is exactly the self-localized off-line
endpoint-charge budget. -/
theorem xiEndpointWeightedWardCubicBudget_eq_offLineChargeBudget :
    xiEndpointWeightedWardCubicBudget =
      xiThermalOffLineChargeCubicBudget := by
  unfold xiEndpointWeightedWardCubicBudget
    xiThermalOffLineChargeCubicBudget
  rw [xiEndpointOffLineCharge_eq_weightedWardIndex_div_twoPi]

/-- **Ward-to-thermal cubic law.**  The full transverse thermal defect is
controlled by the same source-weighted Ward index that counts every off-line
quartet with its exact endpoint charge. -/
theorem xiThermalOrientationEnergy_le_weightedWardCubicBudget :
    xiThermalOrientationEnergy ≤
      xiEndpointWeightedWardCubicBudget := by
  rw [xiEndpointWeightedWardCubicBudget_eq_offLineChargeBudget]
  exact xiThermalOrientationEnergy_le_offLineChargeCubicBudget

/-- **Ward/source/thermal gap law.**  The positive discrepancy between the
thermal second moment and the explicit prime--archimedean source is bounded
cubically by the endpoint-weighted Ward index.  Its zero set is exactly the
zero set of that index. -/
theorem xiWardSourceThermalGapLaw :
    0 ≤ xiThermalSecondMoment - normalizedPrimeArchMoment 1 ∧
    xiThermalSecondMoment - normalizedPrimeArchMoment 1 ≤
      xiEndpointWeightedWardCubicBudget ∧
    (xiThermalSecondMoment = normalizedPrimeArchMoment 1 ↔
      xiEndpointWeightedWardIndex = 0) := by
  have hgap :
      xiThermalSecondMoment - normalizedPrimeArchMoment 1 =
        xiThermalOrientationEnergy :=
    xiThermalSecondMoment_sub_source_eq_orientationEnergy
  constructor
  · rw [hgap]
    exact xiThermalOrientationEnergy_nonneg
  constructor
  · rw [hgap]
    exact xiThermalOrientationEnergy_le_weightedWardCubicBudget
  · rw [← sub_eq_zero, hgap,
      xiThermalOrientationEnergy_eq_zero_iff_rh,
      xiEndpointWeightedWardIndex_eq_zero_iff_rh]

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

/-- **Global endpoint-source/Ward law.**  One positive boundary density
simultaneously records the exact off-line endpoint charge, the RH phase,
the source-produced height gap, and the cubic thermal/source discrepancy. -/
theorem xiWardEndpointSource_globalLaw :
    (∫⁻ t : ℝ, xiEndpointWeightedWardDensity t =
      ENNReal.ofReal xiEndpointWeightedWardIndex) ∧
    xiEndpointWeightedWardIndex =
      (2 * π) * xiEndpointOffLineCharge ∧
    0 ≤ xiEndpointWeightedWardIndex ∧
    xiEndpointWeightedWardIndex < 93 * π / 1000 ∧
    (xiEndpointWeightedWardIndex = 0 ↔ RiemannHypothesis) ∧
    (xiThermalSecondMoment - normalizedPrimeArchMoment 1 =
      xiThermalOrientationEnergy) ∧
    xiThermalOrientationEnergy ≤
      xiEndpointWeightedWardCubicBudget ∧
    (xiThermalSecondMoment = normalizedPrimeArchMoment 1 ↔
      xiEndpointWeightedWardIndex = 0) ∧
    ∀ q : XiRightUpperZeroCopy,
      8 * π ≤ xiEndpointWeightedWardIndex *
        ((xiRightCenteredZero q.1).im ^ 2 + 1) := by
  exact ⟨
    lintegral_xiEndpointWeightedWardDensity,
    xiEndpointWeightedWardIndex_eq_twoPi_offLineCharge,
    xiEndpointWeightedWardIndex_nonneg,
    xiEndpointWeightedWardIndex_lt_ninetyThreePi_over_thousand,
    xiEndpointWeightedWardIndex_eq_zero_iff_rh,
    xiThermalSecondMoment_sub_source_eq_orientationEnergy,
    xiThermalOrientationEnergy_le_weightedWardCubicBudget,
    xiWardSourceThermalGapLaw.2.2,
    eightPi_le_xiEndpointWeightedWardIndex_mul_one_add_height_sq⟩

end

end RHTower
