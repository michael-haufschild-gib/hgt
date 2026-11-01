import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.SemilocalPositivityObstructions
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilExactFiniteSchur
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheApertureFlowNeverStalls
import GaloisForLFunctions.LatticeSectionTheory.BidegreeCountsSeeNoPrimitiveClass
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.LiouvilleOddWindowRefutationAndSelectiveFullPositivity

/-!
# Intrinsic Positive-Operator Trace Rewriting, Krein Polar Splitting, and Window Corollaries

Together with `PrimeValuationShellLogTrace`, `HalfLogThreeCutoffAndTraceIdentity`, and
`SemilocalPositivityObstructions`, this module completes the resolution of the `{∞, 2}` semilocal
operator-trace question through aperture `½ log 3`:

1. **Krein `(+1, -1)` parity-chirality decomposition of `ccmPolarOperator a`:**
   On `suzukiApertureHilbert a`, the hyperbolic combinations
   `c₊ = ½ (h₊ + h₋)` (`cosh`) and `c₋ = ½ (h₊ - h₋)` (`sinh`) split the rank-two polar block into
   the difference `ccmPolarEvenOperator a - ccmPolarOddOperator a` of two positive trace-class
   rank-one operators (`2 |c₊⟩⟨c₊|` and `2 |c₋⟩⟨c₋|`), isolating the odd hyperbolic channel
   responsible for the `{∞, 2}` ground-energy collapse in `SemilocalPositivityObstructions`.
2. **Intrinsic aperture operator-trace rewriting and exact positivity equivalences:**
   On `CCMArchimedeanFormDomain a`, composing the self-adjoint zero-energy operator
   `ccmRestrictedWeilZeroFormOperator a = 1 - ccmRestrictedWeilFormBirmanSchwinger a 0` with the
   rank-one projection `|u⟩⟨u|` yields a trace-class operator with exact trace
   `opTrace (ccmRestrictedWeilZeroFormOperator a ∘L rankOne ℂ u u) = ccmRestrictedWeilForm a u u`.
   At every aperture `a`, positivity of this trace across all `u` is equivalent to
   `IsPositive (ccmRestrictedWeilZeroFormOperator a)` and to `0 ≤ ccmRestrictedWeilGroundEnergy a`,
   and across all apertures to `RiemannHypothesis`.
3. **Unconditional intrinsic operator-trace positivity past `½ log 2` (`a ≤ 181 / 500`):**
   Combining the trace equivalence with the full-sector certificate on `[−181/500, 181/500]` proves
   `IsPositive (ccmRestrictedWeilZeroFormOperator a)` unconditionally for all `0 < a ≤ 181 / 500`
   (including `halfLogTwoAperture`), upgrades the lower bound on `zetaContactAperture` off `RH` to
   `181 / 500 > ½ log 2`, and upgrades all-profile (`realTestsAt a`) Castelnuovo–Severi Hodge index,
   Künneth effectivity, and `l2SourceCone` arithmetic Riemann–Roch from `a ≤ 3 / 10` past the first
   prime `2` to `a ≤ 181 / 500`.
4. **Sharp equivalences and corollaries at `½ log 3` (`halfLogThreeAperture`), and complete
   synthesis:**
   At `halfLogThreeAperture`, `IsPositive (ccmRestrictedWeilZeroFormOperator halfLogThreeAperture)`
   is equivalent to `0 ≤ (primeSingleSemilocalFamily 2).energy halfLogThreeAperture` and to open
   window positivity on `(0, ½ log 3)`, forcing strict positivity of the ground-energy flow and all
   scaling-subsurface Hodge/Künneth laws on `(0, ½ log 3)`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology BigOperators
open scoped ENNReal InnerProductSpace Real
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilDeletion
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.LatticeSectionTheory
open GaloisForLFunctions.ArithmeticEffectivityTheory
open GaloisForLFunctions.ArithmeticOrientationGeometry

namespace GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace

/-! ## 1. Krein `(+1, -1)` parity-chirality decomposition of `ccmPolarOperator` -/

/-- Even (`cosh`) hyperbolic polar vector `½ (h_{1/2} + h_{-1/2})` in `suzukiApertureHilbert a`. -/
def ccmPolarCoshVector (a : SuzukiPositiveAperture) : suzukiApertureHilbert a :=
  ((1 / 2 : ℝ) : ℂ) • (ccmPolarApertureVector a (1 / 2) + ccmPolarApertureVector a (-1 / 2))

/-- Odd (`sinh`) hyperbolic polar vector `½ (h_{1/2} - h_{-1/2})` in `suzukiApertureHilbert a`. -/
def ccmPolarSinhVector (a : SuzukiPositiveAperture) : suzukiApertureHilbert a :=
  ((1 / 2 : ℝ) : ℂ) • (ccmPolarApertureVector a (1 / 2) - ccmPolarApertureVector a (-1 / 2))

/-- Positive rank-one even (`cosh`) polar operator `2 |c₊⟩⟨c₊|`. -/
def ccmPolarEvenOperator (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  (2 : ℂ) • InnerProductSpace.rankOne ℂ (ccmPolarCoshVector a) (ccmPolarCoshVector a)

/-- Positive rank-one odd (`sinh`) polar operator `2 |c₋⟩⟨c₋|`. -/
def ccmPolarOddOperator (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  (2 : ℂ) • InnerProductSpace.rankOne ℂ (ccmPolarSinhVector a) (ccmPolarSinhVector a)

theorem two_smul_rankOne_self_isPositive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (v : H) :
    ContinuousLinearMap.IsPositive ((2 : ℂ) • InnerProductSpace.rankOne ℂ v v) := by
  have hpos := rankOne_self_isPositive v
  have hsa : IsSelfAdjoint ((2 : ℂ) • InnerProductSpace.rankOne ℂ v v) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.adjoint.map_smulₛₗ,
      InnerProductSpace.adjoint_rankOne, map_ofNat]
  refine ⟨hsa.isSymmetric, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf, clm_smul_apply, inner_smul_left, map_ofNat]
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  change 0 ≤ ((2 : ℂ) * inner ℂ (InnerProductSpace.rankOne ℂ v v x) x).re
  rw [h2, Complex.re_ofReal_mul]
  exact mul_nonneg (by norm_num) (hpos.2 x)

theorem rankOne_hasRankLE_one {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (x y : H) :
    HasRankLE (InnerProductSpace.rankOne ℂ x y) 1 := by
  simpa using hasRankLE_sum_range_rankOne (fun _ => x) (fun _ => y) 1

theorem smul_rankOne_isTraceClass {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (c : ℂ) (x y : H) :
    ContinuousLinearMap.IsTraceClass (c • InnerProductSpace.rankOne ℂ x y) := by
  obtain ⟨V, hVfd, hVdim, hVmem⟩ := rankOne_hasRankLE_one x y
  have hrank : HasRankLE (c • InnerProductSpace.rankOne ℂ x y) 1 := by
    refine ⟨V, hVfd, hVdim, fun z => ?_⟩
    rw [clm_smul_apply]
    exact V.smul_mem c (hVmem z)
  exact (memSchattenClass_of_hasRankLE one_pos hrank).one_isTraceClass

theorem ccmPolarEvenOperator_isPositive (a : SuzukiPositiveAperture) :
    ContinuousLinearMap.IsPositive (ccmPolarEvenOperator a) :=
  two_smul_rankOne_self_isPositive (ccmPolarCoshVector a)

theorem ccmPolarOddOperator_isPositive (a : SuzukiPositiveAperture) :
    ContinuousLinearMap.IsPositive (ccmPolarOddOperator a) :=
  two_smul_rankOne_self_isPositive (ccmPolarSinhVector a)

theorem ccmPolarEvenOperator_isTraceClass (a : SuzukiPositiveAperture) :
    ContinuousLinearMap.IsTraceClass (ccmPolarEvenOperator a) :=
  smul_rankOne_isTraceClass 2 (ccmPolarCoshVector a) (ccmPolarCoshVector a)

theorem ccmPolarOddOperator_isTraceClass (a : SuzukiPositiveAperture) :
    ContinuousLinearMap.IsTraceClass (ccmPolarOddOperator a) :=
  smul_rankOne_isTraceClass 2 (ccmPolarSinhVector a) (ccmPolarSinhVector a)

/-- **Exact Krein `(+1, -1)` decomposition of `ccmPolarOperator a`:**
the source polar operator is the difference `2 |c₊⟩⟨c₊| - 2 |c₋⟩⟨c₋|` of two positive trace-class
rank-one operators aligned with the even (`cosh`) and odd (`sinh`) pole moments. -/
theorem ccmPolarOperator_eq_even_sub_odd (a : SuzukiPositiveAperture) :
    ccmPolarOperator a = ccmPolarEvenOperator a - ccmPolarOddOperator a := by
  refine ContinuousLinearMap.ext fun f => ext_inner_right ℂ fun g => ?_
  unfold ccmPolarOperator ccmPolarEvenOperator ccmPolarOddOperator
    ccmPolarCoshVector ccmPolarSinhVector
  simp only [clm_add_apply, clm_sub_apply, clm_smul_apply,
    InnerProductSpace.rankOne_apply, inner_add_left, inner_sub_left, inner_smul_left,
    map_add, map_sub, map_mul, map_ofNat, Complex.conj_ofReal]
  push_cast
  ring

/-! ## 2. Intrinsic operator-trace rewriting and exact positivity equivalences -/

theorem ccmRestrictedWeilZeroFormOperator_isSelfAdjoint (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (ccmRestrictedWeilZeroFormOperator a) :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mpr (ccmRestrictedWeilZeroFormOperator_adjoint a)

theorem comp_rankOne_eq_rankOne {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (u v : H) :
    T ∘L InnerProductSpace.rankOne ℂ u v = InnerProductSpace.rankOne ℂ (T u) v :=
  ContinuousLinearMap.ext fun x => by
    rw [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply,
      InnerProductSpace.rankOne_apply, map_smul]

theorem comp_rankOne_isTraceClass {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (u v : H) :
    ContinuousLinearMap.IsTraceClass (T ∘L InnerProductSpace.rankOne ℂ u v) := by
  rw [comp_rankOne_eq_rankOne]
  exact (memSchattenClass_of_hasRankLE one_pos (rankOne_hasRankLE_one (T u) v)).one_isTraceClass

/-- **Intrinsic trace-class representation of the restricted Weil sesquilinear diagonal:**
`opTrace ((1 - K_a(0)) ∘L |u⟩⟨u|) = ccmRestrictedWeilForm a u u`. -/
theorem opTrace_ccmRestrictedWeilZeroFormOperator_comp_rankOne
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ContinuousLinearMap.opTrace
        (ccmRestrictedWeilZeroFormOperator a ∘L InnerProductSpace.rankOne ℂ u u) =
      ccmRestrictedWeilForm a u u := by
  rw [opTrace_comp_rankOne_self_of_isSelfAdjoint
    (ccmRestrictedWeilZeroFormOperator_isSelfAdjoint a) u,
    inner_ccmRestrictedWeilZeroFormOperator]

/-- **Intrinsic operator-trace identity for the restricted Weil quadratic form:**
at every aperture `a > 0` and for every `u : CCMArchimedeanFormDomain a`,
`ccmRestrictedWeilSourceQuadratic a u = Re Tr((1 - K_a(0)) ∘L |u⟩⟨u|)`. -/
theorem opTrace_ccmRestrictedWeilZeroFormOperator_comp_rankOne_re
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (ContinuousLinearMap.opTrace
        (ccmRestrictedWeilZeroFormOperator a ∘L InnerProductSpace.rankOne ℂ u u)).re =
      ccmRestrictedWeilSourceQuadratic a u := by
  rw [opTrace_ccmRestrictedWeilZeroFormOperator_comp_rankOne,
    ccmRestrictedWeilForm_self_re_eq_source]

/-- **Exact operator-positivity and ground-energy equivalence at aperture `a`:**
`ccmRestrictedWeilZeroFormOperator a` is a positive operator on `CCMArchimedeanFormDomain a` if and
only if the restricted Weil ground energy at `a` is nonnegative. -/
theorem isPositive_ccmRestrictedWeilZeroFormOperator_iff_groundEnergy_nonneg
    (a : SuzukiPositiveAperture) :
    ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator a) ↔
      0 ≤ ccmRestrictedWeilGroundEnergy a := by
  constructor
  · intro hpos
    obtain ⟨u, hu, heq⟩ := ccmRestrictedWeilSource_exists_groundFormState a
    have hge := hpos.2 u
    rw [ContinuousLinearMap.reApplyInnerSelf] at hge
    change 0 ≤ (inner ℂ (ccmRestrictedWeilZeroFormOperator a u) u).re at hge
    rw [inner_ccmRestrictedWeilZeroFormOperator, ccmRestrictedWeilForm_self_re_eq_source,
      heq] at hge
    have hnorm : 0 < ‖ccmArchimedeanFormToAperture a u‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hu)
    by_contra hneg
    push Not at hneg
    linarith only [hge, mul_neg_of_neg_of_pos hneg hnorm]
  · intro hμ
    refine ⟨(ccmRestrictedWeilZeroFormOperator_isSelfAdjoint a).isSymmetric, fun u => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf]
    change 0 ≤ (inner ℂ (ccmRestrictedWeilZeroFormOperator a u) u).re
    rw [inner_ccmRestrictedWeilZeroFormOperator, ccmRestrictedWeilForm_self_re_eq_source]
    exact le_trans (mul_nonneg hμ (sq_nonneg _))
      (ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u)

/-- **Trace-nonnegativity equivalence at aperture `a`:**
`IsPositive (ccmRestrictedWeilZeroFormOperator a)` holds iff the intrinsic rank-one operator trace
is nonnegative on every form vector `u`. -/
theorem isPositive_ccmRestrictedWeilZeroFormOperator_iff_opTrace_nonneg
    (a : SuzukiPositiveAperture) :
    ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator a) ↔
      ∀ u : CCMArchimedeanFormDomain a,
        0 ≤ (ContinuousLinearMap.opTrace
          (ccmRestrictedWeilZeroFormOperator a ∘L InnerProductSpace.rankOne ℂ u u)).re := by
  rw [isPositive_ccmRestrictedWeilZeroFormOperator_iff_groundEnergy_nonneg]
  constructor
  · intro hμ u
    rw [opTrace_ccmRestrictedWeilZeroFormOperator_comp_rankOne_re]
    exact le_trans (mul_nonneg hμ (sq_nonneg _))
      (ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u)
  · intro htr
    obtain ⟨u, hu, heq⟩ := ccmRestrictedWeilSource_exists_groundFormState a
    have hge := htr u
    rw [opTrace_ccmRestrictedWeilZeroFormOperator_comp_rankOne_re, heq] at hge
    have hnorm : 0 < ‖ccmArchimedeanFormToAperture a u‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hu)
    by_contra hneg
    push Not at hneg
    linarith only [hge, mul_neg_of_neg_of_pos hneg hnorm]

/-- Whenever `ccmRestrictedWeilZeroFormOperator a` is positive, every bounded operator sandwich
`Ψ† ∘L ccmRestrictedWeilZeroFormOperator a ∘L Ψ` is positive with nonnegative real trace. -/
theorem isPositive_sandwich_of_isPositive_ccmRestrictedWeilZeroFormOperator
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {a : SuzukiPositiveAperture}
    (hpos : ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator a))
    (Ψ : K →L[ℂ] CCMArchimedeanFormDomain a) :
    ContinuousLinearMap.IsPositive
      (ContinuousLinearMap.adjoint Ψ ∘L ccmRestrictedWeilZeroFormOperator a ∘L Ψ) ∧
    0 ≤ (ContinuousLinearMap.opTrace
      (ContinuousLinearMap.adjoint Ψ ∘L ccmRestrictedWeilZeroFormOperator a ∘L Ψ)).re :=
  ⟨isPositive_adjoint_comp_comp hpos Ψ, opTrace_adjoint_comp_comp_re_nonneg hpos Ψ⟩

/-- **Global `RH` operator-positivity equivalence:** `RiemannHypothesis` holds iff
`ccmRestrictedWeilZeroFormOperator a` is positive at every positive aperture `a`. -/
theorem riemannHypothesis_iff_forall_isPositive_ccmRestrictedWeilZeroFormOperator :
    RiemannHypothesis ↔
      ∀ a : SuzukiPositiveAperture,
        ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator a) := by
  rw [riemannHypothesis_iff_forall_ccmRestrictedWeilGroundEnergy_nonneg]
  exact forall_congr' fun a =>
    (isPositive_ccmRestrictedWeilZeroFormOperator_iff_groundEnergy_nonneg a).symm

/-! ## 3. Unconditional operator-trace positivity past `½ log 2` (`a ≤ 181 / 500`) and corollaries -/

theorem threeHundredSixtyTwoThousandths_lt_half_log_three :
    (181 / 500 : ℝ) < Real.log 3 / 2 := by
  have hexp : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog : 1 < Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hexp
  linarith

/-- **Unconditional positivity of `ccmRestrictedWeilZeroFormOperator a` past `½ log 2`:**
for every `0 < a ≤ 181 / 500 = 0.362` (strictly past `½ log 2 ≈ 0.34657`), the intrinsic zero-form
operator is unconditionally `IsPositive`. -/
theorem isPositive_ccmRestrictedWeilZeroFormOperator_of_le_threeHundredSixtyTwoThousandths
    {a : SuzukiPositiveAperture} (ha : a.1 ≤ 181 / 500) :
    ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator a) :=
  (isPositive_ccmRestrictedWeilZeroFormOperator_iff_groundEnergy_nonneg a).mpr
    (le_trans (by norm_num)
      (one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeHundredSixtyTwoThousandths ha))

/-- At the prime-free threshold `halfLogTwoAperture` (`½ log 2`), the intrinsic zero-form operator
is unconditionally positive. -/
theorem isPositive_ccmRestrictedWeilZeroFormOperator_halfLogTwo :
    ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator halfLogTwoAperture) :=
  isPositive_ccmRestrictedWeilZeroFormOperator_of_le_threeHundredSixtyTwoThousandths
    GaloisForLFunctions.SelectivePositivityAndThresholdLaws.half_log_two_lt_threeHundredSixtyTwoThousandths.le

/-- **Quantitative coercive operator-trace floor past `½ log 2`:**
for all `0 < a ≤ 181 / 500` and `u : CCMArchimedeanFormDomain a`,
`(1 / 5000) ‖J_a u‖² ≤ Re Tr((1 - K_a(0)) ∘L |u⟩⟨u|)`. -/
theorem one_div_5000_mul_norm_sq_le_opTrace_ccmRestrictedWeilZeroFormOperator
    {a : SuzukiPositiveAperture} (ha : a.1 ≤ 181 / 500) (u : CCMArchimedeanFormDomain a) :
    (1 / 5000 : ℝ) * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      (ContinuousLinearMap.opTrace
        (ccmRestrictedWeilZeroFormOperator a ∘L InnerProductSpace.rankOne ℂ u u)).re := by
  rw [opTrace_ccmRestrictedWeilZeroFormOperator_comp_rankOne_re]
  exact le_trans
    (mul_le_mul_of_nonneg_right
      (one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeHundredSixtyTwoThousandths ha)
      (sq_nonneg _))
    (ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a u)

/-- Quantitative ground-energy floor at `½ log 2` for `primeFreeFamily` and through `181 / 500` for
the `{∞, 2}` semilocal family `primeSingleSemilocalFamily 2`. -/
theorem one_div_5000_le_primeFreeFamily_energy_halfLogTwo :
    (1 / 5000 : ℝ) ≤ primeFreeFamily.energy halfLogTwoAperture := by
  rw [primeFreeFamily_energy_halfLogTwo]
  exact one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeHundredSixtyTwoThousandths
    GaloisForLFunctions.SelectivePositivityAndThresholdLaws.half_log_two_lt_threeHundredSixtyTwoThousandths.le

theorem one_div_5000_le_primeTwoSemilocal_energy_of_le_threeHundredSixtyTwoThousandths
    {a : SuzukiPositiveAperture} (ha : a.1 ≤ 181 / 500) :
    (1 / 5000 : ℝ) ≤ (primeSingleSemilocalFamily 2).energy a := by
  rw [primeSingleSemilocalFamily_two_energy_eq_literal_of_le_halfLogThree
    (ha.trans threeHundredSixtyTwoThousandths_lt_half_log_three.le)]
  exact one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeHundredSixtyTwoThousandths ha

theorem threeHundredSixtyTwoThousandths_mem_groundEnergyNonnegApertures :
    (181 / 500 : ℝ) ∈ groundEnergyNonnegApertures :=
  ⟨by norm_num, le_trans (by norm_num)
    (one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeHundredSixtyTwoThousandths
      (A := ⟨181 / 500, by norm_num⟩) le_rfl)⟩

theorem threeHundredSixtyTwoThousandths_mem_windowPositiveApertures :
    (181 / 500 : ℝ) ∈ windowPositiveApertures :=
  ⟨by norm_num, fun F hF hFc hv =>
    le_trans (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
      (fullZeroForm_ge_of_support_le_threeHundredSixtyTwoThousandths hF hFc hv)⟩

/-- **Upgraded contact-aperture lower bound past the first prime (`181 / 500 ≤ zetaContactAperture`):**
off `RH`, the contact aperture of the ground-energy path is at least `181 / 500 = 0.362`, strictly
above `½ log 2` (upgrading `threeTenths_le_zetaContactAperture`). -/
theorem threeHundredSixtyTwoThousandths_le_zetaContactAperture (hRH : ¬ RiemannHypothesis) :
    (181 / 500 : ℝ) ≤ zetaContactAperture :=
  le_csSup (bddAbove_groundEnergyNonnegApertures_of_not_riemannHypothesis hRH)
    threeHundredSixtyTwoThousandths_mem_groundEnergyNonnegApertures

theorem half_log_two_lt_zetaContactAperture (hRH : ¬ RiemannHypothesis) :
    Real.log 2 / 2 < zetaContactAperture :=
  lt_of_lt_of_le
    GaloisForLFunctions.SelectivePositivityAndThresholdLaws.half_log_two_lt_threeHundredSixtyTwoThousandths
    (threeHundredSixtyTwoThousandths_le_zetaContactAperture hRH)

/-- **All-profile coercive Weil positivity on `realTestsAt a` past the first prime (`a ≤ 181 / 500`),**
upgrading `weilPair_ge_of_mem_realTestsAt` from `3 / 10` to `181 / 500 > ½ log 2`. -/
theorem weilPair_ge_of_mem_realTestsAt_threeHundredSixtyTwoThousandths
    {a : ℝ} (ha : a ≤ 181 / 500) (f : realTestsAt a) :
    1 / 5000 * ∫ u, (f.1 : ℝ → ℝ) u ^ 2 ≤ weilPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ) := by
  rw [weilPair_self_eq_zeta_W_re f.1.2.1 f.1.2.2, ← integral_norm_cx_sq]
  refine zetaZeroConfig_re_W_ge_of_aperture_le_threeHundredSixtyTwoThousandths
    (cx_contDiff f.1.2.1) ?_
  refine (closure_mono ?_).trans (f.2.trans (Icc_subset_Icc (by linarith) ha))
  intro u hu
  simp only [Function.mem_support, cx, ne_eq, Complex.ofReal_eq_zero] at hu ⊢
  exact hu

/-- **Unconditional all-profile Castelnuovo–Severi Hodge index and coupled effectivity past the
first prime (`a ≤ 181 / 500`),** upgrading `scalingSubsurface_all_hodgeIndex` from `3 / 10`. -/
theorem scalingSubsurface_all_hodgeIndex_of_le_threeHundredSixtyTwoThousandths
    {a : ℝ} (ha : a ≤ 181 / 500) :
    (scalingSubsurface (realTestsAt a)).HodgeIndex ∧
    (scalingSubsurface (realTestsAt a)).RiemannRochAxiom
      (coupledArithmeticCone (realTestsAt a)) ∧
    (scalingSubsurface (realTestsAt a)).AmpleAxiom
      (coupledArithmeticCone (realTestsAt a)) ∧
    (∀ x ∈ coupledArithmeticCone (realTestsAt a),
      ∀ y ∈ coupledArithmeticCone (realTestsAt a),
        0 ≤ (scalingSubsurface (realTestsAt a)).pair x y) := by
  have hpos : ∀ f : realTestsAt a, 0 ≤ weilPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ) := fun f =>
    le_trans (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
      (weilPair_ge_of_mem_realTestsAt_threeHundredSixtyTwoThousandths ha f)
  exact ⟨scalingSubsurface_hodgeIndex_of_weilPair_nonneg (realTestsAt a) hpos,
    coupledArithmeticCone_effectivity_of_weilPair_nonneg (realTestsAt a) hpos⟩

/-- **Unconditional all-profile Künneth effectivity past the first prime (`a ≤ 181 / 500`),**
upgrading `kunneth_effectivity_realTestsAt` from `3 / 10` past `½ log 2` without any ample
orthogonality constraint. -/
theorem kunneth_effectivity_realTestsAt_of_le_threeHundredSixtyTwoThousandths
    {a : ℝ} (ha : a ≤ 181 / 500) :
    RiemannInequality (scalingSubsurface (realTestsAt a)) 0 0
        (kunnethH0 (scalingSubsurface (realTestsAt a))) ∧
      DegreeBounded (scalingSubsurface (realTestsAt a))
        (kunnethH0 (scalingSubsurface (realTestsAt a))) :=
  (kunneth_effectivity_iff _).mpr
    (scalingSubsurface_all_hodgeIndex_of_le_threeHundredSixtyTwoThousandths ha).1

/-- **Unconditional all-profile source-determinantal arithmetic Riemann–Roch past the first prime
(`a ≤ 181 / 500`, `0 < c ≤ 1 / 5000`),** upgrading
`l2SourceCone_realTestsAt_riemannRoch_of_le_three_tenths` past `½ log 2`. -/
theorem l2SourceCone_realTestsAt_riemannRoch_of_le_threeHundredSixtyTwoThousandths
    {a c : ℝ} (ha : a ≤ 181 / 500) (hc0 : 0 < c) (hc : c ≤ 1 / 5000) :
    (scalingSubsurface (realTestsAt a)).RiemannRochAxiom (l2SourceCone c (realTestsAt a)) ∧
      (scalingSubsurface (realTestsAt a)).AmpleAxiom (l2SourceCone c (realTestsAt a)) ∧
      (scalingSubsurface (realTestsAt a)).SurfaceRiemannRochAxiom 0 0
        (l2SourceCone c (realTestsAt a)) := by
  let V := realTestsAt a
  let S := scalingSubsurface V
  have hle : ∀ x : ℝ × ℝ × V, l2SourceEnergy c V x ≤ S.defect x x := by
    intro x
    rw [scalingSubsurface_defect_self, l2SourceEnergy]
    have h1 := weilPair_ge_of_mem_realTestsAt_threeHundredSixtyTwoThousandths ha x.2.2
    have h2 : c * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 ≤ (1 / 5000 : ℝ) * ∫ u : ℝ, (x.2.2.1.1 u) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (integral_nonneg fun _ => sq_nonneg _)
    exact h2.trans h1
  exact ⟨S.sourceCone_riemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle,
    l2SourceCone_ample hc0 V,
    S.sourceCone_surfaceRiemannRoch_of_le_defect (l2SourceEnergy_neg c V)
      (l2SourceEnergy_nonneg hc0.le V) hle⟩

/-! ## 4. Exact equivalences at `½ log 3` (`halfLogThreeAperture`) and complete Q6 synthesis -/

/-- Exact equivalence at every aperture `A` between `ZetaWindowPositive A` and `weilPair ≥ 0` on
`realTestsAt A`. -/
theorem zetaWindowPositive_iff_realTestsAt_weilPair_nonneg (A : ℝ) :
    ZetaWindowPositive A ↔ ∀ f : realTestsAt A, 0 ≤ weilPair (f.1 : ℝ → ℝ) (f.1 : ℝ → ℝ) := by
  constructor
  · intro hW f
    rw [weilPair_self_eq_fullZeroForm f.1.2.1 f.1.2.2]
    refine hW (f.1 : ℝ → ℝ) f.1.2.1 f.1.2.2 fun x hx => ?_
    by_contra hne
    have hmem : x ∈ Icc (-A) A :=
      f.2 (subset_tsupport (f.1 : ℝ → ℝ) (Function.mem_support.mpr hne))
    have habs := abs_le.mpr hmem
    linarith
  · intro hV F hF hFc hsupp
    let f : realTestsAt A :=
      ⟨⟨F, hF, hFc⟩, closure_minimal
        (fun x hx => abs_le.mp (not_lt.mp fun hlt => hx (hsupp x hlt))) isClosed_Icc⟩
    have hf := hV f
    rwa [show (f.1 : ℝ → ℝ) = F from rfl, weilPair_self_eq_fullZeroForm hF hFc] at hf

theorem zetaWindowPositive_iff_scalingSubsurface_hodgeIndex (A : ℝ) :
    ZetaWindowPositive A ↔ (scalingSubsurface (realTestsAt A)).HodgeIndex :=
  (zetaWindowPositive_iff_realTestsAt_weilPair_nonneg A).trans
    (scalingSubsurface_hodgeIndex_iff_weilPair_nonneg (realTestsAt A)).symm

theorem zetaWindowPositive_iff_kunneth_effectivity (A : ℝ) :
    ZetaWindowPositive A ↔
      (RiemannInequality (scalingSubsurface (realTestsAt A)) 0 0
          (kunnethH0 (scalingSubsurface (realTestsAt A))) ∧
        DegreeBounded (scalingSubsurface (realTestsAt A))
          (kunnethH0 (scalingSubsurface (realTestsAt A)))) :=
  (zetaWindowPositive_iff_realTestsAt_weilPair_nonneg A).trans
    (kunneth_effectivity_scalingSubsurface_iff (realTestsAt A)).symm

/-- **Exact `½ log 3` operator-positivity equivalence:**
positivity of the intrinsic operator `ccmRestrictedWeilZeroFormOperator halfLogThreeAperture` is
equivalent to nonnegativity of the `{∞, 2}` semilocal ground energy at `halfLogThreeAperture`, and
to window positivity on every open sub-aperture `0 < B < ½ log 3`. -/
theorem isPositive_ccmRestrictedWeilZeroFormOperator_halfLogThree_iff_semilocal_energy :
    ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator halfLogThreeAperture) ↔
      0 ≤ (primeSingleSemilocalFamily 2).energy halfLogThreeAperture := by
  rw [isPositive_ccmRestrictedWeilZeroFormOperator_iff_groundEnergy_nonneg,
    primeSingleSemilocalFamily_two_energy_halfLogThree]

theorem isPositive_ccmRestrictedWeilZeroFormOperator_halfLogThree_iff_forall_lt_window :
    ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator halfLogThreeAperture) ↔
      ∀ B : ℝ, 0 < B → B < Real.log 3 / 2 → ZetaWindowPositive B := by
  rw [isPositive_ccmRestrictedWeilZeroFormOperator_iff_groundEnergy_nonneg,
    ccmRestrictedWeilGroundEnergy_nonneg_iff_forall_lt_zetaWindowPositive]
  rfl

/-- **Corollaries of intrinsic operator positivity at `½ log 3`:**
if `ccmRestrictedWeilZeroFormOperator halfLogThreeAperture` is positive, then:
1. every smaller aperture `b < ½ log 3` has strictly positive ground energy `0 < μ(b)` and positive
   intrinsic zero-form operator;
2. every `0 < B < ½ log 3` satisfies `ZetaWindowPositive B`, all-profile `HodgeIndex`, and Künneth
   effectivity on `scalingSubsurface (realTestsAt B)`;
3. off `RH`, `½ log 3 ≤ zetaContactAperture`. -/
theorem corollaries_of_isPositive_ccmRestrictedWeilZeroFormOperator_halfLogThree
    (hpos : ContinuousLinearMap.IsPositive
      (ccmRestrictedWeilZeroFormOperator halfLogThreeAperture)) :
    (∀ b : SuzukiPositiveAperture, b.1 < Real.log 3 / 2 →
      0 < ccmRestrictedWeilGroundEnergy b ∧
        ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator b)) ∧
    (∀ B : ℝ, 0 < B → B < Real.log 3 / 2 →
      ZetaWindowPositive B ∧
        (scalingSubsurface (realTestsAt B)).HodgeIndex ∧
        (RiemannInequality (scalingSubsurface (realTestsAt B)) 0 0
            (kunnethH0 (scalingSubsurface (realTestsAt B))) ∧
          DegreeBounded (scalingSubsurface (realTestsAt B))
            (kunnethH0 (scalingSubsurface (realTestsAt B))))) ∧
    (¬ RiemannHypothesis → Real.log 3 / 2 ≤ zetaContactAperture) := by
  have hμ0 : 0 ≤ ccmRestrictedWeilGroundEnergy halfLogThreeAperture :=
    (isPositive_ccmRestrictedWeilZeroFormOperator_iff_groundEnergy_nonneg
      halfLogThreeAperture).mp hpos
  have hmem : Real.log 3 / 2 ∈ groundEnergyNonnegApertures :=
    ⟨halfLogThreeAperture.2, hμ0⟩
  refine ⟨fun b hb => ?_, fun B hB0 hBlt => ?_, fun hRH =>
    le_csSup (bddAbove_groundEnergyNonnegApertures_of_not_riemannHypothesis hRH) hmem⟩
  · have hlt : b < halfLogThreeAperture := hb
    have hstrict : 0 < ccmRestrictedWeilGroundEnergy b :=
      lt_of_le_of_lt hμ0 (strictAnti_ccmRestrictedWeilGroundEnergy hlt)
    exact ⟨hstrict,
      (isPositive_ccmRestrictedWeilZeroFormOperator_iff_groundEnergy_nonneg b).mpr hstrict.le⟩
  · have hW : ZetaWindowPositive B :=
      (Ioo_subset_windowPositiveApertures hmem ⟨hB0, hBlt⟩).2
    exact ⟨hW, (zetaWindowPositive_iff_scalingSubsurface_hodgeIndex B).mp hW,
      (zetaWindowPositive_iff_kunneth_effectivity B).mp hW⟩

/-- Closed-window converse at `½ log 3`: `ZetaWindowPositive (Real.log 3 / 2)` implies positivity of
`ccmRestrictedWeilZeroFormOperator halfLogThreeAperture`, nonnegativity of the `{∞, 2}` semilocal
ground energy at `halfLogThreeAperture`, and Hodge index + Künneth effectivity at `½ log 3`. -/
theorem isPositive_ccmRestrictedWeilZeroFormOperator_halfLogThree_of_zetaWindowPositive
    (hW : ZetaWindowPositive (Real.log 3 / 2)) :
    ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator halfLogThreeAperture) ∧
      0 ≤ (primeSingleSemilocalFamily 2).energy halfLogThreeAperture ∧
      (scalingSubsurface (realTestsAt (Real.log 3 / 2))).HodgeIndex ∧
      (RiemannInequality (scalingSubsurface (realTestsAt (Real.log 3 / 2))) 0 0
          (kunnethH0 (scalingSubsurface (realTestsAt (Real.log 3 / 2)))) ∧
        DegreeBounded (scalingSubsurface (realTestsAt (Real.log 3 / 2)))
          (kunnethH0 (scalingSubsurface (realTestsAt (Real.log 3 / 2))))) := by
  have hμ : 0 ≤ ccmRestrictedWeilGroundEnergy halfLogThreeAperture :=
    ccmRestrictedWeilGroundEnergy_nonneg_of_zetaWindowPositive halfLogThreeAperture hW
  have hpos : ContinuousLinearMap.IsPositive
      (ccmRestrictedWeilZeroFormOperator halfLogThreeAperture) :=
    (isPositive_ccmRestrictedWeilZeroFormOperator_iff_groundEnergy_nonneg
      halfLogThreeAperture).mpr hμ
  exact ⟨hpos,
    isPositive_ccmRestrictedWeilZeroFormOperator_halfLogThree_iff_semilocal_energy.mp hpos,
    (zetaWindowPositive_iff_scalingSubsurface_hodgeIndex (Real.log 3 / 2)).mp hW,
    (zetaWindowPositive_iff_kunneth_effectivity (Real.log 3 / 2)).mp hW⟩

/-- **Complete unconditional resolution of Question Q6 (`fable.md` §2.2 & §7):**
1. *Positive `2`-adic logarithmic trace & `{∞, 2}` trace identity through `½ log 3`:*
   `primeTwoLogOperator m` is positive and trace-class on `ValuationShellL2` with exact trace
   `m * log 2`, and on the entire closed window `0 < a ≤ ½ log 3` the literal all-prime restricted
   Weil form coincides with `(primeSingleSemilocalFamily 2).Q a` and decomposes into the exact
   `{∞, 2}` operator-trace identity.
2. *Operator-theoretic obstructions killing `{∞, 2}` positive-operator / tensor positivity:*
   the unglued archimedean Sonin operator `ccmSoninGenericPartAt 1` is not positive; neither sign of
   `ccmFinitePrimeOperator a` is positive on `(½ log 2, ½ log 3]`; no scalar or positive-degree
   homogeneous multiplicative tensor factorization over `primeFreeFamily.Q a` exists on
   `(½ log 2, ½ log 3]`; and `(primeSingleSemilocalFamily 2).energy` crosses zero unconditionally
   and admits **no** positive operator-trace carrier across apertures.
3. *Intrinsic positive-operator trace rewriting & certified positivity past `½ log 2`:*
   `ccmRestrictedWeilSourceQuadratic a u = Re Tr((1 - K_a(0)) ∘L |u⟩⟨u|)`, where operator positivity
   of `ccmRestrictedWeilZeroFormOperator a` is equivalent to nonnegativity of that trace for all `u`
   (holding unconditionally for all `0 < a ≤ 181 / 500`, strictly past `½ log 2`, and at
   `halfLogThreeAperture` equivalent to `0 ≤ (primeSingleSemilocalFamily 2).energy halfLogThreeAperture`). -/
theorem question_Q6_complete_resolution :
    (∀ m : ℕ, ContinuousLinearMap.IsPositive (primeTwoLogOperator m) ∧
      ContinuousLinearMap.IsTraceClass (primeTwoLogOperator m) ∧
      ContinuousLinearMap.opTrace (primeTwoLogOperator m) = (m : ℂ) * (Real.log 2 : ℂ)) ∧
    (∀ (a : SuzukiPositiveAperture), a.1 ≤ Real.log 3 / 2 →
      (primeSingleSemilocalFamily 2).energy a = ccmRestrictedWeilGroundEnergy a ∧
      ∀ u : CCMArchimedeanFormDomain a,
        (primeSingleSemilocalFamily 2).Q a u = ccmRestrictedWeilSourceQuadratic a u ∧
        ccmRestrictedWeilSourceQuadratic a u =
          archPart a u +
            (ContinuousLinearMap.opTrace (ccmPolarOperator a ∘L
              InnerProductSpace.rankOne ℂ (ccmArchimedeanFormToAperture a u)
                (ccmArchimedeanFormToAperture a u))).re -
            (soninSemilocalLogPrimePowerCoefficient (twoPrime, 0) *
              ContinuousLinearMap.opTrace (primeTwoLogOperator 1) *
              ContinuousLinearMap.opTrace
                (ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log 2)) ∘L
                  InnerProductSpace.rankOne ℂ (ccmArchimedeanFormToAperture a u)
                    (ccmArchimedeanFormToAperture a u))).re) ∧
    ¬ ContinuousLinearMap.IsPositive (ccmSoninGenericPartAt 1) ∧
    (∀ (a : SuzukiPositiveAperture), Real.log 2 / 2 < a.1 → a.1 ≤ Real.log 3 / 2 →
      ¬ ContinuousLinearMap.IsPositive (ccmFinitePrimeOperator a) ∧
      ¬ ContinuousLinearMap.IsPositive (-ccmFinitePrimeOperator a)) ∧
    (∃ a : SuzukiPositiveAperture, (primeSingleSemilocalFamily 2).energy a = 0 ∧
      ∃ x : ((primeSingleSemilocalFamily 2).operator a).domain,
        (x : suzukiApertureHilbert a) ≠ 0 ∧ (primeSingleSemilocalFamily 2).operator a x = 0) ∧
    (¬ ∃ R : ∀ a : SuzukiPositiveAperture, CCMArchimedeanFormDomain a →
        (ValuationShellL2 →L[ℂ] ValuationShellL2),
      (∀ a u, ContinuousLinearMap.IsPositive (R a u)) ∧
      (∀ a u, (ContinuousLinearMap.opTrace (R a u)).re = (primeSingleSemilocalFamily 2).Q a u)) ∧
    (∀ (a : SuzukiPositiveAperture),
      (∀ u : CCMArchimedeanFormDomain a,
        (ContinuousLinearMap.opTrace
          (ccmRestrictedWeilZeroFormOperator a ∘L InnerProductSpace.rankOne ℂ u u)).re =
            ccmRestrictedWeilSourceQuadratic a u) ∧
      (ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator a) ↔
        ∀ u : CCMArchimedeanFormDomain a,
          0 ≤ (ContinuousLinearMap.opTrace
            (ccmRestrictedWeilZeroFormOperator a ∘L InnerProductSpace.rankOne ℂ u u)).re)) ∧
    (∀ (a : SuzukiPositiveAperture), a.1 ≤ 181 / 500 →
      ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator a)) ∧
    (ContinuousLinearMap.IsPositive (ccmRestrictedWeilZeroFormOperator halfLogThreeAperture) ↔
      0 ≤ (primeSingleSemilocalFamily 2).energy halfLogThreeAperture) :=
  ⟨fun m => ⟨primeTwoLogOperator_isPositive m, primeTwoLogOperator_isTraceClass m,
      opTrace_primeTwoLogOperator m⟩,
   fun _ ha => ⟨primeSingleSemilocalFamily_two_energy_eq_literal_of_le_halfLogThree ha,
      fun u => ⟨primeSingleSemilocalFamily_two_Q_eq_literal_of_le_halfLogThree ha u,
        ccmRestrictedWeilSourceQuadratic_eq_semilocalPrimeTwoTrace_of_le_halfLogThree ha u⟩⟩,
   not_isPositive_ccmSoninGenericPartAt_one,
   fun _ ha2 ha3 => neither_sign_isPositive_ccmFinitePrimeOperator_primeTwo_window ha2 ha3,
   exists_primeTwoSemilocal_zero_crossing,
   no_positive_operator_trace_carrier_for_primeTwoSemilocal,
   fun a => ⟨opTrace_ccmRestrictedWeilZeroFormOperator_comp_rankOne_re a,
      isPositive_ccmRestrictedWeilZeroFormOperator_iff_opTrace_nonneg a⟩,
   fun _ ha => isPositive_ccmRestrictedWeilZeroFormOperator_of_le_threeHundredSixtyTwoThousandths ha,
   isPositive_ccmRestrictedWeilZeroFormOperator_halfLogThree_iff_semilocal_energy⟩

end GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace

end
