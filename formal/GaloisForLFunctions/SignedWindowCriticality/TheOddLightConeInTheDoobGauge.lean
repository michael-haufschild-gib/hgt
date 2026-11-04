import GaloisForLFunctions.ArithmeticCriticalityTheory.EvenGaugeFoldedConductance
import GaloisForLFunctions.SignedWindowCriticality.TheLightConeOfACollarCarriesItsReflection
import GaloisForLFunctions.RHTower.WeilPhiDoobReflectedKillingPotentialAndDisjointSupportDiagonal

/-!
# The odd light cone in the Doob gauge

For an odd gauge, `M = Φω` odd and nonnegative on `(0, ∞)`, and an even profile `u`, the jumps of
`J_M(u)` fold onto the positive quadrant. A same-side pair `(x, x + s)`, `x, s > 0`, carries
`J_s(x) = M(x)M(x + s)(u(x) − u(x + s))² ≥ 0`; the crossing pair `(−x, x + s)` of length `s + 2x`
carries the same squared jump with the weight `M(−x)M(x + s) = −M(x)M(x + s)`.

* **Per-shift split** (`integral_signedShiftJump_eq_split_of_odd`). For every shift `t > 0`,
  `∫_ℝ J_t = 2∫_{x>0} J_t(x) − ∫_0^t M(x)M(t − x)(u(x) − u(t − x))²dx`: twice the same-side jumps
  minus the anti-diagonal ones. At `t = log n` this splits each prime term of `J_M` into its
  same-side and anti-diagonal parts.
* **The odd fold** (`integral_arch_mul_gaugeJumpProfile_eq_fold_of_odd`). The archimedean part is
  `∫_0^∞ ω(t)I(t)dt = 2∫_{x>0}∫_{s>0} (ω(s) − ω(s + 2x)) J_s(x) ds dx`.
* **The odd light cone is nonnegative** (`integral_arch_mul_gaugeJumpProfile_nonneg_of_odd`).
  Since `ω` decreases, the archimedean part of `J_M` is a nonnegative form on even profiles for
  every odd gauge positive on the half-line: its folded conductance `ω(s) − ω(s + 2x)` is positive.

This is the general-gauge form of the odd light cone `κ(|x − y|) − κ(x + y) > 0` of ACT, which ACT
proves for shifted ground states; the even-gauge fold, with conductance `κ(s) + κ(s + 2x)`, is ACT's
`integral_kappa_mul_gaugeJumpProfile_eq_fold_sum`, and the odd case is reduced to it through `|M|`.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticIncidencePositivity

variable {M u : ℝ → ℝ}

theorem signedShiftJump_reflect_of_odd (hMo : ∀ x, M (-x) = -M x) (hue : ∀ x, u (-x) = u x)
    (t x : ℝ) : signedShiftJump M u t (-x - t) = signedShiftJump M u t x := by
  unfold signedShiftJump
  rw [show -x - t + t = -x by ring, show -x - t = -(x + t) by ring, hMo, hMo, hue, hue]
  ring

/-- The crossing jump `(−a, t − a)` of an odd gauge is minus the anti-diagonal jump. -/
theorem signedShiftJump_neg_of_odd (hMo : ∀ x, M (-x) = -M x) (hue : ∀ x, u (-x) = u x)
    (t a : ℝ) : signedShiftJump M u t (-a) = -crossingDiffJump M u t a := by
  unfold signedShiftJump crossingDiffJump
  rw [show -a + t = t - a by ring, hMo, hue]
  ring

/-- **Per-shift split of an odd gauge.** -/
theorem integral_signedShiftJump_eq_split_of_odd {B : ℝ} (hMc : Continuous M)
    (huc : Continuous u) (hMo : ∀ x, M (-x) = -M x) (hue : ∀ x, u (-x) = u x)
    (hMB : ∀ x, B ≤ |x| → M x = 0) {t : ℝ} (ht : 0 < t) :
    (∫ x, signedShiftJump M u t x) =
      2 * (∫ x in Ioi (0 : ℝ), signedShiftJump M u t x) -
        ∫ x in Ioo (0 : ℝ) t, crossingDiffJump M u t x := by
  set g := fun x => signedShiftJump M u t x with hgdef
  have hg : Integrable g := integrable_signedShiftJump hMc huc hMB t
  have h1 : (∫ x, g x) = (∫ x in Ioi (0 : ℝ), g x) + ∫ x in Iic (0 : ℝ), g x := by
    rw [← integral_add_compl measurableSet_Ioi hg, compl_Ioi]
  have h2 : (∫ x in Iic (0 : ℝ), g x) =
      (∫ x in Iic (-t), g x) + ∫ x in Ioc (-t) 0, g x := by
    rw [← setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hg.integrableOn
      hg.integrableOn, Iic_union_Ioc_eq_Iic (by linarith)]
  have h3 : (∫ x in Iic (-t), g x) = ∫ x in Ioi (0 : ℝ), g x := by
    have e3 := integral_comp_neg_Iic (-t) (fun y => g (y - t))
    simp only [neg_neg] at e3
    have e : (∫ x in Iic (-t), g x) = ∫ x in Iic (-t), g (-x - t) :=
      setIntegral_congr_fun measurableSet_Iic fun x _ => by
        simp only [hgdef]
        rw [signedShiftJump_reflect_of_odd hMo hue]
    rw [e, e3, setIntegral_Ioi_translate]
    simp only [add_sub_cancel_right]
  have h4 : (∫ x in Ioc (-t) 0, g x) = -∫ x in Ioo (0 : ℝ) t, crossingDiffJump M u t x := by
    rw [← integral_indicator measurableSet_Ioc,
      ← integral_neg_eq_self (fun x => (Ioc (-t) 0).indicator g x)]
    have e : (fun x => (Ioc (-t) 0).indicator g (-x)) =
        (Ico (0 : ℝ) t).indicator fun x => -crossingDiffJump M u t x := by
      funext x
      by_cases hx : x ∈ Ico (0 : ℝ) t
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show -x ∈ Ioc (-t) 0 from
          ⟨by linarith [hx.2], by linarith [hx.1]⟩)]
        exact signedShiftJump_neg_of_odd hMo hue t x
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx
          ⟨by linarith [h.2], by linarith [h.1]⟩)]
    rw [e, integral_indicator measurableSet_Ico, integral_neg, integral_Ico_eq_integral_Ioo]
  rw [h1, h2, h3, h4]
  ring

section OddFold

variable {B K : ℝ} (hMc : Continuous M) (huc : Continuous u)
  (hMo : ∀ x, M (-x) = -M x) (hue : ∀ x, u (-x) = u x) (hMpos : ∀ x, 0 ≤ x → 0 ≤ M x)
  (hM1 : ∀ x, |M x| ≤ 1) (hMB : ∀ x, B ≤ |x| → M x = 0)
  (huL : ∀ a b, |u a - u b| ≤ K * |a - b|) (hB0 : 0 < B)

/-- The archimedean density is `O(1/t)` near `0`. -/
theorem abs_archLevyDensity_le {B t : ℝ} (ht : 0 < t) (htB : t ≤ 2 * B) :
    |_root_.RHTower.archLevyDensity t| ≤ (1 + 4 * B) / 2 / t := by
  rw [abs_of_pos (_root_.RHTower.archLevyDensity_pos ht), le_div_iff₀ ht]
  have := archLevyDensity_mul_le ht
  linarith

include hMc hMo hMB in
/-- The even companion `|M|` of an odd gauge. -/
theorem absGauge_props :
    Continuous (fun x => |M x|) ∧ (∀ x, |M (-x)| = |M x|) ∧
      (∀ x, B ≤ |x| → |M x| = 0) := by
  refine ⟨hMc.abs, fun x => by rw [hMo, abs_neg], fun x hx => by rw [hMB x hx, abs_zero]⟩

include hMpos in
theorem signedShiftJump_abs_eq {s x : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) :
    signedShiftJump (fun y => |M y|) u s x = signedShiftJump M u s x := by
  unfold signedShiftJump
  beta_reduce
  rw [abs_of_nonneg (hMpos x hx), abs_of_nonneg (hMpos (x + s) (by linarith))]

include hMpos in
theorem crossingDiffJump_abs_eq {t x : ℝ} (hx : 0 ≤ x) (hxt : x ≤ t) :
    crossingDiffJump (fun y => |M y|) u t x = crossingDiffJump M u t x := by
  unfold crossingDiffJump
  beta_reduce
  rw [abs_of_nonneg (hMpos x hx), abs_of_nonneg (hMpos (t - x) (by linarith))]

include hMc huc hMo hue hMpos hM1 hMB huL hB0 in
/-- **The odd fold of the archimedean jump energy.** -/
theorem integral_arch_mul_gaugeJumpProfile_eq_fold_of_odd :
    (∫ t in Ioi (0 : ℝ), _root_.RHTower.archLevyDensity t * gaugeJumpProfile M u t) =
      2 * ((∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
          _root_.RHTower.archLevyDensity s * signedShiftJump M u s x) -
        ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
          _root_.RHTower.archLevyDensity (s + 2 * x) * signedShiftJump M u s x) := by
  set κ := _root_.RHTower.archLevyDensity
  set P : ℝ → ℝ := fun y => |M y|
  obtain ⟨hPc, hPe, hPB⟩ := absGauge_props hMc hMo hMB
  have hP0 : ∀ x, 0 ≤ P x := fun x => abs_nonneg _
  have hκm : Measurable κ := _root_.RHTower.measurable_archLevyDensity
  have hC : 0 ≤ (1 + 4 * B) / 2 := by linarith
  have hκ : ∀ t, 0 < t → t ≤ 2 * B → |κ t| ≤ (1 + 4 * B) / 2 / t :=
    fun t ht htB => abs_archLevyDensity_le ht htB
  have hIS := integrable_kappa_mul_signedShiftJump_prod hPc huc hP0 hM1 hPB huL hB0 hκm hC hκ
  have hID := integrable_foldedKappaCrossing hPc huc hP0 hM1 hPB huL hB0 hκm hC hκ
  -- the same-side and crossing profiles of `M` are those of `P`
  have hS : ∀ t ∈ Ioi (0 : ℝ), (∫ x in Ioi (0 : ℝ), signedShiftJump M u t x) =
      ∫ x in Ioi (0 : ℝ), signedShiftJump P u t x := fun t ht =>
    setIntegral_congr_fun measurableSet_Ioi fun x hx =>
      (signedShiftJump_abs_eq hMpos (le_of_lt hx) (le_of_lt ht)).symm
  have hD : ∀ t ∈ Ioi (0 : ℝ), (∫ x in Ioo (0 : ℝ) t, crossingDiffJump M u t x) =
      ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P u t x := fun t _ =>
    setIntegral_congr_fun measurableSet_Ioo fun x hx =>
      (crossingDiffJump_abs_eq hMpos hx.1.le hx.2.le).symm
  have hSi : IntegrableOn (fun t => κ t * ∫ x in Ioi (0 : ℝ), signedShiftJump P u t x) (Ioi 0) :=
    hIS.integral_prod_left.congr (Eventually.of_forall fun t => by
      simp only [Function.uncurry_apply_pair]
      rw [integral_const_mul])
  have hDi : IntegrableOn (fun t => κ t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P u t x)
      (Ioi 0) := by
    have h2 : IntegrableOn (fun t => 2 * ∫ x in Ioi (0 : ℝ), foldedKappaCrossing κ P u (t, x))
        (Ioi 0) := hID.integral_prod_left.const_mul 2
    refine h2.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := ht
    simp only
    simp_rw [foldedKappaCrossing_apply]
    rw [integral_const_mul, setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Ioi_self,
      integral_crossingDiffJump_eq_two_mul_half hPc huc ht0]
    ring
  have hsplit : ∀ t ∈ Ioi (0 : ℝ), κ t * gaugeJumpProfile M u t =
      2 * (κ t * ∫ x in Ioi (0 : ℝ), signedShiftJump P u t x) -
        κ t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P u t x := fun t ht => by
    unfold gaugeJumpProfile
    rw [integral_signedShiftJump_eq_split_of_odd hMc huc hMo hue hMB ht, hS t ht, hD t ht]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
    integral_sub (f := fun t => 2 * (κ t * ∫ x in Ioi (0 : ℝ), signedShiftJump P u t x))
      (g := fun t => κ t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P u t x) (hSi.const_mul 2) hDi,
    integral_const_mul, kappaSameEnergy_eq hPc huc hP0 hM1 hPB huL hB0 hκm hC hκ,
    kappaCrossingEnergy_eq hPc huc hP0 hM1 hPB huL hB0 hκm hC hκ]
  have hback : ∀ (k : ℝ → ℝ → ℝ),
      (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), k s x * signedShiftJump P u s x) =
        ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), k s x * signedShiftJump M u s x := fun k =>
    setIntegral_congr_fun measurableSet_Ioi fun x hx =>
      setIntegral_congr_fun measurableSet_Ioi fun s hs => by
        rw [signedShiftJump_abs_eq hMpos (le_of_lt hx) (le_of_lt hs)]
  rw [hback (fun s _ => κ s), hback (fun s x => κ (s + 2 * x))]
  ring

include hMc huc hMo hue hMpos hM1 hMB huL hB0 in
/-- **The odd light cone is nonnegative**: the archimedean part of `J_M` on an even profile is
`2∫_{x>0}∫_{s>0}(ω(s) − ω(s + 2x))J_s(x) ≥ 0` for every odd gauge positive on the half-line. -/
theorem integral_arch_mul_gaugeJumpProfile_nonneg_of_odd :
    0 ≤ ∫ t in Ioi (0 : ℝ), _root_.RHTower.archLevyDensity t * gaugeJumpProfile M u t := by
  set κ := _root_.RHTower.archLevyDensity
  set P : ℝ → ℝ := fun y => |M y|
  obtain ⟨hPc, hPe, hPB⟩ := absGauge_props hMc hMo hMB
  have hP0 : ∀ x, 0 ≤ P x := fun x => abs_nonneg _
  have hκm : Measurable κ := _root_.RHTower.measurable_archLevyDensity
  have hC : 0 ≤ (1 + 4 * B) / 2 := by linarith
  have hκ : ∀ t, 0 < t → t ≤ 2 * B → |κ t| ≤ (1 + 4 * B) / 2 / t :=
    fun t ht htB => abs_archLevyDensity_le ht htB
  have hIS := integrable_kappa_mul_signedShiftJump_prod hPc huc hP0 hM1 hPB huL hB0 hκm hC hκ
  have hID := integrable_foldedKappaCrossing hPc huc hP0 hM1 hPB huL hB0 hκm hC hκ
  rw [integral_arch_mul_gaugeJumpProfile_eq_fold_of_odd hMc huc hMo hue hMpos hM1 hMB huL hB0]
  have hback : ∀ (k : ℝ → ℝ → ℝ),
      (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), k s x * signedShiftJump M u s x) =
        ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), k s x * signedShiftJump P u s x := fun k =>
    setIntegral_congr_fun measurableSet_Ioi fun x hx =>
      setIntegral_congr_fun measurableSet_Ioi fun s hs => by
        rw [signedShiftJump_abs_eq hMpos (le_of_lt hx) (le_of_lt hs)]
  rw [hback (fun s _ => κ s), hback (fun s x => κ (s + 2 * x))]
  have hA : IntegrableOn (fun x => ∫ s in Ioi (0 : ℝ), κ s * signedShiftJump P u s x) (Ioi 0) :=
    hIS.integral_prod_right
  have hCr : IntegrableOn (fun x => ∫ s in Ioi (0 : ℝ), κ (s + 2 * x) * signedShiftJump P u s x)
      (Ioi 0) :=
    IntegrableOn.congr_fun hID.integral_prod_right
      (fun x hx => integral_foldedKappaCrossing_eq (mem_Ioi.mp hx)) measurableSet_Ioi
  rw [← integral_sub hA hCr]
  refine mul_nonneg zero_le_two (setIntegral_nonneg measurableSet_Ioi fun x hx => ?_)
  have hx0 : 0 < x := hx
  rw [← integral_sub (integrableOn_kappa_mul_signedShiftJump_section hPc huc hP0 hM1 hPB huL hB0
      hκm hC hκ hx0)
    (integrableOn_kappa_reflect_mul_signedShiftJump_section hPc huc hP0 hM1 hPB huL hB0 hκm hC
      hκ hx0)]
  refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  have hmono : κ (s + 2 * x) ≤ κ s :=
    (_root_.RHTower.strictAntiOn_archLevyDensity.antitoneOn) hs0 (by
      show (0 : ℝ) < s + 2 * x; linarith) (by linarith)
  have hJ := signedShiftJump_nonneg' hP0 (F := u) s x
  nlinarith

end OddFold

end GaloisForLFunctions.SignedWindowCriticality

end
