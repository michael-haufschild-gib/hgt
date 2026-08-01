import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Integrating a power tail over the outside of a band

A bound `K |ξ|^{-p}` with `p > 1` is integrable past any positive radius, and integrates over the
outside of a symmetric band to `2 K t^{1-p}/(p-1)`.  Both rays contribute equally, the left one by
reflection, since the bound is even.

This is what a supremum bound cannot do: control mass on an unbounded region.  A nonnegative
function dominated by such a tail therefore has small mass outside a large band, with an explicit
rate in the radius.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

/-- The outside of a symmetric band is a pair of rays. -/
theorem centralTail_eq_union (t : ℝ) : {η : ℝ | t ≤ |η|} = Iic (-t) ∪ Ici t := by
  ext η
  simp only [mem_setOf_eq, mem_union, mem_Iic, mem_Ici, le_abs]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (by linarith)
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl h

theorem measurableSet_centralTail (t : ℝ) : MeasurableSet {η : ℝ | t ≤ |η|} := by
  rw [centralTail_eq_union]
  exact measurableSet_Iic.union measurableSet_Ici

/-- The power tail is integrable on the right open ray. -/
theorem integrableOn_powerTail_Ioi {t p : ℝ} (ht : 0 < t) (hp : 1 < p) :
    IntegrableOn (fun ξ : ℝ => |ξ| ^ (-p)) (Ioi t) volume := by
  have hbase : IntegrableOn (fun ξ : ℝ => ξ ^ (-p)) (Ioi t) volume :=
    (integrableOn_Ioi_rpow_iff ht).mpr (by linarith)
  refine hbase.congr_fun (fun ξ hξ => ?_) measurableSet_Ioi
  rw [abs_of_pos (ht.trans hξ)]

theorem integrableOn_powerTail_Ici {t p : ℝ} (ht : 0 < t) (hp : 1 < p) :
    IntegrableOn (fun ξ : ℝ => |ξ| ^ (-p)) (Ici t) volume := by
  rw [IntegrableOn, ← Measure.restrict_congr_set Ioi_ae_eq_Ici]
  exact integrableOn_powerTail_Ioi ht hp

/-- Reflection carries the right ray's integrability to the left one. -/
theorem integrableOn_powerTail_Iic {t p : ℝ} (ht : 0 < t) (hp : 1 < p) :
    IntegrableOn (fun ξ : ℝ => |ξ| ^ (-p)) (Iic (-t)) volume := by
  have hIci := integrableOn_powerTail_Ici ht hp
  have hpre : (fun x : ℝ => -x) ⁻¹' (Iic (-t)) = Ici t := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_Ici]
    constructor <;> intro h <;> linarith
  have hiff := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (MeasurableEquiv.neg ℝ).measurableEmbedding (f := fun ξ : ℝ => |ξ| ^ (-p)) (s := Iic (-t))
  rw [hpre] at hiff
  refine hiff.mp ?_
  refine hIci.congr_fun (fun ξ _ => ?_) measurableSet_Ici
  simp [abs_neg]

/-- The power tail is integrable outside a symmetric band. -/
theorem integrableOn_powerTail {t p : ℝ} (ht : 0 < t) (hp : 1 < p) :
    IntegrableOn (fun ξ : ℝ => |ξ| ^ (-p)) {η : ℝ | t ≤ |η|} volume := by
  rw [centralTail_eq_union]
  exact (integrableOn_powerTail_Iic ht hp).union (integrableOn_powerTail_Ici ht hp)

/-- The power tail's integral on the right ray. -/
theorem integral_powerTail_Ioi {t p : ℝ} (ht : 0 < t) (hp : 1 < p) :
    ∫ ξ in Ioi t, |ξ| ^ (-p) = t ^ (1 - p) / (p - 1) := by
  have hcongr : ∫ ξ in Ioi t, |ξ| ^ (-p) = ∫ ξ in Ioi t, ξ ^ (-p) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
    rw [abs_of_pos (ht.trans hξ)]
  rw [hcongr, integral_Ioi_rpow_of_lt (by linarith : -p < -1) ht]
  have h1 : -p + 1 = 1 - p := by ring
  have hne₁ : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (by linarith)
  have hne₂ : p - (1 : ℝ) ≠ 0 := sub_ne_zero.mpr (by linarith)
  rw [h1]
  field_simp
  ring

/-- **The power-tail integral.**  Outside a symmetric band the tail integrates to twice the ray
value. -/
theorem integral_powerTail {t p : ℝ} (ht : 0 < t) (hp : 1 < p) :
    ∫ ξ in {η : ℝ | t ≤ |η|}, |ξ| ^ (-p) = 2 * (t ^ (1 - p) / (p - 1)) := by
  have hdisj : Disjoint (Iic (-t)) (Ici t) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : x ≤ -t := hx
    have h2 : t ≤ x := hx'
    linarith
  have hIicval : ∫ ξ in Iic (-t), |ξ| ^ (-p) = ∫ ξ in Ioi t, |ξ| ^ (-p) := by
    rw [← integral_comp_neg_Ioi t fun η : ℝ => |η| ^ (-p)]
    simp only [abs_neg]
  have hIcival : ∫ ξ in Ici t, |ξ| ^ (-p) = ∫ ξ in Ioi t, |ξ| ^ (-p) := by
    rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
  rw [centralTail_eq_union,
    setIntegral_union hdisj measurableSet_Ici (integrableOn_powerTail_Iic ht hp)
      (integrableOn_powerTail_Ici ht hp),
    hIicval, hIcival, integral_powerTail_Ioi ht hp]
  ring

/-- **Small mass outside a band.**  A nonnegative function dominated by a power tail has mass at
most `2 K t^{1-p}/(p-1)` outside the band of radius `t`. -/
theorem setIntegral_le_of_le_powerTail {f : ℝ → ℝ} {K t p : ℝ}
    (hnn : ∀ ξ : ℝ, 0 ≤ f ξ) (ht : 0 < t) (hp : 1 < p)
    (hbound : ∀ ξ : ℝ, t ≤ |ξ| → f ξ ≤ K * |ξ| ^ (-p)) :
    ∫ ξ in {η : ℝ | t ≤ |η|}, f ξ ≤ 2 * K * (t ^ (1 - p) / (p - 1)) := by
  have hmaj : IntegrableOn (fun ξ : ℝ => K * |ξ| ^ (-p)) {η : ℝ | t ≤ |η|} volume :=
    (integrableOn_powerTail ht hp).const_mul K
  have hae : (fun ξ : ℝ => f ξ) ≤ᵐ[volume.restrict {η : ℝ | t ≤ |η|}]
      fun ξ : ℝ => K * |ξ| ^ (-p) := by
    refine (ae_restrict_iff' (measurableSet_centralTail t)).mpr ?_
    exact Filter.Eventually.of_forall fun ξ hξ => hbound ξ hξ
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ξ => hnn ξ) hmaj hae
  refine le_trans hmono ?_
  rw [integral_const_mul, integral_powerTail ht hp]
  ring_nf
  exact le_rfl

end GaloisForLFunctions.HTGeometry
