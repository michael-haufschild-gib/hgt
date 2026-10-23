import GaloisForLFunctions.RHTower.CCM.CCMSoninFiniteWordNormalForm

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

set_option maxHeartbeats 1000000

/-- Physical shells with the first ceiling below the second floor are disjoint. -/
theorem evenIndicatorShell_mul_eq_zero_of_left_ceiling_le_right_floor
    (s t u v : ℝ) (hst : s ≤ t) (huv : u ≤ v) (htu : t ≤ u) :
    (evenIndicatorCutoff t - evenIndicatorCutoff s) *
        (evenIndicatorCutoff v - evenIndicatorCutoff u) = 0 := by
  rw [evenIndicatorCutoff_generalShellProduct s t u v hst huv]
  have htv : t ≤ v := htu.trans huv
  rw [min_eq_left htv]
  have htmax : t ≤ max s u := htu.trans (le_max_right _ _)
  rw [min_eq_right htmax, sub_self]

/-- Physical shells with the second ceiling below the first floor are disjoint. -/
theorem evenIndicatorShell_mul_eq_zero_of_right_ceiling_le_left_floor
    (s t u v : ℝ) (hst : s ≤ t) (huv : u ≤ v) (hvs : v ≤ s) :
    (evenIndicatorCutoff t - evenIndicatorCutoff s) *
        (evenIndicatorCutoff v - evenIndicatorCutoff u) = 0 := by
  rw [evenIndicatorCutoff_generalShellProduct s t u v hst huv]
  have hvt : v ≤ t := hvs.trans hst
  rw [min_eq_right hvt]
  have hvmax : v ≤ max s u := hvs.trans (le_max_left _ _)
  rw [min_eq_right hvmax, sub_self]

/-- Multiplication by a containing physical shell fixes the smaller shell. -/
theorem evenIndicatorShell_mul_eq_left_of_subset
    (s t u v : ℝ) (hst : s ≤ t) (huv : u ≤ v) (hus : u ≤ s) (htv : t ≤ v) :
    (evenIndicatorCutoff t - evenIndicatorCutoff s) *
        (evenIndicatorCutoff v - evenIndicatorCutoff u) =
      evenIndicatorCutoff t - evenIndicatorCutoff s := by
  rw [evenIndicatorCutoff_generalShellProduct s t u v hst huv]
  rw [min_eq_left htv, max_eq_left hus]
  rw [min_eq_left hst]

/-- A compact congruence between nondegenerate two-polarization shells cannot increase the
ceiling. -/
theorem evenTwoPolarizationShell_ceiling_not_lt_of_compactEq
    {s t u v : ℝ} (hs : 0 < s) (hst : s < t) (huv : u < v)
    (h : evenTwoPolarizationShell s t =ₖ evenTwoPolarizationShell u v) :
    ¬ t < v := by
  intro htv
  let w := max t u
  let B := evenIndicatorCutoff v - evenIndicatorCutoff w
  have hwv : w < v := max_lt htv huv
  have hw0 : 0 < w := lt_of_lt_of_le hs (le_trans hst.le (le_max_left _ _))
  have hphys1 : B * (evenIndicatorCutoff t - evenIndicatorCutoff s) = 0 := by
    exact evenIndicatorShell_mul_eq_zero_of_right_ceiling_le_left_floor
      w v s t hwv.le hst.le (le_max_left _ _)
  have hphys2 : B * (evenIndicatorCutoff v - evenIndicatorCutoff u) = B := by
    exact evenIndicatorShell_mul_eq_left_of_subset w v u v hwv.le huv.le
      (le_max_right _ _) le_rfl
  have hcross1 : IsCompactOperator
      (B * (evenFourierCutoff t - evenFourierCutoff s)) :=
    isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff
      v w t s (hw0.trans hwv) hw0
  have hcross2 : IsCompactOperator
      (B * (evenFourierCutoff v - evenFourierCutoff u)) :=
    isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff
      v w v u (hw0.trans hwv) hw0
  have hB1 : B * evenTwoPolarizationShell s t =ₖ 0 := by
    have hc := compactOperatorEq_zero_of_isCompact hcross1
    dsimp only [evenTwoPolarizationShell]
    rw [mul_add, hphys1, zero_add]
    exact hc
  have hB2 : B * evenTwoPolarizationShell u v =ₖ B := by
    have hc := compactOperatorEq_zero_of_isCompact hcross2
    have hsum := CompactOperatorEq.add (CompactOperatorEq.refl B) hc
    dsimp only [evenTwoPolarizationShell]
    rw [mul_add, hphys2]
    simpa only [add_zero] using hsum
  have hzeroB : (0 : evenSubspace →L[Complex] evenSubspace) =ₖ B :=
    hB1.symm.trans ((CompactOperatorEq.left_mul B h).trans hB2)
  have hBcompact : IsCompactOperator B := by
    have hz : IsCompactOperator ((0 : evenSubspace →L[Complex] evenSubspace) - B) := hzeroB
    have hzneg : IsCompactOperator (-B) := by simpa using hz
    have hdouble : -(-B) = B := neg_neg B
    rw [← hdouble]
    exact hzneg.neg
  exact not_isCompactOperator_evenIndicatorShellDiff w v hw0 hwv hBcompact

/-- Compact congruence recovers the ceiling of a nondegenerate two-polarization shell. -/
theorem evenTwoPolarizationShell_ceiling_eq_of_compactEq
    {s t u v : ℝ} (hs : 0 < s) (hst : s < t) (hu : 0 < u) (huv : u < v)
    (h : evenTwoPolarizationShell s t =ₖ evenTwoPolarizationShell u v) :
    t = v := by
  apply le_antisymm
  · exact le_of_not_gt
      (evenTwoPolarizationShell_ceiling_not_lt_of_compactEq hu huv hst h.symm)
  · exact le_of_not_gt
      (evenTwoPolarizationShell_ceiling_not_lt_of_compactEq hs hst huv h)

/-- With a common ceiling, compact congruence cannot increase the floor. -/
theorem evenTwoPolarizationShell_floor_not_lt_of_compactEq
    {s u t : ℝ} (hs : 0 < s) (hst : s < t) (hut : u < t)
    (h : evenTwoPolarizationShell s t =ₖ evenTwoPolarizationShell u t) :
    ¬ s < u := by
  intro hsu
  let B := evenIndicatorCutoff u - evenIndicatorCutoff s
  have hphys1 : B * (evenIndicatorCutoff t - evenIndicatorCutoff s) = B := by
    exact evenIndicatorShell_mul_eq_left_of_subset s u s t hsu.le hst.le le_rfl hut.le
  have hphys2 : B * (evenIndicatorCutoff t - evenIndicatorCutoff u) = 0 := by
    exact evenIndicatorShell_mul_eq_zero_of_left_ceiling_le_right_floor
      s u u t hsu.le hut.le le_rfl
  have hcross1 : IsCompactOperator
      (B * (evenFourierCutoff t - evenFourierCutoff s)) :=
    isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff
      u s t s (hs.trans hsu) hs
  have hcross2 : IsCompactOperator
      (B * (evenFourierCutoff t - evenFourierCutoff u)) :=
    isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff
      u s t u (hs.trans hsu) hs
  have hB1 : B * evenTwoPolarizationShell s t =ₖ B := by
    have hc := compactOperatorEq_zero_of_isCompact hcross1
    have hsum := CompactOperatorEq.add (CompactOperatorEq.refl B) hc
    dsimp only [evenTwoPolarizationShell]
    rw [mul_add, hphys1]
    simpa only [add_zero] using hsum
  have hB2 : B * evenTwoPolarizationShell u t =ₖ 0 := by
    have hc := compactOperatorEq_zero_of_isCompact hcross2
    dsimp only [evenTwoPolarizationShell]
    rw [mul_add, hphys2, zero_add]
    exact hc
  have hBzero : B =ₖ (0 : evenSubspace →L[Complex] evenSubspace) :=
    hB1.symm.trans ((CompactOperatorEq.left_mul B h).trans hB2)
  have hBcompact : IsCompactOperator B := by
    have hz : IsCompactOperator (B - (0 : evenSubspace →L[Complex] evenSubspace)) := hBzero
    simpa using hz
  exact not_isCompactOperator_evenIndicatorShellDiff s u hs hsu hBcompact

/-- Compact congruence recovers the floor once the ceiling is fixed. -/
theorem evenTwoPolarizationShell_floor_eq_of_compactEq
    {s u t : ℝ} (hs : 0 < s) (hst : s < t) (hu : 0 < u) (hut : u < t)
    (h : evenTwoPolarizationShell s t =ₖ evenTwoPolarizationShell u t) :
    s = u := by
  apply le_antisymm
  · exact le_of_not_gt
      (evenTwoPolarizationShell_floor_not_lt_of_compactEq hu hut hst h.symm)
  · exact le_of_not_gt
      (evenTwoPolarizationShell_floor_not_lt_of_compactEq hs hst hut h)

/-- **Two-polarization shell faithfulness.**  The Calkin class of a nondegenerate shell recovers
both endpoints. -/
theorem evenTwoPolarizationShell_compactEq_iff
    {s t u v : ℝ} (hs : 0 < s) (hst : s < t) (hu : 0 < u) (huv : u < v) :
    (evenTwoPolarizationShell s t =ₖ evenTwoPolarizationShell u v) ↔
      s = u ∧ t = v := by
  constructor
  · intro h
    have htv := evenTwoPolarizationShell_ceiling_eq_of_compactEq hs hst hu huv h
    subst v
    exact ⟨evenTwoPolarizationShell_floor_eq_of_compactEq hs hst hu huv h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact CompactOperatorEq.refl _

end RHTower

namespace RHTower

open ContinuousLinearMap Metric
open scoped InnerProduct

/-- Taking adjoints preserves compact congruence. -/
theorem CompactOperatorEq.adjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T S : H →L[ℂ] H} (h : T =ₖ S) : T† =ₖ S† := by
  have hc : IsCompactOperator (T - S) := h
  have ha := isCompactOperator_adjoint (T - S) hc
  have heq : (T - S)† = T† - S† := by
    change star (T - S) = star T - star S
    rw [star_sub]
  rw [heq] at ha
  exact ha

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- The adjoint of a canonical physical window is the inverse window. -/
theorem adjoint_evenPhysicalWindowTranslation_of_canonical
    (a C F x : ℝ) (haF : a ≤ F) (hFC : F ≤ C) (hdom : a ≤ x * F) (hx : 0 < x) :
    (evenPhysicalWindowTranslation a C F x hx)† =
      evenPhysicalWindowTranslation a (x * C) (x * F) x⁻¹ (inv_pos.mpr hx) := by
  let A := evenIndicatorCutoff a
  let AC := evenIndicatorCutoff C
  let AF := evenIndicatorCutoff F
  let AxC := evenIndicatorCutoff (x * C)
  let AxF := evenIndicatorCutoff (x * F)
  let Axa := evenIndicatorCutoff (x * a)
  let Ui := evenDilationCLM x⁻¹ (inv_pos.mpr hx)
  have hxaF : x * a ≤ x * F := mul_le_mul_of_nonneg_left haF hx.le
  have hxFC : x * F ≤ x * C := mul_le_mul_of_nonneg_left hFC hx.le
  have hmoveShell : Ui * (AC - AF) = (AxC - AxF) * Ui := by
    have hC := evenDilationCLM_mul_evenIndicatorCutoff C x⁻¹ (inv_pos.mpr hx)
    have hF := evenDilationCLM_mul_evenIndicatorCutoff F x⁻¹ (inv_pos.mpr hx)
    have hscaleC : (x⁻¹)⁻¹ * C = x * C := by rw [inv_inv]
    have hscaleF : (x⁻¹)⁻¹ * F = x * F := by rw [inv_inv]
    rw [hscaleC] at hC
    rw [hscaleF] at hF
    change Ui * AC = AxC * Ui at hC
    change Ui * AF = AxF * Ui at hF
    rw [mul_sub, hC, hF, sub_mul]
  have hleft : (1 - A) * (AxC - AxF) = AxC - AxF :=
    evenIndicatorCutoff_complement_shellProduct (x * C) (x * F) a
      hdom (hdom.trans hxFC)
  have hmoveComplement : Ui * (1 - A) = (1 - Axa) * Ui := by
    have h := evenDilationCLM_mul_evenIndicatorCutoff a x⁻¹ (inv_pos.mpr hx)
    have hscale : (x⁻¹)⁻¹ * a = x * a := by rw [inv_inv]
    rw [hscale] at h
    change Ui * A = Axa * Ui at h
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  have hright : (AxC - AxF) * (1 - Axa) = AxC - AxF := by
    have h := evenIndicatorCutoff_shellComplementProduct (x * C) (x * F) (x * a)
      (hxaF.trans hxFC)
    rw [max_eq_left hxaF] at h
    exact h
  dsimp only [evenPhysicalWindowTranslation]
  rw [physicalWindow_adjoint a C F x hx]
  change (1 - A) * (Ui * (AC - AF)) = (AxC - AxF) * Ui * (1 - A)
  calc
    (1 - A) * (Ui * (AC - AF)) = (1 - A) * ((AxC - AxF) * Ui) := by
      rw [hmoveShell]
    _ = ((1 - A) * (AxC - AxF)) * Ui := by rw [mul_assoc]
    _ = (AxC - AxF) * Ui := by rw [hleft]
    _ = (AxC - AxF) * ((1 - Axa) * Ui) := by
      rw [← mul_assoc, hright]
    _ = (AxC - AxF) * (Ui * (1 - A)) := by rw [hmoveComplement]
    _ = (AxC - AxF) * Ui * (1 - A) := by rw [mul_assoc]

/-- The adjoint of a canonical Fourier window is the inverse window. -/
theorem adjoint_evenFourierWindowTranslation_of_canonical
    (a C F x : ℝ) (haF : a ≤ F) (hFC : F ≤ C) (hdom : a ≤ x * F) (hx : 0 < x) :
    (evenFourierWindowTranslation a C F x hx)† =
      evenFourierWindowTranslation a (x * C) (x * F) x⁻¹ (inv_pos.mpr hx) := by
  let R := evenFourierCutoff a
  let RC := evenFourierCutoff C
  let RF := evenFourierCutoff F
  let RxC := evenFourierCutoff (x * C)
  let RxF := evenFourierCutoff (x * F)
  let Rxa := evenFourierCutoff (x * a)
  let U := evenDilationCLM x hx
  have hxaF : x * a ≤ x * F := mul_le_mul_of_nonneg_left haF hx.le
  have hxFC : x * F ≤ x * C := mul_le_mul_of_nonneg_left hFC hx.le
  have hmoveShell : U * (RC - RF) = (RxC - RxF) * U := by
    have hC := evenDilationCLM_mul_evenFourierCutoff C x hx
    have hF := evenDilationCLM_mul_evenFourierCutoff F x hx
    change U * RC = RxC * U at hC
    change U * RF = RxF * U at hF
    rw [mul_sub, hC, hF, sub_mul]
  have hleft : (1 - R) * (RxC - RxF) = RxC - RxF :=
    evenFourierCutoff_complement_shellProduct (x * C) (x * F) a
      hdom (hdom.trans hxFC)
  have hmoveComplement : U * (1 - R) = (1 - Rxa) * U := by
    have h := evenDilationCLM_mul_evenFourierCutoff a x hx
    change U * R = Rxa * U at h
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  have hright : (RxC - RxF) * (1 - Rxa) = RxC - RxF := by
    have h := evenFourierCutoff_shellComplementProduct (x * C) (x * F) (x * a)
      (hxaF.trans hxFC)
    rw [max_eq_left hxaF] at h
    exact h
  dsimp only [evenFourierWindowTranslation]
  rw [fourierWindow_adjoint a C F x⁻¹ (inv_pos.mpr hx)]
  simp only [inv_inv]
  change (1 - R) * (U * (RC - RF)) = (RxC - RxF) * U * (1 - R)
  calc
    (1 - R) * (U * (RC - RF)) = (1 - R) * ((RxC - RxF) * U) := by
      rw [hmoveShell]
    _ = ((1 - R) * (RxC - RxF)) * U := by rw [mul_assoc]
    _ = (RxC - RxF) * U := by rw [hleft]
    _ = (RxC - RxF) * ((1 - Rxa) * U) := by
      rw [← mul_assoc, hright]
    _ = (RxC - RxF) * (U * (1 - R)) := by rw [hmoveComplement]
    _ = (RxC - RxF) * U * (1 - R) := by rw [mul_assoc]

/-- The adjoint of a canonical two-polarization window is its inverse window. -/
theorem adjoint_evenSoninWindowTranslation_of_canonical
    (a C F x : ℝ) (haF : a ≤ F) (hFC : F ≤ C) (hdom : a ≤ x * F) (hx : 0 < x) :
    (evenSoninWindowTranslation a C F x hx)† =
      evenSoninWindowTranslation a (x * C) (x * F) x⁻¹ (inv_pos.mpr hx) := by
  dsimp only [evenSoninWindowTranslation]
  rw [adjoint_add_clm,
    adjoint_evenPhysicalWindowTranslation_of_canonical a C F x haF hFC hdom hx,
    adjoint_evenFourierWindowTranslation_of_canonical a C F x haF hFC hdom hx]

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

set_option maxHeartbeats 1000000

/-- The final Calkin projection of a canonical live window is its unscaled shell. -/
theorem evenSoninWindowTranslation_mul_adjoint_compactEq_shell_of_canonical
    (a C F x : ℝ) (ha : 0 < a) (haF : a ≤ F) (hFC : F < C)
    (hdom : a ≤ x * F) (hx : 0 < x) :
    evenSoninWindowTranslation a C F x hx *
        (evenSoninWindowTranslation a C F x hx)† =ₖ
      evenTwoPolarizationShell F C := by
  have hF0 : 0 < F := lt_of_lt_of_le ha haF
  have hC0 : 0 < C := hF0.trans hFC
  have hxF0 : 0 < x * F := mul_pos hx hF0
  have hxC0 : 0 < x * C := mul_pos hx hC0
  have hAdj := adjoint_evenSoninWindowTranslation_of_canonical
    a C F x haF hFC.le hdom hx
  have hI := evenSoninWindowTranslation_adjoint_mul_compactEq_shell
    a (x * C) (x * F) x⁻¹ hxC0 hxF0
      (mul_le_mul_of_nonneg_left hFC.le hx.le) (inv_pos.mpr hx)
  rw [← hAdj] at hI
  have hinvF : x⁻¹ * (x * F) = F := inv_mul_cancel_left₀ hx.ne' F
  have hinvC : x⁻¹ * (x * C) = C := inv_mul_cancel_left₀ hx.ne' C
  rw [hinvF, hinvC, max_eq_left haF, max_eq_left (haF.trans hFC.le)] at hI
  simpa using hI

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- Compact congruence is stable under the initial-projection construction. -/
theorem CompactOperatorEq.adjoint_mul_self
    {T S : evenSubspace →L[Complex] evenSubspace} (h : T =ₖ S) :
    T† * T =ₖ S† * S := CompactOperatorEq.mul h.adjoint h

/-- Compact congruence is stable under the final-projection construction. -/
theorem CompactOperatorEq.mul_adjoint
    {T S : evenSubspace →L[Complex] evenSubspace} (h : T =ₖ S) :
    T * T† =ₖ S * S† := CompactOperatorEq.mul h h.adjoint

/-- The initial Calkin projection of live window data is its scaled shell. -/
theorem SoninLiveWindow.adjoint_mul_compactEq_scaledShell
    {a : ℝ} (ha : 0 < a) (d : SoninLiveWindow a) :
    d.operator† * d.operator =ₖ
      evenTwoPolarizationShell (d.scale * d.floor) (d.scale * d.ceiling) := by
  have hF0 : 0 < d.floor := lt_of_lt_of_le ha d.base_le_floor
  have hC0 : 0 < d.ceiling := hF0.trans d.floor_lt_ceiling
  have hxC : a ≤ d.scale * d.ceiling := d.domain_le.trans
    (mul_le_mul_of_nonneg_left d.floor_lt_ceiling.le d.scale_pos.le)
  have h := evenSoninWindowTranslation_adjoint_mul_compactEq_shell
    a d.ceiling d.floor d.scale hC0 hF0 d.floor_lt_ceiling.le d.scale_pos
  rw [max_eq_left d.domain_le, max_eq_left hxC] at h
  exact h

/-- The final Calkin projection of live window data is its unscaled shell. -/
theorem SoninLiveWindow.mul_adjoint_compactEq_shell
    {a : ℝ} (ha : 0 < a) (d : SoninLiveWindow a) :
    d.operator * d.operator† =ₖ evenTwoPolarizationShell d.floor d.ceiling := by
  exact evenSoninWindowTranslation_mul_adjoint_compactEq_shell_of_canonical
    a d.ceiling d.floor d.scale ha d.base_le_floor d.floor_lt_ceiling
      d.domain_le d.scale_pos

/-- Extensionality of live data by its three numerical coordinates. -/
theorem SoninLiveWindow.ext_coordinates {a : ℝ} {d e : SoninLiveWindow a}
    (hC : d.ceiling = e.ceiling) (hF : d.floor = e.floor)
    (hx : d.scale = e.scale) : d = e := by
  cases d
  cases e
  simp only [SoninLiveWindow.mk.injEq] at *
  exact ⟨hC, hF, hx⟩

/-- **Faithful live-window normal form.**  A canonical live Sonin window is recovered exactly
from its Calkin class. -/
theorem SoninLiveWindow.operator_compactEq_iff
    {a : ℝ} (ha : 0 < a) (d e : SoninLiveWindow a) :
    d.operator =ₖ e.operator ↔ d = e := by
  constructor
  · intro h
    have hdF0 : 0 < d.floor := lt_of_lt_of_le ha d.base_le_floor
    have heF0 : 0 < e.floor := lt_of_lt_of_le ha e.base_le_floor
    have hFinal : evenTwoPolarizationShell d.floor d.ceiling =ₖ
        evenTwoPolarizationShell e.floor e.ceiling :=
      (d.mul_adjoint_compactEq_shell ha).symm.trans
        (h.mul_adjoint.trans (e.mul_adjoint_compactEq_shell ha))
    have hFinalCoordinates := (evenTwoPolarizationShell_compactEq_iff
      hdF0 d.floor_lt_ceiling heF0 e.floor_lt_ceiling).mp hFinal
    have hInitial : evenTwoPolarizationShell (d.scale * d.floor)
        (d.scale * d.ceiling) =ₖ
      evenTwoPolarizationShell (e.scale * e.floor) (e.scale * e.ceiling) :=
      (d.adjoint_mul_compactEq_scaledShell ha).symm.trans
        (h.adjoint_mul_self.trans (e.adjoint_mul_compactEq_scaledShell ha))
    have hInitialCoordinates := (evenTwoPolarizationShell_compactEq_iff
      (mul_pos d.scale_pos hdF0)
      (mul_lt_mul_of_pos_left d.floor_lt_ceiling d.scale_pos)
      (mul_pos e.scale_pos heF0)
      (mul_lt_mul_of_pos_left e.floor_lt_ceiling e.scale_pos)).mp hInitial
    have hscale : d.scale = e.scale := by
      apply mul_right_cancel₀ hdF0.ne'
      calc
        d.scale * d.floor = e.scale * e.floor := hInitialCoordinates.1
        _ = e.scale * d.floor := by rw [hFinalCoordinates.1]
    exact SoninLiveWindow.ext_coordinates hFinalCoordinates.2
      hFinalCoordinates.1 hscale
  · rintro rfl
    exact CompactOperatorEq.refl _

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- **Faithful zero/live state normal form.**  Canonical window states have the same Calkin class
exactly when they are equal. -/
theorem SoninWindowState.operator_compactEq_iff
    {a : ℝ} (ha : 0 < a) (s t : SoninWindowState a) :
    s.operator =ₖ t.operator ↔ s = t := by
  cases s with
  | zero =>
      cases t with
      | zero =>
          constructor
          · intro _
            rfl
          · intro _
            exact CompactOperatorEq.refl _
      | live e =>
          constructor
          · intro h
            exact False.elim (e.not_isCompactOperator ha
              (RHTower.IsCompactOperator.compactEq_right isCompactOperator_zero h))
          · intro h
            cases h
  | live d =>
      cases t with
      | zero =>
          constructor
          · intro h
            exact False.elim (d.not_isCompactOperator ha
              (RHTower.IsCompactOperator.compactEq_right isCompactOperator_zero h.symm))
          · intro h
            cases h
      | live e =>
          simpa only [SoninWindowState.operator_live, SoninWindowState.live.injEq] using!
            d.operator_compactEq_iff ha e

/-- **Faithful finite-word normal-form theorem.**  Two nonempty canonical Sonin-window words
represent the same Calkin class exactly when their recursively computed zero/live states agree. -/
theorem finiteSoninWindowWords_compactEq_iff_normalState_eq
    {a : ℝ} (ha : 0 < a) (d e : SoninLiveWindow a)
    (ds es : List (SoninLiveWindow a)) :
    foldSoninWindowOperators (SoninWindowState.live d).operator ds =ₖ
        foldSoninWindowOperators (SoninWindowState.live e).operator es ↔
      foldSoninWindowStates (SoninWindowState.live d) ds =
        foldSoninWindowStates (SoninWindowState.live e) es := by
  let Td := foldSoninWindowOperators (SoninWindowState.live d).operator ds
  let Te := foldSoninWindowOperators (SoninWindowState.live e).operator es
  let sd := foldSoninWindowStates (SoninWindowState.live d) ds
  let se := foldSoninWindowStates (SoninWindowState.live e) es
  have hd : Td =ₖ sd.operator := finiteSoninWindowWord_compactEq_state ha d ds
  have he : Te =ₖ se.operator := finiteSoninWindowWord_compactEq_state ha e es
  constructor
  · intro h
    exact (sd.operator_compactEq_iff ha se).mp (hd.symm.trans (h.trans he))
  · intro h
    exact hd.trans ((CompactOperatorEq.of_eq (congrArg SoninWindowState.operator h)).trans he.symm)

/-- **Faithful actual CCM Gram-word classification.**  Two nonempty words of genuine even-Sonin
Gram corners represent the same Calkin class exactly when their canonical states agree. -/
theorem finiteSoninGramWords_compactEq_iff_normalState_eq
    (a : ℝ) (ha : 0 < a) (g h : SoninGramFactor)
    (gs hs : List SoninGramFactor) :
    foldSoninGramFactorOperators a (g.operator a) gs =ₖ
        foldSoninGramFactorOperators a (h.operator a) hs ↔
      foldSoninWindowStates (SoninWindowState.live (g.liveWindow a ha))
          (gs.map fun k => k.liveWindow a ha) =
        foldSoninWindowStates (SoninWindowState.live (h.liveWindow a ha))
          (hs.map fun k => k.liveWindow a ha) := by
  let Tg := foldSoninGramFactorOperators a (g.operator a) gs
  let Th := foldSoninGramFactorOperators a (h.operator a) hs
  let sg := foldSoninWindowStates (SoninWindowState.live (g.liveWindow a ha))
    (gs.map fun k => k.liveWindow a ha)
  let sh := foldSoninWindowStates (SoninWindowState.live (h.liveWindow a ha))
    (hs.map fun k => k.liveWindow a ha)
  have hg : Tg =ₖ sg.operator := finiteSoninGramWord_compactEq_state a ha g gs
  have hh : Th =ₖ sh.operator := finiteSoninGramWord_compactEq_state a ha h hs
  constructor
  · intro H
    exact (sg.operator_compactEq_iff ha sh).mp (hg.symm.trans (H.trans hh))
  · intro H
    exact hg.trans ((CompactOperatorEq.of_eq (congrArg SoninWindowState.operator H)).trans hh.symm)

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- **Exact associativity of the tropical Sonin state product.**  For a positive base cutoff,
the zero/live recursion is an associative multiplication, not merely a left-fold algorithm. -/
theorem composeSoninWindowStates_assoc
    {a : ℝ} (ha : 0 < a) (r s t : SoninWindowState a) :
    composeSoninWindowStates (composeSoninWindowStates r s) t =
      composeSoninWindowStates r (composeSoninWindowStates s t) := by
  apply ((composeSoninWindowStates (composeSoninWindowStates r s) t).operator_compactEq_iff
    ha (composeSoninWindowStates r (composeSoninWindowStates s t))).mp
  have hrs := soninWindowState_operator_mul_compactEq ha r s
  have hst := soninWindowState_operator_mul_compactEq ha s t
  have hleft := soninWindowState_operator_mul_compactEq ha
    (composeSoninWindowStates r s) t
  have hright := soninWindowState_operator_mul_compactEq ha r
    (composeSoninWindowStates s t)
  exact hleft.symm.trans
    ((CompactOperatorEq.mul hrs.symm (CompactOperatorEq.refl t.operator)).trans
      ((CompactOperatorEq.of_eq (mul_assoc r.operator s.operator t.operator)).trans
        ((CompactOperatorEq.left_mul r.operator hst).trans hright)))

@[simp] theorem composeSoninWindowStates_zero_left
    {a : ℝ} (s : SoninWindowState a) :
    composeSoninWindowStates SoninWindowState.zero s = SoninWindowState.zero := by
  cases s <;> rfl

@[simp] theorem composeSoninWindowStates_zero_right
    {a : ℝ} (s : SoninWindowState a) :
    composeSoninWindowStates s SoninWindowState.zero = SoninWindowState.zero := by
  cases s <;> rfl

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- Canonical inverse data: exchange initial and final shells and invert displacement. -/
def SoninLiveWindow.inverse {a : ℝ} (d : SoninLiveWindow a) : SoninLiveWindow a where
  ceiling := d.scale * d.ceiling
  floor := d.scale * d.floor
  scale := d.scale⁻¹
  scale_pos := inv_pos.mpr d.scale_pos
  base_le_floor := d.domain_le
  floor_lt_ceiling := mul_lt_mul_of_pos_left d.floor_lt_ceiling d.scale_pos
  domain_le := by
    have hscale : d.scale⁻¹ * (d.scale * d.floor) = d.floor := by
      field_simp [d.scale_pos.ne']
    rw [hscale]
    exact d.base_le_floor

/-- The inverse datum carries the Hilbert-space adjoint exactly. -/
theorem SoninLiveWindow.inverse_operator {a : ℝ} (d : SoninLiveWindow a) :
    d.inverse.operator = d.operator† := by
  exact (adjoint_evenSoninWindowTranslation_of_canonical
    a d.ceiling d.floor d.scale d.base_le_floor d.floor_lt_ceiling.le
      d.domain_le d.scale_pos).symm

/-- Canonical inversion is involutive. -/
@[simp] theorem SoninLiveWindow.inverse_inverse {a : ℝ} (d : SoninLiveWindow a) :
    d.inverse.inverse = d := by
  apply SoninLiveWindow.ext_coordinates
  · dsimp only [SoninLiveWindow.inverse]
    field_simp [d.scale_pos.ne']
  · dsimp only [SoninLiveWindow.inverse]
    field_simp [d.scale_pos.ne']
  · dsimp only [SoninLiveWindow.inverse]
    exact inv_inv d.scale

/-- Canonical involution on zero/live Sonin states. -/
def SoninWindowState.inverse {a : ℝ} : SoninWindowState a → SoninWindowState a
  | .zero => .zero
  | .live d => .live d.inverse

/-- State inversion carries the Hilbert-space adjoint exactly. -/
theorem SoninWindowState.inverse_operator {a : ℝ} (s : SoninWindowState a) :
    s.inverse.operator = s.operator† := by
  cases s with
  | zero => simp [SoninWindowState.inverse]
  | live d => exact d.inverse_operator

/-- State inversion is involutive. -/
@[simp] theorem SoninWindowState.inverse_inverse {a : ℝ} (s : SoninWindowState a) :
    s.inverse.inverse = s := by
  cases s <;> simp [SoninWindowState.inverse]

/-- **Exact anti-multiplicativity of canonical inversion.** -/
theorem composeSoninWindowStates_inverse
    {a : ℝ} (ha : 0 < a) (s t : SoninWindowState a) :
    (composeSoninWindowStates s t).inverse =
      composeSoninWindowStates t.inverse s.inverse := by
  apply ((composeSoninWindowStates s t).inverse.operator_compactEq_iff ha
    (composeSoninWindowStates t.inverse s.inverse)).mp
  rw [SoninWindowState.inverse_operator]
  have hst := soninWindowState_operator_mul_compactEq ha s t
  have hinv := soninWindowState_operator_mul_compactEq ha t.inverse s.inverse
  rw [SoninWindowState.inverse_operator, SoninWindowState.inverse_operator] at hinv
  have hadj := hst.adjoint.symm
  change (composeSoninWindowStates s t).operator† =ₖ
    star (s.operator * t.operator) at hadj
  have hstar : star (s.operator * t.operator) =
      t.operator† * s.operator† := by
    change ContinuousLinearMap.adjoint (s.operator ∘L t.operator) = _
    rw [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.mul_def]
  rw [hstar] at hadj
  exact hadj.trans hinv

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- A live window satisfies the partial-isometry regularity equation modulo compacts. -/
theorem SoninLiveWindow.mul_adjoint_mul_compactEq_self
    {a : ℝ} (ha : 0 < a) (d : SoninLiveWindow a) :
    (d.operator * d.operator†) * d.operator =ₖ d.operator := by
  let S := evenTwoPolarizationShell (d.scale * d.floor) (d.scale * d.ceiling)
  have hF0 : 0 < d.floor := lt_of_lt_of_le ha d.base_le_floor
  have hI : d.operator† * d.operator =ₖ S := d.adjoint_mul_compactEq_scaledShell ha
  have hSadj : S† = S := adjoint_evenTwoPolarizationShell _ _
  have hSS : S * S =ₖ S := evenTwoPolarizationShell_mul_compactEq_self
    (d.scale * d.floor) (d.scale * d.ceiling)
    (mul_pos d.scale_pos hF0)
    (mul_le_mul_of_nonneg_left d.floor_lt_ceiling.le d.scale_pos.le)
  have hc : IsCompactOperator
      ((d.operator * (1 - S) : evenSubspace →L[Complex] evenSubspace)) :=
    isCompactOperator_mul_one_sub_of_compactEq d.operator S hSadj hI hSS
  have hTS : d.operator * S =ₖ d.operator := by
    rw [CompactOperatorEq]
    have heq : d.operator * S - d.operator = -(d.operator * (1 - S)) := by
      rw [mul_sub, mul_one]
      abel
    rw [heq]
    exact hc.neg
  exact (CompactOperatorEq.of_eq
    (mul_assoc d.operator (d.operator†) d.operator)).trans
    ((CompactOperatorEq.left_mul d.operator hI).trans hTS)

/-- **First exact inverse-semigroup regularity law.** -/
theorem composeSoninWindowStates_inverse_regular
    {a : ℝ} (ha : 0 < a) (s : SoninWindowState a) :
    composeSoninWindowStates (composeSoninWindowStates s s.inverse) s = s := by
  apply ((composeSoninWindowStates (composeSoninWindowStates s s.inverse) s).operator_compactEq_iff
    ha s).mp
  have hinner := soninWindowState_operator_mul_compactEq ha s s.inverse
  have houter := soninWindowState_operator_mul_compactEq ha
    (composeSoninWindowStates s s.inverse) s
  have htriple : (s.operator * s.operator†) * s.operator =ₖ s.operator := by
    cases s with
    | zero => exact CompactOperatorEq.refl _
    | live d => exact d.mul_adjoint_mul_compactEq_self ha
  rw [SoninWindowState.inverse_operator] at hinner
  exact houter.symm.trans
    ((CompactOperatorEq.mul hinner.symm (CompactOperatorEq.refl s.operator)).trans htriple)

/-- **Second exact inverse-semigroup regularity law.** -/
theorem composeSoninWindowStates_inverse_regular'
    {a : ℝ} (ha : 0 < a) (s : SoninWindowState a) :
    composeSoninWindowStates (composeSoninWindowStates s.inverse s) s.inverse = s.inverse := by
  simpa using composeSoninWindowStates_inverse_regular ha s.inverse

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

set_option maxHeartbeats 1000000

/-- Any two nondegenerate two-polarization shells commute in the Calkin algebra. -/
theorem evenTwoPolarizationShell_comm_compactEq
    (s t u v : ℝ) (hs : 0 < s) (hst : s ≤ t) (hu : 0 < u) (huv : u ≤ v) :
    evenTwoPolarizationShell s t * evenTwoPolarizationShell u v =ₖ
      evenTwoPolarizationShell u v * evenTwoPolarizationShell s t := by
  let As := evenIndicatorCutoff t - evenIndicatorCutoff s
  let Rs := evenFourierCutoff t - evenFourierCutoff s
  let Au := evenIndicatorCutoff v - evenIndicatorCutoff u
  let Ru := evenFourierCutoff v - evenFourierCutoff u
  have hAA : As * Au = Au * As := by
    dsimp only [As, Au]
    rw [evenIndicatorCutoff_generalShellProduct s t u v hst huv,
      evenIndicatorCutoff_generalShellProduct u v s t huv hst]
    simp only [min_comm, max_comm]
  have hRR : Rs * Ru = Ru * Rs := by
    dsimp only [Rs, Ru]
    rw [evenFourierCutoff_generalShellProduct s t u v hst huv,
      evenFourierCutoff_generalShellProduct u v s t huv hst]
    simp only [min_comm, max_comm]
  have hAsRu : As * Ru =ₖ 0 := compactOperatorEq_zero_of_isCompact
    (isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff t s v u
      (hs.trans_le hst) hs)
  have hRsAu : Rs * Au =ₖ 0 := compactOperatorEq_zero_of_isCompact
    (isCompactOperator_evenFourierDiff_mul_evenIndicatorDiff t s v u
      (hs.trans_le hst) hs)
  have hAuRs : Au * Rs =ₖ 0 := compactOperatorEq_zero_of_isCompact
    (isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff v u t s
      (hu.trans_le huv) hu)
  have hRuAs : Ru * As =ₖ 0 := compactOperatorEq_zero_of_isCompact
    (isCompactOperator_evenFourierDiff_mul_evenIndicatorDiff v u t s
      (hu.trans_le huv) hu)
  have hleft : (As + Rs) * (Au + Ru) =ₖ As * Au + Rs * Ru := by
    have hexpand : (As + Rs) * (Au + Ru) =
        (As * Au + As * Ru) + (Rs * Au + Rs * Ru) := by noncomm_ring
    rw [hexpand]
    have hsum := CompactOperatorEq.add
      (CompactOperatorEq.add (CompactOperatorEq.refl (As * Au)) hAsRu)
      (CompactOperatorEq.add hRsAu (CompactOperatorEq.refl (Rs * Ru)))
    simpa only [add_zero, zero_add] using hsum
  have hright : (Au + Ru) * (As + Rs) =ₖ As * Au + Rs * Ru := by
    have hexpand : (Au + Ru) * (As + Rs) =
        (Au * As + Au * Rs) + (Ru * As + Ru * Rs) := by noncomm_ring
    rw [hexpand]
    have hsum := CompactOperatorEq.add
      (CompactOperatorEq.add (CompactOperatorEq.of_eq hAA.symm) hAuRs)
      (CompactOperatorEq.add hRuAs (CompactOperatorEq.of_eq hRR.symm))
    simpa only [add_zero, zero_add] using hsum
  change (As + Rs) * (Au + Ru) =ₖ (Au + Ru) * (As + Rs)
  exact hleft.trans hright.symm

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- Canonical range states commute modulo compacts at the operator level. -/
theorem SoninWindowState.rangeOperators_comm_compactEq
    {a : ℝ} (ha : 0 < a) (s t : SoninWindowState a) :
    (composeSoninWindowStates s s.inverse).operator *
        (composeSoninWindowStates t t.inverse).operator =ₖ
      (composeSoninWindowStates t t.inverse).operator *
        (composeSoninWindowStates s s.inverse).operator := by
  cases s with
  | zero =>
      exact CompactOperatorEq.of_eq (by
        simp [SoninWindowState.inverse, composeSoninWindowStates])
  | live d =>
      cases t with
      | zero =>
          exact CompactOperatorEq.of_eq (by
            simp [SoninWindowState.inverse, composeSoninWindowStates])
      | live e =>
          have hdProduct := soninWindowState_operator_mul_compactEq ha
            (SoninWindowState.live d) (SoninWindowState.live d.inverse)
          have heProduct := soninWindowState_operator_mul_compactEq ha
            (SoninWindowState.live e) (SoninWindowState.live e.inverse)
          change d.operator * d.inverse.operator =ₖ _ at hdProduct
          change e.operator * e.inverse.operator =ₖ _ at heProduct
          rw [d.inverse_operator] at hdProduct
          rw [e.inverse_operator] at heProduct
          have hdRange : (composeSoninWindowStates
              (SoninWindowState.live d) (SoninWindowState.live d.inverse)).operator =ₖ
              evenTwoPolarizationShell d.floor d.ceiling :=
            hdProduct.symm.trans (d.mul_adjoint_compactEq_shell ha)
          have heRange : (composeSoninWindowStates
              (SoninWindowState.live e) (SoninWindowState.live e.inverse)).operator =ₖ
              evenTwoPolarizationShell e.floor e.ceiling :=
            heProduct.symm.trans (e.mul_adjoint_compactEq_shell ha)
          have hcomm := evenTwoPolarizationShell_comm_compactEq
            d.floor d.ceiling e.floor e.ceiling
            (lt_of_lt_of_le ha d.base_le_floor) d.floor_lt_ceiling.le
            (lt_of_lt_of_le ha e.base_le_floor) e.floor_lt_ceiling.le
          exact (CompactOperatorEq.mul hdRange heRange).trans
            (hcomm.trans (CompactOperatorEq.mul heRange hdRange).symm)

/-- **Commuting canonical idempotent law.**  Range idempotents commute exactly in the faithful
zero/live normal-form semigroup. -/
theorem composeSoninWindowStates_range_comm
    {a : ℝ} (ha : 0 < a) (s t : SoninWindowState a) :
    composeSoninWindowStates (composeSoninWindowStates s s.inverse)
        (composeSoninWindowStates t t.inverse) =
      composeSoninWindowStates (composeSoninWindowStates t t.inverse)
        (composeSoninWindowStates s s.inverse) := by
  apply ((composeSoninWindowStates (composeSoninWindowStates s s.inverse)
    (composeSoninWindowStates t t.inverse)).operator_compactEq_iff ha
      (composeSoninWindowStates (composeSoninWindowStates t t.inverse)
        (composeSoninWindowStates s s.inverse))).mp
  have hleft := soninWindowState_operator_mul_compactEq ha
    (composeSoninWindowStates s s.inverse) (composeSoninWindowStates t t.inverse)
  have hright := soninWindowState_operator_mul_compactEq ha
    (composeSoninWindowStates t t.inverse) (composeSoninWindowStates s s.inverse)
  exact hleft.symm.trans ((s.rangeOperators_comm_compactEq ha t).trans hright)

end RHTower

namespace RHTower

/-- Canonical range states are exact idempotents. -/
theorem composeSoninWindowStates_range_idempotent
    {a : ℝ} (ha : 0 < a) (s : SoninWindowState a) :
    composeSoninWindowStates (composeSoninWindowStates s s.inverse)
        (composeSoninWindowStates s s.inverse) =
      composeSoninWindowStates s s.inverse := by
  rw [← composeSoninWindowStates_assoc ha
    (composeSoninWindowStates s s.inverse) s s.inverse]
  rw [composeSoninWindowStates_inverse_regular ha s]

/-- Canonical source states are exact idempotents. -/
theorem composeSoninWindowStates_source_idempotent
    {a : ℝ} (ha : 0 < a) (s : SoninWindowState a) :
    composeSoninWindowStates (composeSoninWindowStates s.inverse s)
        (composeSoninWindowStates s.inverse s) =
      composeSoninWindowStates s.inverse s := by
  simpa using composeSoninWindowStates_range_idempotent ha s.inverse

end RHTower

namespace RHTower

/-- Every canonical zero/live state is represented by a Calkin partial isometry. -/
theorem SoninWindowState.isCalkinPartialIsometry
    {a : ℝ} (ha : 0 < a) (s : SoninWindowState a) :
    IsCalkinPartialIsometry s.operator := by
  cases s with
  | zero =>
      constructor <;> exact CompactOperatorEq.refl _
  | live d => exact d.isCalkinPartialIsometry ha

/-- **CCM finite-word carrier capstone.**  At every positive Sonin cutoff, canonical states form a
faithfully represented associative involutive regular semigroup with zero; inversion is adjoint,
range and source states are idempotent, canonical range idempotents commute, and every represented
state is a Calkin partial isometry. -/
theorem ccmSoninFiniteWord_faithful_regular_star_semigroup
    {a : ℝ} (ha : 0 < a) :
    (∀ s t : SoninWindowState a,
      (s.operator =ₖ t.operator ↔ s = t)) ∧
    (∀ r s t : SoninWindowState a,
      composeSoninWindowStates (composeSoninWindowStates r s) t =
        composeSoninWindowStates r (composeSoninWindowStates s t)) ∧
    (∀ s t : SoninWindowState a,
      (composeSoninWindowStates s t).inverse =
        composeSoninWindowStates t.inverse s.inverse) ∧
    (∀ s : SoninWindowState a,
      composeSoninWindowStates (composeSoninWindowStates s s.inverse) s = s) ∧
    (∀ s : SoninWindowState a,
      composeSoninWindowStates (composeSoninWindowStates s s.inverse)
          (composeSoninWindowStates s s.inverse) =
        composeSoninWindowStates s s.inverse) ∧
    (∀ s t : SoninWindowState a,
      composeSoninWindowStates (composeSoninWindowStates s s.inverse)
          (composeSoninWindowStates t t.inverse) =
        composeSoninWindowStates (composeSoninWindowStates t t.inverse)
          (composeSoninWindowStates s s.inverse)) ∧
    (∀ s : SoninWindowState a, IsCalkinPartialIsometry s.operator) := by
  exact ⟨fun s t => s.operator_compactEq_iff ha t,
    composeSoninWindowStates_assoc ha,
    composeSoninWindowStates_inverse ha,
    composeSoninWindowStates_inverse_regular ha,
    composeSoninWindowStates_range_idempotent ha,
    composeSoninWindowStates_range_comm ha,
    SoninWindowState.isCalkinPartialIsometry ha⟩

end RHTower
