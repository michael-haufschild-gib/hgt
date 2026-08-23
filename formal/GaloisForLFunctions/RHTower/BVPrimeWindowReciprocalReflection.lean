import GaloisForLFunctions.RHTower.BVPrimeWindowDilationOrientation
import GaloisForLFunctions.RHTower.ZetaZeroOrderReflection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Reciprocal reflection of bounded-variation prime windows

Compact BV prime windows are closed under `W#(x) = conj (W (1/x))`.  The exact Mellin
change of variables gives `M_{W#}(s) = conj (M_W(2-conj s))`; functional-equation reflection
then swaps the forward and inverse continued-source residue channels with exact multiplicity.
-/

open Complex Filter MeasureTheory Set Topology

noncomputable section

namespace RHTower
namespace CompactBVPrimeWindow

/-- Extending a BV map on a closed interval by zero on both complementary rays preserves bounded
variation globally.  Endpoint jumps contribute only finite `edist` terms. -/
theorem boundedVariationOn_univ_of_eq_zero_off_Icc
    {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Set.Icc a b))
    (hzero : ∀ x, x ∉ Set.Icc a b → f x = 0) :
    BoundedVariationOn f Set.univ := by
  have hleftTendsto : Tendsto f (𝓝[Set.univ ∩ Set.Iio a] a) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    symm
    apply hzero
    intro hxab
    exact (not_lt_of_ge hxab.1) hx.2
  have hrightTendsto : Tendsto f (𝓝[Set.univ ∩ Set.Ioi b] b) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    symm
    apply hzero
    intro hxab
    exact (not_lt_of_ge hxab.2) hx.2
  have hleftEq := eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist
    (f := f) (s := Set.univ) (a := a) (l := 0)
    (by simpa only [Set.univ_inter] using (nhdsLT_neBot a)) (Set.mem_univ a) hleftTendsto
  have hrightEq := eVariationOn.eVariationOn_on_inter_Ici_eq_Ioi_add_edist
    (f := f) (s := Set.univ) (a := b) (l := 0)
    (by simpa only [Set.univ_inter] using (nhdsGT_neBot b)) (Set.mem_univ b) hrightTendsto
  have hleftZero : eVariationOn f (Set.Iio a) = 0 := by
    rw [eVariationOn.eq_zero_iff]
    intro x hx y hy
    rw [hzero x (by simp only [Set.mem_Icc, not_and_or]; exact Or.inl (not_le.mpr hx)),
      hzero y (by simp only [Set.mem_Icc, not_and_or]; exact Or.inl (not_le.mpr hy))]
    simp
  have hrightZero : eVariationOn f (Set.Ioi b) = 0 := by
    rw [eVariationOn.eq_zero_iff]
    intro x hx y hy
    rw [hzero x (by simp only [Set.mem_Icc, not_and_or]; exact Or.inr (not_le.mpr hx)),
      hzero y (by simp only [Set.mem_Icc, not_and_or]; exact Or.inr (not_le.mpr hy))]
    simp
  have hleft : eVariationOn f (Set.Iic a) ≠ ⊤ := by
    simp only [Set.univ_inter] at hleftEq
    rw [hleftZero, zero_add] at hleftEq
    rw [hleftEq]
    finiteness
  have hright : eVariationOn f (Set.Ici b) ≠ ⊤ := by
    simp only [Set.univ_inter] at hrightEq
    rw [hrightZero, zero_add] at hrightEq
    rw [hrightEq]
    finiteness
  have hsplitMiddle :
      eVariationOn f (Set.Icc a b ∪ Set.Ici b) =
        eVariationOn f (Set.Icc a b) + eVariationOn f (Set.Ici b) :=
    eVariationOn.union f
      ⟨⟨hab, le_rfl⟩, fun _ hx => hx.2⟩
      ⟨by simp, fun _ hx => hx⟩
  have hmiddleSet : Set.Icc a b ∪ Set.Ici b = Set.Ici a := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact hab.trans hx
    · intro hx
      exact le_total x b |>.elim (fun hxb => Or.inl ⟨hx, hxb⟩) Or.inr
  have hmiddle : eVariationOn f (Set.Ici a) ≠ ⊤ := by
    rw [← hmiddleSet, hsplitMiddle, ENNReal.add_ne_top]
    exact ⟨hf, hright⟩
  have hsplitAll :
      eVariationOn f (Set.Iic a ∪ Set.Ici a) =
        eVariationOn f (Set.Iic a) + eVariationOn f (Set.Ici a) :=
    eVariationOn.union f
      ⟨by simp, fun _ hx => hx⟩
      ⟨by simp, fun _ hx => hx⟩
  have hallSet : Set.Iic a ∪ Set.Ici a = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ, iff_true]
    exact le_total x a
  rw [BoundedVariationOn, ← hallSet, hsplitAll, ENNReal.add_ne_top]
  exact ⟨hleft, hmiddle⟩

private theorem intervalIntegrable_reciprocalConjugate
    (W : CompactBVPrimeWindow) :
    IntervalIntegrable (fun x : ℝ => (starRingEnd ℂ) (W x⁻¹)) volume
      W.upper⁻¹ W.lower⁻¹ := by
  let g : ℝ → ℂ := fun u => (starRingEnd ℂ) (W u)
  have hgGlobal : Integrable g volume := by
    exact Complex.conjCLE.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp W.integrable
  have hg : IntervalIntegrable g volume W.upper W.lower := hgGlobal.intervalIntegrable
  let f : ℝ → ℝ := fun x => x⁻¹
  let f' : ℝ → ℝ := fun x => -(x ^ 2)⁻¹
  have ha : 0 < W.upper⁻¹ := inv_pos.mpr W.upper_pos
  have hab : W.upper⁻¹ ≤ W.lower⁻¹ :=
    (inv_le_inv₀ W.upper_pos W.lower_pos).2 W.lower_le_upper
  have hfcont : ContinuousOn f (uIcc W.upper⁻¹ W.lower⁻¹) := by
    exact continuousOn_inv₀.mono (by
      intro x hx
      rw [uIcc_of_le hab] at hx
      exact ne_of_gt (ha.trans_le hx.1))
  have hfderiv : ∀ x ∈ Set.Ioo (min W.upper⁻¹ W.lower⁻¹)
      (max W.upper⁻¹ W.lower⁻¹), HasDerivAt f (f' x) x := by
    intro x hx
    apply hasDerivAt_inv
    rw [min_eq_left hab, max_eq_right hab] at hx
    exact ne_of_gt (ha.trans hx.1)
  have hfnonpos : ∀ x ∈ Set.Ioo (min W.upper⁻¹ W.lower⁻¹)
      (max W.upper⁻¹ W.lower⁻¹), f' x ≤ 0 := by
    intro x hx
    exact neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg x))
  have hweighted : IntervalIntegrable
      (fun x => f' x • (g ∘ f) x) volume W.upper⁻¹ W.lower⁻¹ :=
    (intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonpos
      hfcont hfderiv hfnonpos).2 (by simpa [f] using hg)
  have hmult := hweighted.mul_continuousOn
    (g := fun x : ℝ => (-(x ^ 2) : ℂ))
    (by fun_prop : ContinuousOn (fun x : ℝ => (-(x ^ 2) : ℂ))
      (uIcc W.upper⁻¹ W.lower⁻¹))
  refine hmult.congr ?_
  intro x hxmem
  by_cases hx : x = 0
  · subst x
    simp [f, f']
  · have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
    simp only [f, f', Function.comp_apply, g, real_smul, Complex.ofReal_neg,
      Complex.ofReal_inv, Complex.ofReal_pow]
    field_simp [hxC]

/-- Reciprocal-conjugate compact BV window: `x ↦ conj (W (1/x))`. -/
def reciprocalConjugate (W : CompactBVPrimeWindow) : CompactBVPrimeWindow where
  lower := W.upper⁻¹
  upper := W.lower⁻¹
  lower_pos := inv_pos.mpr W.upper_pos
  lower_lt_upper := by
    simpa only [one_div] using one_div_lt_one_div_of_lt W.lower_pos W.lower_lt_upper
  toFun := fun x => (starRingEnd ℂ) (W x⁻¹)
  eq_zero_off_support := by
    intro x hx
    have hW : W x⁻¹ = 0 := by
      apply W.eq_zero_off_support
      intro hinv
      apply hx
      have hxinvPos : 0 < x⁻¹ := W.lower_pos.trans_le hinv.1
      constructor
      · calc
          W.upper⁻¹ ≤ (x⁻¹)⁻¹ := (inv_le_inv₀ W.upper_pos hxinvPos).2 hinv.2
          _ = x := inv_inv x
      · calc
          x = (x⁻¹)⁻¹ := (inv_inv x).symm
          _ ≤ W.lower⁻¹ := (inv_le_inv₀ hxinvPos W.lower_pos).2 hinv.1
    simpa using congrArg (starRingEnd ℂ) hW
  integrable := by
    have hint := intervalIntegrable_reciprocalConjugate W
    have hle : W.upper⁻¹ ≤ W.lower⁻¹ :=
      (inv_le_inv₀ W.upper_pos W.lower_pos).2 W.lower_le_upper
    have hOn : IntegrableOn (fun x : ℝ => (starRingEnd ℂ) (W x⁻¹))
        (Set.Icc W.upper⁻¹ W.lower⁻¹) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hle).1 hint
    have hInd := hOn.integrable_indicator measurableSet_Icc
    apply hInd.congr
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc W.upper⁻¹ W.lower⁻¹
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hW : W x⁻¹ = 0 := by
        apply W.eq_zero_off_support
        intro hinv
        apply hx
        have hxinvPos : 0 < x⁻¹ := W.lower_pos.trans_le hinv.1
        constructor
        · calc
            W.upper⁻¹ ≤ (x⁻¹)⁻¹ := (inv_le_inv₀ W.upper_pos hxinvPos).2 hinv.2
            _ = x := inv_inv x
        · calc
            x = (x⁻¹)⁻¹ := (inv_inv x).symm
            _ ≤ W.lower⁻¹ := (inv_le_inv₀ hxinvPos W.lower_pos).2 hinv.1
      simpa using (congrArg (starRingEnd ℂ) hW).symm
  boundedVariation := by
    have hinner : BoundedVariationOn (fun x : ℝ => W x⁻¹)
        (Set.Icc W.upper⁻¹ W.lower⁻¹) := by
      apply ne_top_of_le_ne_top W.boundedVariation
      apply eVariationOn.comp_le_of_antitoneOn W (fun x : ℝ => x⁻¹)
      · intro x hx y hy hxy
        exact (inv_le_inv₀ (inv_pos.mpr W.upper_pos |>.trans_le hy.1)
          (inv_pos.mpr W.upper_pos |>.trans_le hx.1)).2 hxy
      · intro x hx
        exact Set.mem_univ x
    have hcentral : BoundedVariationOn
        (fun x : ℝ => (starRingEnd ℂ) (W x⁻¹))
        (Set.Icc W.upper⁻¹ W.lower⁻¹) := by
      change BoundedVariationOn
        ((starRingEnd ℂ) ∘ fun x : ℝ => W x⁻¹)
        (Set.Icc W.upper⁻¹ W.lower⁻¹)
      exact Complex.isometry_conj.lipschitz.comp_boundedVariationOn hinner
    apply boundedVariationOn_univ_of_eq_zero_off_Icc
      ((inv_le_inv₀ W.upper_pos W.lower_pos).2 W.lower_le_upper) hcentral
    intro x hx
    have hW : W x⁻¹ = 0 := by
      apply W.eq_zero_off_support
      intro hinv
      apply hx
      have hxinvPos : 0 < x⁻¹ := W.lower_pos.trans_le hinv.1
      constructor
      · calc
          W.upper⁻¹ ≤ (x⁻¹)⁻¹ := (inv_le_inv₀ W.upper_pos hxinvPos).2 hinv.2
          _ = x := inv_inv x
      · calc
          x = (x⁻¹)⁻¹ := (inv_inv x).symm
          _ ≤ W.lower⁻¹ := (inv_le_inv₀ hxinvPos W.lower_pos).2 hinv.1
    simpa using congrArg (starRingEnd ℂ) hW

@[simp] theorem reciprocalConjugate_apply (W : CompactBVPrimeWindow) (x : ℝ) :
    W.reciprocalConjugate x = (starRingEnd ℂ) (W x⁻¹) := rfl

@[simp] theorem reciprocalConjugate_lower (W : CompactBVPrimeWindow) :
    W.reciprocalConjugate.lower = W.upper⁻¹ := rfl

@[simp] theorem reciprocalConjugate_upper (W : CompactBVPrimeWindow) :
    W.reciprocalConjugate.upper = W.lower⁻¹ := rfl

/-- Reciprocal conjugation is pointwise involutive. -/
theorem reciprocalConjugate_reciprocalConjugate_apply
    (W : CompactBVPrimeWindow) (x : ℝ) :
    W.reciprocalConjugate.reciprocalConjugate x = W x := by
  simp [reciprocalConjugate_apply]

/-- Reciprocal conjugation swaps positive argument dilation with reciprocal expansion. -/
theorem reciprocalConjugate_argumentDilation_apply
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (x : ℝ) :
    (W.argumentDilation r hr).reciprocalConjugate x =
      W.reciprocalConjugate.argumentExpansion r hr x := by
  rw [reciprocalConjugate_apply, argumentDilation_apply,
    argumentExpansion_apply, reciprocalConjugate_apply]
  congr 2
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · field_simp

/-- Reciprocal conjugation swaps reciprocal expansion with positive argument dilation. -/
theorem reciprocalConjugate_argumentExpansion_apply
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r) (x : ℝ) :
    (W.argumentExpansion r hr).reciprocalConjugate x =
      W.reciprocalConjugate.argumentDilation r hr x := by
  rw [reciprocalConjugate_apply, argumentExpansion_apply,
    argumentDilation_apply, reciprocalConjugate_apply]
  congr 2
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · field_simp

private theorem conj_ofReal_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (starRingEnd ℂ) ((x : ℂ) ^ s) = (x : ℂ) ^ ((starRingEnd ℂ) s) := by
  have hxc : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx
  rw [Complex.cpow_def_of_ne_zero hxc, Complex.cpow_def_of_ne_zero hxc,
    ← Complex.exp_conj, map_mul]
  congr 2
  rw [← Complex.ofReal_log hx.le]
  exact Complex.conj_ofReal _

private theorem reciprocalMellin_changeOfVariables
    (W : CompactBVPrimeWindow) (s : ℂ) :
    (∫ x in W.upper⁻¹ / 2..2 * W.lower⁻¹,
      (starRingEnd ℂ) (W x⁻¹) * (x : ℂ) ^ (-s)) =
      ∫ u in W.lower / 2..2 * W.upper,
        (starRingEnd ℂ) (W u) * (u : ℂ) ^ (s - 2) := by
  let A : ℝ := W.upper⁻¹ / 2
  let B : ℝ := 2 * W.lower⁻¹
  let f : ℝ → ℝ := fun x => x⁻¹
  let f' : ℝ → ℝ := fun x => -(x ^ 2)⁻¹
  let g : ℝ → ℂ := fun u => (starRingEnd ℂ) (W u) * (u : ℂ) ^ (s - 2)
  have hA : 0 < A := by
    dsimp only [A]
    exact div_pos (inv_pos.mpr W.upper_pos) (by norm_num)
  have hB : 0 < B := by
    dsimp only [B]
    exact mul_pos (by norm_num) (inv_pos.mpr W.lower_pos)
  have hAB : A ≤ B := by
    dsimp only [A, B]
    have hInv : W.upper⁻¹ < W.lower⁻¹ := by
      exact (inv_lt_inv₀ W.upper_pos W.lower_pos).2 W.lower_lt_upper
    nlinarith [inv_pos.mpr W.upper_pos, inv_pos.mpr W.lower_pos]
  have hfcont : ContinuousOn f (uIcc A B) := by
    exact continuousOn_inv₀.mono (by
      intro x hx
      rw [uIcc_of_le hAB] at hx
      exact ne_of_gt (hA.trans_le hx.1))
  have hfderiv : ∀ x ∈ Set.Ioo (min A B) (max A B), HasDerivAt f (f' x) x := by
    intro x hx
    apply hasDerivAt_inv
    rw [min_eq_left hAB, max_eq_right hAB] at hx
    exact ne_of_gt (hA.trans hx.1)
  have hfnonpos : ∀ x ∈ Set.Ioo (min A B) (max A B), f' x ≤ 0 := by
    intro x hx
    exact neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg x))
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
    (g := g) hfcont hfderiv hfnonpos
  have hpoint : ∀ x ∈ uIcc A B,
      f' x • (g ∘ f) x =
        -((starRingEnd ℂ) (W x⁻¹) * (x : ℂ) ^ (-s)) := by
    intro x hx
    rw [uIcc_of_le hAB] at hx
    have hxpos : 0 < x := hA.trans_le hx.1
    have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hxpos.ne'
    have harg : (x : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hxpos.le]
      exact ne_of_lt Real.pi_pos
    have hinvpow : (((x⁻¹ : ℝ) : ℂ) ^ (s - 2)) = (x : ℂ) ^ (2 - s) := by
      rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
      congr 1
      ring
    rw [Complex.ofReal_inv] at hinvpow
    simp only [f, f', g, Function.comp_apply, real_smul, Complex.ofReal_neg,
      Complex.ofReal_inv, Complex.ofReal_pow]
    rw [hinvpow]
    rw [show (2 - s : ℂ) = 2 + (-s) by ring, Complex.cpow_add _ _ hxC]
    norm_num only [Complex.cpow_ofNat]
    field_simp [hxC]
  have hderivInt :
      (∫ x in A..B, f' x • (g ∘ f) x) =
        -(∫ x in A..B, (starRingEnd ℂ) (W x⁻¹) * (x : ℂ) ^ (-s)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    exact hpoint x hx
  have hAinv : A⁻¹ = 2 * W.upper := by
    dsimp only [A]
    field_simp [W.upper_pos.ne']
  have hBinv : B⁻¹ = W.lower / 2 := by
    dsimp only [B]
    field_simp [W.lower_pos.ne']
  change (∫ x in A..B, (starRingEnd ℂ) (W x⁻¹) * (x : ℂ) ^ (-s)) = _
  calc
    (∫ x in A..B, (starRingEnd ℂ) (W x⁻¹) * (x : ℂ) ^ (-s)) =
        -(∫ x in A..B, f' x • (g ∘ f) x) := by rw [hderivInt]; ring
    _ = -(∫ u in f A..f B, g u) := by rw [hsub]
    _ = ∫ u in f B..f A, g u :=
      (intervalIntegral.integral_symm (f := g) (a := f A) (b := f B)).symm
    _ = ∫ u in W.lower / 2..2 * W.upper,
        (starRingEnd ℂ) (W u) * (u : ℂ) ^ (s - 2) := by
      rw [show f A = A⁻¹ by rfl, show f B = B⁻¹ by rfl, hAinv, hBinv]

/-- Exact Mellin reflection of the reciprocal-conjugate compact BV source. -/
theorem mellinTransform_reciprocalConjugate
    (W : CompactBVPrimeWindow) (s : ℂ) :
    W.reciprocalConjugate.mellinTransform s =
      (starRingEnd ℂ) (W.mellinTransform (2 - (starRingEnd ℂ) s)) := by
  have hleftSupport : Function.support (W.reciprocalConjugate.mellinIntegrand s) ⊆
      Set.Ioc (W.upper⁻¹ / 2) (2 * W.lower⁻¹) := by
    intro x hx
    have hxmem := W.reciprocalConjugate.support_mellinIntegrand_subset s hx
    constructor
    · have huinv : 0 < W.upper⁻¹ := inv_pos.mpr W.upper_pos
      exact lt_of_lt_of_le (by linarith : W.upper⁻¹ / 2 < W.upper⁻¹) hxmem.1
    · have hlinv : 0 < W.lower⁻¹ := inv_pos.mpr W.lower_pos
      exact hxmem.2.trans (by linarith : W.lower⁻¹ ≤ 2 * W.lower⁻¹)
  have hrightSupport : Function.support
      (fun u : ℝ => (starRingEnd ℂ) (W u) * (u : ℂ) ^ (s - 2)) ⊆
      Set.Ioc (W.lower / 2) (2 * W.upper) := by
    intro u hu
    have hWu : W u ≠ 0 := by
      intro h
      apply hu
      simp [h]
    have humem : u ∈ Set.Icc W.lower W.upper := by
      by_contra hmem
      exact hWu (W.eq_zero_off_support u hmem)
    constructor
    · exact lt_of_lt_of_le (by linarith [W.lower_pos] : W.lower / 2 < W.lower) humem.1
    · exact humem.2.trans (by linarith [W.upper_pos] : W.upper ≤ 2 * W.upper)
  calc
    W.reciprocalConjugate.mellinTransform s =
        ∫ x in W.upper⁻¹ / 2..2 * W.lower⁻¹,
          W.reciprocalConjugate.mellinIntegrand s x := by
      rw [mellinTransform]
      exact (intervalIntegral.integral_eq_integral_of_support_subset hleftSupport).symm
    _ = ∫ x in W.upper⁻¹ / 2..2 * W.lower⁻¹,
          (starRingEnd ℂ) (W x⁻¹) * (x : ℂ) ^ (-s) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact W.reciprocalConjugate.mellinIntegrand_eq_raw s x
    _ = ∫ u in W.lower / 2..2 * W.upper,
          (starRingEnd ℂ) (W u) * (u : ℂ) ^ (s - 2) :=
      reciprocalMellin_changeOfVariables W s
    _ = ∫ u : ℝ, (starRingEnd ℂ) (W u) * (u : ℂ) ^ (s - 2) :=
      intervalIntegral.integral_eq_integral_of_support_subset hrightSupport
    _ = (starRingEnd ℂ) (W.mellinTransform (2 - (starRingEnd ℂ) s)) := by
      rw [mellinTransform, ← integral_conj]
      apply integral_congr_ae
      filter_upwards with u
      by_cases hW : W u = 0
      · rw [W.mellinIntegrand_eq_raw]
        simp [hW]
      · have huMem : u ∈ Set.Icc W.lower W.upper := by
          by_contra hmem
          exact hW (W.eq_zero_off_support u hmem)
        have hu : 0 < u := W.lower_pos.trans_le huMem.1
        rw [W.mellinIntegrand_eq_raw, map_mul, conj_ofReal_cpow hu]
        have hexp :
            (starRingEnd ℂ) (-(2 - (starRingEnd ℂ) s)) = s - 2 := by
          have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
            simpa using Complex.conj_ofReal 2
          rw [map_neg, map_sub, htwo, Complex.conj_conj]
          ring
        rw [hexp]

end CompactBVPrimeWindow

/-- Pole-filled zeta multiplicity is preserved by functional-equation reflection followed by
Schwarz conjugation throughout the open critical strip. -/
theorem analyticOrderAt_regularizedRiemannZeta_one_sub_conj
    {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    analyticOrderAt regularizedRiemannZeta (1 - (starRingEnd ℂ) rho) =
      analyticOrderAt regularizedRiemannZeta rho := by
  have hrho1 : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at h1
  have hconj1 : (starRingEnd ℂ) rho ≠ 1 := by
    intro h
    have := congrArg (starRingEnd ℂ) h
    exact hrho1 (by simpa using this)
  have href1 : 1 - (starRingEnd ℂ) rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  rw [analyticOrderAt_regularizedRiemannZeta_eq_riemannZeta href1,
    analyticOrderAt_regularizedRiemannZeta_eq_riemannZeta hrho1]
  calc
    analyticOrderAt riemannZeta (1 - (starRingEnd ℂ) rho) =
        analyticOrderAt riemannZeta ((starRingEnd ℂ) rho) :=
      analyticOrderAt_riemannZeta_one_sub (by simpa using h0) (by simpa using h1)
    _ = analyticOrderAt riemannZeta rho :=
      analyticOrderAt_conj_of_conjEquivariant riemannZeta_conj
        (analyticOn_riemannZeta rho hrho1)
        (analyticOn_riemannZeta ((starRingEnd ℂ) rho) hconj1)

namespace CompactBVPrimeWindow

/-- Reciprocal source reflection conjugates the exact continued-source residue at the
functional-equation reflected point. -/
theorem continuedSourceResidueValue_reciprocalConjugate
    (W : CompactBVPrimeWindow) {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    W.reciprocalConjugate.continuedSourceResidueValue
        (1 - (starRingEnd ℂ) rho) =
      (starRingEnd ℂ) (W.continuedSourceResidueValue rho) := by
  rw [continuedSourceResidueValue, continuedSourceResidueValue,
    mellinTransform_reciprocalConjugate,
    analyticOrderAt_regularizedRiemannZeta_one_sub_conj h0 h1]
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simpa using Complex.conj_ofReal 2
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, htwo]
  have hcoord :
      2 - (starRingEnd ℂ) ((1 - (starRingEnd ℂ) rho) + 1 / 2) =
        rho + 1 / 2 := by
    rw [map_add, map_sub, map_one, Complex.conj_conj, hhalf]
    ring
  rw [hcoord, map_mul, map_mul]
  rw [htwo]
  simp only [map_natCast]

/-- Formula `(14)`, first channel: reflected reciprocal expansion is the conjugate of the
original positive-dilation residue. -/
theorem continuedSourceResidueValue_reciprocalConjugate_argumentExpansion
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r)
    {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    (W.reciprocalConjugate.argumentExpansion r hr).continuedSourceResidueValue
        (1 - (starRingEnd ℂ) rho) =
      (starRingEnd ℂ)
        ((W.argumentDilation r hr).continuedSourceResidueValue rho) := by
  rw [continuedSourceResidueValue_argumentExpansion,
    continuedSourceResidueValue_argumentDilation,
    continuedSourceResidueValue_reciprocalConjugate W h0 h1,
    map_mul, conj_ofReal_cpow hr]
  congr 2
  rw [map_sub]
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simpa using Complex.conj_ofReal 2
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, htwo]
  rw [hhalf]
  ring

/-- Formula `(14)`, second channel: reflected positive dilation is the conjugate of the
original reciprocal-expansion residue. -/
theorem continuedSourceResidueValue_reciprocalConjugate_argumentDilation
    (W : CompactBVPrimeWindow) (r : ℝ) (hr : 0 < r)
    {rho : ℂ} (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    (W.reciprocalConjugate.argumentDilation r hr).continuedSourceResidueValue
        (1 - (starRingEnd ℂ) rho) =
      (starRingEnd ℂ)
        ((W.argumentExpansion r hr).continuedSourceResidueValue rho) := by
  rw [continuedSourceResidueValue_argumentDilation,
    continuedSourceResidueValue_argumentExpansion,
    continuedSourceResidueValue_reciprocalConjugate W h0 h1,
    map_mul, conj_ofReal_cpow hr]
  congr 2
  rw [map_sub]
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    simpa using Complex.conj_ofReal 2
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, htwo]
  rw [hhalf]
  ring

end CompactBVPrimeWindow

end RHTower
