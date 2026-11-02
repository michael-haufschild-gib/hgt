import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.OddLogarithmicPairGap
import GaloisForLFunctions.BiScaleUncertainty.KreinIncrementAndChordCascade
import GaloisForLFunctions.RHTower.CHMDCompactSourceClass

/-!
# The interior logarithmic jumps of an odd test

For an odd compact `C²` test supported in `[-a,a]`, its autocorrelation `A`
satisfies `∫₀²ᵃ (A(0)-A(t))/t dt ≥ (log 2+7/5) A(0)`.
Fubini turns the lag count into a symmetric pair count. Reflection gives
the principal odd kernel; jumps leaving the support give the exact exterior
charge. The cubic ground-state bound then applies, and dilation removes the
normalization `a=1`.
-/

open Real MeasureTheory Set
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section

namespace GaloisForLFunctions.LatticeSectionTheory

/-- Logarithmic jumps of length at most two. The diagonal has weight zero. -/
def logarithmicJumpKernel (t : ℝ) : ℝ := if |t| ≤ 2 then |t|⁻¹ else 0

private theorem measurable_logarithmicJumpKernel : Measurable logarithmicJumpKernel :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    continuous_abs.measurable.inv measurable_const

/-- The unnormalized pair count of truncated logarithmic jumps. -/
def logarithmicJumpPair (F : ℝ → ℝ) (x y : ℝ) : ℝ :=
  logarithmicJumpKernel (y - x) * (F x - F y) ^ 2

private theorem measurable_logarithmicJumpPair {F : ℝ → ℝ} (hFc : Continuous F) :
    Measurable (fun p : ℝ × ℝ => logarithmicJumpPair F p.1 p.2) :=
  (measurable_logarithmicJumpKernel.comp (measurable_snd.sub measurable_fst)).mul
    (((hFc.measurable.comp measurable_fst).sub (hFc.measurable.comp measurable_snd)).pow_const 2)

private theorem logarithmicJumpPair_nonneg (F : ℝ → ℝ) (x y : ℝ) :
    0 ≤ logarithmicJumpPair F x y := by
  unfold logarithmicJumpPair logarithmicJumpKernel
  split_ifs <;> positivity

private theorem logarithmicJumpPair_comm (F : ℝ → ℝ) (x y : ℝ) :
    logarithmicJumpPair F x y = logarithmicJumpPair F y x := by
  unfold logarithmicJumpPair logarithmicJumpKernel
  rw [abs_sub_comm]
  ring

private theorem logarithmicJumpPair_bound {F : ℝ → ℝ} {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|) (x y : ℝ) :
    |logarithmicJumpPair F x y| ≤ 2 * K ^ 2 := by
  by_cases he : x = y
  · simp only [he, logarithmicJumpPair, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, abs_zero]
    positivity
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr he)
  have hf : (F x - F y) ^ 2 ≤ K ^ 2 * |x - y| ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (F x - F y)) (hFL x y) 2
    simpa only [sq_abs, mul_pow] using h
  unfold logarithmicJumpPair logarithmicJumpKernel
  rw [abs_sub_comm]
  split_ifs with hxy
  · rw [abs_of_nonneg (by positivity)]
    calc
      |x - y|⁻¹ * (F x - F y) ^ 2 ≤ |x - y|⁻¹ * (K ^ 2 * |x - y| ^ 2) :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ = K ^ 2 * |x - y| := by field_simp
      _ ≤ 2 * K ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hxy (sq_nonneg K)]
  · simp only [zero_mul, abs_zero]
    positivity

private theorem logarithmicJumpPair_zero_left {F : ℝ → ℝ}
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) {x y : ℝ} (hx : 3 < |x|) :
    logarithmicJumpPair F x y = 0 := by
  have hFx : F x = 0 := hFs x (by linarith only [hx])
  unfold logarithmicJumpPair logarithmicJumpKernel
  split_ifs with hxy
  · have hy : 1 ≤ |y| := by
      have h := abs_add_le (x - y) y
      rw [sub_add_cancel, abs_sub_comm] at h
      linarith only [h, hx, hxy]
    rw [hFx, hFs y hy, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · exact zero_mul _

private theorem integrable_on_cube {G : ℝ × ℝ → ℝ} {C : ℝ}
    (hm : Measurable G) (hb : ∀ p, |G p| ≤ C)
    (hz : ∀ p, p ∉ (Icc (-3 : ℝ) 3 ×ˢ Icc (-3 : ℝ) 3) → G p = 0) :
    Integrable G (volume.prod volume) := by
  have he : G = (Icc (-3 : ℝ) 3 ×ˢ Icc (-3 : ℝ) 3).indicator G := by
    funext p
    by_cases hp : p ∈ (Icc (-3 : ℝ) 3 ×ˢ Icc (-3 : ℝ) 3)
    · exact (Set.indicator_of_mem hp G).symm
    · rw [Set.indicator_of_notMem hp, hz p hp]
  rw [he, integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)]
  have hfin : (volume.prod volume) (Icc (-3 : ℝ) 3 ×ˢ Icc (-3 : ℝ) 3) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact (ENNReal.mul_lt_top measure_Icc_lt_top measure_Icc_lt_top).ne
  refine Measure.integrableOn_of_bounded (M := C) hfin hm.aestronglyMeasurable ?_
  filter_upwards with p
  rw [Real.norm_eq_abs]
  exact hb p

private theorem integrable_logarithmicJumpPair {F : ℝ → ℝ} (hFc : Continuous F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) :
    Integrable (fun p : ℝ × ℝ => logarithmicJumpPair F p.1 p.2) (volume.prod volume) := by
  apply integrable_on_cube (C := 2 * K ^ 2)
  · exact measurable_logarithmicJumpPair hFc
  · intro p
    exact logarithmicJumpPair_bound hFL p.1 p.2
  · intro p hp
    have h : 3 < |p.1| ∨ 3 < |p.2| := by
      by_contra hn
      push Not at hn
      exact hp ⟨(abs_le.mp hn.1), (abs_le.mp hn.2)⟩
    rcases h with hx | hy
    · exact logarithmicJumpPair_zero_left hFs hx
    · rw [logarithmicJumpPair_comm]
      exact logarithmicJumpPair_zero_left hFs hy

private theorem integrable_logarithmicJumpShift {F : ℝ → ℝ} (hFc : Continuous F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) :
    Integrable (fun p : ℝ × ℝ => logarithmicJumpPair F p.1 (p.1 + p.2)) (volume.prod volume) := by
  apply integrable_on_cube (C := 2 * K ^ 2)
  · exact (measurable_logarithmicJumpPair hFc).comp
      (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  · intro p
    exact logarithmicJumpPair_bound hFL p.1 (p.1 + p.2)
  · intro p hp
    have h : 3 < |p.1| ∨ 3 < |p.2| := by
      by_contra hn
      push Not at hn
      exact hp ⟨abs_le.mp hn.1, abs_le.mp hn.2⟩
    rcases h with hx | ht
    · exact logarithmicJumpPair_zero_left hFs hx
    · unfold logarithmicJumpPair logarithmicJumpKernel
      rw [add_sub_cancel_left, if_neg (by linarith only [ht]), zero_mul]

private theorem compactSupport_of_unit_window {F : ℝ → ℝ}
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) : HasCompactSupport F := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx => ?_
  exact hFs x (le_of_lt (lt_of_not_ge fun h => hx (abs_le.mp h)))

/-- Lag and pair counts agree, including all jumps leaving the support interval. -/
theorem logarithmic_pair_eq_lag {F : ℝ → ℝ} (hFc : Continuous F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) :
    (∫ p : ℝ × ℝ, logarithmicJumpPair F p.1 p.2 ∂(volume.prod volume)) =
      4 * ∫ t in Ioc (0 : ℝ) 2, (autocorr F 0 - autocorr F t) / t := by
  have hIH := integrable_logarithmicJumpPair hFc hFL hFs
  have hIL := integrable_logarithmicJumpShift hFc hFL hFs
  have hcs := compactSupport_of_unit_window hFs
  let g : ℝ → ℝ := fun t => logarithmicJumpKernel t * (2 * (autocorr F 0 - autocorr F t))
  have htrans : ∀ x, (∫ y, logarithmicJumpPair F x y) =
      ∫ t, logarithmicJumpPair F x (x + t) := by
    intro x
    calc
      (∫ y, logarithmicJumpPair F x y) = ∫ t, logarithmicJumpPair F x (t + x) :=
        (integral_add_right_eq_self (fun y => logarithmicJumpPair F x y) x).symm
      _ = ∫ t, logarithmicJumpPair F x (x + t) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [add_comm]
  have hinner : ∀ t, (∫ x, logarithmicJumpPair F x (x + t)) = g t := by
    intro t
    simp only [logarithmicJumpPair, add_sub_cancel_left]
    rw [integral_const_mul, integral_sub_shift_sq hcs hFc t]
  have hQ : (∫ p : ℝ × ℝ, logarithmicJumpPair F p.1 p.2 ∂(volume.prod volume)) = ∫ t, g t := by
    rw [← integral_integral (f := fun x y => logarithmicJumpPair F x y) hIH]
    rw [integral_congr_ae (Filter.Eventually.of_forall htrans),
      integral_integral_swap (f := fun x t => logarithmicJumpPair F x (x + t)) hIL]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)
  have heven : ∀ t, g (-t) = g t := by
    intro t
    dsimp [g, logarithmicJumpKernel]
    rw [abs_neg, autocorr_neg]
  have habs : ∀ t, g |t| = g t := by
    intro t
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, heven]
  have hhalf : (∫ t, g t) = 2 * ∫ t in Ioi (0 : ℝ), g t := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall habs), integral_comp_abs]
  have hcut : (∫ t in Ioi (0 : ℝ), g t) =
      2 * ∫ t in Ioc (0 : ℝ) 2, (autocorr F 0 - autocorr F t) / t := by
    have he : ∀ t ∈ Ioi (0 : ℝ), g t =
        (Iic (2 : ℝ)).indicator (fun t => 2 * ((autocorr F 0 - autocorr F t) / t)) t := by
      intro t ht
      have ht0 : 0 < t := Set.mem_Ioi.mp ht
      simp only [g, logarithmicJumpKernel, abs_of_pos ht0, Set.indicator_apply, mem_Iic]
      split_ifs <;> ring
    rw [setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Iic,
      Ioi_inter_Iic, integral_const_mul]
  rw [hQ, hhalf, hcut]
  ring

private theorem integrable_bounded_window {g : ℝ → ℝ} {C : ℝ}
    (hm : Measurable g) (hb : ∀ x, |g x| ≤ C)
    (hz : ∀ x, 3 < |x| → g x = 0) : Integrable g := by
  have he : g = (Icc (-3 : ℝ) 3).indicator g := by
    funext x
    by_cases hx : x ∈ Icc (-3 : ℝ) 3
    · exact (Set.indicator_of_mem hx g).symm
    · rw [Set.indicator_of_notMem hx, hz x (lt_of_not_ge fun h => hx (abs_le.mp h))]
  rw [he, integrable_indicator_iff measurableSet_Icc]
  refine Measure.integrableOn_of_bounded (M := C) (by simp) hm.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact hb x

private theorem integrable_logarithmicJumpPair_row {F : ℝ → ℝ}
    (hFc : Continuous F) {K : ℝ} (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) (x : ℝ) :
    Integrable (logarithmicJumpPair F x) := by
  apply integrable_bounded_window (C := 2 * K ^ 2)
  · exact (measurable_logarithmicJumpPair hFc).comp (measurable_const.prodMk measurable_id)
  · exact logarithmicJumpPair_bound hFL x
  · intro y hy
    rw [logarithmicJumpPair_comm]
    exact logarithmicJumpPair_zero_left hFs hy

private theorem logarithmicJumpPair_reflect {F : ℝ → ℝ}
    (hFo : ∀ x, F (-x) = -F x) (x y : ℝ) :
    logarithmicJumpPair F (-x) (-y) = logarithmicJumpPair F x y := by
  unfold logarithmicJumpPair logarithmicJumpKernel
  rw [show -y - -x = -(y - x) by ring, abs_neg, hFo, hFo]
  split_ifs <;> ring

private theorem integral_pos_add_neg {g : ℝ → ℝ} (hg : Integrable g)
    (hgn : Integrable (fun x => g (-x))) :
    (∫ x, g x) = ∫ x in Ioi (0 : ℝ), g x + g (-x) := by
  rw [integral_add hg.integrableOn hgn.integrableOn]
  have hn : (∫ x in Ioi (0 : ℝ), g (-x)) = ∫ x in Iic (0 : ℝ), g x := by
    simpa only [neg_zero] using integral_comp_neg_Ioi 0 g
  rw [hn, ← compl_Ioi, integral_add_compl measurableSet_Ioi hg]

/-- Folding an odd test pairs same-side differences with crossing sums. -/
theorem logarithmic_pair_eq_positive_fold {F : ℝ → ℝ} (hFc : Continuous F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) (hFo : ∀ x, F (-x) = -F x) :
    (∫ p : ℝ × ℝ, logarithmicJumpPair F p.1 p.2 ∂(volume.prod volume)) =
      2 * ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
        logarithmicJumpPair F x y + logarithmicJumpPair F x (-y) := by
  have hIH := integrable_logarithmicJumpPair hFc hFL hFs
  let row : ℝ → ℝ := fun x => ∫ y, logarithmicJumpPair F x y
  have hrow : ∀ x, row (-x) = row x := by
    intro x
    calc
      row (-x) = ∫ y, logarithmicJumpPair F (-x) (-y) :=
        (integral_neg_eq_self (fun y => logarithmicJumpPair F (-x) y) volume).symm
      _ = row x := integral_congr_ae (Filter.Eventually.of_forall fun y =>
        logarithmicJumpPair_reflect hFo x y)
  have habs : ∀ x, row |x| = row x := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, hrow]
  have hfold : (∫ x, row x) = 2 * ∫ x in Ioi (0 : ℝ), row x := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall habs), integral_comp_abs]
  rw [← integral_integral (f := fun x y => logarithmicJumpPair F x y) hIH]
  change (∫ x, row x) = _
  rw [hfold]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  have hi := integrable_logarithmicJumpPair_row hFc hFL hFs x
  have hin : Integrable (fun y => logarithmicJumpPair F x (-y)) := by
    apply integrable_bounded_window (C := 2 * K ^ 2)
    · exact (measurable_logarithmicJumpPair hFc).comp
        (measurable_const.prodMk measurable_id.neg)
    · intro y
      exact logarithmicJumpPair_bound hFL x (-y)
    · intro y hy
      rw [logarithmicJumpPair_comm]
      exact logarithmicJumpPair_zero_left hFs (by simpa only [abs_neg] using hy)
  exact integral_pos_add_neg hi hin

private def foldedPair (F : ℝ → ℝ) (x y : ℝ) : ℝ :=
  logarithmicJumpPair F x y + logarithmicJumpPair F x (-y)

private theorem measurable_foldedPair {F : ℝ → ℝ} (hFc : Continuous F) :
    Measurable (fun p : ℝ × ℝ => foldedPair F p.1 p.2) :=
  (measurable_logarithmicJumpPair hFc).add
    ((measurable_logarithmicJumpPair hFc).comp (measurable_fst.prodMk measurable_snd.neg))

private theorem foldedPair_eq {F : ℝ → ℝ} (hFo : ∀ x, F (-x) = -F x) (x y : ℝ) :
    foldedPair F x y = logarithmicJumpKernel (y - x) * (F x - F y) ^ 2 +
      logarithmicJumpKernel (x + y) * (F x + F y) ^ 2 := by
  unfold foldedPair logarithmicJumpPair logarithmicJumpKernel
  rw [hFo, show -y - x = -(x + y) by ring, abs_neg]
  simp only [sub_neg_eq_add]

private theorem foldedPair_comm {F : ℝ → ℝ} (hFo : ∀ x, F (-x) = -F x) (x y : ℝ) :
    foldedPair F x y = foldedPair F y x := by
  rw [foldedPair_eq hFo, foldedPair_eq hFo]
  unfold logarithmicJumpKernel
  rw [abs_sub_comm, add_comm y x, add_comm (F y) (F x)]
  ring

private theorem foldedPair_bound {F : ℝ → ℝ} {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|) (x y : ℝ) :
    |foldedPair F x y| ≤ 4 * K ^ 2 := by
  exact (abs_add_le _ _).trans (by
    linarith only [logarithmicJumpPair_bound hFL x y, logarithmicJumpPair_bound hFL x (-y)])

private theorem foldedPair_zero_right {F : ℝ → ℝ}
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) {x y : ℝ} (hy : 3 < |y|) :
    foldedPair F x y = 0 := by
  unfold foldedPair
  rw [logarithmicJumpPair_comm F x y, logarithmicJumpPair_comm F x (-y),
    logarithmicJumpPair_zero_left hFs hy,
    logarithmicJumpPair_zero_left hFs (by simpa only [abs_neg] using hy)]
  exact zero_add _

private theorem integrable_foldedPair {F : ℝ → ℝ} (hFc : Continuous F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) :
    Integrable (fun p : ℝ × ℝ => foldedPair F p.1 p.2) (volume.prod volume) := by
  apply integrable_on_cube (C := 4 * K ^ 2)
  · exact measurable_foldedPair hFc
  · intro p
    exact foldedPair_bound hFL p.1 p.2
  · intro p hp
    have h : 3 < |p.1| ∨ 3 < |p.2| := by
      by_contra hn
      push Not at hn
      exact hp ⟨abs_le.mp hn.1, abs_le.mp hn.2⟩
    rcases h with hx | hy
    · unfold foldedPair
      rw [logarithmicJumpPair_zero_left hFs hx, logarithmicJumpPair_zero_left hFs hx, zero_add]
    · exact foldedPair_zero_right hFs hy

private theorem integrable_foldedPair_row {F : ℝ → ℝ} (hFc : Continuous F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) (x : ℝ) : Integrable (foldedPair F x) := by
  apply integrable_bounded_window (C := 4 * K ^ 2)
  · exact (measurable_foldedPair hFc).comp (measurable_const.prodMk measurable_id)
  · exact foldedPair_bound hFL x
  · intro y hy
    exact foldedPair_zero_right hFs hy

private theorem positive_square_split {D : ℝ → ℝ → ℝ}
    (hI : Integrable (fun p : ℝ × ℝ => D p.1 p.2) (volume.prod volume))
    (hrow : ∀ x, Integrable (D x)) (hcomm : ∀ x y, D x y = D y x)
    (hz : ∀ x, 1 < x → ∀ y, 1 < y → D x y = 0) :
    (∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), D x y) =
      (∫ x in Ioc (0 : ℝ) 1, ∫ y in Ioc (0 : ℝ) 1, D x y) +
        2 * ∫ x in Ioc (0 : ℝ) 1, ∫ y in Ioi (1 : ℝ), D x y := by
  have hqs : Integrable (fun p : ℝ × ℝ => D p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hI.restrict
  have hqt : Integrable (fun p : ℝ × ℝ => D p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (1 : ℝ)))) := by
    rw [Measure.prod_restrict]
    exact hI.restrict
  have hts : Integrable (fun p : ℝ × ℝ => D p.1 p.2)
      ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hI.restrict
  have hqs0 : IntegrableOn (fun x => ∫ y in Ioc (0 : ℝ) 1, D x y) (Ioi (0 : ℝ)) :=
    hqs.integral_prod_left
  have hqt0 : IntegrableOn (fun x => ∫ y in Ioi (1 : ℝ), D x y) (Ioi (0 : ℝ)) :=
    hqt.integral_prod_left
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact lt_trans zero_lt_one h
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
  have hdis : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1.2 h2
  have hs : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := fun _ h => h.1
  have ht : Ioi (1 : ℝ) ⊆ Ioi 0 := fun _ h =>
    Set.mem_Ioi.mpr (lt_trans zero_lt_one (Set.mem_Ioi.mp h))
  have hinner : ∀ x, (∫ y in Ioi (0 : ℝ), D x y) =
      (∫ y in Ioc (0 : ℝ) 1, D x y) + ∫ y in Ioi (1 : ℝ), D x y := by
    intro x
    rw [← hunion, setIntegral_union hdis measurableSet_Ioi
      (hrow x).integrableOn (hrow x).integrableOn]
  have hos : (∫ x in Ioi (0 : ℝ), ∫ y in Ioc (0 : ℝ) 1, D x y) =
      (∫ x in Ioc (0 : ℝ) 1, ∫ y in Ioc (0 : ℝ) 1, D x y) +
      ∫ x in Ioi (1 : ℝ), ∫ y in Ioc (0 : ℝ) 1, D x y := by
    rw [← hunion, setIntegral_union hdis measurableSet_Ioi
      (hqs0.mono_set hs) (hqs0.mono_set ht)]
  have hot : (∫ x in Ioi (0 : ℝ), ∫ y in Ioi (1 : ℝ), D x y) =
      (∫ x in Ioc (0 : ℝ) 1, ∫ y in Ioi (1 : ℝ), D x y) +
      ∫ x in Ioi (1 : ℝ), ∫ y in Ioi (1 : ℝ), D x y := by
    rw [← hunion, setIntegral_union hdis measurableSet_Ioi
      (hqt0.mono_set hs) (hqt0.mono_set ht)]
  have hswap : (∫ x in Ioi (1 : ℝ), ∫ y in Ioc (0 : ℝ) 1, D x y) =
      ∫ x in Ioc (0 : ℝ) 1, ∫ y in Ioi (1 : ℝ), D x y := by
    rw [integral_integral_swap (f := D) hts]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ => hcomm y x
  have hzero : (∫ x in Ioi (1 : ℝ), ∫ y in Ioi (1 : ℝ), D x y) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact setIntegral_eq_zero_of_forall_eq_zero fun y hy => hz x hx y hy
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hinner x),
    integral_add hqs0 hqt0, hos, hot, hswap, hzero]
  ring

private theorem right_exterior_log_integral {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    IntegrableOn (fun y => logarithmicJumpKernel (y - x)) (Ioi (1 : ℝ)) ∧
      (∫ y in Ioi (1 : ℝ), logarithmicJumpKernel (y - x)) =
        Real.log 2 - Real.log (1 - x) := by
  have hden : 0 < 1 - x := sub_pos.mpr hx1
  have hm : Measurable (fun y => (Ioi (1 : ℝ)).indicator
      (fun y => logarithmicJumpKernel (y - x)) y) :=
    (measurable_logarithmicJumpKernel.comp (measurable_id.sub measurable_const)).indicator
      measurableSet_Ioi
  have hi : Integrable (fun y => (Ioi (1 : ℝ)).indicator
      (fun y => logarithmicJumpKernel (y - x)) y) := by
    apply integrable_bounded_window hm (C := (1 - x)⁻¹)
    · intro y
      by_cases hy : 1 < y
      · have hp : 0 < y - x := by linarith only [hy, hx1]
        rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hy)]
        unfold logarithmicJumpKernel
        rw [abs_of_pos hp]
        split_ifs with h2
        · rw [abs_of_nonneg (by positivity)]
          simpa only [one_div] using one_div_le_one_div_of_le hden
            (show 1 - x ≤ y - x by linarith only [hy])
        · rw [abs_zero]
          positivity
      · rw [Set.indicator_of_notMem (show y ∉ Ioi (1 : ℝ) from fun h => hy (Set.mem_Ioi.mp h)), abs_zero]
        positivity
    · intro y hy
      by_cases hy1 : 1 < y
      · have hy3 : 3 < y := by rwa [abs_of_pos (by linarith only [hy1])] at hy
        rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hy1)]
        unfold logarithmicJumpKernel
        rw [abs_of_pos (show 0 < y - x by linarith only [hy3, hx1]),
          if_neg (by linarith only [hy3, hx1])]
      · exact Set.indicator_of_notMem (show y ∉ Ioi (1 : ℝ) from fun h => hy1 (Set.mem_Ioi.mp h)) _
  refine ⟨(integrable_indicator_iff measurableSet_Ioi).mp hi, ?_⟩
  have he : ∀ y ∈ Ioi (1 : ℝ), logarithmicJumpKernel (y - x) =
      (Iic (x + 2)).indicator (fun y => 1 / (y - x)) y := by
    intro y hy
    have hy1 : 1 < y := Set.mem_Ioi.mp hy
    have hp : 0 < y - x := by linarith only [hy1, hx1]
    simp only [logarithmicJumpKernel, abs_of_pos hp, Set.indicator_apply, mem_Iic, one_div]
    congr 1
    exact propext (by constructor <;> intro h <;> linarith only [h])
  rw [setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Iic,
    Ioi_inter_Iic, ← intervalIntegral.integral_of_le (show 1 ≤ x + 2 by linarith only [hx0])]
  have h := ArithmeticIncidencePositivity.integral_quartic_sub_log
    (x := -x) (a := 1) (b := x + 2) (c₀ := 0) (c₁ := 0) (c₂ := 0) (c₃ := 0) (c₄ := 0)
    (K := -1) (by linarith only [hx0]) (by linarith only [hx1])
  simp only [zero_mul, zero_add, zero_sub, neg_one_mul, neg_neg,
    show -x + (x + 2) = 2 by ring, show -x + 1 = 1 - x by ring] at h
  convert h using 1
  apply intervalIntegral.integral_congr
  intro y _
  ring

private theorem foldedPair_exterior_integral {F : ℝ → ℝ}
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∫ y in Ioi (1 : ℝ), foldedPair F x y) =
      F x ^ 2 * (2 * Real.log 2 - Real.log (1 - x) - Real.log (1 + x)) := by
  obtain ⟨hI1, he1⟩ := right_exterior_log_integral (show -1 < x by linarith only [hx.1]) hx.2
  obtain ⟨hI2, he2⟩ := right_exterior_log_integral
    (x := -x) (by linarith only [hx.2]) (by linarith only [hx.1])
  have he : ∀ y ∈ Ioi (1 : ℝ), foldedPair F x y =
      F x ^ 2 * (logarithmicJumpKernel (y - x) + logarithmicJumpKernel (y - -x)) := by
    intro y hy
    have hy0 : 0 < y := lt_trans zero_lt_one hy
    have hFy := hFs y (by rw [abs_of_pos hy0]; exact hy.le)
    have hFny := hFs (-y) (by rw [abs_neg, abs_of_pos hy0]; exact hy.le)
    unfold foldedPair logarithmicJumpPair logarithmicJumpKernel
    rw [hFy, hFny, sub_zero, show -y - x = -(y - -x) by ring, abs_neg]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
    integral_add hI1 hI2, he1, he2, show 1 - -x = 1 + x by ring]
  ring

private theorem integral_inv_add_unit {x : ℝ} (hx : 0 < x) :
    (∫ y in Ioo (0 : ℝ) 1, 1 / (x + y)) = Real.log (x + 1) - Real.log x := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have h := ArithmeticIncidencePositivity.integral_quartic_sub_log
    (x := x) (a := 0) (b := 1) (c₀ := 0) (c₁ := 0) (c₂ := 0) (c₃ := 0) (c₄ := 0)
    (K := -1) zero_le_one (by simpa only [add_zero] using hx)
  simpa only [zero_mul, mul_zero, zero_add, add_zero, zero_sub, neg_one_mul, neg_neg, neg_div] using h

private theorem reflected_mass_bound {F : ℝ → ℝ} {K x y : ℝ} (hF0 : F 0 = 0)
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    |F x ^ 2 / (x + y)| ≤ K ^ 2 := by
  have hf := hFL x 0
  rw [hF0, sub_zero, sub_zero, abs_of_pos hx.1] at hf
  have hf2 : F x ^ 2 ≤ K ^ 2 * x ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (F x)) hf 2
    simpa only [sq_abs, mul_pow] using h
  have hx2 : x ^ 2 ≤ x := by nlinarith only [hx.1, hx.2]
  have hxy : 0 < x + y := add_pos hx.1 hy.1
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hxy.le), div_le_iff₀ hxy]
  nlinarith only [hf2, mul_le_mul_of_nonneg_left hx2 (sq_nonneg K),
    mul_nonneg (sq_nonneg K) hy.1.le]

private theorem foldedPair_interior_integral {F : ℝ → ℝ} (hFc : Continuous F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) (hFo : ∀ x, F (-x) = -F x) :
    (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, foldedPair F x y) =
      2 * (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1,
        principalOddKernel x y * (F x - F y) ^ 2) +
      4 * ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * (Real.log (x + 1) - Real.log x) := by
  have hF0 : F 0 = 0 := by have h := hFo 0; simp only [neg_zero] at h; linarith only [h]
  let B : ℝ × ℝ → ℝ := fun p => F p.1 ^ 2 / (p.1 + p.2)
  let E : ℝ × ℝ → ℝ := fun p => principalOddKernel p.1 p.2 * (F p.1 - F p.2) ^ 2
  have hmB : Measurable B := by dsimp [B]; fun_prop
  have hIB : Integrable B
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    refine Measure.integrableOn_of_bounded (M := K ^ 2) (by simp) hmB.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    rw [Real.norm_eq_abs]
    exact reflected_mass_bound hF0 hFL hp.1 hp.2
  have hIBs : Integrable (fun p : ℝ × ℝ => B (p.2, p.1))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    refine Measure.integrableOn_of_bounded (M := K ^ 2) (by simp)
      (hmB.comp (measurable_snd.prodMk measurable_fst)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    rw [Real.norm_eq_abs]
    exact reflected_mass_bound hF0 hFL hp.2 hp.1
  have hIE : Integrable E
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    principalOddKernel_energy_integrable hFc (fun x _ y _ => hFL x y)
  have hID : Integrable (fun p : ℝ × ℝ => foldedPair F p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact (integrable_foldedPair hFc hFL hFs).restrict
  have hp : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1,
      foldedPair F x y = 2 * E (x, y) + 2 * B (x, y) + 2 * B (y, x) := by
    intro x hx y hy
    have hd : |y - x| ≤ 2 := by rw [abs_le]; constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2]
    have hs : |x + y| ≤ 2 := by rw [abs_of_pos (add_pos hx.1 hy.1)]; linarith only [hx.2, hy.2]
    rw [foldedPair_eq hFo]
    dsimp [E, B]
    unfold logarithmicJumpKernel principalOddKernel
    rw [if_pos hd, if_pos hs, abs_of_pos (add_pos hx.1 hy.1), abs_sub_comm y x]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hBrow : ∀ x ∈ Ioo (0 : ℝ) 1, (∫ y in Ioo (0 : ℝ) 1, B (x, y)) =
      F x ^ 2 * (Real.log (x + 1) - Real.log x) := by
    intro x hx
    dsimp [B]
    simp only [div_eq_mul_inv]
    rw [integral_const_mul]
    simpa only [one_div] using congrArg (fun z => F x ^ 2 * z) (integral_inv_add_unit hx.1)
  rw [integral_integral (f := fun x y => foldedPair F x y) hID]
  have hae : (fun p : ℝ × ℝ => foldedPair F p.1 p.2) =ᵐ[
      (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))]
      (fun p => 2 * E p + 2 * B p + 2 * B (p.2, p.1)) := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp'
    exact hp p.1 hp'.1 p.2 hp'.2
  rw [integral_congr_ae hae,
    integral_add (f := fun p => 2 * E p + 2 * B p) (g := fun p => 2 * B (p.2, p.1))
      ((hIE.const_mul 2).add (hIB.const_mul 2)) (hIBs.const_mul 2),
    integral_add (f := fun p => 2 * E p) (g := fun p => 2 * B p)
      (hIE.const_mul 2) (hIB.const_mul 2), integral_const_mul, integral_const_mul,
    integral_const_mul,
    ← integral_integral (f := fun x y => E (x, y)) hIE,
    ← integral_integral (f := fun x y => B (x, y)) hIB,
    ← integral_integral (f := fun x y => B (y, x)) hIBs,
    integral_integral_swap (f := fun x y => B (y, x)) hIBs,
    setIntegral_congr_fun measurableSet_Ioo hBrow]
  dsimp [E]
  ring

/-- The complete logarithmic pair count is its reflected interior count plus exterior killing. -/
theorem logarithmic_pair_eq_folded_count {F : ℝ → ℝ} (hFc : Continuous F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) (hFo : ∀ x, F (-x) = -F x) :
    (∫ p : ℝ × ℝ, logarithmicJumpPair F p.1 p.2 ∂(volume.prod volume)) =
      4 * (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1,
        principalOddKernel x y * (F x - F y) ^ 2) +
      8 * ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * oddLogKilling x := by
  have hF0 : F 0 = 0 := by have h := hFo 0; simp only [neg_zero] at h; linarith only [h]
  have hF1 : F 1 = 0 := hFs 1 (by norm_num)
  have hIK := oddLogKilling_integrable hFc hF0 hF1 (fun x _ y _ => hFL x y)
  have hIB : IntegrableOn (fun x => F x ^ 2 * (Real.log (x + 1) - Real.log x))
      (Ioo (0 : ℝ) 1) := by
    refine hIK.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hr : 0 ≤ Real.log (x + 1) - Real.log x :=
      sub_nonneg.mpr (Real.log_le_log hx.1 (by linarith))
    have hx2 : x ^ 2 < 1 := by nlinarith only [hx.1, hx.2]
    have hl : Real.log (1 - x ^ 2) ≤ 0 := by
      have h := Real.log_le_log (show 0 < 1 - x ^ 2 by linarith only [hx2])
        (show 1 - x ^ 2 ≤ 1 by nlinarith only [sq_nonneg x])
      simpa only [Real.log_one] using h
    have hp : Real.log (x + 1) - Real.log x ≤ oddLogKilling x := by
      unfold oddLogKilling
      linarith only [hl, Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hr)]
    exact mul_le_mul_of_nonneg_left hp (sq_nonneg _)
  have htail : ∀ x, 1 < x → ∀ y, 1 < y → foldedPair F x y = 0 := by
    intro x hx y hy
    have hFx := hFs x (by rw [abs_of_pos (lt_trans zero_lt_one hx)]; exact hx.le)
    have hFy := hFs y (by rw [abs_of_pos (lt_trans zero_lt_one hy)]; exact hy.le)
    have hFny := hFs (-y) (by rw [abs_neg, abs_of_pos (lt_trans zero_lt_one hy)]; exact hy.le)
    simp only [foldedPair, logarithmicJumpPair, hFx, hFy, hFny, sub_self,
      zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  have hsplit := positive_square_split (integrable_foldedPair hFc hFL hFs)
    (integrable_foldedPair_row hFc hFL hFs) (foldedPair_comm hFo) htail
  simp_rw [integral_Ioc_eq_integral_Ioo] at hsplit
  have hext : (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioi (1 : ℝ), foldedPair F x y) =
      2 * ((∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * oddLogKilling x) -
        ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * (Real.log (x + 1) - Real.log x)) := by
    rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => foldedPair_exterior_integral hFs hx)]
    have he : ∀ x ∈ Ioo (0 : ℝ) 1,
        F x ^ 2 * (2 * Real.log 2 - Real.log (1 - x) - Real.log (1 + x)) =
          2 * (F x ^ 2 * oddLogKilling x - F x ^ 2 * (Real.log (x + 1) - Real.log x)) := by
      intro x hx
      have hl : Real.log (1 - x ^ 2) = Real.log (1 - x) + Real.log (1 + x) := by
        rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
          Real.log_mul (sub_pos.mpr hx.2).ne' (by linarith only [hx.1])]
      unfold oddLogKilling
      rw [hl, add_comm 1 x]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioo he, integral_const_mul, integral_sub hIK hIB]
  rw [logarithmic_pair_eq_positive_fold hFc hFL hFs hFo]
  change 2 * (∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), foldedPair F x y) = _
  rw [hsplit, foldedPair_interior_integral hFc hFL hFs hFo, hext]
  ring

private theorem odd_unit_mass {F : ℝ → ℝ}
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) (hFo : ∀ x, F (-x) = -F x) :
    (∫ x, F x ^ 2) = 2 * ∫ x in Ioo (0 : ℝ) 1, F x ^ 2 := by
  have habs : ∀ x, F |x| ^ 2 = F x ^ 2 := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, hFo, neg_sq]
  rw [← integral_congr_ae (Filter.Eventually.of_forall habs),
    integral_comp_abs (f := fun x => F x ^ 2)]
  have he : ∀ x ∈ Ioi (0 : ℝ), F x ^ 2 = (Iic (1 : ℝ)).indicator (fun x => F x ^ 2) x := by
    intro x hx
    by_cases h : x ≤ 1
    · exact (Set.indicator_of_mem (Set.mem_Iic.mpr h) (fun x : ℝ => F x ^ 2)).symm
    · rw [Set.indicator_of_notMem (show x ∉ Iic (1 : ℝ) from fun h' => h (Set.mem_Iic.mp h')),
        hFs x (by rw [abs_of_pos (Set.mem_Ioi.mp hx)]; exact (lt_of_not_ge h).le)]
      norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Iic,
    Ioi_inter_Iic, integral_Ioc_eq_integral_Ioo]

/-- Odd tests on the unit interval have a scale-free logarithmic jump gap. -/
theorem odd_logarithmic_jump_gap_unit {F : ℝ → ℝ} (hFc : Continuous F) {K : ℝ}
    (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, 1 ≤ |x| → F x = 0) (hFo : ∀ x, F (-x) = -F x) :
    (Real.log 2 + 7 / 5) * (∫ x, F x ^ 2) ≤
      ∫ t in Ioc (0 : ℝ) 2, (autocorr F 0 - autocorr F t) / t := by
  have hF0 : F 0 = 0 := by have h := hFo 0; simp only [neg_zero] at h; linarith only [h]
  have hF1 : F 1 = 0 := hFs 1 (by norm_num)
  have hgap := folded_logarithmic_jump_gap hFc hF0 hF1 (fun x _ y _ => hFL x y)
  have hlag := logarithmic_pair_eq_lag hFc hFL hFs
  have hpair := logarithmic_pair_eq_folded_count hFc hFL hFs hFo
  rw [odd_unit_mass hFs hFo]
  linarith only [hgap, hlag, hpair]

private theorem autocorr_comp_pos_mul (F : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    autocorr (fun x => F (a * x)) t = a⁻¹ * autocorr F (a * t) := by
  unfold autocorr
  have h := Measure.integral_comp_mul_left (fun x => F x * F (x + a * t)) a
  rw [abs_of_pos (inv_pos.mpr ha), smul_eq_mul] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with x
  rw [mul_add]

/-- Every odd Lipschitz test supported on an interval has the same logarithmic jump gap. -/
theorem odd_logarithmic_jump_gap {F : ℝ → ℝ} (hFc : Continuous F) {K a : ℝ}
    (ha : 0 < a) (hFL : ∀ x y, |F x - F y| ≤ K * |x - y|)
    (hFs : ∀ x, a ≤ |x| → F x = 0) (hFo : ∀ x, F (-x) = -F x) :
    (Real.log 2 + 7 / 5) * (∫ x, F x ^ 2) ≤
      ∫ t in Ioc (0 : ℝ) (2 * a), (autocorr F 0 - autocorr F t) / t := by
  let G : ℝ → ℝ := fun x => F (a * x)
  have hGc : Continuous G := hFc.comp (continuous_const.mul continuous_id)
  have hGL : ∀ x y, |G x - G y| ≤ (K * a) * |x - y| := by
    intro x y
    have h := hFL (a * x) (a * y)
    rw [← mul_sub, abs_mul, abs_of_pos ha] at h
    dsimp [G]
    nlinarith only [h]
  have hGs : ∀ x, 1 ≤ |x| → G x = 0 := by
    intro x hx
    apply hFs
    rw [abs_mul, abs_of_pos ha]
    nlinarith only [mul_le_mul_of_nonneg_left hx ha.le]
  have hGo : ∀ x, G (-x) = -G x := by
    intro x
    dsimp [G]
    rw [mul_neg, hFo]
  have hgap := odd_logarithmic_jump_gap_unit hGc hGL hGs hGo
  have hmass : (∫ x, G x ^ 2) = a⁻¹ * ∫ x, F x ^ 2 := by
    have h := Measure.integral_comp_mul_left (fun x => F x ^ 2) a
    simpa only [abs_of_pos (inv_pos.mpr ha), smul_eq_mul] using h
  have hlag : (∫ t in Ioc (0 : ℝ) 2, (autocorr G 0 - autocorr G t) / t) =
      a⁻¹ * ∫ t in Ioc (0 : ℝ) (2 * a), (autocorr F 0 - autocorr F t) / t := by
    have he : ∀ t, (autocorr G 0 - autocorr G t) / t =
        (autocorr F 0 - autocorr F (a * t)) / (a * t) := by
      intro t
      dsimp [G]
      rw [autocorr_comp_pos_mul F ha 0, autocorr_comp_pos_mul F ha t, mul_zero]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc (fun t _ => he t),
      ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 by norm_num)]
    have h := intervalIntegral.integral_comp_mul_left
      (fun t => (autocorr F 0 - autocorr F t) / t) (a := 0) (b := 2) ha.ne'
    rw [smul_eq_mul, mul_zero, mul_comm a 2,
      intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * a by positivity)] at h
    exact h
  rw [hmass, hlag] at hgap
  have h : a⁻¹ * ((Real.log 2 + 7 / 5) * ∫ x, F x ^ 2) ≤
      a⁻¹ * ∫ t in Ioc (0 : ℝ) (2 * a), (autocorr F 0 - autocorr F t) / t := by
    calc
      a⁻¹ * ((Real.log 2 + 7 / 5) * ∫ x, F x ^ 2) =
          (Real.log 2 + 7 / 5) * (a⁻¹ * ∫ x, F x ^ 2) := by ring
      _ ≤ _ := hgap
  have hm := mul_le_mul_of_nonneg_left h ha.le
  simpa only [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] using hm

/-- The logarithmic interior-jump count controls the mass of every odd compact smooth test. -/
theorem odd_interior_jump_poincare {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {a : ℝ}
    (ha : 0 < a) (hFs : tsupport F ⊆ Icc (-a) a) (hFo : ∀ x, F (-x) = -F x) :
    (Real.log 2 + 7 / 5) * (∫ x, F x ^ 2) ≤
      ∫ t in Ioc (0 : ℝ) (2 * a), (autocorr F 0 - autocorr F t) / t := by
  have hcs : HasCompactSupport F :=
    HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun x hx =>
      image_eq_zero_of_notMem_tsupport fun hs => hx (hFs hs)
  obtain ⟨K, hK⟩ := RHTower.CHMDDoobGraph.compact_source_lipschitz hF hcs
  have hFL : ∀ x y, |F x - F y| ≤ (K : ℝ) * |x - y| := by
    intro x y
    simpa only [Real.dist_eq] using hK.dist_le_mul x y
  have hz : Ioi a ⊆ {x | F x = 0} := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport fun hs => not_le_of_gt hx (hFs hs).2
  have hzr : ∀ x, a ≤ x → F x = 0 := by
    have h := closure_minimal hz (isClosed_eq hF.continuous continuous_const)
    rw [closure_Ioi] at h
    exact fun x hx => h hx
  have hsupport : ∀ x, a ≤ |x| → F x = 0 := by
    intro x hx
    rcases le_total 0 x with hx0 | hx0
    · exact hzr x (by rwa [abs_of_nonneg hx0] at hx)
    · have hneg := hzr (-x) (by rwa [abs_of_nonpos hx0] at hx)
      rw [hFo] at hneg
      exact neg_eq_zero.mp hneg
  exact odd_logarithmic_jump_gap hF.continuous ha hFL hsupport hFo

end GaloisForLFunctions.LatticeSectionTheory

