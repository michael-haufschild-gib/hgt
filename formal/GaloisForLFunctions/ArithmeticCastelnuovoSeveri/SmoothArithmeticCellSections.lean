import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolePreservingSmoothing
import GaloisForLFunctions.HTGeometry.CausalJordanTitchmarshSupport
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurface

/-!
# Smooth complete arithmetic sections

A common pole-preserving kernel retains exact Hecke subdivision. The first
nonzero coefficient supplies a sign-definite support edge, so convolution is
injective even when the smoothed cells overlap. Their span inside the original
compact C² test carrier therefore has exactly one dimension per cell.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped Convolution
open _root_.RHTower hiding mollifier
open _root_.RHTower.CHMDDoobGraph

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open HTGeometry

/-- One complete logarithmic cell, including its left endpoint. -/
def rawCell (a : ℕ) : ℝ → ℝ :=
  (Ico (Real.log a) (Real.log ((a + 1 : ℕ) : ℝ))).indicator (fun _ => 1)

theorem measurable_rawCell (a : ℕ) : Measurable (rawCell a) :=
  measurable_const.indicator measurableSet_Ico

theorem rawCell_bound (a : ℕ) (x : ℝ) : |rawCell a x| ≤ 1 := by
  simp only [rawCell, indicator_apply]
  split_ifs <;> norm_num

theorem rawCell_compact (a : ℕ) : HasCompactSupport (rawCell a) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  exact indicator_of_notMem (fun h => hx ⟨h.1, h.2.le⟩) _

theorem memLp_rawCell (a : ℕ) : MemLp (rawCell a) 2 volume :=
  bounded_compact_memLp_volume (measurable_rawCell a) (rawCell_compact a)
    (by norm_num) (rawCell_bound a)

private def halfStep (a x : ℝ) : ℝ := if a ≤ x then 1 else 0

private theorem indicator_Ico_eq_step_sub {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    (Ico a b).indicator (fun _ => (1 : ℝ)) x = halfStep a x - halfStep b x := by
  simp only [indicator_apply, mem_Ico, halfStep]
  split_ifs <;> simp_all <;> linarith

private theorem halfStep_bv (a : ℝ) : BoundedVariationOn (halfStep a) univ := by
  have hm : Monotone (halfStep a) := by
    intro x y hxy
    by_cases hx : a ≤ x
    · simp only [halfStep, if_pos hx, if_pos (hx.trans hxy), le_refl]
    · simp only [halfStep, if_neg hx]
      split_ifs <;> norm_num
  exact (hm.monotoneOn univ).boundedVariationOn (C := 1) (fun x _ => by
    simp only [halfStep]
    split_ifs <;> norm_num)

theorem rawCell_bv (a : ℕ) : BoundedVariationOn (rawCell a) univ := by
  have ha : Real.log a ≤ Real.log ((a + 1 : ℕ) : ℝ) := by
    by_cases ha : a = 0
    · simp only [ha, Nat.cast_zero, zero_add, Nat.cast_one, Real.log_zero, Real.log_one, le_refl]
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero ha) (by exact_mod_cast Nat.le_succ a)
  have he : rawCell a = fun x => halfStep (Real.log a) x -
      halfStep (Real.log ((a + 1 : ℕ) : ℝ)) x := funext (indicator_Ico_eq_step_sub ha)
  rw [he]
  exact boundedVariationOn_sub (halfStep_bv _) (halfStep_bv _)

theorem bv_const_mul {f : ℝ → ℝ} (c : ℝ) (hf : BoundedVariationOn f univ) :
    BoundedVariationOn (fun x => c * f x) univ := by
  have hl : LipschitzWith ⟨|c|, abs_nonneg c⟩ (fun x : ℝ => c * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, show c * x - c * y = c * (x - y) by ring, abs_mul]
    exact le_rfl
  simpa only [Function.comp_def] using hl.comp_boundedVariationOn hf

private theorem indicator_Ico_subdivision (b : ℕ → ℝ) (hb : Monotone b) (m : ℕ) (x : ℝ) :
    (Ico (b 0) (b m)).indicator (fun _ => (1 : ℝ)) x =
      ∑ r ∈ Finset.range m, (Ico (b r) (b (r + 1))).indicator (fun _ => (1 : ℝ)) x := by
  rw [indicator_Ico_eq_step_sub (hb (Nat.zero_le m))]
  simp_rw [indicator_Ico_eq_step_sub (hb (Nat.le_succ _))]
  calc
    _ = -(halfStep (b m) x - halfStep (b 0) x) := by ring
    _ = -(∑ r ∈ Finset.range m, (halfStep (b (r + 1)) x - halfStep (b r) x)) := by
      exact congrArg (fun y : ℝ => -y)
        (Finset.sum_range_sub (fun r => halfStep (b r) x) m).symm
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- The translated complete cell is exactly the union of its successor cells. -/
theorem rawCell_hecke {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) (x : ℝ) :
    rawCell a (x - Real.log m) = ∑ r ∈ Finset.range m, rawCell (a * m + r) x := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have ham0 : (0 : ℝ) < a * m := mul_pos ha0 hm0
  have hlog (b : ℕ) (hb : 1 ≤ b) :
      Real.log ((b * m : ℕ) : ℝ) = Real.log b + Real.log m := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (Nat.ne_of_gt hb)) hm0.ne']
  have hshift : x - Real.log m ∈ Ico (Real.log a) (Real.log ((a + 1 : ℕ) : ℝ)) ↔
      x ∈ Ico (Real.log ((a * m : ℕ) : ℝ)) (Real.log (((a + 1) * m : ℕ) : ℝ)) := by
    rw [hlog a ha, hlog (a + 1) (by omega)]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have he : rawCell a (x - Real.log m) =
      (Ico (Real.log ((a * m : ℕ) : ℝ)) (Real.log (((a + 1) * m : ℕ) : ℝ))).indicator
        (fun _ => (1 : ℝ)) x := by
    simp only [rawCell, indicator_apply, hshift]
  rw [he]
  have hb : Monotone (fun r : ℕ => Real.log ((a * m + r : ℕ) : ℝ)) := by
    intro i j hij
    apply Real.log_le_log
    · exact_mod_cast (Nat.add_pos_left
        (Nat.mul_pos (by omega : 0 < a) (by omega : 0 < m)) i)
    · exact_mod_cast Nat.add_le_add_left hij (a * m)
  have h := indicator_Ico_subdivision (fun r => Real.log ((a * m + r : ℕ) : ℝ)) hb m x
  simpa only [Nat.add_zero, Nat.add_mul, Nat.one_mul, rawCell, Nat.add_assoc] using h

/-- Every complete cell is realized by the same smooth arithmetic operator. -/
def smoothCell (n a : ℕ) : realTests :=
  ⟨poleSmooth (rawCell a) n, poleSmooth_contDiff (memLp_rawCell a) n,
    poleSmooth_compact (rawCell_compact a) n⟩

theorem poleSmooth_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hm : ∀ i ∈ s, Measurable (f i)) (B : ι → ℝ)
    (hB : ∀ i ∈ s, 0 ≤ B i) (hb : ∀ i ∈ s, ∀ x, |f i x| ≤ B i) (n : ℕ) :
    poleSmooth (fun x => ∑ i ∈ s, f i x) n = fun x => ∑ i ∈ s, poleSmooth (f i) n x := by
  funext x
  simp only [poleSmooth, smooth, lineConvolution, Finset.mul_sum]
  rw [integral_finsetSum s (fun i hi => integrable_mollifier_mul (hm i hi) (hB i hi) (hb i hi) n x)]
  exact Finset.mul_sum _ _ _

/-- Hecke subdivision is exact after smoothing, with one common smoothing scale. -/
theorem smoothCell_hecke (n : ℕ) {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) (x : ℝ) :
    (smoothCell n a : ℝ → ℝ) (x - Real.log m) =
      ∑ r ∈ Finset.range m, (smoothCell n (a * m + r) : ℝ → ℝ) x := by
  change poleSmooth (rawCell a) n (x - Real.log m) = _
  rw [← poleSmooth_translate]
  have he : (fun u => rawCell a (u - Real.log m)) =
      fun u => ∑ r ∈ Finset.range m, rawCell (a * m + r) u := funext (rawCell_hecke ha hm)
  rw [he, poleSmooth_finset_sum (Finset.range m) _
    (fun r _ => measurable_rawCell _) (fun _ => 1) (fun _ _ => by norm_num)
    (fun r _ => rawCell_bound _) n]
  rfl

theorem poleKernel_leftEdge (n : ℕ) :
    LeftEdge (poleKernel n) (-(WeilOneSided.narrowBump n).rOut) 1 := by
  let r := (WeilOneSided.narrowBump n).rOut
  have hr : 0 < r := (WeilOneSided.narrowBump n).rOut_pos
  have hs (x : ℝ) : mollifier n x ≠ 0 ↔ |x| < r := by
    change x ∈ Function.support ((WeilOneSided.narrowBump n).normed volume) ↔ _
    rw [(WeilOneSided.narrowBump n).support_normed_eq]
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, r]
  constructor
  · exact Eventually.of_forall fun x hx => by
      have hz : mollifier n x = 0 := by
        by_contra h
        have ht := (abs_lt.mp ((hs x).mp h)).1
        linarith
      simp only [poleKernel, hz, mul_zero]
  · refine ⟨2 * r, by positivity, Eventually.of_forall fun x hx => ?_⟩
    have hn : mollifier n x ≠ 0 := (hs x).mpr (abs_lt.mpr ⟨hx.1, by linarith [hx.2]⟩)
    have hp : 0 < mollifier n x := lt_of_le_of_ne (mollifier_nonneg n x) hn.symm
    simpa only [one_mul, poleKernel] using mul_pos (inv_pos.mpr (poleNormalizer_pos n)) hp

private theorem leftEdge_not_zero {f : ℝ → ℝ} {a σ : ℝ} (h : LeftEdge f a σ) : f ≠ 0 := by
  intro hf
  obtain ⟨ε, hε, he⟩ := h.edge
  have hz : ∀ᵐ x : ℝ, x ∉ Ioo a (a + ε) := by
    filter_upwards [he] with x hx hmem
    have := hx hmem
    simp only [hf, Pi.zero_apply, mul_zero, lt_self_iff_false] at this
  have hvol : volume (Ioo a (a + ε)) = 0 := by
    simpa only [not_not, setOf_mem_eq] using (ae_iff.mp hz)
  rw [Real.volume_Ioo] at hvol
  have hp : 0 < ENNReal.ofReal (a + ε - a) := ENNReal.ofReal_pos.mpr (by linarith)
  exact hp.ne' hvol

/-- An arbitrary finite coefficient vector on whole logarithmic cells. -/
def rawSection {X : ℕ} (c : Fin X → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * rawCell (i.val + 1) x

theorem rawSection_measurable {X : ℕ} (c : Fin X → ℝ) : Measurable (rawSection c) :=
  Finset.measurable_sum _ (fun _ _ => measurable_const.mul (measurable_rawCell _))

theorem rawSection_bound {X : ℕ} (c : Fin X → ℝ) (x : ℝ) :
    |rawSection c x| ≤ ∑ i, |c i| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (rawCell_bound _ _)

theorem rawSection_compact {X : ℕ} (c : Fin X → ℝ) : HasCompactSupport (rawSection c) := by
  refine HasCompactSupport.intro
    (show IsCompact (Icc (0 : ℝ) (Real.log (X + 1 : ℕ))) from isCompact_Icc) ?_
  intro x hx
  apply Finset.sum_eq_zero
  intro i _
  have hn : x ∉ Ico (Real.log (i.val + 1 : ℕ)) (Real.log (i.val + 1 + 1 : ℕ)) := by
    intro hi
    have hlo : 0 ≤ Real.log (i.val + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 i.val)
    have hhi : Real.log (i.val + 1 + 1 : ℕ) ≤ Real.log (X + 1 : ℕ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast (show i.val + 1 + 1 ≤ X + 1 by omega)
    exact hx ⟨hlo.trans hi.1, hi.2.le.trans hhi⟩
  rw [rawCell, indicator_of_notMem hn, mul_zero]

theorem rawSection_bv {X : ℕ} (c : Fin X → ℝ) : BoundedVariationOn (rawSection c) univ := by
  have hsum (s : Finset (Fin X)) :
      BoundedVariationOn (fun x => ∑ i ∈ s, c i * rawCell (i.val + 1) x) univ := by
    classical
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        ((monotone_const : Monotone (fun _ : ℝ => (0 : ℝ))).monotoneOn univ).boundedVariationOn
          (C := 0) (fun x _ => by simp)
    | @insert i s hi ih =>
      have h := boundedVariationOn_sub
        (bv_const_mul (c i) (rawCell_bv (i.val + 1)))
        (bv_const_mul (-1) ih)
      simpa only [Finset.sum_insert hi, neg_one_mul, sub_neg_eq_add] using h
  exact hsum Finset.univ

theorem poleSmooth_rawSection {X : ℕ} (c : Fin X → ℝ) (n : ℕ) :
    poleSmooth (rawSection c) n = fun x => ∑ i, c i * (smoothCell n (i.val + 1) : ℝ → ℝ) x := by
  unfold rawSection
  have hb (i : Fin X) : ∀ x, |c i * rawCell (i.val + 1) x| ≤ |c i| := by
    intro x
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (rawCell_bound _ _)
  have h := poleSmooth_finset_sum Finset.univ
    (fun i : Fin X => fun x => c i * rawCell (i.val + 1) x)
    (fun i _ => (measurable_rawCell (i.val + 1)).const_mul (c i))
    (fun i => |c i|) (fun i _ => abs_nonneg _) (fun i _ => hb i) n
  simpa only [poleSmooth_const_mul, smoothCell] using h

/-- The first nonzero coefficient fixes the exact left support edge. -/
theorem rawSection_first_edge {X : ℕ} {c : Fin X → ℝ} (hc : c ≠ 0) :
    ∃ i : Fin X, c i ≠ 0 ∧ LeftEdge (rawSection c) (Real.log (i.val + 1 : ℕ)) (c i) := by
  classical
  let s := Finset.univ.filter (fun i => c i ≠ 0)
  have hs : s.Nonempty := by
    by_contra hn
    apply hc
    funext i
    have hi : i ∉ s := by rw [Finset.not_nonempty_iff_eq_empty.mp hn]; simp
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not, Pi.zero_apply] using hi
  let i := s.min' hs
  have hi := Finset.mem_filter.mp (Finset.min'_mem s hs)
  have hzero (j : Fin X) (hji : j < i) : c j = 0 := by
    by_contra hj
    have hmin := Finset.min'_le s j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    exact (not_le_of_gt hji) hmin
  have hlog (j k : Fin X) (hjk : j ≤ k) :
      Real.log (j.val + 1 : ℕ) ≤ Real.log (k.val + 1 : ℕ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hjk 1
  have hgap : Real.log (i.val + 1 : ℕ) < Real.log (i.val + 2 : ℕ) := by
    apply Real.log_lt_log (by positivity)
    exact_mod_cast (show i.val + 1 < i.val + 2 by omega)
  refine ⟨i, hi.2, ?_⟩
  constructor
  · exact Eventually.of_forall fun x hx => by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hji : j < i
      · rw [hzero j hji, zero_mul]
      · have hjx : x < Real.log (j.val + 1 : ℕ) := hx.trans_le (hlog i j (le_of_not_gt hji))
        rw [rawCell, indicator_of_notMem (fun h => (not_le_of_gt hjx) h.1), mul_zero]
  · refine ⟨Real.log (i.val + 2 : ℕ) - Real.log (i.val + 1 : ℕ), sub_pos.mpr hgap,
      Eventually.of_forall fun x hx => ?_⟩
    have hxi : x ∈ Ico (Real.log (i.val + 1 : ℕ)) (Real.log (i.val + 2 : ℕ)) :=
      ⟨hx.1.le, by linarith [hx.2]⟩
    have he : rawSection c x = c i := by
      unfold rawSection
      rw [Finset.sum_eq_single i]
      · rw [rawCell, indicator_of_mem (by simpa only [Nat.add_assoc] using hxi), mul_one]
      · intro j _ hji
        rcases lt_or_gt_of_ne hji with hji | hij
        · rw [hzero j hji, zero_mul]
        · have hl : Real.log (i.val + 2 : ℕ) ≤ Real.log (j.val + 1 : ℕ) := by
            apply Real.log_le_log (by positivity)
            exact_mod_cast (show i.val + 2 ≤ j.val + 1 by omega)
          rw [rawCell, indicator_of_notMem (fun h => (not_le_of_gt (hxi.2.trans_le hl)) h.1), mul_zero]
      · simp
    rw [he]
    exact mul_self_pos.mpr hi.2

/-- A nonzero complete-cell vector stays nonzero under every smoothing scale. -/
theorem poleSmooth_rawSection_ne_zero {X : ℕ} {c : Fin X → ℝ} (hc : c ≠ 0) (n : ℕ) :
    poleSmooth (rawSection c) n ≠ 0 := by
  obtain ⟨i, _, hi⟩ := rawSection_first_edge hc
  have hk := poleKernel_leftEdge n
  have hb := (poleKernel_compact n).exists_bound_of_continuous (poleKernel_contDiff n).continuous
  obtain ⟨M, hM⟩ := hb
  have hi1 : Integrable (rawSection c) :=
    integrable_finsetSum _ (fun i _ =>
      (integrable_indicator_Ico (Real.log (i.val + 1 : ℕ))
        (Real.log (i.val + 1 + 1 : ℕ))).const_mul (c i))
  have he := hk.convolution hi (fun x => integrable_mul_comp_sub
    (poleKernel_contDiff n).continuous.aestronglyMeasurable
    (fun x => by simpa only [Real.norm_eq_abs] using hM x) hi1 x)
  rw [poleSmooth_eq_convolution]
  exact leftEdge_not_zero he

/-- Whole-cell arithmetic sections have no presentation kernel. -/
theorem linearIndependent_smoothCell (n X : ℕ) :
    LinearIndependent ℝ (fun i : Fin X => smoothCell n (i.val + 1)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hi
  have hn : c ≠ 0 := fun he => hi (congrFun he i)
  apply poleSmooth_rawSection_ne_zero hn n
  rw [poleSmooth_rawSection]
  funext x
  have he := congrArg (fun f : realTests => (f : ℝ → ℝ) x) hc
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply] using he

/-- The original smooth-test carrier contains exactly one degree of freedom per cell. -/
theorem finrank_smoothCell_span (n X : ℕ) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : Fin X => smoothCell n (i.val + 1)))) = X := by
  simpa only [Fintype.card_fin] using finrank_span_eq_card (linearIndependent_smoothCell n X)

#print axioms smoothCell_hecke
#print axioms poleSmooth_rawSection_ne_zero
#print axioms finrank_smoothCell_span

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
