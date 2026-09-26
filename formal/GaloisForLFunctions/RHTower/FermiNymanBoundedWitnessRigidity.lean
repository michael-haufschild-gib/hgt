import GaloisForLFunctions.RHTower.FermiNymanBoundedWitnessMellin
import GaloisForLFunctions.RHTower.Sieve.ZetaPoleBoxLowerBound

/-!
# Bounded witnesses of the alternating Nyman–Beurling system are dyadically self-similar

For a bounded witness `w` (continuous and bounded on `(0,1]`, `∫_0^1 φ_a w = 0` for `a ≥ 1`) the
dyadic defect `V(z) = (1 − 2^{−z}) W(z)`, `W(z) = ∫_0^1 t^{z−1} w`, continues to an entire function:
on the strip the Fubini identity of `FermiNymanBoundedWitnessMellin` gives

`V(z) = −2^{−z} z (1 − z) Φ₀(1 − z) / Ξ(1 − z)`,  `Ξ(s) = (s − 1) ζ(s)` (the entire `zetaEntire`),

and `Ξ` has no zero on `Re s ≥ 1`.  This file builds the entire continuation.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.NymanMellin

variable {w : ℝ → ℂ} {M : ℝ}

/-! ## The two forms of the dyadic defect -/

/-- `V(z) = (1 − 2^{−z}) W(z)` (right form, `Re z > 0`). -/
def dyadicDefectRight (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (-z)) * boundedWitnessMellin w z

/-- `V(z) = −2^{−z} z (1 − z) Φ₀(1 − z)/Ξ(1 − z)` (left form, `Re z < 1`). -/
def dyadicDefectLeft (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  -((2 : ℂ) ^ (-z)) * z * (1 - z) * correlationMellin w (1 - z) / zetaEntire (1 - z)

theorem mellin_fermiNymanGen_one {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fermiNymanGen 1) s = -((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s / s) := by
  rw [mellin_fermiNymanGen hs0 hs1 one_pos]
  simp

/-- **Strip identity.**  On `0 < Re z < 1` with `Ξ(1 − z) ≠ 0` the two forms agree. -/
theorem IsBoundedFermiWitness.dyadicDefectRight_eq_left (hw : IsBoundedFermiWitness w M) {z : ℂ}
    (hz0 : 0 < z.re) (hz1 : z.re < 1) (hΞ : zetaEntire (1 - z) ≠ 0) :
    dyadicDefectRight w z = dyadicDefectLeft w z := by
  have hs0 : 0 < (1 - z).re := by simp; linarith
  have hs1 : (1 - z).re < 1 := by simp; linarith
  have hz : z ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hz0; exact lt_irrefl 0 hz0
  have h1z : (1 : ℂ) - z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this; linarith
  have hne1 : (1 : ℂ) - z ≠ 1 := by
    intro h; apply hz; linear_combination -h
  have hfub := hw.correlationMellin_eq hs0 hs1
  rw [show (1 : ℂ) - (1 - z) = z by ring, mellin_fermiNymanGen_one hs0 hs1,
    show (1 : ℂ) - (1 - z) = z by ring] at hfub
  have hζ : riemannZeta (1 - z) = zetaEntire (1 - z) / (1 - z - 1) := by
    rw [zetaEntire_eq hne1]
    have : (1 : ℂ) - z - 1 ≠ 0 := by
      rw [show (1 : ℂ) - z - 1 = -z by ring]; exact neg_ne_zero.2 hz
    field_simp
  rw [hζ] at hfub
  have h2 : (2 : ℂ) ^ z ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num)]; exact Complex.exp_ne_zero _
  have hinv : (2 : ℂ) ^ (-z) * (2 : ℂ) ^ z = 1 := by
    rw [Complex.cpow_neg, inv_mul_cancel₀ h2]
  have hzz : (1 : ℂ) - z - 1 = -z := by ring
  have key : z * (1 - z) * correlationMellin w (1 - z) =
      (1 - (2 : ℂ) ^ z) * zetaEntire (1 - z) * boundedWitnessMellin w z := by
    rw [hfub, hzz]
    field_simp
  unfold dyadicDefectRight dyadicDefectLeft
  rw [eq_div_iff hΞ]
  linear_combination (2 : ℂ) ^ (-z) * key -
    boundedWitnessMellin w z * zetaEntire (1 - z) * hinv

/-! ## The entire continuation -/

/-- The dyadic defect `V`, glued from its right and left forms. -/
def dyadicDefect (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  if 0 < z.re then dyadicDefectRight w z else dyadicDefectLeft w z

theorem IsBoundedFermiWitness.differentiableAt_dyadicDefectRight (hw : IsBoundedFermiWitness w M)
    {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ (dyadicDefectRight w) z := by
  unfold dyadicDefectRight
  exact ((differentiableAt_const _).sub ((differentiableAt_id.neg).const_cpow
    (Or.inl (by norm_num : (2 : ℂ) ≠ 0)))).mul (hw.differentiableAt_boundedWitnessMellin hz)

theorem IsBoundedFermiWitness.differentiableAt_dyadicDefectLeft (hw : IsBoundedFermiWitness w M)
    {z : ℂ} (hz : 0 < (1 - z).re) (hΞ : zetaEntire (1 - z) ≠ 0) :
    DifferentiableAt ℂ (dyadicDefectLeft w) z := by
  unfold dyadicDefectLeft
  have h1 : DifferentiableAt ℂ (fun u : ℂ => (1 : ℂ) - u) z :=
    (differentiableAt_const _).sub differentiableAt_id
  have hΦ : DifferentiableAt ℂ (fun u : ℂ => correlationMellin w (1 - u)) z :=
    (hw.differentiableAt_correlationMellin hz).comp z h1
  have hΞd : DifferentiableAt ℂ (fun u : ℂ => zetaEntire (1 - u)) z :=
    (differentiable_zetaEntire (1 - z)).comp z h1
  have h2 : DifferentiableAt ℂ (fun u : ℂ => -((2 : ℂ) ^ (-u))) z :=
    ((differentiableAt_id.neg).const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))).neg
  exact (((h2.mul differentiableAt_id).mul h1).mul hΦ).div hΞd hΞ

/-- **The dyadic defect is entire.** -/
theorem IsBoundedFermiWitness.differentiable_dyadicDefect (hw : IsBoundedFermiWitness w M) :
    Differentiable ℂ (dyadicDefect w) := by
  intro z
  rcases lt_trichotomy z.re 0 with hneg | hzero | hpos
  · have hev : dyadicDefect w =ᶠ[𝓝 z] dyadicDefectLeft w := by
      filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hneg] with u hu
      unfold dyadicDefect
      rw [if_neg (not_lt.2 (le_of_lt hu))]
    have h1 : 0 < (1 - z).re := by simp; linarith
    exact (hw.differentiableAt_dyadicDefectLeft h1
      (Sieve.zetaEntire_ne_zero_of_one_le_re (by simp; linarith))).congr_of_eventuallyEq hev
  · have hopen : IsOpen ({u : ℂ | |u.re| < 1 / 2} ∩ {u : ℂ | zetaEntire (1 - u) ≠ 0}) := by
      refine (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter ?_
      exact isOpen_ne_fun (differentiable_zetaEntire.continuous.comp
        (continuous_const.sub continuous_id)) continuous_const
    have hΞz : zetaEntire (1 - z) ≠ 0 := Sieve.zetaEntire_ne_zero_of_one_le_re (by simp; linarith)
    have hmem : z ∈ {u : ℂ | |u.re| < 1 / 2} ∩ {u : ℂ | zetaEntire (1 - u) ≠ 0} := by
      refine ⟨?_, hΞz⟩
      show |z.re| < 1 / 2
      rw [hzero, abs_zero]; norm_num
    have hev : dyadicDefect w =ᶠ[𝓝 z] dyadicDefectLeft w := by
      filter_upwards [hopen.mem_nhds hmem] with u hu
      obtain ⟨hre, hΞ⟩ := hu
      simp only [mem_setOf_eq] at hre hΞ
      unfold dyadicDefect
      split_ifs with hup
      · exact hw.dyadicDefectRight_eq_left hup (by linarith [(abs_lt.1 hre).2]) hΞ
      · rfl
    have h1 : 0 < (1 - z).re := by simp; linarith
    exact (hw.differentiableAt_dyadicDefectLeft h1 hΞz).congr_of_eventuallyEq hev
  · have hev : dyadicDefect w =ᶠ[𝓝 z] dyadicDefectRight w := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos] with u hu
      unfold dyadicDefect
      rw [if_pos hu]
    exact (hw.differentiableAt_dyadicDefectRight hpos).congr_of_eventuallyEq hev

/-! ## Lower and upper parts -/

/-- `∫_{1/2}^1 t^{z−1} w(t) dt`, entire. -/
def upperWitnessMellin (w : ℝ → ℂ) (z : ℂ) : ℂ := mellin ((Ioc (1 / 2 : ℝ) 1).indicator w) z

/-- `∫_0^{1/2} t^{z−1} (w(t) − w(2t)) dt`. -/
def lowerDefectMellin (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) (1 / 2), (t : ℂ) ^ (z - 1) * (w t - w (2 * t))

theorem mellin_indicator_eq_setIntegral {a b : ℝ} (ha : 0 ≤ a) (f : ℝ → ℂ) (z : ℂ) :
    mellin ((Ioc a b).indicator f) z = ∫ t in Ioc a b, (t : ℂ) ^ (z - 1) * f t := by
  unfold mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun t (ht : t ∈ Ioc a b) => lt_of_le_of_lt ha ht.1)]
  · refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    rw [Set.indicator_of_mem ht, smul_eq_mul]
  · intro t ht
    rw [Set.indicator_of_notMem ht.2, smul_zero]

theorem IsBoundedFermiWitness.differentiable_upperWitnessMellin (hw : IsBoundedFermiWitness w M) :
    Differentiable ℂ (upperWitnessMellin w) := by
  intro z
  have hmeas : Measurable ((Ioc (1 / 2 : ℝ) 1).indicator w) := by
    have h := hw.measurable_unitExt
    have heq : (Ioc (1 / 2 : ℝ) 1).indicator w = (Ioc (1 / 2 : ℝ) 1).indicator (unitExt w) := by
      funext t
      by_cases ht : t ∈ Ioc (1 / 2 : ℝ) 1
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, unitExt,
          Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨by linarith [ht.1], ht.2⟩)]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
    rw [heq]; exact h.indicator measurableSet_Ioc
  have hbd : ∀ t, ‖(Ioc (1 / 2 : ℝ) 1).indicator w t‖ ≤ M := by
    intro t
    by_cases ht : t ∈ Ioc (1 / 2 : ℝ) 1
    · rw [Set.indicator_of_mem ht]; exact hw.bound t ⟨by linarith [ht.1], ht.2⟩
    · rw [Set.indicator_of_notMem ht, norm_zero]; exact hw.nonneg
  have hint : IntegrableOn ((Ioc (1 / 2 : ℝ) 1).indicator w) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
    refine IntegrableOn.union ?_ ?_
    · exact Measure.integrableOn_of_bounded (M := M) measure_Ioc_lt_top.ne
        hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
    · refine (integrableOn_zero).congr_fun (fun x hx => ?_) measurableSet_Ioi
      exact (Set.indicator_of_notMem (fun (h : x ∈ Ioc (1 / 2 : ℝ) 1) =>
        by linarith [h.2, show (1 : ℝ) < x from hx]) w).symm
  refine mellin_differentiableAt_of_isBigO_rpow (a := z.re + 1) (b := z.re - 1)
    hint.locallyIntegrableOn ?_ (by linarith) ?_ (by linarith)
  · refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    rw [Set.indicator_of_notMem (fun (h : x ∈ Ioc (1 / 2 : ℝ) 1) => by linarith [h.2]), norm_zero,
      zero_mul]
  · refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    rw [Set.indicator_of_notMem (fun (h : x ∈ Ioc (1 / 2 : ℝ) 1) => by linarith [h.1, hx.2]),
      norm_zero, zero_mul]

theorem integrableOn_cpow_mul_of_bound {z : ℂ} (hz : 0 < z.re) {a b : ℝ}
    (hab : Ioc a b ⊆ Ioc 0 1) {g : ℝ → ℂ} (hg : ContinuousOn g (Ioc a b)) {C : ℝ}
    (hgb : ∀ t ∈ Ioc a b, ‖g t‖ ≤ C) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * g t) (Ioc a b) := by
  have hI : IntegrableOn (fun t : ℝ => C * t ^ (z.re - 1)) (Ioc 0 1) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := z.re - 1) (by linarith))
    exact this.const_mul _
  refine (hI.mono_set hab).mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine ContinuousOn.mul ?_ hg
    intro t ht
    exact ((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 (hab ht).1)).continuousWithinAt
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hab ht).1, Complex.sub_re, Complex.one_re,
      mul_comm]
    exact mul_le_mul_of_nonneg_right (hgb t ht) (Real.rpow_nonneg (hab ht).1.le _)

/-- **Splitting the right form.**  On `Re z > 0`, `V = lower + upper`. -/
theorem IsBoundedFermiWitness.dyadicDefectRight_eq (hw : IsBoundedFermiWitness w M) {z : ℂ}
    (hz : 0 < z.re) :
    dyadicDefectRight w z = lowerDefectMellin w z + upperWitnessMellin w z := by
  have hsubL : Ioc (0 : ℝ) (1 / 2) ⊆ Ioc 0 1 := Ioc_subset_Ioc_right (by norm_num)
  have hsubU : Ioc (1 / 2 : ℝ) 1 ⊆ Ioc 0 1 := Ioc_subset_Ioc_left (by norm_num)
  have hw2 : ContinuousOn (fun t => w (2 * t)) (Ioc 0 (1 / 2)) :=
    hw.cont.comp (continuousOn_const.mul continuousOn_id) (fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have iL := integrableOn_cpow_mul_of_bound hz hsubL (hw.cont.mono hsubL) (C := M)
    (fun t ht => hw.bound t (hsubL ht))
  have iU := integrableOn_cpow_mul_of_bound hz hsubU (hw.cont.mono hsubU) (C := M)
    (fun t ht => hw.bound t (hsubU ht))
  have iL2 := integrableOn_cpow_mul_of_bound hz hsubL hw2 (C := M)
    (fun t ht => hw.bound (2 * t) ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  -- the dilated part
  have hdil : (2 : ℂ) ^ (-z) * boundedWitnessMellin w z =
      ∫ t in Ioc (0 : ℝ) (1 / 2), (t : ℂ) ^ (z - 1) * w (2 * t) := by
    have h := mellin_comp_mul_left (unitExt w) z (by norm_num : (0 : ℝ) < 2)
    rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num, smul_eq_mul] at h
    unfold boundedWitnessMellin
    rw [← h]
    unfold mellin
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
    · refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      beta_reduce
      rw [smul_eq_mul, unitExt,
        Set.indicator_of_mem (show 2 * t ∈ Ioc (0 : ℝ) 1 from ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
    · intro t ht
      have ht1 : 1 / 2 < t := by
        rcases ht with ⟨ht0, htn⟩
        simp only [mem_Ioc, not_and, not_le] at htn
        exact htn ht0
      beta_reduce
      rw [unitExt, Set.indicator_of_notMem (fun (h : 2 * t ∈ Ioc (0 : ℝ) 1) => by linarith [h.2]),
        smul_zero]
  have hsplit : boundedWitnessMellin w z =
      (∫ t in Ioc (0 : ℝ) (1 / 2), (t : ℂ) ^ (z - 1) * w t) +
        ∫ t in Ioc (1 / 2 : ℝ) 1, (t : ℂ) ^ (z - 1) * w t := by
    rw [boundedWitnessMellin_eq_integral, ← Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1), setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc iL iU]
  unfold dyadicDefectRight lowerDefectMellin upperWitnessMellin
  rw [mellin_indicator_eq_setIntegral (by norm_num), sub_mul, one_mul, hdil, hsplit]
  have hsub : (∫ t in Ioc (0 : ℝ) (1 / 2), (t : ℂ) ^ (z - 1) * (w t - w (2 * t))) =
      (∫ t in Ioc (0 : ℝ) (1 / 2), (t : ℂ) ^ (z - 1) * w t) -
        ∫ t in Ioc (0 : ℝ) (1 / 2), (t : ℂ) ^ (z - 1) * w (2 * t) := by
    rw [← integral_sub iL iL2]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    ring
  rw [hsub]
  ring

/-! ## The transform `U(z) = 2^z (V(z) − ∫_{1/2}^1 t^{z−1} w)` -/

/-- `‖∫_0^1 t^{z−1} g‖ ≤ C / Re z` for `‖g‖ ≤ C` on `(0,1]`. -/
theorem norm_setIntegral_cpow_mul_le {g : ℝ → ℂ} {z : ℂ} (hz : 0 < z.re) {C : ℝ}
    (hC : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ C) :
    ‖∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (z - 1) * g t‖ ≤ C / z.re := by
  have hint : IntegrableOn (fun t : ℝ => C * t ^ (z.re - 1)) (Ioc 0 1) := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := z.re - 1)
      (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.const_mul C
  calc ‖∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (z - 1) * g t‖
      ≤ ∫ t in Ioc (0 : ℝ) 1, C * t ^ (z.re - 1) := by
        refine norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioc ?_)
        intro t ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.sub_re, Complex.one_re,
          mul_comm]
        exact mul_le_mul_of_nonneg_right (hC t ht) (Real.rpow_nonneg ht.1.le _)
    _ = C / z.re := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
          integral_rpow (Or.inl (by linarith))]
        simp only [sub_add_cancel, Real.one_rpow, Real.zero_rpow hz.ne', sub_zero]
        field_simp

/-- The transform `U`; it is entire. -/
def dyadicDefectTransform (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ) ^ z * (dyadicDefect w z - upperWitnessMellin w z)

theorem IsBoundedFermiWitness.differentiable_dyadicDefectTransform
    (hw : IsBoundedFermiWitness w M) : Differentiable ℂ (dyadicDefectTransform w) := by
  intro z
  exact (differentiableAt_id.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))).mul
    ((hw.differentiable_dyadicDefect z).sub (hw.differentiable_upperWitnessMellin z))

theorem two_cpow_mul_two_cpow_neg (z : ℂ) : (2 : ℂ) ^ z * (2 : ℂ) ^ (-z) = 1 := by
  rw [← Complex.cpow_add _ _ two_ne_zero, add_neg_cancel, Complex.cpow_zero]

/-- `2^z ∫_0^{1/2} t^{z−1}(w(t) − w(2t)) = ∫_0^1 u^{z−1}(w(u/2) − w(u))`. -/
theorem two_cpow_mul_lowerDefectMellin (w : ℝ → ℂ) (z : ℂ) :
    (2 : ℂ) ^ z * lowerDefectMellin w z =
      ∫ u in Ioc (0 : ℝ) 1, (u : ℂ) ^ (z - 1) * (w (u / 2) - w u) := by
  have h := mellin_comp_mul_left ((Ioc (0 : ℝ) 1).indicator (fun u => w (u / 2) - w u)) z
    (by norm_num : (0 : ℝ) < 2)
  have hcomp : (fun t => (Ioc (0 : ℝ) 1).indicator (fun u => w (u / 2) - w u) (2 * t)) =
      (Ioc (0 : ℝ) (1 / 2)).indicator (fun t => w t - w (2 * t)) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) (1 / 2)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem
        (show 2 * t ∈ Ioc (0 : ℝ) 1 from ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
      have : 2 * t / 2 = t := by ring
      simp only [this]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem]
      intro h2; apply ht; exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  rw [hcomp, mellin_indicator_eq_setIntegral le_rfl, mellin_indicator_eq_setIntegral le_rfl,
    show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num, smul_eq_mul] at h
  unfold lowerDefectMellin
  rw [h, ← mul_assoc, two_cpow_mul_two_cpow_neg, one_mul]

theorem IsBoundedFermiWitness.dyadicDefectTransform_eq_of_re_pos (hw : IsBoundedFermiWitness w M)
    {z : ℂ} (hz : 0 < z.re) :
    dyadicDefectTransform w z = ∫ u in Ioc (0 : ℝ) 1, (u : ℂ) ^ (z - 1) * (w (u / 2) - w u) := by
  unfold dyadicDefectTransform dyadicDefect
  rw [if_pos hz, hw.dyadicDefectRight_eq hz, add_sub_cancel_right, two_cpow_mul_lowerDefectMellin]

/-- On `Re z > 0`, `‖U(z)‖ ≤ 2M / Re z`. -/
theorem IsBoundedFermiWitness.norm_dyadicDefectTransform_le_of_re_pos
    (hw : IsBoundedFermiWitness w M) {z : ℂ} (hz : 0 < z.re) :
    ‖dyadicDefectTransform w z‖ ≤ 2 * M / z.re := by
  rw [hw.dyadicDefectTransform_eq_of_re_pos hz]
  refine norm_setIntegral_cpow_mul_le hz (fun t ht => ?_)
  have h1 := hw.bound (t / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 := hw.bound t ht
  calc ‖w (t / 2) - w t‖ ≤ ‖w (t / 2)‖ + ‖w t‖ := norm_sub_le _ _
    _ ≤ 2 * M := by linarith

/-- On `Re z ≤ 1`, `‖2^z ∫_{1/2}^1 t^{z−1} w‖ ≤ M`. -/
theorem IsBoundedFermiWitness.norm_two_cpow_mul_upperWitnessMellin_le
    (hw : IsBoundedFermiWitness w M) {z : ℂ} (hz : z.re ≤ 1) :
    ‖(2 : ℂ) ^ z * upperWitnessMellin w z‖ ≤ M := by
  unfold upperWitnessMellin
  rw [mellin_indicator_eq_setIntegral (by norm_num), norm_mul]
  have h2 : ‖(2 : ℂ) ^ z‖ = (2 : ℝ) ^ z.re := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) z
    rwa [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num] at this
  have hI : ‖∫ t in Ioc (1 / 2 : ℝ) 1, (t : ℂ) ^ (z - 1) * w t‖ ≤
      (1 / 2 : ℝ) ^ (z.re - 1) * M * (1 / 2) := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (1 / 2 : ℝ) 1)
      (f := fun t : ℝ => (t : ℂ) ^ (z - 1) * w t) (C := (1 / 2 : ℝ) ^ (z.re - 1) * M)
      measure_Ioc_lt_top (fun t ht => ?_)
    · rw [Real.volume_real_Ioc_of_le (by norm_num)] at this
      calc _ ≤ (1 / 2 : ℝ) ^ (z.re - 1) * M * (1 - 1 / 2) := this
        _ = _ := by norm_num
    · have ht0 : (0 : ℝ) < t := by linarith [ht.1]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
      exact mul_le_mul (Real.rpow_le_rpow_of_nonpos (by norm_num) ht.1.le (by linarith))
        (hw.bound t ⟨ht0, ht.2⟩) (norm_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  rw [h2]
  have e : (1 / 2 : ℝ) ^ (z.re - 1) = (1 / 2 : ℝ) ^ z.re / (1 / 2) :=
    Real.rpow_sub_one (by norm_num) z.re
  have e2 : (2 : ℝ) ^ z.re * (1 / 2 : ℝ) ^ z.re = 1 := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  calc (2 : ℝ) ^ z.re * ‖∫ t in Ioc (1 / 2 : ℝ) 1, (t : ℂ) ^ (z - 1) * w t‖
      ≤ (2 : ℝ) ^ z.re * ((1 / 2 : ℝ) ^ (z.re - 1) * M * (1 / 2)) :=
        mul_le_mul_of_nonneg_left hI (Real.rpow_nonneg (by norm_num) _)
    _ = ((2 : ℝ) ^ z.re * (1 / 2 : ℝ) ^ z.re) * M := by rw [e]; ring
    _ = M := by rw [e2, one_mul]

/-- `2^z V_left(z) = (1 − z) Φ₀(1 − z) / ζ(1 − z)` for `z ≠ 0`. -/
theorem two_cpow_mul_dyadicDefectLeft {z : ℂ} (hz : z ≠ 0) :
    (2 : ℂ) ^ z * dyadicDefectLeft w z =
      (1 - z) * correlationMellin w (1 - z) / riemannZeta (1 - z) := by
  have hne1 : (1 : ℂ) - z ≠ 1 := by intro h; apply hz; linear_combination -h
  unfold dyadicDefectLeft
  rw [zetaEntire_eq hne1, show (1 : ℂ) - z - 1 = -z by ring]
  have h2 := two_cpow_mul_two_cpow_neg z
  calc (2 : ℂ) ^ z * (-(2 : ℂ) ^ (-z) * z * (1 - z) * correlationMellin w (1 - z) /
        (-z * riemannZeta (1 - z)))
      = ((2 : ℂ) ^ z * (2 : ℂ) ^ (-z)) * (z / z) *
          ((1 - z) * correlationMellin w (1 - z) / riemannZeta (1 - z)) := by ring
    _ = _ := by rw [h2, div_self hz, one_mul, one_mul]

/-- **The left bound.**  For `Re z < 1`, `z ≠ 0`, and `ζ(1 − z) ≠ 0` when `Re z > 0`:
`‖U(z)‖ ≤ ‖1 − z‖ · 3M/(1 − Re z) · ‖ζ(1 − z)‖⁻¹ + M`. -/
theorem IsBoundedFermiWitness.norm_dyadicDefectTransform_le_left (hw : IsBoundedFermiWitness w M)
    {z : ℂ} (hz1 : z.re < 1) (hz0 : z ≠ 0) (hζ : 0 < z.re → riemannZeta (1 - z) ≠ 0) :
    ‖dyadicDefectTransform w z‖ ≤
      ‖1 - z‖ * (3 * M / (1 - z.re)) * (1 / ‖riemannZeta (1 - z)‖) + M := by
  have hne1 : (1 : ℂ) - z ≠ 1 := by intro h; apply hz0; linear_combination -h
  have hV : dyadicDefect w z = dyadicDefectLeft w z := by
    unfold dyadicDefect
    split_ifs with hpos
    · refine hw.dyadicDefectRight_eq_left hpos hz1 ?_
      rw [zetaEntire_eq hne1]
      exact mul_ne_zero (sub_ne_zero.2 hne1) (hζ hpos)
    · rfl
  have hs0 : 0 < (1 - z).re := by simp; linarith
  have hΦ := hw.norm_correlationMellin_le hs0
  have hre : (1 - z).re = 1 - z.re := by simp
  rw [hre] at hΦ
  unfold dyadicDefectTransform
  rw [hV, mul_sub]
  refine (norm_sub_le _ _).trans (add_le_add ?_ (hw.norm_two_cpow_mul_upperWitnessMellin_le hz1.le))
  rw [two_cpow_mul_dyadicDefectLeft hz0, norm_div, norm_mul, div_eq_mul_one_div _ ‖riemannZeta _‖]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΦ (norm_nonneg _))
    (by positivity)

end RHTower
