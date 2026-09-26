import GaloisForLFunctions.RHTower.FermiNymanWitnessMellin
import GaloisForLFunctions.RHTower.Sieve.ZetaPoleBoxLowerBound

/-!
# The dyadic defect of a witness of the alternating Nyman–Beurling system

For a witness `w` of Mellin exponent `a` the dyadic defect `V(z) = (1 − 2^{−z}) W(z)`, analytic on
`Re z > a`, agrees on `a < Re z < 1` with

`V(z) = −2^{−z} z (1 − z) Φ₀(1 − z) / Ξ(1 − z)`,  `Ξ(s) = (s − 1) ζ(s)` (the entire `zetaEntire`),

by the Fubini identity.  If `Ξ(1 − z) ≠ 0` for `Re z ≤ a` the two forms glue to an entire function.
The transform `U(z) = 2^z (V(z) − ∫_{1/2}^1 t^{z−1} w)` is entire as well, equals
`2^z ∫_0^{1/2} t^{z−1}(w(t) − w(2t)) dt` on `Re z > a`, is bounded on every right half-plane
`Re z ≥ x₁ > a`, tends to zero along the positive integers, and on `Re z < 1` is controlled by
`‖1 − z‖ · 3 m(1)/(1 − Re z) · ‖ζ(1 − z)‖⁻¹` plus a constant.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.NymanMellin

variable {w : ℝ → ℂ} {a : ℝ}

/-! ## The two forms of the dyadic defect -/

/-- `V(z) = (1 − 2^{−z}) W(z)` (right form). -/
def dyadicDefectRight (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (-z)) * witnessMellin w z

/-- `V(z) = −2^{−z} z (1 − z) Φ₀(1 − z)/Ξ(1 − z)` (left form). -/
def dyadicDefectLeft (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  -((2 : ℂ) ^ (-z)) * z * (1 - z) * correlationMellin w (1 - z) / zetaEntire (1 - z)

theorem mellin_fermiNymanGen_one {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fermiNymanGen 1) s = -((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s / s) := by
  rw [mellin_fermiNymanGen hs0 hs1 one_pos]
  simp

/-- **Strip identity.**  On `a < Re z < 1` with `Ξ(1 − z) ≠ 0` the two forms agree. -/
theorem IsMellinFermiWitness.dyadicDefectRight_eq_left (hw : IsMellinFermiWitness w a) {z : ℂ}
    (hza : a < z.re) (hz1 : z.re < 1) (hΞ : zetaEntire (1 - z) ≠ 0) :
    dyadicDefectRight w z = dyadicDefectLeft w z := by
  have hz0' : 0 < z.re := lt_of_le_of_lt hw.nonneg hza
  have hs0 : 0 < (1 - z).re := by simp; linarith
  have hs1 : (1 - z).re < 1 := by simp; linarith
  have hs1a : (1 - z).re < 1 - a := by simp; linarith
  have hz : z ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hz0'; exact lt_irrefl 0 hz0'
  have hne1 : (1 : ℂ) - z ≠ 1 := by
    intro h; apply hz; linear_combination -h
  have hfub := hw.correlationMellin_eq hs0 hs1a
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
  have h1z : (1 : ℂ) - z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this; linarith
  have key : z * (1 - z) * correlationMellin w (1 - z) =
      (1 - (2 : ℂ) ^ z) * zetaEntire (1 - z) * witnessMellin w z := by
    rw [hfub, hzz]
    field_simp
  unfold dyadicDefectRight dyadicDefectLeft
  rw [eq_div_iff hΞ]
  linear_combination (2 : ℂ) ^ (-z) * key - witnessMellin w z * zetaEntire (1 - z) * hinv

/-! ## The entire continuation -/

/-- The dyadic defect `V`, glued from its right and left forms along `Re z = a`. -/
def dyadicDefect (w : ℝ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  if a < z.re then dyadicDefectRight w z else dyadicDefectLeft w z

theorem IsMellinFermiWitness.differentiableAt_dyadicDefectRight (hw : IsMellinFermiWitness w a)
    {z : ℂ} (hz : a < z.re) : DifferentiableAt ℂ (dyadicDefectRight w) z := by
  unfold dyadicDefectRight
  exact ((differentiableAt_const _).sub ((differentiableAt_id.neg).const_cpow
    (Or.inl (by norm_num : (2 : ℂ) ≠ 0)))).mul (hw.differentiableAt_witnessMellin hz)

theorem IsMellinFermiWitness.differentiableAt_dyadicDefectLeft (hw : IsMellinFermiWitness w a)
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

/-- **The dyadic defect is entire** when `Ξ(1 − z)` has no zero on `Re z ≤ a`. -/
theorem IsMellinFermiWitness.differentiable_dyadicDefect (hw : IsMellinFermiWitness w a)
    (hΞ : ∀ z : ℂ, z.re ≤ a → zetaEntire (1 - z) ≠ 0) :
    Differentiable ℂ (dyadicDefect w a) := by
  intro z
  have ha1 := hw.lt_one
  rcases lt_trichotomy z.re a with hneg | hzero | hpos
  · have hev : dyadicDefect w a =ᶠ[𝓝 z] dyadicDefectLeft w := by
      filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hneg] with u hu
      unfold dyadicDefect
      rw [if_neg (not_lt.2 (le_of_lt hu))]
    have h1 : 0 < (1 - z).re := by simp; linarith
    exact (hw.differentiableAt_dyadicDefectLeft h1 (hΞ z hneg.le)).congr_of_eventuallyEq hev
  · set δ : ℝ := (1 - a) / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    have hopen : IsOpen ({u : ℂ | |u.re - a| < δ} ∩ {u : ℂ | zetaEntire (1 - u) ≠ 0}) := by
      refine (isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const))
        continuous_const).inter ?_
      exact isOpen_ne_fun (differentiable_zetaEntire.continuous.comp
        (continuous_const.sub continuous_id)) continuous_const
    have hΞz : zetaEntire (1 - z) ≠ 0 := hΞ z hzero.le
    have hmem : z ∈ {u : ℂ | |u.re - a| < δ} ∩ {u : ℂ | zetaEntire (1 - u) ≠ 0} := by
      refine ⟨?_, hΞz⟩
      show |z.re - a| < δ
      rw [hzero, sub_self, abs_zero]; exact hδ0
    have hev : dyadicDefect w a =ᶠ[𝓝 z] dyadicDefectLeft w := by
      filter_upwards [hopen.mem_nhds hmem] with u hu
      obtain ⟨hre, hΞu⟩ := hu
      simp only [mem_setOf_eq] at hre hΞu
      unfold dyadicDefect
      split_ifs with hup
      · exact hw.dyadicDefectRight_eq_left hup (by linarith [(abs_lt.1 hre).2]) hΞu
      · rfl
    have h1 : 0 < (1 - z).re := by simp; linarith
    exact (hw.differentiableAt_dyadicDefectLeft h1 hΞz).congr_of_eventuallyEq hev
  · have hev : dyadicDefect w a =ᶠ[𝓝 z] dyadicDefectRight w := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos] with u hu
      unfold dyadicDefect
      rw [if_pos hu]
    exact (hw.differentiableAt_dyadicDefectRight hpos).congr_of_eventuallyEq hev

/-! ## Lower and upper parts -/

/-- `∫_{1/2}^1 t^{z−1} w(t) dt`, entire. -/
def upperWitnessMellin (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Ioc (1 / 2 : ℝ) 1, (t : ℂ) ^ (z - 1) * w t

/-- `∫_0^{1/2} t^{z−1} (w(t) − w(2t)) dt`. -/
def lowerDefectMellin (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) (1 / 2), (t : ℂ) ^ (z - 1) * (w t - w (2 * t))

theorem mellin_indicator_eq_setIntegral {b c : ℝ} (hb : 0 ≤ b) (f : ℝ → ℂ) (z : ℂ) :
    mellin ((Ioc b c).indicator f) z = ∫ t in Ioc b c, (t : ℂ) ^ (z - 1) * f t := by
  unfold mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun t (ht : t ∈ Ioc b c) => lt_of_le_of_lt hb ht.1)]
  · refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    rw [Set.indicator_of_mem ht, smul_eq_mul]
  · intro t ht
    rw [Set.indicator_of_notMem ht.2, smul_zero]

theorem IsMellinFermiWitness.exists_bound_upper (hw : IsMellinFermiWitness w a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (1 / 2 : ℝ) 1, ‖w t‖ ≤ C := by
  have hsub : Icc (1 / 2 : ℝ) 1 ⊆ Ioc 0 1 := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hw.cont.mono hsub)
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  exact (hC t ⟨ht.1.le, ht.2⟩).trans (le_max_left _ _)

theorem IsMellinFermiWitness.differentiable_upperWitnessMellin (hw : IsMellinFermiWitness w a) :
    Differentiable ℂ (upperWitnessMellin w) := by
  intro z
  obtain ⟨M, hM0, hM⟩ := hw.exists_bound_upper
  have heqf : upperWitnessMellin w = mellin ((Ioc (1 / 2 : ℝ) 1).indicator w) := by
    funext z; rw [mellin_indicator_eq_setIntegral (by norm_num)]; rfl
  rw [heqf]
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
    · rw [Set.indicator_of_mem ht]; exact hM t ht
    · rw [Set.indicator_of_notMem ht, norm_zero]; exact hM0
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

/-- Integrability of `t^{z−1} w(2t)` on `(0, 1/2]`, by the scaling `t ↦ 2t`. -/
theorem IsMellinFermiWitness.integrableOn_cpow_mul_comp_two (hw : IsMellinFermiWitness w a)
    {z : ℂ} (hz : a < z.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * w (2 * t)) (Ioc 0 (1 / 2)) := by
  have hG : Integrable ((Ioc (0 : ℝ) 1).indicator (fun t : ℝ => (t : ℂ) ^ (z - 1) * w t)) :=
    (hw.integrableOn_cpow_mul hz).integrable_indicator measurableSet_Ioc
  have h2 : IntegrableOn
      (fun t : ℝ => (Ioc (0 : ℝ) 1).indicator (fun t : ℝ => (t : ℂ) ^ (z - 1) * w t) (2 * t))
      (Ioc 0 (1 / 2)) :=
    (hG.comp_mul_left' (R := 2) two_ne_zero).integrableOn
  have h3 : IntegrableOn (fun t : ℝ => (2 : ℂ) ^ (1 - z) *
      (Ioc (0 : ℝ) 1).indicator (fun t : ℝ => (t : ℂ) ^ (z - 1) * w t) (2 * t))
      (Ioc 0 (1 / 2)) := h2.const_mul _
  refine h3.congr_fun (fun t ht => ?_) measurableSet_Ioc
  have ht2 : 2 * t ∈ Ioc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp only
  rw [Set.indicator_of_mem ht2, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by norm_num) ht.1.le, Complex.ofReal_ofNat]
  have h22 : (2 : ℂ) ^ (1 - z) * (2 : ℂ) ^ (z - 1) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero, show (1 : ℂ) - z + (z - 1) = 0 by ring,
      Complex.cpow_zero]
  calc (2 : ℂ) ^ (1 - z) * ((2 : ℂ) ^ (z - 1) * (t : ℂ) ^ (z - 1) * w (2 * t))
      = ((2 : ℂ) ^ (1 - z) * (2 : ℂ) ^ (z - 1)) * ((t : ℂ) ^ (z - 1) * w (2 * t)) := by ring
    _ = (t : ℂ) ^ (z - 1) * w (2 * t) := by rw [h22, one_mul]

theorem IsMellinFermiWitness.integrableOn_rpow_mul_norm_comp_two (hw : IsMellinFermiWitness w a)
    {x : ℝ} (hx : a < x) :
    IntegrableOn (fun t : ℝ => t ^ (x - 1) * ‖w (2 * t)‖) (Ioc 0 (1 / 2)) := by
  have h : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((x : ℂ) - 1) * w (2 * t)‖) (Ioc 0 (1 / 2)) :=
    (hw.integrableOn_cpow_mul_comp_two (z := (x : ℂ)) (by simpa using hx)).norm
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioc
  simp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
  simp

theorem IsMellinFermiWitness.integrableOn_rpow_mul_norm_half (hw : IsMellinFermiWitness w a)
    {x : ℝ} (hx : a < x) :
    IntegrableOn (fun t : ℝ => t ^ (x - 1) * ‖w t‖) (Ioc 0 (1 / 2)) :=
  (hw.integ x hx).mono_set (Ioc_subset_Ioc_right (by norm_num))

/-- **Splitting the right form.**  On `Re z > a`, `V = lower + upper`. -/
theorem IsMellinFermiWitness.dyadicDefectRight_eq (hw : IsMellinFermiWitness w a) {z : ℂ}
    (hz : a < z.re) :
    dyadicDefectRight w z = lowerDefectMellin w z + upperWitnessMellin w z := by
  have hsubL : Ioc (0 : ℝ) (1 / 2) ⊆ Ioc 0 1 := Ioc_subset_Ioc_right (by norm_num)
  have hsubU : Ioc (1 / 2 : ℝ) 1 ⊆ Ioc 0 1 := Ioc_subset_Ioc_left (by norm_num)
  have iL := (hw.integrableOn_cpow_mul hz).mono_set hsubL
  have iU := (hw.integrableOn_cpow_mul hz).mono_set hsubU
  have iL2 := hw.integrableOn_cpow_mul_comp_two hz
  have hdil : (2 : ℂ) ^ (-z) * witnessMellin w z =
      ∫ t in Ioc (0 : ℝ) (1 / 2), (t : ℂ) ^ (z - 1) * w (2 * t) := by
    have h := mellin_comp_mul_left (unitExt w) z (by norm_num : (0 : ℝ) < 2)
    rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num, smul_eq_mul] at h
    rw [witnessMellin_eq_mellin, ← h]
    unfold mellin
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
    · refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      beta_reduce
      rw [smul_eq_mul, unitExt, Set.indicator_of_mem
        (show 2 * t ∈ Ioc (0 : ℝ) 1 from ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
    · intro t ht
      have ht1 : 1 / 2 < t := by
        rcases ht with ⟨ht0, htn⟩
        simp only [mem_Ioc, not_and, not_le] at htn
        exact htn ht0
      beta_reduce
      rw [unitExt, Set.indicator_of_notMem (fun (h : 2 * t ∈ Ioc (0 : ℝ) 1) => by linarith [h.2]),
        smul_zero]
  have hsplit : witnessMellin w z =
      (∫ t in Ioc (0 : ℝ) (1 / 2), (t : ℂ) ^ (z - 1) * w t) +
        ∫ t in Ioc (1 / 2 : ℝ) 1, (t : ℂ) ^ (z - 1) * w t := by
    unfold witnessMellin
    rw [← Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1), setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc iL iU]
  unfold dyadicDefectRight lowerDefectMellin upperWitnessMellin
  rw [sub_mul, one_mul, hdil, hsplit]
  have hsub : (∫ t in Ioc (0 : ℝ) (1 / 2), (t : ℂ) ^ (z - 1) * (w t - w (2 * t))) =
      (∫ t in Ioc (0 : ℝ) (1 / 2), (t : ℂ) ^ (z - 1) * w t) -
        ∫ t in Ioc (0 : ℝ) (1 / 2), (t : ℂ) ^ (z - 1) * w (2 * t) := by
    rw [← integral_sub iL iL2]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    ring
  rw [hsub]
  ring

/-! ## The transform `U(z) = 2^z (V(z) − ∫_{1/2}^1 t^{z−1} w)` -/

/-- The transform `U`. -/
def dyadicDefectTransform (w : ℝ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  (2 : ℂ) ^ z * (dyadicDefect w a z - upperWitnessMellin w z)

theorem IsMellinFermiWitness.differentiable_dyadicDefectTransform (hw : IsMellinFermiWitness w a)
    (hΞ : ∀ z : ℂ, z.re ≤ a → zetaEntire (1 - z) ≠ 0) :
    Differentiable ℂ (dyadicDefectTransform w a) := by
  intro z
  exact (differentiableAt_id.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))).mul
    ((hw.differentiable_dyadicDefect hΞ z).sub (hw.differentiable_upperWitnessMellin z))

theorem two_cpow_mul_two_cpow_neg (z : ℂ) : (2 : ℂ) ^ z * (2 : ℂ) ^ (-z) = 1 := by
  rw [← Complex.cpow_add _ _ two_ne_zero, add_neg_cancel, Complex.cpow_zero]

theorem norm_two_cpow (z : ℂ) : ‖(2 : ℂ) ^ z‖ = (2 : ℝ) ^ z.re := by
  have := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) z
  rwa [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num] at this

theorem IsMellinFermiWitness.dyadicDefectTransform_eq_of_lt_re (hw : IsMellinFermiWitness w a)
    {z : ℂ} (hz : a < z.re) :
    dyadicDefectTransform w a z = (2 : ℂ) ^ z * lowerDefectMellin w z := by
  unfold dyadicDefectTransform dyadicDefect
  rw [if_pos hz, hw.dyadicDefectRight_eq hz, add_sub_cancel_right]

/-- `2^x t^{x−1} ≤ 2 t^{x₁−1}` for `0 < t ≤ 1/2`, `x ≥ x₁`, `x₁ ≤ 1`. -/
theorem two_rpow_mul_rpow_le {t x x₁ : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2) (hx : x₁ ≤ x)
    (hx₁ : x₁ ≤ 1) : (2 : ℝ) ^ x * t ^ (x - 1) ≤ 2 * t ^ (x₁ - 1) := by
  have ht1 : t ≤ 1 := by linarith
  rcases le_total x 1 with hx1 | hx1
  · have h1 : (2 : ℝ) ^ x ≤ 2 := by
      calc (2 : ℝ) ^ x ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hx1
        _ = 2 := Real.rpow_one 2
    have h2 : t ^ (x - 1) ≤ t ^ (x₁ - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith)
    exact mul_le_mul h1 h2 (Real.rpow_nonneg ht0.le _) (by norm_num)
  · have hsplit : (2 : ℝ) ^ x * t ^ (x - 1) = 2 * (2 * t) ^ (x - 1) := by
      rw [Real.mul_rpow (by norm_num) ht0.le, ← mul_assoc, ← Real.rpow_one_add' (by norm_num)
        (by linarith)]
      ring_nf
    have h1 : (2 * t) ^ (x - 1) ≤ 1 :=
      Real.rpow_le_one (by positivity) (by linarith) (by linarith)
    have h2 : 1 ≤ t ^ (x₁ - 1) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
    rw [hsplit]
    nlinarith

/-- The constant bounding `U` on `Re z ≥ x₁`. -/
def rightDefectBound (w : ℝ → ℂ) (x₁ : ℝ) : ℝ :=
  2 * ∫ t in Ioc (0 : ℝ) (1 / 2), t ^ (x₁ - 1) * (‖w t‖ + ‖w (2 * t)‖)

/-- **The right bound.**  For `a < x₁ ≤ 1` and `Re z ≥ x₁`, `‖U(z)‖ ≤ rightDefectBound w x₁`. -/
theorem IsMellinFermiWitness.norm_dyadicDefectTransform_le_right (hw : IsMellinFermiWitness w a)
    {x₁ : ℝ} (hx₁ : a < x₁) (hx₁1 : x₁ ≤ 1) {z : ℂ} (hz : x₁ ≤ z.re) :
    ‖dyadicDefectTransform w a z‖ ≤ rightDefectBound w x₁ := by
  rw [hw.dyadicDefectTransform_eq_of_lt_re (by linarith), norm_mul, norm_two_cpow]
  unfold lowerDefectMellin rightDefectBound
  have hI : IntegrableOn (fun t : ℝ => t ^ (x₁ - 1) * (‖w t‖ + ‖w (2 * t)‖)) (Ioc 0 (1 / 2)) := by
    refine ((hw.integrableOn_rpow_mul_norm_half hx₁).add
      (hw.integrableOn_rpow_mul_norm_comp_two hx₁)).congr_fun (fun t _ => ?_) measurableSet_Ioc
    simp only [Pi.add_apply]; ring
  have h2x : 0 ≤ (2 : ℝ) ^ z.re := Real.rpow_nonneg (by norm_num) _
  calc (2 : ℝ) ^ z.re * ‖∫ t in Ioc (0 : ℝ) (1 / 2), (t : ℂ) ^ (z - 1) * (w t - w (2 * t))‖
      = ‖∫ t in Ioc (0 : ℝ) (1 / 2),
          (((2 : ℝ) ^ z.re : ℝ) : ℂ) * ((t : ℂ) ^ (z - 1) * (w t - w (2 * t)))‖ := by
        rw [integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2x]
    _ ≤ ∫ t in Ioc (0 : ℝ) (1 / 2), 2 * (t ^ (x₁ - 1) * (‖w t‖ + ‖w (2 * t)‖)) := by
        refine norm_integral_le_of_norm_le (hI.const_mul 2)
          (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2x, norm_mul,
          Complex.norm_cpow_eq_rpow_re_of_pos ht.1, Complex.sub_re, Complex.one_re]
        have hd : ‖w t - w (2 * t)‖ ≤ ‖w t‖ + ‖w (2 * t)‖ := norm_sub_le _ _
        have hk := two_rpow_mul_rpow_le ht.1 ht.2 hz hx₁1
        have htp : 0 ≤ t ^ (z.re - 1) := Real.rpow_nonneg ht.1.le _
        calc (2 : ℝ) ^ z.re * (t ^ (z.re - 1) * ‖w t - w (2 * t)‖)
            ≤ (2 : ℝ) ^ z.re * (t ^ (z.re - 1) * (‖w t‖ + ‖w (2 * t)‖)) := by gcongr
          _ = ((2 : ℝ) ^ z.re * t ^ (z.re - 1)) * (‖w t‖ + ‖w (2 * t)‖) := by ring
          _ ≤ (2 * t ^ (x₁ - 1)) * (‖w t‖ + ‖w (2 * t)‖) :=
              mul_le_mul_of_nonneg_right hk (by positivity)
          _ = 2 * (t ^ (x₁ - 1) * (‖w t‖ + ‖w (2 * t)‖)) := by ring
    _ = 2 * ∫ t in Ioc (0 : ℝ) (1 / 2), t ^ (x₁ - 1) * (‖w t‖ + ‖w (2 * t)‖) :=
        integral_const_mul _ _

/-- **`U` tends to zero along the integers:** `U(n+1) = ∫_0^{1/2} 2(2t)^n (w(t) − w(2t)) dt`. -/
theorem IsMellinFermiWitness.tendsto_dyadicDefectTransform_nat (hw : IsMellinFermiWitness w a) :
    Tendsto (fun n : ℕ => dyadicDefectTransform w a ((n : ℂ) + 1)) atTop (𝓝 0) := by
  have hre : ∀ n : ℕ, a < ((n : ℂ) + 1).re := fun n => by
    have h1 := hw.lt_one
    have h2 : (0 : ℝ) ≤ n := n.cast_nonneg
    simp; linarith
  have hform : ∀ n : ℕ, dyadicDefectTransform w a ((n : ℂ) + 1) =
      ∫ t in Ioo (0 : ℝ) (1 / 2), (((2 * (2 * t) ^ n : ℝ)) : ℂ) * (w t - w (2 * t)) := by
    intro n
    rw [hw.dyadicDefectTransform_eq_of_lt_re (hre n), lowerDefectMellin, ← integral_const_mul,
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t _ => ?_)
    have e1 : (2 : ℂ) ^ ((n : ℂ) + 1) = (2 : ℂ) ^ (n + 1) := by
      rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]
    have e2 : (t : ℂ) ^ ((n : ℂ) + 1 - 1) = (t : ℂ) ^ n := by
      rw [show ((n : ℂ) + 1 - 1) = (n : ℂ) by ring, Complex.cpow_natCast]
    rw [e1, e2]
    push_cast
    ring
  have hsubL : Ioo (0 : ℝ) (1 / 2) ⊆ Ioc 0 (1 / 2) := Ioo_subset_Ioc_self
  have hI1 : IntegrableOn (fun t : ℝ => ‖w t‖) (Ioo 0 (1 / 2)) :=
    ((hw.integrableOn_rpow_mul_norm_half hw.lt_one).mono_set hsubL).congr_fun
      (fun t _ => by simp) measurableSet_Ioo
  have hI2 : IntegrableOn (fun t : ℝ => ‖w (2 * t)‖) (Ioo 0 (1 / 2)) :=
    ((hw.integrableOn_rpow_mul_norm_comp_two hw.lt_one).mono_set hsubL).congr_fun
      (fun t _ => by simp) measurableSet_Ioo
  have hbound : Integrable (fun t : ℝ => 2 * (‖w t‖ + ‖w (2 * t)‖))
      (volume.restrict (Ioo (0 : ℝ) (1 / 2))) := (hI1.add hI2).const_mul 2
  have hcont : ContinuousOn (fun t : ℝ => w t - w (2 * t)) (Ioo 0 (1 / 2)) := by
    refine (hw.cont.mono (fun t ht => ⟨ht.1, by linarith [ht.2]⟩)).sub ?_
    exact hw.cont.comp (continuousOn_const.mul continuousOn_id)
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioo (0 : ℝ) (1 / 2)))
    (F := fun (n : ℕ) (t : ℝ) => (((2 * (2 * t) ^ n : ℝ)) : ℂ) * (w t - w (2 * t)))
    (f := fun _ => 0) _
    (fun n => ((Complex.continuous_ofReal.comp (continuous_const.mul
      ((continuous_const.mul continuous_id).pow n))).continuousOn.mul hcont).aestronglyMeasurable
      measurableSet_Ioo)
    hbound
    (fun n => ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => by
      have h2t : 0 ≤ 2 * t := by linarith [ht.1]
      have hp : (2 * t) ^ n ≤ 1 := pow_le_one₀ h2t (by linarith [ht.2])
      have hp0 : 0 ≤ (2 * t) ^ n := pow_nonneg h2t n
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc 2 * (2 * t) ^ n * ‖w t - w (2 * t)‖ ≤ 2 * 1 * (‖w t‖ + ‖w (2 * t)‖) :=
            mul_le_mul (by nlinarith) (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
        _ = 2 * (‖w t‖ + ‖w (2 * t)‖) := by ring)
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => by
      have h2t : 0 ≤ 2 * t := by linarith [ht.1]
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one h2t (by linarith [ht.2])
      have h3 : Tendsto (fun n : ℕ => (((2 * (2 * t) ^ n : ℝ)) : ℂ)) atTop (𝓝 ((2 * 0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp (hp.const_mul 2)
      simpa using h3.mul_const (w t - w (2 * t)))
  simp only [integral_zero] at hlim
  exact hlim.congr (fun n => (hform n).symm)

/-- The constant bounding `2^z ∫_{1/2}^1 t^{z−1} w` on `Re z ≤ 1`. -/
def upperDefectBound (w : ℝ → ℂ) : ℝ := 2 * ∫ t in Ioc (1 / 2 : ℝ) 1, ‖w t‖

/-- On `Re z ≤ 1`, `‖2^z ∫_{1/2}^1 t^{z−1} w‖ ≤ 2 ∫_{1/2}^1 |w|`. -/
theorem IsMellinFermiWitness.norm_two_cpow_mul_upperWitnessMellin_le
    (hw : IsMellinFermiWitness w a) {z : ℂ} (hz : z.re ≤ 1) :
    ‖(2 : ℂ) ^ z * upperWitnessMellin w z‖ ≤ upperDefectBound w := by
  have hI : IntegrableOn (fun t : ℝ => ‖w t‖) (Ioc (1 / 2) 1) :=
    hw.integrableOn_norm.mono_set (Ioc_subset_Ioc_left (by norm_num))
  unfold upperWitnessMellin upperDefectBound
  rw [← integral_const_mul, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hI.const_mul 2)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := by linarith [ht.1]
  rw [norm_mul, norm_mul, norm_two_cpow, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
    Complex.sub_re, Complex.one_re, ← mul_assoc]
  have hk : (2 : ℝ) ^ z.re * t ^ (z.re - 1) ≤ 2 := by
    have hsplit : (2 : ℝ) ^ z.re * t ^ (z.re - 1) = 2 * (2 * t) ^ (z.re - 1) := by
      rw [Real.mul_rpow (by norm_num) ht0.le]
      have h2 : (2 : ℝ) ^ z.re = 2 * (2 : ℝ) ^ (z.re - 1) := by
        rw [show (2 : ℝ) * (2 : ℝ) ^ (z.re - 1) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (z.re - 1) by
          rw [Real.rpow_one], ← Real.rpow_add (by norm_num)]
        ring_nf
      rw [h2]; ring
    rw [hsplit]
    have : (2 * t) ^ (z.re - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [ht.1]) (by linarith)
    linarith
  exact mul_le_mul_of_nonneg_right hk (norm_nonneg _)

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

/-- **The left bound.**  For `Re z < 1`, `z ≠ 0`, and `ζ(1 − z) ≠ 0` when `Re z > a`:
`‖U(z)‖ ≤ ‖1 − z‖ · 3m(1)/(1 − Re z) · ‖ζ(1 − z)‖⁻¹ + 2∫_{1/2}^1 |w|`. -/
theorem IsMellinFermiWitness.norm_dyadicDefectTransform_le_left (hw : IsMellinFermiWitness w a)
    {z : ℂ} (hz1 : z.re < 1) (hz0 : z ≠ 0) (hζ : a < z.re → riemannZeta (1 - z) ≠ 0) :
    ‖dyadicDefectTransform w a z‖ ≤
      ‖1 - z‖ * (3 * witnessMajorant w 1 / (1 - z.re)) * (1 / ‖riemannZeta (1 - z)‖) +
        upperDefectBound w := by
  have hne1 : (1 : ℂ) - z ≠ 1 := by intro h; apply hz0; linear_combination -h
  have hV : dyadicDefect w a z = dyadicDefectLeft w z := by
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
