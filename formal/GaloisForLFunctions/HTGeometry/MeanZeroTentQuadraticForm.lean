import Mathlib

/-!
# Tent kernels on mean-zero tests

Let `g` be continuous, vanishing for `|x| ≥ R`, with `∫ g = 0`, and let `Γ(x) = ∫_{-R}^x g` be its
primitive; `Γ` vanishes for `|x| ≥ R`.  For every `w ≥ 0`,

`∫∫ conj (g s) g t (t - s - w)₊ ds dt = -∫ conj (Γ x) Γ(x + w) dx`,

since `(t - s - w)₊` is the length of `{x : s ≤ x ≤ t - w}` and `∫_{t ≥ y} g = -Γ(y)`.  The symmetric
tent `(|t - s| - w)₊` therefore has form `-2 Re ∫ conj Γ · Γ(· + w)`, of modulus at most `2 ‖Γ‖²`,
and the kernel `|t - s|` (`w = 0`) has form exactly `-2 ‖Γ‖²`.
-/

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

/-- A function bounded by a constant on a set of finite measure and vanishing off it is
integrable. -/
theorem integrable_of_norm_le_indicator_const {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ s.indicator (fun _ => C) x) :
    Integrable f μ :=
  Integrable.mono' ((integrableOn_const hμs).integrable_indicator hs) hf
    (Filter.Eventually.of_forall hC)

/-- The almost-everywhere version. -/
theorem integrable_of_ae_norm_le_indicator_const {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ s.indicator (fun _ => C) x) :
    Integrable f μ :=
  Integrable.mono' ((integrableOn_const hμs).integrable_indicator hs) hf hC

/-- The primitive `Γ(x) = ∫_{-R}^x g`. -/
def tentPrimitive (g : ℝ → ℂ) (R x : ℝ) : ℂ := ∫ t in (-R)..x, g t

section Support

variable {g : ℝ → ℂ} {R : ℝ} (hg : Continuous g) (hsupp : ∀ x, R ≤ |x| → g x = 0)
include hsupp

theorem tent_eq_zero_of_le_neg {x : ℝ} (hx : x ≤ -R) : g x = 0 := by
  refine hsupp x ?_
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_neg h]; linarith

theorem tent_eq_zero_of_ge {x : ℝ} (hx : R ≤ x) : g x = 0 := hsupp x (hx.trans (le_abs_self x))

theorem tent_eq_zero_of_notMem {x : ℝ} (hx : x ∉ Icc (-R) R) : g x = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · exact tent_eq_zero_of_le_neg hsupp h.le
  · exact tent_eq_zero_of_ge hsupp h.le

include hg

theorem tent_integrable : Integrable g volume :=
  hg.integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc fun _ hx => tent_eq_zero_of_notMem hsupp hx)

theorem tent_exists_bound : ∃ M, 0 ≤ M ∧ ∀ x, ‖g x‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (-R) R
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [tent_eq_zero_of_notMem hsupp hx, norm_zero]
    exact le_max_right _ _

theorem setIntegral_Iic_eq_tentPrimitive (x : ℝ) :
    ∫ t in Iic x, g t = tentPrimitive g R x := by
  have hi := tent_integrable hg hsupp
  have h0 : ∫ t in Iic (-R), g t = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun t ht => tent_eq_zero_of_le_neg hsupp ht
  rw [tentPrimitive, ← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn, h0,
    sub_zero]

theorem setIntegral_Ici_eq_neg_tentPrimitive (hmean : ∫ x, g x = 0) (y : ℝ) :
    ∫ t in Ici y, g t = -tentPrimitive g R y := by
  have h := integral_add_compl (measurableSet_Ici (a := y)) (tent_integrable hg hsupp)
  rw [compl_Ici, ← integral_Iic_eq_integral_Iio, setIntegral_Iic_eq_tentPrimitive hg hsupp,
    hmean] at h
  linear_combination h

theorem tentPrimitive_eq_zero (hmean : ∫ x, g x = 0) {x : ℝ} (hx : R ≤ |x|) :
    tentPrimitive g R x = 0 := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx
    rw [← neg_eq_zero, ← setIntegral_Ici_eq_neg_tentPrimitive hg hsupp hmean]
    exact setIntegral_eq_zero_of_forall_eq_zero fun t ht => tent_eq_zero_of_ge hsupp (hx.trans ht)
  · rw [abs_of_neg h] at hx
    rw [← setIntegral_Iic_eq_tentPrimitive hg hsupp]
    exact setIntegral_eq_zero_of_forall_eq_zero fun t ht =>
      tent_eq_zero_of_le_neg hsupp (le_trans (mem_Iic.mp ht) (by linarith))

omit hsupp in
theorem continuous_tentPrimitive : Continuous (tentPrimitive g R) :=
  intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) (-R)

end Support

section Tent

variable {g : ℝ → ℂ} {R : ℝ} (hg : Continuous g) (hsupp : ∀ x, R ≤ |x| → g x = 0)
include hg hsupp

omit hg hsupp in
theorem measure_Icc_prod_Icc_ne_top (a b : ℝ) :
    (volume.prod volume) (Icc a b ×ˢ Icc a b) ≠ ⊤ := by
  rw [Measure.prod_prod]
  exact ENNReal.mul_ne_top (by simp [Real.volume_Icc]) (by simp [Real.volume_Icc])

omit hg hsupp in
theorem continuous_conj_mul_mul (hg : Continuous g) {k : ℝ × ℝ → ℝ} (hk : Continuous k) :
    Continuous fun p : ℝ × ℝ => conj (g p.1) * g p.2 * ((k p : ℝ) : ℂ) :=
  ((Complex.continuous_conj.comp (hg.comp continuous_fst)).mul (hg.comp continuous_snd)).mul
    (Complex.continuous_ofReal.comp hk)

/-- A plane integrand `conj (g s) g t k(s, t)` with `|k| ≤ C` on the support square is
integrable. -/
theorem integrable_conj_mul_mul {k : ℝ × ℝ → ℝ} (hk : Continuous k) {C : ℝ}
    (hkC : ∀ p : ℝ × ℝ, p ∈ Icc (-R) R ×ˢ Icc (-R) R → |k p| ≤ C) :
    Integrable (fun p : ℝ × ℝ => conj (g p.1) * g p.2 * ((k p : ℝ) : ℂ)) (volume.prod volume) := by
  obtain ⟨M, hM0, hM⟩ := tent_exists_bound hg hsupp
  refine integrable_of_norm_le_indicator_const (measurableSet_Icc.prod measurableSet_Icc)
    (measure_Icc_prod_Icc_ne_top (-R) R)
    (continuous_conj_mul_mul hg hk).aestronglyMeasurable (C := M * M * C) fun p => ?_
  by_cases hp : p ∈ Icc (-R) R ×ˢ Icc (-R) R
  · rw [indicator_of_mem hp, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_mul (mul_le_mul (hM _) (hM _) (norm_nonneg _) hM0) (hkC p hp) (abs_nonneg _)
      (mul_nonneg hM0 hM0)
  · rw [indicator_of_notMem hp]
    rw [mem_prod, not_and_or] at hp
    rcases hp with h | h
    · simp [tent_eq_zero_of_notMem hsupp h]
    · simp [tent_eq_zero_of_notMem hsupp h]

variable (hmean : ∫ x, g x = 0)
include hmean

/-- **One-sided tent.**  `∫∫ conj (g s) g t (t - s - w)₊ = -∫ conj (Γ x) Γ(x + w)`. -/
theorem integral_integral_mul_tent_right {w : ℝ} (hw : 0 ≤ w) :
    ∫ s, ∫ t, conj (g s) * g t * ((max (t - s - w) 0 : ℝ) : ℂ) =
      -∫ x, conj (tentPrimitive g R x) * tentPrimitive g R (x + w) := by
  obtain ⟨M, hM0, hM⟩ := tent_exists_bound hg hsupp
  have hk : Continuous fun p : ℝ × ℝ => max (p.2 - p.1 - w) 0 := by fun_prop
  have hF := integrable_conj_mul_mul hg hsupp hk (C := 2 * R) fun p hp => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (by linarith)
  rw [← integral_prod _ hF]
  -- `(t - s - w)₊` is the length of `[s, t - w]`
  set S : Set ((ℝ × ℝ) × ℝ) := {q | q.1.1 ≤ q.2 ∧ q.2 ≤ q.1.2 - w}
  have hS : MeasurableSet S :=
    (measurableSet_le (measurable_fst.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd ((measurable_snd.comp measurable_fst).sub_const w))
  set H : (ℝ × ℝ) × ℝ → ℂ := fun q =>
    conj (g q.1.1) * g q.1.2 * ((S.indicator (fun _ => (1 : ℝ)) q : ℝ) : ℂ)
  have hpt : ∀ p : ℝ × ℝ, conj (g p.1) * g p.2 * ((max (p.2 - p.1 - w) 0 : ℝ) : ℂ) =
      ∫ x, H (p, x) := by
    intro p
    have hind : ∀ x, S.indicator (fun _ => (1 : ℝ)) (p, x) =
        (Icc p.1 (p.2 - w)).indicator 1 x := by
      intro x
      by_cases hx : x ∈ Icc p.1 (p.2 - w)
      · rw [indicator_of_mem (show (p, x) ∈ S from hx), indicator_of_mem hx, Pi.one_apply]
      · rw [indicator_of_notMem (show (p, x) ∉ S from hx), indicator_of_notMem hx]
    simp only [H, hind]
    rw [integral_const_mul, integral_complex_ofReal, integral_indicator_one measurableSet_Icc,
      Real.volume_real_Icc]
    congr 3
    ring
  simp_rw [hpt]
  have hH : Integrable H ((volume.prod volume).prod volume) := by
    refine integrable_of_norm_le_indicator_const (s := (Icc (-R) R ×ˢ Icc (-R) R) ×ˢ Icc (-R) R)
      ((measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Icc) ?_ ?_
      (C := M * M) fun q => ?_
    · rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top (measure_Icc_prod_Icc_ne_top (-R) R)
        (by simp [Real.volume_Icc])
    · exact (((Complex.continuous_conj.comp (hg.comp (continuous_fst.comp continuous_fst))).mul
        (hg.comp (continuous_snd.comp continuous_fst))).aestronglyMeasurable).mul
        ((Complex.measurable_ofReal.comp ((measurable_const.indicator hS))).aestronglyMeasurable)
    · by_cases hq : q.1.1 ∈ Icc (-R) R ∧ q.1.2 ∈ Icc (-R) R ∧ q ∈ S
      · obtain ⟨h1, h2, h3⟩ := hq
        have hqbox : q ∈ (Icc (-R) R ×ˢ Icc (-R) R) ×ˢ Icc (-R) R :=
          ⟨⟨h1, h2⟩, ⟨by linarith [h1.1, h3.1], by linarith [h2.2, h3.2]⟩⟩
        rw [indicator_of_mem hqbox]
        simp only [H, indicator_of_mem h3, Complex.ofReal_one, mul_one, norm_mul, Complex.norm_conj]
        exact mul_le_mul (hM _) (hM _) (norm_nonneg _) hM0
      · have hzero : H q = 0 := by
          simp only [H]
          rw [not_and_or, not_and_or] at hq
          rcases hq with h | h | h
          · rw [tent_eq_zero_of_notMem hsupp h]; simp
          · rw [tent_eq_zero_of_notMem hsupp h]; simp
          · rw [indicator_of_notMem h]; simp
        rw [hzero, norm_zero]
        exact indicator_nonneg (fun _ _ => mul_nonneg hM0 hM0) _
  rw [integral_integral_swap (f := fun p x => H (p, x)) hH]
  -- separation of variables
  have hsep : ∀ x, ∫ p : ℝ × ℝ, H (p, x) ∂(volume.prod volume) =
      conj (tentPrimitive g R x) * -tentPrimitive g R (x + w) := by
    intro x
    have hfac : ∀ p : ℝ × ℝ, H (p, x) =
        (Iic x).indicator (fun s => conj (g s)) p.1 * (Ici (x + w)).indicator g p.2 := by
      intro p
      simp only [H, S]
      by_cases h1 : p.1 ≤ x <;> by_cases h2 : x + w ≤ p.2
      · rw [indicator_of_mem (show (p, x) ∈ S from ⟨h1, by linarith⟩),
          indicator_of_mem (show p.1 ∈ Iic x from h1), indicator_of_mem (show p.2 ∈ Ici (x + w) from h2)]
        simp
      · rw [indicator_of_notMem (show (p, x) ∉ S from fun h => h2 (by linarith [h.2])),
          indicator_of_notMem (show p.2 ∉ Ici (x + w) from h2)]
        simp
      · rw [indicator_of_notMem (show (p, x) ∉ S from fun h => h1 h.1),
          indicator_of_notMem (show p.1 ∉ Iic x from h1)]
        simp
      · rw [indicator_of_notMem (show (p, x) ∉ S from fun h => h1 h.1),
          indicator_of_notMem (show p.1 ∉ Iic x from h1)]
        simp
    simp_rw [hfac]
    rw [integral_prod_mul, integral_indicator measurableSet_Iic, integral_indicator measurableSet_Ici,
      integral_conj, setIntegral_Iic_eq_tentPrimitive hg hsupp,
      setIntegral_Ici_eq_neg_tentPrimitive hg hsupp hmean]
  simp_rw [hsep]
  rw [← integral_neg]
  congr 1
  funext x
  ring

theorem integrable_tentPrimitive_sq :
    Integrable (fun x => ‖tentPrimitive g R x‖ ^ 2) volume := by
  refine (((continuous_tentPrimitive hg).norm.pow 2)).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun x hx => ?_
  have hxR : R ≤ |x| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · exact (by linarith : R ≤ -x).trans (neg_le_abs x)
    · exact (h.le.trans (le_abs_self x))
  simp [tentPrimitive_eq_zero hg hsupp hmean hxR]

/-- `|∫ conj (Γ x) Γ(x + w)| ≤ ‖Γ‖²`. -/
theorem norm_integral_conj_tentPrimitive_mul_le (w : ℝ) :
    ‖∫ x, conj (tentPrimitive g R x) * tentPrimitive g R (x + w)‖ ≤
      ∫ x, ‖tentPrimitive g R x‖ ^ 2 := by
  set Γ := tentPrimitive g R
  have hsq := integrable_tentPrimitive_sq hg hsupp hmean
  have hsq' : Integrable (fun x => ‖Γ (x + w)‖ ^ 2) volume := hsq.comp_add_right w
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ x, ‖conj (Γ x) * Γ (x + w)‖
      ≤ ∫ x, (‖Γ x‖ ^ 2 + ‖Γ (x + w)‖ ^ 2) / 2 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
          ((hsq.add hsq').div_const 2) (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [norm_mul, Complex.norm_conj]
        nlinarith [sq_nonneg (‖Γ x‖ - ‖Γ (x + w)‖)]
    _ = ∫ x, ‖Γ x‖ ^ 2 := by
        rw [integral_div, integral_add hsq hsq',
          integral_add_right_eq_self (fun x => ‖Γ x‖ ^ 2) w]
        ring

/-- **Symmetric tent.**
`∫∫ conj (g s) g t (|t - s| - w)₊ = -(I + conj I)`, `I = ∫ conj (Γ x) Γ(x + w)`. -/
theorem integral_integral_mul_tent {w : ℝ} (hw : 0 ≤ w) :
    ∫ s, ∫ t, conj (g s) * g t * ((max (|t - s| - w) 0 : ℝ) : ℂ) =
      -((∫ x, conj (tentPrimitive g R x) * tentPrimitive g R (x + w)) +
        conj (∫ x, conj (tentPrimitive g R x) * tentPrimitive g R (x + w))) := by
  have hkR : Continuous fun p : ℝ × ℝ => max (p.2 - p.1 - w) 0 := by fun_prop
  have hkL : Continuous fun p : ℝ × ℝ => max (p.1 - p.2 - w) 0 := by fun_prop
  have hkA : Continuous fun p : ℝ × ℝ => max (|p.2 - p.1| - w) 0 := by fun_prop
  have hbound : ∀ p : ℝ × ℝ, p ∈ Icc (-R) R ×ˢ Icc (-R) R → |p.2 - p.1| ≤ 2 * R := by
    intro p hp
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
    rw [abs_le]; constructor <;> linarith
  have hFA := integrable_conj_mul_mul hg hsupp hkA (C := 2 * R) fun p hp => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [hbound p hp]) (by linarith [abs_nonneg (p.2 - p.1), hbound p hp])
  have hFR := integrable_conj_mul_mul hg hsupp hkR (C := 2 * R) fun p hp => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [le_abs_self (p.2 - p.1), hbound p hp])
      (by linarith [abs_nonneg (p.2 - p.1), hbound p hp])
  have hFL := integrable_conj_mul_mul hg hsupp hkL (C := 2 * R) fun p hp => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [neg_abs_le (p.2 - p.1), hbound p hp])
      (by linarith [abs_nonneg (p.2 - p.1), hbound p hp])
  have hsplit : ∀ p : ℝ × ℝ, max (|p.2 - p.1| - w) 0 = max (p.2 - p.1 - w) 0 +
      max (p.1 - p.2 - w) 0 := by
    intro p
    rcases le_total 0 (p.2 - p.1) with h | h
    · rw [abs_of_nonneg h, max_eq_right (show p.1 - p.2 - w ≤ 0 by linarith), add_zero]
    · rw [abs_of_nonpos h, max_eq_right (show p.2 - p.1 - w ≤ 0 by linarith), zero_add]
      congr 1; ring
  rw [← integral_prod _ hFA]
  have hsum : (fun p : ℝ × ℝ => conj (g p.1) * g p.2 * ((max (|p.2 - p.1| - w) 0 : ℝ) : ℂ)) =
      fun p => conj (g p.1) * g p.2 * ((max (p.2 - p.1 - w) 0 : ℝ) : ℂ) +
        conj (g p.1) * g p.2 * ((max (p.1 - p.2 - w) 0 : ℝ) : ℂ) := by
    funext p
    rw [hsplit p]
    push_cast
    ring
  rw [hsum, integral_add hFR hFL]
  have hR : ∫ p : ℝ × ℝ, conj (g p.1) * g p.2 * ((max (p.2 - p.1 - w) 0 : ℝ) : ℂ)
      ∂(volume.prod volume) =
        -∫ x, conj (tentPrimitive g R x) * tentPrimitive g R (x + w) := by
    rw [integral_prod _ hFR]
    exact integral_integral_mul_tent_right hg hsupp hmean hw
  have hL : ∫ p : ℝ × ℝ, conj (g p.1) * g p.2 * ((max (p.1 - p.2 - w) 0 : ℝ) : ℂ)
      ∂(volume.prod volume) =
        conj (∫ p : ℝ × ℝ, conj (g p.1) * g p.2 * ((max (p.2 - p.1 - w) 0 : ℝ) : ℂ)
          ∂(volume.prod volume)) := by
    rw [← integral_conj, ← integral_prod_swap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Prod.fst_swap, Prod.snd_swap, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  rw [hL, hR, map_neg]
  ring

/-- **The kernel `|t - s|`.**  `∫∫ conj (g s) g t |t - s| = -2 ‖Γ‖²`. -/
theorem integral_integral_mul_abs_sub :
    ∫ s, ∫ t, conj (g s) * g t * ((|t - s| : ℝ) : ℂ) =
      -2 * ((∫ x, ‖tentPrimitive g R x‖ ^ 2 : ℝ) : ℂ) := by
  have h := integral_integral_mul_tent hg hsupp hmean (le_refl 0)
  have hmax : ∀ s t : ℝ, max (|t - s| - 0) 0 = |t - s| := fun s t => by
    rw [sub_zero, max_eq_left (abs_nonneg _)]
  simp only [hmax, add_zero] at h
  rw [h]
  have hI : ∫ x, conj (tentPrimitive g R x) * tentPrimitive g R x =
      ((∫ x, ‖tentPrimitive g R x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hI, Complex.conj_ofReal]
  ring

end Tent

section Mixture

variable {g : ℝ → ℂ} {R : ℝ} (hg : Continuous g) (hsupp : ∀ x, R ≤ |x| → g x = 0)
  (hmean : ∫ x, g x = 0)
include hg hsupp hmean

/-- **Tent mixtures.**  For continuous `h`,
`|∫∫ conj (g s) g t ∫₀^δ (|t - s| - w)₊ h(w) dw| ≤ 2 (∫₀^δ |h|) ‖Γ‖²`. -/
theorem norm_integral_integral_mul_tentMixture_le {h : ℝ → ℝ} (hh : Continuous h) (δ : ℝ) :
    ‖∫ s, ∫ t, conj (g s) * g t *
        ((∫ w in Ioc 0 δ, max (|t - s| - w) 0 * h w : ℝ) : ℂ)‖ ≤
      2 * (∫ w in Ioc 0 δ, |h w|) * ∫ x, ‖tentPrimitive g R x‖ ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := tent_exists_bound hg hsupp
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := 0) (b := δ)).exists_bound_of_continuousOn hh.continuousOn
  set Q := ∫ x, ‖tentPrimitive g R x‖ ^ 2
  have hQ : 0 ≤ Q := integral_nonneg fun x => sq_nonneg _
  -- the triple integrand on `(ℝ × ℝ) × (0, δ]`
  set K : (ℝ × ℝ) × ℝ → ℂ := fun q =>
    conj (g q.1.1) * g q.1.2 * ((max (|q.1.2 - q.1.1| - q.2) 0 * h q.2 : ℝ) : ℂ)
  have hKint : Integrable K ((volume.prod volume).prod (volume.restrict (Ioc 0 δ))) := by
    have hcont : Continuous K := by
      refine ((Complex.continuous_conj.comp (hg.comp (continuous_fst.comp continuous_fst))).mul
        (hg.comp (continuous_snd.comp continuous_fst))).mul (Complex.continuous_ofReal.comp ?_)
      exact (by fun_prop : Continuous fun q : (ℝ × ℝ) × ℝ => max (|q.1.2 - q.1.1| - q.2) 0).mul
        (hh.comp continuous_snd)
    refine integrable_of_ae_norm_le_indicator_const
      (s := (Icc (-R) R ×ˢ Icc (-R) R) ×ˢ Ioc 0 δ)
      ((measurableSet_Icc.prod measurableSet_Icc).prod measurableSet_Ioc) ?_
      hcont.aestronglyMeasurable (C := M * M * (2 * R * B)) ?_
    · rw [Measure.prod_prod]
      refine ENNReal.mul_ne_top (measure_Icc_prod_Icc_ne_top (-R) R) ?_
      rw [Measure.restrict_apply measurableSet_Ioc, inter_self]
      simp [Real.volume_Ioc]
    · have hae : ∀ᵐ q : (ℝ × ℝ) × ℝ ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
          ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) δ))),
          q.2 ∈ Ioc (0 : ℝ) δ := by
        rw [← Measure.restrict_univ (μ := (volume : Measure ℝ).prod (volume : Measure ℝ)),
          Measure.prod_restrict]
        filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioc)] with q hq
        exact hq.2
      filter_upwards [hae] with q hq2
      by_cases hq : q ∈ (Icc (-R) R ×ˢ Icc (-R) R) ×ˢ Ioc 0 δ
      · rw [indicator_of_mem hq]
        obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩ := hq
        simp only [K, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
        have hmax : |max (|q.1.2 - q.1.1| - q.2) 0| ≤ 2 * R := by
          rw [abs_of_nonneg (le_max_right _ _)]
          have : |q.1.2 - q.1.1| ≤ 2 * R := by rw [abs_le]; constructor <;> linarith
          exact max_le (by linarith) (by linarith [abs_nonneg (q.1.2 - q.1.1)])
        have hhB : |h q.2| ≤ B := by
          have := hB q.2 ⟨h5.le, h6⟩
          rwa [Real.norm_eq_abs] at this
        have hRB := mul_le_mul hmax hhB (abs_nonneg _) (by linarith [abs_nonneg (q.1.2 - q.1.1)])
        exact mul_le_mul (mul_le_mul (hM _) (hM _) (norm_nonneg _) hM0) hRB (by positivity)
          (mul_nonneg hM0 hM0)
      · rw [indicator_of_notMem hq]
        rw [mem_prod, mem_prod, not_and_or, not_and_or] at hq
        rcases hq with (hq | hq) | hq
        · simp [K, tent_eq_zero_of_notMem hsupp hq]
        · simp [K, tent_eq_zero_of_notMem hsupp hq]
        · exact absurd hq2 hq
  -- reduce to the `w`-integral of the plane forms
  have hF : ∀ p : ℝ × ℝ,
      conj (g p.1) * g p.2 * ((∫ w in Ioc 0 δ, max (|p.2 - p.1| - w) 0 * h w : ℝ) : ℂ) =
        ∫ w in Ioc 0 δ, K (p, w) := by
    intro p
    simp only [K]
    rw [integral_const_mul, integral_complex_ofReal]
  have hFint : Integrable (fun p : ℝ × ℝ =>
      conj (g p.1) * g p.2 * ((∫ w in Ioc 0 δ, max (|p.2 - p.1| - w) 0 * h w : ℝ) : ℂ))
      (volume.prod volume) := by
    simp_rw [hF]
    exact hKint.integral_prod_left
  rw [← integral_prod _ hFint]
  simp_rw [hF]
  rw [integral_integral_swap (f := fun p w => K (p, w)) hKint]
  -- each tent form is bounded by `2 |h(w)| ‖Γ‖²`
  have hpt : ∀ w ∈ Ioc (0 : ℝ) δ, ‖∫ p, K (p, w) ∂(volume.prod volume)‖ ≤ 2 * |h w| * Q := by
    intro w hw
    have hKw : ∫ p, K (p, w) ∂(volume.prod volume) = (h w : ℂ) *
        ∫ s, ∫ t, conj (g s) * g t * ((max (|t - s| - w) 0 : ℝ) : ℂ) := by
      have hk : Continuous fun p : ℝ × ℝ => max (|p.2 - p.1| - w) 0 := by fun_prop
      have hint := integrable_conj_mul_mul hg hsupp hk (C := 2 * R + |w|) fun p hp => by
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
        rw [abs_of_nonneg (le_max_right _ _)]
        have : |p.2 - p.1| ≤ 2 * R := by rw [abs_le]; constructor <;> linarith
        exact max_le (by linarith [neg_abs_le w]) (by linarith [abs_nonneg (p.2 - p.1), abs_nonneg w])
      rw [← integral_prod _ hint, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only [K]
      push_cast
      ring
    rw [hKw, integral_integral_mul_tent hg hsupp hmean hw.1.le, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, norm_neg]
    have hI := norm_integral_conj_tentPrimitive_mul_le hg hsupp hmean w
    have h2 : ‖(∫ x, conj (tentPrimitive g R x) * tentPrimitive g R (x + w)) +
        conj (∫ x, conj (tentPrimitive g R x) * tentPrimitive g R (x + w))‖ ≤ 2 * Q := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_conj]
      linarith
    calc |h w| * ‖(∫ x, conj (tentPrimitive g R x) * tentPrimitive g R (x + w)) +
          conj (∫ x, conj (tentPrimitive g R x) * tentPrimitive g R (x + w))‖
        ≤ |h w| * (2 * Q) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = 2 * |h w| * Q := by ring
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [show 2 * (∫ w in Ioc 0 δ, |h w|) * Q = ∫ w in Ioc 0 δ, 2 * |h w| * Q by
    rw [integral_mul_const, integral_const_mul]]
  refine setIntegral_mono_on hKint.integral_prod_right.norm ?_ measurableSet_Ioc hpt
  exact ((continuous_const.mul hh.abs).mul continuous_const).integrableOn_Ioc

end Mixture



end GaloisForLFunctions.HTGeometry
