import GaloisForLFunctions.RHTower.CHMDMasslessCramerContinuation

/-!
# CHMD: the massless zero-side wave across the whole boundary

The massless wave `Φ₀(v) = Σ_ρ m_ρ cos(v γ_ρ) sech²(γ_ρ/2)` is even and real on the real axis:
`Φ₀(−v) = Φ₀(v)`, `Φ₀(v̄) = conj Φ₀(v)` (`masslessZeroWave_neg`, `masslessZeroWave_conj`).  The
continuations `masslessContinuation a` (cutoff `0 < a ≤ 1/2`, valid on `Re v > a`) agree with each other
(`archContinuation_congr`), so choosing the cutoff `min (1/2) (Re v / 2)` pointwise gives one
continuation on the whole quadrant `Re v > 0`, `Im v > 0` (`masslessUpperRight`), and the two symmetries
carry it to the other three quadrants (`masslessBoundaryWave`).

**Cramér's theorem for the massless wave** (`masslessZeroWave_cramer`).  There is `F` with

* `F = Φ₀` on the time strip `|Im v| < 1`;
* `F` holomorphic at every `v` with `|Im v| < 3/2`, `Re v ≠ 0`, that is not a prime point
  `±log n ± i` (`Λ(n) ≠ 0`);
* a simple pole at each prime point: `(v − (s₁ log n + s₂ i)) F(v) → s₂ (2i/π) Λ(n)/√n` for all four
  sign choices `s₁, s₂ = ±1`.
-/

open Complex MeasureTheory Set Filter Topology Metric Zeta23
open scoped Real ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.CHMDLightCone

open RHTower.CHMDGrowthCollapse

/-! ## Symmetries of the massless wave -/

theorem masslessZeroWave_neg (z : ℂ) : masslessZeroWave (-z) = masslessZeroWave z := by
  unfold masslessZeroWave
  exact tsum_congr fun ρ => by rw [neg_mul, Complex.cos_neg]

theorem masslessZeroWave_conj (z : ℂ) : masslessZeroWave (conj z) = conj (masslessZeroWave z) := by
  unfold masslessZeroWave
  rw [Complex.conj_tsum, ← reflectEquiv.tsum_eq]
  refine tsum_congr fun ρ => ?_
  simp only [reflectEquiv, Equiv.coe_fn_mk, mult_reflectZero, kgWeight_reflectZero, map_mul,
    map_natCast, ← Complex.cos_conj]
  unfold reflectZero
  simp only
  rw [gammaOf_reflect]

/-! ## Avoiding the prime points -/

theorem exists_ball_avoiding_primePoints {v₁ : ℂ}
    (hpole : ∀ n : ℕ, chmdPrimeWeight n ≠ 0 → v₁ ≠ (Real.log n : ℂ) + I) :
    ∃ ε > 0, ∀ v ∈ ball v₁ ε, ∀ n : ℕ, chmdPrimeWeight n ≠ 0 → v ≠ (Real.log n : ℂ) + I := by
  set N := ⌈Real.exp (|v₁.re| + 1)⌉₊
  have hlogN : ∀ n : ℕ, N < n → |v₁.re| + 1 < Real.log n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hn)
    rw [Real.lt_log_iff_exp_lt hn0]
    exact lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hn)
  set S : Set ℂ := (fun n : ℕ => (Real.log n : ℂ) + I) '' {n | n ≤ N ∧ chmdPrimeWeight n ≠ 0}
  have hSfin : S.Finite := ((Set.finite_Iic N).subset fun n hn => hn.1).image _
  have hv₁S : v₁ ∉ S := by
    rintro ⟨n, ⟨-, hw⟩, hn⟩
    exact hpole n hw hn.symm
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.mp hSfin.isClosed.isOpen_compl v₁ hv₁S
  refine ⟨min ε (1 / 2), lt_min hε (by norm_num), fun v hv n hw hvn => ?_⟩
  rcases Nat.lt_or_ge N n with hnN | hnN
  · have h1 := abs_re_sub_lt_of_mem_ball hv
    have h2 : v.re = Real.log n := by
      rw [hvn, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
    have := hlogN n hnN
    have hm : min ε (1 / 2) ≤ 1 / 2 := min_le_right _ _
    rw [h2] at h1
    linarith [(abs_lt.mp h1).2, le_abs_self v₁.re]
  · exact hεS (ball_subset_ball (min_le_left _ _) hv) ⟨n, ⟨hnN, hw⟩, hvn.symm⟩

theorem analyticAt_masslessContinuation {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) {v₁ : ℂ}
    (hre : a < v₁.re) (h1 : -1 / 2 < v₁.im) (h2 : v₁.im < 3 / 2)
    (hpole : ∀ n : ℕ, chmdPrimeWeight n ≠ 0 → v₁ ≠ (Real.log n : ℂ) + I) :
    AnalyticAt ℂ (masslessContinuation a) v₁ := by
  obtain ⟨ε, hε, hball⟩ := exists_ball_avoiding_primePoints hpole
  set U : Set ℂ := ball v₁ ε ∩ ({v | a < v.re} ∩ ({v | -1 / 2 < v.im} ∩ {v | v.im < 3 / 2}))
  have hUo : IsOpen U := isOpen_ball.inter ((isOpen_lt continuous_const continuous_re).inter
    ((isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)))
  refine DifferentiableOn.analyticAt (fun v hv => ?_) (hUo.mem_nhds ⟨mem_ball_self hε, hre, h1, h2⟩)
  obtain ⟨hvb, hvre, hv1, hv2⟩ := hv
  exact (differentiableAt_masslessContinuation ha ha' hvre hv1 hv2 (hball v hvb)).differentiableWithinAt

/-! ## The continuation on the upper right quadrant -/

/-- The cutoff `min (1/2) (Re v / 2)`. -/
def cutoffAt (v : ℂ) : ℝ := min (1 / 2) (v.re / 2)

/-- The continuation on `Re v > 0`, built with the cutoff `cutoffAt v`. -/
def masslessUpperRight (v : ℂ) : ℂ := masslessContinuation (cutoffAt v) v

/-- Near a point of the right half-plane the quadrant continuation is one fixed continuation. -/
theorem masslessUpperRight_eventuallyEq {v₁ : ℂ} (hre : 0 < v₁.re) (h1 : -1 / 2 < v₁.im)
    (h2 : v₁.im < 3 / 2) :
    masslessUpperRight =ᶠ[𝓝 v₁] masslessContinuation (min (1 / 2) (v₁.re / 4)) := by
  set a₁ := min (1 / 2) (v₁.re / 4)
  have ha₁ : 0 < a₁ := lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : (0 : ℝ) < v₁.re / 4)
  have ha₁' : a₁ ≤ 1 / 2 := min_le_left _ _
  have hU : {v : ℂ | v₁.re / 2 < v.re ∧ -1 / 2 < v.im ∧ v.im < 3 / 2} ∈ 𝓝 v₁ :=
    ((isOpen_lt continuous_const continuous_re).inter ((isOpen_lt continuous_const continuous_im).inter
      (isOpen_lt continuous_im continuous_const))).mem_nhds ⟨by simp only [Set.mem_setOf_eq]; linarith, h1, h2⟩
  filter_upwards [hU] with v ⟨hvre, hv1, hv2⟩
  have hvpos : 0 < v.re := by linarith
  have hc : 0 < cutoffAt v := lt_min (by norm_num) (by linarith)
  have hc' : cutoffAt v ≤ 1 / 2 := min_le_left _ _
  have hcv : cutoffAt v < v.re := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have ha₁v : a₁ < v.re := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  unfold masslessUpperRight masslessContinuation
  rw [archContinuation_congr hc hc' ha₁ ha₁' hcv ha₁v hv1 hv2]

/-! ## The global continuation -/

/-- The massless wave continued across both boundary lines `Im v = ±1` (away from `Re v = 0`). -/
def masslessBoundaryWave (v : ℂ) : ℂ :=
  if |v.im| < 1 then masslessZeroWave v
  else if 0 < v.re then
    (if 0 < v.im then masslessUpperRight v else conj (masslessUpperRight (conj v)))
  else (if 0 < v.im then conj (masslessUpperRight (-conj v)) else masslessUpperRight (-v))

theorem masslessBoundaryWave_of_strip {v : ℂ} (hv : |v.im| < 1) :
    masslessBoundaryWave v = masslessZeroWave v := by
  simp only [masslessBoundaryWave, if_pos hv]

theorem isOpen_strip : IsOpen {v : ℂ | |v.im| < 1} :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_const

/-- Upper right quadrant: the global wave is locally a continuation `masslessContinuation a₁`. -/
theorem masslessBoundaryWave_eventuallyEq_UR {v₁ : ℂ} (hre : 0 < v₁.re) (h1 : 0 < v₁.im)
    (h2 : v₁.im < 3 / 2) :
    masslessBoundaryWave =ᶠ[𝓝 v₁] masslessContinuation (min (1 / 2) (v₁.re / 4)) := by
  set a₁ := min (1 / 2) (v₁.re / 4)
  have ha₁ : 0 < a₁ := lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : (0 : ℝ) < v₁.re / 4)
  have ha₁' : a₁ ≤ 1 / 2 := min_le_left _ _
  have hU : {v : ℂ | v₁.re / 2 < v.re ∧ 0 < v.im ∧ v.im < 3 / 2} ∈ 𝓝 v₁ :=
    ((isOpen_lt continuous_const continuous_re).inter ((isOpen_lt continuous_const continuous_im).inter
      (isOpen_lt continuous_im continuous_const))).mem_nhds ⟨by simp only [Set.mem_setOf_eq]; linarith, h1, h2⟩
  filter_upwards [hU, masslessUpperRight_eventuallyEq hre (by linarith) h2] with v ⟨hvre, hv1, hv2⟩ hUR
  have hvpos : 0 < v.re := by linarith
  by_cases hs : |v.im| < 1
  · rw [masslessBoundaryWave, if_pos hs]
    exact masslessZeroWave_eq_masslessContinuation ha₁ ha₁'
      (lt_of_le_of_lt (min_le_right _ _) (by linarith)) (by linarith) (abs_lt.mp hs).2
  · rw [masslessBoundaryWave, if_neg hs, if_pos hvpos, if_pos hv1]
    exact hUR

theorem conj_conj_comp_eq (f : ℂ → ℂ) (v : ℂ) :
    (⇑(starRingEnd ℂ) ∘ f ∘ ⇑(starRingEnd ℂ)) (conj v) = conj (f v) := by
  simp

/-- Lower right quadrant. -/
theorem masslessBoundaryWave_eventuallyEq_LR {v₁ : ℂ} (hre : 0 < v₁.re) (h1 : -3 / 2 < v₁.im)
    (h2 : v₁.im < 0) :
    masslessBoundaryWave =ᶠ[𝓝 v₁]
      fun v => conj (masslessContinuation (min (1 / 2) (v₁.re / 4)) (conj v)) := by
  set a₁ := min (1 / 2) (v₁.re / 4)
  have ha₁ : 0 < a₁ := lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : (0 : ℝ) < v₁.re / 4)
  have ha₁' : a₁ ≤ 1 / 2 := min_le_left _ _
  have hU : {v : ℂ | v₁.re / 2 < v.re ∧ -3 / 2 < v.im ∧ v.im < 0} ∈ 𝓝 v₁ :=
    ((isOpen_lt continuous_const continuous_re).inter ((isOpen_lt continuous_const continuous_im).inter
      (isOpen_lt continuous_im continuous_const))).mem_nhds ⟨by simp only [Set.mem_setOf_eq]; linarith, h1, h2⟩
  have hc : Tendsto (fun v : ℂ => conj v) (𝓝 v₁) (𝓝 (conj v₁)) :=
    Complex.continuous_conj.tendsto v₁
  have hUR := hc.eventually (masslessUpperRight_eventuallyEq (v₁ := conj v₁)
    (by rw [Complex.conj_re]; exact hre) (by rw [Complex.conj_im]; linarith)
    (by rw [Complex.conj_im]; linarith))
  have hre' : (conj v₁).re / 4 = v₁.re / 4 := by simp
  rw [hre'] at hUR
  filter_upwards [hU, hUR] with v ⟨hvre, hv1, hv2⟩ hvUR
  have hvpos : 0 < v.re := by linarith
  by_cases hs : |v.im| < 1
  · rw [masslessBoundaryWave, if_pos hs, ← masslessZeroWave_eq_masslessContinuation ha₁ ha₁'
      (by simp; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)) (by simp; linarith)
      (by simp; linarith [(abs_lt.mp hs).1]), masslessZeroWave_conj, Complex.conj_conj]
  · rw [masslessBoundaryWave, if_neg hs, if_pos hvpos, if_neg (not_lt.mpr hv2.le), hvUR]

/-- Upper left quadrant. -/
theorem masslessBoundaryWave_eventuallyEq_UL {v₁ : ℂ} (hre : v₁.re < 0) (h1 : 0 < v₁.im)
    (h2 : v₁.im < 3 / 2) :
    masslessBoundaryWave =ᶠ[𝓝 v₁]
      fun v => conj (masslessContinuation (min (1 / 2) (-v₁.re / 4)) (-conj v)) := by
  set a₁ := min (1 / 2) (-v₁.re / 4)
  have ha₁ : 0 < a₁ := lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : (0 : ℝ) < -v₁.re / 4)
  have ha₁' : a₁ ≤ 1 / 2 := min_le_left _ _
  have hU : {v : ℂ | v.re < v₁.re / 2 ∧ 0 < v.im ∧ v.im < 3 / 2} ∈ 𝓝 v₁ :=
    ((isOpen_lt continuous_re continuous_const).inter ((isOpen_lt continuous_const continuous_im).inter
      (isOpen_lt continuous_im continuous_const))).mem_nhds ⟨by simp only [Set.mem_setOf_eq]; linarith, h1, h2⟩
  have hc : Tendsto (fun v : ℂ => -conj v) (𝓝 v₁) (𝓝 (-conj v₁)) :=
    (Complex.continuous_conj.neg).tendsto v₁
  have hUR := hc.eventually (masslessUpperRight_eventuallyEq (v₁ := -conj v₁)
    (by rw [Complex.neg_re, Complex.conj_re]; linarith)
    (by rw [Complex.neg_im, Complex.conj_im, neg_neg]; linarith)
    (by rw [Complex.neg_im, Complex.conj_im, neg_neg]; linarith))
  have hre' : (-conj v₁).re / 4 = -v₁.re / 4 := by simp
  rw [hre'] at hUR
  filter_upwards [hU, hUR] with v ⟨hvre, hv1, hv2⟩ hvUR
  have hvneg : v.re < 0 := by linarith
  by_cases hs : |v.im| < 1
  · rw [masslessBoundaryWave, if_pos hs, ← masslessZeroWave_eq_masslessContinuation ha₁ ha₁'
      (by simp; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)) (by simp; linarith)
      (by simp; linarith [(abs_lt.mp hs).2]), masslessZeroWave_neg, masslessZeroWave_conj,
      Complex.conj_conj]
  · rw [masslessBoundaryWave, if_neg hs, if_neg (not_lt.mpr hvneg.le), if_pos hv1, hvUR]

/-- Lower left quadrant. -/
theorem masslessBoundaryWave_eventuallyEq_LL {v₁ : ℂ} (hre : v₁.re < 0) (h1 : -3 / 2 < v₁.im)
    (h2 : v₁.im < 0) :
    masslessBoundaryWave =ᶠ[𝓝 v₁]
      fun v => masslessContinuation (min (1 / 2) (-v₁.re / 4)) (-v) := by
  set a₁ := min (1 / 2) (-v₁.re / 4)
  have ha₁ : 0 < a₁ := lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : (0 : ℝ) < -v₁.re / 4)
  have ha₁' : a₁ ≤ 1 / 2 := min_le_left _ _
  have hU : {v : ℂ | v.re < v₁.re / 2 ∧ -3 / 2 < v.im ∧ v.im < 0} ∈ 𝓝 v₁ :=
    ((isOpen_lt continuous_re continuous_const).inter ((isOpen_lt continuous_const continuous_im).inter
      (isOpen_lt continuous_im continuous_const))).mem_nhds ⟨by simp only [Set.mem_setOf_eq]; linarith, h1, h2⟩
  have hc : Tendsto (fun v : ℂ => -v) (𝓝 v₁) (𝓝 (-v₁)) := continuous_neg.tendsto v₁
  have hUR := hc.eventually (masslessUpperRight_eventuallyEq (v₁ := -v₁)
    (by rw [Complex.neg_re]; linarith) (by rw [Complex.neg_im]; linarith)
    (by rw [Complex.neg_im]; linarith))
  have hre' : (-v₁).re / 4 = -v₁.re / 4 := by simp
  rw [hre'] at hUR
  filter_upwards [hU, hUR] with v ⟨hvre, hv1, hv2⟩ hvUR
  have hvneg : v.re < 0 := by linarith
  by_cases hs : |v.im| < 1
  · rw [masslessBoundaryWave, if_pos hs, ← masslessZeroWave_eq_masslessContinuation ha₁ ha₁'
      (by simp; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)) (by simp; linarith)
      (by simp; linarith [(abs_lt.mp hs).1]), masslessZeroWave_neg]
  · rw [masslessBoundaryWave, if_neg hs, if_neg (not_lt.mpr hvneg.le), if_neg (not_lt.mpr hv2.le),
      hvUR]

/-! ## Analyticity off the prime points -/

/-- `v` is none of the prime points `±log n ± i` with `Λ(n) ≠ 0`. -/
def AvoidsPrimePoints (v : ℂ) : Prop :=
  ∀ n : ℕ, chmdPrimeWeight n ≠ 0 → |v.re| ≠ Real.log n ∨ |v.im| ≠ 1

theorem analyticAt_conj_comp_conj {f : ℂ → ℂ} {v : ℂ} (hf : AnalyticAt ℂ f (conj v)) :
    AnalyticAt ℂ (fun u => conj (f (conj u))) v := by
  have hev : ∀ᶠ u in 𝓝 v, AnalyticAt ℂ f (conj u) :=
    (Complex.continuous_conj.tendsto v).eventually hf.eventually_analyticAt
  refine DifferentiableOn.analyticAt (s := {u | AnalyticAt ℂ f (conj u)}) (fun u hu => ?_) hev
  have h := (hu.differentiableAt).conj_conj
  rw [Complex.conj_conj] at h
  exact h.differentiableWithinAt

theorem analyticAt_comp_neg {f : ℂ → ℂ} {v : ℂ} (hf : AnalyticAt ℂ f (-v)) :
    AnalyticAt ℂ (fun u => f (-u)) v :=
  hf.comp (f := fun u : ℂ => -u) (analyticAt_id.neg)

theorem log_nonneg_of_weight {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) : 0 ≤ Real.log n :=
  (half_lt_log_of_two_le (two_le_of_chmdPrimeWeight_ne_zero hw)).le.trans' (by norm_num)

/-- **Analyticity of the continued massless wave** on the strip and off the imaginary axis away
from the prime points. -/
theorem analyticAt_masslessBoundaryWave {v : ℂ}
    (hv : |v.im| < 1 ∨ (|v.im| < 3 / 2 ∧ v.re ≠ 0 ∧ AvoidsPrimePoints v)) :
    AnalyticAt ℂ masslessBoundaryWave v := by
  rcases hv with hs | ⟨hs, hre, hav⟩
  · refine AnalyticAt.congr (f := masslessZeroWave) ?_ ?_
    · exact differentiableOn_masslessZeroWave.analyticAt (isOpen_causalTimeStrip.mem_nhds hs)
    · filter_upwards [isOpen_strip.mem_nhds hs] with u hu
      exact (masslessBoundaryWave_of_strip hu).symm
  have him := abs_lt.mp hs
  by_cases hs1 : |v.im| < 1
  · refine AnalyticAt.congr (f := masslessZeroWave) ?_ ?_
    · exact differentiableOn_masslessZeroWave.analyticAt (isOpen_causalTimeStrip.mem_nhds hs1)
    · filter_upwards [isOpen_strip.mem_nhds hs1] with u hu
      exact (masslessBoundaryWave_of_strip hu).symm
  have hs1' := not_lt.mp hs1
  -- the pole condition for the representative point in the upper right quadrant
  have hpoleUR : ∀ w : ℂ, |w.re| = |v.re| → |w.im| = |v.im| →
      ∀ n : ℕ, chmdPrimeWeight n ≠ 0 → w ≠ (Real.log n : ℂ) + I := by
    intro w hwre hwim n hw h
    have h1 : w.re = Real.log n := by
      rw [h, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
    have h2 : w.im = 1 := by rw [h, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
    rcases hav n hw with h' | h'
    · exact h' (by rw [← hwre, h1, abs_of_nonneg (log_nonneg_of_weight hw)])
    · exact h' (by rw [← hwim, h2, abs_one])
  rcases lt_or_gt_of_ne hre with hneg | hpos
  · set a₁ := min (1 / 2) (-v.re / 4)
    have ha₁ : 0 < a₁ := lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : (0 : ℝ) < -v.re / 4)
    have ha₁' : a₁ ≤ 1 / 2 := min_le_left _ _
    have hlt : a₁ < -v.re := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    rcases le_or_gt v.im 0 with him0 | him0
    · -- lower left
      have hv1 : v.im ≤ -1 := by
        rcases le_abs'.mp hs1' with h | h <;> linarith
      refine AnalyticAt.congr (f := fun u => masslessContinuation a₁ (-u)) ?_
        (masslessBoundaryWave_eventuallyEq_LL hneg (by linarith) (by linarith)).symm
      refine analyticAt_comp_neg (analyticAt_masslessContinuation ha₁ ha₁' (by simpa using hlt)
        (by simp; linarith) (by simp; linarith) (hpoleUR _ (by simp) (by simp)))
    · -- upper left
      have hv1 : 1 ≤ v.im := by
        rcases le_abs'.mp hs1' with h | h <;> linarith
      refine AnalyticAt.congr (f := fun u => conj (masslessContinuation a₁ (-conj u))) ?_
        (masslessBoundaryWave_eventuallyEq_UL hneg (by linarith) (by linarith)).symm
      have h := analyticAt_masslessContinuation ha₁ ha₁' (v₁ := -conj v)
        (by rw [Complex.neg_re, Complex.conj_re]; exact hlt)
        (by rw [Complex.neg_im, Complex.conj_im, neg_neg]; linarith)
        (by rw [Complex.neg_im, Complex.conj_im, neg_neg]; linarith)
        (hpoleUR _ (by rw [Complex.neg_re, Complex.conj_re, abs_neg])
          (by rw [Complex.neg_im, Complex.conj_im, neg_neg]))
      exact analyticAt_conj_comp_conj (f := fun u => masslessContinuation a₁ (-u))
        (analyticAt_comp_neg h)
  · set a₁ := min (1 / 2) (v.re / 4)
    have ha₁ : 0 < a₁ := lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : (0 : ℝ) < v.re / 4)
    have ha₁' : a₁ ≤ 1 / 2 := min_le_left _ _
    have hlt : a₁ < v.re := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    rcases le_or_gt v.im 0 with him0 | him0
    · -- lower right
      have hv1 : v.im ≤ -1 := by
        rcases le_abs'.mp hs1' with h | h <;> linarith
      refine AnalyticAt.congr (f := fun u => conj (masslessContinuation a₁ (conj u))) ?_
        (masslessBoundaryWave_eventuallyEq_LR hpos (by linarith) (by linarith)).symm
      exact analyticAt_conj_comp_conj (analyticAt_masslessContinuation ha₁ ha₁'
        (by simpa using hlt) (by simp; linarith) (by simp; linarith)
        (hpoleUR _ (by simp) (by simp)))
    · -- upper right
      have hv1 : 1 ≤ v.im := by
        rcases le_abs'.mp hs1' with h | h <;> linarith
      exact AnalyticAt.congr (analyticAt_masslessContinuation ha₁ ha₁' hlt (by linarith)
        (by linarith) (hpoleUR _ rfl rfl))
        (masslessBoundaryWave_eventuallyEq_UR hpos (by linarith) (by linarith)).symm

/-! ## The residues at the four families of prime points -/

theorem tendsto_punctured_of_injective {φ : ℂ → ℂ} {p q : ℂ} (hφ : Continuous φ) (hp : φ p = q)
    (hinj : Function.Injective φ) : Tendsto φ (𝓝[≠] p) (𝓝[≠] q) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · rw [← hp]; exact (hφ.tendsto p).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with v hv
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hv ⊢
    intro h
    exact hv (hinj (h.trans hp.symm))

/-- **The four residue laws**: at `s₁ log n + s₂ i` the residue is `s₂ (2i/π) Λ(n)/√n`. -/
theorem tendsto_masslessBoundaryWave_residue {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) :
    Tendsto (fun v => (v - ((Real.log n : ℂ) + I)) * masslessBoundaryWave v)
        (𝓝[≠] ((Real.log n : ℂ) + I)) (𝓝 (2 * I / π * chmdPrimeWeight n)) ∧
    Tendsto (fun v => (v - ((Real.log n : ℂ) - I)) * masslessBoundaryWave v)
        (𝓝[≠] ((Real.log n : ℂ) - I)) (𝓝 (-(2 * I / π * chmdPrimeWeight n))) ∧
    Tendsto (fun v => (v - (-(Real.log n : ℂ) + I)) * masslessBoundaryWave v)
        (𝓝[≠] (-(Real.log n : ℂ) + I)) (𝓝 (2 * I / π * chmdPrimeWeight n)) ∧
    Tendsto (fun v => (v - (-(Real.log n : ℂ) - I)) * masslessBoundaryWave v)
        (𝓝[≠] (-(Real.log n : ℂ) - I)) (𝓝 (-(2 * I / π * chmdPrimeWeight n))) := by
  set p₀ : ℂ := (Real.log n : ℂ) + I with hp₀
  set R : ℂ := 2 * I / π * chmdPrimeWeight n with hR
  have hlog := half_lt_log_of_two_le (two_le_of_chmdPrimeWeight_ne_zero hw)
  set a₁ := min (1 / 2) (Real.log n / 4)
  have ha₁ : 0 < a₁ := lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : (0 : ℝ) < Real.log n / 4)
  have ha₁' : a₁ ≤ 1 / 2 := min_le_left _ _
  have hres := tendsto_masslessContinuation_residue ha₁ ha₁' hw
  have hconjR : conj R = -R := by
    rw [hR, map_mul, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal,
      map_ofNat]
    ring
  have hre0 : (0 : ℝ) < Real.log n := by linarith
  have hp₀re : p₀.re = Real.log n := by
    rw [hp₀, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
  have hp₀im : p₀.im = 1 := by
    rw [hp₀, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
  -- (a) log n + i
  have ha : Tendsto (fun v => (v - p₀) * masslessBoundaryWave v) (𝓝[≠] p₀) (𝓝 R) := by
    have hev := masslessBoundaryWave_eventuallyEq_UR (v₁ := p₀) (by rw [hp₀re]; exact hre0)
      (by rw [hp₀im]; norm_num) (by rw [hp₀im]; norm_num)
    rw [hp₀re] at hev
    refine hres.congr' ?_
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with v hv
    rw [hv]
  -- (b) log n − i
  have hb : Tendsto (fun v => (v - conj p₀) * masslessBoundaryWave v) (𝓝[≠] (conj p₀))
      (𝓝 (conj R)) := by
    have hev := masslessBoundaryWave_eventuallyEq_LR (v₁ := conj p₀)
      (by rw [Complex.conj_re, hp₀re]; exact hre0) (by rw [Complex.conj_im, hp₀im]; norm_num)
      (by rw [Complex.conj_im, hp₀im]; norm_num)
    rw [Complex.conj_re, hp₀re] at hev
    have hφ := tendsto_punctured_of_injective (φ := fun v => conj v) Complex.continuous_conj
      (Complex.conj_conj p₀) (star_injective)
    refine ((Complex.continuous_conj.tendsto R).comp (hres.comp hφ)).congr' ?_
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with v hv
    rw [hv]
    simp only [Function.comp, map_mul, map_sub, Complex.conj_conj]
    rfl
  -- (c) −log n + i
  have hc : Tendsto (fun v => (v - (-conj p₀)) * masslessBoundaryWave v) (𝓝[≠] (-conj p₀))
      (𝓝 (conj (-R))) := by
    have hev := masslessBoundaryWave_eventuallyEq_UL (v₁ := -conj p₀)
      (by rw [Complex.neg_re, Complex.conj_re, hp₀re]; linarith)
      (by rw [Complex.neg_im, Complex.conj_im, neg_neg, hp₀im]; norm_num)
      (by rw [Complex.neg_im, Complex.conj_im, neg_neg, hp₀im]; norm_num)
    rw [Complex.neg_re, Complex.conj_re, hp₀re, neg_neg] at hev
    have hφ := tendsto_punctured_of_injective (φ := fun v => -conj v)
      Complex.continuous_conj.neg (by show -conj (-conj p₀) = p₀; rw [map_neg, Complex.conj_conj, neg_neg])
      (neg_injective.comp star_injective : Function.Injective fun v : ℂ => -conj v)
    refine ((Complex.continuous_conj.tendsto _).comp ((hres.comp hφ).neg)).congr' ?_
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with v hv
    rw [hv]
    simp only [Function.comp, map_mul, map_sub, map_neg, Complex.conj_conj]
    ring
  -- (d) −log n − i
  have hd : Tendsto (fun v => (v - (-p₀)) * masslessBoundaryWave v) (𝓝[≠] (-p₀)) (𝓝 (-R)) := by
    have hev := masslessBoundaryWave_eventuallyEq_LL (v₁ := -p₀)
      (by rw [Complex.neg_re, hp₀re]; linarith) (by rw [Complex.neg_im, hp₀im]; norm_num)
      (by rw [Complex.neg_im, hp₀im]; norm_num)
    rw [Complex.neg_re, hp₀re, neg_neg] at hev
    have hφ := tendsto_punctured_of_injective (φ := fun v => -v) continuous_neg
      (by show -(-p₀) = p₀; exact neg_neg p₀) neg_injective
    refine (hres.comp hφ).neg.congr' ?_
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with v hv
    rw [hv]
    simp only [Function.comp]
    ring
  have hconjp : conj p₀ = (Real.log n : ℂ) - I := by
    rw [hp₀, map_add, Complex.conj_ofReal, Complex.conj_I]; ring
  refine ⟨ha, ?_, ?_, ?_⟩
  · rw [← hconjR, ← hconjp]; exact hb
  · rw [show -(Real.log n : ℂ) + I = -conj p₀ by rw [hconjp]; ring,
      show R = conj (-R) by rw [map_neg, hconjR, neg_neg]]
    exact hc
  · rw [show -(Real.log n : ℂ) - I = -p₀ by rw [hp₀]; ring]
    exact hd

/-! ## Cramér's theorem for the massless wave -/

/-- **Cramér's theorem for the massless zero-side wave.**  The wave
`Φ₀(v) = Σ_ρ m_ρ cos(vγ_ρ) sech²(γ_ρ/2)`, holomorphic on `|Im v| < 1`, continues to a function `F` that
is holomorphic at every point with `|Im v| < 3/2`, `Re v ≠ 0` other than the prime points `±log n ± i`
(`Λ(n) ≠ 0`), and has a simple pole with residue `s₂ (2i/π) Λ(n)/√n` at `s₁ log n + s₂ i`. -/
theorem masslessZeroWave_cramer :
    ∃ F : ℂ → ℂ,
      (∀ v : ℂ, |v.im| < 1 → masslessZeroWave v = F v) ∧
      (∀ v : ℂ, |v.im| < 1 ∨ (|v.im| < 3 / 2 ∧ v.re ≠ 0 ∧ AvoidsPrimePoints v) →
        AnalyticAt ℂ F v) ∧
      (∀ n : ℕ, chmdPrimeWeight n ≠ 0 →
        Tendsto (fun v => (v - ((Real.log n : ℂ) + I)) * F v)
          (𝓝[≠] ((Real.log n : ℂ) + I)) (𝓝 (2 * I / π * chmdPrimeWeight n)) ∧
        Tendsto (fun v => (v - ((Real.log n : ℂ) - I)) * F v)
          (𝓝[≠] ((Real.log n : ℂ) - I)) (𝓝 (-(2 * I / π * chmdPrimeWeight n))) ∧
        Tendsto (fun v => (v - (-(Real.log n : ℂ) + I)) * F v)
          (𝓝[≠] (-(Real.log n : ℂ) + I)) (𝓝 (2 * I / π * chmdPrimeWeight n)) ∧
        Tendsto (fun v => (v - (-(Real.log n : ℂ) - I)) * F v)
          (𝓝[≠] (-(Real.log n : ℂ) - I)) (𝓝 (-(2 * I / π * chmdPrimeWeight n)))) :=
  ⟨masslessBoundaryWave, fun _ hv => (masslessBoundaryWave_of_strip hv).symm,
    fun _ hv => analyticAt_masslessBoundaryWave hv,
    fun _ hw => tendsto_masslessBoundaryWave_residue hw⟩

end RHTower.CHMDLightCone
