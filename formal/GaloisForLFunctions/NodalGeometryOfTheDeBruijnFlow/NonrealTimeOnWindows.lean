import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheDepthMomentsAreDissipated
import GaloisForLFunctions.HTGeometry.DaiYoshikawa.IntegralGronwallAffine
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Nonreal time on unit windows

Let `w₀` be a smooth bump, `1` on `[−½, ½]` and `0` off `(−1, 1)`, and for an integer height `j` let `N_j(s)` be the
nonreal count of `H_s` localized by `w₀(· − j)`, `E₁_j(s)`, `E₂_j(s)` the localized second and fourth moments of the
depths. The two energy laws give, on any block of windows at heights `≤ Y` and for `τ₁ = 1/log Y`, a budget for the
time spent nonreal above `τ₀` (`exists_sum_nonrealTime_le`):

`Σ_j ∫_{τ₀}^{τ₁} N_j ≤ C (1/τ₀ + log Y) (Σ_j E₂_j(0) + 2^{−K} · size)`,

with windows enlarged by `O(K)`. The mechanism is the following.

* For `s ≤ τ₀`, the `E₁` law gives `2 ∫_{τ₀}^{τ₁} N ≤ E₁(s) + K log Y ∫ E₁^{out}`; averaging over `s ∈ [0, τ₀]` turns the
  nonreal time into `(1/τ₀) ∫ E₁`.
* The `E₂` law pays `∫ E₁` by `E₂`.
* Outer cutoffs are dominated by nine neighbouring windows, so a block of windows closes under the flow up to an
  enlargement; a weighted sum over nested blocks and Gronwall bound `E₂` for all times by its value at time zero
  (`sum_quartic_le`).
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn
open scoped ContDiff

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## The window bump -/

/-- The bump behind the unit windows. -/
def windowBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The window profile `w₀`: `1` on `[−½, ½]`, `0` off `(−1, 1)`. -/
def w₀ : ℝ → ℝ := fun x => windowBump x

theorem contDiff_w₀ : ContDiff ℝ ∞ w₀ := windowBump.contDiff

theorem w₀_nonneg (x : ℝ) : 0 ≤ w₀ x := windowBump.nonneg

theorem w₀_le_one (x : ℝ) : w₀ x ≤ 1 := windowBump.le_one

theorem w₀_eq_one {x : ℝ} (hx : |x| ≤ 1 / 2) : w₀ x = 1 :=
  windowBump.one_of_mem_closedBall (by
    rw [mem_closedBall, Real.dist_eq, sub_zero]
    exact hx)

theorem w₀_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : w₀ x = 0 :=
  windowBump.zero_of_le_dist (by
    rw [Real.dist_eq, sub_zero]
    exact hx)

theorem hasCompactSupport_w₀ : HasCompactSupport w₀ := windowBump.hasCompactSupport

theorem continuous_w₀ : Continuous w₀ := contDiff_w₀.continuous

/-- The derivative of the window profile. -/
def v₀ : ℝ → ℝ := deriv w₀

theorem hasDerivAt_w₀ (x : ℝ) : HasDerivAt w₀ (v₀ x) x :=
  (contDiff_w₀.differentiable (by simp) x).hasDerivAt

theorem exists_abs_v₀_le : ∃ V, 0 ≤ V ∧ ∀ x, |v₀ x| ≤ V := by
  have hc : Continuous v₀ := contDiff_w₀.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hasCompactSupport_w₀.deriv
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

theorem exists_lipschitz_v₀ : ∃ M, 0 ≤ M ∧ ∀ x x', |v₀ x - v₀ x'| ≤ M * |x - x'| := by
  have h2 : ContDiff ℝ ∞ v₀ := (contDiff_infty_iff_deriv.mp contDiff_w₀).2
  have hc : Continuous (deriv v₀) := h2.continuous_deriv (by simp)
  have hcs : HasCompactSupport (deriv v₀) := hasCompactSupport_w₀.deriv.deriv
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  refine ⟨max C 0, le_max_right _ _, fun x x' => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := v₀) (s := univ) (x := x') (y := x)
    (C := max C 0) (fun u _ => (h2.differentiable (by simp) u))
    (fun u _ => (hC u).trans (le_max_left C 0)) convex_univ (mem_univ _) (mem_univ _)
  simpa only [Real.norm_eq_abs] using h

/-! ## Window observables -/

/-- The observable `Σ_z m(z) w₀(Re z − j) u(Im z)` of the zeros of `H_s` on the window at height `j`. -/
def windowObs (u : ℝ → ℝ) (j : ℤ) (s : ℝ) : ℝ := heatLocalizedZeroObservable (j : ℝ) w₀ u s

/-- The sum of a window observable over a block `A ≤ j ≤ B`. -/
def blockObs (u : ℝ → ℝ) (A B : ℤ) (s : ℝ) : ℝ := ∑ j ∈ Finset.Icc A B, windowObs u j s

/-- The fourth power of the depth. -/
def uQuartic : ℝ → ℝ := fun y => y ^ 4

/-- The square of the depth. -/
def uSquare : ℝ → ℝ := fun y => y ^ 2

/-- The nonreal indicator. -/
def uNonreal : ℝ → ℝ := fun y => if y = 0 then 0 else 1

theorem windowObs_nonneg {u : ℝ → ℝ} (hu : ∀ y, 0 ≤ u y) (j : ℤ) (s : ℝ) : 0 ≤ windowObs u j s :=
  heatLocalizedZeroObservable_nonneg w₀_nonneg hu

theorem blockObs_nonneg {u : ℝ → ℝ} (hu : ∀ y, 0 ≤ u y) (A B : ℤ) (s : ℝ) : 0 ≤ blockObs u A B s :=
  Finset.sum_nonneg fun j _ => windowObs_nonneg hu j s

theorem blockObs_mono {u : ℝ → ℝ} (hu : ∀ y, 0 ≤ u y) {A B A' B' : ℤ} (hA : A' ≤ A) (hB : B ≤ B')
    (s : ℝ) : blockObs u A B s ≤ blockObs u A' B' s :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc hA hB)
    fun j _ _ => windowObs_nonneg hu j s

theorem continuous_windowObs_clamped {u : ℝ → ℝ} (hu : Continuous u) (j : ℤ) :
    Continuous fun s => windowObs u j (max s 0) :=
  continuous_heatLocalizedZeroObservable_clamped continuous_w₀ hu hasCompactSupport_w₀ j

theorem continuous_blockObs_clamped {u : ℝ → ℝ} (hu : Continuous u) (A B : ℤ) :
    Continuous fun s => blockObs u A B (max s 0) := by
  simp only [blockObs]
  exact continuous_finsetSum _ fun j _ => continuous_windowObs_clamped hu j

theorem intervalIntegrable_of_clamped {f : ℝ → ℝ} (hf : Continuous fun s => f (max s 0)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable f volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  exact hf.continuousOn.congr fun s hs => by simp only [max_eq_left (ha.trans hs.1)]

theorem intervalIntegrable_windowObs {u : ℝ → ℝ} (hu : Continuous u) (j : ℤ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : IntervalIntegrable (windowObs u j) volume a b :=
  intervalIntegrable_of_clamped (continuous_windowObs_clamped hu j) ha hab

theorem intervalIntegrable_blockObs {u : ℝ → ℝ} (hu : Continuous u) (A B : ℤ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : IntervalIntegrable (blockObs u A B) volume a b :=
  intervalIntegrable_of_clamped (continuous_blockObs_clamped hu A B) ha hab

/-! ## Domination of the outer cutoff by nine windows -/

theorem heatOuterCutoff_le_sum (x : ℝ) :
    heatOuterCutoff x ≤ ∑ i ∈ Finset.Icc (-4 : ℤ) 4, w₀ (x - i) := by
  classical
  have hnn : 0 ≤ ∑ i ∈ Finset.Icc (-4 : ℤ) 4, w₀ (x - i) := Finset.sum_nonneg fun i _ => w₀_nonneg _
  rcases lt_or_ge 3 |x| with hx | hx
  · have h0 : heatOuterCutoff x = 0 := PhaseKernel.tentCutoff_eq_zero (by
      norm_num
      exact hx)
    rw [h0]
    exact hnn
  · set i := round x with hi
    have hr : |x - i| ≤ 1 / 2 := abs_sub_round x
    have him : i ∈ Finset.Icc (-4 : ℤ) 4 := by
      rw [Finset.mem_Icc]
      obtain ⟨h1, h2⟩ := abs_le.mp hx
      obtain ⟨h3, h4⟩ := abs_le.mp hr
      constructor
      · have : (-4 : ℝ) ≤ i := by linarith only [h1, h4]
        exact_mod_cast this
      · have : (i : ℝ) ≤ 4 := by linarith only [h2, h3]
        exact_mod_cast this
    have hle := Finset.single_le_sum (f := fun i : ℤ => w₀ (x - i)) (fun i _ => w₀_nonneg _) him
    simp only [w₀_eq_one hr] at hle
    exact (PhaseKernel.tentCutoff_le_one 2 x).trans hle

/-- The outer observable is dominated by nine window observables. -/
theorem outerObs_le_sum {u : ℝ → ℝ} (hu : ∀ y, 0 ≤ u y) (j : ℤ) {s : ℝ} (hs : 0 ≤ s) :
    heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff u s ≤
      ∑ i ∈ Finset.Icc (-4 : ℤ) 4, windowObs u (j + i) s := by
  have hsum (i : ℤ) := summable_heatLocalizedZeroObservable hasCompactSupport_w₀ u ((j + i : ℤ) : ℝ) hs
  have houter := summable_heatLocalizedZeroObservable hasCompactSupport_heatOuterCutoff u (j : ℝ) hs
  unfold windowObs heatLocalizedZeroObservable heatWeightedZeroSum
  rw [← Summable.tsum_finsetSum fun i _ => hsum i]
  refine Summable.tsum_le_tsum (fun z => ?_) houter (summable_sum fun i _ => hsum i)
  have h := heatOuterCutoff_le_sum (z.re - j)
  have hm : (0 : ℝ) ≤ zeroMult (riemannHeat s) z := Nat.cast_nonneg _
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (hu _)) hm
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  congr 1
  push_cast
  ring

/-- A sum over a block of a sum over nine shifts is at most nine sums over the enlarged block. -/
theorem sum_sum_shift_le {f : ℤ → ℝ} (hf : ∀ j, 0 ≤ f j) (A B : ℤ) :
    ∑ j ∈ Finset.Icc A B, ∑ i ∈ Finset.Icc (-4 : ℤ) 4, f (j + i) ≤
      9 * ∑ j ∈ Finset.Icc (A - 4) (B + 4), f j := by
  classical
  rw [Finset.sum_comm]
  have hone (i : ℤ) (hi : i ∈ Finset.Icc (-4 : ℤ) 4) :
      ∑ j ∈ Finset.Icc A B, f (j + i) ≤ ∑ j ∈ Finset.Icc (A - 4) (B + 4), f j := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    have himg : (Finset.Icc A B).image (· + i) ⊆ Finset.Icc (A - 4) (B + 4) := by
      intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨h3, h4⟩ := Finset.mem_Icc.mp hj
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := f) himg fun j _ _ => hf j
    rwa [Finset.sum_image fun a _ b _ h => add_right_cancel h] at hs
  have hcard : (Finset.Icc (-4 : ℤ) 4).card = 9 := by decide
  calc _ ≤ ∑ _i ∈ Finset.Icc (-4 : ℤ) 4, ∑ j ∈ Finset.Icc (A - 4) (B + 4), f j :=
        Finset.sum_le_sum hone
    _ = _ := by
      rw [Finset.sum_const, hcard]
      norm_num

/-- Outer observables over a block are dominated by nine times the enlarged block. -/
theorem sum_outerObs_le {u : ℝ → ℝ} (hu : ∀ y, 0 ≤ u y) (A B : ℤ) {s : ℝ} (hs : 0 ≤ s) :
    ∑ j ∈ Finset.Icc A B, heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff u s ≤
      9 * blockObs u (A - 4) (B + 4) s :=
  (Finset.sum_le_sum fun j _ => outerObs_le_sum hu j hs).trans
    (sum_sum_shift_le (f := fun j => windowObs u j s) (fun j => windowObs_nonneg hu j s) A B)

/-! ## The window laws -/

/-- **The two energy laws on unit windows.** -/
theorem exists_window_laws :
    ∃ K > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ j : ℤ, X₀ ≤ j → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 / 8 →
      b * Real.log j ≤ 1 →
        IntervalIntegrable (windowObs uNonreal j) volume a b ∧
        windowObs uSquare j b - windowObs uSquare j a + 2 * (∫ s in a..b, windowObs uNonreal j s) ≤
          K * Real.log j * ∫ s in a..b, heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff uSquare s ∧
        windowObs uQuartic j b - windowObs uQuartic j a + 4 * (∫ s in a..b, windowObs uSquare j s) ≤
          K * Real.log j * ∫ s in a..b, heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff uQuartic s := by
  obtain ⟨V, hV, hvV⟩ := exists_abs_v₀_le
  obtain ⟨M, hM, hvM⟩ := exists_lipschitz_v₀
  obtain ⟨C₁, hC₁, X₁, hX₁, h₁⟩ := exists_uniform_heatLocalizedVerticalEnergy_evolution
  obtain ⟨C₂, hC₂, X₂, hX₂, h₂⟩ := exists_uniform_heatLocalizedQuarticEnergy_evolution
  set K₁ := (2 * M + 2 * V + 4 * 1) * C₁ with hK₁
  set K₂ := (16 * M + 2 * V + 8 * 1) * C₂ with hK₂
  have hK₁p : 0 < K₁ := by positivity
  have hK₂p : 0 < K₂ := by positivity
  refine ⟨max K₁ K₂, lt_max_of_lt_left hK₁p, max X₁ X₂, hX₁.trans (le_max_left _ _), ?_⟩
  intro j hj a b ha hab hb hbj
  have hj₁ : X₁ ≤ j := (le_max_left _ _).trans hj
  have hj₂ : X₂ ≤ j := (le_max_right _ _).trans hj
  have hL : 0 ≤ Real.log j := Real.log_nonneg (by linarith only [hj₁, hX₁])
  obtain ⟨hI, he₁⟩ := h₁ j hj₁ w₀ v₀ M V 1 hM hV zero_le_one hasDerivAt_w₀ w₀_nonneg w₀_le_one hvV hvM
    (fun x hx => w₀_eq_zero hx) a b ha hab hb hbj
  have he₂ := h₂ j hj₂ w₀ v₀ M V 1 hM hV zero_le_one hasDerivAt_w₀ w₀_nonneg w₀_le_one hvV hvM
    (fun x hx => w₀_eq_zero hx) a b ha hab hb hbj
  have hint₁ : 0 ≤ ∫ s in a..b, heatLocalizedVerticalEnergy (j : ℝ) heatOuterCutoff s :=
    intervalIntegral.integral_nonneg hab fun s _ =>
      heatLocalizedZeroObservable_nonneg (u := fun y => y ^ 2) heatOuterCutoff_nonneg
        (fun y => sq_nonneg y)
  have hint₂ : 0 ≤ ∫ s in a..b, heatLocalizedQuarticEnergy (j : ℝ) heatOuterCutoff s :=
    intervalIntegral.integral_nonneg hab fun s _ =>
      heatLocalizedZeroObservable_nonneg (u := fun y => y ^ 4) heatOuterCutoff_nonneg
        (fun y => by positivity)
  refine ⟨hI, he₁.trans ?_, he₂.trans ?_⟩
  · have hc : (2 * M + 2 * V + 4 * 1) * (C₁ * Real.log j) ≤ max K₁ K₂ * Real.log j := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hL
    exact mul_le_mul_of_nonneg_right hc hint₁
  · have hc : (16 * M + 2 * V + 8 * 1) * (C₂ * Real.log j) ≤ max K₁ K₂ * Real.log j := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hL
    exact mul_le_mul_of_nonneg_right hc hint₂

/-- The window laws as a statement. -/
def WindowLaws (K X₀ : ℝ) : Prop :=
  ∀ j : ℤ, X₀ ≤ j → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 / 8 → b * Real.log j ≤ 1 →
    IntervalIntegrable (windowObs uNonreal j) volume a b ∧
    windowObs uSquare j b - windowObs uSquare j a + 2 * (∫ s in a..b, windowObs uNonreal j s) ≤
      K * Real.log j * ∫ s in a..b, heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff uSquare s ∧
    windowObs uQuartic j b - windowObs uQuartic j a + 4 * (∫ s in a..b, windowObs uSquare j s) ≤
      K * Real.log j * ∫ s in a..b, heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff uQuartic s

theorem continuous_uSquare : Continuous uSquare := by unfold uSquare; fun_prop

theorem continuous_uQuartic : Continuous uQuartic := by unfold uQuartic; fun_prop

theorem uSquare_nonneg (y : ℝ) : 0 ≤ uSquare y := sq_nonneg y

theorem uQuartic_nonneg (y : ℝ) : 0 ≤ uQuartic y := by unfold uQuartic; positivity

theorem uNonreal_nonneg (y : ℝ) : 0 ≤ uNonreal y := by
  unfold uNonreal
  split_ifs <;> norm_num

theorem intervalIntegrable_outerObs {u : ℝ → ℝ} (hu : Continuous u) (j : ℤ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    IntervalIntegrable (heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff u) volume a b :=
  intervalIntegrable_of_clamped (continuous_heatLocalizedZeroObservable_clamped
    continuous_heatOuterCutoff hu hasCompactSupport_heatOuterCutoff j) ha hab

theorem integral_outerObs_nonneg {u : ℝ → ℝ} (hu : ∀ y, 0 ≤ u y) (j : ℤ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ ∫ s in a..b, heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff u s :=
  intervalIntegral.integral_nonneg hab fun _ _ =>
    heatLocalizedZeroObservable_nonneg heatOuterCutoff_nonneg hu

/-- Summing outer integrals over a block gives nine integrals over the enlarged block. -/
theorem sum_integral_outerObs_le {u : ℝ → ℝ} (hc : Continuous u) (hu : ∀ y, 0 ≤ u y) (A B : ℤ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Finset.Icc A B, ∫ s in a..b, heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff u s ≤
      9 * ∫ s in a..b, blockObs u (A - 4) (B + 4) s := by
  rw [← intervalIntegral.integral_finsetSum fun j _ => intervalIntegrable_outerObs hc j ha hab,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab
    (intervalIntegrable_of_clamped (f := fun s => ∑ j ∈ Finset.Icc A B,
      heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff u s)
      (continuous_finsetSum _ fun j _ => continuous_heatLocalizedZeroObservable_clamped
        continuous_heatOuterCutoff hc hasCompactSupport_heatOuterCutoff j) ha hab)
    ((intervalIntegrable_blockObs hc _ _ ha hab).const_mul 9) fun s hs => ?_
  exact sum_outerObs_le hu A B (ha.trans hs.1)

/-- **The `E₂` law on a block of windows.** -/
theorem block_quartic_law {K X₀ Y : ℝ} (hlaws : WindowLaws K X₀) (hK : 0 < K) (hX₀ : 1 ≤ X₀) (hY : 1 ≤ Y)
    {A B : ℤ} (hA : X₀ ≤ A) (hB : (B : ℝ) ≤ Y) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 8)
    (hbY : b * Real.log Y ≤ 1) :
    blockObs uQuartic A B b - blockObs uQuartic A B a + 4 * (∫ s in a..b, blockObs uSquare A B s) ≤
      9 * K * Real.log Y * ∫ s in a..b, blockObs uQuartic (A - 4) (B + 4) s := by
  have hb0 : 0 ≤ b := ha.trans hab
  have hL : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hone (j : ℤ) (hj : j ∈ Finset.Icc A B) :
      windowObs uQuartic j b - windowObs uQuartic j a + 4 * (∫ s in a..b, windowObs uSquare j s) ≤
        K * Real.log Y * ∫ s in a..b,
          heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff uQuartic s := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
    have hjA : (A : ℝ) ≤ j := by exact_mod_cast h1
    have hjB : (j : ℝ) ≤ B := by exact_mod_cast h2
    have hjpos : (0 : ℝ) < j := by linarith only [hX₀, hA, hjA]
    have hlog : Real.log j ≤ Real.log Y := Real.log_le_log hjpos (hjB.trans hB)
    have hbj : b * Real.log j ≤ 1 := (mul_le_mul_of_nonneg_left hlog hb0).trans hbY
    obtain ⟨-, -, h3⟩ := hlaws j (hA.trans hjA) a b ha hab hb hbj
    refine h3.trans (mul_le_mul_of_nonneg_right ?_ (integral_outerObs_nonneg uQuartic_nonneg j hab))
    exact mul_le_mul_of_nonneg_left hlog hK.le
  have hsum := Finset.sum_le_sum hone
  have hint := sum_integral_outerObs_le continuous_uQuartic uQuartic_nonneg A B ha hab
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← intervalIntegral.integral_finsetSum fun j _ => intervalIntegrable_windowObs continuous_uSquare j ha hab]
    at hsum
  change blockObs uQuartic A B b - blockObs uQuartic A B a + 4 * (∫ s in a..b, blockObs uSquare A B s) ≤ _
    at hsum
  refine hsum.trans ?_
  have hKL : 0 ≤ K * Real.log Y := mul_nonneg hK.le hL
  have := mul_le_mul_of_nonneg_left hint hKL
  linarith only [this]

/-- **The nonreal-time budget of a block.** Averaging the `E₁` law over the first `τ₀` of heat time. -/
theorem block_nonreal_budget {K X₀ Y : ℝ} (hlaws : WindowLaws K X₀) (hK : 0 < K) (hX₀ : 1 ≤ X₀) (hY : 1 ≤ Y)
    {A B : ℤ} (hA : X₀ ≤ A) (hB : (B : ℝ) ≤ Y) {τ₀ τ₁ : ℝ} (hτ₀ : 0 < τ₀) (hτ : τ₀ ≤ τ₁) (hτ₁ : τ₁ ≤ 1 / 8)
    (hτY : τ₁ * Real.log Y ≤ 1) :
    2 * τ₀ * ∑ j ∈ Finset.Icc A B, ∫ s in τ₀..τ₁, windowObs uNonreal j s ≤
      (1 + 9 * K * Real.log Y * τ₀) * ∫ s in (0 : ℝ)..τ₁, blockObs uSquare (A - 4) (B + 4) s := by
  have hL : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hτ₁0 : 0 ≤ τ₁ := hτ₀.le.trans hτ
  set D : ℤ → ℝ := fun j => K * Real.log Y *
    ∫ s in (0 : ℝ)..τ₁, heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff uSquare s with hD
  have hone (j : ℤ) (hj : j ∈ Finset.Icc A B) :
      τ₀ * (2 * ∫ s in τ₀..τ₁, windowObs uNonreal j s) ≤
        (∫ s in (0 : ℝ)..τ₀, windowObs uSquare j s) + τ₀ * D j := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
    have hjA : (A : ℝ) ≤ j := by exact_mod_cast h1
    have hjB : (j : ℝ) ≤ B := by exact_mod_cast h2
    have hjpos : (0 : ℝ) < j := by linarith only [hX₀, hA, hjA]
    have hlog : Real.log j ≤ Real.log Y := Real.log_le_log hjpos (hjB.trans hB)
    have hτj : τ₁ * Real.log j ≤ 1 := (mul_le_mul_of_nonneg_left hlog hτ₁0).trans hτY
    -- the bound at each initial time `s ≤ τ₀`
    have hat (s : ℝ) (hs : s ∈ Icc (0 : ℝ) τ₀) :
        2 * (∫ u in τ₀..τ₁, windowObs uNonreal j u) ≤ windowObs uSquare j s + D j := by
      have hsτ : s ≤ τ₁ := hs.2.trans hτ
      obtain ⟨hI, h3, -⟩ := hlaws j (hA.trans hjA) s τ₁ hs.1 hsτ hτ₁ hτj
      obtain ⟨hI₀, -, -⟩ := hlaws j (hA.trans hjA) s τ₀ hs.1 hs.2 (hτ.trans hτ₁)
        ((mul_le_mul_of_nonneg_right hτ (Real.log_nonneg (by linarith only [hX₀, hA, hjA]))).trans hτj)
      obtain ⟨hI₁, -, -⟩ := hlaws j (hA.trans hjA) τ₀ τ₁ hτ₀.le hτ hτ₁ hτj
      have hsplit := intervalIntegral.integral_add_adjacent_intervals hI₀ hI₁
      have hN0 : 0 ≤ ∫ u in s..τ₀, windowObs uNonreal j u :=
        intervalIntegral.integral_nonneg hs.2 fun u _ => windowObs_nonneg uNonreal_nonneg j u
      have hend : 0 ≤ windowObs uSquare j τ₁ := windowObs_nonneg uSquare_nonneg j τ₁
      have hmono : (∫ u in s..τ₁, heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff uSquare u) ≤
          ∫ u in (0 : ℝ)..τ₁, heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff uSquare u := by
        have h4 := intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_outerObs continuous_uSquare j le_rfl hs.1)
          (intervalIntegrable_outerObs continuous_uSquare j hs.1 hsτ)
        have h5 := integral_outerObs_nonneg uSquare_nonneg j hs.1
        linarith only [h4, h5]
      have hKL : K * Real.log j ≤ K * Real.log Y := mul_le_mul_of_nonneg_left hlog hK.le
      have h6 : K * Real.log j *
          (∫ u in s..τ₁, heatLocalizedZeroObservable (j : ℝ) heatOuterCutoff uSquare u) ≤ D j := by
        refine (mul_le_mul_of_nonneg_right hKL
          (integral_outerObs_nonneg uSquare_nonneg j hsτ)).trans ?_
        exact mul_le_mul_of_nonneg_left hmono (mul_nonneg hK.le hL)
      linarith only [h3, h6, hsplit, hN0, hend]
    -- average over `s ∈ [0, τ₀]`
    have hmono := intervalIntegral.integral_mono_on (a := 0) (b := τ₀)
      (f := fun _ => 2 * (∫ u in τ₀..τ₁, windowObs uNonreal j u))
      (g := fun s => windowObs uSquare j s + D j) hτ₀.le intervalIntegrable_const
      ((intervalIntegrable_windowObs continuous_uSquare j le_rfl hτ₀.le).add intervalIntegrable_const)
      (fun s hs => hat s hs)
    rw [intervalIntegral.integral_const, intervalIntegral.integral_add
      (intervalIntegrable_windowObs continuous_uSquare j le_rfl hτ₀.le) intervalIntegrable_const,
      intervalIntegral.integral_const] at hmono
    simpa only [sub_zero, smul_eq_mul] using hmono
  have hsum := Finset.sum_le_sum hone
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← intervalIntegral.integral_finsetSum fun j _ =>
      intervalIntegrable_windowObs continuous_uSquare j le_rfl hτ₀.le] at hsum
  change τ₀ * (2 * _) ≤ (∫ s in (0 : ℝ)..τ₀, blockObs uSquare A B s) + _ at hsum
  -- the block integrals
  have h1 : (∫ s in (0 : ℝ)..τ₀, blockObs uSquare A B s) ≤
      ∫ s in (0 : ℝ)..τ₁, blockObs uSquare (A - 4) (B + 4) s := by
    have hI := intervalIntegrable_blockObs continuous_uSquare (A - 4) (B + 4) le_rfl hτ₀.le
    have hI' := intervalIntegrable_blockObs continuous_uSquare (A - 4) (B + 4) hτ₀.le hτ
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hI hI'
    have h3 : 0 ≤ ∫ s in τ₀..τ₁, blockObs uSquare (A - 4) (B + 4) s :=
      intervalIntegral.integral_nonneg hτ fun s _ => blockObs_nonneg uSquare_nonneg _ _ s
    have h4 := intervalIntegral.integral_mono_on (a := 0) (b := τ₀) hτ₀.le
      (intervalIntegrable_blockObs continuous_uSquare A B le_rfl hτ₀.le) hI
      (fun s _ => blockObs_mono uSquare_nonneg (by omega : A - 4 ≤ A) (by omega : B ≤ B + 4) s)
    linarith only [hsplit, h3, h4]
  have h2 : ∑ j ∈ Finset.Icc A B, D j ≤ K * Real.log Y * (9 *
      ∫ s in (0 : ℝ)..τ₁, blockObs uSquare (A - 4) (B + 4) s) := by
    simp only [hD]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (sum_integral_outerObs_le continuous_uSquare uSquare_nonneg A B le_rfl hτ₁0)
      (mul_nonneg hK.le hL)
  have h3 := mul_le_mul_of_nonneg_left h2 hτ₀.le
  nlinarith only [hsum, h1, h3]

/-! ## Closing the block by Gronwall -/

/-- **A nested family closes under Gronwall.** If `f_k(b) ≤ f_k(0) + A ∫_0^b f_{k+1}` for `k ≤ K` and the last member is
bounded, the first member is bounded by the initial data up to a term `2^{−K}`. -/
theorem weighted_nest_le {f : ℕ → ℝ → ℝ} (hc : ∀ k, Continuous (f k)) (hn : ∀ k s, 0 ≤ f k s) {A T B : ℝ}
    (hA : 0 < A) (hB0 : 0 ≤ B) (K : ℕ) (hB : ∀ s ∈ Icc (0 : ℝ) T, f (K + 1) s ≤ B)
    (h : ∀ k ≤ K, ∀ b ∈ Icc (0 : ℝ) T, f k b ≤ f k 0 + A * ∫ s in (0 : ℝ)..b, f (k + 1) s) :
    ∀ b ∈ Icc (0 : ℝ) T, f 0 b ≤
      (∑ k ∈ Finset.range (K + 1), (1 / 2 : ℝ) ^ k * f k 0 + A * T * B * (1 / 2 : ℝ) ^ K) *
        Real.exp (2 * A * b) := by
  set w : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k with hw
  have hwn (k : ℕ) : 0 ≤ w k := by positivity
  set Φ : ℝ → ℝ := fun s => ∑ k ∈ Finset.range (K + 1), w k * f k s with hΦ
  have hΦc : Continuous Φ := continuous_finsetSum _ fun k _ => continuous_const.mul (hc k)
  set C : ℝ := Φ 0 + A * T * B * (1 / 2 : ℝ) ^ K with hC
  have hmain (b : ℝ) (hb : b ∈ Icc (0 : ℝ) T) : Φ b ≤ C + 2 * A * ∫ s in (0 : ℝ)..b, Φ s := by
    set I : ℕ → ℝ := fun k => ∫ s in (0 : ℝ)..b, f k s with hI
    have hInt (k : ℕ) : IntervalIntegrable (f k) volume 0 b := (hc k).intervalIntegrable 0 b
    have hInn (k : ℕ) : 0 ≤ I k := intervalIntegral.integral_nonneg hb.1 fun s _ => hn k s
    have hΦI : (∫ s in (0 : ℝ)..b, Φ s) = ∑ k ∈ Finset.range (K + 1), w k * I k := by
      simp only [hΦ]
      rw [intervalIntegral.integral_finsetSum fun k _ => (hInt k).const_mul _]
      exact Finset.sum_congr rfl fun k _ => intervalIntegral.integral_const_mul _ _
    have hstep : Φ b ≤ Φ 0 + A * ∑ k ∈ Finset.range (K + 1), w k * I (k + 1) := by
      simp only [hΦ]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun k hk => ?_
      have := h k (by simpa [Nat.lt_succ_iff] using hk) b hb
      have h2 := mul_le_mul_of_nonneg_left this (hwn k)
      simp only [hI]
      nlinarith only [h2]
    have hshift : ∑ k ∈ Finset.range (K + 1), w k * I (k + 1) ≤
        2 * ∑ k ∈ Finset.range (K + 1), w k * I k + w K * I (K + 1) := by
      have h1 : ∑ k ∈ Finset.range (K + 1), w k * I (k + 1) =
          2 * ∑ k ∈ Finset.range (K + 1), w (k + 1) * I (k + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hw, pow_succ]
        ring
      have h2 := Finset.sum_range_succ' (fun k => w k * I k) (K + 1)
      have h3 := Finset.sum_range_succ (fun k => w k * I k) (K + 1)
      have h4 : 0 ≤ w 0 * I 0 := mul_nonneg (hwn 0) (hInn 0)
      have h5 : 2 * (w (K + 1) * I (K + 1)) = w K * I (K + 1) := by
        simp only [hw, pow_succ]
        ring
      rw [h1]
      linarith only [h2, h3, h4, h5]
    have hlast : I (K + 1) ≤ T * B := by
      have hle := intervalIntegral.integral_mono_on (a := 0) (b := b) hb.1 (hInt (K + 1))
        (intervalIntegrable_const (c := B)) (fun s hs => hB s ⟨hs.1, hs.2.trans hb.2⟩)
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hle
      exact hle.trans (mul_le_mul_of_nonneg_right hb.2 hB0)
    rw [hΦI]
    have h6 := mul_le_mul_of_nonneg_left hlast (mul_nonneg hA.le (hwn K))
    have h7 := mul_le_mul_of_nonneg_left hshift hA.le
    simp only [hC, hw] at h6 ⊢
    nlinarith only [hstep, h6, h7]
  -- Gronwall for `u = Φ − C`
  have hu : Continuous fun s => Φ s - C := hΦc.sub continuous_const
  have hgr := GaloisForLFunctions.HTGeometry.DaiYoshikawa.le_affine_gronwall_of_volterra_bound
    (T := T) (a := 2 * A * C) (b := 2 * A) (by positivity) hu (fun x hx => by
      have hm := hmain x hx
      have hsub : (∫ σ in (0 : ℝ)..x, (Φ σ - C)) = (∫ σ in (0 : ℝ)..x, Φ σ) - x * C := by
        rw [intervalIntegral.integral_sub (hΦc.intervalIntegrable 0 x) intervalIntegrable_const,
          intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      rw [hsub]
      nlinarith only [hm])
  intro b hb
  have hg := hgr b hb
  have hsimp : 2 * A * C / (2 * A) = C := by
    field_simp
  rw [hsimp] at hg
  have hf0 : f 0 b ≤ Φ b := by
    have h1 := Finset.single_le_sum (f := fun k => w k * f k b)
      (fun k _ => mul_nonneg (hwn k) (hn k b)) (Finset.mem_range.mpr (Nat.succ_pos K))
    have h2 : w 0 = 1 := by simp [hw]
    simp only [h2, one_mul] at h1
    exact h1
  have hfin : Φ b ≤ C * Real.exp (2 * A * b) := by nlinarith only [hg]
  exact hf0.trans hfin

/-! ## The crude bound -/

/-- The fourth moment of a unit window is at most its zero count. -/
theorem exists_windowObs_quartic_le :
    ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ j : ℤ, X₀ ≤ j → ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 8 → s * Real.log j ≤ 1 →
      windowObs uQuartic j s ≤ C * Real.log j := by
  obtain ⟨C, hC, X₀, hX₀, hforce⟩ := exists_uniform_riemannHeat_exterior_force
  refine ⟨C, hC, X₀, hX₀, fun j hj s hs hs8 hsj => ?_⟩
  obtain ⟨S, Q, hS, hcount, -, -⟩ := hforce j hj s hs hs8 hsj
  have heq := heatLocalizedZeroObservable_eq_sum (X := (j : ℝ)) hs w₀ uQuartic
    (fun x hx => w₀_eq_zero hx) S (fun z hz hr => (hS z).mpr ⟨hz, by linarith only [hr]⟩)
  change windowObs uQuartic j s = _ at heq
  rw [heq]
  refine le_trans ?_ hcount
  rw [Nat.cast_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  have him := abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg hs ((hS z).mp hz).1
  have hy : uQuartic z.im ≤ 1 := by
    unfold uQuartic
    have h1 : z.im ^ 2 ≤ 1 := by
      have := abs_le.mp him
      nlinarith only [this.1, this.2]
    nlinarith only [h1, sq_nonneg z.im]
  have hw : w₀ (z.re - j) * uQuartic z.im ≤ 1 :=
    (mul_le_mul (w₀_le_one _) hy (uQuartic_nonneg _) zero_le_one).trans (by norm_num)
  have hm : (0 : ℝ) ≤ zeroMult (riemannHeat s) z := Nat.cast_nonneg _
  simpa using mul_le_mul_of_nonneg_left hw hm

/-! ## The budget -/

/-- **The nonreal-time budget.** On a block of unit windows at heights `≤ Y`, the total time spent nonreal above `τ₀`
and below `τ₁ = 1/log Y` is controlled by the fourth moment of the depths at time zero, on the enlarged block, up to a term
`2^{−K}` in the enlargement `K`. -/
theorem exists_sum_nonrealTime_le :
    ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ (Y : ℝ) (A B : ℤ) (K : ℕ), 8 ≤ Real.log Y → A ≤ B →
      X₀ ≤ ((A - 4 * (K + 3) : ℤ) : ℝ) → ((B + 4 * (K + 3) : ℤ) : ℝ) ≤ Y →
      ∀ τ₀, 0 < τ₀ → τ₀ ≤ 1 / Real.log Y →
        ∑ j ∈ Finset.Icc A B, ∫ s in τ₀..(1 / Real.log Y), windowObs uNonreal j s ≤
          C * (1 / τ₀ + Real.log Y) * (blockObs uQuartic (A - 4 * (K + 2)) (B + 4 * (K + 2)) 0 +
            (1 / 2 : ℝ) ^ K * (((B - A + 8 * (K + 3) + 1 : ℤ) : ℝ) * Real.log Y)) := by
  obtain ⟨K₀, hK₀, X₁, hX₁, hlaws⟩ := exists_window_laws
  obtain ⟨C₀, hC₀, X₂, hX₂, hcrude⟩ := exists_windowObs_quartic_le
  set c₁ : ℝ := 1 + 18 * K₀ * Real.exp (18 * K₀) + 81 * K₀ ^ 2 * Real.exp (18 * K₀) * (1 + C₀) with hc₁
  have hc₁p : 0 < c₁ := by positivity
  refine ⟨(1 + 9 * K₀) * c₁, by positivity, max X₁ X₂, hX₁.trans (le_max_left _ _), ?_⟩
  intro Y A B K hlogY hAB hA hB τ₀ hτ₀ hτ₀le
  set X₀ := max X₁ X₂ with hX₀def
  have hX₀1 : 1 ≤ X₀ := by linarith only [hX₁, le_max_left X₁ X₂]
  have hW : WindowLaws K₀ X₀ := fun j hj => hlaws j ((le_max_left _ _).trans hj)
  have hL : 0 < Real.log Y := by linarith only [hlogY]
  set L := Real.log Y with hLdef
  -- the height range
  have hKn : (0 : ℤ) ≤ K := Int.natCast_nonneg K
  have hAdown (n : ℤ) (hn : n ≤ K + 3) : X₀ ≤ ((A - 4 * n : ℤ) : ℝ) := by
    refine hA.trans ?_
    have : A - 4 * ((K : ℤ) + 3) ≤ A - 4 * n := by omega
    exact_mod_cast this
  have hBup (n : ℤ) (hn : n ≤ K + 3) : ((B + 4 * n : ℤ) : ℝ) ≤ Y := by
    refine le_trans ?_ hB
    have : B + 4 * n ≤ B + 4 * ((K : ℤ) + 3) := by omega
    exact_mod_cast this
  have hY : 1 ≤ Y := by
    have h1 := hAdown (K + 3) le_rfl
    have h2 := hBup (K + 3) le_rfl
    have h3 : ((A - 4 * ((K : ℤ) + 3) : ℤ) : ℝ) ≤ ((B + 4 * ((K : ℤ) + 3) : ℤ) : ℝ) := by
      have : A - 4 * ((K : ℤ) + 3) ≤ B + 4 * ((K : ℤ) + 3) := by omega
      exact_mod_cast this
    linarith only [h1, h2, h3, hX₀1]
  set τ₁ : ℝ := 1 / L with hτ₁def
  have hτ₁L : τ₁ * L = 1 := by rw [hτ₁def]; field_simp
  have hτ₁pos : 0 < τ₁ := by positivity
  have hτ₁8 : τ₁ ≤ 1 / 8 := by
    rw [hτ₁def]
    exact one_div_le_one_div_of_le (by norm_num) hlogY
  have hsτ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) τ₁) : s * L ≤ 1 :=
    (mul_le_mul_of_nonneg_right hs.2 hL.le).trans hτ₁L.le
  set A' : ℝ := 9 * K₀ * L with hA'
  have hA'pos : 0 < A' := by positivity
  have hA'τ : A' * τ₁ = 9 * K₀ := by
    rw [hA']
    calc 9 * K₀ * L * τ₁ = 9 * K₀ * (τ₁ * L) := by ring
      _ = _ := by rw [hτ₁L, mul_one]
  -- the nested family
  set f : ℕ → ℝ → ℝ := fun k s =>
    blockObs uQuartic (A - 4 * ((k : ℤ) + 2)) (B + 4 * ((k : ℤ) + 2)) (max s 0) with hf
  have hfc (k : ℕ) : Continuous (f k) := continuous_blockObs_clamped continuous_uQuartic _ _
  have hfn (k : ℕ) (s : ℝ) : 0 ≤ f k s := blockObs_nonneg uQuartic_nonneg _ _ _
  have hfeq (k : ℕ) {s : ℝ} (hs : 0 ≤ s) :
      f k s = blockObs uQuartic (A - 4 * ((k : ℤ) + 2)) (B + 4 * ((k : ℤ) + 2)) s := by
    simp only [hf, max_eq_left hs]
  -- the crude bound on the outermost block
  set R : ℝ := ((B - A + 8 * (K + 3) + 1 : ℤ) : ℝ) * L with hR
  have hRn : 0 ≤ R := by
    have : (0 : ℤ) ≤ B - A + 8 * ((K : ℤ) + 3) + 1 := by omega
    have h' : (0 : ℝ) ≤ ((B - A + 8 * (K + 3) + 1 : ℤ) : ℝ) := by exact_mod_cast this
    exact mul_nonneg h' hL.le
  have hlast (s : ℝ) (hs : s ∈ Icc (0 : ℝ) τ₁) : f (K + 1) s ≤ C₀ * R := by
    rw [hfeq _ hs.1]
    unfold blockObs
    have hcard : ((Finset.Icc (A - 4 * (((K + 1 : ℕ) : ℤ) + 2)) (B + 4 * (((K + 1 : ℕ) : ℤ) + 2))).card : ℝ) =
        ((B - A + 8 * (K + 3) + 1 : ℤ) : ℝ) := by
      rw [Int.card_Icc]
      have h0 : (0 : ℤ) ≤ B + 4 * (((K + 1 : ℕ) : ℤ) + 2) + 1 - (A - 4 * (((K + 1 : ℕ) : ℤ) + 2)) := by
        push_cast
        omega
      have h1 : ((((B + 4 * (((K + 1 : ℕ) : ℤ) + 2) + 1 - (A - 4 * (((K + 1 : ℕ) : ℤ) + 2))).toNat : ℕ) : ℤ)) =
          B - A + 8 * (K + 3) + 1 := by
        rw [Int.toNat_of_nonneg h0]
        push_cast
        ring
      calc (((B + 4 * (((K + 1 : ℕ) : ℤ) + 2) + 1 - (A - 4 * (((K + 1 : ℕ) : ℤ) + 2))).toNat : ℕ) : ℝ)
          = (((((B + 4 * (((K + 1 : ℕ) : ℤ) + 2) + 1 - (A - 4 * (((K + 1 : ℕ) : ℤ) + 2))).toNat : ℕ) : ℤ)) : ℝ) := by
            push_cast
            rfl
        _ = _ := by rw [h1]
    have hsum : ∑ j ∈ Finset.Icc (A - 4 * (((K + 1 : ℕ) : ℤ) + 2)) (B + 4 * (((K + 1 : ℕ) : ℤ) + 2)),
        windowObs uQuartic j s ≤
        ∑ _j ∈ Finset.Icc (A - 4 * (((K + 1 : ℕ) : ℤ) + 2)) (B + 4 * (((K + 1 : ℕ) : ℤ) + 2)), C₀ * L := by
      refine Finset.sum_le_sum fun j hj => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
      have hj1 : ((A - 4 * ((K : ℤ) + 3) : ℤ) : ℝ) ≤ j := by
        have : A - 4 * ((K : ℤ) + 3) ≤ j := by
          push_cast at h1
          omega
        exact_mod_cast this
      have hj2 : (j : ℝ) ≤ ((B + 4 * ((K : ℤ) + 3) : ℤ) : ℝ) := by
        have : j ≤ B + 4 * ((K : ℤ) + 3) := by
          push_cast at h2
          omega
        exact_mod_cast this
      have hjX : X₀ ≤ j := (hAdown (K + 3) le_rfl).trans hj1
      have hjY : (j : ℝ) ≤ Y := hj2.trans (hBup (K + 3) le_rfl)
      have hjpos : (0 : ℝ) < j := by linarith only [hjX, hX₀1]
      have hlog : Real.log j ≤ L := Real.log_le_log hjpos hjY
      have hsj : s * Real.log j ≤ 1 := (mul_le_mul_of_nonneg_left hlog hs.1).trans (hsτ s hs)
      refine (hcrude j ((le_max_right _ _).trans hjX) s hs.1 (hs.2.trans hτ₁8) hsj).trans ?_
      exact mul_le_mul_of_nonneg_left hlog hC₀.le
    refine hsum.trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hcard, hR]
    ring
  -- the nesting
  have hnest : ∀ k ≤ K, ∀ b ∈ Icc (0 : ℝ) τ₁, f k b ≤ f k 0 + A' * ∫ s in (0 : ℝ)..b, f (k + 1) s := by
    intro k hk b hb
    have hkZ : ((k : ℤ) + 2) ≤ K + 3 := by omega
    have hkZ' : ((k : ℤ) + 3) ≤ K + 3 := by omega
    have hlaw := block_quartic_law (Y := Y) hW hK₀ hX₀1 hY (A := A - 4 * ((k : ℤ) + 2))
      (B := B + 4 * ((k : ℤ) + 2)) (hAdown _ hkZ) (hBup _ hkZ) le_rfl hb.1 (hb.2.trans hτ₁8) (hsτ b hb)
    have hV : 0 ≤ ∫ s in (0 : ℝ)..b, blockObs uSquare (A - 4 * ((k : ℤ) + 2)) (B + 4 * ((k : ℤ) + 2)) s :=
      intervalIntegral.integral_nonneg hb.1 fun s _ => blockObs_nonneg uSquare_nonneg _ _ s
    have hint : (∫ s in (0 : ℝ)..b, f (k + 1) s) = ∫ s in (0 : ℝ)..b,
        blockObs uQuartic (A - 4 * ((k : ℤ) + 2) - 4) (B + 4 * ((k : ℤ) + 2) + 4) s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hb.1] at hs
      rw [hfeq _ hs.1]
      congr 1
      · push_cast; ring
      · push_cast; ring
    rw [hint, hfeq k hb.1, hfeq k le_rfl]
    have hmul : 9 * K₀ * Real.log Y = A' := rfl
    rw [hmul] at hlaw
    linarith only [hlaw, hV]
  have hnested := weighted_nest_le hfc hfn hA'pos (by positivity : 0 ≤ C₀ * R) K hlast hnest
  -- the total at time zero
  set T₀ := blockObs uQuartic (A - 4 * ((K : ℤ) + 2)) (B + 4 * ((K : ℤ) + 2)) 0 with hT₀
  have hT₀n : 0 ≤ T₀ := blockObs_nonneg uQuartic_nonneg _ _ _
  have hsum0 : ∑ k ∈ Finset.range (K + 1), (1 / 2 : ℝ) ^ k * f k 0 ≤ 2 * T₀ := by
    have hle (k : ℕ) (hk : k ∈ Finset.range (K + 1)) : (1 / 2 : ℝ) ^ k * f k 0 ≤ (1 / 2 : ℝ) ^ k * T₀ := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hfeq k le_rfl]
      have hk' : k ≤ K := by simpa [Nat.lt_succ_iff] using hk
      have hkZ : (k : ℤ) ≤ K := by exact_mod_cast hk'
      exact blockObs_mono uQuartic_nonneg (by omega) (by omega) 0
    refine (Finset.sum_le_sum hle).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_geometric_two_le (K + 1)) hT₀n
  set M : ℝ := (2 * T₀ + 9 * K₀ * (C₀ * R) * (1 / 2 : ℝ) ^ K) * Real.exp (18 * K₀) with hM
  have hMn : 0 ≤ M := by positivity
  have hbound (b : ℝ) (hb : b ∈ Icc (0 : ℝ) τ₁) :
      blockObs uQuartic (A - 4 - 4) (B + 4 + 4) b ≤ M := by
    have h1 := hnested b hb
    have h2 : f 0 b = blockObs uQuartic (A - 4 - 4) (B + 4 + 4) b := by
      rw [hfeq 0 hb.1]
      congr 1
      · push_cast; ring
      · push_cast; ring
    rw [← h2]
    refine h1.trans ?_
    have hexp : Real.exp (2 * A' * b) ≤ Real.exp (18 * K₀) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hb.2 hA'pos.le
      nlinarith only [this, hA'τ]
    have hcoef : A' * τ₁ * (C₀ * R) * (1 / 2 : ℝ) ^ K = 9 * K₀ * (C₀ * R) * (1 / 2 : ℝ) ^ K := by
      rw [hA'τ]
    rw [hM]
    refine mul_le_mul ?_ hexp (Real.exp_pos _).le (by positivity)
    rw [hcoef]
    linarith only [hsum0]
  -- the `E₂` law on the first enlargement pays the integrated `E₁`
  have h41 : ((1 : ℤ)) ≤ K + 3 := by omega
  have hlaw1 := block_quartic_law (Y := Y) hW hK₀ hX₀1 hY (A := A - 4) (B := B + 4)
    (by simpa using hAdown 1 h41) (by simpa using hBup 1 h41) le_rfl hτ₁pos.le hτ₁8 hτ₁L.le
  have hint₂ : (∫ s in (0 : ℝ)..τ₁, blockObs uQuartic (A - 4 - 4) (B + 4 + 4) s) ≤ τ₁ * M := by
    have hle := intervalIntegral.integral_mono_on (a := 0) (b := τ₁) hτ₁pos.le
      (intervalIntegrable_blockObs continuous_uQuartic (A - 4 - 4) (B + 4 + 4) le_rfl hτ₁pos.le)
      (intervalIntegrable_const (c := M)) (fun s hs => hbound s hs)
    rwa [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hle
  have hT₁ : blockObs uQuartic (A - 4) (B + 4) 0 ≤ T₀ :=
    blockObs_mono uQuartic_nonneg (by omega) (by omega) 0
  set I₁ := ∫ s in (0 : ℝ)..τ₁, blockObs uSquare (A - 4) (B + 4) s with hI₁
  have hI₁n : 0 ≤ I₁ := intervalIntegral.integral_nonneg hτ₁pos.le fun s _ =>
    blockObs_nonneg uSquare_nonneg _ _ s
  have hI₁le : 4 * I₁ ≤ T₀ + 9 * K₀ * M := by
    have hend : 0 ≤ blockObs uQuartic (A - 4) (B + 4) τ₁ := blockObs_nonneg uQuartic_nonneg _ _ _
    have hprod : 9 * K₀ * Real.log Y * (∫ s in (0 : ℝ)..τ₁, blockObs uQuartic (A - 4 - 4) (B + 4 + 4) s) ≤
        9 * K₀ * M := by
      have h1 := mul_le_mul_of_nonneg_left hint₂ hA'pos.le
      have h2 : A' * (τ₁ * M) = 9 * K₀ * M := by
        rw [← mul_assoc, hA'τ]
      rw [h2] at h1
      exact h1
    linarith only [hlaw1, hend, hprod, hT₁]
  -- the budget
  have hbudget := block_nonreal_budget (Y := Y) hW hK₀ hX₀1 hY (A := A) (B := B)
    (by simpa using hAdown 0 (by omega)) (by simpa using hBup 0 (by omega)) hτ₀ hτ₀le hτ₁8 hτ₁L.le
  set S := ∑ j ∈ Finset.Icc A B, ∫ s in τ₀..τ₁, windowObs uNonreal j s with hS
  set P := 1 / τ₀ + L with hP
  have hPn : 0 < P := by positivity
  set G := T₀ + (1 / 2 : ℝ) ^ K * R with hG
  have hGn : 0 ≤ G := by positivity
  have hS1 : S ≤ (1 / (2 * τ₀) + 9 * K₀ * L / 2) * I₁ := by
    have heq : (1 / (2 * τ₀) + 9 * K₀ * L / 2) * I₁ = (1 + 9 * K₀ * L * τ₀) * I₁ / (2 * τ₀) := by
      field_simp
    rw [heq, le_div_iff₀ (by positivity)]
    linarith only [hbudget]
  have hcoef : 1 / (2 * τ₀) + 9 * K₀ * L / 2 ≤ (1 + 9 * K₀) * P := by
    have h1 : 1 / (2 * τ₀) ≤ 1 / τ₀ := by
      apply one_div_le_one_div_of_le hτ₀
      linarith only [hτ₀]
    have h2 : 0 ≤ 1 / τ₀ := by positivity
    rw [hP]
    nlinarith only [h1, h2, hL, hK₀, mul_pos hK₀ hL]
  have hI₁c : I₁ ≤ c₁ * G := by
    have hexp : 0 < Real.exp (18 * K₀) := Real.exp_pos _
    have hpow : 0 ≤ (1 / 2 : ℝ) ^ K := by positivity
    have hexpand : T₀ + 9 * K₀ * M = (1 + 18 * K₀ * Real.exp (18 * K₀)) * T₀ +
        81 * K₀ ^ 2 * Real.exp (18 * K₀) * C₀ * ((1 / 2 : ℝ) ^ K * R) := by
      rw [hM]
      ring
    have hupper : (1 + 18 * K₀ * Real.exp (18 * K₀)) * T₀ +
        81 * K₀ ^ 2 * Real.exp (18 * K₀) * C₀ * ((1 / 2 : ℝ) ^ K * R) ≤ c₁ * G := by
      rw [hc₁, hG]
      have h1 : 0 ≤ 81 * K₀ ^ 2 * Real.exp (18 * K₀) := by positivity
      have h2 : 0 ≤ (1 / 2 : ℝ) ^ K * R := by positivity
      nlinarith only [mul_nonneg h1 hT₀n, mul_nonneg h1 h2, hT₀n, h2,
        mul_nonneg (mul_nonneg hK₀.le hexp.le) h2, mul_nonneg h1 (mul_nonneg hC₀.le hT₀n),
        mul_nonneg (mul_nonneg hK₀.le hexp.le) hT₀n]
    have hGc : 0 ≤ c₁ * G := by positivity
    linarith only [hI₁le, hexpand, hupper, hGc]
  have hfinal := mul_le_mul hcoef hI₁c hI₁n (by positivity : 0 ≤ (1 + 9 * K₀) * P)
  calc S ≤ (1 / (2 * τ₀) + 9 * K₀ * L / 2) * I₁ := hS1
    _ ≤ (1 + 9 * K₀) * P * (c₁ * G) := hfinal
    _ = (1 + 9 * K₀) * c₁ * P * G := by ring

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
