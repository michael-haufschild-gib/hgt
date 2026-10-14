import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# A continuous inversion-symmetric Fourier-blind core of support ratio `9/5`

A continuous even `G : ℝ → ℝ` with `G(1/x) = x G(x)` for `x > 0`, vanishing on `[0, c)` and with
`Ĝ(n) = 0` for every integer `|n| ≥ 2`, vanishes when `12c > 7`
(`eq_zero_of_inversionSymmetric_fourierBlind_of_twelve_sevenths`).  This file shows that the
threshold for continuous `G` lies below `2`.

**Theorem** (`exists_inversionSymmetric_fourierBlind_nine_fifths`).  There is a nonzero
continuous even `G` with `G(1/x) = x G(x)` for `x > 0`, vanishing on `[0, 5/9)`, and with
`Ĝ(n) = 0` for *every* integer `n`.  Its support is contained in `5/9 ≤ |x| ≤ 9/5`.

So the support-ratio threshold for continuous Fourier-blind cores lies in `[12/7, 9/5]`.

**Construction.**
* *A `−1`-eigenfunction of the twisted Mayer operator* (`exists_blindCoreMayer_eigen`).  Let
  `M u(r) = u(1/(r+1))/(r+1) − u(1/(r+2))/(r+2) + u(1/(r+3))/(r+3)`: the Gauss–Mayer operator at
  `s = ½`, twisted by `(−1)^{m−1}`, on functions vanishing outside `(1/4, 4/5)` (only the
  branches `m ≤ 3` meet that interval).  The lift `S u(y) = (−1)^{m−1} u(r)/W(r)` at
  `y = 1/(r + m)`, with `W(r) = Σ_{m ≤ 3} 1/(r+m) ≥ 13/12` on `[0, 1]`, satisfies `M S u = u` on
  `[0, 1]` and `‖S u‖ ≤ (12/13)‖u‖`.  For a seed `u₀` with `M u₀ = 0`, the series
  `f = Σ_k (−1)^k S^k u₀` converges uniformly and `M f = −f` on `[0, 1]`; `f + S f = u₀ ≠ 0`.
  Splitting the value among three branches makes the lift contract (`13/12 > 1`); this is
  where continuity, not analyticity, is used.
* *The core* (`blindCoreFn`).  `G(x) = Γ(|x|) + Γ(1/|x|)/|x|`, where on `[½, 1)`
  `Γ(x) = f(1 − x) − f((1−x)/x)/x − f((1−x)/(2−x))/(2−x) = −M f(r)/(1 − x)`,
  `r = (2x − 1)/(1 − x)`.  The eigen-equation at `(1 − x)/x` gives the three-term identity
  `G(x) + G(1 + x) + G(2 − x) = 0` on `[½, 1]`, hence `Σ_k G(x + k) = 0`, and every Fourier
  coefficient of the periodization, i.e. `Ĝ(n)`, vanishes (`Real.fourierCoeff_tsum_comp_add`).
-/

open MeasureTheory Set Real Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

/-! ### The three-branch twisted Mayer operator and its lift -/

/-- Vanishing outside the open interval `(1/4, 4/5)`. -/
def BlindCoreSupported (u : ℝ → ℝ) : Prop := ∀ t, (t ≤ 1 / 4 ∨ 4 / 5 ≤ t) → u t = 0

/-- `W(t) = 1/(t + 1) + 1/(t + 2) + 1/(t + 3)`. -/
def blindCoreWeight (t : ℝ) : ℝ := (t + 1)⁻¹ + (t + 2)⁻¹ + (t + 3)⁻¹

/-- The twisted Mayer operator at `s = ½` on its first three branches. -/
def blindCoreMayer (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  u (r + 1)⁻¹ / (r + 1) - u (r + 2)⁻¹ / (r + 2) + u (r + 3)⁻¹ / (r + 3)

/-- The lift: at `y = 1/(r + m)`, `m ≤ 3`, the value `(−1)^{m−1} u(r)/W(r)`. -/
def blindCoreLift (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  u (y⁻¹ - 1) / blindCoreWeight (y⁻¹ - 1) - u (y⁻¹ - 2) / blindCoreWeight (y⁻¹ - 2) +
    u (y⁻¹ - 3) / blindCoreWeight (y⁻¹ - 3)

theorem blindCoreWeight_pos {t : ℝ} (ht : 0 ≤ t) : 0 < blindCoreWeight t := by
  unfold blindCoreWeight
  have h1 : 0 < (t + 1)⁻¹ := inv_pos.mpr (by linarith)
  have h2 : 0 < (t + 2)⁻¹ := inv_pos.mpr (by linarith)
  have h3 : 0 < (t + 3)⁻¹ := inv_pos.mpr (by linarith)
  linarith

theorem thirteen_twelfths_le_blindCoreWeight {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    13 / 12 ≤ blindCoreWeight t := by
  unfold blindCoreWeight
  have e1 : (2 : ℝ)⁻¹ ≤ (t + 1)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have e2 : (3 : ℝ)⁻¹ ≤ (t + 2)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have e3 : (4 : ℝ)⁻¹ ≤ (t + 3)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  norm_num at e1 e2 e3
  linarith

/-- Composition with a Gauss branch `y ↦ 1/y − m`, `1 ≤ m ≤ 3`, keeps the support in
`(1/4, 4/5)`. -/
theorem blindCoreSupported_comp_inv_sub {g : ℝ → ℝ} (hs : BlindCoreSupported g) {m : ℝ}
    (hm1 : 1 ≤ m) (hm3 : m ≤ 3) : BlindCoreSupported fun y => g (y⁻¹ - m) := by
  intro y hy
  apply hs
  rcases hy with hy | hy
  · rcases le_or_gt y 0 with hy0 | hy0
    · left
      have : y⁻¹ ≤ 0 := inv_nonpos.mpr hy0
      linarith
    · right
      have h4 : 4 ≤ y⁻¹ := by
        rw [le_inv_comm₀ (by norm_num) hy0]
        norm_num
        linarith
      linarith
  · left
    have hy0 : 0 < y := by linarith
    have : y⁻¹ ≤ 5 / 4 := by
      rw [inv_le_comm₀ hy0 (by norm_num)]
      norm_num
      linarith
    linarith

/-- A continuous function supported in `(1/4, 4/5)` composed with `y ↦ 1/y − m`, `m ≥ 0`, is
continuous: it vanishes near `0`. -/
theorem continuous_comp_inv_sub_of_blindCoreSupported {g : ℝ → ℝ} (hg : Continuous g)
    (hs : BlindCoreSupported g) {m : ℝ} (hm : 0 ≤ m) : Continuous fun y => g (y⁻¹ - m) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    have hpos : (0 : ℝ) < (m + 1)⁻¹ := inv_pos.mpr (by linarith)
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 0] fun y => g (y⁻¹ - m) := by
      filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hpos) hpos] with z hz
      symm
      apply hs
      rcases lt_trichotomy z 0 with hz0 | hz0 | hz0
      · left
        have : z⁻¹ < 0 := inv_lt_zero.mpr hz0
        linarith
      · left
        rw [hz0, inv_zero]
        linarith
      · right
        have : m + 1 < z⁻¹ := by
          rw [lt_inv_comm₀ (by linarith) hz0]
          exact hz.2
        linarith
    exact continuousAt_const.congr hev
  · exact hg.continuousAt.comp ((continuousAt_inv₀ hy).sub continuousAt_const)

theorem continuous_div_blindCoreWeight {u : ℝ → ℝ} (hu : Continuous u)
    (hs : BlindCoreSupported u) : Continuous fun t => u t / blindCoreWeight t := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_or_ge t (1 / 4) with ht | ht
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 t] fun t => u t / blindCoreWeight t := by
      filter_upwards [Iio_mem_nhds ht] with s hs'
      rw [hs s (Or.inl (le_of_lt hs')), zero_div]
    exact continuousAt_const.congr hev
  · have c1 : ContinuousAt (fun s : ℝ => (s + 1)⁻¹) t :=
      (continuousAt_id.add continuousAt_const).inv₀ (ne_of_gt (by simp; linarith))
    have c2 : ContinuousAt (fun s : ℝ => (s + 2)⁻¹) t :=
      (continuousAt_id.add continuousAt_const).inv₀ (ne_of_gt (by simp; linarith))
    have c3 : ContinuousAt (fun s : ℝ => (s + 3)⁻¹) t :=
      (continuousAt_id.add continuousAt_const).inv₀ (ne_of_gt (by simp; linarith))
    have hW : ContinuousAt blindCoreWeight t := (c1.add c2).add c3
    exact hu.continuousAt.div hW (blindCoreWeight_pos (by linarith)).ne'

theorem blindCoreSupported_div_weight {u : ℝ → ℝ} (hs : BlindCoreSupported u) :
    BlindCoreSupported fun t => u t / blindCoreWeight t := fun t ht => by
  simp only [hs t ht, zero_div]

theorem blindCoreSupported_lift {u : ℝ → ℝ} (hs : BlindCoreSupported u) :
    BlindCoreSupported (blindCoreLift u) := by
  have hq := blindCoreSupported_div_weight hs
  intro y hy
  have h1 := blindCoreSupported_comp_inv_sub hq (m := 1) le_rfl (by norm_num) y hy
  have h2 := blindCoreSupported_comp_inv_sub hq (m := 2) (by norm_num) (by norm_num) y hy
  have h3 := blindCoreSupported_comp_inv_sub hq (m := 3) (by norm_num) le_rfl y hy
  unfold blindCoreLift
  simp only at h1 h2 h3
  rw [h1, h2, h3]
  ring

theorem continuous_blindCoreLift {u : ℝ → ℝ} (hu : Continuous u) (hs : BlindCoreSupported u) :
    Continuous (blindCoreLift u) := by
  have hq := continuous_div_blindCoreWeight hu hs
  have hqs := blindCoreSupported_div_weight hs
  have c1 := continuous_comp_inv_sub_of_blindCoreSupported hq hqs (m := 1) (by norm_num)
  have c2 := continuous_comp_inv_sub_of_blindCoreSupported hq hqs (m := 2) (by norm_num)
  have c3 := continuous_comp_inv_sub_of_blindCoreSupported hq hqs (m := 3) (by norm_num)
  exact (c1.sub c2).add c3

/-- **The lift contracts**: `|S u| ≤ (12/13) sup |u|`.  At each point at most one branch
contributes, and `W ≥ 13/12` on `[0, 1]`. -/
theorem abs_blindCoreLift_le {u : ℝ → ℝ} {B : ℝ} (hs : BlindCoreSupported u)
    (hB : ∀ t, |u t| ≤ B) (y : ℝ) : |blindCoreLift u y| ≤ 12 / 13 * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hz : ∀ t, ¬(1 / 4 < t ∧ t < 4 / 5) → u t = 0 := by
    intro t ht
    apply hs
    by_contra h
    push Not at h
    exact ht h
  have hq : ∀ t, 1 / 4 < t → t < 4 / 5 → |u t / blindCoreWeight t| ≤ 12 / 13 * B := by
    intro t h1 h2
    have hW := thirteen_twelfths_le_blindCoreWeight (t := t) (by linarith) (by linarith)
    have hWp : 0 < blindCoreWeight t := by linarith
    rw [abs_div, abs_of_pos hWp, div_le_iff₀ hWp]
    have := hB t
    nlinarith
  unfold blindCoreLift
  set a := y⁻¹
  by_cases h1 : 1 / 4 < a - 1 ∧ a - 1 < 4 / 5
  · rw [hz (a - 2) (fun h => by linarith [h.1, h1.2]),
      hz (a - 3) (fun h => by linarith [h.1, h1.2]), zero_div, zero_div, sub_zero, add_zero]
    exact hq _ h1.1 h1.2
  · rw [hz (a - 1) h1, zero_div, zero_sub]
    by_cases h2 : 1 / 4 < a - 2 ∧ a - 2 < 4 / 5
    · rw [hz (a - 3) (fun h => by linarith [h.1, h2.2]), zero_div, add_zero, abs_neg]
      exact hq _ h2.1 h2.2
    · rw [hz (a - 2) h2, zero_div, neg_zero, zero_add]
      by_cases h3 : 1 / 4 < a - 3 ∧ a - 3 < 4 / 5
      · exact hq _ h3.1 h3.2
      · rw [hz (a - 3) h3, zero_div, abs_zero]
        exact mul_nonneg (by norm_num) hB0

/-- **`M S = id` on `[0, 1]`.** -/
theorem blindCoreMayer_lift {u : ℝ → ℝ} (hs : BlindCoreSupported u) {r : ℝ} (h0 : 0 ≤ r)
    (h1 : r ≤ 1) : blindCoreMayer (blindCoreLift u) r = u r := by
  unfold blindCoreMayer blindCoreLift
  simp only [inv_inv]
  have e11 : r + 1 - 1 = r := by ring
  have e22 : r + 2 - 2 = r := by ring
  have e33 : r + 3 - 3 = r := by ring
  have z12 : u (r + 1 - 2) = 0 := hs _ (Or.inl (by linarith))
  have z13 : u (r + 1 - 3) = 0 := hs _ (Or.inl (by linarith))
  have z21 : u (r + 2 - 1) = 0 := hs _ (Or.inr (by linarith))
  have z23 : u (r + 2 - 3) = 0 := hs _ (Or.inl (by linarith))
  have z31 : u (r + 3 - 1) = 0 := hs _ (Or.inr (by linarith))
  have z32 : u (r + 3 - 2) = 0 := hs _ (Or.inr (by linarith))
  rw [e11, e22, e33, z12, z13, z21, z23, z31, z32]
  have hW := (blindCoreWeight_pos h0).ne'
  have key : u r = u r / blindCoreWeight r * ((r + 1)⁻¹ + (r + 2)⁻¹ + (r + 3)⁻¹) := by
    rw [show (r + 1)⁻¹ + (r + 2)⁻¹ + (r + 3)⁻¹ = blindCoreWeight r from rfl,
      div_mul_cancel₀ _ hW]
  conv_rhs => rw [key]
  ring

/-! ### The seed -/

/-- A bump supported in `[1/4, 4/5]`. -/
def blindCoreBump (t : ℝ) : ℝ := max 0 ((t - 1 / 4) * (4 / 5 - t))

/-- The seed `u₀(y) = (1/y)(β(1/y − 1) + β(1/y − 2))`, written through the branch variables. -/
def blindCoreSeed (y : ℝ) : ℝ :=
  (y⁻¹ - 1 + 1) * blindCoreBump (y⁻¹ - 1) + (y⁻¹ - 2 + 2) * blindCoreBump (y⁻¹ - 2)

theorem continuous_blindCoreBump : Continuous blindCoreBump := by
  unfold blindCoreBump
  fun_prop

theorem blindCoreSupported_bump : BlindCoreSupported blindCoreBump := by
  intro t ht
  unfold blindCoreBump
  apply max_eq_left
  rcases ht with ht | ht <;> nlinarith

theorem blindCoreSupported_bump_mul (m : ℝ) :
    BlindCoreSupported fun t => (t + m) * blindCoreBump t := fun t ht => by
  simp only [blindCoreSupported_bump t ht, mul_zero]

theorem continuous_blindCoreSeed : Continuous blindCoreSeed := by
  have c1 := continuous_comp_inv_sub_of_blindCoreSupported
    ((continuous_id.add continuous_const).mul continuous_blindCoreBump)
    (blindCoreSupported_bump_mul 1) (m := 1) (by norm_num)
  have c2 := continuous_comp_inv_sub_of_blindCoreSupported
    ((continuous_id.add continuous_const).mul continuous_blindCoreBump)
    (blindCoreSupported_bump_mul 2) (m := 2) (by norm_num)
  exact c1.add c2

theorem blindCoreSupported_seed : BlindCoreSupported blindCoreSeed := by
  intro y hy
  have h1 := blindCoreSupported_comp_inv_sub (blindCoreSupported_bump_mul 1) (m := 1) le_rfl
    (by norm_num) y hy
  have h2 := blindCoreSupported_comp_inv_sub (blindCoreSupported_bump_mul 2) (m := 2)
    (by norm_num) (by norm_num) y hy
  unfold blindCoreSeed
  simp only at h1 h2
  rw [h1, h2, add_zero]

/-- The seed lies in the kernel of `M` on `[0, 1]`. -/
theorem blindCoreMayer_seed {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    blindCoreMayer blindCoreSeed r = 0 := by
  unfold blindCoreMayer blindCoreSeed
  simp only [inv_inv]
  have e11 : r + 1 - 1 = r := by ring
  have e22 : r + 2 - 2 = r := by ring
  have z12 : blindCoreBump (r + 1 - 2) = 0 := blindCoreSupported_bump _ (Or.inl (by linarith))
  have z21 : blindCoreBump (r + 2 - 1) = 0 := blindCoreSupported_bump _ (Or.inr (by linarith))
  have z31 : blindCoreBump (r + 3 - 1) = 0 := blindCoreSupported_bump _ (Or.inr (by linarith))
  have z32 : blindCoreBump (r + 3 - 2) = 0 := blindCoreSupported_bump _ (Or.inr (by linarith))
  rw [e11, e22, z12, z21, z31, z32]
  have h1' : r + 1 ≠ 0 := by linarith
  have h2' : r + 2 ≠ 0 := by linarith
  field_simp
  ring

theorem blindCoreSeed_two_thirds : blindCoreSeed (2 / 3) = 9 / 80 := by
  unfold blindCoreSeed blindCoreBump
  norm_num [max_def]

theorem exists_abs_blindCoreSeed_le : ∃ B, ∀ y, |blindCoreSeed y| ≤ B := by
  have hcpt : HasCompactSupport blindCoreSeed := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun x hx => ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    apply blindCoreSupported_seed
    rcases hx with hx | hx
    · left; linarith
    · right; linarith
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuous continuous_blindCoreSeed
  exact ⟨C, fun y => by rw [← Real.norm_eq_abs]; exact hC y⟩

/-! ### The eigenfunction -/

/-- The iterates `S^k u₀`. -/
def blindCoreIter (k : ℕ) : ℝ → ℝ := blindCoreLift^[k] blindCoreSeed

theorem blindCoreIter_zero : blindCoreIter 0 = blindCoreSeed := rfl

theorem blindCoreIter_succ (k : ℕ) : blindCoreIter (k + 1) = blindCoreLift (blindCoreIter k) :=
  Function.iterate_succ_apply' _ _ _

theorem blindCoreSupported_iter (k : ℕ) : BlindCoreSupported (blindCoreIter k) := by
  induction k with
  | zero => exact blindCoreSupported_seed
  | succ k ih => rw [blindCoreIter_succ]; exact blindCoreSupported_lift ih

theorem continuous_blindCoreIter (k : ℕ) : Continuous (blindCoreIter k) := by
  induction k with
  | zero => exact continuous_blindCoreSeed
  | succ k ih =>
    rw [blindCoreIter_succ]
    exact continuous_blindCoreLift ih (blindCoreSupported_iter k)

theorem abs_blindCoreIter_le {B : ℝ} (hB : ∀ y, |blindCoreSeed y| ≤ B) (k : ℕ) (y : ℝ) :
    |blindCoreIter k y| ≤ (12 / 13) ^ k * B := by
  induction k generalizing y with
  | zero => rw [blindCoreIter_zero, pow_zero, one_mul]; exact hB y
  | succ k ih =>
    rw [blindCoreIter_succ]
    calc |blindCoreLift (blindCoreIter k) y| ≤ 12 / 13 * ((12 / 13) ^ k * B) :=
          abs_blindCoreLift_le (blindCoreSupported_iter k) ih y
      _ = (12 / 13) ^ (k + 1) * B := by ring

theorem summable_blindCoreIter (y : ℝ) :
    Summable fun k : ℕ => (-1 : ℝ) ^ k * blindCoreIter k y := by
  obtain ⟨B, hB⟩ := exists_abs_blindCoreSeed_le
  have hg := (summable_geometric_of_lt_one (r := 12 / 13) (by norm_num) (by norm_num)).mul_right B
  refine Summable.of_norm_bounded hg fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_blindCoreIter_le hB k y

/-- The eigenfunction `f = Σ_k (−1)^k S^k u₀`. -/
def blindCoreEigen (y : ℝ) : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k * blindCoreIter k y

theorem continuous_blindCoreEigen : Continuous blindCoreEigen := by
  obtain ⟨B, hB⟩ := exists_abs_blindCoreSeed_le
  have hg := (summable_geometric_of_lt_one (r := 12 / 13) (by norm_num) (by norm_num)).mul_right B
  refine continuous_tsum (fun k => continuous_const.mul (continuous_blindCoreIter k)) hg
    fun k y => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_blindCoreIter_le hB k y

theorem blindCoreSupported_eigen : BlindCoreSupported blindCoreEigen := by
  intro t ht
  unfold blindCoreEigen
  simp only [blindCoreSupported_iter _ t ht, mul_zero, tsum_zero]

/-- **The eigen-equation** `M f = −f` on `[0, 1]`. -/
theorem blindCoreMayer_eigen {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    blindCoreMayer blindCoreEigen r = -blindCoreEigen r := by
  have hs := summable_blindCoreIter
  have hT : (fun k : ℕ => (-1 : ℝ) ^ k * blindCoreMayer (blindCoreIter k) r) = fun k =>
      (-1) ^ k * blindCoreIter k (r + 1)⁻¹ / (r + 1) -
        (-1) ^ k * blindCoreIter k (r + 2)⁻¹ / (r + 2) +
        (-1) ^ k * blindCoreIter k (r + 3)⁻¹ / (r + 3) := by
    funext k
    unfold blindCoreMayer
    ring
  have hTs : Summable fun k : ℕ => (-1 : ℝ) ^ k * blindCoreMayer (blindCoreIter k) r := by
    rw [hT]
    exact (((hs _).div_const _).sub ((hs _).div_const _)).add ((hs _).div_const _)
  have lhs : blindCoreMayer blindCoreEigen r =
      ∑' k : ℕ, (-1 : ℝ) ^ k * blindCoreMayer (blindCoreIter k) r := by
    rw [hT, Summable.tsum_add (((hs _).div_const _).sub ((hs _).div_const _))
      ((hs _).div_const _), Summable.tsum_sub ((hs _).div_const _) ((hs _).div_const _),
      tsum_div_const, tsum_div_const, tsum_div_const]
    rfl
  have hstep : ∀ k : ℕ, (-1 : ℝ) ^ (k + 1) * blindCoreMayer (blindCoreIter (k + 1)) r =
      -((-1 : ℝ) ^ k * blindCoreIter k r) := by
    intro k
    rw [blindCoreIter_succ, blindCoreMayer_lift (blindCoreSupported_iter k) h0 h1, pow_succ]
    ring
  rw [lhs, hTs.tsum_eq_zero_add]
  simp only [hstep, pow_zero, one_mul, blindCoreIter_zero, blindCoreMayer_seed h0 h1, zero_add,
    tsum_neg]
  rfl

/-- `f + S f = u₀`. -/
theorem blindCoreEigen_add_lift (y : ℝ) :
    blindCoreEigen y + blindCoreLift blindCoreEigen y = blindCoreSeed y := by
  have hs := summable_blindCoreIter
  have hT : (fun k : ℕ => (-1 : ℝ) ^ k * blindCoreIter (k + 1) y) = fun k =>
      (-1) ^ k * blindCoreIter k (y⁻¹ - 1) / blindCoreWeight (y⁻¹ - 1) -
        (-1) ^ k * blindCoreIter k (y⁻¹ - 2) / blindCoreWeight (y⁻¹ - 2) +
        (-1) ^ k * blindCoreIter k (y⁻¹ - 3) / blindCoreWeight (y⁻¹ - 3) := by
    funext k
    rw [blindCoreIter_succ]
    unfold blindCoreLift
    ring
  have hL : blindCoreLift blindCoreEigen y =
      ∑' k : ℕ, (-1 : ℝ) ^ k * blindCoreIter (k + 1) y := by
    rw [hT, Summable.tsum_add (((hs _).div_const _).sub ((hs _).div_const _))
      ((hs _).div_const _), Summable.tsum_sub ((hs _).div_const _) ((hs _).div_const _),
      tsum_div_const, tsum_div_const, tsum_div_const]
    rfl
  have hE : blindCoreEigen y = blindCoreSeed y -
      ∑' k : ℕ, (-1 : ℝ) ^ k * blindCoreIter (k + 1) y := by
    unfold blindCoreEigen
    rw [(hs y).tsum_eq_zero_add]
    have h : ∀ k : ℕ, (-1 : ℝ) ^ (k + 1) * blindCoreIter (k + 1) y =
        -((-1) ^ k * blindCoreIter (k + 1) y) := fun k => by ring
    simp only [h, tsum_neg, pow_zero, one_mul, blindCoreIter_zero]
    ring
  rw [hL, hE]
  ring

theorem exists_blindCoreEigen_ne_zero : ∃ t, blindCoreEigen t ≠ 0 := by
  by_contra h
  push Not at h
  have hS : blindCoreLift blindCoreEigen (2 / 3) = 0 := by
    unfold blindCoreLift
    simp [h]
  have := blindCoreEigen_add_lift (2 / 3)
  rw [h, hS, add_zero, blindCoreSeed_two_thirds] at this
  norm_num at this

/-- **The twisted Mayer operator at `s = ½` has a continuous `−1`-eigenfunction supported in
`[1/4, 4/5]`.** -/
theorem exists_blindCoreMayer_eigen :
    ∃ f : ℝ → ℝ, Continuous f ∧ BlindCoreSupported f ∧
      (∀ r, 0 ≤ r → r ≤ 1 → blindCoreMayer f r = -f r) ∧ ∃ t, f t ≠ 0 :=
  ⟨blindCoreEigen, continuous_blindCoreEigen, blindCoreSupported_eigen,
    fun _ h0 h1 => blindCoreMayer_eigen h0 h1, exists_blindCoreEigen_ne_zero⟩

/-! ### The Fourier-blind core -/

/-- The profile `Γ(x) = f(1 − x) − f((1−x)/x)/x − f((1−x)/(2−x))/(2−x)`. -/
def blindCoreProfile (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (1 - x) - f ((1 - x) / x) / x - f ((1 - x) / (2 - x)) / (2 - x)

/-- A cutoff equal to `1` on `[5/9, 4/5]` and to `0` outside `(1/2, 1)`. -/
def blindCoreCutoff (x : ℝ) : ℝ := max 0 (min 1 (min (18 * (x - 1 / 2)) (5 * (1 - x))))

def blindCoreHalf (f : ℝ → ℝ) (x : ℝ) : ℝ := blindCoreCutoff x * blindCoreProfile f x

/-- The core `G(x) = Γ(|x|) + Γ(1/|x|)/|x|`. -/
def blindCoreFn (f : ℝ → ℝ) (x : ℝ) : ℝ := blindCoreHalf f |x| + blindCoreHalf f |x|⁻¹ * |x|⁻¹

theorem blindCoreCutoff_of_le_half {x : ℝ} (hx : x ≤ 1 / 2) : blindCoreCutoff x = 0 := by
  unfold blindCoreCutoff
  apply max_eq_left
  exact (min_le_right _ _).trans ((min_le_left _ _).trans (by linarith))

theorem blindCoreCutoff_of_one_le {x : ℝ} (hx : 1 ≤ x) : blindCoreCutoff x = 0 := by
  unfold blindCoreCutoff
  apply max_eq_left
  exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))

theorem blindCoreCutoff_of_mem {x : ℝ} (h1 : 5 / 9 ≤ x) (h2 : x ≤ 4 / 5) :
    blindCoreCutoff x = 1 := by
  unfold blindCoreCutoff
  rw [min_eq_left (le_min (by linarith) (by linarith)), max_eq_right zero_le_one]

theorem continuous_blindCoreCutoff : Continuous blindCoreCutoff := by
  unfold blindCoreCutoff
  fun_prop

section Core

variable {f : ℝ → ℝ} (hf : Continuous f) (hs : BlindCoreSupported f)
  (heig : ∀ r, 0 ≤ r → r ≤ 1 → blindCoreMayer f r = -f r)

/-- `Γ(x) = −M f(r)/(1 − x)` with `r = (2x − 1)/(1 − x)`. -/
theorem blindCoreProfile_eq {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    blindCoreProfile f x = -blindCoreMayer f ((2 * x - 1) / (1 - x)) / (1 - x) := by
  have hx0 : x ≠ 0 := h0.ne'
  have hx1 : 1 - x ≠ 0 := by linarith
  have hx2 : 2 - x ≠ 0 := by linarith
  have a1 : ((2 * x - 1) / (1 - x) + 1)⁻¹ = (1 - x) / x := by
    rw [inv_eq_iff_eq_inv, inv_div]; field_simp; ring
  have a2 : ((2 * x - 1) / (1 - x) + 2)⁻¹ = 1 - x := by
    rw [inv_eq_iff_eq_inv]; field_simp; ring
  have a3 : ((2 * x - 1) / (1 - x) + 3)⁻¹ = (1 - x) / (2 - x) := by
    rw [inv_eq_iff_eq_inv, inv_div]; field_simp; ring
  have a1' : (2 * x - 1) / (1 - x) + 1 = x / (1 - x) := by field_simp; ring
  have a2' : (2 * x - 1) / (1 - x) + 2 = 1 / (1 - x) := by field_simp; ring
  have a3' : (2 * x - 1) / (1 - x) + 3 = (2 - x) / (1 - x) := by field_simp; ring
  unfold blindCoreProfile blindCoreMayer
  rw [a1, a2, a3, a1', a2', a3']
  set A := f (1 - x)
  set B := f ((1 - x) / x)
  set C := f ((1 - x) / (2 - x))
  field_simp
  ring

include heig hs in
theorem blindCoreProfile_eq_zero_of_le {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 5 / 9) :
    blindCoreProfile f x = 0 := by
  have h1x : 0 < 1 - x := by linarith
  rw [blindCoreProfile_eq (by linarith) (by linarith)]
  have hr0 : 0 ≤ (2 * x - 1) / (1 - x) := div_nonneg (by linarith) h1x.le
  have hr : (2 * x - 1) / (1 - x) ≤ 1 / 4 := by
    rw [div_le_iff₀ h1x]; linarith
  rw [heig _ hr0 (by linarith), hs _ (Or.inl hr)]
  simp

include hs in
theorem blindCoreProfile_eq_zero_of_ge {x : ℝ} (h1 : 4 / 5 ≤ x) (h2 : x ≤ 1) :
    blindCoreProfile f x = 0 := by
  have hx0 : 0 < x := by linarith
  unfold blindCoreProfile
  rw [hs (1 - x) (Or.inl (by linarith)),
    hs ((1 - x) / x) (Or.inl (by rw [div_le_iff₀ hx0]; linarith)),
    hs ((1 - x) / (2 - x)) (Or.inl (by rw [div_le_iff₀ (by linarith)]; linarith))]
  simp

include heig hs in
theorem blindCoreHalf_eq_profile {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 1) :
    blindCoreHalf f x = blindCoreProfile f x := by
  unfold blindCoreHalf
  rcases le_or_gt x (5 / 9) with h | h
  · rw [blindCoreProfile_eq_zero_of_le hs heig h1 h, mul_zero]
  rcases le_or_gt (4 / 5) x with h' | h'
  · rw [blindCoreProfile_eq_zero_of_ge hs h' h2, mul_zero]
  rw [blindCoreCutoff_of_mem h.le h'.le, one_mul]

theorem blindCoreHalf_of_le_half {x : ℝ} (hx : x ≤ 1 / 2) : blindCoreHalf f x = 0 := by
  unfold blindCoreHalf; rw [blindCoreCutoff_of_le_half hx, zero_mul]

theorem blindCoreHalf_of_one_le {x : ℝ} (hx : 1 ≤ x) : blindCoreHalf f x = 0 := by
  unfold blindCoreHalf; rw [blindCoreCutoff_of_one_le hx, zero_mul]

include heig hs in
theorem blindCoreHalf_of_lt {x : ℝ} (hx : x < 5 / 9) : blindCoreHalf f x = 0 := by
  rcases le_or_gt x (1 / 2) with h | h
  · exact blindCoreHalf_of_le_half h
  · rw [blindCoreHalf_eq_profile hs heig h.le (by linarith),
      blindCoreProfile_eq_zero_of_le hs heig h.le hx.le]

include hf in
theorem continuous_blindCoreHalf : Continuous (blindCoreHalf f) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_or_ge x (1 / 2) with hx | hx
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x] blindCoreHalf f := by
      filter_upwards [Iio_mem_nhds hx] with z hz
      exact (blindCoreHalf_of_le_half hz.le).symm
    exact continuousAt_const.congr hev
  rcases lt_or_ge 1 x with hx' | hx'
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x] blindCoreHalf f := by
      filter_upwards [Ioi_mem_nhds hx'] with z hz
      exact (blindCoreHalf_of_one_le (le_of_lt hz)).symm
    exact continuousAt_const.congr hev
  have hx0 : x ≠ 0 := by intro h; linarith
  have hx2 : 2 - x ≠ 0 := by intro h; linarith
  unfold blindCoreHalf blindCoreProfile
  have hc : Continuous blindCoreCutoff := continuous_blindCoreCutoff
  fun_prop (disch := assumption)

/-- `G` vanishes for `|x| ≥ 2`. -/
theorem blindCoreFn_of_two_le {x : ℝ} (hx : 2 ≤ |x|) : blindCoreFn f x = 0 := by
  unfold blindCoreFn
  have hpos : 0 < |x| := by linarith
  rw [blindCoreHalf_of_one_le (by linarith),
    blindCoreHalf_of_le_half (by rw [inv_le_comm₀ hpos (by norm_num)]; norm_num; linarith)]
  ring

theorem blindCoreFn_neg (x : ℝ) : blindCoreFn f (-x) = blindCoreFn f x := by
  unfold blindCoreFn; rw [abs_neg]

theorem blindCoreFn_inv {x : ℝ} (hx : 0 < x) : blindCoreFn f x⁻¹ = x * blindCoreFn f x := by
  unfold blindCoreFn
  rw [abs_of_pos (inv_pos.mpr hx), abs_of_pos hx, inv_inv]
  field_simp
  ring

include hf in
theorem continuous_blindCoreFn : Continuous (blindCoreFn f) := by
  have hH := continuous_blindCoreHalf hf
  have c1 : Continuous fun x => blindCoreHalf f |x| := hH.comp continuous_abs
  have c2 : Continuous fun x => blindCoreHalf f |x|⁻¹ * |x|⁻¹ := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · subst hx
      have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 0] fun x => blindCoreHalf f |x|⁻¹ * |x|⁻¹ := by
        filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
          (show (0 : ℝ) < 1 by norm_num)] with z hz
        by_cases hz0 : z = 0
        · subst hz0; simp
        · have hpos : 0 < |z| := abs_pos.mpr hz0
          have hlt : |z| < 1 := abs_lt.mpr ⟨hz.1, hz.2⟩
          rw [blindCoreHalf_of_one_le (by rw [le_inv_comm₀ one_pos hpos]; simp; exact hlt.le)]
          ring
      exact continuousAt_const.congr hev
    · have ha : ContinuousAt (fun x : ℝ => |x|⁻¹) x :=
        continuous_abs.continuousAt.inv₀ (abs_ne_zero.mpr hx)
      exact (hH.continuousAt.comp ha).mul ha
  exact c1.add c2

include heig hs in
theorem blindCoreFn_of_lt {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 5 / 9) : blindCoreFn f x = 0 := by
  unfold blindCoreFn
  rw [abs_of_nonneg h0, blindCoreHalf_of_lt hs heig h1]
  rcases eq_or_lt_of_le h0 with h | h
  · subst h; simp
  · rw [blindCoreHalf_of_one_le (by rw [le_inv_comm₀ one_pos h]; simp; linarith)]
    ring

include heig hs in
/-- **The three-term identity** on `[½, 1]`, from the eigen-equation at `(1 − x)/x`. -/
theorem blindCoreProfile_three_term {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 1) :
    blindCoreProfile f x + blindCoreProfile f (1 + x)⁻¹ * (1 + x)⁻¹ +
      blindCoreProfile f (2 - x)⁻¹ * (2 - x)⁻¹ = 0 := by
  have hx0 : 0 < x := by linarith
  have hx0' : x ≠ 0 := hx0.ne'
  have hp1 : 1 + x ≠ 0 := by linarith
  have hp2 : 2 - x ≠ 0 := by linarith
  have hp3 : 1 + 2 * x ≠ 0 := by linarith
  have hp4 : 3 - 2 * x ≠ 0 := by linarith
  have hp3' : 1 + x * 2 ≠ 0 := by linarith
  have hp4' : 3 - x * 2 ≠ 0 := by linarith
  have hp5 : x * 2 + 1 ≠ 0 := by linarith
  have hp6 : 2 * x + 1 ≠ 0 := by linarith
  have b1 : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  have b4 : 2 - (1 + x)⁻¹ = (1 + 2 * x) / (1 + x) := by field_simp; ring
  have c1 : 1 - (2 - x)⁻¹ = (1 - x) / (2 - x) := by field_simp; ring
  have c4 : 2 - (2 - x)⁻¹ = (3 - 2 * x) / (2 - x) := by field_simp; ring
  have b2 : (1 - (1 + x)⁻¹) / (1 + x)⁻¹ = x := by
    rw [b1, div_inv_eq_mul, div_mul_cancel₀ _ hp1]
  have b3 : (1 - (1 + x)⁻¹) / (2 - (1 + x)⁻¹) = x / (1 + 2 * x) := by
    rw [b1, b4, div_div_div_cancel_right₀ hp1]
  have c2 : (1 - (2 - x)⁻¹) / (2 - x)⁻¹ = 1 - x := by
    rw [c1, div_inv_eq_mul, div_mul_cancel₀ _ hp2]
  have c3 : (1 - (2 - x)⁻¹) / (2 - (2 - x)⁻¹) = (1 - x) / (3 - 2 * x) := by
    rw [c1, c4, div_div_div_cancel_right₀ hp2]
  have hs0 : 0 ≤ (1 - x) / x := div_nonneg (by linarith) hx0.le
  have hs1 : (1 - x) / x ≤ 1 := by rw [div_le_iff₀ hx0]; linarith
  have eig := heig _ hs0 hs1
  unfold blindCoreMayer at eig
  have d1 : ((1 - x) / x + 1)⁻¹ = x := by rw [inv_eq_iff_eq_inv]; field_simp; ring
  have d2 : ((1 - x) / x + 2)⁻¹ = x / (1 + x) := by
    rw [inv_eq_iff_eq_inv, inv_div]; field_simp; ring
  have d3 : ((1 - x) / x + 3)⁻¹ = x / (1 + 2 * x) := by
    rw [inv_eq_iff_eq_inv, inv_div]; field_simp; ring
  rw [d1, d2, d3] at eig
  have hK : f ((1 - x) / (3 - 2 * x)) = 0 :=
    hs _ (Or.inl (by rw [div_le_iff₀ (by linarith)]; linarith))
  unfold blindCoreProfile
  rw [b2, b3, b1, b4, c2, c3, c1, c4, hK]
  have e1 : (1 - x) / x + 1 = x⁻¹ := by field_simp; ring
  have e2 : (1 - x) / x + 2 = (1 + x) / x := by field_simp; ring
  have e3 : (1 - x) / x + 3 = (1 + 2 * x) / x := by field_simp; ring
  rw [e1, e2, e3, div_inv_eq_mul, div_div_eq_mul_div, div_div_eq_mul_div] at eig
  set A := f x
  set B := f (x / (1 + x))
  set C := f (x / (1 + 2 * x))
  set D := f (1 - x)
  set E := f ((1 - x) / x)
  set F := f ((1 - x) / (2 - x))
  have h1' : B * x / (1 + x) * (1 + x) = B * x := div_mul_cancel₀ _ hp1
  have h2' : C * x / (1 + 2 * x) * (1 + 2 * x) = C * x := div_mul_cancel₀ _ hp3
  have eigp : A * x * ((1 + x) * (1 + 2 * x)) - B * x * (1 + 2 * x) + C * x * (1 + x) +
      E * ((1 + x) * (1 + 2 * x)) = 0 := by
    linear_combination ((1 + x) * (1 + 2 * x)) * eig + (1 + 2 * x) * h1' - (1 + x) * h2'
  field_simp
  linear_combination (-(3 - 2 * x) * (2 - x)) * eigp

include heig hs in
/-- **The four-term periodization vanishes** on `[½, 1]`. -/
theorem blindCoreFn_four_term {z : ℝ} (h1 : 1 / 2 ≤ z) (h2 : z ≤ 1) :
    blindCoreFn f z + blindCoreFn f (1 - z) + blindCoreFn f (1 + z) + blindCoreFn f (2 - z) =
      0 := by
  have hz0 : 0 < z := by linarith
  unfold blindCoreFn
  rw [abs_of_pos hz0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - z),
    abs_of_pos (by linarith : (0 : ℝ) < 1 + z), abs_of_pos (by linarith : (0 : ℝ) < 2 - z)]
  have v1 : blindCoreHalf f z⁻¹ = 0 :=
    blindCoreHalf_of_one_le (by rw [le_inv_comm₀ one_pos hz0]; simp; linarith)
  have v2 : blindCoreHalf f (1 - z) = 0 := blindCoreHalf_of_le_half (by linarith)
  have v3 : blindCoreHalf f (1 - z)⁻¹ = 0 := by
    rcases eq_or_lt_of_le h2 with h | h
    · rw [h, sub_self, inv_zero]; exact blindCoreHalf_of_le_half (by norm_num)
    · exact blindCoreHalf_of_one_le
        (by rw [le_inv_comm₀ one_pos (by linarith)]; simp; linarith)
  have v4 : blindCoreHalf f (1 + z) = 0 := blindCoreHalf_of_one_le (by linarith)
  have v5 : blindCoreHalf f (2 - z) = 0 := blindCoreHalf_of_one_le (by linarith)
  have w1 : 1 / 2 ≤ (1 + z)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (by linarith)]; norm_num; linarith
  have w2 : (1 + z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have w3 : 1 / 2 ≤ (2 - z)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (by linarith)]; norm_num; linarith
  have w4 : (2 - z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  rw [v1, v2, v3, v4, v5, blindCoreHalf_eq_profile hs heig h1 h2,
    blindCoreHalf_eq_profile hs heig w1 w2, blindCoreHalf_eq_profile hs heig w3 w4]
  have := blindCoreProfile_three_term hs heig h1 h2
  linear_combination this

include heig hs in
/-- **The periodization of `G` vanishes identically.** -/
theorem tsum_blindCoreFn_add_int (x : ℝ) : ∑' k : ℤ, blindCoreFn f (x + k) = 0 := by
  have hshift : ∑' k : ℤ, blindCoreFn f (x + k) =
      ∑' k : ℤ, blindCoreFn f (Int.fract x + k) := by
    have h := (Equiv.addRight ⌊x⌋).tsum_eq (fun k : ℤ => blindCoreFn f (Int.fract x + k))
    rw [← h]
    congr 1
    funext k
    simp only [Equiv.coe_addRight]
    congr 1
    push_cast
    linarith [Int.floor_add_fract x]
  rw [hshift]
  have hy0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hy1 : Int.fract x < 1 := Int.fract_lt_one x
  set y := Int.fract x
  rw [tsum_eq_sum (s := {0, -1, 1, -2}) fun k hk => ?_]
  · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    push_cast
    have e1 : blindCoreFn f (y + -1) = blindCoreFn f (1 - y) := by
      rw [← blindCoreFn_neg]; congr 1; ring
    have e2 : blindCoreFn f (y + -2) = blindCoreFn f (2 - y) := by
      rw [← blindCoreFn_neg]; congr 1; ring
    have e3 : blindCoreFn f (y + 1) = blindCoreFn f (1 + y) := by rw [add_comm]
    rw [add_zero, e1, e2, e3]
    rcases le_or_gt (1 / 2) y with h | h
    · have := blindCoreFn_four_term hs heig h hy1.le
      linear_combination this
    · have := blindCoreFn_four_term hs heig (z := 1 - y) (by linarith) (by linarith)
      rw [show 1 - (1 - y) = y by ring, show 1 + (1 - y) = 2 - y by ring,
        show 2 - (1 - y) = 1 + y by ring] at this
      linear_combination this
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    apply blindCoreFn_of_two_le
    rcases le_or_gt 2 k with hk2 | hk2
    · have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hk3 : k ≤ -3 := by omega
      have : (k : ℝ) ≤ -3 := by exact_mod_cast hk3
      rw [abs_of_neg (by linarith)]
      linarith

end Core

/-! ### Fourier blindness from a vanishing periodization -/

/-- If the `1`-periodization of a continuous compactly supported real `G` vanishes, then
`Ĝ(n) = 0` for every integer `n`: the Fourier coefficients of the periodization are the values
`Ĝ(n)` (`Real.fourierCoeff_tsum_comp_add`). -/
theorem fourier_eq_zero_of_tsum_add_int_eq_zero {G : ℝ → ℝ} (hG : Continuous G)
    (hcpt : HasCompactSupport G) (hP : ∀ x, ∑' k : ℤ, G (x + k) = 0) (n : ℤ) :
    𝓕 (fun x => (G x : ℂ)) n = 0 := by
  set ρ : C(ℝ, ℂ) := ⟨fun x => (G x : ℂ), Complex.continuous_ofReal.comp hG⟩ with hρ
  obtain ⟨B, hB⟩ : ∃ B, ∀ y, G y ≠ 0 → |y| ≤ B := by
    obtain ⟨B, hB⟩ := hcpt.isCompact.isBounded.subset_closedBall 0
    refine ⟨B, fun y hy => ?_⟩
    have := hB (subset_tsupport _ hy)
    rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  have h_norm : ∀ K : TopologicalSpace.Compacts ℝ,
      Summable fun n : ℤ => ‖(ρ.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ := by
    intro K
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
    obtain ⟨N, hN⟩ := exists_int_gt (R + B)
    refine summable_of_ne_finset_zero (s := Finset.Icc (-N) N) fun n hn => ?_
    rw [norm_eq_zero]
    ext ⟨y, hy⟩
    have hyR : |y| ≤ R := by
      have := hR hy
      rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    have hn' : (N : ℝ) < |(n : ℝ)| := by
      rw [Finset.mem_Icc] at hn
      have : N < |n| := by rw [lt_abs]; omega
      exact_mod_cast this
    have hbig : B < |y + n| := by
      have h3 := abs_add_le (y + n) (-y)
      have e1 : y + n + -y = (n : ℝ) := by ring
      rw [e1, abs_neg] at h3
      linarith
    simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_addRight, ContinuousMap.zero_apply, hρ, ContinuousMap.coe_mk]
    by_contra hne
    have hne' : G (y + n) ≠ 0 := fun h => hne (by rw [h, Complex.ofReal_zero])
    linarith [hB _ hne']
  have h_norm' : ∀ K : TopologicalSpace.Compacts ℝ,
      Summable fun n : ℤ => ‖(ρ.comp (ContinuousMap.addRight (n • (1 : ℝ)))).restrict K‖ := by
    simpa only [zsmul_one] using h_norm
  have hsum := ContinuousMap.summable_of_locally_summable_norm h_norm'
  have hzero : ∀ x : ℝ, (∑' k : ℤ, ρ.comp (ContinuousMap.addRight (k • (1 : ℝ)))) x = 0 := by
    intro x
    rw [← ContinuousMap.tsum_apply hsum]
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight, zsmul_one, hρ,
      ContinuousMap.coe_mk]
    rw [← Complex.ofReal_tsum, hP x, Complex.ofReal_zero]
  have hlift : Function.Periodic.lift (ρ.periodic_tsum_comp_add_zsmul 1) = fun _ => (0 : ℂ) := by
    funext t
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
    exact (Function.Periodic.lift_coe _ x).trans (hzero x)
  have h := Real.fourierCoeff_tsum_comp_add h_norm n
  calc 𝓕 (fun x => (G x : ℂ)) n = 𝓕 (ρ : ℝ → ℂ) n := rfl
    _ = _ := h.symm
    _ = 0 := by rw [hlift]; simp [fourierCoeff]

/-! ### The theorem -/

/-- **A continuous inversion-symmetric Fourier-blind core of support ratio `9/5`.**  There is a
nonzero continuous even `G` with `G(1/x) = x G(x)` for `x > 0`, vanishing on `[0, 5/9)`, whose
Fourier transform vanishes at every integer. -/
theorem exists_inversionSymmetric_fourierBlind_nine_fifths :
    ∃ G : ℝ → ℝ, Continuous G ∧ (∀ x, G (-x) = G x) ∧ (∀ x, 0 < x → G x⁻¹ = x * G x) ∧
      (∀ x, 0 ≤ x → x < 5 / 9 → G x = 0) ∧ (∀ n : ℤ, 𝓕 (fun x => (G x : ℂ)) n = 0) ∧
      ∃ y, G y ≠ 0 := by
  obtain ⟨f, hf, hs, heig, t, ht⟩ := exists_blindCoreMayer_eigen
  have hcpt : HasCompactSupport (blindCoreFn f) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun x hx => ?_
    apply blindCoreFn_of_two_le
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  refine ⟨blindCoreFn f, continuous_blindCoreFn hf, blindCoreFn_neg,
    fun x hx => blindCoreFn_inv hx, fun x h0 h1 => blindCoreFn_of_lt hs heig h0 h1,
    fun n => fourier_eq_zero_of_tsum_add_int_eq_zero (continuous_blindCoreFn hf) hcpt
      (tsum_blindCoreFn_add_int hs heig) n, ?_⟩
  have ht1 : 1 / 4 < t := by
    by_contra h
    exact ht (hs t (Or.inl (not_lt.mp h)))
  have ht2 : t < 4 / 5 := by
    by_contra h
    exact ht (hs t (Or.inr (not_lt.mp h)))
  have h2t : (2 + t) ≠ 0 := by linarith
  set xs := (1 + t) / (2 + t) with hxs
  have hx0 : 0 < xs := div_pos (by linarith) (by linarith)
  have hx1 : xs < 1 := by rw [hxs, div_lt_one (by linarith)]; linarith
  have hlo : 5 / 9 ≤ xs := by rw [hxs, le_div_iff₀ (by linarith)]; linarith
  have hhi : xs ≤ 4 / 5 := by rw [hxs, div_le_iff₀ (by linarith)]; linarith
  have hn : 2 * xs - 1 = t / (2 + t) := by rw [hxs]; field_simp; ring
  have hd : 1 - xs = 1 / (2 + t) := by rw [hxs]; field_simp; ring
  have hr : (2 * xs - 1) / (1 - xs) = t := by
    rw [hn, hd, div_div_div_cancel_right₀ h2t, div_one]
  have hv : blindCoreHalf f xs⁻¹ = 0 :=
    blindCoreHalf_of_one_le (by rw [le_inv_comm₀ one_pos hx0]; simp; exact hx1.le)
  refine ⟨xs, ?_⟩
  unfold blindCoreFn
  rw [abs_of_pos hx0, hv, zero_mul, add_zero]
  unfold blindCoreHalf
  rw [blindCoreCutoff_of_mem hlo hhi, one_mul, blindCoreProfile_eq hx0 hx1, hr,
    heig t (by linarith) (by linarith), neg_neg]
  exact div_ne_zero ht (by linarith)

end

end RHTower
