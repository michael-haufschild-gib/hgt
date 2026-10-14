import GaloisForLFunctions.RHTower.InversionSymmetricFourierBlindContinuousCore

/-!
# A continuous inversion-symmetric Fourier-blind core of support ratio `97/56 ≈ √3`

A continuous even `G` with `G(1/x) = x G(x)` for `x > 0`, vanishing on `[0, c)` and with
`Ĝ(n) = 0` for every integer `|n| ≥ 2`, vanishes when `12c > 7`
(`eq_zero_of_inversionSymmetric_fourierBlind_of_twelve_sevenths`).

**Theorem** (`exists_inversionSymmetric_fourierBlind_ninety_seven_fifty_sixths`).  There is a
nonzero continuous even `G` with `G(1/x) = x G(x)` for `x > 0`, vanishing on `[0, 56/97)`, and
with `Ĝ(n) = 0` for every integer `n`.  Hence the support-ratio threshold for continuous
Fourier-blind cores lies in `[12/7, 97/56] ≈ [1.7143, 1.7321]`.

**Construction.**  As in `exists_inversionSymmetric_fourierBlind_nine_fifths`, the core is
`blindCoreFn f` for a continuous `f` with `M f = −f` on `[0, 1]`, where `M` is the twisted
Gauss–Mayer operator at `s = ½` (`blindCoreMayer`).  Here `f` lives on
`U = (15/41, 11/26) ∪ (15/26, 11/15)`, which is mapped into itself by the first two Gauss
branches `r ↦ 1/(r + 1)`, `r ↦ 1/(r + 2)`.  Its closure contains the attractor of these two branches
(continued fractions with digits in `{1, 2}`, extreme points `(√3 − 1)/2` and `√3 − 1`, Hausdorff
dimension `≈ 0.531 > ½`).

The lift splits the value `u(r)` between the two branches in the proportion of a two-level gauge
`w = 7/6` on `(0, ½)`, `w = 1` on `[½, 1)`:
`S u(1/(r+1)) = u(r)/D(r)`, `S u(1/(r+2)) = −(7/6) u(r)/D(r)`,
`D(r) = 1/(r+1) + (7/6)/(r+2)` (`sqrtThreeCoreLift`).  Then `M S u = u` on `[0, 1]`, and
`|S u| ≤ (533/535) ‖u/w‖_∞ w` (`abs_sqrtThreeCoreLift_le`): on the upper interval
`D ≥ D(11/15) = 535/533`, on the lower one `D ≥ D(11/26) = 1183/999 > (7/6)(535/533)`.  A single
branch weight `1/(r+1) + 1/(r+2)` drops below `1` near `√3 − 1`, so a gauge is needed.  The gauge
makes the positive two-branch transfer operator at `s = ½` exceed `1` on `U`, which is the
quantitative form of `dim > ½`.

The series `f = Σ_k (−1)^k S^k u₀`, with `M u₀ = 0`, gives `M f = −f` and `f + S f = u₀ ≠ 0`.
Since `f = 0` on `[0, 15/41]`, the core vanishes for `(2x − 1)/(1 − x) < 15/41`, i.e. `x < 56/97`.
-/

open MeasureTheory Set Real Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

/-! ### The invariant set, the gauge and the weight -/

/-- Membership in `U = (15/41, 11/26) ∪ (15/26, 11/15)`. -/
def SqrtThreeCoreMem (t : ℝ) : Prop := (15 / 41 < t ∧ t < 11 / 26) ∨ (15 / 26 < t ∧ t < 11 / 15)

/-- Vanishing outside `U`. -/
def SqrtThreeCoreSupported (u : ℝ → ℝ) : Prop := ∀ t, ¬SqrtThreeCoreMem t → u t = 0

theorem SqrtThreeCoreSupported.blindCoreSupported {u : ℝ → ℝ} (hs : SqrtThreeCoreSupported u) :
    BlindCoreSupported u := by
  intro t ht
  apply hs
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> rcases ht with ht | ht <;> linarith

theorem SqrtThreeCoreSupported.eq_zero_of_le {u : ℝ → ℝ} (hs : SqrtThreeCoreSupported u) {t : ℝ}
    (ht : t ≤ 15 / 41) : u t = 0 :=
  hs t (by rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith)

theorem SqrtThreeCoreSupported.eq_zero_of_ge {u : ℝ → ℝ} (hs : SqrtThreeCoreSupported u) {t : ℝ}
    (ht : 11 / 15 ≤ t) : u t = 0 :=
  hs t (by rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith)

/-- The gauge: `7/6` below `½`, `1` from `½` on. -/
def sqrtThreeCoreGauge (t : ℝ) : ℝ := if t < 1 / 2 then 7 / 6 else 1

theorem one_le_sqrtThreeCoreGauge (t : ℝ) : 1 ≤ sqrtThreeCoreGauge t := by
  unfold sqrtThreeCoreGauge; split_ifs <;> norm_num

theorem sqrtThreeCoreGauge_le (t : ℝ) : sqrtThreeCoreGauge t ≤ 7 / 6 := by
  unfold sqrtThreeCoreGauge; split_ifs <;> norm_num

/-- `D(r) = 1/(r + 1) + (7/6)/(r + 2)`. -/
def sqrtThreeCoreWeight (r : ℝ) : ℝ := (r + 1)⁻¹ + 7 / 6 * (r + 2)⁻¹

theorem sqrtThreeCoreWeight_pos {r : ℝ} (hr : 0 ≤ r) : 0 < sqrtThreeCoreWeight r := by
  unfold sqrtThreeCoreWeight
  have h1 : 0 < (r + 1)⁻¹ := inv_pos.mpr (by linarith)
  have h2 : 0 < (r + 2)⁻¹ := inv_pos.mpr (by linarith)
  linarith

theorem sqrtThreeCoreWeight_anti {r q : ℝ} (hr : 0 ≤ r) (hrq : r ≤ q) :
    sqrtThreeCoreWeight q ≤ sqrtThreeCoreWeight r := by
  unfold sqrtThreeCoreWeight
  have h1 : (q + 1)⁻¹ ≤ (r + 1)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have h2 : (q + 2)⁻¹ ≤ (r + 2)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  linarith

/-- The lift splitting `u(r)` between the first two branches. -/
def sqrtThreeCoreLift (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  u (y⁻¹ - 1) / sqrtThreeCoreWeight (y⁻¹ - 1) -
    7 / 6 * (u (y⁻¹ - 2) / sqrtThreeCoreWeight (y⁻¹ - 2))

/-- If `1/y − m ∈ (p, q)` with `m + p > 0`, then `y ∈ (1/(m + q), 1/(m + p))`. -/
theorem mem_of_inv_sub_mem {y m p q : ℝ} (hp : 0 < m + p) (h1 : p < y⁻¹ - m)
    (h2 : y⁻¹ - m < q) : (m + q)⁻¹ < y ∧ y < (m + p)⁻¹ := by
  have hy : 0 < y⁻¹ := by linarith
  have hy0 : 0 < y := inv_pos.mp hy
  constructor
  · rw [inv_lt_comm₀ (by linarith) hy0]; linarith
  · rw [lt_inv_comm₀ hy0 hp]; linarith

/-- The first branch maps `U` into its upper interval. -/
theorem upper_of_inv_sub_one_mem {y : ℝ} (h : SqrtThreeCoreMem (y⁻¹ - 1)) :
    15 / 26 < y ∧ y < 11 / 15 := by
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · obtain ⟨b1, b2⟩ := mem_of_inv_sub_mem (by norm_num) a1 a2
    norm_num at b1 b2
    constructor <;> linarith
  · obtain ⟨b1, b2⟩ := mem_of_inv_sub_mem (by norm_num) a1 a2
    norm_num at b1 b2
    constructor <;> linarith

/-- The second branch maps `U` into its lower interval. -/
theorem lower_of_inv_sub_two_mem {y : ℝ} (h : SqrtThreeCoreMem (y⁻¹ - 2)) :
    15 / 41 < y ∧ y < 11 / 26 := by
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · obtain ⟨b1, b2⟩ := mem_of_inv_sub_mem (by norm_num) a1 a2
    norm_num at b1 b2
    constructor <;> linarith
  · obtain ⟨b1, b2⟩ := mem_of_inv_sub_mem (by norm_num) a1 a2
    norm_num at b1 b2
    constructor <;> linarith

/-! ### The lift -/

theorem sqrtThreeCoreSupported_lift {u : ℝ → ℝ} (hs : SqrtThreeCoreSupported u) :
    SqrtThreeCoreSupported (sqrtThreeCoreLift u) := by
  intro y hy
  have h1 : u (y⁻¹ - 1) = 0 := hs _ fun h => hy (Or.inr (upper_of_inv_sub_one_mem h))
  have h2 : u (y⁻¹ - 2) = 0 := hs _ fun h => hy (Or.inl (lower_of_inv_sub_two_mem h))
  unfold sqrtThreeCoreLift
  rw [h1, h2]
  simp

theorem continuous_div_sqrtThreeCoreWeight {u : ℝ → ℝ} (hu : Continuous u)
    (hs : BlindCoreSupported u) : Continuous fun t => u t / sqrtThreeCoreWeight t := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_or_ge t (1 / 4) with ht | ht
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 t] fun t => u t / sqrtThreeCoreWeight t := by
      filter_upwards [Iio_mem_nhds ht] with s hs'
      rw [hs s (Or.inl (le_of_lt hs')), zero_div]
    exact continuousAt_const.congr hev
  · have c1 : ContinuousAt (fun s : ℝ => (s + 1)⁻¹) t :=
      (continuousAt_id.add continuousAt_const).inv₀ (ne_of_gt (by simp; linarith))
    have c2 : ContinuousAt (fun s : ℝ => (s + 2)⁻¹) t :=
      (continuousAt_id.add continuousAt_const).inv₀ (ne_of_gt (by simp; linarith))
    have hW : ContinuousAt sqrtThreeCoreWeight t := c1.add (continuousAt_const.mul c2)
    exact hu.continuousAt.div hW (sqrtThreeCoreWeight_pos (by linarith)).ne'

theorem continuous_sqrtThreeCoreLift {u : ℝ → ℝ} (hu : Continuous u)
    (hs : SqrtThreeCoreSupported u) : Continuous (sqrtThreeCoreLift u) := by
  have hb := hs.blindCoreSupported
  have hq := continuous_div_sqrtThreeCoreWeight hu hb
  have hqs : BlindCoreSupported fun t => u t / sqrtThreeCoreWeight t := fun t ht => by
    simp only [hb t ht, zero_div]
  have c1 := continuous_comp_inv_sub_of_blindCoreSupported hq hqs (m := 1) (by norm_num)
  have c2 := continuous_comp_inv_sub_of_blindCoreSupported hq hqs (m := 2) (by norm_num)
  exact c1.sub (continuous_const.mul c2)

/-- On `U`, `|u|/D ≤ (533/535) B` whenever `|u| ≤ B w`. -/
theorem abs_div_sqrtThreeCoreWeight_le {u : ℝ → ℝ} {B : ℝ}
    (hB : ∀ t, |u t| ≤ B * sqrtThreeCoreGauge t) {s : ℝ} (hs : SqrtThreeCoreMem s) :
    |u s / sqrtThreeCoreWeight s| ≤ 533 / 535 * B := by
  have hB0 : 0 ≤ B := by
    have h := (abs_nonneg _).trans (hB 1)
    unfold sqrtThreeCoreGauge at h
    norm_num at h
    exact h
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hD : 1183 / 999 ≤ sqrtThreeCoreWeight s := by
      have := sqrtThreeCoreWeight_anti (r := s) (q := 11 / 26) (by linarith) h2.le
      unfold sqrtThreeCoreWeight at this ⊢
      norm_num at this ⊢
      linarith
    have hDp : 0 < sqrtThreeCoreWeight s := by linarith
    have hu : |u s| ≤ 7 / 6 * B := by
      have := hB s
      unfold sqrtThreeCoreGauge at this
      rw [if_pos (by linarith)] at this
      linarith
    rw [abs_div, abs_of_pos hDp, div_le_iff₀ hDp]
    nlinarith
  · have hD : 535 / 533 ≤ sqrtThreeCoreWeight s := by
      have := sqrtThreeCoreWeight_anti (r := s) (q := 11 / 15) (by linarith) h2.le
      unfold sqrtThreeCoreWeight at this ⊢
      norm_num at this ⊢
      linarith
    have hDp : 0 < sqrtThreeCoreWeight s := by linarith
    have hu : |u s| ≤ B := by
      have := hB s
      unfold sqrtThreeCoreGauge at this
      rw [if_neg (by linarith)] at this
      linarith
    rw [abs_div, abs_of_pos hDp, div_le_iff₀ hDp]
    nlinarith

/-- **The gauged lift contracts**: `|S u| ≤ (533/535) B w` whenever `|u| ≤ B w`. -/
theorem abs_sqrtThreeCoreLift_le {u : ℝ → ℝ} {B : ℝ} (hs : SqrtThreeCoreSupported u)
    (hB : ∀ t, |u t| ≤ B * sqrtThreeCoreGauge t) (y : ℝ) :
    |sqrtThreeCoreLift u y| ≤ 533 / 535 * B * sqrtThreeCoreGauge y := by
  have hB0 : 0 ≤ B := by
    have h := (abs_nonneg _).trans (hB 1)
    unfold sqrtThreeCoreGauge at h
    norm_num at h
    exact h
  unfold sqrtThreeCoreLift
  by_cases h1 : SqrtThreeCoreMem (y⁻¹ - 1)
  · have hy := upper_of_inv_sub_one_mem h1
    have h2 : u (y⁻¹ - 2) = 0 := hs _ (by
      rintro (⟨a1, a2⟩ | ⟨a1, a2⟩) <;> rcases h1 with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> linarith)
    rw [h2, zero_div, mul_zero, sub_zero]
    have hg : sqrtThreeCoreGauge y = 1 := by
      unfold sqrtThreeCoreGauge; rw [if_neg (by linarith)]
    rw [hg, mul_one]
    exact abs_div_sqrtThreeCoreWeight_le hB h1
  · rw [hs _ h1, zero_div, zero_sub]
    by_cases h2 : SqrtThreeCoreMem (y⁻¹ - 2)
    · have hy := lower_of_inv_sub_two_mem h2
      have hg : sqrtThreeCoreGauge y = 7 / 6 := by
        unfold sqrtThreeCoreGauge; rw [if_pos (by linarith)]
      rw [hg, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 6)]
      have := abs_div_sqrtThreeCoreWeight_le hB h2
      nlinarith
    · rw [hs _ h2, zero_div, mul_zero, neg_zero, abs_zero]
      have := one_le_sqrtThreeCoreGauge y
      positivity

/-- **`M S = id` on `[0, 1]`.** -/
theorem blindCoreMayer_sqrtThreeCoreLift {u : ℝ → ℝ} (hs : SqrtThreeCoreSupported u) {r : ℝ}
    (h0 : 0 ≤ r) (h1 : r ≤ 1) : blindCoreMayer (sqrtThreeCoreLift u) r = u r := by
  unfold blindCoreMayer sqrtThreeCoreLift
  simp only [inv_inv]
  have e11 : r + 1 - 1 = r := by ring
  have e22 : r + 2 - 2 = r := by ring
  have z12 : u (r + 1 - 2) = 0 := hs.eq_zero_of_le (by linarith)
  have z21 : u (r + 2 - 1) = 0 := hs.eq_zero_of_ge (by linarith)
  have z31 : u (r + 3 - 1) = 0 := hs.eq_zero_of_ge (by linarith)
  have z32 : u (r + 3 - 2) = 0 := hs.eq_zero_of_ge (by linarith)
  rw [e11, e22, z12, z21, z31, z32]
  have hW := (sqrtThreeCoreWeight_pos h0).ne'
  have key : u r = u r / sqrtThreeCoreWeight r * ((r + 1)⁻¹ + 7 / 6 * (r + 2)⁻¹) := by
    rw [show (r + 1)⁻¹ + 7 / 6 * (r + 2)⁻¹ = sqrtThreeCoreWeight r from rfl,
      div_mul_cancel₀ _ hW]
  conv_rhs => rw [key]
  ring

/-! ### The seed -/

/-- A bump supported in `[2/5, 7/10]`. -/
def sqrtThreeCoreBump (t : ℝ) : ℝ := max 0 ((t - 2 / 5) * (7 / 10 - t))

/-- The seed `u₀(y) = (1/y)(β(1/y − 1) + β(1/y − 2))`. -/
def sqrtThreeCoreSeed (y : ℝ) : ℝ :=
  (y⁻¹ - 1 + 1) * sqrtThreeCoreBump (y⁻¹ - 1) + (y⁻¹ - 2 + 2) * sqrtThreeCoreBump (y⁻¹ - 2)

theorem sqrtThreeCoreBump_eq_zero {t : ℝ} (ht : t ≤ 2 / 5 ∨ 7 / 10 ≤ t) :
    sqrtThreeCoreBump t = 0 := by
  unfold sqrtThreeCoreBump
  apply max_eq_left
  rcases ht with ht | ht <;> nlinarith

theorem blindCoreSupported_sqrtThreeCoreBump_mul (m : ℝ) :
    BlindCoreSupported fun t => (t + m) * sqrtThreeCoreBump t := fun t ht => by
  have h : t ≤ 2 / 5 ∨ 7 / 10 ≤ t := by
    rcases ht with ht | ht
    · left; linarith
    · right; linarith
  simp only [sqrtThreeCoreBump_eq_zero h, mul_zero]

theorem continuous_sqrtThreeCoreSeed : Continuous sqrtThreeCoreSeed := by
  have hb : Continuous sqrtThreeCoreBump := by unfold sqrtThreeCoreBump; fun_prop
  have c1 := continuous_comp_inv_sub_of_blindCoreSupported
    ((continuous_id.add continuous_const).mul hb)
    (blindCoreSupported_sqrtThreeCoreBump_mul 1) (m := 1) (by norm_num)
  have c2 := continuous_comp_inv_sub_of_blindCoreSupported
    ((continuous_id.add continuous_const).mul hb)
    (blindCoreSupported_sqrtThreeCoreBump_mul 2) (m := 2) (by norm_num)
  exact c1.add c2

theorem sqrtThreeCoreSupported_seed : SqrtThreeCoreSupported sqrtThreeCoreSeed := by
  intro y hy
  unfold sqrtThreeCoreSeed
  have h1 : sqrtThreeCoreBump (y⁻¹ - 1) = 0 := by
    by_contra hne
    apply hy
    have hm : 2 / 5 < y⁻¹ - 1 ∧ y⁻¹ - 1 < 7 / 10 := by
      by_contra h
      rw [not_and_or, not_lt, not_lt] at h
      exact hne (sqrtThreeCoreBump_eq_zero h)
    obtain ⟨b1, b2⟩ := mem_of_inv_sub_mem (by norm_num) hm.1 hm.2
    norm_num at b1 b2
    right; constructor <;> linarith
  have h2 : sqrtThreeCoreBump (y⁻¹ - 2) = 0 := by
    by_contra hne
    apply hy
    have hm : 2 / 5 < y⁻¹ - 2 ∧ y⁻¹ - 2 < 7 / 10 := by
      by_contra h
      rw [not_and_or, not_lt, not_lt] at h
      exact hne (sqrtThreeCoreBump_eq_zero h)
    obtain ⟨b1, b2⟩ := mem_of_inv_sub_mem (by norm_num) hm.1 hm.2
    norm_num at b1 b2
    left; constructor <;> linarith
  rw [h1, h2]
  ring

theorem blindCoreMayer_sqrtThreeCoreSeed {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    blindCoreMayer sqrtThreeCoreSeed r = 0 := by
  unfold blindCoreMayer sqrtThreeCoreSeed
  simp only [inv_inv]
  have e11 : r + 1 - 1 = r := by ring
  have e22 : r + 2 - 2 = r := by ring
  have z12 : sqrtThreeCoreBump (r + 1 - 2) = 0 := sqrtThreeCoreBump_eq_zero (Or.inl (by linarith))
  have z21 : sqrtThreeCoreBump (r + 2 - 1) = 0 := sqrtThreeCoreBump_eq_zero (Or.inr (by linarith))
  have z31 : sqrtThreeCoreBump (r + 3 - 1) = 0 := sqrtThreeCoreBump_eq_zero (Or.inr (by linarith))
  have z32 : sqrtThreeCoreBump (r + 3 - 2) = 0 := sqrtThreeCoreBump_eq_zero (Or.inr (by linarith))
  rw [e11, e22, z12, z21, z31, z32]
  have h1' : r + 1 ≠ 0 := by linarith
  have h2' : r + 2 ≠ 0 := by linarith
  field_simp
  ring

theorem sqrtThreeCoreSeed_two_thirds : sqrtThreeCoreSeed (2 / 3) = 3 / 100 := by
  unfold sqrtThreeCoreSeed sqrtThreeCoreBump
  norm_num [max_def]

theorem exists_abs_sqrtThreeCoreSeed_le :
    ∃ B, ∀ y, |sqrtThreeCoreSeed y| ≤ B * sqrtThreeCoreGauge y := by
  have hcpt : HasCompactSupport sqrtThreeCoreSeed := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun x hx => ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · exact sqrtThreeCoreSupported_seed.eq_zero_of_le (by linarith)
    · exact sqrtThreeCoreSupported_seed.eq_zero_of_ge (by linarith)
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuous continuous_sqrtThreeCoreSeed
  refine ⟨C, fun y => ?_⟩
  have h := hC y
  rw [Real.norm_eq_abs] at h
  have hC0 : 0 ≤ C := (abs_nonneg _).trans h
  have := one_le_sqrtThreeCoreGauge y
  nlinarith

/-! ### The eigenfunction -/

/-- The iterates `S^k u₀`. -/
def sqrtThreeCoreIter (k : ℕ) : ℝ → ℝ := sqrtThreeCoreLift^[k] sqrtThreeCoreSeed

theorem sqrtThreeCoreIter_zero : sqrtThreeCoreIter 0 = sqrtThreeCoreSeed := rfl

theorem sqrtThreeCoreIter_succ (k : ℕ) :
    sqrtThreeCoreIter (k + 1) = sqrtThreeCoreLift (sqrtThreeCoreIter k) :=
  Function.iterate_succ_apply' _ _ _

theorem sqrtThreeCoreSupported_iter (k : ℕ) : SqrtThreeCoreSupported (sqrtThreeCoreIter k) := by
  induction k with
  | zero => exact sqrtThreeCoreSupported_seed
  | succ k ih => rw [sqrtThreeCoreIter_succ]; exact sqrtThreeCoreSupported_lift ih

theorem continuous_sqrtThreeCoreIter (k : ℕ) : Continuous (sqrtThreeCoreIter k) := by
  induction k with
  | zero => exact continuous_sqrtThreeCoreSeed
  | succ k ih =>
    rw [sqrtThreeCoreIter_succ]
    exact continuous_sqrtThreeCoreLift ih (sqrtThreeCoreSupported_iter k)

theorem abs_sqrtThreeCoreIter_le {B : ℝ}
    (hB : ∀ y, |sqrtThreeCoreSeed y| ≤ B * sqrtThreeCoreGauge y)
    (k : ℕ) (y : ℝ) : |sqrtThreeCoreIter k y| ≤ (533 / 535) ^ k * B * sqrtThreeCoreGauge y := by
  induction k generalizing y with
  | zero => rw [sqrtThreeCoreIter_zero, pow_zero, one_mul]; exact hB y
  | succ k ih =>
    rw [sqrtThreeCoreIter_succ]
    calc |sqrtThreeCoreLift (sqrtThreeCoreIter k) y|
        ≤ 533 / 535 * ((533 / 535) ^ k * B) * sqrtThreeCoreGauge y :=
          abs_sqrtThreeCoreLift_le (sqrtThreeCoreSupported_iter k) ih y
      _ = (533 / 535) ^ (k + 1) * B * sqrtThreeCoreGauge y := by ring

theorem abs_sqrtThreeCoreIter_le' {B : ℝ}
    (hB : ∀ y, |sqrtThreeCoreSeed y| ≤ B * sqrtThreeCoreGauge y) (k : ℕ) (y : ℝ) :
    |(-1 : ℝ) ^ k * sqrtThreeCoreIter k y| ≤ (533 / 535) ^ k * (B * (7 / 6)) := by
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have h := abs_sqrtThreeCoreIter_le hB k y
  have hB0 : 0 ≤ B := by
    have h' := (abs_nonneg _).trans (hB 1)
    unfold sqrtThreeCoreGauge at h'
    norm_num at h'
    exact h'
  have hg := sqrtThreeCoreGauge_le y
  have hp : 0 ≤ (533 / 535 : ℝ) ^ k * B := by positivity
  calc |sqrtThreeCoreIter k y| ≤ (533 / 535) ^ k * B * sqrtThreeCoreGauge y := h
    _ ≤ (533 / 535) ^ k * B * (7 / 6) := mul_le_mul_of_nonneg_left hg hp
    _ = _ := by ring

theorem summable_sqrtThreeCoreIter (y : ℝ) :
    Summable fun k : ℕ => (-1 : ℝ) ^ k * sqrtThreeCoreIter k y := by
  obtain ⟨B, hB⟩ := exists_abs_sqrtThreeCoreSeed_le
  have hg := (summable_geometric_of_lt_one (r := 533 / 535) (by norm_num)
    (by norm_num)).mul_right (B * (7 / 6))
  refine Summable.of_norm_bounded hg fun k => ?_
  rw [Real.norm_eq_abs]
  exact abs_sqrtThreeCoreIter_le' hB k y

/-- The eigenfunction `f = Σ_k (−1)^k S^k u₀`. -/
def sqrtThreeCoreEigen (y : ℝ) : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k * sqrtThreeCoreIter k y

theorem continuous_sqrtThreeCoreEigen : Continuous sqrtThreeCoreEigen := by
  obtain ⟨B, hB⟩ := exists_abs_sqrtThreeCoreSeed_le
  have hg := (summable_geometric_of_lt_one (r := 533 / 535) (by norm_num)
    (by norm_num)).mul_right (B * (7 / 6))
  refine continuous_tsum (fun k => continuous_const.mul (continuous_sqrtThreeCoreIter k)) hg
    fun k y => ?_
  rw [Real.norm_eq_abs]
  exact abs_sqrtThreeCoreIter_le' hB k y

theorem sqrtThreeCoreSupported_eigen : SqrtThreeCoreSupported sqrtThreeCoreEigen := by
  intro t ht
  unfold sqrtThreeCoreEigen
  simp only [sqrtThreeCoreSupported_iter _ t ht, mul_zero, tsum_zero]

/-- **The eigen-equation** `M f = −f` on `[0, 1]`. -/
theorem blindCoreMayer_sqrtThreeCoreEigen {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    blindCoreMayer sqrtThreeCoreEigen r = -sqrtThreeCoreEigen r := by
  have hs := summable_sqrtThreeCoreIter
  have hT : (fun k : ℕ => (-1 : ℝ) ^ k * blindCoreMayer (sqrtThreeCoreIter k) r) = fun k =>
      (-1) ^ k * sqrtThreeCoreIter k (r + 1)⁻¹ / (r + 1) -
        (-1) ^ k * sqrtThreeCoreIter k (r + 2)⁻¹ / (r + 2) +
        (-1) ^ k * sqrtThreeCoreIter k (r + 3)⁻¹ / (r + 3) := by
    funext k
    unfold blindCoreMayer
    ring
  have hTs : Summable fun k : ℕ => (-1 : ℝ) ^ k * blindCoreMayer (sqrtThreeCoreIter k) r := by
    rw [hT]
    exact (((hs _).div_const _).sub ((hs _).div_const _)).add ((hs _).div_const _)
  have lhs : blindCoreMayer sqrtThreeCoreEigen r =
      ∑' k : ℕ, (-1 : ℝ) ^ k * blindCoreMayer (sqrtThreeCoreIter k) r := by
    rw [hT, Summable.tsum_add (((hs _).div_const _).sub ((hs _).div_const _))
      ((hs _).div_const _), Summable.tsum_sub ((hs _).div_const _) ((hs _).div_const _),
      tsum_div_const, tsum_div_const, tsum_div_const]
    rfl
  have hstep : ∀ k : ℕ, (-1 : ℝ) ^ (k + 1) * blindCoreMayer (sqrtThreeCoreIter (k + 1)) r =
      -((-1 : ℝ) ^ k * sqrtThreeCoreIter k r) := by
    intro k
    rw [sqrtThreeCoreIter_succ,
      blindCoreMayer_sqrtThreeCoreLift (sqrtThreeCoreSupported_iter k) h0 h1, pow_succ]
    ring
  rw [lhs, hTs.tsum_eq_zero_add]
  simp only [hstep, pow_zero, one_mul, sqrtThreeCoreIter_zero,
    blindCoreMayer_sqrtThreeCoreSeed h0 h1, zero_add, tsum_neg]
  rfl

/-- `f + S f = u₀`. -/
theorem sqrtThreeCoreEigen_add_lift (y : ℝ) :
    sqrtThreeCoreEigen y + sqrtThreeCoreLift sqrtThreeCoreEigen y = sqrtThreeCoreSeed y := by
  have hs := summable_sqrtThreeCoreIter
  have hT : (fun k : ℕ => (-1 : ℝ) ^ k * sqrtThreeCoreIter (k + 1) y) = fun k =>
      (-1) ^ k * sqrtThreeCoreIter k (y⁻¹ - 1) / sqrtThreeCoreWeight (y⁻¹ - 1) -
        7 / 6 * ((-1) ^ k * sqrtThreeCoreIter k (y⁻¹ - 2) / sqrtThreeCoreWeight (y⁻¹ - 2)) := by
    funext k
    rw [sqrtThreeCoreIter_succ]
    unfold sqrtThreeCoreLift
    ring
  have hL : sqrtThreeCoreLift sqrtThreeCoreEigen y =
      ∑' k : ℕ, (-1 : ℝ) ^ k * sqrtThreeCoreIter (k + 1) y := by
    rw [hT, Summable.tsum_sub ((hs _).div_const _) (((hs _).div_const _).mul_left _),
      tsum_mul_left, tsum_div_const, tsum_div_const]
    rfl
  have hE : sqrtThreeCoreEigen y = sqrtThreeCoreSeed y -
      ∑' k : ℕ, (-1 : ℝ) ^ k * sqrtThreeCoreIter (k + 1) y := by
    unfold sqrtThreeCoreEigen
    rw [(hs y).tsum_eq_zero_add]
    have h : ∀ k : ℕ, (-1 : ℝ) ^ (k + 1) * sqrtThreeCoreIter (k + 1) y =
        -((-1) ^ k * sqrtThreeCoreIter (k + 1) y) := fun k => by ring
    simp only [h, tsum_neg, pow_zero, one_mul, sqrtThreeCoreIter_zero]
    ring
  rw [hL, hE]
  ring

theorem exists_sqrtThreeCoreEigen_ne_zero : ∃ t, sqrtThreeCoreEigen t ≠ 0 := by
  by_contra h
  push Not at h
  have hS : sqrtThreeCoreLift sqrtThreeCoreEigen (2 / 3) = 0 := by
    unfold sqrtThreeCoreLift
    simp [h]
  have := sqrtThreeCoreEigen_add_lift (2 / 3)
  rw [h, hS, add_zero, sqrtThreeCoreSeed_two_thirds] at this
  norm_num at this

/-! ### The core -/

section Core

variable {f : ℝ → ℝ} (hs : SqrtThreeCoreSupported f)
  (heig : ∀ r, 0 ≤ r → r ≤ 1 → blindCoreMayer f r = -f r)

include hs heig in
/-- `G` vanishes on `[0, 56/97)`: there `r = (2x − 1)/(1 − x) < 15/41`. -/
theorem blindCoreFn_of_lt_fifty_six_ninety_sevenths {x : ℝ} (h0 : 0 ≤ x)
    (h1 : x < 56 / 97) : blindCoreFn f x = 0 := by
  have hb := hs.blindCoreSupported
  unfold blindCoreFn
  rw [abs_of_nonneg h0]
  have hA : blindCoreHalf f x = 0 := by
    rcases le_or_gt x (1 / 2) with h | h
    · exact blindCoreHalf_of_le_half h
    · have hx1 : 0 < 1 - x := by linarith
      unfold blindCoreHalf
      rw [blindCoreProfile_eq (by linarith) (by linarith)]
      have hr0 : 0 ≤ (2 * x - 1) / (1 - x) := div_nonneg (by linarith) hx1.le
      have hr : (2 * x - 1) / (1 - x) ≤ 15 / 41 := by
        rw [div_le_iff₀ hx1]; linarith
      rw [heig _ hr0 (by linarith), hs.eq_zero_of_le hr]
      simp
  rw [hA, zero_add]
  rcases eq_or_lt_of_le h0 with h | h
  · subst h; simp
  · rw [blindCoreHalf_of_one_le (by rw [le_inv_comm₀ one_pos h]; simp; linarith)]
    ring

end Core

/-- **A continuous inversion-symmetric Fourier-blind core of support ratio `97/56`.**  There is a
nonzero continuous even `G` with `G(1/x) = x G(x)` for `x > 0`, vanishing on `[0, 56/97)`, whose
Fourier transform vanishes at every integer. -/
theorem exists_inversionSymmetric_fourierBlind_ninety_seven_fifty_sixths :
    ∃ G : ℝ → ℝ, Continuous G ∧ (∀ x, G (-x) = G x) ∧ (∀ x, 0 < x → G x⁻¹ = x * G x) ∧
      (∀ x, 0 ≤ x → x < 56 / 97 → G x = 0) ∧ (∀ n : ℤ, 𝓕 (fun x => (G x : ℂ)) n = 0) ∧
      ∃ y, G y ≠ 0 := by
  set f := sqrtThreeCoreEigen
  have hf : Continuous f := continuous_sqrtThreeCoreEigen
  have hs : SqrtThreeCoreSupported f := sqrtThreeCoreSupported_eigen
  have hb := hs.blindCoreSupported
  have heig : ∀ r, 0 ≤ r → r ≤ 1 → blindCoreMayer f r = -f r :=
    fun _ h0 h1 => blindCoreMayer_sqrtThreeCoreEigen h0 h1
  obtain ⟨t, ht⟩ := exists_sqrtThreeCoreEigen_ne_zero
  have hcpt : HasCompactSupport (blindCoreFn f) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun x hx => ?_
    apply blindCoreFn_of_two_le
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  refine ⟨blindCoreFn f, continuous_blindCoreFn hf, blindCoreFn_neg,
    fun x hx => blindCoreFn_inv hx,
    fun x h0 h1 => blindCoreFn_of_lt_fifty_six_ninety_sevenths hs heig h0 h1,
    fun n => fourier_eq_zero_of_tsum_add_int_eq_zero (continuous_blindCoreFn hf) hcpt
      (tsum_blindCoreFn_add_int hb heig) n, ?_⟩
  have ht1 : 15 / 41 < t := by
    by_contra h
    exact ht (hs.eq_zero_of_le (not_lt.mp h))
  have ht2 : t < 11 / 15 := by
    by_contra h
    exact ht (hs.eq_zero_of_ge (not_lt.mp h))
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
