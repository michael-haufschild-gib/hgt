import Mathlib

/-!
# Continuous profile of the norm-four weighted count

Let `r(x)` be the squared distance from `x/2` to the integers, and let
`A(x) = x²/4 - r(x)` be the weighted count of positive odd integers for `x ≥ 0`.
The finite sum `R₄(x) = Σ_b 4^b A(x/4^b)` has deficit `H(x) = x²/3 - R₄(x)`.

There is a continuous profile `P` on the positive axis with
`0 ≤ x P(x) - H(x) ≤ 1/12`, `P(4x) = P(x)`, and
`P(x) + P(x/2) = 1/2`. The last identity follows from the exact parity
partition and the vanishing of the scaled rounding remainder. In particular,
`0 ≤ P(x) ≤ 1/2`. No averaging or equidistribution input is assumed.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount

/-- Squared midpoint-rounding error of the positive odd integers. -/
def midpointRounding (Y : ℝ) : ℝ := ‖((Y / 2 : ℝ) : UnitAddCircle)‖ ^ 2

theorem midpointRounding_nonneg (Y : ℝ) : 0 ≤ midpointRounding Y := sq_nonneg _

theorem midpointRounding_le_quarter (Y : ℝ) : midpointRounding Y ≤ 1 / 4 := by
  have h : ‖((Y / 2 : ℝ) : UnitAddCircle)‖ ≤ 1 / 2 := by
    rw [UnitAddCircle.norm_eq]
    exact abs_sub_round _
  have hn := norm_nonneg ((Y / 2 : ℝ) : UnitAddCircle)
  dsimp only [midpointRounding]
  nlinarith only [h, hn]

/-- The squared circle norm removes the jump of the nearest-integer map. -/
theorem continuous_midpointRounding : Continuous midpointRounding := by
  exact (((AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_id.div_const 2)).norm).pow 2

theorem midpointRounding_periodic : Function.Periodic midpointRounding 2 := by
  intro Y
  change ‖(((Y + 2) / 2 : ℝ) : UnitAddCircle)‖ ^ 2 = _
  rw [show (Y + 2) / 2 = Y / 2 + 1 by ring,
    AddCircle.coe_add, AddCircle.coe_period, add_zero]
  rfl

theorem midpointRounding_small {Y : ℝ} (hY : 0 ≤ Y) (hY1 : Y ≤ 1) :
    midpointRounding Y = Y ^ 2 / 4 := by
  have ha : |Y / 2| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_of_nonneg (div_nonneg hY (by norm_num)), abs_one]
    linarith only [hY1]
  have hn := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr ha
  rw [midpointRounding, hn, sq_abs]
  ring

theorem midpointRounding_eq_floor {Y : ℝ} (hY : 0 ≤ Y) :
    midpointRounding Y = ((⌊(Y + 1) / 2⌋₊ : ℝ) - Y / 2) ^ 2 := by
  have hn : (⌊(Y + 1) / 2⌋₊ : ℤ) = ⌊(Y + 1) / 2⌋ := by
    rw [← Int.floor_toNat]
    exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity))
  have hr : (⌊(Y + 1) / 2⌋₊ : ℝ) = (⌊(Y + 1) / 2⌋ : ℤ) := by
    exact_mod_cast hn
  rw [midpointRounding, UnitAddCircle.norm_eq, sq_abs, round_eq,
    show Y / 2 + 1 / 2 = (Y + 1) / 2 by ring, ← hr]
  ring

/-- Weighted odd-integer count as a continuous midpoint-rounding formula. -/
def oddArea (Y : ℝ) : ℝ := Y ^ 2 / 4 - midpointRounding Y

theorem continuous_oddArea : Continuous oddArea :=
  ((continuous_id.pow 2).div_const 4).sub continuous_midpointRounding

theorem oddArea_eq_floor {Y : ℝ} (hY : 0 ≤ Y) :
    oddArea Y = (⌊(Y + 1) / 2⌋₊ : ℝ) * Y - (⌊(Y + 1) / 2⌋₊ : ℝ) ^ 2 := by
  rw [oddArea, midpointRounding_eq_floor hY]
  ring

theorem oddArea_zero {Y : ℝ} (hY : 0 ≤ Y) (hY1 : Y ≤ 1) : oddArea Y = 0 := by
  rw [oddArea, midpointRounding_small hY hY1, sub_self]

theorem midpointRounding_small_abs {Y : ℝ} (hY : |Y| ≤ 1) :
    midpointRounding Y = Y ^ 2 / 4 := by
  have ha : |Y / 2| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_div, abs_two, abs_one]
    linarith only [hY]
  have hn := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr ha
  rw [midpointRounding, hn, sq_abs]
  ring

theorem oddArea_zero_abs {Y : ℝ} (hY : |Y| ≤ 1) : oddArea Y = 0 := by
  rw [oddArea, midpointRounding_small_abs hY, sub_self]

/-- Weighted count of ordinary positive integers. -/
def ordinaryArea (Y : ℝ) : ℝ :=
  Y * (⌊Y⌋₊ : ℝ) - (⌊Y⌋₊ : ℝ) * ((⌊Y⌋₊ : ℝ) + 1) / 2

theorem ordinaryArea_zero {Y : ℝ} (hY1 : Y ≤ 1) : ordinaryArea Y = 0 := by
  by_cases h : Y < 1
  · have hf : ⌊Y⌋₊ = 0 := Nat.floor_eq_zero.mpr h
    simp only [ordinaryArea, hf, Nat.cast_zero, mul_zero, zero_mul, zero_div, sub_zero]
  · have hy : Y = 1 := le_antisymm hY1 (le_of_not_gt h)
    rw [hy]
    norm_num [ordinaryArea]

theorem oddArea_eq_ordinary_sub {Y : ℝ} (hY : 0 ≤ Y) :
    oddArea Y = ordinaryArea Y - 2 * ordinaryArea (Y / 2) := by
  have hJ : ⌊(Y + 1) / 2⌋₊ = (⌊Y⌋₊ + 1) / 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl,
      Nat.floor_div_natCast, Nat.floor_add_one hY]
  rw [oddArea_eq_floor hY, hJ, ordinaryArea, ordinaryArea,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, Nat.floor_div_natCast]
  generalize ⌊Y⌋₊ = n
  by_cases hm : n % 2 = 0
  · have hj : (n + 1) / 2 = n / 2 := by omega
    have hn : (n : ℝ) = 2 * (n / 2 : ℕ) := by
      exact_mod_cast (show n = 2 * (n / 2) by omega)
    rw [hj, hn]
    norm_num
    ring
  · have hj : (n + 1) / 2 = n / 2 + 1 := by omega
    have hn : (n : ℝ) = 2 * (n / 2 : ℕ) + 1 := by
      exact_mod_cast (show n = 2 * (n / 2) + 1 by omega)
    rw [hj, hn]
    push_cast
    ring

theorem oddArea_pair_telescope {Y : ℝ} (hY : 0 ≤ Y) :
    oddArea Y + 2 * oddArea (Y / 2) = ordinaryArea Y - 4 * ordinaryArea (Y / 4) := by
  rw [oddArea_eq_ordinary_sub hY, oddArea_eq_ordinary_sub (div_nonneg hY (by norm_num)),
    show Y / 2 / 2 = Y / 4 by ring]
  ring

theorem ordinaryArea_deficit (Y : ℝ) :
    Y ^ 2 / 2 - ordinaryArea Y =
      Y / 2 - (Y - (⌊Y⌋₊ : ℝ)) * (1 - (Y - (⌊Y⌋₊ : ℝ))) / 2 := by
  rw [ordinaryArea]
  ring

/-- Weighted odd-integer counts along all powers of four; only finitely many terms survive. -/
def fourArea (X : ℝ) : ℝ := ∑' b : ℕ, (4 : ℝ) ^ b * oddArea (X / (4 : ℝ) ^ b)

private theorem four_term_zero {X : ℝ} {B b : ℕ}
    (hX : |X| ≤ (4 : ℝ) ^ B) (hb : B ≤ b) :
    (4 : ℝ) ^ b * oddArea (X / (4 : ℝ) ^ b) = 0 := by
  have hp : 0 < (4 : ℝ) ^ b := by positivity
  have hXB := hX.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hb)
  have hz : oddArea (X / (4 : ℝ) ^ b) = 0 := by
    apply oddArea_zero_abs
    rw [abs_div, abs_of_pos hp]
    exact (div_le_one hp).mpr hXB
  rw [hz, mul_zero]

theorem fourArea_eq_sum {X : ℝ} (B : ℕ) (hX : |X| ≤ (4 : ℝ) ^ B) :
    fourArea X = ∑ b ∈ Finset.range B, (4 : ℝ) ^ b * oddArea (X / (4 : ℝ) ^ b) := by
  apply tsum_eq_sum
  intro b hb
  exact four_term_zero hX (by simpa only [Finset.mem_range, not_lt] using hb)

theorem four_terms_summable (X : ℝ) :
    Summable (fun b : ℕ => (4 : ℝ) ^ b * oddArea (X / (4 : ℝ) ^ b)) := by
  obtain ⟨B, hB⟩ := pow_unbounded_of_one_lt |X| (by norm_num : (1 : ℝ) < 4)
  apply summable_of_ne_finset_zero (s := Finset.range B)
  intro b hb
  exact four_term_zero hB.le (by simpa only [Finset.mem_range, not_lt] using hb)

theorem continuous_fourArea : Continuous fourArea := by
  apply continuous_iff_continuousAt.mpr
  intro X
  obtain ⟨B, hB⟩ := pow_unbounded_of_one_lt |X| (by norm_num : (1 : ℝ) < 4)
  have hc : Continuous (fun Y : ℝ =>
      ∑ b ∈ Finset.range B, (4 : ℝ) ^ b * oddArea (Y / (4 : ℝ) ^ b)) :=
    continuous_finsetSum _ (fun b _ => continuous_const.mul
      (continuous_oddArea.comp (continuous_id.div_const _)))
  apply hc.continuousAt.congr_of_eventuallyEq
  have hU : {Y : ℝ | |Y| < (4 : ℝ) ^ B} ∈ nhds X :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds hB
  filter_upwards [hU] with Y hY
  exact fourArea_eq_sum B hY.le

theorem oddArea_nonneg {Y : ℝ} (hY : 0 ≤ Y) : 0 ≤ oddArea Y := by
  by_cases hy : Y ≤ 1
  · rw [oddArea_zero hY hy]
  · have hy1 : 1 ≤ Y := le_of_not_ge hy
    have hJ := Nat.floor_le (show 0 ≤ (Y + 1) / 2 by positivity)
    have hjY : (⌊(Y + 1) / 2⌋₊ : ℝ) ≤ Y := by linarith only [hy1, hJ]
    have hp := mul_nonneg (Nat.cast_nonneg ⌊(Y + 1) / 2⌋₊) (sub_nonneg.mpr hjY)
    rw [oddArea_eq_floor hY]
    nlinarith only [hp]

theorem fourArea_nonneg {X : ℝ} (hX : 0 ≤ X) : 0 ≤ fourArea X := by
  apply tsum_nonneg
  intro b
  exact mul_nonneg (by positivity) (oddArea_nonneg (by positivity))

theorem fourArea_le_quadratic (X : ℝ) : fourArea X ≤ X ^ 2 / 3 := by
  have hterm (b : ℕ) : (4 : ℝ) ^ b * oddArea (X / (4 : ℝ) ^ b) ≤
      X ^ 2 / 4 * (1 / 4 : ℝ) ^ b := by
    have hp : 0 < (4 : ℝ) ^ b := by positivity
    calc
      _ ≤ (4 : ℝ) ^ b * ((X / (4 : ℝ) ^ b) ^ 2 / 4) := by
        apply mul_le_mul_of_nonneg_left _ hp.le
        exact sub_le_self _ (midpointRounding_nonneg _)
      _ = _ := by simp only [div_pow, one_pow]; field_simp
  have hg : Summable (fun b : ℕ => X ^ 2 / 4 * (1 / 4 : ℝ) ^ b) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left _
  have hmain : (∑' b : ℕ, X ^ 2 / 4 * (1 / 4 : ℝ) ^ b) = X ^ 2 / 3 := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
    norm_num
    ring
  have h := Summable.tsum_le_tsum hterm (four_terms_summable X) hg
  rwa [hmain] at h

/-- Deficit of the norm-four stack from its quadratic density. -/
def fourDeficit (X : ℝ) : ℝ := X ^ 2 / 3 - fourArea X

theorem continuous_fourDeficit : Continuous fourDeficit :=
  ((continuous_id.pow 2).div_const 3).sub continuous_fourArea

theorem fourDeficit_nonneg (X : ℝ) : 0 ≤ fourDeficit X :=
  sub_nonneg.mpr (fourArea_le_quadratic X)

theorem fourArea_four (X : ℝ) : fourArea (4 * X) = oddArea (4 * X) + 4 * fourArea X := by
  rw [fourArea, (four_terms_summable (4 * X)).tsum_eq_zero_add]
  simp only [pow_zero, div_one, one_mul]
  congr 1
  rw [fourArea, ← tsum_mul_left]
  apply tsum_congr
  intro b
  have hd : 4 * X / (4 : ℝ) ^ (b + 1) = X / (4 : ℝ) ^ b := by
    rw [pow_succ]
    field_simp
  rw [hd, pow_succ]
  ring

theorem fourDeficit_four (X : ℝ) :
    fourDeficit (4 * X) = 4 * fourDeficit X + midpointRounding (4 * X) := by
  rw [fourDeficit, fourDeficit, fourArea_four, oddArea]
  ring

private theorem four_pair_partial {X : ℝ} (hX : 0 ≤ X) (B : ℕ) :
    (∑ b ∈ Finset.range B, (4 : ℝ) ^ b *
      (oddArea (X / (4 : ℝ) ^ b) + 2 * oddArea ((X / (4 : ℝ) ^ b) / 2))) =
      ordinaryArea X - (4 : ℝ) ^ B * ordinaryArea (X / (4 : ℝ) ^ B) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Finset.sum_range_succ, ih,
      oddArea_pair_telescope (show 0 ≤ X / (4 : ℝ) ^ B by positivity)]
    rw [show X / (4 : ℝ) ^ B / 4 = X / (4 : ℝ) ^ (B + 1) by
      rw [pow_succ, div_mul_eq_div_div]]
    rw [pow_succ]
    ring

theorem fourArea_half_partition {X : ℝ} (hX : 0 ≤ X) :
    fourArea X + 2 * fourArea (X / 2) = ordinaryArea X := by
  obtain ⟨B, hB⟩ := pow_unbounded_of_one_lt X (by norm_num : (1 : ℝ) < 4)
  have hBX : |X| ≤ (4 : ℝ) ^ B := by rw [abs_of_nonneg hX]; exact hB.le
  have hBX2 : |X / 2| ≤ (4 : ℝ) ^ B := by
    rw [abs_of_nonneg (div_nonneg hX (by norm_num))]
    linarith only [hB, hX]
  have hz : ordinaryArea (X / (4 : ℝ) ^ B) = 0 := by
    apply ordinaryArea_zero
    exact (div_le_one (by positivity : 0 < (4 : ℝ) ^ B)).mpr hB.le
  rw [fourArea_eq_sum B hBX, fourArea_eq_sum B hBX2, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  calc
    _ = ∑ b ∈ Finset.range B, (4 : ℝ) ^ b *
        (oddArea (X / (4 : ℝ) ^ b) + 2 * oddArea ((X / (4 : ℝ) ^ b) / 2)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [show (X / 2) / (4 : ℝ) ^ b = (X / (4 : ℝ) ^ b) / 2 by ring]
      ring
    _ = _ := by rw [four_pair_partial hX B, hz, mul_zero, sub_zero]

theorem fourDeficit_half_partition {X : ℝ} (hX : 0 ≤ X) :
    fourDeficit X + 2 * fourDeficit (X / 2) =
      X / 2 - (X - (⌊X⌋₊ : ℝ)) * (1 - (X - (⌊X⌋₊ : ℝ))) / 2 := by
  have hp := fourArea_half_partition hX
  have hd := ordinaryArea_deficit X
  dsimp only [fourDeficit]
  linear_combination -hp + hd

private def profileTailTerm (j : ℕ) (X : ℝ) : ℝ :=
  midpointRounding ((4 : ℝ) ^ (j + 1) * X) / ((4 : ℝ) ^ (j + 1) * X)

private theorem profileTailTerm_nonneg {X : ℝ} (hX : 0 < X) (j : ℕ) :
    0 ≤ profileTailTerm j X :=
  div_nonneg (midpointRounding_nonneg _) (by positivity)

private theorem profileTailTerm_le {a X : ℝ} (ha : 0 < a) (haX : a ≤ X) (j : ℕ) :
    profileTailTerm j X ≤ (1 / (16 * a)) * (1 / 4 : ℝ) ^ j := by
  have hX : 0 < X := ha.trans_le haX
  have hpow : 0 < (4 : ℝ) ^ (j + 1) := by positivity
  calc
    _ ≤ (1 / 4 : ℝ) / ((4 : ℝ) ^ (j + 1) * X) :=
      div_le_div_of_nonneg_right (midpointRounding_le_quarter _) (by positivity)
    _ ≤ (1 / 4 : ℝ) / ((4 : ℝ) ^ (j + 1) * a) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left haX hpow.le)
    _ = _ := by
      simp only [pow_succ, div_pow, one_pow]
      field_simp
      ring

/-- The summable correction from finite scale to the multiplicatively periodic limit. -/
def profileTail (X : ℝ) : ℝ := ∑' j : ℕ, profileTailTerm j X

private theorem profileTail_summable {X : ℝ} (hX : 0 < X) :
    Summable (fun j : ℕ => profileTailTerm j X) := by
  have hg : Summable (fun j : ℕ => (1 / (16 * X)) * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left _
  exact Summable.of_nonneg_of_le (fun j => profileTailTerm_nonneg hX j)
    (fun j => profileTailTerm_le hX le_rfl j) hg

theorem profileTail_nonneg {X : ℝ} (hX : 0 < X) : 0 ≤ profileTail X :=
  tsum_nonneg (fun j => profileTailTerm_nonneg hX j)

theorem profileTail_le {X : ℝ} (hX : 0 < X) : profileTail X ≤ 1 / (12 * X) := by
  have hg : Summable (fun j : ℕ => (1 / (16 * X)) * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left _
  have hmain : (∑' j : ℕ, (1 / (16 * X)) * (1 / 4 : ℝ) ^ j) = 1 / (12 * X) := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]
    norm_num
    field_simp
    norm_num
  have h := Summable.tsum_le_tsum (fun j => profileTailTerm_le hX le_rfl j)
    (profileTail_summable hX) hg
  rwa [hmain] at h

private theorem continuousOn_profileTail {a : ℝ} (ha : 0 < a) :
    ContinuousOn profileTail (Set.Ici a) := by
  apply continuousOn_tsum (u := fun j : ℕ => (1 / (16 * a)) * (1 / 4 : ℝ) ^ j)
  · intro j
    apply ((continuous_midpointRounding.comp (continuous_const.mul continuous_id)).continuousOn).div
      ((continuous_const.mul continuous_id).continuousOn)
    intro X hX
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (ha.trans_le hX))
  · exact (summable_geometric_of_norm_lt_one
      (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left _
  · intro j X hX
    rw [Real.norm_eq_abs, abs_of_nonneg (profileTailTerm_nonneg (ha.trans_le hX) j)]
    exact profileTailTerm_le ha hX j

theorem continuousAt_profileTail {X : ℝ} (hX : 0 < X) : ContinuousAt profileTail X := by
  have ha : 0 < X / 2 := by linarith only [hX]
  apply (continuousOn_profileTail ha).continuousAt
  exact Ici_mem_nhds (by linarith only [hX])

/-- Limit of the normalized norm-four deficit along successive powers of four. -/
def fourProfile (X : ℝ) : ℝ := fourDeficit X / X + profileTail X

theorem continuousAt_fourProfile {X : ℝ} (hX : 0 < X) : ContinuousAt fourProfile X :=
  (continuous_fourDeficit.continuousAt.div continuousAt_id hX.ne').add
    (continuousAt_profileTail hX)

theorem fourProfile_nonneg {X : ℝ} (hX : 0 < X) : 0 ≤ fourProfile X :=
  add_nonneg (div_nonneg (fourDeficit_nonneg X) hX.le) (profileTail_nonneg hX)

theorem fourProfile_approx {X : ℝ} (hX : 0 < X) :
    0 ≤ X * fourProfile X - fourDeficit X ∧
      X * fourProfile X - fourDeficit X ≤ 1 / 12 := by
  have hid : X * fourProfile X - fourDeficit X = X * profileTail X := by
    rw [fourProfile]
    field_simp
    ring
  rw [hid]
  constructor
  · exact mul_nonneg hX.le (profileTail_nonneg hX)
  · calc
      _ ≤ X * (1 / (12 * X)) := mul_le_mul_of_nonneg_left (profileTail_le hX) hX.le
      _ = 1 / 12 := by field_simp

private theorem profileTail_shift {X : ℝ} (hX : 0 < X) :
    profileTail X = midpointRounding (4 * X) / (4 * X) + profileTail (4 * X) := by
  have hs := (profileTail_summable hX).tsum_eq_zero_add
  have ht : (∑' j : ℕ, profileTailTerm (j + 1) X) = profileTail (4 * X) := by
    apply tsum_congr
    intro j
    dsimp only [profileTailTerm]
    rw [show (4 : ℝ) ^ (j + 1 + 1) * X = (4 : ℝ) ^ (j + 1) * (4 * X) by
      rw [pow_succ]; ring]
  change profileTail X = profileTailTerm 0 X + ∑' j : ℕ, profileTailTerm (j + 1) X at hs
  rw [ht] at hs
  simpa only [profileTailTerm, zero_add, pow_one] using hs

theorem fourProfile_four {X : ℝ} (hX : 0 < X) : fourProfile (4 * X) = fourProfile X := by
  rw [fourProfile, fourProfile, fourDeficit_four, profileTail_shift hX]
  field_simp
  ring

theorem fourProfile_pow {X : ℝ} (hX : 0 < X) (n : ℕ) :
    fourProfile ((4 : ℝ) ^ n * X) = fourProfile X := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, show (4 : ℝ) ^ n * 4 * X = 4 * ((4 : ℝ) ^ n * X) by ring,
      fourProfile_four (by positivity), ih]

private theorem fourProfile_pair_error {X : ℝ} (hX : 0 < X) :
    |fourProfile X + fourProfile (X / 2) - 1 / 2| ≤ 1 / (4 * X) := by
  have h1 := fourProfile_approx hX
  have h2 := fourProfile_approx (show 0 < X / 2 by positivity)
  have hp := fourDeficit_half_partition hX.le
  have ht0 : 0 ≤ X - (⌊X⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le hX.le)
  have ht1 : X - (⌊X⌋₊ : ℝ) ≤ 1 := by
    have h := Nat.lt_floor_add_one X
    linarith only [h]
  have hp0 : 0 ≤ (X - (⌊X⌋₊ : ℝ)) * (1 - (X - (⌊X⌋₊ : ℝ))) :=
    mul_nonneg ht0 (sub_nonneg.mpr ht1)
  have hp1 : (X - (⌊X⌋₊ : ℝ)) * (1 - (X - (⌊X⌋₊ : ℝ))) ≤ 1 / 4 := by
    nlinarith only [sq_nonneg (X - (⌊X⌋₊ : ℝ) - 1 / 2)]
  have he : |X * (fourProfile X + fourProfile (X / 2) - 1 / 2)| ≤ 1 / 4 := by
    apply abs_le.mpr
    constructor
    · nlinarith only [h1.1, h2.1, hp, hp1]
    · nlinarith only [h1.2, h2.2, hp, hp0]
  rw [abs_mul, abs_of_pos hX] at he
  apply (le_div_iff₀ (by positivity : 0 < 4 * X)).mpr
  nlinarith only [he]

/-- The two complementary half-periods sum exactly to one half. -/
theorem fourProfile_half {X : ℝ} (hX : 0 < X) :
    fourProfile X + fourProfile (X / 2) = 1 / 2 := by
  apply sub_eq_zero.mp
  by_contra hne
  have he : 0 < |fourProfile X + fourProfile (X / 2) - 1 / 2| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (1 / (4 * X * |fourProfile X + fourProfile (X / 2) - 1 / 2|))
    (by norm_num : (1 : ℝ) < 4)
  have hb := fourProfile_pair_error (show 0 < (4 : ℝ) ^ n * X by positivity)
  rw [fourProfile_pow hX n,
    show (4 : ℝ) ^ n * X / 2 = (4 : ℝ) ^ n * (X / 2) by ring,
    fourProfile_pow (show 0 < X / 2 by positivity) n] at hb
  have hsmall : 1 / (4 * ((4 : ℝ) ^ n * X)) <
      |fourProfile X + fourProfile (X / 2) - 1 / 2| := by
    apply (div_lt_iff₀ (by positivity : 0 < 4 * ((4 : ℝ) ^ n * X))).mpr
    have hn' := (div_lt_iff₀ (by positivity :
      0 < 4 * X * |fourProfile X + fourProfile (X / 2) - 1 / 2|)).mp hn
    nlinarith only [hn']
  exact (lt_irrefl _ (hb.trans_lt hsmall))

theorem fourProfile_le_half {X : ℝ} (hX : 0 < X) : fourProfile X ≤ 1 / 2 := by
  have h := fourProfile_half hX
  have hn := fourProfile_nonneg (show 0 < X / 2 by positivity)
  linarith only [h, hn]

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount
