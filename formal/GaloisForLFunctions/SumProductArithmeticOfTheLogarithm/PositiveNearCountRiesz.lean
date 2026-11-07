import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCountEstimate
import GaloisForLFunctions.RHTower.LayerCakeZeroCount

/-!
# Sharp logarithmic averaged deficit

For the odd-prime system with extra norms three and four, the first Riesz
count R(X) is the integral of its actual generalized-integer count. For X ≥ 1,

  X log X / (12 log 3) ≤ X²/2 − R(X)
    ≤ (2/3) X (log X/log 3 + 1) + X/2.

Odd-integer midpoint rounding and the omitted norm-four geometric tail give
a deficit between X/12 and 2X/3 at each retained norm-three exponent.
Summing these exponents gives the exact logarithmic order. This is an
averaged count estimate; the pointwise count error remains a separate question.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount

/-- The first Riesz count sums the distance of each generalized-integer norm below X. -/
def rieszCount (X : ℝ) : ℝ :=
  ∑ g ∈ (isDiscrete X).toFinset, (X - system.intNorm g)

/-- The norm-ball coordinate bijection preserves every weighted summand. -/
private theorem riesz_coordinates (X : ℝ) :
    rieszCount X = ∑ v ∈ (tripleSet_finite X).toFinset,
      (X - (v.1 : ℝ) * 3 ^ v.2.1 * 4 ^ v.2.2) := by
  have him : (isDiscrete X).toFinset.image coordinates =
      (tripleSet_finite X).toFinset := by
    ext v
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    rw [tripleSet_eq_image]
    rfl
  rw [rieszCount, ← him, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro g _
    rw [intNorm_coordinates]
  · intro g _ g' _ he
    exact coordinates_injective he

/-- Finite exponent fibres with their odd-integer coordinate retained. -/
private def fibres (X : ℝ) (A B : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (A + 1) ×ˢ Finset.range (B + 1)).biUnion fun ab =>
    (oddIntegers (X / ((3 : ℝ) ^ ab.1 * 4 ^ ab.2))).image fun u => (u, ab)

/-- The two exponent coordinates separate the finite fibres. -/
private theorem disjoint_fibres (X : ℝ) (A B : ℕ) :
    ((Finset.range (A + 1) ×ˢ Finset.range (B + 1) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun ab => (oddIntegers (X / ((3 : ℝ) ^ ab.1 * 4 ^ ab.2))).image fun u => (u, ab)) := by
  intro ab _ cd _ hne
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hv
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hw
  exact hne (congrArg Prod.snd (hu.trans hw.symm))

/-- The cardinality of the disjoint fibre union is the rectangular count sum. -/
private theorem card_fibres (X : ℝ) (A B : ℕ) :
    (fibres X A B).card =
      ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
        (oddIntegers (X / ((3 : ℝ) ^ a * 4 ^ b))).card := by
  rw [fibres, Finset.card_biUnion (disjoint_fibres X A B), Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.card_image_of_injective _ (fun u v huv => congrArg Prod.fst huv)

/-- The fibre union is the full coordinate ball, by containment and equal cardinality. -/
private theorem fibres_eq {X : ℝ} (hX : 0 ≤ X) (A B : ℕ)
    (hA : X < (3 : ℝ) ^ (A + 1)) (hB : X < (4 : ℝ) ^ (B + 1)) :
    fibres X A B = (tripleSet_finite X).toFinset := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨ab, _, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    have hd : 0 < (3 : ℝ) ^ ab.1 * 4 ^ ab.2 := by positivity
    obtain ⟨huo, huX⟩ := (mem_oddIntegers (div_nonneg hX hd.le) u).mp hu
    apply (tripleSet_finite X).mem_toFinset.mpr
    refine ⟨huo, ?_⟩
    simpa only [mul_assoc] using (le_div_iff₀ hd).mp huX
  · have hc := countBall_eq_rectangle_sum hX A B hA hB
    rw [countBall_eq_ncard_triples, ← card_fibres] at hc
    rw [Set.ncard_eq_toFinset_card _ (tripleSet_finite X)] at hc
    exact hc.le

/-- The actual weighted norm count is the corresponding finite sum over fibres. -/
private theorem riesz_rectangle {X : ℝ} (hX : 0 ≤ X) (A B : ℕ)
    (hA : X < (3 : ℝ) ^ (A + 1)) (hB : X < (4 : ℝ) ^ (B + 1)) :
    rieszCount X = ∑ a ∈ Finset.range (A + 1), ∑ b ∈ Finset.range (B + 1),
      ∑ u ∈ oddIntegers (X / ((3 : ℝ) ^ a * 4 ^ b)),
        (X - (u : ℝ) * (3 : ℝ) ^ a * 4 ^ b) := by
  rw [riesz_coordinates, ← fibres_eq hX A B hA hB,
    fibres, Finset.sum_biUnion (disjoint_fibres X A B), Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_image]
  intro u _ v _ he
  exact congrArg Prod.fst he

/-- The first Riesz count of the positive odd integers. -/
private def oddRiesz (Y : ℝ) : ℝ := ∑ u ∈ oddIntegers Y, (Y - u)

/-- The first J positive odd integers sum to J squared. -/
private theorem sum_odds (J : ℕ) : (∑ j ∈ Finset.range J, (2 * j + 1 : ℝ)) = (J : ℝ) ^ 2 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The weighted odd count is J times the endpoint minus J squared. -/
private theorem oddRiesz_eq (Y : ℝ) :
    oddRiesz Y = (⌊(Y + 1) / 2⌋₊ : ℝ) * Y - (⌊(Y + 1) / 2⌋₊ : ℝ) ^ 2 := by
  rw [oddRiesz, oddIntegers, Finset.sum_image]
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sum_odds]
  · intro a _ b _ he
    change 2 * a + 1 = 2 * b + 1 at he
    omega

/-- Odd-integer midpoint rounding has a nonnegative deficit at most one quarter. -/
private theorem oddRiesz_error {Y : ℝ} (hY : 0 ≤ Y) :
    0 ≤ Y ^ 2 / 4 - oddRiesz Y ∧ Y ^ 2 / 4 - oddRiesz Y ≤ 1 / 4 := by
  have h := odd_count_error hY
  rw [card_oddIntegers] at h
  let e := (⌊(Y + 1) / 2⌋₊ : ℝ) - Y / 2
  have he : -(1 / 2 : ℝ) ≤ e ∧ e ≤ 1 / 2 := abs_le.mp h
  have hid : Y ^ 2 / 4 - oddRiesz Y = e ^ 2 := by
    rw [oddRiesz_eq]
    dsimp only [e]
    ring
  rw [hid]
  refine ⟨sq_nonneg e, ?_⟩
  have hp := mul_nonneg (sub_nonneg.mpr he.2) (show 0 ≤ e + 1 / 2 by linarith only [he.1])
  nlinarith only [hp]

/-- An endpoint below one contains no positive odd integer. -/
private theorem oddRiesz_zero {Y : ℝ} (hY : Y < 1) : oddRiesz Y = 0 := by
  have hJ : ⌊(Y + 1) / 2⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith only [hY])
  rw [oddRiesz_eq, hJ]
  norm_num

/-- Logarithmic floors bracket the endpoint between successive powers. -/
private theorem power_cutoffs {b X : ℝ} (hb : 1 < b) (hX : 1 ≤ X) :
    b ^ ⌊Real.log X / Real.log b⌋₊ ≤ X ∧
    X < b ^ (⌊Real.log X / Real.log b⌋₊ + 1) ∧
    (⌊Real.log X / Real.log b⌋₊ : ℝ) ≤ Real.log X / Real.log b := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hx0 : 0 < X := zero_lt_one.trans_le hX
  have hl : 0 < Real.log b := Real.log_pos hb
  have hr : 0 ≤ Real.log X / Real.log b := div_nonneg (Real.log_nonneg hX) hl.le
  have hlo := Nat.floor_le hr
  have hhi := Nat.lt_floor_add_one (Real.log X / Real.log b)
  refine ⟨?_, ?_, hlo⟩
  · apply (Real.log_le_log_iff (pow_pos hb0 _) hx0).mp
    rw [Real.log_pow]
    exact (le_div_iff₀ hl).mp hlo
  · apply (Real.log_lt_log_iff hx0 (pow_pos hb0 _)).mp
    rw [Real.log_pow]
    push_cast
    exact (div_lt_iff₀ hl).mp hhi

/-- The finite stack of odd-integer Riesz counts along powers of four. -/
private def fourRiesz (Y : ℝ) (B : ℕ) : ℝ :=
  ∑ b ∈ Finset.range (B + 1), (4 : ℝ) ^ b * oddRiesz (Y / (4 : ℝ) ^ b)

/-- Extending an exponent cutoff beyond the endpoint adds only zero terms. -/
private theorem fourRiesz_tail {Y : ℝ} (A B : ℕ) (hAB : A ≤ B)
    (hY : Y < (4 : ℝ) ^ (A + 1)) : fourRiesz Y B = fourRiesz Y A := by
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : A + 1 ≤ B + 1))
  intro b hb hba
  have hab : A + 1 ≤ b := by simpa only [Finset.mem_range, not_lt] using hba
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hab
  have hz : oddRiesz (Y / (4 : ℝ) ^ b) = 0 := by
    apply oddRiesz_zero
    exact (div_lt_one (by positivity : 0 < (4 : ℝ) ^ b)).mpr (hY.trans_le hpow)
  rw [hz, mul_zero]

/-- Summing the norm-four geometric main terms gives coefficient one third. -/
private theorem four_main (Y : ℝ) (B : ℕ) :
    (∑ b ∈ Finset.range (B + 1), Y ^ 2 / (4 * (4 : ℝ) ^ b)) =
      Y ^ 2 / 3 * (1 - (1 / 4 : ℝ) ^ (B + 1)) := by
  have he : (∑ b ∈ Finset.range (B + 1), Y ^ 2 / (4 * (4 : ℝ) ^ b)) =
      Y ^ 2 / 4 * ∑ b ∈ Finset.range (B + 1), (1 / 4 : ℝ) ^ b := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [div_pow, one_pow]
    ring
  rw [he, geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
  norm_num
  ring

/-- The finite norm-four stack has nonnegative error bounded by the sum of its rounding scales. -/
private theorem four_finite_error {Y : ℝ} (hY : 0 ≤ Y) (B : ℕ) :
    0 ≤ Y ^ 2 / 3 * (1 - (1 / 4 : ℝ) ^ (B + 1)) - fourRiesz Y B ∧
    Y ^ 2 / 3 * (1 - (1 / 4 : ℝ) ^ (B + 1)) - fourRiesz Y B ≤
      ((4 : ℝ) ^ (B + 1) - 1) / 12 := by
  have hterm (b : ℕ) :
      0 ≤ Y ^ 2 / (4 * (4 : ℝ) ^ b) - (4 : ℝ) ^ b * oddRiesz (Y / (4 : ℝ) ^ b) ∧
      Y ^ 2 / (4 * (4 : ℝ) ^ b) - (4 : ℝ) ^ b * oddRiesz (Y / (4 : ℝ) ^ b) ≤
        (4 : ℝ) ^ b / 4 := by
    have hp : 0 < (4 : ℝ) ^ b := by positivity
    have he := oddRiesz_error (Y := Y / (4 : ℝ) ^ b) (by positivity)
    have hid : (4 : ℝ) ^ b * ((Y / (4 : ℝ) ^ b) ^ 2 / 4 -
        oddRiesz (Y / (4 : ℝ) ^ b)) =
        Y ^ 2 / (4 * (4 : ℝ) ^ b) - (4 : ℝ) ^ b * oddRiesz (Y / (4 : ℝ) ^ b) := by
      field_simp
    constructor
    · rw [← hid]
      exact mul_nonneg hp.le he.1
    · rw [← hid]
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left he.2 hp.le
  have hlo := Finset.sum_nonneg (s := Finset.range (B + 1)) (fun b _ => (hterm b).1)
  have hhi := Finset.sum_le_sum (s := Finset.range (B + 1)) (fun b _ => (hterm b).2)
  simp only [Finset.sum_sub_distrib, four_main] at hlo hhi
  refine ⟨hlo, ?_⟩
  have hsum : (∑ b ∈ Finset.range (B + 1), (4 : ℝ) ^ b / 4) =
      ((4 : ℝ) ^ (B + 1) - 1) / 12 := by
    rw [← Finset.sum_div, geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1)]
    norm_num
    ring
  rwa [hsum] at hhi

/-- The omitted geometric tail forces a deficit between Y/12 and 2Y/3 in the norm-four stack. -/
private theorem fourRiesz_bound {Y : ℝ} (hY : 1 ≤ Y) (B : ℕ)
    (hB : Y < (4 : ℝ) ^ (B + 1)) :
    Y / 12 ≤ Y ^ 2 / 3 - fourRiesz Y B ∧
      Y ^ 2 / 3 - fourRiesz Y B ≤ 2 * Y / 3 := by
  let C := ⌊Real.log Y / Real.log 4⌋₊
  obtain ⟨hClo, hChi, _⟩ := power_cutoffs (by norm_num : (1 : ℝ) < 4) hY
  change (4 : ℝ) ^ C ≤ Y at hClo
  change Y < (4 : ℝ) ^ (C + 1) at hChi
  have hCB : C ≤ B := by
    by_contra hh
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (show B + 1 ≤ C by omega)
    exact (not_le_of_gt hB) (hp.trans hClo)
  rw [fourRiesz_tail C B hCB hChi]
  have he := four_finite_error (zero_le_one.trans hY) C
  have htail : Y / 12 ≤ Y ^ 2 / 3 * (1 / 4 : ℝ) ^ (C + 1) ∧
      Y ^ 2 / 3 * (1 / 4 : ℝ) ^ (C + 1) ≤ Y / 3 := by
    constructor
    · have hP : (4 : ℝ) ^ (C + 1) ≤ 4 * Y := by
        rw [pow_succ]
        linarith only [hClo]
      have hm := mul_le_mul_of_nonneg_left hP (zero_le_one.trans hY)
      rw [div_pow, one_pow]
      have hid : Y ^ 2 / 3 * (1 / (4 : ℝ) ^ (C + 1)) =
          Y ^ 2 / (3 * (4 : ℝ) ^ (C + 1)) := by ring
      rw [hid]
      apply (le_div_iff₀ (by positivity : 0 < 3 * (4 : ℝ) ^ (C + 1))).mpr
      nlinarith only [hm]
    · have hdiv : Y / (4 : ℝ) ^ (C + 1) ≤ 1 :=
        (div_le_one (by positivity : 0 < (4 : ℝ) ^ (C + 1))).mpr hChi.le
      have hm := mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ Y / 3)
      rw [div_pow, one_pow]
      calc
        _ = (Y / 3) * (Y / (4 : ℝ) ^ (C + 1)) := by ring
        _ ≤ Y / 3 := by simpa only [mul_one] using hm
  have hround : ((4 : ℝ) ^ (C + 1) - 1) / 12 ≤ Y / 3 := by
    rw [pow_succ]
    linarith only [hClo]
  constructor <;> nlinarith only [he.1, he.2, htail.1, htail.2, hround]

/-- Regroup the actual Riesz count by its norm-three exponent. -/
private theorem riesz_by_three {X : ℝ} (hX : 0 ≤ X) (A B : ℕ)
    (hA : X < (3 : ℝ) ^ (A + 1)) (hB : X < (4 : ℝ) ^ (B + 1)) :
    rieszCount X = ∑ a ∈ Finset.range (A + 1),
      (3 : ℝ) ^ a * fourRiesz (X / (3 : ℝ) ^ a) B := by
  rw [riesz_rectangle hX A B hA hB]
  apply Finset.sum_congr rfl
  intro a _
  rw [fourRiesz, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [oddRiesz, Finset.mul_sum, Finset.mul_sum]
  simp only [div_mul_eq_div_div]
  apply Finset.sum_congr rfl
  intro u _
  field_simp

/-- The outer geometric sum gives leading coefficient one half. -/
private theorem three_main (X : ℝ) (A : ℕ) :
    (∑ a ∈ Finset.range (A + 1), X ^ 2 / (3 * (3 : ℝ) ^ a)) =
      X ^ 2 / 2 * (1 - (1 / 3 : ℝ) ^ (A + 1)) := by
  have he : (∑ a ∈ Finset.range (A + 1), X ^ 2 / (3 * (3 : ℝ) ^ a)) =
      X ^ 2 / 3 * ∑ a ∈ Finset.range (A + 1), (1 / 3 : ℝ) ^ a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [div_pow, one_pow]
    ring
  rw [he, geom_sum_eq (by norm_num : (1 / 3 : ℝ) ≠ 1)]
  norm_num
  ring

/-- Every retained norm-three exponent costs between X/12 and 2X/3 in the Riesz deficit. -/
private theorem riesz_exponent_bound {X : ℝ} (hX : 1 ≤ X) (A B : ℕ)
    (hAlo : (3 : ℝ) ^ A ≤ X) (hAhi : X < (3 : ℝ) ^ (A + 1))
    (hB : X < (4 : ℝ) ^ (B + 1)) :
    ((A + 1 : ℕ) : ℝ) * (X / 12) ≤ X ^ 2 / 2 - rieszCount X ∧
      X ^ 2 / 2 - rieszCount X ≤ ((A + 1 : ℕ) : ℝ) * (2 * X / 3) + X / 2 := by
  have hterm (a : ℕ) (ha : a ∈ Finset.range (A + 1)) :
      X / 12 ≤ X ^ 2 / (3 * (3 : ℝ) ^ a) -
        (3 : ℝ) ^ a * fourRiesz (X / (3 : ℝ) ^ a) B ∧
      X ^ 2 / (3 * (3 : ℝ) ^ a) -
        (3 : ℝ) ^ a * fourRiesz (X / (3 : ℝ) ^ a) B ≤ 2 * X / 3 := by
    have hp : 0 < (3 : ℝ) ^ a := by positivity
    have haA : a ≤ A := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ha
    have hpa : (3 : ℝ) ^ a ≤ X :=
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) haA).trans hAlo
    have hy1 : 1 ≤ X / (3 : ℝ) ^ a := (one_le_div hp).mpr hpa
    have hyX : X / (3 : ℝ) ^ a ≤ X := by
      apply (div_le_iff₀ hp).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3) : (1 : ℝ) ≤ 3 ^ a)
        (zero_le_one.trans hX)
    have he := fourRiesz_bound hy1 B (hyX.trans_lt hB)
    have hid : (3 : ℝ) ^ a * ((X / (3 : ℝ) ^ a) ^ 2 / 3 -
        fourRiesz (X / (3 : ℝ) ^ a) B) = X ^ 2 / (3 * (3 : ℝ) ^ a) -
        (3 : ℝ) ^ a * fourRiesz (X / (3 : ℝ) ^ a) B := by
      field_simp
    constructor
    · rw [← hid]
      calc
        X / 12 = (3 : ℝ) ^ a * ((X / (3 : ℝ) ^ a) / 12) := by field_simp
        _ ≤ (3 : ℝ) ^ a * ((X / (3 : ℝ) ^ a) ^ 2 / 3 -
            fourRiesz (X / (3 : ℝ) ^ a) B) := mul_le_mul_of_nonneg_left he.1 hp.le
    · rw [← hid]
      have hh := mul_le_mul_of_nonneg_left he.2 hp.le
      calc
        _ ≤ (3 : ℝ) ^ a * (2 * (X / (3 : ℝ) ^ a) / 3) := hh
        _ = 2 * X / 3 := by field_simp
  have hlo := Finset.sum_le_sum (s := Finset.range (A + 1)) (fun a ha => (hterm a ha).1)
  have hhi := Finset.sum_le_sum (s := Finset.range (A + 1)) (fun a ha => (hterm a ha).2)
  have hr := riesz_by_three (zero_le_one.trans hX) A B hAhi hB
  simp only [Finset.sum_sub_distrib, three_main, ← hr,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlo hhi
  have htail : 0 ≤ X ^ 2 / 2 * (1 / 3 : ℝ) ^ (A + 1) ∧
      X ^ 2 / 2 * (1 / 3 : ℝ) ^ (A + 1) ≤ X / 2 := by
    constructor
    · positivity
    · have hd : X / (3 : ℝ) ^ (A + 1) ≤ 1 :=
        (div_le_one (by positivity : 0 < (3 : ℝ) ^ (A + 1))).mpr hAhi.le
      have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ X / 2)
      rw [div_pow, one_pow]
      calc
        _ = (X / 2) * (X / (3 : ℝ) ^ (A + 1)) := by ring
        _ ≤ X / 2 := by simpa only [mul_one] using hm
  constructor <;> nlinarith only [hlo, hhi, htail.1, htail.2]

/-- The actual Riesz deficit has order X log X, with explicit bounds for every X at least one. -/
theorem riesz_log_bound {X : ℝ} (hX : 1 ≤ X) :
    X * Real.log X / (12 * Real.log 3) ≤ X ^ 2 / 2 - rieszCount X ∧
      X ^ 2 / 2 - rieszCount X ≤
        (2 / 3 : ℝ) * X * (Real.log X / Real.log 3 + 1) + X / 2 := by
  let A := ⌊Real.log X / Real.log 3⌋₊
  let B := ⌊Real.log X / Real.log 4⌋₊
  obtain ⟨hAlo, hAhi, hA⟩ := power_cutoffs (by norm_num : (1 : ℝ) < 3) hX
  obtain ⟨_, hBhi, _⟩ := power_cutoffs (by norm_num : (1 : ℝ) < 4) hX
  have h := riesz_exponent_bound hX A B hAlo hAhi hBhi
  have hlow : Real.log X / Real.log 3 ≤ ((A + 1 : ℕ) : ℝ) := by
    have hh := (Nat.lt_floor_add_one (Real.log X / Real.log 3)).le
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  refine ⟨?_, ?_⟩
  · calc
      _ = (Real.log X / Real.log 3) * (X / 12) := by ring
      _ ≤ ((A + 1 : ℕ) : ℝ) * (X / 12) :=
        mul_le_mul_of_nonneg_right hlow (by positivity)
      _ ≤ _ := h.1
  · have hsize : ((A + 1 : ℕ) : ℝ) ≤ Real.log X / Real.log 3 + 1 := by
      push_cast
      change (A : ℝ) ≤ Real.log X / Real.log 3 at hA
      linarith only [hA]
    have hm := mul_le_mul_of_nonneg_right hsize (by positivity : 0 ≤ 2 * X / 3)
    nlinarith only [h.2, hm]

open MeasureTheory intervalIntegral

/-- The weighted norm count is the integral of the actual counting function, including multiplicities. -/
theorem rieszCount_eq_integral_count {X : ℝ} (hX : 0 ≤ X) :
    rieszCount X = ∫ t in (0 : ℝ)..X, (system.countBall t : ℝ) := by
  let S := (isDiscrete X).toFinset
  have hcard (t : ℝ) (ht : t ≤ X) :
      (system.countBall t : ℝ) = ∑ g ∈ S, (if t < system.intNorm g then (0 : ℝ) else 1) := by
    have hset : (S.filter (fun g => system.intNorm g ≤ t) : Set system.Integer) =
        {g | system.intNorm g ≤ t} := by
      ext g
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq]
      change (g ∈ (isDiscrete X).toFinset ∧ system.intNorm g ≤ t) ↔ system.intNorm g ≤ t
      rw [(isDiscrete X).mem_toFinset]
      change (system.intNorm g ≤ X ∧ system.intNorm g ≤ t) ↔ system.intNorm g ≤ t
      exact ⟨And.right, fun hg => ⟨hg.trans ht, hg⟩⟩
    have he : system.countBall t = (S.filter (fun g => system.intNorm g ≤ t)).card := by
      rw [← Set.ncard_coe_finset, hset]
      rfl
    rw [he, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro g _
    by_cases hh : t < system.intNorm g
    · simp only [hh, not_le_of_gt hh, if_true, if_false]
    · simp only [hh, not_lt.mp hh, if_true, if_false]
  have hif (b t : ℝ) : (if t < b then (0 : ℝ) else 1) =
      1 - (if t < b then (1 : ℝ) else 0) := by
    by_cases h : t < b <;> simp only [h, if_true, if_false] <;> norm_num
  have hi (g : system.Integer) : IntervalIntegrable
      (fun t : ℝ => 1 - (if t < system.intNorm g then (1 : ℝ) else 0)) volume 0 X :=
    intervalIntegrable_const.sub (RHTower.intervalIntegrable_indicator_lt _ _ _)
  have hc : (∫ t in (0 : ℝ)..X, (system.countBall t : ℝ)) =
      ∫ t in (0 : ℝ)..X, ∑ g ∈ S,
        (1 - (if t < system.intNorm g then (1 : ℝ) else 0)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    dsimp only
    rw [hcard t ht.2]
    apply Finset.sum_congr rfl
    intro g _
    exact hif _ _
  rw [hc, intervalIntegral.integral_finsetSum (fun g _ => hi g)]
  change (∑ g ∈ S, (X - system.intNorm g)) = _
  apply Finset.sum_congr rfl
  intro g hg
  have hgX : system.intNorm g ≤ X := (isDiscrete X).mem_toFinset.mp hg
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (RHTower.intervalIntegrable_indicator_lt _ _ _),
    RHTower.integral_indicator_lt (system.intNorm_pos g).le hgX]
  simp

/-- The integrated counting deficit has logarithmic order after normalization by X. -/
theorem integral_count_deficit {X : ℝ} (hX : 1 ≤ X) :
    X * Real.log X / (12 * Real.log 3) ≤ X ^ 2 / 2 - (∫ t in (0 : ℝ)..X, (system.countBall t : ℝ)) ∧
      X ^ 2 / 2 - (∫ t in (0 : ℝ)..X, (system.countBall t : ℝ)) ≤
        (2 / 3 : ℝ) * X * (Real.log X / Real.log 3 + 1) + X / 2 := by
  rw [← rieszCount_eq_integral_count (zero_le_one.trans hX)]
  exact riesz_log_bound hX

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PositiveNearCount

