import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.SmoothPrimeCollisionClasses

/-!
# Cumulative smooth-times-prime energy and integer cutoffs

For fixed balanced rows with gcd `g`, only differences divisible by `g`
contribute, each with at most `g` column pairs. Summing to `H` costs at most
`g * floor(H/g) <= H`. The full smooth-times-prime energy is consequently
at most its exact diagonal plus `2 * floor(4*X^2*delta) * card(rows)^2`.
The floor cutoff also retains the exact gcd classes, and yields purely
diagonal energy at height resolution `1/T` when `T > 4*X^2`.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open GaloisForLFunctions.Goldbach


/-- Summing compatible differences cancels the fixed-row gcd cost exactly. -/
theorem cumulative_balanced_collision_fiber_le {X : ℕ} (m₁ m₂ : Fin X) (H : ℕ) :
    (∑ h ∈ Icc 1 H, (balancedProductCollisionFiber m₁ m₂ h).card) ≤ H := by
  let g := Nat.gcd (balancedIntervalValue m₁) (balancedIntervalValue m₂)
  have hcard : ((Icc 1 H).filter fun h => g ∣ h).card = H / g := by
    have he : Icc 1 H = Ioc 0 H := by
      ext h
      simp only [mem_Icc, mem_Ioc]
      omega
    rw [he]
    exact Nat.Ioc_filter_dvd_card_eq_div H g
  calc
    _ ≤ ∑ h ∈ Icc 1 H, if g ∣ h then g else 0 :=
      sum_le_sum fun h _ => card_balancedProductCollisionFiber_le_gcd_gate m₁ m₂ h
    _ = g * (H / g) := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, hcard, Nat.cast_id]
      ring
    _ ≤ H := Nat.mul_div_le H g

/-- The actual smooth-times-prime cumulative count loses no divisor sum. -/
theorem cumulative_smooth_prime_collision_le (X y H : ℕ) :
    (∑ h ∈ Icc 1 H, smoothPrimeCollisionCount X y h) ≤ H * (smoothRows X y).card ^ 2 := by
  have hrow (m₁ m₂ : Fin X) :
      (∑ h ∈ Icc 1 H, (smoothPrimeCollisionFiber y m₁ m₂ h).card) ≤ H := by
    apply le_trans _ (cumulative_balanced_collision_fiber_le m₁ m₂ H)
    apply sum_le_sum
    intro h _
    apply card_le_card
    intro p hp
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩
  calc
    _ = ∑ m₁ ∈ smoothRows X y, ∑ m₂ ∈ smoothRows X y,
        ∑ h ∈ Icc 1 H, (smoothPrimeCollisionFiber y m₁ m₂ h).card := by
      unfold smoothPrimeCollisionCount
      rw [sum_comm]
      apply sum_congr rfl
      intro m₁ _
      rw [sum_comm]
    _ ≤ ∑ _m₁ ∈ smoothRows X y, ∑ _m₂ ∈ smoothRows X y, H :=
      sum_le_sum fun m₁ _ => sum_le_sum fun m₂ _ => hrow m₁ m₂
    _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]; ring

private theorem nat_gap_le_of_log_gap {a b : ℕ} (ha : 0 < a) (hab : a < b)
    {δ : ℝ} (hlog : Real.log (b : ℝ) - Real.log (a : ℝ) ≤ δ) :
    ((b - a : ℕ) : ℝ) ≤ (b : ℝ) * δ := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast ha.trans hab
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hbR haR)
  rw [Real.log_div hbR.ne' haR.ne', inv_div] at hl
  have he : 1 - (a : ℝ) / b = ((b : ℝ) - a) / b := by field_simp
  rw [he] at hl
  have h := (div_le_iff₀ hbR).mp (hl.trans hlog)
  rw [Nat.cast_sub hab.le]
  simpa only [mul_comm] using h

private theorem balanced_product_le (X : ℕ) (m p : Fin X) :
    (balancedIntervalValue m * balancedIntervalValue p : ℕ) ≤ 4 * X ^ 2 := by
  have h := Nat.mul_le_mul (balancedIntervalValue_le m) (balancedIntervalValue_le p)
  calc
    _ ≤ (2 * X) * (2 * X) := h
    _ = _ := by ring

private theorem upperLogFiber_le_floor_sum {X y : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (m₁ m₂ : Fin X) :
    (smoothPrimeUpperLogFiber y m₁ m₂ δ).card ≤
      ∑ h ∈ Icc 1 ⌊4 * (X : ℝ) ^ 2 * δ⌋₊, (smoothPrimeCollisionFiber y m₁ m₂ h).card := by
  have hsub : smoothPrimeUpperLogFiber y m₁ m₂ δ ⊆
      (Icc 1 ⌊4 * (X : ℝ) ^ 2 * δ⌋₊).biUnion (fun h => smoothPrimeCollisionFiber y m₁ m₂ h) := by
    intro p hp
    obtain ⟨hpCols, hlt, hlog⟩ := mem_filter.mp hp
    let a := balancedIntervalValue m₁ * balancedIntervalValue p.1
    let b := balancedIntervalValue m₂ * balancedIntervalValue p.2
    have ha : 0 < a := Nat.mul_pos (balancedIntervalValue_pos m₁) (balancedIntervalValue_pos p.1)
    have hb : (b : ℝ) ≤ 4 * (X : ℝ) ^ 2 := by exact_mod_cast balanced_product_le X m₂ p.2
    have hgap : ((b - a : ℕ) : ℝ) ≤ 4 * (X : ℝ) ^ 2 * δ :=
      (nat_gap_le_of_log_gap ha hlt hlog).trans (mul_le_mul_of_nonneg_right hb hδ)
    have hNat : b - a ≤ ⌊4 * (X : ℝ) ^ 2 * δ⌋₊ := Nat.le_floor hgap
    apply mem_biUnion.mpr
    refine ⟨b - a, mem_Icc.mpr ⟨by omega, hNat⟩, mem_filter.mpr ⟨hpCols, ?_⟩⟩
    change a + (b - a) = b
    omega
  exact (card_le_card hsub).trans card_biUnion_le

/-- A logarithmic collision fibre is bounded by its integral product-difference width. -/
theorem smoothPrimeUpperLogFiber_le_floor {X : ℕ} (y : ℕ) (m₁ m₂ : Fin X)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (smoothPrimeUpperLogFiber y m₁ m₂ δ).card ≤ ⌊4 * (X : ℝ) ^ 2 * δ⌋₊ := by
  apply (upperLogFiber_le_floor_sum hδ m₁ m₂).trans
  apply le_trans _ (cumulative_balanced_collision_fiber_le m₁ m₂ _)
  apply sum_le_sum
  intro h _
  apply card_le_card
  intro p hp
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩

/-- Integer differences in the logarithmic window stop at the floor of its real width. -/
theorem smoothPrimeUpperLogCount_le_floor_sum (X y : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    smoothPrimeUpperLogCount X y δ ≤
      ∑ h ∈ Icc 1 ⌊4 * (X : ℝ) ^ 2 * δ⌋₊, smoothPrimeCollisionCount X y h := by
  calc
    _ ≤ ∑ m₁ ∈ smoothRows X y, ∑ m₂ ∈ smoothRows X y,
        ∑ h ∈ Icc 1 ⌊4 * (X : ℝ) ^ 2 * δ⌋₊, (smoothPrimeCollisionFiber y m₁ m₂ h).card :=
      sum_le_sum fun m₁ _ => sum_le_sum fun m₂ _ => upperLogFiber_le_floor_sum hδ m₁ m₂
    _ = _ := by
      simp only [smoothPrimeCollisionCount]
      simp_rw [sum_comm (s := smoothRows X y) (t := Icc 1 ⌊4 * (X : ℝ) ^ 2 * δ⌋₊)]

/-- The sharp integer cutoff also retains the disjoint gcd-class arithmetic bound. -/
theorem smoothPrimeLogEnergy_le_floor_gcd_classes (X y : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    smoothPrimeLogEnergy X y δ ≤ (smoothRows X y).card * (roughPrimeColumns X y).card +
      2 * ∑ h ∈ Icc 1 ⌊4 * (X : ℝ) ^ 2 * δ⌋₊,
        ∑ d ∈ h.divisors, d * (smoothGcdRows X y h d).card ^ 2 := by
  rw [smoothPrimeLogEnergy_eq_diagonal_add_twice X y hδ]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  apply (smoothPrimeUpperLogCount_le_floor_sum X y hδ).trans
  exact sum_le_sum fun h hh => smoothPrimeCollisionCount_le_gcd_classes X y (mem_Icc.mp hh).1

/-- A uniform fine-energy envelope with no accumulated gcd or divisor loss. -/
theorem smoothPrimeLogEnergy_le_floor_envelope (X y : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    smoothPrimeLogEnergy X y δ ≤ (smoothRows X y).card * (roughPrimeColumns X y).card +
      2 * ⌊4 * (X : ℝ) ^ 2 * δ⌋₊ * (smoothRows X y).card ^ 2 := by
  rw [smoothPrimeLogEnergy_eq_diagonal_add_twice X y hδ]
  have h := (smoothPrimeUpperLogCount_le_floor_sum X y hδ).trans
    (cumulative_smooth_prime_collision_le X y ⌊4 * (X : ℝ) ^ 2 * δ⌋₊)
  calc
    _ ≤ (smoothRows X y).card * (roughPrimeColumns X y).card +
        2 * (⌊4 * (X : ℝ) ^ 2 * δ⌋₊ * (smoothRows X y).card ^ 2) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 2 h) _
    _ = _ := by ring

/-- The cumulative incidence envelope at height resolution `1/T`. -/
theorem smoothPrimeLogEnergy_le_floor_at_height (X y : ℕ) {T : ℝ} (hT : 0 < T) :
    smoothPrimeLogEnergy X y (1 / T) ≤ (smoothRows X y).card * (roughPrimeColumns X y).card +
      2 * ⌊4 * (X : ℝ) ^ 2 / T⌋₊ * (smoothRows X y).card ^ 2 := by
  simpa only [mul_one_div] using smoothPrimeLogEnergy_le_floor_envelope X y (by positivity : 0 ≤ 1 / T)

/-- Above inverse-product resolution the actual smooth-times-prime energy is exactly diagonal. -/
theorem smoothPrimeLogEnergy_eq_diagonal_of_height (X y : ℕ) {T : ℝ}
    (hT : 4 * (X : ℝ) ^ 2 < T) :
    smoothPrimeLogEnergy X y (1 / T) = (smoothRows X y).card * (roughPrimeColumns X y).card := by
  have hT0 : 0 < T := lt_of_le_of_lt (by positivity) hT
  have hδ : 0 ≤ 1 / T := by positivity
  have hlt : 4 * (X : ℝ) ^ 2 * (1 / T) < 1 := by
    rw [mul_one_div]
    exact (div_lt_one hT0).mpr hT
  have hfloor : ⌊4 * (X : ℝ) ^ 2 * (1 / T)⌋₊ = 0 := Nat.floor_eq_zero.mpr hlt
  have hbound := smoothPrimeLogEnergy_le_floor_envelope X y hδ
  rw [hfloor, mul_zero, zero_mul, add_zero] at hbound
  apply Nat.le_antisymm hbound
  rw [smoothPrimeLogEnergy_eq_diagonal_add_twice X y hδ]
  exact Nat.le_add_right _ _

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
