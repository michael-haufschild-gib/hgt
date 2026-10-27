import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.LogCellsFixTheGauge

/-!
# The cell-holonomy defect counts charged cells

The dyadic cell dilation `M_2` spreads the point mass at `a` over the two cells `2a, 2a + 1`. For a
gauge `ω` and a scalar `c`, the failure of covariance on the horizon `[1, X]` is measured by the
Hilbert–Schmidt defect

`Def_X(ω, c) = Σ_{a=1}^{X} Σ_n |(U_ω M_2 δ_a − c M_2 U_ω δ_a)(n)|²
             = Σ_{a=1}^{X} (|χ(2a) − cχ(a)|² + |χ(2a + 1) − cχ(a)|²)`

(`hsDefect_eq`). For a real sign gauge `σ` the first term is `(σ(2) − c)²` and the second
`(σ(a)σ(2a + 1) − c)²`. Call the cell `a` *charged* when `σ(a)σ(2a + 1) ≠ σ(2)`.

* **Lower bound** (`hsDefect_ge_charged`): for every `c`, `Def_X(σ, c) ≥ 2 · #(charged cells)`.
* **Vanishing** (`exists_hsDefect_eq_zero_iff`): some `c` makes the defect vanish iff no cell is
  charged.
* **Liouville** (`hsDefect_liouville_sandwich`): at `σ = λ`, `σ(2) = −1`, so the charged cells are
  the `a` with `λ(a) = λ(2a + 1)`; the minimal defect lies between `2N₊` and `4N₊`, with
  `N₊ = #{a ≤ X : λ(a) = λ(2a + 1)}`, and `N₊ ≥ 1` once `X ≥ 2` (`one_le_liouvilleAgreements`).

So the quantitative cell holonomy at the Liouville gauge is the correlation of `λ` along the affine
map `a ↦ 2a + 1`: lower bounds for the gauge-fixing power of cells are binary correlation bounds
for `λ` along `(+1, ×2)`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open BiarithmeticGaugeGeometry

/-- The point mass at `a`. -/
def pointMass (a : ℕ) : ℕ → ℂ := fun n => if n = a then 1 else 0

/-- The Hilbert–Schmidt defect of covariance of the dyadic cell dilation on `[1, X]`. -/
def hsDefect (ω : PrimeGauge) (X : ℕ) (c : ℂ) : ℝ :=
  ∑ a ∈ Icc 1 X, ∑ n ∈ range (2 * X + 2),
    ‖gaugeTwist ω (cellDilate 2 (pointMass a)) n -
      c * cellDilate 2 (gaugeTwist ω (pointMass a)) n‖ ^ 2

/-- The defect of one cell `a`: only `n = 2a, 2a + 1` contribute. -/
theorem hsDefect_cell (ω : PrimeGauge) {X a : ℕ} (ha : a ≤ X) (c : ℂ) :
    ∑ n ∈ range (2 * X + 2),
      ‖gaugeTwist ω (cellDilate 2 (pointMass a)) n -
      c * cellDilate 2 (gaugeTwist ω (pointMass a)) n‖ ^ 2
      = ‖ω.gaugeChar (2 * a) - c * ω.gaugeChar a‖ ^ 2 +
        ‖ω.gaugeChar (2 * a + 1) - c * ω.gaugeChar a‖ ^ 2 := by
  have hterm : ∀ n, ‖gaugeTwist ω (cellDilate 2 (pointMass a)) n -
      c * cellDilate 2 (gaugeTwist ω (pointMass a)) n‖ ^ 2 =
        if n / 2 = a then ‖ω.gaugeChar n - c * ω.gaugeChar a‖ ^ 2 else 0 := by
    intro n
    simp only [gaugeTwist, cellDilate, pointMass]
    split_ifs with h
    · rw [h]; simp
    · simp
  rw [sum_congr rfl fun n _ => hterm n, ← sum_filter]
  have hfilt : (range (2 * X + 2)).filter (fun n => n / 2 = a) = {2 * a, 2 * a + 1} := by
    ext n
    simp only [mem_filter, mem_range, mem_insert, mem_singleton]
    omega
  rw [hfilt, sum_pair (by omega)]

/-- **The defect formula.** -/
theorem hsDefect_eq (ω : PrimeGauge) (X : ℕ) (c : ℂ) :
    hsDefect ω X c = ∑ a ∈ Icc 1 X, (‖ω.gaugeChar (2 * a) - c * ω.gaugeChar a‖ ^ 2 +
      ‖ω.gaugeChar (2 * a + 1) - c * ω.gaugeChar a‖ ^ 2) :=
  sum_congr rfl fun _ ha => hsDefect_cell ω (mem_Icc.mp ha).2 c

/-- For a real gauge and real `c`, each cell contributes `(σ(2) − c)² + (σ(a)σ(2a+1) − c)²`. -/
theorem hsDefect_realSign {ω : PrimeGauge} (hω : IsRealSignGauge ω) (X : ℕ) (c : ℝ) :
    hsDefect ω X c = ∑ a ∈ Icc 1 X, ((realSignChar ω 2 - c) ^ 2 +
      (realSignChar ω a * realSignChar ω (2 * a + 1) - c) ^ 2) := by
  rw [hsDefect_eq]
  refine sum_congr rfl fun a ha => ?_
  have ha0 : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
  have hsq := realSignChar_sq_eq_one hω ha0
  set u := realSignChar ω 2
  set v := realSignChar ω a
  set w := realSignChar ω (2 * a + 1)
  have k1 : ω.gaugeChar (2 * a) - (c : ℂ) * ω.gaugeChar a = ((u * v - c * v : ℝ) : ℂ) := by
    rw [gaugeChar_eq_realSignChar hω, gaugeChar_eq_realSignChar hω, realSignChar_mul hω]
    push_cast; ring
  have k2 : ω.gaugeChar (2 * a + 1) - (c : ℂ) * ω.gaugeChar a = ((w - c * v : ℝ) : ℂ) := by
    rw [gaugeChar_eq_realSignChar hω, gaugeChar_eq_realSignChar hω]
    push_cast; ring
  rw [k1, k2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs]
  -- Multiply by `σ(a)² = 1`.
  have e1 : (u * v - c * v) ^ 2 = (u - c) ^ 2 := by
    rw [show u * v - c * v = (u - c) * v by ring, mul_pow, hsq, mul_one]
  have e2 : (w - c * v) ^ 2 = (v * w - c) ^ 2 := by
    have : w - c * v = v * (v * w - c) := by
      rw [mul_sub, ← mul_assoc, ← sq, hsq, one_mul, mul_comm c]
    rw [this, mul_pow, hsq, one_mul]
  rw [e1, e2]

/-- A cell `a` is charged when `σ(a)σ(2a + 1) ≠ σ(2)`. -/
def chargedCells (ω : PrimeGauge) (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter fun a => realSignChar ω a * realSignChar ω (2 * a + 1) ≠ realSignChar ω 2

/-- Real sign characters take the values `±1` away from `0`. -/
theorem realSignChar_eq_one_or {ω : PrimeGauge} (hω : IsRealSignGauge ω) {n : ℕ} (hn : n ≠ 0) :
    realSignChar ω n = 1 ∨ realSignChar ω n = -1 := by
  have h := realSignChar_sq_eq_one hω hn
  have h' : (realSignChar ω n - 1) * (realSignChar ω n + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- **Each charged cell costs at least `2`, whatever the scalar.** -/
theorem hsDefect_ge_charged {ω : PrimeGauge} (hω : IsRealSignGauge ω) (X : ℕ) (c : ℝ) :
    2 * ((chargedCells ω X).card : ℝ) ≤ hsDefect ω X c := by
  rw [hsDefect_realSign hω, chargedCells, card_eq_sum_ones, Nat.cast_sum, mul_sum, sum_filter]
  refine sum_le_sum fun a ha => ?_
  have ha0 : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
  split_ifs with hch
  · -- Two values `±1` that differ: `(u − c)² + (v − c)² ≥ (u − v)²/2 = 2`.
    have h2 := realSignChar_eq_one_or hω (show (2 : ℕ) ≠ 0 by norm_num)
    have hv : realSignChar ω a * realSignChar ω (2 * a + 1) = 1 ∨
        realSignChar ω a * realSignChar ω (2 * a + 1) = -1 := by
      rcases realSignChar_eq_one_or hω ha0 with h | h <;>
        rcases realSignChar_eq_one_or hω (show 2 * a + 1 ≠ 0 by omega) with h' | h' <;>
          simp [h, h']
    norm_num
    rcases h2 with h2 | h2 <;> rcases hv with hv | hv
    · exact absurd (hv.trans h2.symm) hch
    · rw [h2, hv]; nlinarith [sq_nonneg c]
    · rw [h2, hv]; nlinarith [sq_nonneg c]
    · exact absurd (hv.trans h2.symm) hch
  · positivity

/-- **Vanishing.** Some scalar makes the defect vanish iff no cell is charged. -/
theorem exists_hsDefect_eq_zero_iff {ω : PrimeGauge} (hω : IsRealSignGauge ω) (X : ℕ) :
    (∃ c : ℝ, hsDefect ω X c = 0) ↔ chargedCells ω X = ∅ := by
  constructor
  · rintro ⟨c, hc⟩
    have h := hsDefect_ge_charged hω X c
    rw [hc] at h
    have : ((chargedCells ω X).card : ℝ) = 0 := le_antisymm (by linarith) (Nat.cast_nonneg _)
    exact card_eq_zero.mp (by exact_mod_cast this)
  · intro h
    refine ⟨realSignChar ω 2, ?_⟩
    rw [hsDefect_realSign hω]
    refine sum_eq_zero fun a ha => ?_
    have hnot : a ∉ chargedCells ω X := by rw [h]; exact Finset.notMem_empty a
    simp only [chargedCells, mem_filter, not_and, not_not] at hnot
    rw [hnot ha]
    ring

/-! ### The Liouville gauge -/

/-- The cells where `λ(a) = λ(2a + 1)`: the charged cells of the Liouville gauge. -/
def liouvilleAgreements (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter fun a =>
    realSignChar PrimeGauge.liouvilleGauge a *
      realSignChar PrimeGauge.liouvilleGauge (2 * a + 1) = 1

theorem realSignChar_liouville_prime {p : ℕ} (hp : p.Prime) :
    realSignChar PrimeGauge.liouvilleGauge p = -1 := by
  simp [realSignChar, PrimeGauge.liouvilleGauge, hp]

theorem chargedCells_liouville (X : ℕ) :
    chargedCells PrimeGauge.liouvilleGauge X = liouvilleAgreements X := by
  have hω : IsRealSignGauge PrimeGauge.liouvilleGauge := fun hp => isRealSignGauge_liouville hp
  ext a
  simp only [chargedCells, liouvilleAgreements, mem_filter, realSignChar_liouville_prime
    Nat.prime_two]
  constructor
  · rintro ⟨ha, hne⟩
    refine ⟨ha, ?_⟩
    have ha0 : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
    rcases realSignChar_eq_one_or hω ha0 with h | h <;>
      rcases realSignChar_eq_one_or hω (show 2 * a + 1 ≠ 0 by omega) with h' | h' <;>
        simp_all
  · rintro ⟨ha, h1⟩
    exact ⟨ha, by rw [h1]; norm_num⟩

/-- **The Liouville sandwich.** For every scalar the defect is at least `2N₊`, and at `c = −1` it
is exactly `4N₊`, where `N₊ = #{a ≤ X : λ(a) = λ(2a + 1)}`. -/
theorem hsDefect_liouville_sandwich (X : ℕ) :
    (∀ c : ℝ, 2 * ((liouvilleAgreements X).card : ℝ) ≤ hsDefect PrimeGauge.liouvilleGauge X c) ∧
      hsDefect PrimeGauge.liouvilleGauge X ((-1 : ℝ) : ℂ) = 4 * (liouvilleAgreements X).card := by
  have hω : IsRealSignGauge PrimeGauge.liouvilleGauge := fun hp => isRealSignGauge_liouville hp
  refine ⟨fun c => ?_, ?_⟩
  · rw [← chargedCells_liouville]; exact hsDefect_ge_charged hω X c
  · rw [hsDefect_realSign hω, realSignChar_liouville_prime Nat.prime_two, liouvilleAgreements,
      card_eq_sum_ones, Nat.cast_sum, mul_sum, sum_filter]
    refine sum_congr rfl fun a ha => ?_
    have ha0 : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
    rcases realSignChar_eq_one_or hω ha0 with h | h <;>
      rcases realSignChar_eq_one_or hω (show 2 * a + 1 ≠ 0 by omega) with h' | h' <;>
        simp [h, h'] <;> norm_num

/-- `λ(2)λ(5) = 1`: the Liouville gauge has a charged cell as soon as `X ≥ 2`. -/
theorem one_le_liouvilleAgreements {X : ℕ} (hX : 2 ≤ X) : 1 ≤ (liouvilleAgreements X).card := by
  refine card_pos.mpr ⟨2, ?_⟩
  simp only [liouvilleAgreements, mem_filter, mem_Icc]
  refine ⟨⟨by norm_num, hX⟩, ?_⟩
  rw [show 2 * 2 + 1 = 5 by rfl, realSignChar_liouville_prime Nat.prime_two,
    realSignChar_liouville_prime Nat.prime_five]
  norm_num

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
