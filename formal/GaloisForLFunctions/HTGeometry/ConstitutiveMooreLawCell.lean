import Mathlib

/-!
# Even Moore law cell: effectivity, filling memory, and positive-topology collapse

The two-dimensional Moore law cell of degree `n` has reduced chain complex `A →[n] A`, `x ↦ xⁿ`;
a degree-one boundary law `y` is filled by a degree-two class `x` exactly when `xⁿ = y`, so
`H₂ = ker [n]` measures ambiguity between fillings and `H₁ = coker [n]` measures fillability
obstruction.

Over the oriented coefficients `ℝˣ`:

* `odd_fill_existsUnique` — for odd `n` the boundary is bijective, so both law-homology groups are
  trivial;
* `even_fillable_iff`, `even_fill_eq_pair`, `even_units_pow_eq_one_iff`, `even_coker_two` — for even
  `n` a boundary is fillable iff it is positive, every fillable boundary has exactly the two
  fillings `±y^{1/n}`, the kernel is exactly `{±1}` and the cokernel has exactly the two classes
  `±1`.

Over the positive coefficients the same boundary is bijective for every `n ≥ 1`
(`positive_fill_existsUnique`), so one coefficient change simultaneously repairs the effectivity
obstruction and erases the filling memory (`positive_repairs_and_erases`), and moves the realization
fibre from empty or two-point to a singleton.
-/

namespace GaloisForLFunctions.HTGeometry

section MooreCell

variable {n : ℕ}

/-- Nonnegative reals are determined by their `n`-th powers. -/
theorem pow_left_inj_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hn0 : n ≠ 0)
    (h : a ^ n = b ^ n) : a = b := by
  have h1 : (a ^ n) ^ ((n : ℝ)⁻¹) = a := Real.pow_rpow_inv_natCast ha hn0
  have h2 : (b ^ n) ^ ((n : ℝ)⁻¹) = b := Real.pow_rpow_inv_natCast hb hn0
  rw [← h1, h, h2]

/-- **Odd degree: every oriented boundary has exactly one filling.** -/
theorem odd_fill_existsUnique (hn : Odd n) {y : ℝ} (hy : y ≠ 0) :
    ∃! x : ℝ, x ≠ 0 ∧ x ^ n = y := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine ⟨(Real.sign y) * |y| ^ ((n : ℝ)⁻¹), ⟨?_, ?_⟩, ?_⟩
  · have h1 : Real.sign y ≠ 0 := by
      rcases lt_trichotomy y 0 with h | h | h
      · rw [Real.sign_of_neg h]; norm_num
      · exact absurd h hy
      · rw [Real.sign_of_pos h]; norm_num
    have h2 : |y| ^ ((n : ℝ)⁻¹) ≠ 0 := by
      refine ne_of_gt (Real.rpow_pos_of_pos ?_ _)
      exact abs_pos.mpr hy
    exact mul_ne_zero h1 h2
  · rw [mul_pow, Real.rpow_inv_natCast_pow (abs_nonneg y) hn0]
    rcases lt_trichotomy y 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h, hn.neg_one_pow]
      ring
    · exact absurd h hy
    · rw [Real.sign_of_pos h, abs_of_pos h, one_pow, one_mul]
  · rintro x ⟨-, hx⟩
    have hinj := Odd.pow_injective (R := ℝ) hn
    apply hinj
    show x ^ n = _ ^ n
    rw [hx]
    rw [mul_pow, Real.rpow_inv_natCast_pow (abs_nonneg y) hn0]
    rcases lt_trichotomy y 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h, hn.neg_one_pow]
      ring
    · exact absurd h hy
    · rw [Real.sign_of_pos h, abs_of_pos h, one_pow, one_mul]

/-- **Even degree: a boundary is fillable exactly when it is positive.** -/
theorem even_fillable_iff (hn : Even n) (hn0 : n ≠ 0) {y : ℝ} (hy : y ≠ 0) :
    (∃ x : ℝ, x ≠ 0 ∧ x ^ n = y) ↔ 0 < y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hn.pow_pos hx
  · intro hpos
    refine ⟨y ^ ((n : ℝ)⁻¹), ne_of_gt (Real.rpow_pos_of_pos hpos _), ?_⟩
    exact Real.rpow_inv_natCast_pow hpos.le hn0

/-- **Even degree: a positive boundary has exactly the two fillings `±y^{1/n}`.** -/
theorem even_fill_eq_pair (hn : Even n) (hn0 : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    {x : ℝ | x ^ n = y} = {y ^ ((n : ℝ)⁻¹), -(y ^ ((n : ℝ)⁻¹))} := by
  have hroot : (y ^ ((n : ℝ)⁻¹)) ^ n = y := Real.rpow_inv_natCast_pow hy.le hn0
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    have habs : |x| = |y ^ ((n : ℝ)⁻¹)| := by
      have h1 : |x| ^ n = |y ^ ((n : ℝ)⁻¹)| ^ n := by
        rw [← abs_pow, ← abs_pow, hx, hroot]
      exact pow_left_inj_nonneg (abs_nonneg x) (abs_nonneg _) hn0 h1
    rw [abs_of_pos (Real.rpow_pos_of_pos hy _)] at habs
    rcases abs_eq (le_of_lt (Real.rpow_pos_of_pos hy _)) |>.mp habs with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact hroot
    · rw [hn.neg_pow, hroot]

/-- **Even degree: the kernel is exactly `{±1}`.** -/
theorem even_units_pow_eq_one_iff (hn : Even n) (hn0 : n ≠ 0) (x : ℝˣ) :
    x ^ n = 1 ↔ (x = 1 ∨ x = -1) := by
  constructor
  · intro hx
    have hx' : ((x : ℝ)) ^ n = 1 := by
      have := congrArg (fun u : ℝˣ => (u : ℝ)) hx
      simpa using this
    have hmem : (x : ℝ) ∈ ({(1 : ℝ) ^ ((n : ℝ)⁻¹), -((1 : ℝ) ^ ((n : ℝ)⁻¹))} : Set ℝ) := by
      rw [← even_fill_eq_pair hn hn0 (y := (1 : ℝ)) one_pos]
      exact hx'
    simp only [Real.one_rpow, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by simpa using h))
  · rintro (rfl | rfl)
    · exact one_pow n
    · rw [hn.neg_pow, one_pow]

/-- **Even degree: the cokernel has exactly the two classes `±1`.** -/
theorem even_coker_two (hn : Even n) (hn0 : n ≠ 0) :
    (∀ y : ℝˣ, (∃ x : ℝˣ, x ^ n = y) ↔ 0 < (y : ℝ)) ∧
      (∃ y : ℝˣ, ¬ ∃ x : ℝˣ, x ^ n = y) ∧
      (∀ y : ℝˣ, (∃ x : ℝˣ, x ^ n = y) ∨ (∃ x : ℝˣ, x ^ n = -y)) := by
  have hkey : ∀ y : ℝˣ, (∃ x : ℝˣ, x ^ n = y) ↔ 0 < (y : ℝ) := by
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      have : ((x ^ n : ℝˣ) : ℝ) = (x : ℝ) ^ n := by simp
      rw [this]
      exact hn.pow_pos x.ne_zero
    · intro hpos
      obtain ⟨x, hx, hxn⟩ := (even_fillable_iff hn hn0 y.ne_zero).mpr hpos
      refine ⟨Units.mk0 x hx, ?_⟩
      apply Units.ext
      simpa using hxn
  refine ⟨hkey, ⟨-1, ?_⟩, ?_⟩
  · rw [hkey]
    norm_num
  · intro y
    rcases lt_trichotomy ((y : ℝ)) 0 with h | h | h
    · right
      rw [hkey]
      simpa using h
    · exact absurd h y.ne_zero
    · exact Or.inl ((hkey y).mpr h)

/-- **Positive coefficients: every boundary has exactly one filling, for every degree.** -/
theorem positive_fill_existsUnique (hn0 : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    ∃! x : ℝ, 0 < x ∧ x ^ n = y := by
  refine ⟨y ^ ((n : ℝ)⁻¹), ⟨Real.rpow_pos_of_pos hy _, Real.rpow_inv_natCast_pow hy.le hn0⟩, ?_⟩
  rintro x ⟨hx, hxn⟩
  refine pow_left_inj_nonneg hx.le (Real.rpow_pos_of_pos hy _).le hn0 ?_
  rw [hxn, Real.rpow_inv_natCast_pow hy.le hn0]

/-- **Positivity simultaneously repairs and erases.**  Passing to the absolute value turns a
nonfillable negative boundary into a fillable one and merges the two oriented fillings into one. -/
theorem positive_repairs_and_erases (hn : Even n) (hn0 : n ≠ 0) {y : ℝ} (hy : y < 0) :
    (¬ ∃ x : ℝ, x ≠ 0 ∧ x ^ n = y) ∧ (∃! x : ℝ, 0 < x ∧ x ^ n = |y|) := by
  refine ⟨?_, positive_fill_existsUnique hn0 (abs_pos.mpr (ne_of_lt hy))⟩
  intro hcon
  have := (even_fillable_iff hn hn0 (ne_of_lt hy)).mp hcon
  linarith

/-- **The realization fibre profile moves under the coefficient change.**  Over the oriented
coefficients an even Moore cell is neither injective nor surjective — the mixed phase — while over
the positive coefficients it is bijective. -/
theorem even_mixed_positive_reconstructible (hn : Even n) (hn0 : n ≠ 0) :
    (¬ Function.Injective fun x : ℝˣ => x ^ n) ∧
      (¬ Function.Surjective fun x : ℝˣ => x ^ n) ∧
      (∀ y : ℝ, 0 < y → ∃! x : ℝ, 0 < x ∧ x ^ n = y) := by
  refine ⟨?_, ?_, fun y hy => positive_fill_existsUnique hn0 hy⟩
  · intro hinj
    have h : ((-1 : ℝˣ) ^ n) = (1 : ℝˣ) ^ n := by
      rw [hn.neg_pow, one_pow]
    have := hinj h
    have h2 : ((-1 : ℝˣ) : ℝ) = ((1 : ℝˣ) : ℝ) := congrArg (fun u : ℝˣ => (u : ℝ)) this
    norm_num at h2
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj (-1)
    have hpos := ((even_coker_two hn hn0).1 (-1)).mp ⟨x, hx⟩
    norm_num at hpos

end MooreCell

end GaloisForLFunctions.HTGeometry
