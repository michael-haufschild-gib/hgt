import Mathlib

/-!
# Laurent coefficients of a product of three-term factors

For data `a_i ∈ ℝ`, `x_i, y_i ∈ ℂ` indexed by a list `L`, the product
`∏_{i ∈ L} (1 + a_i (x_i w + y_i w⁻¹))` is a Laurent polynomial in `w` with coefficients `laurentCoef`,
defined by the recursion `c'(n) = c(n) + a x c(n − 1) + a y c(n + 1)`.

* **Discrete extraction** (`diagFourier_diagProd_eq`).  With `ω = e^{2πi/N}`, the averages
  `N⁻¹ Σ_{j<N} F(ω^j) ω^{−jm}` of the product equal `laurentCoef L m` whenever `|m| + |L| < N`.
* **Weighted remainder** (`tsum_laurentRemainder_le`).  If `|a_i x_i| ≤ d_i B` and
  `|a_i y_i| ≤ d_i B⁻¹`, the coefficients minus their constant and linear parts satisfy
  `Σ_n |r(n)| B^{−n} ≤ ∏(1 + 2d_i) − 1 − 2Σ d_i`.  So the frequency-`±1` coefficients equal their
  linear parts `Σ a_i x_i`, `Σ a_i y_i` up to `B^{±1}` times a quadratic error, however large the
  individual powers `B^n` are.
-/

open Complex

namespace RHTower

noncomputable section

variable {ι : Type*}

/-! ## The coefficients -/

/-- Laurent coefficients of `∏_{i ∈ L} (1 + a_i (x_i w + y_i w⁻¹))`. -/
def laurentCoef (a : ι → ℝ) (x y : ι → ℂ) : List ι → ℤ → ℂ
  | [], n => if n = 0 then 1 else 0
  | i :: L, n => laurentCoef a x y L n + (a i : ℂ) * x i * laurentCoef a x y L (n - 1) +
      (a i : ℂ) * y i * laurentCoef a x y L (n + 1)

theorem laurentCoef_eq_zero (a : ι → ℝ) (x y : ι → ℂ) :
    ∀ (L : List ι) (n : ℤ), (L.length : ℤ) < |n| → laurentCoef a x y L n = 0
  | [], n, h => by
    simp only [List.length_nil, Nat.cast_zero, abs_pos] at h
    simp [laurentCoef, h]
  | i :: L, n, h => by
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
    have h1 : (L.length : ℤ) < |n| := by linarith
    have h2 : (L.length : ℤ) < |n - 1| := by
      rcases abs_cases n with ⟨hn, _⟩ | ⟨hn, _⟩ <;> rcases abs_cases (n - 1) with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
        omega
    have h3 : (L.length : ℤ) < |n + 1| := by
      rcases abs_cases n with ⟨hn, _⟩ | ⟨hn, _⟩ <;> rcases abs_cases (n + 1) with ⟨hm, _⟩ | ⟨hm, _⟩ <;>
        omega
    simp only [laurentCoef, laurentCoef_eq_zero a x y L n h1, laurentCoef_eq_zero a x y L _ h2,
      laurentCoef_eq_zero a x y L _ h3, mul_zero, add_zero]

/-! ## Discrete extraction -/

/-- `ω_N = e^{2πi/N}`. -/
def unitRoot (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / N)

theorem unitRoot_ne_zero (N : ℕ) : unitRoot N ≠ 0 := Complex.exp_ne_zero _

/-- The product at the `j`-th root of unity. -/
def diagProd (a : ι → ℝ) (x y : ι → ℂ) (L : List ι) (N j : ℕ) : ℂ :=
  (L.map fun i => 1 + (a i : ℂ) * (x i * unitRoot N ^ (j : ℤ) + y i * unitRoot N ^ (-(j : ℤ)))).prod

/-- The discrete Fourier coefficient `N⁻¹ Σ_{j<N} F(j) ω^{−jm}`. -/
def diagFourier (F : ℕ → ℂ) (N : ℕ) (m : ℤ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, F j * unitRoot N ^ (-(j : ℤ) * m)

theorem diagFourier_one {N : ℕ} (hN : N ≠ 0) (m : ℤ) :
    diagFourier (fun _ => 1) N m = if (N : ℤ) ∣ m then 1 else 0 := by
  have hp := Complex.isPrimitiveRoot_exp N hN
  have hω : unitRoot N = Complex.exp (2 * Real.pi * I / N) := rfl
  have hpow : ∀ j : ℕ, unitRoot N ^ (-(j : ℤ) * m) = (unitRoot N ^ (-m)) ^ j := fun j => by
    rw [← zpow_natCast, ← zpow_mul]; ring_nf
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  unfold diagFourier
  simp only [one_mul, hpow]
  split_ifs with hdvd
  · have h1 : unitRoot N ^ (-m) = 1 := by
      rw [hω]; exact (hp.zpow_eq_one_iff_dvd _).mpr (by simpa using hdvd)
    simp [h1, hN0]
  · have h1 : unitRoot N ^ (-m) ≠ 1 := by
      rw [hω]; intro h; exact hdvd (by simpa using (hp.zpow_eq_one_iff_dvd _).mp h)
    have h2 : (unitRoot N ^ (-m)) ^ N = 1 := by
      rw [← zpow_natCast, ← zpow_mul, hω]
      exact (hp.zpow_eq_one_iff_dvd _).mpr ⟨-m, by ring⟩
    rw [geom_sum_eq h1, h2, sub_self, zero_div, mul_zero]

theorem diagFourier_cons (a : ι → ℝ) (x y : ι → ℂ) (i : ι) (L : List ι) (N : ℕ) (m : ℤ) :
    diagFourier (diagProd a x y (i :: L) N) N m =
      diagFourier (diagProd a x y L N) N m +
        (a i : ℂ) * x i * diagFourier (diagProd a x y L N) N (m - 1) +
        (a i : ℂ) * y i * diagFourier (diagProd a x y L N) N (m + 1) := by
  have hω := unitRoot_ne_zero N
  unfold diagFourier diagProd
  simp only [List.map_cons, List.prod_cons]
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℂ, P = fun j : ℕ => (L.map fun i => 1 + (a i : ℂ) *
      (x i * unitRoot N ^ (j : ℤ) + y i * unitRoot N ^ (-(j : ℤ)))).prod := ⟨_, rfl⟩
  have hPj : ∀ j : ℕ, (L.map fun i => 1 + (a i : ℂ) *
      (x i * unitRoot N ^ (j : ℤ) + y i * unitRoot N ^ (-(j : ℤ)))).prod = P j := fun j => by rw [hP]
  simp only [hPj]
  have key : ∀ j ∈ Finset.range N, (1 + (a i : ℂ) * (x i * unitRoot N ^ (j : ℤ) +
      y i * unitRoot N ^ (-(j : ℤ)))) * P j * unitRoot N ^ (-(j : ℤ) * m) =
      P j * unitRoot N ^ (-(j : ℤ) * m) + (a i : ℂ) * x i * (P j * unitRoot N ^ (-(j : ℤ) * (m - 1))) +
        (a i : ℂ) * y i * (P j * unitRoot N ^ (-(j : ℤ) * (m + 1))) := by
    intro j _
    have e1 : unitRoot N ^ (-(j : ℤ) * (m - 1)) =
        unitRoot N ^ (j : ℤ) * unitRoot N ^ (-(j : ℤ) * m) := by rw [← zpow_add₀ hω]; ring_nf
    have e2 : unitRoot N ^ (-(j : ℤ) * (m + 1)) =
        unitRoot N ^ (-(j : ℤ)) * unitRoot N ^ (-(j : ℤ) * m) := by rw [← zpow_add₀ hω]; ring_nf
    rw [e1, e2]
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

/-- **Discrete extraction.**  For `|m| + |L| < N`, the `m`-th discrete Fourier coefficient of the
product is its Laurent coefficient. -/
theorem diagFourier_diagProd_eq (a : ι → ℝ) (x y : ι → ℂ) {N : ℕ} (hN : N ≠ 0) :
    ∀ (L : List ι) (m : ℤ), |m| + L.length < N →
      diagFourier (diagProd a x y L N) N m = laurentCoef a x y L m
  | [], m, h => by
    have hprod : diagProd a x y [] N = fun _ => 1 := by funext j; simp [diagProd]
    rw [hprod, diagFourier_one hN]
    simp only [List.length_nil, Nat.cast_zero, add_zero] at h
    simp only [laurentCoef]
    by_cases hm : m = 0
    · simp [hm]
    · rw [if_neg hm, if_neg]
      intro hd
      exact hm (Int.eq_zero_of_abs_lt_dvd hd h)
  | i :: L, m, h => by
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h
    have h1 : |m| + L.length < N := by linarith
    have h2 : |m - 1| + L.length < N := by
      have := abs_sub_le m 0 1; simp at this; linarith [abs_sub m 1]
    have h3 : |m + 1| + L.length < N := by
      have := abs_add_le m 1; simp at this; linarith
    rw [diagFourier_cons, diagFourier_diagProd_eq a x y hN L m h1,
      diagFourier_diagProd_eq a x y hN L _ h2, diagFourier_diagProd_eq a x y hN L _ h3]
    rfl

/-! ## The weighted remainder -/

/-- Constant and linear parts of the coefficients: `δ₀ + δ₁ Σ a x + δ₋₁ Σ a y`. -/
def laurentMain (a : ι → ℝ) (x y : ι → ℂ) (L : List ι) (n : ℤ) : ℂ :=
  (if n = 0 then 1 else 0) + (if n = 1 then (L.map fun i => (a i : ℂ) * x i).sum else 0) +
    (if n = -1 then (L.map fun i => (a i : ℂ) * y i).sum else 0)

/-- The remainder after the constant and linear parts. -/
def laurentRem (a : ι → ℝ) (x y : ι → ℂ) (L : List ι) (n : ℤ) : ℂ :=
  laurentCoef a x y L n - laurentMain a x y L n

theorem laurentRem_nil (a : ι → ℝ) (x y : ι → ℂ) (n : ℤ) : laurentRem a x y [] n = 0 := by
  simp only [laurentRem, laurentCoef, laurentMain, List.map_nil, List.sum_nil]
  split_ifs <;> simp

theorem laurentRem_cons (a : ι → ℝ) (x y : ι → ℂ) (i : ι) (L : List ι) (n : ℤ) :
    laurentRem a x y (i :: L) n = laurentRem a x y L n +
      (a i : ℂ) * x i * (laurentRem a x y L (n - 1) +
        (if n = 2 then (L.map fun i => (a i : ℂ) * x i).sum else 0) +
        (if n = 0 then (L.map fun i => (a i : ℂ) * y i).sum else 0)) +
      (a i : ℂ) * y i * (laurentRem a x y L (n + 1) +
        (if n = 0 then (L.map fun i => (a i : ℂ) * x i).sum else 0) +
        (if n = -2 then (L.map fun i => (a i : ℂ) * y i).sum else 0)) := by
  rcases (show n = -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 ∨
      (n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2) by omega) with h | h | h | h | h | ⟨h1, h2, h3, h4, h5⟩
  · subst h; simp only [laurentRem, laurentCoef, laurentMain, List.map_cons, List.sum_cons]; norm_num
  · subst h; simp only [laurentRem, laurentCoef, laurentMain, List.map_cons, List.sum_cons]; norm_num; ring
  · subst h; simp only [laurentRem, laurentCoef, laurentMain, List.map_cons, List.sum_cons]; norm_num; ring
  · subst h; simp only [laurentRem, laurentCoef, laurentMain, List.map_cons, List.sum_cons]; norm_num; ring
  · subst h; simp only [laurentRem, laurentCoef, laurentMain, List.map_cons, List.sum_cons]; norm_num
  · have e1 : n - 1 ≠ 0 := by omega
    have e2 : n - 1 ≠ 1 := by omega
    have e3 : n - 1 ≠ -1 := by omega
    have e4 : n + 1 ≠ 0 := by omega
    have e5 : n + 1 ≠ 1 := by omega
    have e6 : n + 1 ≠ -1 := by omega
    simp only [laurentRem, laurentCoef, laurentMain, List.map_cons, List.sum_cons, if_neg h1,
      if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg e1, if_neg e2, if_neg e3, if_neg e4,
      if_neg e5, if_neg e6]
    ring

theorem laurentRem_eq_zero (a : ι → ℝ) (x y : ι → ℂ) (L : List ι) (n : ℤ)
    (h : (L.length : ℤ) + 1 < |n|) : laurentRem a x y L n = 0 := by
  have h1 : laurentCoef a x y L n = 0 := laurentCoef_eq_zero a x y L n (by linarith)
  have h0 : n ≠ 0 := by rintro rfl; simp at h; omega
  have h2 : n ≠ 1 := by rintro rfl; simp at h; omega
  have h3 : n ≠ -1 := by rintro rfl; simp at h; omega
  simp [laurentRem, laurentMain, h1, h0, h2, h3]

theorem norm_list_sum_map_le (L : List ι) (f : ι → ℂ) (g : ι → ℝ) (h : ∀ i ∈ L, ‖f i‖ ≤ g i) :
    ‖(L.map f).sum‖ ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons j L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add (h j List.mem_cons_self)
      (ih fun i hi => h i (List.mem_cons_of_mem _ hi)))

theorem summable_of_abs_gt {f : ℤ → ℝ} (K : ℕ) (h : ∀ n : ℤ, (K : ℤ) < |n| → f n = 0) :
    Summable f := by
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(K : ℤ)) K) fun n hn => h n ?_
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  rcases hn with hn | hn
  · rw [abs_of_neg (by omega)]; omega
  · rw [abs_of_pos (by omega)]; omega

/-- **Weighted remainder bound.**  If `|a_i x_i| ≤ d_i B` and `|a_i y_i| ≤ d_i B⁻¹`, then
`Σ_n |r(n)| B^{−n} ≤ ∏(1 + 2d_i) − 1 − 2 Σ d_i`. -/
theorem tsum_laurentRem_le (a : ι → ℝ) (x y : ι → ℂ) (d : ι → ℝ) {B : ℝ} (hB : 0 < B) :
    ∀ L : List ι, (∀ i ∈ L, 0 ≤ d i) → (∀ i ∈ L, ‖(a i : ℂ) * x i‖ ≤ d i * B) →
      (∀ i ∈ L, ‖(a i : ℂ) * y i‖ ≤ d i * B⁻¹) →
      ∑' n : ℤ, ‖laurentRem a x y L n‖ * B ^ (-n) ≤
        (L.map fun i => 1 + 2 * d i).prod - 1 - 2 * (L.map d).sum
  | [], _, _, _ => by simp [laurentRem_nil]
  | i :: L, hd, hx, hy => by
    have hB0 : B ≠ 0 := hB.ne'
    have hdL : ∀ j ∈ L, 0 ≤ d j := fun j hj => hd j (List.mem_cons_of_mem _ hj)
    have hxL : ∀ j ∈ L, ‖(a j : ℂ) * x j‖ ≤ d j * B := fun j hj => hx j (List.mem_cons_of_mem _ hj)
    have hyL : ∀ j ∈ L, ‖(a j : ℂ) * y j‖ ≤ d j * B⁻¹ :=
      fun j hj => hy j (List.mem_cons_of_mem _ hj)
    have IH := tsum_laurentRem_le a x y d hB L hdL hxL hyL
    have hdi : 0 ≤ d i := hd i List.mem_cons_self
    have hxi : ‖(a i : ℂ) * x i‖ ≤ d i * B := hx i List.mem_cons_self
    have hyi : ‖(a i : ℂ) * y i‖ ≤ d i * B⁻¹ := hy i List.mem_cons_self
    obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = (L.map d).sum := ⟨_, rfl⟩
    obtain ⟨lp, hlp⟩ : ∃ lp : ℂ, lp = (L.map fun i => (a i : ℂ) * x i).sum := ⟨_, rfl⟩
    obtain ⟨lm, hlm⟩ : ∃ lm : ℂ, lm = (L.map fun i => (a i : ℂ) * y i).sum := ⟨_, rfl⟩
    have hD0 : 0 ≤ D := by
      rw [hDdef]
      refine List.sum_nonneg fun z hz => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
      exact hdL j hj
    have hlpB : ‖lp‖ ≤ D * B := by
      rw [hlp, hDdef, ← List.sum_map_mul_right]
      exact norm_list_sum_map_le L _ _ hxL
    have hlmB : ‖lm‖ ≤ D * B⁻¹ := by
      rw [hlm, hDdef, ← List.sum_map_mul_right]
      exact norm_list_sum_map_le L _ _ hyL
    obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = ∑' n : ℤ, ‖laurentRem a x y L n‖ * B ^ (-n) := ⟨_, rfl⟩
    rw [← hEdef, ← hDdef] at IH
    -- summability of the pieces
    have hs0 : Summable fun n : ℤ => ‖laurentRem a x y L n‖ * B ^ (-n) :=
      summable_of_abs_gt (L.length + 1) fun n hn => by
        rw [laurentRem_eq_zero a x y L n (by push_cast at hn ⊢; linarith), norm_zero, zero_mul]
    have hs1 : Summable fun n : ℤ => ‖laurentRem a x y L (n - 1)‖ * B ^ (-n) :=
      summable_of_abs_gt (L.length + 2) fun n hn => by
        rw [laurentRem_eq_zero a x y L (n - 1) (by
          push_cast at hn ⊢
          rcases abs_cases n with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
            rcases abs_cases (n - 1) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega), norm_zero, zero_mul]
    have hs2 : Summable fun n : ℤ => ‖laurentRem a x y L (n + 1)‖ * B ^ (-n) :=
      summable_of_abs_gt (L.length + 2) fun n hn => by
        rw [laurentRem_eq_zero a x y L (n + 1) (by
          push_cast at hn ⊢
          rcases abs_cases n with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
            rcases abs_cases (n + 1) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega), norm_zero, zero_mul]
    have hsh1 : ∑' n : ℤ, ‖laurentRem a x y L (n - 1)‖ * B ^ (-n) = B⁻¹ * E := by
      have : ∀ n : ℤ, ‖laurentRem a x y L (n - 1)‖ * B ^ (-n) =
          B⁻¹ * (‖laurentRem a x y L (n - 1)‖ * B ^ (-(n - 1))) := fun n => by
        rw [show -n = -(n - 1) + (-1) by ring, zpow_add₀ hB0, zpow_neg_one]; ring
      simp_rw [this]
      rw [tsum_mul_left, hEdef]
      congr 1
      exact (Equiv.subRight (1 : ℤ)).tsum_eq fun m => ‖laurentRem a x y L m‖ * B ^ (-m)
    have hsh2 : ∑' n : ℤ, ‖laurentRem a x y L (n + 1)‖ * B ^ (-n) = B * E := by
      have : ∀ n : ℤ, ‖laurentRem a x y L (n + 1)‖ * B ^ (-n) =
          B * (‖laurentRem a x y L (n + 1)‖ * B ^ (-(n + 1))) := fun n => by
        rw [show -n = -(n + 1) + 1 by ring, zpow_add₀ hB0, zpow_one]; ring
      simp_rw [this]
      rw [tsum_mul_left, hEdef]
      congr 1
      exact (Equiv.addRight (1 : ℤ)).tsum_eq fun m => ‖laurentRem a x y L m‖ * B ^ (-m)
    -- termwise bound
    obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = ‖(a i : ℂ) * x i‖ * ‖lp‖ * B ^ (-2 : ℤ) := ⟨_, rfl⟩
    obtain ⟨c₂, hc₂⟩ : ∃ c : ℝ, c = ‖(a i : ℂ) * x i‖ * ‖lm‖ + ‖(a i : ℂ) * y i‖ * ‖lp‖ := ⟨_, rfl⟩
    obtain ⟨c₃, hc₃⟩ : ∃ c : ℝ, c = ‖(a i : ℂ) * y i‖ * ‖lm‖ * B ^ (2 : ℤ) := ⟨_, rfl⟩
    have hterm : ∀ n : ℤ, ‖laurentRem a x y (i :: L) n‖ * B ^ (-n) ≤
        ‖laurentRem a x y L n‖ * B ^ (-n) +
          ‖(a i : ℂ) * x i‖ * (‖laurentRem a x y L (n - 1)‖ * B ^ (-n)) +
          ‖(a i : ℂ) * y i‖ * (‖laurentRem a x y L (n + 1)‖ * B ^ (-n)) +
          ((if n = 2 then c₁ else 0) + (if n = 0 then c₂ else 0) + (if n = -2 then c₃ else 0)) := by
      intro n
      have hBn : 0 < B ^ (-n) := zpow_pos hB _
      obtain ⟨Z₁, hZ₁⟩ : ∃ Z : ℂ, Z = laurentRem a x y L (n - 1) + (if n = 2 then lp else 0) +
          (if n = 0 then lm else 0) := ⟨_, rfl⟩
      obtain ⟨Z₂, hZ₂⟩ : ∃ Z : ℂ, Z = laurentRem a x y L (n + 1) + (if n = 0 then lp else 0) +
          (if n = -2 then lm else 0) := ⟨_, rfl⟩
      have hA : ‖Z₁‖ ≤ ‖laurentRem a x y L (n - 1)‖ + ‖(if n = 2 then lp else 0)‖ +
          ‖(if n = 0 then lm else 0)‖ := by rw [hZ₁]; exact norm_add₃_le
      have hC : ‖Z₂‖ ≤ ‖laurentRem a x y L (n + 1)‖ + ‖(if n = 0 then lp else 0)‖ +
          ‖(if n = -2 then lm else 0)‖ := by rw [hZ₂]; exact norm_add₃_le
      have hax := norm_nonneg ((a i : ℂ) * x i)
      have hay := norm_nonneg ((a i : ℂ) * y i)
      have step : ‖laurentRem a x y (i :: L) n‖ ≤ ‖laurentRem a x y L n‖ +
          ‖(a i : ℂ) * x i‖ * (‖laurentRem a x y L (n - 1)‖ + ‖(if n = 2 then lp else 0)‖ +
            ‖(if n = 0 then lm else 0)‖) +
          ‖(a i : ℂ) * y i‖ * (‖laurentRem a x y L (n + 1)‖ + ‖(if n = 0 then lp else 0)‖ +
            ‖(if n = -2 then lm else 0)‖) := by
        rw [laurentRem_cons, ← hlp, ← hlm, ← hZ₁, ← hZ₂]
        have hn : ‖laurentRem a x y L n + (a i : ℂ) * x i * Z₁ + (a i : ℂ) * y i * Z₂‖ ≤
            ‖laurentRem a x y L n‖ + ‖(a i : ℂ) * x i‖ * ‖Z₁‖ + ‖(a i : ℂ) * y i‖ * ‖Z₂‖ := by
          have := norm_add₃_le (a := laurentRem a x y L n) (b := (a i : ℂ) * x i * Z₁)
            (c := (a i : ℂ) * y i * Z₂)
          rwa [norm_mul ((a i : ℂ) * x i), norm_mul ((a i : ℂ) * y i)] at this
        refine hn.trans ?_
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hA hax))
          (mul_le_mul_of_nonneg_left hC hay)
      have := mul_le_mul_of_nonneg_right step hBn.le
      refine this.trans (le_of_eq ?_)
      rw [hc₁, hc₂, hc₃]
      by_cases h2 : n = 2
      · subst h2; simp; ring
      · by_cases h0 : n = 0
        · subst h0; simp; ring
        · by_cases hm2 : n = -2
          · subst hm2; simp; ring
          · simp [h2, h0, hm2]; ring
    have hsd : Summable fun n : ℤ =>
        ((if n = 2 then c₁ else 0) + (if n = 0 then c₂ else 0) + (if n = -2 then c₃ else 0)) :=
      summable_of_abs_gt 2 fun n hn => by
        have : n ≠ 2 := by rintro rfl; simp at hn
        have : n ≠ 0 := by rintro rfl; simp at hn
        have : n ≠ -2 := by rintro rfl; simp at hn
        simp [*]
    have hsr : Summable fun n : ℤ => ‖laurentRem a x y (i :: L) n‖ * B ^ (-n) :=
      summable_of_abs_gt ((i :: L).length + 1) fun n hn => by
        rw [laurentRem_eq_zero a x y (i :: L) n (by push_cast at hn ⊢; linarith), norm_zero, zero_mul]
    have hsum := hsr.tsum_le_tsum hterm
      (((hs0.add (hs1.mul_left _)).add (hs2.mul_left _)).add hsd)
    rw [(((hs0.add (hs1.mul_left _)).add (hs2.mul_left _))).tsum_add hsd,
      ((hs0.add (hs1.mul_left _))).tsum_add (hs2.mul_left _), hs0.tsum_add (hs1.mul_left _),
      tsum_mul_left, tsum_mul_left, hsh1, hsh2, ← hEdef] at hsum
    have hdsum : ∑' n : ℤ, ((if n = 2 then c₁ else 0) + (if n = 0 then c₂ else 0) +
        (if n = -2 then c₃ else 0)) = c₁ + c₂ + c₃ := by
      rw [Summable.tsum_add (by
          exact (summable_of_abs_gt 2 fun n hn => by
            have : n ≠ 2 := by rintro rfl; simp at hn
            have : n ≠ 0 := by rintro rfl; simp at hn
            simp [*]))
        (summable_of_abs_gt 2 fun n hn => by
          have : n ≠ -2 := by rintro rfl; simp at hn
          simp [*]),
        Summable.tsum_add (summable_of_abs_gt 2 fun n hn => by
          have : n ≠ 2 := by rintro rfl; simp at hn
          simp [*]) (summable_of_abs_gt 2 fun n hn => by
          have : n ≠ 0 := by rintro rfl; simp at hn
          simp [*]),
        tsum_ite_eq, tsum_ite_eq, tsum_ite_eq]
    rw [hdsum] at hsum
    -- the arithmetic
    have hB2 : B ^ (-2 : ℤ) = B⁻¹ * B⁻¹ := by rw [zpow_neg, zpow_two, mul_inv]
    have hB2' : B ^ (2 : ℤ) = B * B := by rw [zpow_two]
    have hBi : B * B⁻¹ = 1 := mul_inv_cancel₀ hB0
    have k1 : c₁ ≤ d i * D := by
      rw [hc₁, hB2]
      calc ‖(a i : ℂ) * x i‖ * ‖lp‖ * (B⁻¹ * B⁻¹) ≤ (d i * B) * (D * B) * (B⁻¹ * B⁻¹) := by
            gcongr
        _ = d i * D * (B * B⁻¹) * (B * B⁻¹) := by ring
        _ = d i * D := by rw [hBi]; ring
    have k2 : c₂ ≤ 2 * (d i * D) := by
      rw [hc₂]
      calc ‖(a i : ℂ) * x i‖ * ‖lm‖ + ‖(a i : ℂ) * y i‖ * ‖lp‖
          ≤ (d i * B) * (D * B⁻¹) + (d i * B⁻¹) * (D * B) := by gcongr
        _ = 2 * (d i * D) * (B * B⁻¹) := by ring
        _ = 2 * (d i * D) := by rw [hBi, mul_one]
    have k3 : c₃ ≤ d i * D := by
      rw [hc₃, hB2']
      calc ‖(a i : ℂ) * y i‖ * ‖lm‖ * (B * B) ≤ (d i * B⁻¹) * (D * B⁻¹) * (B * B) := by gcongr
        _ = d i * D * (B * B⁻¹) * (B * B⁻¹) := by ring
        _ = d i * D := by rw [hBi]; ring
    have hE0 : 0 ≤ E := by rw [hEdef]; exact tsum_nonneg fun n => by positivity
    have k4 : ‖(a i : ℂ) * x i‖ * (B⁻¹ * E) ≤ d i * E := by
      calc ‖(a i : ℂ) * x i‖ * (B⁻¹ * E) ≤ (d i * B) * (B⁻¹ * E) := by gcongr
        _ = d i * E * (B * B⁻¹) := by ring
        _ = d i * E := by rw [hBi, mul_one]
    have k5 : ‖(a i : ℂ) * y i‖ * (B * E) ≤ d i * E := by
      calc ‖(a i : ℂ) * y i‖ * (B * E) ≤ (d i * B⁻¹) * (B * E) := by gcongr
        _ = d i * E * (B * B⁻¹) := by ring
        _ = d i * E := by rw [hBi, mul_one]
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [← hDdef]
    have hM : 0 ≤ (L.map fun i => 1 + 2 * d i).prod := by
      refine List.prod_nonneg fun z hz => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
      linarith [hdL j hj]
    nlinarith

/-! ## Bochner's inequality on the discrete circle -/

theorem norm_unitRoot_zpow (N : ℕ) (k : ℤ) : ‖unitRoot N ^ k‖ = 1 := by
  rw [norm_zpow, unitRoot, Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * I / N).re = 0 := by
    rw [show 2 * (Real.pi : ℂ) * I / N = ((2 * Real.pi / N : ℝ) : ℂ) * I by push_cast; ring]
    simp
  rw [this, Real.exp_zero, one_zpow]

theorem conj_unitRoot_zpow (N : ℕ) (k : ℤ) :
    (starRingEnd ℂ) (unitRoot N ^ k) = unitRoot N ^ (-k) := by
  have hn := norm_unitRoot_zpow N k
  rw [zpow_neg, Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

/-- **Bochner on the discrete circle.**  If `Re T(j) ≥ 0` for every `j < N`, then the discrete
Fourier coefficients satisfy `‖ĉ₁ + conj ĉ₋₁‖ ≤ 2 Re ĉ₀`. -/
theorem norm_diagFourier_one_add_conj_le {T : ℕ → ℂ} {N : ℕ} (hN : N ≠ 0)
    (hT : ∀ j < N, 0 ≤ (T j).re) :
    ‖diagFourier T N 1 + (starRingEnd ℂ) (diagFourier T N (-1))‖ ≤ 2 * (diagFourier T N 0).re := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  obtain ⟨S0, hS0⟩ : ∃ S, S = ∑ j ∈ Finset.range N, T j * unitRoot N ^ (-(j : ℤ) * 0) := ⟨_, rfl⟩
  obtain ⟨S1, hS1⟩ : ∃ S, S = ∑ j ∈ Finset.range N, T j * unitRoot N ^ (-(j : ℤ) * 1) := ⟨_, rfl⟩
  obtain ⟨Sm, hSm⟩ : ∃ S, S = ∑ j ∈ Finset.range N, T j * unitRoot N ^ (-(j : ℤ) * (-1)) :=
    ⟨_, rfl⟩
  have hc0 : diagFourier T N 0 = (N : ℂ)⁻¹ * S0 := by rw [hS0]; rfl
  have hc1 : diagFourier T N 1 = (N : ℂ)⁻¹ * S1 := by rw [hS1]; rfl
  have hcm : diagFourier T N (-1) = (N : ℂ)⁻¹ * Sm := by rw [hSm]; rfl
  have key : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 →
      0 ≤ S0.re + ((ζ * S1).re + (ζ * (starRingEnd ℂ) Sm).re) / 2 := by
    intro ζ hζ
    have hterm : ∀ j : ℕ, (1 + (ζ * unitRoot N ^ (-(j : ℤ))).re) * (T j).re =
        (T j * unitRoot N ^ (-(j : ℤ) * 0)).re + ((ζ * (T j * unitRoot N ^ (-(j : ℤ) * 1))).re +
          (ζ * (starRingEnd ℂ) (T j * unitRoot N ^ (-(j : ℤ) * (-1)))).re) / 2 := by
      intro j
      have hconj : (starRingEnd ℂ) (unitRoot N ^ (-(j : ℤ) * (-1))) = unitRoot N ^ (-(j : ℤ)) := by
        rw [conj_unitRoot_zpow]; ring_nf
      rw [map_mul, hconj]
      simp only [mul_zero, zpow_zero, mul_one]
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    have hsum : 0 ≤ ∑ j ∈ Finset.range N, (1 + (ζ * unitRoot N ^ (-(j : ℤ))).re) * (T j).re := by
      refine Finset.sum_nonneg fun j hj => mul_nonneg ?_ (hT j (Finset.mem_range.mp hj))
      have h1 := Complex.abs_re_le_norm (ζ * unitRoot N ^ (-(j : ℤ)))
      rw [norm_mul, norm_unitRoot_zpow, mul_one] at h1
      linarith [neg_abs_le (ζ * unitRoot N ^ (-(j : ℤ))).re]
    simp only [hterm] at hsum
    rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_add_distrib, ← Complex.re_sum,
      ← Complex.re_sum, ← Complex.re_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← map_sum, ← hS0,
      ← hS1, ← hSm] at hsum
    exact hsum
  have hS0re : 0 ≤ S0.re := by simpa using key 0 (by simp)
  have hNinv : (starRingEnd ℂ) ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ := by simp
  have hD : diagFourier T N 1 + (starRingEnd ℂ) (diagFourier T N (-1)) =
      (N : ℂ)⁻¹ * (S1 + (starRingEnd ℂ) Sm) := by
    rw [hc1, hcm, map_mul, hNinv]; ring
  have hre0 : (diagFourier T N 0).re = (N : ℝ)⁻¹ * S0.re := by
    rw [hc0, show ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  rw [hD, hre0, norm_mul, norm_inv, Complex.norm_natCast]
  obtain ⟨D, hDdef⟩ : ∃ D : ℂ, D = S1 + (starRingEnd ℂ) Sm := ⟨_, rfl⟩
  rw [← hDdef]
  have hDle : ‖D‖ ≤ 2 * S0.re := by
    by_cases hD0 : D = 0
    · rw [hD0, norm_zero]; linarith
    · have hn : 0 < ‖D‖ := norm_pos_iff.mpr hD0
      have hζ : ‖-(starRingEnd ℂ) D / (‖D‖ : ℂ)‖ ≤ 1 := by
        rw [norm_div, norm_neg, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hn, div_self hn.ne']
      have h := key _ hζ
      have e : ((-(starRingEnd ℂ) D / (‖D‖ : ℂ)) * S1).re +
          ((-(starRingEnd ℂ) D / (‖D‖ : ℂ)) * (starRingEnd ℂ) Sm).re = -‖D‖ := by
        rw [← Complex.add_re, ← mul_add, ← hDdef, div_mul_eq_mul_div, neg_mul,
          mul_comm ((starRingEnd ℂ) D), Complex.mul_conj, Complex.normSq_eq_norm_sq]
        rw [show -((‖D‖ ^ 2 : ℝ) : ℂ) / (‖D‖ : ℂ) = ((-‖D‖ : ℝ) : ℂ) by
          rw [div_eq_iff (by exact_mod_cast hn.ne')]; push_cast; ring]
        exact Complex.ofReal_re _
      rw [e] at h
      linarith
  have hNinvpos : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hN0
  calc (N : ℝ)⁻¹ * ‖D‖ ≤ (N : ℝ)⁻¹ * (2 * S0.re) := mul_le_mul_of_nonneg_left hDle hNinvpos.le
    _ = 2 * ((N : ℝ)⁻¹ * S0.re) := by ring

/-- **Single coefficients of the remainder.**  `|r(n)| ≤ B^n (∏(1 + 2d_i) − 1 − 2Σ d_i)`. -/
theorem norm_laurentRem_le (a : ι → ℝ) (x y : ι → ℂ) (d : ι → ℝ) {B : ℝ} (hB : 0 < B) (L : List ι)
    (hd : ∀ i ∈ L, 0 ≤ d i) (hx : ∀ i ∈ L, ‖(a i : ℂ) * x i‖ ≤ d i * B)
    (hy : ∀ i ∈ L, ‖(a i : ℂ) * y i‖ ≤ d i * B⁻¹) (n : ℤ) :
    ‖laurentRem a x y L n‖ ≤ B ^ n * ((L.map fun i => 1 + 2 * d i).prod - 1 - 2 * (L.map d).sum) := by
  have hs : Summable fun m : ℤ => ‖laurentRem a x y L m‖ * B ^ (-m) :=
    summable_of_abs_gt (L.length + 1) fun m hm => by
      rw [laurentRem_eq_zero a x y L m (by push_cast at hm ⊢; linarith), norm_zero, zero_mul]
  have h1 : ‖laurentRem a x y L n‖ * B ^ (-n) ≤ ∑' m : ℤ, ‖laurentRem a x y L m‖ * B ^ (-m) :=
    hs.le_tsum n fun m _ => by positivity
  have h2 := h1.trans (tsum_laurentRem_le a x y d hB L hd hx hy)
  have hBn : 0 < B ^ n := zpow_pos hB n
  have e : ‖laurentRem a x y L n‖ = B ^ n * (‖laurentRem a x y L n‖ * B ^ (-n)) := by
    rw [zpow_neg, mul_comm (‖_‖), ← mul_assoc, mul_inv_cancel₀ hBn.ne', one_mul]
  rw [e]
  exact mul_le_mul_of_nonneg_left h2 hBn.le

end

end RHTower
