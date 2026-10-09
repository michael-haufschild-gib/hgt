import Mathlib

/-!
# Toeplitz total positivity of order two

A nonnegative sequence `a : ℕ → ℝ` is a *Turán sequence* (`TuranSeq a`) when
`a i · a (j + 1) ≤ a (i + 1) · a j` for all `i < j`.  Equivalently, every `2 × 2` minor of its
Toeplitz matrix `(a (j − i))` (zero below the diagonal) is nonnegative.  Log-concave sequences
without internal zeros are Turán sequences.

* `TuranSeq.shift`, `TuranSeq.inner_outer`: an inner index pair dominates an outer pair with the
  same index sum, `a u · a v ≤ a x · a y` for `u ≤ x, y` and `x + y = u + v`.
* `TuranSeq.cauchyConv`: the class is closed under the Cauchy product.  The minor of a product of
  Toeplitz matrices is, by the Binet–Cauchy formula (`binet_cauchy`), a sum of products of minors
  of the factors, all of them nonnegative.
* `TuranSeq.of_tendsto`: the class is closed under pointwise limits.
* `TuranSeq.of_three`: a nonnegative sequence supported on `{0, 1, 2}` is a Turán sequence exactly
  when `a 0 · a 2 ≤ a 1²`.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A nonnegative sequence whose Toeplitz matrix has nonnegative `2 × 2` minors. -/
def TuranSeq (a : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ a n) ∧ ∀ i j : ℕ, i < j → a i * a (j + 1) ≤ a (i + 1) * a j

/-- The Cauchy product of two sequences. -/
def cauchyConv (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ range (n + 1), a m * b (n - m)

/-- Extension of a sequence by zero to the integers. -/
def zext (a : ℕ → ℝ) (z : ℤ) : ℝ :=
  if 0 ≤ z then a z.toNat else 0

theorem zext_natCast (a : ℕ → ℝ) (n : ℕ) : zext a n = a n := by
  simp [zext]

theorem zext_of_neg (a : ℕ → ℝ) {z : ℤ} (hz : z < 0) : zext a z = 0 := by
  simp [zext, not_le.mpr hz]

/-- The Binet–Cauchy formula for the `2 × 2` minors of a product of two matrices. -/
theorem binet_cauchy (N : ℕ) (x u y v : ℕ → ℝ) :
    (∑ m ∈ range N, x m * y m) * (∑ m ∈ range N, u m * v m) -
        (∑ m ∈ range N, x m * v m) * (∑ m ∈ range N, u m * y m) =
      ∑ m ∈ range N, ∑ m' ∈ range N,
        if m < m' then (x m * u m' - x m' * u m) * (y m * v m' - y m' * v m) else 0 := by
  set F : ℕ → ℕ → ℝ := fun m m' => x m * u m' * (y m * v m' - v m * y m') with hF
  have hL : (∑ m ∈ range N, x m * y m) * (∑ m ∈ range N, u m * v m) -
      (∑ m ∈ range N, x m * v m) * (∑ m ∈ range N, u m * y m) =
      ∑ m ∈ range N, ∑ m' ∈ range N, F m m' := by
    rw [sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun m' _ => ?_
    simp only [hF]
    ring
  have hsplit : ∑ m ∈ range N, ∑ m' ∈ range N, F m m' =
      (∑ m ∈ range N, ∑ m' ∈ range N, if m < m' then F m m' else 0) +
        ∑ m ∈ range N, ∑ m' ∈ range N, if m' < m then F m m' else 0 := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m' _ => ?_
    rcases lt_trichotomy m m' with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp only [lt_irrefl, if_false, add_zero, hF]
      ring
    · simp [h, not_lt.mpr h.le]
  have hswap : (∑ m ∈ range N, ∑ m' ∈ range N, if m' < m then F m m' else 0) =
      ∑ m ∈ range N, ∑ m' ∈ range N, if m < m' then F m' m else 0 :=
    sum_comm
  rw [hL, hsplit, hswap, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun m' _ => ?_
  split_ifs
  · simp only [hF]
    ring
  · simp

namespace TuranSeq

variable {a b : ℕ → ℝ}

theorem nonneg (ha : TuranSeq a) (n : ℕ) : 0 ≤ a n :=
  ha.1 n

/-- The Turán inequality at every shift. -/
theorem shift (ha : TuranSeq a) :
    ∀ e i j : ℕ, i + e ≤ j → a i * a (j + e) ≤ a (i + e) * a j := by
  intro e
  induction e with
  | zero => intro i j _; simp
  | succ e ih =>
    intro i j hij
    have h1 : a i * a (j + e + 1) ≤ a (i + 1) * a (j + e) := ha.2 i (j + e) (by omega)
    have h2 : a (i + 1) * a (j + e) ≤ a (i + 1 + e) * a j := ih (i + 1) j (by omega)
    rw [show j + (e + 1) = j + e + 1 by omega, show i + (e + 1) = i + 1 + e by omega]
    exact h1.trans h2

/-- An inner index pair dominates an outer pair with the same index sum. -/
theorem inner_outer (ha : TuranSeq a) {u x y v : ℕ} (hux : u ≤ x) (huy : u ≤ y)
    (hsum : x + y = u + v) : a u * a v ≤ a x * a y := by
  rcases le_total x y with hxy | hyx
  · have h := ha.shift (x - u) u y (by omega)
    rwa [show u + (x - u) = x by omega, show y + (x - u) = v by omega] at h
  · have h := ha.shift (y - u) u x (by omega)
    rw [show u + (y - u) = y by omega, show x + (y - u) = v by omega] at h
    rw [mul_comm (a x)]
    exact h

theorem zext_nonneg (ha : TuranSeq a) (z : ℤ) : 0 ≤ zext a z := by
  unfold zext
  split_ifs
  exacts [ha.nonneg _, le_rfl]

/-- The inner–outer inequality for the extension by zero. -/
theorem zext_inner_outer (ha : TuranSeq a) {u x y v : ℤ} (hux : u ≤ x) (huy : u ≤ y)
    (hsum : x + y = u + v) : zext a u * zext a v ≤ zext a x * zext a y := by
  by_cases hu : 0 ≤ u
  · have hx : 0 ≤ x := hu.trans hux
    have hy : 0 ≤ y := hu.trans huy
    have hv : 0 ≤ v := by omega
    simp only [zext, hu, hx, hy, hv, if_true]
    exact ha.inner_outer (by omega) (by omega) (by omega)
  · rw [zext_of_neg a (not_le.mp hu), zero_mul]
    exact mul_nonneg (ha.zext_nonneg x) (ha.zext_nonneg y)

end TuranSeq

/-- The Cauchy product written with extended sequences over a longer range. -/
theorem sum_zext_eq_cauchyConv (a b : ℕ → ℝ) {n N : ℕ} (hN : n + 1 ≤ N) :
    ∑ m ∈ range N, zext a m * zext b ((n : ℤ) - m) = cauchyConv a b n := by
  induction N, hN using Nat.le_induction with
  | base =>
    unfold cauchyConv
    refine sum_congr rfl fun m hm => ?_
    have hm' : m ≤ n := by
      rw [mem_range] at hm
      omega
    rw [zext_natCast, show ((n : ℤ) - m) = ((n - m : ℕ) : ℤ) by push_cast [hm']; ring,
      zext_natCast]
  | succ N hN ih =>
    rw [sum_range_succ, ih, zext_of_neg b (by omega : ((n : ℤ) - N) < 0), mul_zero, add_zero]

/-- The shifted Cauchy product: the first factor delayed by one step. -/
theorem sum_zext_shift_eq_cauchyConv (a b : ℕ → ℝ) {n N : ℕ} (hN : n + 1 ≤ N) :
    ∑ m ∈ range (N + 1), zext a ((m : ℤ) - 1) * zext b ((n : ℤ) + 1 - m) =
      cauchyConv a b n := by
  rw [sum_range_succ', zext_of_neg a (by norm_num : ((0 : ℕ) : ℤ) - 1 < 0), zero_mul, add_zero,
    ← sum_zext_eq_cauchyConv a b hN]
  refine sum_congr rfl fun m _ => ?_
  congr 2 <;> push_cast <;> ring

namespace TuranSeq

variable {a b : ℕ → ℝ}

/-- **Turán sequences are closed under the Cauchy product.** -/
theorem conv (ha : TuranSeq a) (hb : TuranSeq b) : TuranSeq (cauchyConv a b) := by
  refine ⟨fun n => sum_nonneg fun m _ => mul_nonneg (ha.nonneg _) (hb.nonneg _), ?_⟩
  intro i j hij
  set x : ℕ → ℝ := fun m => zext a m with hx
  set u : ℕ → ℝ := fun m => zext a ((m : ℤ) - 1) with hu
  set y : ℕ → ℝ := fun m => zext b (((i + 1 : ℕ) : ℤ) - m) with hy
  set v : ℕ → ℝ := fun m => zext b (((j + 1 : ℕ) : ℤ) - m) with hv
  have hxy : ∑ m ∈ range (j + 2), x m * y m = cauchyConv a b (i + 1) :=
    sum_zext_eq_cauchyConv a b (by omega)
  have hxv : ∑ m ∈ range (j + 2), x m * v m = cauchyConv a b (j + 1) :=
    sum_zext_eq_cauchyConv a b (by omega)
  have huv : ∑ m ∈ range (j + 2), u m * v m = cauchyConv a b j := by
    rw [← sum_zext_shift_eq_cauchyConv a b (n := j) (N := j + 1) (by omega)]
    refine sum_congr rfl fun m _ => ?_
    simp only [hu, hv]
    push_cast
    ring_nf
  have huy : ∑ m ∈ range (j + 2), u m * y m = cauchyConv a b i := by
    rw [← sum_zext_shift_eq_cauchyConv a b (n := i) (N := j + 1) (by omega)]
    refine sum_congr rfl fun m _ => ?_
    simp only [hu, hy]
    push_cast
    ring_nf
  have hBC := binet_cauchy (j + 2) x u y v
  rw [hxy, huv, hxv, huy] at hBC
  have hpos : 0 ≤ ∑ m ∈ range (j + 2), ∑ m' ∈ range (j + 2),
      if m < m' then (x m * u m' - x m' * u m) * (y m * v m' - y m' * v m) else 0 := by
    refine sum_nonneg fun m _ => sum_nonneg fun m' _ => ?_
    split_ifs with hmm
    · refine mul_nonneg ?_ ?_
      · have h := ha.zext_inner_outer (u := (m : ℤ) - 1) (x := m) (y := (m' : ℤ) - 1)
          (v := m') (by omega) (by omega) (by ring)
        simp only [hx, hu]
        linarith [mul_comm (zext a ((m : ℤ) - 1)) (zext a m')]
      · have h := hb.zext_inner_outer (u := ((i + 1 : ℕ) : ℤ) - m')
          (x := ((i + 1 : ℕ) : ℤ) - m) (y := ((j + 1 : ℕ) : ℤ) - m')
          (v := ((j + 1 : ℕ) : ℤ) - m) (by omega) (by push_cast; omega) (by ring)
        simp only [hy, hv]
        linarith
    · exact le_rfl
  nlinarith [hBC, hpos]

/-- **Turán sequences are closed under pointwise limits.** -/
theorem of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℕ → ℝ} {f : ℕ → ℝ}
    (hF : ∀ k, TuranSeq (F k)) (h : ∀ n, Tendsto (fun k => F k n) l (𝓝 (f n))) :
    TuranSeq f := by
  refine ⟨fun n => ge_of_tendsto' (h n) fun k => (hF k).nonneg n, fun i j hij => ?_⟩
  exact le_of_tendsto_of_tendsto' ((h i).mul (h (j + 1))) ((h (i + 1)).mul (h j))
    fun k => (hF k).2 i j hij

/-- A nonnegative sequence supported on `{0, 1, 2}` is a Turán sequence when
`a 0 · a 2 ≤ a 1²`. -/
theorem of_three {a0 a1 a2 : ℝ} (h0 : 0 ≤ a0) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2)
    (h : a0 * a2 ≤ a1 * a1) :
    TuranSeq (fun n => if n = 0 then a0 else if n = 1 then a1 else if n = 2 then a2 else 0) := by
  set s : ℕ → ℝ := fun n => if n = 0 then a0 else if n = 1 then a1 else if n = 2 then a2 else 0
    with hs
  have hnn : ∀ n, 0 ≤ s n := by
    intro n
    simp only [hs]
    split_ifs <;> first | assumption | exact le_rfl
  refine ⟨hnn, fun i j hij => ?_⟩
  by_cases hj : j = 1
  · subst hj
    have hi : i = 0 := by omega
    subst hi
    simpa [hs] using h
  · have hz : s (j + 1) = 0 := by
      have hj0 : j ≠ 0 := by omega
      simp [hs, hj0, hj]
    rw [hz, mul_zero]
    exact mul_nonneg (hnn _) (hnn _)

end TuranSeq

end GaloisForLFunctions.HTGeometry
