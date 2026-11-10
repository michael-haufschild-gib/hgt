import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheHodgeIndexHoldsAtEveryScaleOnShortWindows
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.WeilsFormInTheGaugeOfTheFlatTail

/-!
# The index of a window is finite at every scale

On a window of ratio above `19/18` the inequality `D·D ≤ 2 d₁ d₂` is not known at finite scale.
This file bounds the number of directions in which it can fail, uniformly in the scale.

Cut the window `(N, N + M]` into blocks of `B` consecutive degree points. For every real divisor
whose sum over each block vanishes,

  `D·D ≤ 0` and `2 d₁ d₂ − D·D ≥ 0`   (`combForm_nonneg_of_blockSum_eq_zero`),

as soon as `H_{2B} + 2 + M/(4N) + 2ψ(Q) ≤ log(N/2π)`, where `Q` bounds the ratio of the window.
The blocks then have `B ≈ N/R` points with `R` depending on `Q` only
(`exists_blockSize_combForm_nonneg`), and the window has fewer than `2QR` blocks
(`blockIndex_lt`): at every scale Weil's form on a window of ratio at most `Q` is nonnegative on
a subspace of real divisors of codimension below `2QR`. The index of the pairing on a window is
finite at finite scale, with a bound that does not depend on the scale.

The proof is a Schur test after one subtraction.

* **The block kernel** (`blockKernel`): `1/(2B|i − j|)` between two blocks at distance
  `|i − j| ≥ 2`. It pairs two divisors through their block sums and vanishes on the divisors
  above (`sum_mul_mul_blockKernel_eq_zero`).
* **Far pairs** (`abs_inv_sub_blockKernel_le`): between blocks at distance at least `2` the
  singular part `1/(2|m − n|)` of the jet differs from the block kernel by at most
  `B/(m − n)²`.
* **The row** (`sum_abs_pairKernel_sub_blockKernel_le`): the row of the pairing minus the block
  kernel is at most `H_{2B} + 2 + M/(4N) + 2ψ(Q)`: near pairs, far pairs, the regular part of
  the jets, and the contacts, whose quotients are at most `Q`.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

/-! ### Blocks -/

/-- The block of the degree point `n` of a window above `N`, for blocks of `B` points. -/
def blockIndex (N B n : ℕ) : ℕ := (n - N - 1) / B

/-- The kernel of two blocks at distance at least `2`: `1/(2B|i − j|)`. -/
def blockWeight (B i j : ℕ) : ℝ :=
  if i + 2 ≤ j ∨ j + 2 ≤ i then 1 / (2 * (B : ℝ) * |(i : ℝ) - j|) else 0

/-- The block kernel on the degree points. -/
def blockKernel (N B m n : ℕ) : ℝ := blockWeight B (blockIndex N B m) (blockIndex N B n)

theorem blockWeight_comm (B i j : ℕ) : blockWeight B i j = blockWeight B j i := by
  unfold blockWeight
  rw [abs_sub_comm]
  simp only [or_comm]

theorem blockWeight_self (B i : ℕ) : blockWeight B i i = 0 := by
  unfold blockWeight
  rw [if_neg (by omega)]

theorem blockKernel_comm (N B m n : ℕ) : blockKernel N B m n = blockKernel N B n m :=
  blockWeight_comm _ _ _

/-- **The block kernel sees only the block sums.** It vanishes on a divisor whose sum over every
block is zero. -/
theorem sum_mul_mul_blockKernel_eq_zero (N B : ℕ) (S : Finset ℕ) (c : ℕ → ℝ)
    (hzero : ∀ j : ℕ, ∑ n ∈ S.filter (fun n => blockIndex N B n = j), c n = 0) :
    ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * blockKernel N B m n = 0 := by
  refine Finset.sum_eq_zero fun n hn => ?_
  have hfull : ∑ m ∈ S.erase n, c m * c n * blockKernel N B m n =
      ∑ m ∈ S, c m * c n * blockKernel N B m n := by
    rw [← Finset.add_sum_erase S _ hn, blockKernel, blockWeight_self, mul_zero, zero_add]
  have hfib : ∑ m ∈ S, c m * c n * blockKernel N B m n =
      ∑ i ∈ S.image (blockIndex N B), ∑ m ∈ S.filter (fun m => blockIndex N B m = i),
        c m * c n * blockKernel N B m n :=
    (Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm) _).symm
  rw [hfull, hfib]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hconst : ∀ m ∈ S.filter (fun m => blockIndex N B m = i),
      c m * c n * blockKernel N B m n = c m * (c n * blockWeight B i (blockIndex N B n)) := by
    intro m hm
    rw [blockKernel, (Finset.mem_filter.mp hm).2]
    ring
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul, hzero i, zero_mul]

/-! ### Far pairs -/

/-- The comparison of `1/(2x)` with `1/(2Bk)` for `(k − 1)B < x < (k + 1)B`. -/
theorem abs_inv_sub_inv_le {x b k : ℝ} (hx : 0 < x) (hb : 0 < b) (hk : 2 ≤ k)
    (h1 : (k - 1) * b < x) (h2 : x < (k + 1) * b) :
    |1 / (2 * x) - 1 / (2 * b * k)| ≤ b / x ^ 2 := by
  have hk0 : 0 < k := by linarith
  have e : 1 / (2 * x) - 1 / (2 * b * k) = (b * k - x) / (2 * x * b * k) := by
    field_simp
  have hden : 0 < 2 * x * b * k := by positivity
  rw [e, abs_div, abs_of_pos hden, div_le_div_iff₀ hden (by positivity)]
  have habs : |b * k - x| ≤ b := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hx2 : x ≤ 2 * k * b := by nlinarith
  calc |b * k - x| * x ^ 2 ≤ b * x ^ 2 := mul_le_mul_of_nonneg_right habs (sq_nonneg x)
    _ = b * x * x := by ring
    _ ≤ b * x * (2 * k * b) := mul_le_mul_of_nonneg_left hx2 (by positivity)
    _ = b * (2 * x * b * k) := by ring

/-- The distance of two degree points of the window, by their blocks. -/
theorem dist_bounds_of_blockIndex {N B m n : ℕ} (hB : 0 < B) (hm : N < m) (hn : N < n)
    (hmn : blockIndex N B m ≤ blockIndex N B n) :
    (blockIndex N B n - blockIndex N B m) * B < n - m + B ∧
      n - m < (blockIndex N B n - blockIndex N B m + 1) * B ∧ m ≤ n + B := by
  unfold blockIndex at hmn ⊢
  have e1 := Nat.div_add_mod (m - N - 1) B
  have e2 := Nat.div_add_mod (n - N - 1) B
  have r1 := Nat.mod_lt (m - N - 1) hB
  have r2 := Nat.mod_lt (n - N - 1) hB
  set i := (m - N - 1) / B
  set j := (n - N - 1) / B
  obtain ⟨k, hk⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  have hjk : j - i = k := by omega
  rw [hjk]
  have e3 : B * j = B * i + B * k := by rw [hk]; ring
  have e4 : k * B = B * k := mul_comm _ _
  have e5 : (k + 1) * B = B * k + B := by ring
  rw [e4, e5]
  omega

/-- **Far pairs.** Between two blocks at distance at least `2`, the singular part of the jet
differs from the block kernel by at most `B/(m − n)²`, and the points are more than `B` apart. -/
theorem abs_inv_sub_blockKernel_le {N B m n : ℕ} (hB : 0 < B) (hm : N < m) (hn : N < n)
    (hfar : blockIndex N B m + 2 ≤ blockIndex N B n ∨ blockIndex N B n + 2 ≤ blockIndex N B m) :
    |1 / (2 * |(m : ℝ) - n|) - blockKernel N B m n| ≤ B / ((m : ℝ) - n) ^ 2 ∧
      (B : ℝ) < |(m : ℝ) - n| := by
  -- by symmetry the block of `m` is the lower one
  wlog h : blockIndex N B m + 2 ≤ blockIndex N B n generalizing m n
  · have hfar' := hfar.resolve_left h
    have := this hn hm (Or.inl hfar') hfar'
    rw [abs_sub_comm (n : ℝ) m, blockKernel_comm,
      show ((n : ℝ) - m) ^ 2 = ((m : ℝ) - n) ^ 2 by ring] at this
    exact this
  obtain ⟨d1, d2, -⟩ := dist_bounds_of_blockIndex hB hm hn (by omega)
  set i := blockIndex N B m with hi
  set j := blockIndex N B n with hj
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hmn : m < n := by
    by_contra hle
    have h0 : n - m = 0 := by omega
    have hpos : 2 * B ≤ (j - i) * B := Nat.mul_le_mul_right B (by omega)
    omega
  have hx : (0 : ℝ) < (n : ℝ) - m := by
    have : (m : ℝ) < n := by exact_mod_cast hmn
    linarith
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := Nat.cast_sub hmn.le
  have hk : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := Nat.cast_sub (by omega)
  have hk2 : (2 : ℝ) ≤ (j : ℝ) - i := by
    rw [← hk]
    exact_mod_cast (by omega : 2 ≤ j - i)
  have b1 : ((j : ℝ) - i - 1) * B < (n : ℝ) - m := by
    have : (((j - i) * B : ℕ) : ℝ) < ((n - m + B : ℕ) : ℝ) := by exact_mod_cast d1
    push_cast at this
    rw [hk, hcast] at this
    linarith
  have b2 : (n : ℝ) - m < ((j : ℝ) - i + 1) * B := by
    have : ((n - m : ℕ) : ℝ) < (((j - i + 1) * B : ℕ) : ℝ) := by exact_mod_cast d2
    push_cast at this
    rw [hk, hcast] at this
    linarith
  have habs : |(m : ℝ) - n| = (n : ℝ) - m := by rw [abs_sub_comm, abs_of_pos hx]
  have hw : blockKernel N B m n = 1 / (2 * (B : ℝ) * ((j : ℝ) - i)) := by
    rw [blockKernel, blockWeight, ← hi, ← hj, if_pos (Or.inl h), abs_sub_comm,
      abs_of_pos (by linarith)]
  rw [habs, hw, show ((m : ℝ) - n) ^ 2 = ((n : ℝ) - m) ^ 2 by ring]
  refine ⟨abs_inv_sub_inv_le hx hB' hk2 b1 b2, ?_⟩
  nlinarith

/-! ### Sums over distances -/

/-- A sum of a nonnegative function of the distance to `n` over distinct degree points is at
most twice its sum over the distances. -/
theorem sum_dist_le (T : Finset ℕ) (n : ℕ) (h : ℕ → ℝ) (hh : ∀ d, 0 ≤ h d) (D : Finset ℕ)
    (hT : ∀ m ∈ T, Nat.dist m n ∈ D) :
    ∑ m ∈ T, h (Nat.dist m n) ≤ 2 * ∑ d ∈ D, h d := by
  rw [← Finset.sum_filter_add_sum_filter_not T (· < n)]
  have side : ∀ U : Finset ℕ, U ⊆ T → (∀ x ∈ U, ∀ y ∈ U, Nat.dist x n = Nat.dist y n → x = y) →
      ∑ m ∈ U, h (Nat.dist m n) ≤ ∑ d ∈ D, h d := by
    intro U hU hinj
    rw [← Finset.sum_image (f := h) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) fun d _ _ => hh d
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
    exact hT m (hU hm)
  have h1 := side (T.filter (· < n)) (Finset.filter_subset _ _) fun x hx y hy hxy => by
    have hx' : x < n := (Finset.mem_filter.mp hx).2
    have hy' : y < n := (Finset.mem_filter.mp hy).2
    rw [Nat.dist_eq_sub_of_le hx'.le, Nat.dist_eq_sub_of_le hy'.le] at hxy
    omega
  have h2 := side (T.filter fun m => ¬ m < n) (Finset.filter_subset _ _) fun x hx y hy hxy => by
    have hx' : n ≤ x := not_lt.mp (Finset.mem_filter.mp hx).2
    have hy' : n ≤ y := not_lt.mp (Finset.mem_filter.mp hy).2
    rw [Nat.dist_eq_sub_of_le_right hx', Nat.dist_eq_sub_of_le_right hy'] at hxy
    omega
  linarith

theorem cast_dist (m n : ℕ) : ((Nat.dist m n : ℕ) : ℝ) = |(m : ℝ) - n| := by
  rcases le_total m n with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_sub_comm,
      abs_of_nonneg (by have : (m : ℝ) ≤ n := by exact_mod_cast h
                        linarith)]
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h,
      abs_of_nonneg (by have : (n : ℝ) ≤ m := by exact_mod_cast h
                        linarith)]

/-- `Σ_{B < d ≤ D} 1/d² ≤ 1/B`. -/
theorem sum_inv_sq_Ioc_le {B : ℕ} (hB : 0 < B) (D : ℕ) :
    ∑ d ∈ Ioc B (B + D), 1 / (d : ℝ) ^ 2 ≤ 1 / (B : ℝ) - 1 / ((B : ℝ) + D) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  induction D with
  | zero => simp
  | succ D ih =>
    rw [← Nat.add_assoc, Finset.sum_Ioc_succ_top (by omega : B ≤ B + D)]
    have hpos : (0 : ℝ) < (B : ℝ) + D := by positivity
    have hstep : 1 / (((B + D + 1 : ℕ) : ℝ)) ^ 2 ≤
        1 / ((B : ℝ) + D) - 1 / ((B : ℝ) + (D + 1 : ℕ)) := by
      push_cast
      rw [div_sub_div _ _ hpos.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- The majorant of the singular part of the jet minus the block kernel at the distance `d`. -/
def distMajorant (B d : ℕ) : ℝ :=
  (if d < 2 * B then 1 / (2 * (d : ℝ)) else 0) + (if B < d then (B : ℝ) / (d : ℝ) ^ 2 else 0)

theorem distMajorant_nonneg (B d : ℕ) : 0 ≤ distMajorant B d := by
  unfold distMajorant
  refine add_nonneg ?_ ?_ <;> split_ifs <;> positivity

/-- The majorant summed over the distances `1 ≤ d ≤ D`: at most `H_{2B}/2 + 1`. -/
theorem sum_distMajorant_le {B : ℕ} (hB : 0 < B) (D : ℕ) :
    ∑ d ∈ Icc 1 D, distMajorant B d ≤ harm (2 * B) / 2 + 1 := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  unfold distMajorant
  rw [Finset.sum_add_distrib]
  have h1 : ∑ d ∈ Icc 1 D, (if d < 2 * B then 1 / (2 * (d : ℝ)) else 0) ≤ harm (2 * B) / 2 := by
    rw [← Finset.sum_filter, ← sum_Icc_one_div, Finset.sum_div]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) fun d _ _ => by positivity).trans
      (le_of_eq (Finset.sum_congr rfl fun d _ => by ring))
    obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd1).1, hd2.le⟩
  have h2 : ∑ d ∈ Icc 1 D, (if B < d then (B : ℝ) / (d : ℝ) ^ 2 else 0) ≤ 1 := by
    rw [← Finset.sum_filter]
    have hsub : (Icc 1 D).filter (fun d => B < d) ⊆ Ioc B (B + D) := fun d hd => by
      obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_Ioc.mpr ⟨hd2, by have := (Finset.mem_Icc.mp hd1).2; omega⟩
    have hle : ∑ d ∈ (Icc 1 D).filter (fun d => B < d), (B : ℝ) / (d : ℝ) ^ 2 ≤
        ∑ d ∈ Ioc B (B + D), (B : ℝ) / (d : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => by positivity
    have hsum : ∑ d ∈ Ioc B (B + D), (B : ℝ) / (d : ℝ) ^ 2 =
        B * ∑ d ∈ Ioc B (B + D), 1 / (d : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    have hbound := sum_inv_sq_Ioc_le hB D
    have hfin : (B : ℝ) * (1 / (B : ℝ) - 1 / ((B : ℝ) + D)) ≤ 1 := by
      have h0 : 0 ≤ (B : ℝ) * (1 / ((B : ℝ) + D)) := by positivity
      have h1 : (B : ℝ) * (1 / (B : ℝ)) = 1 := by field_simp
      nlinarith
    calc ∑ d ∈ (Icc 1 D).filter (fun d => B < d), (B : ℝ) / (d : ℝ) ^ 2
        ≤ B * ∑ d ∈ Ioc B (B + D), 1 / (d : ℝ) ^ 2 := hle.trans (le_of_eq hsum)
      _ ≤ B * (1 / (B : ℝ) - 1 / ((B : ℝ) + D)) := mul_le_mul_of_nonneg_left hbound hB'.le
      _ ≤ 1 := hfin
  linarith

/-! ### The row of the pairing minus the block kernel -/

/-- The singular part of the jet minus the block kernel is at most the majorant of the
distance. -/
theorem abs_inv_sub_blockKernel_le_distMajorant {N B m n : ℕ} (hB : 0 < B) (hm : N < m)
    (hn : N < n) (hmn : m ≠ n) :
    |1 / (2 * |(m : ℝ) - n|) - blockKernel N B m n| ≤ distMajorant B (Nat.dist m n) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hd0 : 0 < Nat.dist m n := Nat.dist_pos_of_ne hmn
  have hd0' : (0 : ℝ) < |(m : ℝ) - n| := by
    rw [← cast_dist]
    exact_mod_cast hd0
  by_cases hfar : blockIndex N B m + 2 ≤ blockIndex N B n ∨
      blockIndex N B n + 2 ≤ blockIndex N B m
  · obtain ⟨h1, h2⟩ := abs_inv_sub_blockKernel_le hB hm hn hfar
    have hBd : B < Nat.dist m n := by
      have : (B : ℝ) < (Nat.dist m n : ℕ) := by rwa [cast_dist]
      exact_mod_cast this
    have hsq : ((m : ℝ) - n) ^ 2 = ((Nat.dist m n : ℕ) : ℝ) ^ 2 := by rw [cast_dist, sq_abs]
    unfold distMajorant
    rw [if_pos hBd, ← hsq]
    have : (0 : ℝ) ≤ if Nat.dist m n < 2 * B then 1 / (2 * ((Nat.dist m n : ℕ) : ℝ)) else 0 := by
      split_ifs <;> positivity
    linarith
  · -- near pairs: the block kernel vanishes and the distance is below `2B`
    have hw : blockKernel N B m n = 0 := by rw [blockKernel, blockWeight, if_neg hfar]
    have hnear : Nat.dist m n < 2 * B := by
      rcases le_total (blockIndex N B m) (blockIndex N B n) with hle | hle
      · obtain ⟨-, d2, d3⟩ := dist_bounds_of_blockIndex hB hm hn hle
        have hk : blockIndex N B n - blockIndex N B m + 1 ≤ 2 := by omega
        have hk' : (blockIndex N B n - blockIndex N B m + 1) * B ≤ 2 * B :=
          Nat.mul_le_mul_right B hk
        rw [Nat.dist]
        omega
      · obtain ⟨-, d2, d3⟩ := dist_bounds_of_blockIndex hB hn hm hle
        have hk : blockIndex N B m - blockIndex N B n + 1 ≤ 2 := by omega
        have hk' : (blockIndex N B m - blockIndex N B n + 1) * B ≤ 2 * B :=
          Nat.mul_le_mul_right B hk
        rw [Nat.dist]
        omega
    unfold distMajorant
    rw [hw, sub_zero, if_pos hnear, abs_of_pos (by positivity), cast_dist]
    have : (0 : ℝ) ≤ if B < Nat.dist m n then (B : ℝ) / |(m : ℝ) - n| ^ 2 else 0 := by
      split_ifs <;> positivity
    linarith

/-- The contacts of `Γ_n` with the other graphs of a window of ratio at most `Q`: at most
`2ψ(Q)`. -/
theorem sum_contact_erase_le {N M Q : ℕ} (hN : 0 < N) (hQ : N + M ≤ Q * N) {S : Finset ℕ}
    (hS : S ⊆ Ioc N (N + M)) {n : ℕ} (hn : n ∈ S) :
    ∑ m ∈ S.erase n, contact m n ≤ 2 * chebyshev Q := by
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp (hS hn)
  have hmem : ∀ m ∈ S.erase n, N < m ∧ m ≤ N + M := fun m hm =>
    Finset.mem_Ioc.mp (hS (Finset.mem_of_mem_erase hm))
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt k : ℝ) := fun k =>
    ArithmeticFunction.vonMangoldt_nonneg
  rw [sum_contact_erase]
  have hlow : ∑ m ∈ (S.erase n).filter (· ∣ n), (ArithmeticFunction.vonMangoldt (n / m) : ℝ) ≤
      chebyshev Q := by
    rw [chebyshev, ← Finset.sum_image (f := fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℝ))
      (g := fun m => n / m)]
    · refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => hnn k
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hm1, hd⟩ := Finset.mem_filter.mp hm
      obtain ⟨hmN, -⟩ := hmem m hm1
      refine Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hd) (by omega), ?_⟩
      exact Nat.div_le_of_le_mul (by nlinarith)
    · intro x hx y hy hxy
      obtain ⟨hx1, hxd⟩ := Finset.mem_filter.mp hx
      obtain ⟨hy1, hyd⟩ := Finset.mem_filter.mp hy
      have hy0 : 0 < y := by have := (hmem y hy1).1; omega
      have e1 := Nat.mul_div_cancel' hxd
      have e2 := Nat.mul_div_cancel' hyd
      have hxy' : n / x = n / y := hxy
      rw [hxy'] at e1
      have ht : 0 < n / y := Nat.div_pos (Nat.le_of_dvd (by omega) hyd) hy0
      exact Nat.eq_of_mul_eq_mul_right ht (e1.trans e2.symm)
  have hhigh : ∑ m ∈ (S.erase n).filter (n ∣ ·), (ArithmeticFunction.vonMangoldt (m / n) : ℝ) ≤
      chebyshev Q := by
    rw [chebyshev, ← Finset.sum_image (f := fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℝ))
      (g := fun m => m / n)]
    · refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ => hnn k
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hm1, hd⟩ := Finset.mem_filter.mp hm
      obtain ⟨hmN, hmtop⟩ := hmem m hm1
      refine Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hd) (by omega), ?_⟩
      exact Nat.div_le_of_le_mul (by nlinarith)
    · intro x hx y hy hxy
      obtain ⟨-, ⟨a, ha⟩⟩ := Finset.mem_filter.mp hx
      obtain ⟨-, ⟨b, hb⟩⟩ := Finset.mem_filter.mp hy
      simp only at hxy
      rw [ha, hb, Nat.mul_div_cancel_left a (by omega), Nat.mul_div_cancel_left b (by omega)] at hxy
      rw [ha, hb, hxy]
  linarith

/-- **The row of the pairing minus the block kernel.** -/
theorem sum_abs_pairKernel_sub_blockKernel_le {N M B Q : ℕ} (hN : 0 < N) (hB : 0 < B)
    (hQ : N + M ≤ Q * N) {S : Finset ℕ} (hS : S ⊆ Ioc N (N + M)) {n : ℕ} (hn : n ∈ S) :
    ∑ m ∈ S.erase n, |pairKernel m n - blockKernel N B m n| ≤
      harm (2 * B) + 2 + (M : ℝ) / (4 * N) + 2 * chebyshev Q := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp (hS hn)
  have hmem : ∀ m ∈ S.erase n, N < m ∧ m ≤ N + M := fun m hm =>
    Finset.mem_Ioc.mp (hS (Finset.mem_of_mem_erase hm))
  -- termwise: the singular part against the block kernel, the regular part, the contact
  have hterm : ∀ m ∈ S.erase n, |pairKernel m n - blockKernel N B m n| ≤
      distMajorant B (Nat.dist m n) + 1 / (4 * (N : ℝ)) + contact m n := by
    intro m hm
    obtain ⟨hmN, -⟩ := hmem m hm
    have hmN' : (N : ℝ) < m := by exact_mod_cast hmN
    have hnN' : (N : ℝ) < n := by exact_mod_cast hn1
    have h1 := abs_inv_sub_blockKernel_le_distMajorant hB hmN hn1 (Finset.ne_of_mem_erase hm)
    have hsplit : pairKernel m n - blockKernel N B m n =
        (1 / (2 * |(m : ℝ) - n|) - blockKernel N B m n) + 1 / ((m : ℝ) + n) / 2 +
          contact m n := by
      rw [pairKernel, jetKernel]
      ring
    have hreg : 1 / ((m : ℝ) + n) / 2 ≤ 1 / (4 * (N : ℝ)) := by
      rw [div_div]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hreg0 : (0 : ℝ) ≤ 1 / ((m : ℝ) + n) / 2 := by positivity
    rw [hsplit]
    calc |(1 / (2 * |(m : ℝ) - n|) - blockKernel N B m n) + 1 / ((m : ℝ) + n) / 2 +
          contact m n|
        ≤ |1 / (2 * |(m : ℝ) - n|) - blockKernel N B m n| + |1 / ((m : ℝ) + n) / 2| +
            |contact m n| := abs_add_three _ _ _
      _ ≤ distMajorant B (Nat.dist m n) + 1 / (4 * (N : ℝ)) + contact m n := by
          rw [abs_of_nonneg hreg0, abs_of_nonneg (contact_nonneg m n)]
          linarith
  have hcard : ((S.erase n).card : ℝ) ≤ M := by
    have h1 : (S.erase n).card ≤ S.card := Finset.card_le_card (Finset.erase_subset n S)
    have h2 : S.card ≤ (Ioc N (N + M)).card := Finset.card_le_card hS
    rw [Nat.card_Ioc] at h2
    exact_mod_cast (by omega : (S.erase n).card ≤ M)
  have hdist : ∑ m ∈ S.erase n, distMajorant B (Nat.dist m n) ≤ harm (2 * B) + 2 := by
    have h := sum_dist_le (S.erase n) n (distMajorant B) (distMajorant_nonneg B) (Icc 1 M)
      fun m hm => by
        obtain ⟨hmN, hmtop⟩ := hmem m hm
        have hne : m ≠ n := Finset.ne_of_mem_erase hm
        have hpos := Nat.dist_pos_of_ne hne
        refine Finset.mem_Icc.mpr ⟨hpos, ?_⟩
        rw [Nat.dist]
        omega
    have h2 := sum_distMajorant_le hB M
    linarith
  have hregsum : ∑ _m ∈ S.erase n, 1 / (4 * (N : ℝ)) ≤ (M : ℝ) / (4 * N) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    calc ((S.erase n).card : ℝ) * (1 / (4 * (N : ℝ))) ≤ M * (1 / (4 * (N : ℝ))) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (M : ℝ) / (4 * N) := by ring
  calc ∑ m ∈ S.erase n, |pairKernel m n - blockKernel N B m n|
      ≤ ∑ m ∈ S.erase n, (distMajorant B (Nat.dist m n) + 1 / (4 * (N : ℝ)) + contact m n) :=
        Finset.sum_le_sum hterm
    _ = ∑ m ∈ S.erase n, distMajorant B (Nat.dist m n) + ∑ _m ∈ S.erase n, 1 / (4 * (N : ℝ)) +
          ∑ m ∈ S.erase n, contact m n := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ harm (2 * B) + 2 + (M : ℝ) / (4 * N) + 2 * chebyshev Q := by
        linarith [sum_contact_erase_le hN hQ hS hn]

/-! ### The Schur test -/

/-- **The Schur test for a symmetric kernel**: its form is at most its rows of absolute values on
the squares. -/
theorem sum_mul_mul_le_abs_row (S : Finset ℕ) (K : ℕ → ℕ → ℝ) (hK : ∀ m n, K m n = K n m)
    (c : ℕ → ℝ) :
    ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * K m n ≤
      ∑ n ∈ S, c n ^ 2 * ∑ m ∈ S.erase n, |K m n| := by
  have hLK := sum_mul_mul_eq_row_sub_dirichlet S (fun m n => |K m n|)
    (fun m n => by rw [hK]) fun n => |c n|
  have hterm : ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * K m n ≤
      ∑ n ∈ S, ∑ m ∈ S.erase n, |c m| * |c n| * |K m n| :=
    Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => by
      rw [← abs_mul, ← abs_mul]
      exact le_abs_self _
  have hD : 0 ≤ ∑ n ∈ S, ∑ m ∈ S.erase n, (|c m| - |c n|) ^ 2 * |K m n| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hsq : ∑ n ∈ S, |c n| ^ 2 * ∑ m ∈ S.erase n, |K m n| =
      ∑ n ∈ S, c n ^ 2 * ∑ m ∈ S.erase n, |K m n| :=
    Finset.sum_congr rfl fun n _ => by rw [sq_abs]
  rw [hsq] at hLK
  linarith

/-! ### The index of a window -/

/-- **On the divisors with vanishing block sums the pairing is nonpositive and Weil's form is
nonnegative.** Let `S` be a set of degree points of `(N, N + M]`, of ratio at most `Q`, cut into
blocks of `B` points with `H_{2B} + 2 + M/(4N) + 2ψ(Q) ≤ log(N/2π)`. For every real divisor on `S`
whose sum over each block vanishes: `D·D ≤ 0`, `d₂ = 0` and `2 d₁ d₂ − D·D ≥ 0`. -/
theorem combForm_nonneg_of_blockSum_eq_zero {N M B Q : ℕ} (hN : 0 < N) (hB : 0 < B)
    (hQ : N + M ≤ Q * N)
    (hsize : harm (2 * B) + 2 + (M : ℝ) / (4 * N) + 2 * chebyshev Q ≤
      Real.log ((N : ℝ) / (2 * Real.pi)))
    {S : Finset ℕ} (hS : S ⊆ Ioc N (N + M)) (c : ℕ → ℝ)
    (hzero : ∀ j : ℕ, ∑ n ∈ S.filter (fun n => blockIndex N B n = j), c n = 0) :
    combPairing S c ≤ 0 ∧ 0 ≤ combForm S c := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  -- the second degree vanishes
  have hdeg : degTwo S c = 0 := by
    rw [degTwo, ← Finset.sum_fiberwise_of_maps_to
      (fun n hn => Finset.mem_image_of_mem (blockIndex N B) hn) c]
    exact Finset.sum_eq_zero fun j _ => hzero j
  -- subtract the block kernel
  have hsub : ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * pairKernel m n =
      ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * (pairKernel m n - blockKernel N B m n) := by
    have h0 := sum_mul_mul_blockKernel_eq_zero N B S c hzero
    have : ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * (pairKernel m n - blockKernel N B m n) =
        ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * pairKernel m n -
          ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * blockKernel N B m n := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [this, h0, sub_zero]
  have hschur := sum_mul_mul_le_abs_row S (fun m n => pairKernel m n - blockKernel N B m n)
    (fun m n => by rw [pairKernel_comm, blockKernel_comm]) c
  have hrow : ∑ n ∈ S, c n ^ 2 * ∑ m ∈ S.erase n, |pairKernel m n - blockKernel N B m n| ≤
      ∑ n ∈ S, c n ^ 2 * counterterm n := by
    refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hnN : (N : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp (hS hn)).1
    have hct : Real.log ((N : ℝ) / (2 * Real.pi)) ≤ counterterm n :=
      Real.log_le_log (by positivity)
        (div_le_div_of_nonneg_right hnN.le (by positivity))
    exact (sum_abs_pairKernel_sub_blockKernel_le hN hB hQ hS hn).trans (hsize.trans hct)
  have hpair : combPairing S c ≤ 0 := by
    rw [combPairing, hsub]
    linarith
  refine ⟨hpair, ?_⟩
  rw [combForm, hdeg, mul_zero, mul_zero]
  linarith

/-- The number of blocks of a window of ratio at most `Q` is below `2QR` for blocks of `⌊N/R⌋`
points. -/
theorem blockIndex_lt {N M Q R n : ℕ} (hR : 0 < R) (hRN : R ≤ N) (hQ : N + M ≤ Q * N)
    (hn : n ∈ Ioc N (N + M)) : blockIndex N (N / R) n < 2 * Q * R := by
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
  have hB : 0 < N / R := Nat.div_pos hRN hR
  rw [blockIndex, Nat.div_lt_iff_lt_mul hB]
  have h1 : N < 2 * R * (N / R) := by
    have e := Nat.div_add_mod N R
    have r := Nat.mod_lt N hR
    nlinarith
  calc n - N - 1 < Q * N := by omega
    _ ≤ Q * (2 * R * (N / R)) := Nat.mul_le_mul_left Q h1.le
    _ = 2 * Q * R * (N / R) := by ring

/-- **The index of a window is finite at every scale.** For every bound `Q` on the ratio there is
`R` such that at every scale `N ≥ R`, on every set of degree points of a window `(N, N + M]` of
ratio at most `Q`, cut into blocks of `⌊N/R⌋` points, every real divisor whose sum over each
block vanishes has `D·D ≤ 0` and `2 d₁ d₂ − D·D ≥ 0`. The blocks are fewer than `2QR`
(`blockIndex_lt`). -/
theorem exists_blockSize_combForm_nonneg (Q : ℕ) :
    ∃ R : ℕ, 0 < R ∧ ∀ N M : ℕ, R ≤ N → N + M ≤ Q * N → ∀ S : Finset ℕ, S ⊆ Ioc N (N + M) →
      ∀ c : ℕ → ℝ, (∀ j : ℕ, ∑ n ∈ S.filter (fun n => blockIndex N (N / R) n = j), c n = 0) →
        combPairing S c ≤ 0 ∧ 0 ≤ combForm S c := by
  set E : ℝ := 3 + (Q : ℝ) / 4 + 2 * chebyshev Q + Real.log (4 * Real.pi) with hE
  refine ⟨⌈Real.exp E⌉₊, Nat.ceil_pos.mpr (Real.exp_pos E), ?_⟩
  intro N M hRN hQ S hS c hzero
  set R := ⌈Real.exp E⌉₊ with hRdef
  have hR : 0 < R := Nat.ceil_pos.mpr (Real.exp_pos E)
  have hN : 0 < N := lt_of_lt_of_le hR hRN
  have hB : 0 < N / R := Nat.div_pos hRN hR
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hB' : (0 : ℝ) < ((N / R : ℕ) : ℝ) := by exact_mod_cast hB
  refine combForm_nonneg_of_blockSum_eq_zero hN hB hQ ?_ hS c hzero
  -- the size of the blocks
  have hharm : harm (2 * (N / R)) ≤ 1 + Real.log ((2 * (N / R) : ℕ) : ℝ) := by
    rw [harm_eq_harmonic]
    exact harmonic_le_one_add_log _
  have hBle : ((N / R : ℕ) : ℝ) ≤ (N : ℝ) / R := by
    rw [le_div_iff₀ hR']
    exact_mod_cast Nat.div_mul_le_self N R
  have hlogB : Real.log ((2 * (N / R) : ℕ) : ℝ) ≤ Real.log 2 + Real.log N - E := by
    have hRE : E ≤ Real.log R := by
      rw [Real.le_log_iff_exp_le hR']
      exact Nat.le_ceil _
    have h1 : Real.log ((2 * (N / R) : ℕ) : ℝ) ≤ Real.log (2 * ((N : ℝ) / R)) := by
      refine Real.log_le_log (by positivity) ?_
      push_cast
      linarith
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_div hN'.ne' hR'.ne'] at h1
    linarith
  have hMN : (M : ℝ) / (4 * N) ≤ (Q : ℝ) / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : ((N + M : ℕ) : ℝ) ≤ ((Q * N : ℕ) : ℝ) := by exact_mod_cast hQ
    push_cast at this
    nlinarith
  have hlogN : Real.log ((N : ℝ) / (2 * Real.pi)) = Real.log N - Real.log (2 * Real.pi) :=
    Real.log_div hN'.ne' (by positivity)
  have h4π : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
    rw [show (4 : ℝ) * Real.pi = 2 * (2 * Real.pi) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  rw [hlogN]
  rw [hE] at hlogB
  linarith

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
