import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheIndexOfAWindowIsFiniteAtEveryScale
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheInequalityAtFiniteScaleDecidesTheLimit
import GaloisForLFunctions.HTGeometry.HarmonicTailSquareIdentity

/-!
# The inequality at finite scale is decided on block averages

On a window of ratio at most `Q` cut into blocks of `B` points, Weil's form is at least
`(log(N/2π) − ρ) Σ c_n²` on the divisors with vanishing block sums, `ρ` the row of the pairing
minus the block kernel. This file treats the complement, the divisors that are constant on the
blocks, and the cross term of the two.

Write a real divisor on a window of complete blocks as `c = s + z`, with `s` its block averages
and `z` of vanishing block sums. Then

  `𝔚(c) ≥ 𝔚(s) − ε Σ c_n²`   as soon as `C_Q²/ε ≤ log(N/2π) − ρ`   (`combForm_ge_blockMean`),

with `C_Q = 12 + 2Q + 2ψ(Q)`. For blocks of `⌊N/R⌋` points the margin is `log R − O_Q(1)`: for
every `ε > 0` there is `R`, depending on `Q` and `ε` only, such that at every scale the form of a
real divisor is at least the form of its block averages minus `ε Σ c_n²`
(`exists_blockSize_combForm_ge_blockMean`). The block averages live on fewer than `2QR` blocks:
the inequality `D·D ≤ 2 d₁ d₂` up to `ε Σ c_n²` on all real divisors of a window is a statement
about a space of divisors whose dimension does not depend on the scale.

* **The cross term** (`two_mul_abs_formBilin_le`): for `s` constant on blocks and `z` of
  vanishing block sums, `2|𝔚(s, z)| ≤ C_Q (p Σ s_n² + q Σ z_n²)` whenever `pq = 1`. The constant
  does not depend on the block size, although the rows of the pairing grow like `log B`:
  - the block kernel pairs `z` to zero with every divisor (`sum_mul_blockKernel_eq_zero`);
  - between points more than `B` apart, and for the regular part of the jets and the contacts,
    the rows are bounded (`sum_abs_farKernel_le`): a Schur test;
  - between points at most `B` apart the potential of `s` is `s_n H_B` plus a remainder carried
    by the jumps of `s` to the two adjacent blocks, with the weights `H_B − H_a` at the position
    `a` (`sum_blockFunction_mul_nearKernel`). The first term is constant on blocks and pairs to
    zero with `z`; the weights have `Σ_a (H_B − H_a)² = 2B − H_B`, so the remainder has norm at
    most `2√2 ‖s‖` (`sum_nearRemainder_sq_le`);
  - the pole and the counterterm vary by `B/N²` and `B/N` inside a block
    (`two_mul_abs_degTwo_mul_degOne_le`, `two_mul_abs_sum_counterterm_le`).
* **The Riemann hypothesis on block-constant divisors**
  (`riemannHypothesis_of_frequently_blockFunction_combForm_ge`): if for every window ratio,
  every `η > 0` and every `R` there are arbitrarily large block sizes `B` at which every divisor
  constant on the blocks of the window above `N = RB` has `2 d₁ d₂ − D·D ≥ −η Σ c_n²`, the
  Riemann hypothesis holds.
-/

open Finset Filter

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

/-! ### Weighted inequalities -/

/-- The second weight of a pair `pq = 1` is positive. -/
theorem pos_of_mul_eq_one {p q : ℝ} (hp : 0 < p) (hpq : p * q = 1) : 0 < q := by
  by_contra h
  nlinarith [mul_nonneg hp.le (neg_nonneg.mpr (not_lt.mp h))]

/-- `2|ab| ≤ p a² + q b²` for `pq = 1`. -/
theorem two_mul_abs_mul_le {p q : ℝ} (hp : 0 < p) (hpq : p * q = 1) (a b : ℝ) :
    2 * |a * b| ≤ p * a ^ 2 + q * b ^ 2 := by
  have h1 : p * (p * a ^ 2 + q * b ^ 2) = (p * |a|) ^ 2 + |b| ^ 2 := by
    have h : p * (p * a ^ 2 + q * b ^ 2) = p ^ 2 * a ^ 2 + p * q * b ^ 2 := by ring
    rw [h, hpq, mul_pow, sq_abs, sq_abs, one_mul]
  have h2 : p * (2 * |a * b|) ≤ p * (p * a ^ 2 + q * b ^ 2) := by
    rw [h1, abs_mul]
    nlinarith [sq_nonneg (p * |a| - |b|)]
  exact le_of_mul_le_mul_left h2 hp

/-- `2|Σ a_n b_n| ≤ p Σ a_n² + q Σ b_n²` for `pq = 1`. -/
theorem two_mul_abs_sum_le (S : Finset ℕ) (a b : ℕ → ℝ) {p q : ℝ} (hp : 0 < p)
    (hpq : p * q = 1) :
    2 * |∑ n ∈ S, a n * b n| ≤ p * ∑ n ∈ S, a n ^ 2 + q * ∑ n ∈ S, b n ^ 2 := by
  calc 2 * |∑ n ∈ S, a n * b n| ≤ 2 * ∑ n ∈ S, |a n * b n| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ = ∑ n ∈ S, 2 * |a n * b n| := Finset.mul_sum _ _ _
    _ ≤ ∑ n ∈ S, (p * a n ^ 2 + q * b n ^ 2) :=
        Finset.sum_le_sum fun n _ => two_mul_abs_mul_le hp hpq _ _
    _ = p * ∑ n ∈ S, a n ^ 2 + q * ∑ n ∈ S, b n ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The same against a weight bounded by `δ`. -/
theorem two_mul_abs_sum_mul_le (S : Finset ℕ) (a b w : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : ∀ n ∈ S, |w n| ≤ δ) {p q : ℝ} (hp : 0 < p) (hpq : p * q = 1) :
    2 * |∑ n ∈ S, a n * b n * w n| ≤ δ * (p * ∑ n ∈ S, a n ^ 2 + q * ∑ n ∈ S, b n ^ 2) := by
  have hterm : ∀ n ∈ S, 2 * |a n * b n * w n| ≤ δ * (p * a n ^ 2 + q * b n ^ 2) := by
    intro n hn
    rw [abs_mul]
    calc 2 * (|a n * b n| * |w n|) ≤ 2 * (|a n * b n| * δ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hw n hn) (abs_nonneg _))
            (by norm_num)
      _ = δ * (2 * |a n * b n|) := by ring
      _ ≤ δ * (p * a n ^ 2 + q * b n ^ 2) :=
          mul_le_mul_of_nonneg_left (two_mul_abs_mul_le hp hpq _ _) hδ
  calc 2 * |∑ n ∈ S, a n * b n * w n| ≤ 2 * ∑ n ∈ S, |a n * b n * w n| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ = ∑ n ∈ S, 2 * |a n * b n * w n| := Finset.mul_sum _ _ _
    _ ≤ ∑ n ∈ S, δ * (p * a n ^ 2 + q * b n ^ 2) := Finset.sum_le_sum hterm
    _ = δ * (p * ∑ n ∈ S, a n ^ 2 + q * ∑ n ∈ S, b n ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The two orders of summation over pairs of distinct points. -/
theorem sum_erase_comm (S : Finset ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ S, ∑ m ∈ S.erase n, F m n = ∑ m ∈ S, ∑ n ∈ S.erase m, F m n :=
  Finset.sum_comm' fun n m => by
    simp only [Finset.mem_erase]
    exact ⟨fun ⟨hn, hne, hm⟩ => ⟨⟨hne.symm, hn⟩, hm⟩, fun ⟨⟨hne, hn⟩, hm⟩ => ⟨hn, hne.symm, hm⟩⟩

/-- **The Schur test for the pairing of two divisors.** A symmetric kernel with rows of absolute
values at most `ρ` pairs two divisors with `2|Σ a_m b_n E(m, n)| ≤ ρ (p Σ a² + q Σ b²)`,
`pq = 1`. -/
theorem two_mul_abs_sum_erase_le (S : Finset ℕ) (E : ℕ → ℕ → ℝ) (hE : ∀ m n, E m n = E n m)
    {ρ : ℝ} (hρ : ∀ n ∈ S, ∑ m ∈ S.erase n, |E m n| ≤ ρ) {p q : ℝ} (hp : 0 < p)
    (hpq : p * q = 1) (a b : ℕ → ℝ) :
    2 * |∑ n ∈ S, ∑ m ∈ S.erase n, a m * b n * E m n| ≤
      ρ * (p * ∑ n ∈ S, a n ^ 2 + q * ∑ n ∈ S, b n ^ 2) := by
  have hq := pos_of_mul_eq_one hp hpq
  have hterm : ∀ m n : ℕ, 2 * |a m * b n * E m n| ≤
      p * (a m ^ 2 * |E m n|) + q * (b n ^ 2 * |E m n|) := by
    intro m n
    rw [abs_mul]
    calc 2 * (|a m * b n| * |E m n|) = 2 * |a m * b n| * |E m n| := by ring
      _ ≤ (p * a m ^ 2 + q * b n ^ 2) * |E m n| :=
          mul_le_mul_of_nonneg_right (two_mul_abs_mul_le hp hpq _ _) (abs_nonneg _)
      _ = p * (a m ^ 2 * |E m n|) + q * (b n ^ 2 * |E m n|) := by ring
  have h1 : 2 * |∑ n ∈ S, ∑ m ∈ S.erase n, a m * b n * E m n| ≤
      p * ∑ n ∈ S, ∑ m ∈ S.erase n, a m ^ 2 * |E m n| +
        q * ∑ n ∈ S, ∑ m ∈ S.erase n, b n ^ 2 * |E m n| := by
    calc 2 * |∑ n ∈ S, ∑ m ∈ S.erase n, a m * b n * E m n|
        ≤ 2 * ∑ n ∈ S, ∑ m ∈ S.erase n, |a m * b n * E m n| :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun n _ => Finset.abs_sum_le_sum_abs _ _)) (by norm_num)
      _ = ∑ n ∈ S, ∑ m ∈ S.erase n, 2 * |a m * b n * E m n| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => Finset.mul_sum _ _ _
      _ ≤ ∑ n ∈ S, ∑ m ∈ S.erase n,
            (p * (a m ^ 2 * |E m n|) + q * (b n ^ 2 * |E m n|)) :=
          Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => hterm m n
      _ = p * ∑ n ∈ S, ∑ m ∈ S.erase n, a m ^ 2 * |E m n| +
            q * ∑ n ∈ S, ∑ m ∈ S.erase n, b n ^ 2 * |E m n| := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
  -- the rows of `a` after exchanging the two sums, the rows of `b` directly
  have hsw : ∑ n ∈ S, ∑ m ∈ S.erase n, a m ^ 2 * |E m n| =
      ∑ m ∈ S, ∑ n ∈ S.erase m, a m ^ 2 * |E m n| :=
    sum_erase_comm S fun m n => a m ^ 2 * |E m n|
  have hA : ∑ n ∈ S, ∑ m ∈ S.erase n, a m ^ 2 * |E m n| ≤ ρ * ∑ n ∈ S, a n ^ 2 := by
    rw [hsw, Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    rw [← Finset.mul_sum]
    have hrow : ∑ n ∈ S.erase m, |E m n| ≤ ρ :=
      (Finset.sum_congr rfl fun n _ => by rw [hE m n]).trans_le (hρ m hm)
    calc a m ^ 2 * ∑ n ∈ S.erase m, |E m n| ≤ a m ^ 2 * ρ :=
          mul_le_mul_of_nonneg_left hrow (sq_nonneg _)
      _ = ρ * a m ^ 2 := mul_comm _ _
  have hB : ∑ n ∈ S, ∑ m ∈ S.erase n, b n ^ 2 * |E m n| ≤ ρ * ∑ n ∈ S, b n ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [← Finset.mul_sum]
    calc b n ^ 2 * ∑ m ∈ S.erase n, |E m n| ≤ b n ^ 2 * ρ :=
          mul_le_mul_of_nonneg_left (hρ n hn) (sq_nonneg _)
      _ = ρ * b n ^ 2 := mul_comm _ _
  nlinarith [mul_le_mul_of_nonneg_left hA hp.le, mul_le_mul_of_nonneg_left hB hq.le]

theorem abs_sub_add_sub_le (P F R D : ℝ) : |P - (F + R - D)| ≤ |P| + |F| + |R| + |D| := by
  rw [abs_le]
  constructor <;>
    linarith [le_abs_self P, neg_abs_le P, le_abs_self F, neg_abs_le F, le_abs_self R,
      neg_abs_le R, le_abs_self D, neg_abs_le D]

/-- The weights `ε/C` and `C/ε` in the cross term. -/
theorem cross_weights {C : ℝ} (hC : C ≠ 0) (ε A Z : ℝ) :
    C * (ε / C * A + C / ε * Z) = ε * A + C ^ 2 / ε * Z := by
  have h2 : C * (ε / C) = ε := by field_simp
  calc C * (ε / C * A + C / ε * Z) = C * (ε / C) * A + C * (C / ε) * Z := by ring
    _ = ε * A + C ^ 2 / ε * Z := by rw [h2]; ring

/-! ### Blocks and positions -/

/-- **A function of the blocks is orthogonal to a divisor with vanishing block sums.** -/
theorem sum_blockFunction_mul_eq_zero (N B : ℕ) (S : Finset ℕ) (u z : ℕ → ℝ)
    (hzero : ∀ j : ℕ, ∑ n ∈ S.filter (fun n => blockIndex N B n = j), z n = 0) :
    ∑ n ∈ S, u (blockIndex N B n) * z n = 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun n hn => Finset.mem_image_of_mem (blockIndex N B) hn)
    (fun n => u (blockIndex N B n) * z n)]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hconst : ∀ n ∈ S.filter (fun n => blockIndex N B n = j),
      u (blockIndex N B n) * z n = u j * z n := fun n hn => by
    rw [(Finset.mem_filter.mp hn).2]
  rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum, hzero j, mul_zero]

/-- The block kernel pairs a divisor with vanishing block sums to zero with every divisor. -/
theorem sum_mul_blockKernel_eq_zero (N B : ℕ) (S : Finset ℕ) (s z : ℕ → ℝ)
    (hzero : ∀ j : ℕ, ∑ n ∈ S.filter (fun n => blockIndex N B n = j), z n = 0) :
    ∑ n ∈ S, ∑ m ∈ S.erase n, s m * z n * blockKernel N B m n = 0 := by
  have hinner : ∀ n ∈ S, ∑ m ∈ S.erase n, s m * z n * blockKernel N B m n =
      (∑ m ∈ S, s m * blockWeight B (blockIndex N B m) (blockIndex N B n)) * z n := by
    intro n hn
    rw [Finset.sum_mul, ← Finset.add_sum_erase S _ hn, blockWeight_self, mul_zero, zero_mul,
      zero_add]
    exact Finset.sum_congr rfl fun m _ => by rw [blockKernel]; ring
  rw [Finset.sum_congr rfl hinner]
  exact sum_blockFunction_mul_eq_zero N B S
    (fun j => ∑ m ∈ S, s m * blockWeight B (blockIndex N B m) j) z hzero

/-- A degree point of the window lies in its block. -/
theorem blockIndex_bounds {N B n : ℕ} (hB : 0 < B) (hn : N < n) :
    N + B * blockIndex N B n < n ∧ n ≤ N + B * blockIndex N B n + B := by
  have e := Nat.div_add_mod (n - N - 1) B
  have r := Nat.mod_lt (n - N - 1) hB
  unfold blockIndex
  omega

/-- The position of a degree point in its block. -/
def blockPos (N B n : ℕ) : ℕ := (n - N - 1) % B

theorem blockIndex_add {B : ℕ} (hB : 0 < B) (N j : ℕ) {a : ℕ} (ha : a < B) :
    blockIndex N B (N + 1 + B * j + a) = j := by
  have h : N + 1 + B * j + a - N - 1 = a + B * j := by omega
  rw [blockIndex, h, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt ha, zero_add]

theorem blockPos_add (N B j : ℕ) {a : ℕ} (ha : a < B) :
    blockPos N B (N + 1 + B * j + a) = a := by
  have h : N + 1 + B * j + a - N - 1 = a + B * j := by omega
  rw [blockPos, h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem eq_add_blockPos {N B n : ℕ} (hn : N < n) :
    n = N + 1 + B * blockIndex N B n + blockPos N B n := by
  have e := Nat.div_add_mod (n - N - 1) B
  unfold blockIndex blockPos
  omega

/-- **A window of complete blocks, by blocks and positions.** -/
theorem sum_Ioc_blocks (G : ℕ → ℝ) (N B J : ℕ) :
    ∑ n ∈ Ioc N (N + B * J), G n = ∑ j ∈ range J, ∑ a ∈ range B, G (N + 1 + B * j + a) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have e : N + B * (J + 1) = N + B * J + B := by ring
    rw [e, ← Finset.sum_Ioc_consecutive G (Nat.le_add_right N (B * J)) (Nat.le_add_right _ B),
      ih, sum_Ioc_add_eq_sum_range, Finset.sum_range_succ]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by congr 1; omega

/-- The sum of a divisor over one block of a window of complete blocks. -/
theorem sum_filter_blockIndex {B : ℕ} (hB : 0 < B) (N J : ℕ) (c : ℕ → ℝ) (j : ℕ) :
    ∑ n ∈ (Ioc N (N + B * J)).filter (fun n => blockIndex N B n = j), c n =
      if j < J then ∑ a ∈ range B, c (N + 1 + B * j + a) else 0 := by
  rw [Finset.sum_filter, sum_Ioc_blocks]
  have h : ∀ i ∈ range J, ∑ a ∈ range B,
      (if blockIndex N B (N + 1 + B * i + a) = j then c (N + 1 + B * i + a) else 0) =
      if i = j then ∑ a ∈ range B, c (N + 1 + B * i + a) else 0 := by
    intro i _
    split_ifs with hij
    · exact Finset.sum_congr rfl fun a ha => by
        rw [blockIndex_add hB N i (Finset.mem_range.mp ha), if_pos hij]
    · exact Finset.sum_eq_zero fun a ha => by
        rw [blockIndex_add hB N i (Finset.mem_range.mp ha), if_neg hij]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (range J) j]
  simp only [Finset.mem_range]

/-! ### The pole and the counterterm inside a block -/

theorem abs_one_div_sub_one_div_le {N x y b : ℝ} (hN : 0 < N) (hy : N ≤ y) (hxy : y ≤ x)
    (hb : x ≤ y + b) : |1 / x - 1 / y| ≤ b / N ^ 2 := by
  have hy0 : 0 < y := lt_of_lt_of_le hN hy
  have hx0 : 0 < x := lt_of_lt_of_le hy0 hxy
  have hb0 : 0 ≤ b := by linarith
  rw [div_sub_div _ _ hx0.ne' hy0.ne', abs_div, abs_of_pos (mul_pos hx0 hy0),
    div_le_div_iff₀ (mul_pos hx0 hy0) (by positivity)]
  have h1 : |1 * y - x * 1| ≤ b := by
    rw [abs_le]
    constructor <;> linarith
  have h2 : N ^ 2 ≤ x * y := by nlinarith
  calc |1 * y - x * 1| * N ^ 2 ≤ b * N ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ b * (x * y) := mul_le_mul_of_nonneg_left h2 hb0

/-- **The pole plane.** For `z` with vanishing block sums, `d₂(z) = 0` and `d₁(z)` sees only the
variation `B/N²` of `1/n` inside a block. -/
theorem two_mul_abs_degTwo_mul_degOne_le {N M B : ℕ} (hN : 0 < N) (hB : 0 < B) {S : Finset ℕ}
    (hS : S ⊆ Ioc N (N + M)) (s z : ℕ → ℝ)
    (hzero : ∀ j : ℕ, ∑ n ∈ S.filter (fun n => blockIndex N B n = j), z n = 0)
    {p q : ℝ} (hp : 0 < p) (hpq : p * q = 1) :
    2 * |degTwo S s * degOne S z| ≤
      (B : ℝ) * M / (N : ℝ) ^ 2 * (p * ∑ n ∈ S, s n ^ 2 + q * ∑ n ∈ S, z n ^ 2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hq := pos_of_mul_eq_one hp hpq
  have hY : 0 ≤ p * ∑ n ∈ S, s n ^ 2 + q * ∑ n ∈ S, z n ^ 2 :=
    add_nonneg (mul_nonneg hp.le (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (mul_nonneg hq.le (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hcard : (S.card : ℝ) ≤ M := by
    have h2 : S.card ≤ (Ioc N (N + M)).card := Finset.card_le_card hS
    rw [Nat.card_Ioc] at h2
    exact_mod_cast (by omega : S.card ≤ M)
  -- the first degree against the foot of each block
  have h0 : ∑ n ∈ S, 1 / ((N : ℝ) + B * ((blockIndex N B n : ℕ) : ℝ)) * z n = 0 :=
    sum_blockFunction_mul_eq_zero N B S (fun j => 1 / ((N : ℝ) + B * (j : ℝ))) z hzero
  have hrep : degOne S z =
      ∑ n ∈ S, (1 / (n : ℝ) - 1 / ((N : ℝ) + B * ((blockIndex N B n : ℕ) : ℝ))) * z n := by
    have h : ∑ n ∈ S, (1 / (n : ℝ) - 1 / ((N : ℝ) + B * ((blockIndex N B n : ℕ) : ℝ))) * z n =
        ∑ n ∈ S, z n / n - ∑ n ∈ S, 1 / ((N : ℝ) + B * ((blockIndex N B n : ℕ) : ℝ)) * z n := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [h, h0, sub_zero, degOne]
  have hw : ∀ n ∈ S, |1 / (n : ℝ) - 1 / ((N : ℝ) + B * ((blockIndex N B n : ℕ) : ℝ))| ≤
      (B : ℝ) / (N : ℝ) ^ 2 := by
    intro n hn
    obtain ⟨hn1, -⟩ := Finset.mem_Ioc.mp (hS hn)
    obtain ⟨h1, h2⟩ := blockIndex_bounds hB hn1
    have h1' : (N : ℝ) + B * ((blockIndex N B n : ℕ) : ℝ) ≤ n := by exact_mod_cast h1.le
    have h2' : (n : ℝ) ≤ (N : ℝ) + B * ((blockIndex N B n : ℕ) : ℝ) + B := by exact_mod_cast h2
    exact abs_one_div_sub_one_div_le hN' (le_add_of_nonneg_right (by positivity)) h1' h2'
  have hd1 : |degOne S z| ≤ (B : ℝ) / (N : ℝ) ^ 2 * ∑ n ∈ S, |z n| := by
    rw [hrep, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hw n hn) (abs_nonneg _)
  have hd2 : |degTwo S s| ≤ ∑ m ∈ S, |s m| := Finset.abs_sum_le_sum_abs _ _
  -- the product of the two sums
  have hprod : 2 * ((∑ m ∈ S, |s m|) * ∑ n ∈ S, |z n|) ≤
      S.card * (p * ∑ n ∈ S, s n ^ 2 + q * ∑ n ∈ S, z n ^ 2) := by
    have h1 : ∀ m ∈ S, ∑ n ∈ S, (p * s m ^ 2 + q * z n ^ 2) =
        S.card * (p * s m ^ 2) + q * ∑ n ∈ S, z n ^ 2 := fun m _ => by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    calc ∑ m ∈ S, 2 * ∑ n ∈ S, |s m| * |z n|
        ≤ ∑ m ∈ S, ∑ n ∈ S, (p * s m ^ 2 + q * z n ^ 2) := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun n _ => ?_
          rw [← abs_mul]
          exact two_mul_abs_mul_le hp hpq _ _
      _ = S.card * (p * ∑ n ∈ S, s n ^ 2 + q * ∑ n ∈ S, z n ^ 2) := by
          rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
  calc 2 * |degTwo S s * degOne S z| = 2 * (|degTwo S s| * |degOne S z|) := by rw [abs_mul]
    _ ≤ 2 * ((∑ m ∈ S, |s m|) * ((B : ℝ) / (N : ℝ) ^ 2 * ∑ n ∈ S, |z n|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hd2 hd1 (abs_nonneg _)
          (Finset.sum_nonneg fun _ _ => abs_nonneg _)) (by norm_num)
    _ = (B : ℝ) / (N : ℝ) ^ 2 * (2 * ((∑ m ∈ S, |s m|) * ∑ n ∈ S, |z n|)) := by ring
    _ ≤ (B : ℝ) / (N : ℝ) ^ 2 *
          (S.card * (p * ∑ n ∈ S, s n ^ 2 + q * ∑ n ∈ S, z n ^ 2)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ (B : ℝ) / (N : ℝ) ^ 2 * (M * (p * ∑ n ∈ S, s n ^ 2 + q * ∑ n ∈ S, z n ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hY) (by positivity)
    _ = (B : ℝ) * M / (N : ℝ) ^ 2 * (p * ∑ n ∈ S, s n ^ 2 + q * ∑ n ∈ S, z n ^ 2) := by ring

/-- **The counterterm.** Against a divisor constant on blocks and a divisor with vanishing block
sums the counterterm `log(n/2π)` acts through its variation inside a block, at most `B/N`. -/
theorem two_mul_abs_sum_counterterm_le {N M B : ℕ} (hN : 0 < N) (hB : 0 < B) {S : Finset ℕ}
    (hS : S ⊆ Ioc N (N + M)) (σ z : ℕ → ℝ)
    (hzero : ∀ j : ℕ, ∑ n ∈ S.filter (fun n => blockIndex N B n = j), z n = 0)
    {p q : ℝ} (hp : 0 < p) (hpq : p * q = 1) :
    2 * |∑ n ∈ S, σ (blockIndex N B n) * z n * counterterm n| ≤
      (B : ℝ) / N * (p * ∑ n ∈ S, σ (blockIndex N B n) ^ 2 + q * ∑ n ∈ S, z n ^ 2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  -- the counterterm at the foot of each block is constant on the block
  have h0 : ∑ n ∈ S, σ (blockIndex N B n) *
      Real.log (((N : ℝ) + B * ((blockIndex N B n : ℕ) : ℝ)) / (2 * Real.pi)) * z n = 0 :=
    sum_blockFunction_mul_eq_zero N B S
      (fun j => σ j * Real.log (((N : ℝ) + B * (j : ℝ)) / (2 * Real.pi))) z hzero
  have hrep : ∑ n ∈ S, σ (blockIndex N B n) * z n * counterterm n =
      ∑ n ∈ S, σ (blockIndex N B n) * z n * (counterterm n -
        Real.log (((N : ℝ) + B * ((blockIndex N B n : ℕ) : ℝ)) / (2 * Real.pi))) := by
    have h : ∑ n ∈ S, σ (blockIndex N B n) * z n * (counterterm n -
          Real.log (((N : ℝ) + B * ((blockIndex N B n : ℕ) : ℝ)) / (2 * Real.pi))) =
        ∑ n ∈ S, σ (blockIndex N B n) * z n * counterterm n -
          ∑ n ∈ S, σ (blockIndex N B n) *
            Real.log (((N : ℝ) + B * ((blockIndex N B n : ℕ) : ℝ)) / (2 * Real.pi)) * z n := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [h, h0, sub_zero]
  have hδ : ∀ n ∈ S, |counterterm n -
      Real.log (((N : ℝ) + B * ((blockIndex N B n : ℕ) : ℝ)) / (2 * Real.pi))| ≤
        (B : ℝ) / N := by
    intro n hn
    obtain ⟨hn1, -⟩ := Finset.mem_Ioc.mp (hS hn)
    obtain ⟨h1, h2⟩ := blockIndex_bounds hB hn1
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (N : ℝ) + B * ((blockIndex N B n : ℕ) : ℝ) := ⟨_, rfl⟩
    have hNy : (N : ℝ) ≤ y := by
      rw [hy]
      exact le_add_of_nonneg_right (by positivity)
    have hy0 : 0 < y := lt_of_lt_of_le hN' hNy
    have h1' : y ≤ n := by
      rw [hy]
      exact_mod_cast h1.le
    have h2' : (n : ℝ) ≤ y + B := by
      rw [hy]
      exact_mod_cast h2
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hy0 h1'
    have e : counterterm n - Real.log (y / (2 * Real.pi)) = Real.log ((n : ℝ) / y) := by
      rw [counterterm, Real.log_div hn0.ne' hπ.ne', Real.log_div hy0.ne' hπ.ne',
        Real.log_div hn0.ne' hy0.ne']
      ring
    have hlow : 0 ≤ Real.log ((n : ℝ) / y) := Real.log_nonneg ((one_le_div hy0).mpr h1')
    have hup : Real.log ((n : ℝ) / y) ≤ (B : ℝ) / N := by
      refine (Real.log_le_sub_one_of_pos (div_pos hn0 hy0)).trans ?_
      rw [div_sub_one hy0.ne', div_le_div_iff₀ hy0 hN']
      nlinarith [mul_le_mul_of_nonneg_left hNy (sub_nonneg.mpr h1'),
        mul_le_mul_of_nonneg_right (sub_le_iff_le_add'.mpr h2') hy0.le]
    rw [← hy, e, abs_of_nonneg hlow]
    exact hup
  rw [hrep]
  exact two_mul_abs_sum_mul_le S (fun n => σ (blockIndex N B n)) z _ (by positivity) hδ hp hpq

/-! ### The kernel between distant points -/

/-- The singular part of the jets between points at most `B` apart. -/
def nearKernel (B m n : ℕ) : ℝ := if Nat.dist m n ≤ B then 1 / (2 * (Nat.dist m n : ℝ)) else 0

theorem nearKernel_comm (B m n : ℕ) : nearKernel B m n = nearKernel B n m := by
  unfold nearKernel
  rw [Nat.dist_comm]

/-- The pairing minus the block kernel and the near kernel. -/
def farKernel (N B m n : ℕ) : ℝ := pairKernel m n - (blockKernel N B m n + nearKernel B m n)

theorem farKernel_comm (N B m n : ℕ) : farKernel N B m n = farKernel N B n m := by
  rw [farKernel, farKernel, pairKernel_comm, blockKernel_comm, nearKernel_comm]

/-- The majorant, at the distance `d`, of the singular part of the jets minus the block kernel and
the near kernel. -/
def farMajorant (B d : ℕ) : ℝ :=
  (if B < d ∧ d < 2 * B then 1 / (2 * (d : ℝ)) else 0) +
    (if B < d then (B : ℝ) / (d : ℝ) ^ 2 else 0)

theorem farMajorant_nonneg (B d : ℕ) : 0 ≤ farMajorant B d := by
  unfold farMajorant
  refine add_nonneg ?_ ?_ <;> split_ifs <;> positivity

/-- The majorant summed over the distances: at most `3/2`, for every block size. -/
theorem sum_farMajorant_le {B : ℕ} (hB : 0 < B) (D : ℕ) :
    ∑ d ∈ Icc 1 D, farMajorant B d ≤ 3 / 2 := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have h1 : ∑ d ∈ Icc 1 D, (if B < d ∧ d < 2 * B then 1 / (2 * (d : ℝ)) else 0) ≤ 1 / 2 := by
    rw [← Finset.sum_filter]
    have hsub : (Icc 1 D).filter (fun d => B < d ∧ d < 2 * B) ⊆ Ioc B (2 * B) := fun d hd => by
      obtain ⟨-, hd1, hd2⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_Ioc.mpr ⟨hd1, hd2.le⟩
    have hcard : (((Icc 1 D).filter (fun d => B < d ∧ d < 2 * B)).card : ℝ) ≤ B := by
      have h := Finset.card_le_card hsub
      rw [Nat.card_Ioc] at h
      exact_mod_cast h.trans (by omega)
    calc ∑ d ∈ (Icc 1 D).filter (fun d => B < d ∧ d < 2 * B), 1 / (2 * (d : ℝ))
        ≤ ∑ _d ∈ (Icc 1 D).filter (fun d => B < d ∧ d < 2 * B), 1 / (2 * (B : ℝ)) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hBd : (B : ℝ) ≤ d := by exact_mod_cast (Finset.mem_filter.mp hd).2.1.le
          exact one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = ((Icc 1 D).filter (fun d => B < d ∧ d < 2 * B)).card * (1 / (2 * (B : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ B * (1 / (2 * (B : ℝ))) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 1 / 2 := by field_simp
  unfold farMajorant
  rw [Finset.sum_add_distrib]
  linarith [sum_ite_lt_div_sq_le hB D]

/-- Off the block kernel and the near kernel the singular part of the jets is at most the
majorant of the distance. -/
theorem abs_inv_sub_far_le {N B m n : ℕ} (hB : 0 < B) (hm : N < m) (hn : N < n) (hmn : m ≠ n) :
    |1 / (2 * |(m : ℝ) - n|) - (blockKernel N B m n + nearKernel B m n)| ≤
      farMajorant B (Nat.dist m n) := by
  have hd0 : 0 < Nat.dist m n := Nat.dist_pos_of_ne hmn
  have hd0' : (0 : ℝ) < ((Nat.dist m n : ℕ) : ℝ) := by exact_mod_cast hd0
  by_cases hfar : blockIndex N B m + 2 ≤ blockIndex N B n ∨
      blockIndex N B n + 2 ≤ blockIndex N B m
  · obtain ⟨h1, h2⟩ := abs_inv_sub_blockKernel_le hB hm hn hfar
    have hBd : B < Nat.dist m n := by
      have : (B : ℝ) < (Nat.dist m n : ℕ) := by rwa [cast_dist]
      exact_mod_cast this
    have hnear : nearKernel B m n = 0 := by rw [nearKernel, if_neg (by omega)]
    have hsq : ((m : ℝ) - n) ^ 2 = ((Nat.dist m n : ℕ) : ℝ) ^ 2 := by rw [cast_dist, sq_abs]
    rw [hnear, add_zero]
    unfold farMajorant
    rw [if_pos hBd, ← hsq]
    have : (0 : ℝ) ≤ if B < Nat.dist m n ∧ Nat.dist m n < 2 * B then
        1 / (2 * ((Nat.dist m n : ℕ) : ℝ)) else 0 := by
      split_ifs <;> positivity
    linarith
  · have hw : blockKernel N B m n = 0 := by rw [blockKernel, blockWeight, if_neg hfar]
    have hlt := dist_lt_two_mul_of_near hB hm hn hfar
    rw [hw, zero_add, ← cast_dist]
    by_cases hd : Nat.dist m n ≤ B
    · rw [nearKernel, if_pos hd, sub_self, abs_zero]
      exact farMajorant_nonneg _ _
    · rw [nearKernel, if_neg hd, sub_zero, abs_of_pos (by positivity)]
      unfold farMajorant
      rw [if_pos ⟨by omega, hlt⟩]
      have : (0 : ℝ) ≤ if B < Nat.dist m n then (B : ℝ) / ((Nat.dist m n : ℕ) : ℝ) ^ 2 else 0 := by
        split_ifs <;> positivity
      linarith

/-- **The row of the far kernel** is at most `3 + M/(4N) + 2ψ(Q)`, for every block size. -/
theorem sum_abs_farKernel_le {N M B Q : ℕ} (hN : 0 < N) (hB : 0 < B) (hQ : N + M ≤ Q * N)
    {S : Finset ℕ} (hS : S ⊆ Ioc N (N + M)) {n : ℕ} (hn : n ∈ S) :
    ∑ m ∈ S.erase n, |farKernel N B m n| ≤ 3 + (M : ℝ) / (4 * N) + 2 * chebyshev Q := by
  have hn1 := (Finset.mem_Ioc.mp (hS hn)).1
  have h := sum_abs_pairKernel_sub_le hN hQ hS hn
    (fun m n => blockKernel N B m n + nearKernel B m n) (farMajorant B) (farMajorant_nonneg B)
    (sum_farMajorant_le hB M) fun m hm hmn => abs_inv_sub_far_le hB hm hn1 hmn
  exact h.trans (by linarith)

/-! ### The potential of a block-constant divisor in the near kernel -/

theorem sum_erase_eq_below_add_above (S : Finset ℕ) (n : ℕ) (F : ℕ → ℝ) :
    ∑ m ∈ S.erase n, F m = ∑ m ∈ S.filter (· < n), F m + ∑ m ∈ S.filter (n < ·), F m := by
  rw [← Finset.sum_filter_add_sum_filter_not (S.erase n) (· < n)]
  congr 1
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext m
    simp only [Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun ⟨⟨_, hm⟩, hlt⟩ => ⟨hm, hlt⟩, fun ⟨hm, hlt⟩ => ⟨⟨hlt.ne, hm⟩, hlt⟩⟩
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext m
    simp only [Finset.mem_filter, Finset.mem_erase, not_lt]
    exact ⟨fun ⟨⟨hne, hm⟩, hle⟩ => ⟨hm, lt_of_le_of_ne hle (Ne.symm hne)⟩,
      fun ⟨hm, hlt⟩ => ⟨⟨hlt.ne', hm⟩, hlt.le⟩⟩

/-- The near kernel summed over the points below `n`, by the distance. -/
theorem sum_nearKernel_below (S : Finset ℕ) (g : ℕ → ℝ) {B n : ℕ} (hBn : B < n) :
    ∑ m ∈ S.filter (· < n), g m * nearKernel B m n =
      ∑ d ∈ Icc 1 B, (if n - d ∈ S then g (n - d) else 0) / (2 * (d : ℝ)) := by
  have hL : ∀ m ∈ S.filter (· < n), g m * nearKernel B m n =
      if n - m ≤ B then g m / (2 * ((n - m : ℕ) : ℝ)) else 0 := by
    intro m hm
    have hmn : m < n := (Finset.mem_filter.mp hm).2
    rw [nearKernel, Nat.dist_eq_sub_of_le hmn.le]
    split_ifs <;> ring
  have hR : ∀ d ∈ Icc 1 B, (if n - d ∈ S then g (n - d) else 0) / (2 * (d : ℝ)) =
      if n - d ∈ S then g (n - d) / (2 * (d : ℝ)) else 0 := fun d _ => by
    rw [ite_div, zero_div]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun m => n - m) (fun d => n - d) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmS, hmn⟩ := Finset.mem_filter.mp hm1
    have e : n - (n - m) = m := by omega
    show n - m ∈ (Icc 1 B).filter (fun d => n - d ∈ S)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hm2⟩, ?_⟩
    show n - (n - m) ∈ S
    rw [e]
    exact hmS
  · intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd3, hd4⟩ := Finset.mem_Icc.mp hd1
    show n - d ∈ (S.filter (· < n)).filter (fun m => n - m ≤ B)
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hd2, by omega⟩, ?_⟩
    show n - (n - d) ≤ B
    omega
  · intro m hm
    have hmn : m < n := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
    show n - (n - m) = m
    omega
  · intro d hd
    have hd4 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
    show n - (n - d) = d
    omega
  · intro m hm
    have hmn : m < n := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
    have e : n - (n - m) = m := by omega
    show g m / (2 * ((n - m : ℕ) : ℝ)) = g (n - (n - m)) / (2 * ((n - m : ℕ) : ℝ))
    rw [e]

/-- The near kernel summed over the points above `n`, by the distance. -/
theorem sum_nearKernel_above (S : Finset ℕ) (g : ℕ → ℝ) (B n : ℕ) :
    ∑ m ∈ S.filter (n < ·), g m * nearKernel B m n =
      ∑ d ∈ Icc 1 B, (if n + d ∈ S then g (n + d) else 0) / (2 * (d : ℝ)) := by
  have hL : ∀ m ∈ S.filter (n < ·), g m * nearKernel B m n =
      if m - n ≤ B then g m / (2 * ((m - n : ℕ) : ℝ)) else 0 := by
    intro m hm
    have hmn : n < m := (Finset.mem_filter.mp hm).2
    rw [nearKernel, Nat.dist_eq_sub_of_le_right hmn.le]
    split_ifs <;> ring
  have hR : ∀ d ∈ Icc 1 B, (if n + d ∈ S then g (n + d) else 0) / (2 * (d : ℝ)) =
      if n + d ∈ S then g (n + d) / (2 * (d : ℝ)) else 0 := fun d _ => by
    rw [ite_div, zero_div]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun m => m - n) (fun d => n + d) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmS, hmn⟩ := Finset.mem_filter.mp hm1
    have e : n + (m - n) = m := by omega
    show m - n ∈ (Icc 1 B).filter (fun d => n + d ∈ S)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hm2⟩, ?_⟩
    show n + (m - n) ∈ S
    rw [e]
    exact hmS
  · intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd3, hd4⟩ := Finset.mem_Icc.mp hd1
    show n + d ∈ (S.filter (n < ·)).filter (fun m => m - n ≤ B)
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hd2, by omega⟩, ?_⟩
    show n + d - n ≤ B
    omega
  · intro m hm
    have hmn : n < m := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
    show n + (m - n) = m
    omega
  · intro d _
    show n + d - n = d
    omega
  · intro m hm
    have hmn : n < m := (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).2
    have e : n + (m - n) = m := by omega
    show g m / (2 * ((m - n : ℕ) : ℝ)) = g (n + (m - n)) / (2 * ((m - n : ℕ) : ℝ))
    rw [e]

/-- A weight with one step, summed against `1/(2d)`. -/
theorem sum_ite_le_div {B a : ℕ} (ha : a ≤ B) (x y : ℝ) :
    ∑ d ∈ Icc 1 B, (if d ≤ a then x else y) / (2 * (d : ℝ)) =
      (x * harm a + y * (harm B - harm a)) / 2 := by
  induction B, ha using Nat.le_induction with
  | base =>
    have h : ∀ d ∈ Icc 1 a, (if d ≤ a then x else y) / (2 * (d : ℝ)) = x / 2 * (1 / (d : ℝ)) :=
      fun d hd => by
        rw [if_pos (Finset.mem_Icc.mp hd).2]
        ring
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum, sum_Icc_one_div]
    ring
  | succ B hB ih =>
    have hterm : y / (2 * ((B : ℝ) + 1)) = y / 2 * (1 / ((B : ℝ) + 1)) := by
      rw [div_mul_eq_div_div]
      ring
    rw [Finset.sum_Icc_succ_top (by omega), ih, if_neg (by omega), harm_succ]
    push_cast
    rw [hterm]
    ring

/-- The value of a block-constant divisor one block below, `0` below the window. -/
def lowerValue (σ : ℕ → ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else σ (j - 1)

/-- The value one block above, `0` above a window of `J` blocks. -/
def upperValue (σ : ℕ → ℝ) (J j : ℕ) : ℝ := if j + 1 < J then σ (j + 1) else 0

/-- The potential of a block-constant divisor in the near kernel at the position `a` of the block
`j`, minus `σ_j H_B`: the jumps to the two adjacent blocks with the weights `H_B − H_a` and
`H_B − H_{B−1−a}`. -/
def nearRemainder (σ : ℕ → ℝ) (B J j a : ℕ) : ℝ :=
  ((lowerValue σ j - σ j) * (harm B - harm a) +
    (upperValue σ J j - σ j) * (harm B - harm (B - 1 - a))) / 2

/-- **The potential of a block-constant divisor in the near kernel.** At the position `a` of the
block `j` of a window of `J` complete blocks it is `σ_j H_B` plus the remainder of the jumps. -/
theorem sum_blockFunction_mul_nearKernel {N B J : ℕ} (hB : 0 < B) (hBN : B ≤ N) (σ : ℕ → ℝ)
    {j a n : ℕ} (hj : j < J) (ha : a < B) (hn : n = N + 1 + B * j + a) :
    ∑ m ∈ (Ioc N (N + B * J)).erase n, σ (blockIndex N B m) * nearKernel B m n =
      σ j * harm B + nearRemainder σ B J j a := by
  have hBj : B * j + B ≤ B * J := by
    calc B * j + B = B * (j + 1) := by ring
      _ ≤ B * J := Nat.mul_le_mul_left B hj
  -- the points below `n`: the block `j` up to the distance `a`, then the block `j − 1`
  have hlow : ∀ d ∈ Icc 1 B,
      (if n - d ∈ Ioc N (N + B * J) then σ (blockIndex N B (n - d)) else 0) =
        if d ≤ a then σ j else lowerValue σ j := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hd
    by_cases hda : d ≤ a
    · have hmem : n - d ∈ Ioc N (N + B * J) := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
      have e : n - d = N + 1 + B * j + (a - d) := by omega
      rw [if_pos hmem, if_pos hda, e, blockIndex_add hB N j (by omega)]
    · rw [if_neg hda, lowerValue]
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · have hmul : B * j = 0 := by rw [hj0, Nat.mul_zero]
        have hmem : n - d ∉ Ioc N (N + B * J) := fun h => by
          have := (Finset.mem_Ioc.mp h).1
          omega
        rw [if_neg hmem, if_pos hj0]
      · obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have hmul : B * j = B * i + B := by rw [hi]; ring
        have hmem : n - d ∈ Ioc N (N + B * J) := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        have e : n - d = N + 1 + B * i + (B + a - d) := by omega
        have hji : j - 1 = i := by omega
        rw [if_pos hmem, if_neg (by omega), e, blockIndex_add hB N i (by omega), hji]
  -- the points above `n`: the block `j` up to the distance `B − 1 − a`, then the block `j + 1`
  have hup : ∀ d ∈ Icc 1 B,
      (if n + d ∈ Ioc N (N + B * J) then σ (blockIndex N B (n + d)) else 0) =
        if d ≤ B - 1 - a then σ j else upperValue σ J j := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hd
    by_cases hdb : d ≤ B - 1 - a
    · have hmem : n + d ∈ Ioc N (N + B * J) := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
      have e : n + d = N + 1 + B * j + (a + d) := by omega
      rw [if_pos hmem, if_pos hdb, e, blockIndex_add hB N j (by omega)]
    · rw [if_neg hdb, upperValue]
      by_cases hjJ : j + 1 < J
      · have hmul : B * (j + 1) = B * j + B := by ring
        have hBj2 : B * (j + 1) + B ≤ B * J := by
          calc B * (j + 1) + B = B * (j + 2) := by ring
            _ ≤ B * J := Nat.mul_le_mul_left B (by omega)
        have hmem : n + d ∈ Ioc N (N + B * J) := Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        have e : n + d = N + 1 + B * (j + 1) + (a + d - B) := by omega
        rw [if_pos hmem, if_pos hjJ, e, blockIndex_add hB N (j + 1) (by omega)]
      · have hJ : J = j + 1 := by omega
        have hmul : B * J = B * j + B := by rw [hJ]; ring
        have hmem : n + d ∉ Ioc N (N + B * J) := fun h => by
          have := (Finset.mem_Ioc.mp h).2
          omega
        rw [if_neg hmem, if_neg hjJ]
  have hbelow : ∑ m ∈ (Ioc N (N + B * J)).filter (· < n),
        σ (blockIndex N B m) * nearKernel B m n =
      ∑ d ∈ Icc 1 B, (if n - d ∈ Ioc N (N + B * J) then σ (blockIndex N B (n - d)) else 0) /
        (2 * (d : ℝ)) :=
    sum_nearKernel_below (Ioc N (N + B * J)) (fun m => σ (blockIndex N B m)) (by omega)
  have habove : ∑ m ∈ (Ioc N (N + B * J)).filter (n < ·),
        σ (blockIndex N B m) * nearKernel B m n =
      ∑ d ∈ Icc 1 B, (if n + d ∈ Ioc N (N + B * J) then σ (blockIndex N B (n + d)) else 0) /
        (2 * (d : ℝ)) :=
    sum_nearKernel_above (Ioc N (N + B * J)) (fun m => σ (blockIndex N B m)) B n
  have e1 : ∑ d ∈ Icc 1 B,
      (if n - d ∈ Ioc N (N + B * J) then σ (blockIndex N B (n - d)) else 0) / (2 * (d : ℝ)) =
        (σ j * harm a + lowerValue σ j * (harm B - harm a)) / 2 := by
    rw [← sum_ite_le_div ha.le]
    exact Finset.sum_congr rfl fun d hd => by rw [hlow d hd]
  have e2 : ∑ d ∈ Icc 1 B,
      (if n + d ∈ Ioc N (N + B * J) then σ (blockIndex N B (n + d)) else 0) / (2 * (d : ℝ)) =
        (σ j * harm (B - 1 - a) + upperValue σ J j * (harm B - harm (B - 1 - a))) / 2 := by
    rw [← sum_ite_le_div (by omega : B - 1 - a ≤ B)]
    exact Finset.sum_congr rfl fun d hd => by rw [hup d hd]
  rw [sum_erase_eq_below_add_above, hbelow, habove, e1, e2, nearRemainder]
  ring

theorem sum_blockFunction_mul_nearKernel_of_mem {N B J : ℕ} (hB : 0 < B) (hBN : B ≤ N)
    (σ : ℕ → ℝ) {n : ℕ} (hn : n ∈ Ioc N (N + B * J)) :
    ∑ m ∈ (Ioc N (N + B * J)).erase n, σ (blockIndex N B m) * nearKernel B m n =
      σ (blockIndex N B n) * harm B +
        nearRemainder σ B J (blockIndex N B n) (blockPos N B n) := by
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
  have e := eq_add_blockPos (B := B) hn1
  have ha : blockPos N B n < B := Nat.mod_lt _ hB
  have hj : blockIndex N B n < J := by
    have h : B * blockIndex N B n < B * J := by omega
    exact lt_of_mul_lt_mul_left h (Nat.zero_le B)
  exact sum_blockFunction_mul_nearKernel hB hBN σ hj ha e

/-! ### The norm of the remainder -/

theorem sq_half_add_le (x y t u : ℝ) :
    ((x * t + y * u) / 2) ^ 2 ≤ x ^ 2 / 2 * t ^ 2 + y ^ 2 / 2 * u ^ 2 := by
  nlinarith [sq_nonneg (x * t - y * u)]

theorem sum_lowerValue_sq_le (σ : ℕ → ℝ) (J : ℕ) :
    ∑ j ∈ range J, lowerValue σ j ^ 2 ≤ ∑ j ∈ range J, σ j ^ 2 := by
  cases J with
  | zero => simp
  | succ J =>
    have h : ∀ j ∈ range J, lowerValue σ (j + 1) ^ 2 = σ j ^ 2 := fun j _ => by
      rw [lowerValue, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
    have h0 : lowerValue σ 0 = 0 := by rw [lowerValue, if_pos rfl]
    rw [Finset.sum_range_succ' (fun j => lowerValue σ j ^ 2), Finset.sum_congr rfl h, h0,
      Finset.sum_range_succ (fun j => σ j ^ 2)]
    nlinarith [sq_nonneg (σ J)]

theorem sum_upperValue_sq_le (σ : ℕ → ℝ) (J : ℕ) :
    ∑ j ∈ range J, upperValue σ J j ^ 2 ≤ ∑ j ∈ range J, σ j ^ 2 := by
  cases J with
  | zero => simp
  | succ J =>
    have h : ∀ j ∈ range J, upperValue σ (J + 1) j ^ 2 = σ (j + 1) ^ 2 := fun j hj => by
      have hjJ := Finset.mem_range.mp hj
      rw [upperValue, if_pos (by omega)]
    have h0 : upperValue σ (J + 1) J = 0 := by rw [upperValue, if_neg (by omega)]
    rw [Finset.sum_range_succ (fun j => upperValue σ (J + 1) j ^ 2), Finset.sum_congr rfl h, h0,
      Finset.sum_range_succ' (fun j => σ j ^ 2)]
    nlinarith [sq_nonneg (σ 0)]

/-- **The norm of the remainder.** The weights `H_B − H_a` have `Σ_a (H_B − H_a)² = 2B − H_B`:
summed over a window of `J` blocks, the squares of the remainders are at most `8B Σ_j σ_j²`. -/
theorem sum_nearRemainder_sq_le (σ : ℕ → ℝ) (B J : ℕ) :
    ∑ j ∈ range J, ∑ a ∈ range B, nearRemainder σ B J j a ^ 2 ≤
      8 * (B * ∑ j ∈ range J, σ j ^ 2) := by
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hH : ∑ a ∈ range B, (harm B - harm a) ^ 2 ≤ 2 * B := by
    have h := HTGeometry.sum_sq_harmonic_tails B
    simp only [← harm_eq_harmonic] at h
    have h0 : 0 ≤ harm B := Finset.sum_nonneg fun k _ => by positivity
    linarith
  have hH' : ∑ a ∈ range B, (harm B - harm (B - 1 - a)) ^ 2 ≤ 2 * B := by
    rw [Finset.sum_range_reflect (fun a => (harm B - harm a) ^ 2) B]
    exact hH
  have hj : ∀ j ∈ range J, ∑ a ∈ range B, nearRemainder σ B J j a ^ 2 ≤
      B * (2 * lowerValue σ j ^ 2 + 2 * upperValue σ J j ^ 2 + 4 * σ j ^ 2) := by
    intro j _
    have h1 : (lowerValue σ j - σ j) ^ 2 ≤ 2 * lowerValue σ j ^ 2 + 2 * σ j ^ 2 := by
      nlinarith [sq_nonneg (lowerValue σ j + σ j)]
    have h2 : (upperValue σ J j - σ j) ^ 2 ≤ 2 * upperValue σ J j ^ 2 + 2 * σ j ^ 2 := by
      nlinarith [sq_nonneg (upperValue σ J j + σ j)]
    calc ∑ a ∈ range B, nearRemainder σ B J j a ^ 2
        ≤ ∑ a ∈ range B, ((lowerValue σ j - σ j) ^ 2 / 2 * (harm B - harm a) ^ 2 +
            (upperValue σ J j - σ j) ^ 2 / 2 * (harm B - harm (B - 1 - a)) ^ 2) :=
          Finset.sum_le_sum fun a _ => by
            rw [nearRemainder]
            exact sq_half_add_le _ _ _ _
      _ = (lowerValue σ j - σ j) ^ 2 / 2 * ∑ a ∈ range B, (harm B - harm a) ^ 2 +
            (upperValue σ J j - σ j) ^ 2 / 2 *
              ∑ a ∈ range B, (harm B - harm (B - 1 - a)) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ (lowerValue σ j - σ j) ^ 2 / 2 * (2 * B) +
            (upperValue σ J j - σ j) ^ 2 / 2 * (2 * B) :=
          add_le_add (mul_le_mul_of_nonneg_left hH (by positivity))
            (mul_le_mul_of_nonneg_left hH' (by positivity))
      _ ≤ B * (2 * lowerValue σ j ^ 2 + 2 * upperValue σ J j ^ 2 + 4 * σ j ^ 2) := by
          nlinarith [mul_le_mul_of_nonneg_left h1 hB0, mul_le_mul_of_nonneg_left h2 hB0]
  calc ∑ j ∈ range J, ∑ a ∈ range B, nearRemainder σ B J j a ^ 2
      ≤ ∑ j ∈ range J,
          B * (2 * lowerValue σ j ^ 2 + 2 * upperValue σ J j ^ 2 + 4 * σ j ^ 2) :=
        Finset.sum_le_sum hj
    _ = B * (2 * ∑ j ∈ range J, lowerValue σ j ^ 2 + 2 * ∑ j ∈ range J, upperValue σ J j ^ 2 +
          4 * ∑ j ∈ range J, σ j ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 8 * (B * ∑ j ∈ range J, σ j ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left (sum_lowerValue_sq_le σ J) hB0,
          mul_le_mul_of_nonneg_left (sum_upperValue_sq_le σ J) hB0]

/-- **The near kernel.** Against a divisor with vanishing block sums the near kernel of a
block-constant divisor acts through the remainder of the jumps only. -/
theorem two_mul_abs_sum_nearKernel_le {N B J : ℕ} (hB : 0 < B) (hBN : B ≤ N) (σ z : ℕ → ℝ)
    (hzero : ∀ j : ℕ,
      ∑ n ∈ (Ioc N (N + B * J)).filter (fun n => blockIndex N B n = j), z n = 0)
    {p q : ℝ} (hp : 0 < p) (hpq : p * q = 1) :
    2 * |∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
        σ (blockIndex N B m) * z n * nearKernel B m n| ≤
      8 * (p * ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) ^ 2 +
        q * ∑ n ∈ Ioc N (N + B * J), z n ^ 2) := by
  have hq := pos_of_mul_eq_one hp hpq
  -- the potential of the block-constant divisor
  have hinner : ∀ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
        σ (blockIndex N B m) * z n * nearKernel B m n =
      harm B * (σ (blockIndex N B n) * z n) +
        nearRemainder σ B J (blockIndex N B n) (blockPos N B n) * z n := by
    intro n hn
    have h := sum_blockFunction_mul_nearKernel_of_mem hB hBN σ hn
    have hfac : ∑ m ∈ (Ioc N (N + B * J)).erase n,
          σ (blockIndex N B m) * z n * nearKernel B m n =
        z n * ∑ m ∈ (Ioc N (N + B * J)).erase n, σ (blockIndex N B m) * nearKernel B m n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hfac, h]
    ring
  -- the multiple of `H_B` is constant on blocks
  have horth : ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) * z n = 0 :=
    sum_blockFunction_mul_eq_zero N B (Ioc N (N + B * J)) σ z hzero
  have hsum : ∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
        σ (blockIndex N B m) * z n * nearKernel B m n =
      ∑ n ∈ Ioc N (N + B * J),
        nearRemainder σ B J (blockIndex N B n) (blockPos N B n) * z n := by
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ← Finset.mul_sum, horth, mul_zero,
      zero_add]
  -- the norm of the remainder, by blocks and positions
  have hrem : ∑ n ∈ Ioc N (N + B * J),
      nearRemainder σ B J (blockIndex N B n) (blockPos N B n) ^ 2 ≤
        8 * ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) ^ 2 := by
    have hL : ∀ j ∈ range J, ∑ a ∈ range B,
          nearRemainder σ B J (blockIndex N B (N + 1 + B * j + a))
            (blockPos N B (N + 1 + B * j + a)) ^ 2 =
        ∑ a ∈ range B, nearRemainder σ B J j a ^ 2 := fun j _ =>
      Finset.sum_congr rfl fun a ha => by
        rw [blockIndex_add hB N j (Finset.mem_range.mp ha),
          blockPos_add N B j (Finset.mem_range.mp ha)]
    have hR : ∀ j ∈ range J, ∑ a ∈ range B, σ (blockIndex N B (N + 1 + B * j + a)) ^ 2 =
        B * σ j ^ 2 := by
      intro j _
      have h : ∀ a ∈ range B, σ (blockIndex N B (N + 1 + B * j + a)) ^ 2 = σ j ^ 2 :=
        fun a ha => by rw [blockIndex_add hB N j (Finset.mem_range.mp ha)]
      rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [sum_Ioc_blocks (fun n => nearRemainder σ B J (blockIndex N B n) (blockPos N B n) ^ 2),
      sum_Ioc_blocks (fun n => σ (blockIndex N B n) ^ 2), Finset.sum_congr rfl hL,
      Finset.sum_congr rfl hR, ← Finset.mul_sum]
    exact sum_nearRemainder_sq_le σ B J
  rw [hsum]
  have h3 : 2 * |∑ n ∈ Ioc N (N + B * J),
      nearRemainder σ B J (blockIndex N B n) (blockPos N B n) * z n| ≤
      p * ∑ n ∈ Ioc N (N + B * J),
          nearRemainder σ B J (blockIndex N B n) (blockPos N B n) ^ 2 +
        q * ∑ n ∈ Ioc N (N + B * J), z n ^ 2 :=
    two_mul_abs_sum_le _ _ z hp hpq
  have hz0 : 0 ≤ ∑ n ∈ Ioc N (N + B * J), z n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hrem hp.le, mul_nonneg hq.le hz0]

/-! ### The cross term -/

theorem chebyshev_nonneg (K : ℕ) : 0 ≤ chebyshev K :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- The constant of the cross term on a window of ratio at most `Q`. -/
def crossConstant (Q : ℕ) : ℝ := 12 + 2 * (Q : ℝ) + 2 * chebyshev Q

theorem crossConstant_pos (Q : ℕ) : 0 < crossConstant Q := by
  have h1 := chebyshev_nonneg Q
  have h2 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  unfold crossConstant
  linarith

/-- The four parts of the cross term add up to at most the constant. -/
theorem add_le_crossConstant {N B M Q : ℕ} (hN : 0 < N) (hBN : B ≤ N) (hQ : N + M ≤ Q * N) :
    (B : ℝ) * M / (N : ℝ) ^ 2 + (3 + (M : ℝ) / (4 * N) + 2 * chebyshev Q) + 8 + (B : ℝ) / N ≤
      crossConstant Q := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hBN' : (B : ℝ) ≤ N := by exact_mod_cast hBN
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hM : (M : ℝ) ≤ Q * N := by
    have : ((N + M : ℕ) : ℝ) ≤ ((Q * N : ℕ) : ℝ) := by exact_mod_cast hQ
    push_cast at this
    linarith
  have h1 : (B : ℝ) * M / (N : ℝ) ^ 2 ≤ Q := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hBN' hM hM0 hN'.le]
  have h2 : (M : ℝ) / (4 * N) ≤ (Q : ℝ) / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h3 : (B : ℝ) / N ≤ 1 := by
    rw [div_le_one hN']
    exact hBN'
  unfold crossConstant
  linarith

/-- The pairing of two divisors is symmetric. -/
theorem combBilin_comm (S : Finset ℕ) (c e : ℕ → ℝ) : combBilin S c e = combBilin S e c := by
  have hsw : ∑ n ∈ S, ∑ m ∈ S.erase n, c m * e n * pairKernel m n =
      ∑ m ∈ S, ∑ n ∈ S.erase m, c m * e n * pairKernel m n :=
    sum_erase_comm S fun m n => c m * e n * pairKernel m n
  rw [combBilin, combBilin, hsw]
  congr 1
  · exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by
      rw [pairKernel_comm m n]
      ring
  · exact Finset.sum_congr rfl fun n _ => by ring

/-- Weil's form of a sum of two divisors. -/
theorem combForm_add (S : Finset ℕ) (s z : ℕ → ℝ) :
    combForm S (fun n => s n + z n) = combForm S s + 2 * formBilin S s z + combForm S z := by
  have h1 : degOne S (fun n => s n + z n) = degOne S s + degOne S z := by
    simp only [degOne, add_div, Finset.sum_add_distrib]
  have h2 : degTwo S (fun n => s n + z n) = degTwo S s + degTwo S z := by
    simp only [degTwo, Finset.sum_add_distrib]
  have h3 : combPairing S (fun n => s n + z n) =
      combPairing S s + (combBilin S s z + combBilin S z s) + combPairing S z := by
    simp only [combPairing, combBilin]
    have hk : ∑ n ∈ S, ∑ m ∈ S.erase n, (s m + z m) * (s n + z n) * pairKernel m n =
        ∑ n ∈ S, ∑ m ∈ S.erase n, s m * s n * pairKernel m n +
        (∑ n ∈ S, ∑ m ∈ S.erase n, s m * z n * pairKernel m n +
          ∑ n ∈ S, ∑ m ∈ S.erase n, z m * s n * pairKernel m n) +
        ∑ n ∈ S, ∑ m ∈ S.erase n, z m * z n * pairKernel m n := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
    have hd : ∑ n ∈ S, (s n + z n) ^ 2 * counterterm n =
        ∑ n ∈ S, s n ^ 2 * counterterm n +
        (∑ n ∈ S, s n * z n * counterterm n + ∑ n ∈ S, z n * s n * counterterm n) +
        ∑ n ∈ S, z n ^ 2 * counterterm n := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hk, hd]
    ring
  unfold combForm formBilin
  rw [h1, h2, h3, combBilin_comm S z s]
  ring

/-- **The cross term.** On a window of `J` complete blocks of `B ≤ N` points and ratio at most
`Q`, a divisor constant on blocks and a divisor with vanishing block sums pair in Weil's form
with `2|𝔚(s, z)| ≤ C_Q (p Σ s_n² + q Σ z_n²)` for all `pq = 1`. The constant does not depend on
the block size. -/
theorem two_mul_abs_formBilin_le {N B J Q : ℕ} (hB : 0 < B) (hBN : B ≤ N)
    (hQ : N + B * J ≤ Q * N) (σ z : ℕ → ℝ)
    (hzero : ∀ j : ℕ,
      ∑ n ∈ (Ioc N (N + B * J)).filter (fun n => blockIndex N B n = j), z n = 0)
    {p q : ℝ} (hp : 0 < p) (hpq : p * q = 1) :
    2 * |formBilin (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) z| ≤
      crossConstant Q * (p * ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) ^ 2 +
        q * ∑ n ∈ Ioc N (N + B * J), z n ^ 2) := by
  have hN : 0 < N := lt_of_lt_of_le hB hBN
  have hq := pos_of_mul_eq_one hp hpq
  have hsub : Ioc N (N + B * J) ⊆ Ioc N (N + B * J) := Finset.Subset.refl _
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = p * ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) ^ 2 +
      q * ∑ n ∈ Ioc N (N + B * J), z n ^ 2 := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by
    rw [hY]
    exact add_nonneg (mul_nonneg hp.le (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (mul_nonneg hq.le (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  -- the four parts
  have hpole : 2 * |degTwo (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) *
      degOne (Ioc N (N + B * J)) z| ≤ (B : ℝ) * ((B * J : ℕ) : ℝ) / (N : ℝ) ^ 2 * Y := by
    rw [hY]
    exact two_mul_abs_degTwo_mul_degOne_le hN hB hsub (fun n => σ (blockIndex N B n)) z hzero
      hp hpq
  have hdiag : 2 * |∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) * z n * counterterm n| ≤
      (B : ℝ) / N * Y := by
    rw [hY]
    exact two_mul_abs_sum_counterterm_le hN hB hsub σ z hzero hp hpq
  have hfar : 2 * |∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
      σ (blockIndex N B m) * z n * farKernel N B m n| ≤
      (3 + ((B * J : ℕ) : ℝ) / (4 * N) + 2 * chebyshev Q) * Y := by
    rw [hY]
    exact two_mul_abs_sum_erase_le _ (farKernel N B) (farKernel_comm N B)
      (fun n hn => sum_abs_farKernel_le hN hB hQ hsub hn) hp hpq
      (fun m => σ (blockIndex N B m)) z
  have hnear : 2 * |∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
      σ (blockIndex N B m) * z n * nearKernel B m n| ≤ 8 * Y := by
    rw [hY]
    exact two_mul_abs_sum_nearKernel_le hB hBN σ z hzero hp hpq
  -- the pairing splits into the far kernel, the block kernel and the near kernel
  have hblock : ∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
      σ (blockIndex N B m) * z n * blockKernel N B m n = 0 :=
    sum_mul_blockKernel_eq_zero N B (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) z hzero
  have hker : ∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
        σ (blockIndex N B m) * z n * pairKernel m n =
      ∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
          σ (blockIndex N B m) * z n * farKernel N B m n +
        ∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
          σ (blockIndex N B m) * z n * nearKernel B m n := by
    have hsplit : ∀ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
          σ (blockIndex N B m) * z n * pairKernel m n =
        ∑ m ∈ (Ioc N (N + B * J)).erase n, σ (blockIndex N B m) * z n * farKernel N B m n +
          ∑ m ∈ (Ioc N (N + B * J)).erase n, σ (blockIndex N B m) * z n * blockKernel N B m n +
          ∑ m ∈ (Ioc N (N + B * J)).erase n, σ (blockIndex N B m) * z n * nearKernel B m n := by
      intro n _
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by
        rw [farKernel]
        ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib, hblock,
      add_zero]
  have hform : formBilin (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) z =
      degTwo (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) * degOne (Ioc N (N + B * J)) z -
        (∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
            σ (blockIndex N B m) * z n * farKernel N B m n +
          ∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
            σ (blockIndex N B m) * z n * nearKernel B m n -
          ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) * z n * counterterm n) := by
    simp only [formBilin, combBilin]
    rw [degTwo_eq_zero_of_blockSum_eq_zero N B _ z hzero, mul_zero, zero_add, hker]
  rw [hform, ← hY]
  have habs := abs_sub_add_sub_le
    (degTwo (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) * degOne (Ioc N (N + B * J)) z)
    (∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
      σ (blockIndex N B m) * z n * farKernel N B m n)
    (∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
      σ (blockIndex N B m) * z n * nearKernel B m n)
    (∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) * z n * counterterm n)
  calc 2 * |degTwo (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) *
          degOne (Ioc N (N + B * J)) z -
        (∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
            σ (blockIndex N B m) * z n * farKernel N B m n +
          ∑ n ∈ Ioc N (N + B * J), ∑ m ∈ (Ioc N (N + B * J)).erase n,
            σ (blockIndex N B m) * z n * nearKernel B m n -
          ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) * z n * counterterm n)|
      ≤ (B : ℝ) * ((B * J : ℕ) : ℝ) / (N : ℝ) ^ 2 * Y +
          (3 + ((B * J : ℕ) : ℝ) / (4 * N) + 2 * chebyshev Q) * Y + 8 * Y + (B : ℝ) / N * Y := by
        linarith
    _ = ((B : ℝ) * ((B * J : ℕ) : ℝ) / (N : ℝ) ^ 2 +
          (3 + ((B * J : ℕ) : ℝ) / (4 * N) + 2 * chebyshev Q) + 8 + (B : ℝ) / N) * Y := by ring
    _ ≤ crossConstant Q * Y := mul_le_mul_of_nonneg_right (add_le_crossConstant hN hBN hQ) hY0

/-! ### Rough divisors are no worse than their block averages -/

/-- **A divisor with a block-constant part.** On a window of `J` complete blocks of `B ≤ N` points
and ratio at most `Q`, let `s` be constant on blocks and `z` have vanishing block sums. If the
margin `log(N/2π) − ρ` of the counterterm over the row is at least `C_Q²/ε`, then
`𝔚(s + z) ≥ 𝔚(s) − ε Σ s_n²`. -/
theorem combForm_blockFunction_add_ge {N B J Q : ℕ} (hB : 0 < B) (hBN : B ≤ N)
    (hQ : N + B * J ≤ Q * N) {ε : ℝ} (hε : 0 < ε)
    (hμ : crossConstant Q ^ 2 / ε ≤ Real.log ((N : ℝ) / (2 * Real.pi)) -
      (harm (2 * B) + 2 + ((B * J : ℕ) : ℝ) / (4 * N) + 2 * chebyshev Q))
    (σ z : ℕ → ℝ)
    (hzero : ∀ j : ℕ,
      ∑ n ∈ (Ioc N (N + B * J)).filter (fun n => blockIndex N B n = j), z n = 0) :
    combForm (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) -
        ε * ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) ^ 2 ≤
      combForm (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n) + z n) := by
  have hN : 0 < N := lt_of_lt_of_le hB hBN
  have hC := crossConstant_pos Q
  have hz0 : 0 ≤ ∑ n ∈ Ioc N (N + B * J), z n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- coercivity on the divisors with vanishing block sums
  have hco : crossConstant Q ^ 2 / ε * ∑ n ∈ Ioc N (N + B * J), z n ^ 2 ≤
      combForm (Ioc N (N + B * J)) z := by
    have hpair := combPairing_le_of_blockSum_eq_zero hN hB hQ (Finset.Subset.refl _) z hzero
    rw [combForm, degTwo_eq_zero_of_blockSum_eq_zero N B _ z hzero, mul_zero, mul_zero, zero_sub]
    nlinarith [mul_le_mul_of_nonneg_right hμ hz0]
  -- the cross term with the weights `ε/C` and `C/ε`
  have hcross := two_mul_abs_formBilin_le hB hBN hQ σ z hzero (p := ε / crossConstant Q)
    (q := crossConstant Q / ε) (div_pos hε hC)
    (by rw [div_mul_div_comm, mul_comm ε, div_self (mul_pos hC hε).ne'])
  rw [cross_weights hC.ne'] at hcross
  rw [combForm_add (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) z]
  have hneg := neg_abs_le (formBilin (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) z)
  linarith

/-- The block averages of a divisor on a window of `J` complete blocks of `B` points. -/
def blockMean (N B J : ℕ) (c : ℕ → ℝ) (j : ℕ) : ℝ :=
  (∑ n ∈ (Ioc N (N + B * J)).filter (fun n => blockIndex N B n = j), c n) / B

/-- A divisor minus its block averages has vanishing block sums. -/
theorem sum_filter_sub_blockMean {B : ℕ} (hB : 0 < B) (N J : ℕ) (c : ℕ → ℝ) (j : ℕ) :
    ∑ n ∈ (Ioc N (N + B * J)).filter (fun n => blockIndex N B n = j),
      (c n - blockMean N B J c (blockIndex N B n)) = 0 := by
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hconst : ∀ n ∈ (Ioc N (N + B * J)).filter (fun n => blockIndex N B n = j),
      c n - blockMean N B J c (blockIndex N B n) = c n - blockMean N B J c j := fun n hn => by
    rw [(Finset.mem_filter.mp hn).2]
  have hcard : (((Ioc N (N + B * J)).filter (fun n => blockIndex N B n = j)).card : ℝ) =
      if j < J then (B : ℝ) else 0 := by
    have h := sum_filter_blockIndex hB N J (fun _ => (1 : ℝ)) j
    simpa using h
  rw [Finset.sum_congr rfl hconst, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
  by_cases hj : j < J
  · have hcancel : (B : ℝ) * blockMean N B J c j =
        ∑ n ∈ (Ioc N (N + B * J)).filter (fun n => blockIndex N B n = j), c n := by
      rw [blockMean]
      field_simp
    rw [if_pos hj, hcancel, sub_self]
  · rw [if_neg hj, zero_mul, sub_zero, sum_filter_blockIndex hB N J c j, if_neg hj]

/-- The block averages have at most the norm of the divisor. -/
theorem sum_blockMean_sq_le {B : ℕ} (hB : 0 < B) (N J : ℕ) (c : ℕ → ℝ) :
    ∑ n ∈ Ioc N (N + B * J), blockMean N B J c (blockIndex N B n) ^ 2 ≤
      ∑ n ∈ Ioc N (N + B * J), c n ^ 2 := by
  have horth : ∑ n ∈ Ioc N (N + B * J), blockMean N B J c (blockIndex N B n) *
      (c n - blockMean N B J c (blockIndex N B n)) = 0 :=
    sum_blockFunction_mul_eq_zero N B (Ioc N (N + B * J)) (blockMean N B J c)
      (fun n => c n - blockMean N B J c (blockIndex N B n)) (sum_filter_sub_blockMean hB N J c)
  have hexp : ∑ n ∈ Ioc N (N + B * J), c n ^ 2 =
      ∑ n ∈ Ioc N (N + B * J), blockMean N B J c (blockIndex N B n) ^ 2 +
        2 * ∑ n ∈ Ioc N (N + B * J), blockMean N B J c (blockIndex N B n) *
          (c n - blockMean N B J c (blockIndex N B n)) +
        ∑ n ∈ Ioc N (N + B * J), (c n - blockMean N B J c (blockIndex N B n)) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hpos : 0 ≤ ∑ n ∈ Ioc N (N + B * J), (c n - blockMean N B J c (blockIndex N B n)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hexp, horth]
  linarith

/-- **Weil's form of a divisor is at least the form of its block averages, up to `ε Σ c_n²`**, as
soon as the margin `log(N/2π) − ρ` is at least `C_Q²/ε`. -/
theorem combForm_ge_blockMean {N B J Q : ℕ} (hB : 0 < B) (hBN : B ≤ N) (hQ : N + B * J ≤ Q * N)
    {ε : ℝ} (hε : 0 < ε)
    (hμ : crossConstant Q ^ 2 / ε ≤ Real.log ((N : ℝ) / (2 * Real.pi)) -
      (harm (2 * B) + 2 + ((B * J : ℕ) : ℝ) / (4 * N) + 2 * chebyshev Q))
    (c : ℕ → ℝ) :
    combForm (Ioc N (N + B * J)) (fun n => blockMean N B J c (blockIndex N B n)) -
        ε * ∑ n ∈ Ioc N (N + B * J), c n ^ 2 ≤ combForm (Ioc N (N + B * J)) c := by
  have h : combForm (Ioc N (N + B * J)) (fun n => blockMean N B J c (blockIndex N B n)) -
      ε * ∑ n ∈ Ioc N (N + B * J), blockMean N B J c (blockIndex N B n) ^ 2 ≤
      combForm (Ioc N (N + B * J))
        (fun n => blockMean N B J c (blockIndex N B n) +
          (c n - blockMean N B J c (blockIndex N B n))) :=
    combForm_blockFunction_add_ge hB hBN hQ hε hμ (blockMean N B J c)
      (fun n => c n - blockMean N B J c (blockIndex N B n)) (sum_filter_sub_blockMean hB N J c)
  have hc : (fun n => blockMean N B J c (blockIndex N B n) +
      (c n - blockMean N B J c (blockIndex N B n))) = c := funext fun n => by ring
  rw [hc] at h
  have hle := sum_blockMean_sq_le hB N J c
  nlinarith [mul_le_mul_of_nonneg_left hle hε.le]

/-- **The inequality at finite scale is decided on block averages.** For every bound `Q` on the
ratio and every `ε > 0` there is `R` such that at every scale `N ≥ R`, on every window of complete
blocks of `⌊N/R⌋` points and ratio at most `Q`, Weil's form of every real divisor is at least the
form of its block averages minus `ε Σ c_n²`. The blocks are fewer than `2QR`
(`blockIndex_lt`). -/
theorem exists_blockSize_combForm_ge_blockMean (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, 0 < R ∧ ∀ N J : ℕ, R ≤ N → N + N / R * J ≤ Q * N → ∀ c : ℕ → ℝ,
      combForm (Ioc N (N + N / R * J))
          (fun n => blockMean N (N / R) J c (blockIndex N (N / R) n)) -
          ε * ∑ n ∈ Ioc N (N + N / R * J), c n ^ 2 ≤
        combForm (Ioc N (N + N / R * J)) c := by
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 3 + (Q : ℝ) / 4 + 2 * chebyshev Q + Real.log (4 * Real.pi) +
      crossConstant Q ^ 2 / ε := ⟨_, rfl⟩
  have hR : 0 < ⌈Real.exp E⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos E)
  refine ⟨⌈Real.exp E⌉₊, hR, ?_⟩
  intro N J hRN hQ c
  have hRE : E ≤ Real.log (⌈Real.exp E⌉₊ : ℝ) := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast hR)]
    exact Nat.le_ceil _
  have hmargin := log_sub_row_ge (M := N / ⌈Real.exp E⌉₊ * J) hR hRN hQ
  exact combForm_ge_blockMean (Nat.div_pos hRN hR) (Nat.div_le_self _ _) hQ hε (by linarith) c

/-- **The Riemann hypothesis is decided on block-constant divisors.** If for every window ratio,
every `η > 0` and every `R` there are arbitrarily large block sizes `B` such that, above the scale
`N = RB`, every divisor constant on the `3KR` blocks of the window `(N, (3K + 1)N]` has
`2 d₁ d₂ − D·D ≥ −η Σ c_n²`, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_frequently_blockFunction_combForm_ge
    (h : ∀ K : ℕ, 1 ≤ K → ∀ η : ℝ, 0 < η → ∀ R : ℕ, 0 < R → ∃ᶠ B : ℕ in atTop, ∀ σ : ℕ → ℝ,
      -η * ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), σ (blockIndex (R * B) B n) ^ 2 ≤
        combForm (Ioc (R * B) (R * B + B * (3 * K * R))) fun n => σ (blockIndex (R * B) B n)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_frequently_combForm_ge fun K hK η hη => ?_
  obtain ⟨R, hR, hred⟩ := exists_blockSize_combForm_ge_blockMean (3 * K + 1) (half_pos hη)
  have hfreq := (h K hK (η / 2) (half_pos hη) R hR).and_eventually (eventually_ge_atTop 1)
  have htend : Tendsto (fun B : ℕ => R * B) atTop atTop :=
    tendsto_atTop_mono (fun B => Nat.le_mul_of_pos_left B hR) tendsto_id
  refine htend.frequently (hfreq.mono fun B hB => ?_)
  obtain ⟨hσ, hB1⟩ := hB
  show ∀ c : ℕ → ℝ, -η * ∑ n ∈ Ioc (R * B) (R * B + 3 * K * (R * B)), c n ^ 2 ≤
    combForm (Ioc (R * B) (R * B + 3 * K * (R * B))) c
  intro c
  have hdiv : R * B / R = B := Nat.mul_div_cancel_left B hR
  have hwin : R * B + 3 * K * (R * B) = R * B + B * (3 * K * R) := by ring
  have h1 := hred (R * B) (3 * K * R) (Nat.le_mul_of_pos_right R hB1)
    (by rw [hdiv]; exact le_of_eq (by ring)) c
  rw [hdiv] at h1
  have h2 := hσ (blockMean (R * B) B (3 * K * R) c)
  have h3 := sum_blockMean_sq_le (by omega : 0 < B) (R * B) (3 * K * R) c
  rw [hwin]
  nlinarith [mul_le_mul_of_nonneg_left h3 (half_pos hη).le]

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
