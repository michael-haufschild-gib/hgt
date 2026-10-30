import Mathlib.Data.Complex.Basic

/-!
# Affine-invariant kernels are trivial

The Weil kernel on the positive integers depends only on the ratio `m/n`: it is invariant under the
dilations `n ↦ a n`. Additive kernels depend only on `m − n`: they are invariant under the successor
`n ↦ n + 1`. A positivity principle for the ring would ask for both. This file shows that a kernel
invariant under both carries no information at all.

* **Translation** (`kernel_add_eq`). Successor invariance gives `K(m + t, n + t) = K(m, n)`.
* **Three constants** (`affineInvariant_kernel_lt`, `affineInvariant_kernel_gt`,
  `affineInvariant_kernel_diag`). If `K` is invariant under every dilation and under the successor,
  then `K(m, n) = K(1, 2)` for `m < n`, `K(m, n) = K(2, 1)` for `m > n`, and `K(m, m) = K(1, 1)`. The
  pair `(m, n)` is first translated to `(dm, d(m + 1))`, `d = n − m`, then dilated to `(m, m + 1)`,
  then translated to `(1, 2)`.

So the affine semigroup acts on ordered pairs of positive integers with one orbit above the
diagonal and one below. A kernel that sees arithmetic must break one of the two invariances. The
Weil kernel keeps the dilations and breaks the successor; the breaking is the shell structure of the
prime pair form, and a ring positivity principle has to carry it as a boundary term rather than as an
invariance.
-/

namespace GaloisForLFunctions.ArithmeticGaugeTheory

variable {K : ℕ → ℕ → ℂ}

/-- Successor invariance iterates to translation invariance. -/
theorem kernel_add_eq (hsucc : ∀ m n, 1 ≤ m → 1 ≤ n → K (m + 1) (n + 1) = K m n)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) : ∀ t, K (m + t) (n + t) = K m n := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [← add_assoc, ← add_assoc, hsucc (m + t) (n + t) (by omega) (by omega), ih]

/-- **Above the diagonal an affine-invariant kernel is constant.** -/
theorem affineInvariant_kernel_lt
    (hdil : ∀ a m n, 1 ≤ a → 1 ≤ m → 1 ≤ n → K (a * m) (a * n) = K m n)
    (hsucc : ∀ m n, 1 ≤ m → 1 ≤ n → K (m + 1) (n + 1) = K m n)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) : K m n = K 1 2 := by
  set d := n - m with hd
  have hd1 : 1 ≤ d := by omega
  -- Translate `(m, n)` to `(dm, d(m + 1))`.
  have htr : K (d * m) (d * (m + 1)) = K m n := by
    have h := kernel_add_eq hsucc hm (by omega : 1 ≤ n) (d * m - m)
    have h1 : m + (d * m - m) = d * m := by
      have : m ≤ d * m := Nat.le_mul_of_pos_left m hd1
      omega
    have h2 : n + (d * m - m) = d * (m + 1) := by
      have : m ≤ d * m := Nat.le_mul_of_pos_left m hd1
      rw [Nat.mul_succ]
      omega
    rwa [h1, h2] at h
  -- Dilate to `(m, m + 1)`, then translate to `(1, 2)`.
  have hdil' := hdil d m (m + 1) hd1 hm (by omega)
  have hshift := kernel_add_eq hsucc (le_refl 1) (by norm_num : 1 ≤ 2) (m - 1)
  have h3 : 1 + (m - 1) = m := by omega
  have h4 : 2 + (m - 1) = m + 1 := by omega
  rw [h3, h4] at hshift
  rw [← htr, hdil', hshift]

/-- **Below the diagonal an affine-invariant kernel is constant.** -/
theorem affineInvariant_kernel_gt
    (hdil : ∀ a m n, 1 ≤ a → 1 ≤ m → 1 ≤ n → K (a * m) (a * n) = K m n)
    (hsucc : ∀ m n, 1 ≤ m → 1 ≤ n → K (m + 1) (n + 1) = K m n)
    {m n : ℕ} (hn : 1 ≤ n) (hnm : n < m) : K m n = K 2 1 := by
  have := affineInvariant_kernel_lt (K := fun i j => K j i)
    (fun a i j ha hi hj => hdil a j i ha hj hi) (fun i j hi hj => hsucc j i hj hi) hn hnm
  exact this

/-- **On the diagonal an affine-invariant kernel is constant.** -/
theorem affineInvariant_kernel_diag (hsucc : ∀ m n, 1 ≤ m → 1 ≤ n → K (m + 1) (n + 1) = K m n)
    {m : ℕ} (hm : 1 ≤ m) : K m m = K 1 1 := by
  have h := kernel_add_eq hsucc (le_refl 1) (le_refl 1) (m - 1)
  rwa [show 1 + (m - 1) = m by omega] at h

end GaloisForLFunctions.ArithmeticGaugeTheory
