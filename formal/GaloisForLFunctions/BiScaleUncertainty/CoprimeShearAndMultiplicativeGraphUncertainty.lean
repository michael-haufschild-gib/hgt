import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Pillar VII: Discrete Coprime Shear & Multiplicative Graph Uncertainty

This module establishes the second part of **Layer III (Non-Commutative Hyperbolic &
Arithmetic-Shear Calculus)** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`).

To overcome **Trap 6 (The Beurling Obstruction)** and **Trap 3 / Trap 7 (The Nodal Collar Blind Spot
on `SourceGraph` in `CHMD`)**, a bi-scale theory must couple the **multiplicative semigroup action**
(`mulShift k v n = v(k * n)`) to the **additive ring generator** (`addShift v n = v(n + 1)` and
`addDiff v n = v(n + 1) - v(n)`).

## Main Results

1. **Non-Commutative Multiplicative-Additive Telescoping
   (`addDiff_mulShift_eq_sum_addDiff`, `mulShift_addShift_comm_eq_sum_addDiff`):**
   The dilated additive step `v(k(n + 1)) - v(kn)` telescopes across `k` unit additive steps
   `∑ j ∈ range k, (v(kn + j + 1) - v(kn + j))`, and the multiplicative-additive commutator
   `v(k(n + 1)) - v(kn + 1)` telescopes across `k - 1` intermediate additive steps.
2. **Bi-Scale Multiplicative-to-Additive Dirichlet Energy Inequality
   (`addDiff_mulShift_sq_le`, `sum_addDiff_mulShift_sq_le`):**
   Using the division-free finite Cauchy–Schwarz identity `sq_sum_le_card_mul_sum_sq` and exact
   residue-block flattening `sum_range_mul_add_eq_sum_range`,
   `∑ n ∈ range N, (v(k(n + 1)) - v(kn))^2 ≤ k * ∑ m ∈ range (k * N), (v(m + 1) - v(m))^2`.
3. **Coprime Successor Orthogonality & Prime-Fiber Coercivity
   (`not_dvd_succ_of_dvd`, `addDiff_sq_eq_sq_of_dvd_support`,
   `two_mul_sq_le_neighbor_addDiff_sq_of_dvd_support`):**
   Because `gcd(n, n + 1) = 1`, no divisor `d ≥ 2` divides both `n` and `n + 1` (or `n - 1`).
   Consequently, any state `v` supported on multiples of `d ≥ 2` is forced to vanish at the
   additive neighbors `n ± 1` of every active node `d ∣ n`, paying full additive Dirichlet energy
   `(v(n) - v(n - 1))^2 + (v(n + 1) - v(n))^2 = 2 v(n)^2`.
4. **Exact Beurling–Deny Nodal Decomposition & Additive Control of Opposite-Sign Multiplicative
   Cross Terms (`nodal_mulJump_sq_decomp`, `four_mul_nodal_cross_le_mulJump_sq`,
   `four_mul_nodal_cross_le_addDiff_sum_sq`):**
   Decomposing `v = v⁺ - v⁻` gives the exact identity
   `(v(kn) - v(n))^2 = (|v(kn)| - |v(n)|)^2 + 4 (v⁺(kn) v⁻(n) + v⁻(kn) v⁺(n))`,
   and coupling it to additive telescoping bounds the nodal cross term `4 (v⁺(kn) v⁻(n) + v⁻(kn) v⁺(n))`
   by the additive Dirichlet energy between `n` and `kn`.
-/

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

/-! ## §1. Discrete Multiplicative Dilation, Additive Shift, and Exact Telescoping -/

/-- Discrete multiplicative dilation `(mulShift k v)(n) = v(k * n)`. -/
def mulShift (k : ℕ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  v (k * n)

/-- Discrete additive successor translation `(addShift v)(n) = v(n + 1)`. -/
def addShift (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  v (n + 1)

/-- Forward additive difference `(addDiff v)(n) = v(n + 1) - v(n)`. -/
def addDiff (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  v (n + 1) - v n

/-- Multiplicative jump along scale `k`: `(mulJump k v)(n) = v(k * n) - v(n)`. -/
def mulJump (k : ℕ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  v (k * n) - v n

/-- **Exact Additive Telescoping Identity:**
For any sequence `v : ℕ → ℝ` and any `a, m : ℕ`,
`v (a + m) - v a = ∑ j ∈ range m, addDiff v (a + j)`. -/
theorem telescope_addDiff (v : ℕ → ℝ) (a m : ℕ) :
    v (a + m) - v a = ∑ j ∈ Finset.range m, addDiff v (a + j) := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold addDiff
    rw [show a + (m + 1) = a + m + 1 by omega]
    ring

/-- **Dilated Additive Step Telescopes Across `k` Unit Additive Steps:**
`addDiff (mulShift k v) n = v(k(n + 1)) - v(kn) = ∑ j ∈ range k, addDiff v (k * n + j)`. -/
theorem addDiff_mulShift_eq_sum_addDiff (v : ℕ → ℝ) (k n : ℕ) :
    addDiff (mulShift k v) n = ∑ j ∈ Finset.range k, addDiff v (k * n + j) := by
  unfold addDiff mulShift
  rw [Nat.mul_add, Nat.mul_one]
  exact telescope_addDiff v (k * n) k

/-- **Multiplicative-Additive Commutator Telescoping (`k ≥ 1`):**
The non-commutativity defect between `addShift` and `mulShift k` at `n`,
`addShift (mulShift k v) n - mulShift k (addShift v) n = v(k(n + 1)) - v(kn + 1)`,
telescopes across the `k - 1` intermediate additive steps from `kn + 1` to `kn + k`. -/
theorem mulShift_addShift_comm_eq_sum_addDiff (v : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    addShift (mulShift k v) n - mulShift k (addShift v) n =
      ∑ j ∈ Finset.range (k - 1), addDiff v (k * n + 1 + j) := by
  unfold addShift mulShift
  have hk_eq : k * (n + 1) = (k * n + 1) + (k - 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [hk_eq]
  exact telescope_addDiff v (k * n + 1) (k - 1)

/-- **Multiplicative Jump Telescopes Across `(k - 1) * n` Additive Steps (`k ≥ 1`):**
For any `k ≥ 1` and `n : ℕ`, `mulJump k v n = v(kn) - v(n)` equals the sum of unit additive
differences over `[n, kn)`. -/
theorem mulJump_eq_sum_addDiff (v : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    mulJump k v n = ∑ j ∈ Finset.range ((k - 1) * n), addDiff v (n + j) := by
  unfold mulJump
  have hkn : k * n = n + (k - 1) * n := by
    calc
      k * n = (1 + (k - 1)) * n := by rw [Nat.add_sub_of_le hk]
      _ = n + (k - 1) * n := by rw [Nat.add_mul, Nat.one_mul]
  rw [hkn]
  exact telescope_addDiff v n ((k - 1) * n)

/-! ## §2. Division-Free Finite Cauchy–Schwarz & Bi-Scale Dirichlet Energy Inequality -/

/-- **Exact Lagrange / Pairwise-Difference Identity on a Finite Set:**
`2 * (s.card : ℝ) * (∑ i ∈ s, u i ^ 2) - 2 * (∑ i ∈ s, u i) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, (u i - u j) ^ 2`. -/
theorem lagrange_finset_sum_sq_sub_sq_sum {ι : Type*} (s : Finset ι) (u : ι → ℝ) :
    2 * (s.card : ℝ) * (∑ i ∈ s, u i ^ 2) - 2 * (∑ i ∈ s, u i) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (u i - u j) ^ 2 := by
  have hinner (i : ι) :
      (∑ j ∈ s, (u i - u j) ^ 2) =
        (s.card : ℝ) * u i ^ 2 - 2 * u i * (∑ j ∈ s, u j) + ∑ j ∈ s, u j ^ 2 := by
    calc
      (∑ j ∈ s, (u i - u j) ^ 2)
          = ∑ j ∈ s, ((u i ^ 2 - 2 * u i * u j) + u j ^ 2) := by
        refine Finset.sum_congr rfl fun j _ => by ring
      _ = (∑ j ∈ s, (u i ^ 2 - 2 * u i * u j)) + ∑ j ∈ s, u j ^ 2 :=
        Finset.sum_add_distrib
      _ = (∑ j ∈ s, u i ^ 2) - (∑ j ∈ s, 2 * u i * u j) + ∑ j ∈ s, u j ^ 2 := by
        rw [Finset.sum_sub_distrib]
      _ = (s.card : ℝ) * u i ^ 2 - 2 * u i * (∑ j ∈ s, u j) + ∑ j ∈ s, u j ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have hmid : (∑ i ∈ s, 2 * u i * (∑ j ∈ s, u j)) = 2 * (∑ i ∈ s, u i) ^ 2 := by
    calc
      (∑ i ∈ s, 2 * u i * (∑ j ∈ s, u j))
          = ∑ i ∈ s, u i * (2 * ∑ j ∈ s, u j) :=
        Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i ∈ s, u i) * (2 * ∑ j ∈ s, u j) := (Finset.sum_mul _ _ _).symm
      _ = 2 * (∑ i ∈ s, u i) ^ 2 := by ring
  calc
    2 * (s.card : ℝ) * (∑ i ∈ s, u i ^ 2) - 2 * (∑ i ∈ s, u i) ^ 2
        = (∑ i ∈ s, (s.card : ℝ) * u i ^ 2) -
            (∑ i ∈ s, 2 * u i * (∑ j ∈ s, u j)) +
            ∑ _i ∈ s, ∑ j ∈ s, u j ^ 2 := by
      rw [← Finset.mul_sum, hmid]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = ∑ i ∈ s, ((s.card : ℝ) * u i ^ 2 - 2 * u i * (∑ j ∈ s, u j) + ∑ j ∈ s, u j ^ 2) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    _ = ∑ i ∈ s, ∑ j ∈ s, (u i - u j) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => (hinner i).symm

/-- **Finite Cauchy–Schwarz Inequality for Sums of Squares:**
`(∑ i ∈ s, u i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, u i ^ 2`. -/
theorem sq_sum_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (u : ι → ℝ) :
    (∑ i ∈ s, u i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, u i ^ 2 := by
  have hlag := lagrange_finset_sum_sq_sub_sq_sum s u
  have hnonneg : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (u i - u j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

/-- **Pointwise Quadratic Magnification of the Dilated Additive Difference:**
`(v(k(n + 1)) - v(kn))^2 ≤ k * ∑ j ∈ range k, (v(kn + j + 1) - v(kn + j))^2`. -/
theorem addDiff_mulShift_sq_le (v : ℕ → ℝ) (k n : ℕ) :
    addDiff (mulShift k v) n ^ 2 ≤
      (k : ℝ) * ∑ j ∈ Finset.range k, addDiff v (k * n + j) ^ 2 := by
  rw [addDiff_mulShift_eq_sum_addDiff]
  simpa only [Finset.card_range] using
    sq_sum_le_card_mul_sum_sq (Finset.range k) (fun j => addDiff v (k * n + j))

/-- **Exact Residue-Block Flattening Identity:**
Summing `g(k * n + j)` over `n ∈ range N` and `j ∈ range k` partitions `range (k * N)` into
disjoint blocks of length `k`:
`∑ n ∈ range N, ∑ j ∈ range k, g (k * n + j) = ∑ m ∈ range (k * N), g m`. -/
theorem sum_range_mul_add_eq_sum_range (g : ℕ → ℝ) (k N : ℕ) :
    (∑ n ∈ Finset.range N, ∑ j ∈ Finset.range k, g (k * n + j)) =
      ∑ m ∈ Finset.range (k * N), g m := by
  induction N with
  | zero =>
    simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]

/-- **Bi-Scale Multiplicative-to-Additive Dirichlet Energy Inequality:**
For any sequence `v : ℕ → ℝ`, dilation factor `k : ℕ`, and truncation `N : ℕ`,
`∑ n ∈ range N, (v(k(n + 1)) - v(kn))^2 ≤ k * ∑ m ∈ range (k * N), (v(m + 1) - v(m))^2`. -/
theorem sum_addDiff_mulShift_sq_le (v : ℕ → ℝ) (k N : ℕ) :
    (∑ n ∈ Finset.range N, addDiff (mulShift k v) n ^ 2) ≤
      (k : ℝ) * ∑ m ∈ Finset.range (k * N), addDiff v m ^ 2 := by
  calc
    (∑ n ∈ Finset.range N, addDiff (mulShift k v) n ^ 2)
        ≤ ∑ n ∈ Finset.range N, (k : ℝ) * ∑ j ∈ Finset.range k, addDiff v (k * n + j) ^ 2 :=
      Finset.sum_le_sum fun n _ => addDiff_mulShift_sq_le v k n
    _ = (k : ℝ) * ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range k, addDiff v (k * n + j) ^ 2 := by
      rw [← Finset.mul_sum]
    _ = (k : ℝ) * ∑ m ∈ Finset.range (k * N), addDiff v m ^ 2 := by
      rw [sum_range_mul_add_eq_sum_range (fun m => addDiff v m ^ 2) k N]

/-! ## §3. Coprime Successor Orthogonality & Prime-Fiber Additive Coercivity -/

/-- **No Divisor `d ≥ 2` Divides Both `n` and `n + 1`:**
Consecutive integers are coprime, so `d ∣ n` and `2 ≤ d` imply `¬ (d ∣ n + 1)`. -/
theorem not_dvd_succ_of_dvd {d n : ℕ} (hd : 2 ≤ d) (hdvd : d ∣ n) :
    ¬ (d ∣ n + 1) := by
  intro hdvd_succ
  have hdvd_one : d ∣ 1 := by
    have hsub := Nat.dvd_sub hdvd_succ hdvd
    simpa using hsub
  have hle : d ≤ 1 := Nat.le_of_dvd zero_lt_one hdvd_one
  omega

/-- **No Divisor `d ≥ 2` Divides Both `n` (`n ≥ 1`) and `n - 1`:**
If `2 ≤ d`, `1 ≤ n`, and `d ∣ n`, then `¬ (d ∣ n - 1)`. -/
theorem not_dvd_pred_of_dvd {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) (hdvd : d ∣ n) :
    ¬ (d ∣ n - 1) := by
  intro hdvd_pred
  have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hnot := not_dvd_succ_of_dvd hd hdvd_pred
  rw [hsucc] at hnot
  exact hnot hdvd

/-- **Forward Additive Coercivity on Divisor-Supported Fibers:**
If `v : ℕ → ℝ` is supported on multiples of `d ≥ 2` (`∀ m, ¬ (d ∣ m) → v m = 0`), then at every
multiple `d ∣ n`, the forward additive difference square `(v(n + 1) - v(n))^2` equals `v(n)^2`. -/
theorem addDiff_sq_eq_sq_of_dvd_support {v : ℕ → ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hsupp : ∀ m : ℕ, ¬ (d ∣ m) → v m = 0) {n : ℕ} (hdvd : d ∣ n) :
    addDiff v n ^ 2 = v n ^ 2 := by
  unfold addDiff
  have hzero : v (n + 1) = 0 := hsupp (n + 1) (not_dvd_succ_of_dvd hd hdvd)
  rw [hzero, zero_sub, neg_sq]

/-- **Two-Sided Additive Neighbor Coercivity on Divisor-Supported Fibers:**
If `v : ℕ → ℝ` is supported on multiples of `d ≥ 2`, then at every positive multiple `d ∣ n`
(`1 ≤ n`), both adjacent additive steps `(n - 1, n)` and `(n, n + 1)` carry full energy `v(n)^2`:
`addDiff v (n - 1) ^ 2 + addDiff v n ^ 2 = 2 * v n ^ 2`. -/
theorem neighbor_addDiff_sq_eq_two_mul_sq_of_dvd_support {v : ℕ → ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hsupp : ∀ m : ℕ, ¬ (d ∣ m) → v m = 0) {n : ℕ} (hn : 1 ≤ n) (hdvd : d ∣ n) :
    addDiff v (n - 1) ^ 2 + addDiff v n ^ 2 = 2 * v n ^ 2 := by
  have hright := addDiff_sq_eq_sq_of_dvd_support hd hsupp hdvd
  have hleft : addDiff v (n - 1) ^ 2 = v n ^ 2 := by
    unfold addDiff
    have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hzero : v (n - 1) = 0 := hsupp (n - 1) (not_dvd_pred_of_dvd hd hn hdvd)
    rw [hsucc, hzero, sub_zero]
  linarith

/-! ## §4. Exact Beurling–Deny Nodal Decomposition & Additive Control of Nodal Cross Terms -/

/-- Positive nodal part `v⁺(n) = max(v(n), 0)` of a discrete state `v : ℕ → ℝ`. -/
def seqPos (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  max (v n) 0

/-- Negative nodal part `v⁻(n) = max(-v(n), 0)` of a discrete state `v : ℕ → ℝ`. -/
def seqNeg (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  max (-v n) 0

theorem seqPos_nonneg (v : ℕ → ℝ) (n : ℕ) : 0 ≤ seqPos v n :=
  le_max_right _ _

theorem seqNeg_nonneg (v : ℕ → ℝ) (n : ℕ) : 0 ≤ seqNeg v n :=
  le_max_right _ _

theorem seqPos_sub_seqNeg (v : ℕ → ℝ) (n : ℕ) :
    seqPos v n - seqNeg v n = v n := by
  unfold seqPos seqNeg
  rcases le_total 0 (v n) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]

theorem seqPos_add_seqNeg (v : ℕ → ℝ) (n : ℕ) :
    seqPos v n + seqNeg v n = |v n| := by
  unfold seqPos seqNeg
  rcases le_total 0 (v n) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero, abs_of_nonneg h]
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_add, abs_of_nonpos h]

theorem seqPos_mul_seqNeg (v : ℕ → ℝ) (n : ℕ) :
    seqPos v n * seqNeg v n = 0 := by
  unfold seqPos seqNeg
  rcases le_total 0 (v n) with h | h
  · rw [max_eq_right (neg_nonpos.mpr h), mul_zero]
  · rw [max_eq_right h, zero_mul]

/-- **Exact Beurling–Deny Nodal Decomposition of the Multiplicative Jump Square:**
For every `v : ℕ → ℝ` and `k, n : ℕ`,
`(v(kn) - v(n))^2 = (|v(kn)| - |v(n)|)^2 + 4 * (v⁺(kn) v⁻(n) + v⁻(kn) v⁺(n))`. -/
theorem nodal_mulJump_sq_decomp (v : ℕ → ℝ) (k n : ℕ) :
    mulJump k v n ^ 2 =
      (|v (k * n)| - |v n|) ^ 2 +
        4 * (seqPos v (k * n) * seqNeg v n + seqNeg v (k * n) * seqPos v n) := by
  unfold mulJump
  rw [← seqPos_add_seqNeg v (k * n), ← seqPos_add_seqNeg v n,
    ← seqPos_sub_seqNeg v (k * n), ← seqPos_sub_seqNeg v n]
  have h1 := seqPos_mul_seqNeg v (k * n)
  have h2 := seqPos_mul_seqNeg v n
  linear_combination -4 * h1 - 4 * h2

/-- **Upper Bound on the Nodal Opposite-Sign Multiplicative Cross Term:**
Because `(|v(kn)| - |v(n)|)^2 ≥ 0`, the opposite-sign nodal cross pairing is bounded above by
the multiplicative jump square:
`4 * (v⁺(kn) v⁻(n) + v⁻(kn) v⁺(n)) ≤ (v(kn) - v(n))^2`. -/
theorem four_mul_nodal_cross_le_mulJump_sq (v : ℕ → ℝ) (k n : ℕ) :
    4 * (seqPos v (k * n) * seqNeg v n + seqNeg v (k * n) * seqPos v n) ≤
      mulJump k v n ^ 2 := by
  have hdecomp := nodal_mulJump_sq_decomp v k n
  have hsq : 0 ≤ (|v (k * n)| - |v n|) ^ 2 := sq_nonneg _
  linarith

/-- **Bi-Scale Additive Control of the Multiplicative Nodal Cross Term (`k ≥ 1`):**
Coupling the Beurling–Deny nodal decomposition with additive telescoping bounds the opposite-sign
multiplicative cross term `4 * (v⁺(kn) v⁻(n) + v⁻(kn) v⁺(n))` directly by the additive successor
Dirichlet energy between `n` and `kn`:
`4 * (v⁺(kn) v⁻(n) + v⁻(kn) v⁺(n)) ≤ ((k - 1) * n : ℝ) * ∑ j ∈ range ((k - 1) * n), addDiff v (n + j) ^ 2`. -/
theorem four_mul_nodal_cross_le_addDiff_sum_sq (v : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    4 * (seqPos v (k * n) * seqNeg v n + seqNeg v (k * n) * seqPos v n) ≤
      (((k - 1) * n : ℕ) : ℝ) *
        ∑ j ∈ Finset.range ((k - 1) * n), addDiff v (n + j) ^ 2 := by
  have hcross := four_mul_nodal_cross_le_mulJump_sq v k n
  have htele := mulJump_eq_sum_addDiff v hk n
  have hcs := sq_sum_le_card_mul_sum_sq (Finset.range ((k - 1) * n))
    (fun j => addDiff v (n + j))
  simp only [Finset.card_range] at hcs
  rw [htele] at hcross
  exact le_trans hcross hcs

end GaloisForLFunctions.BiScaleUncertainty
