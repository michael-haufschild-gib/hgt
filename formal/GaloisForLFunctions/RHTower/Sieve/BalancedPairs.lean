import GaloisForLFunctions.RHTower.Sieve.MoebiusSignCount
import GaloisForLFunctions.RHTower.Sieve.SignSplitLimit

/-!
# Balanced pairs and their sign classes

The card counts ordered pairs `(n₁, n₂)` with

    x ≤ n₁n₂ ≤ x + h√x,   √x ≤ n₁ ≤ 2√x.

Over such pairs the two weights `μ(n₁)μ(n₂)` and `μ²(n₁)μ²(n₂)` are the difference and the sum of
the two sign-class indicators, so

    ∑ μ(n₁)μ(n₂) = R₊ - R₋,    ∑ μ²(n₁)μ²(n₂) = R₊ + R₋.

These are exact Finset identities, valid for every `x` and `h`; combined with the two limits they
give the card's `(7)`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The balanced pair set: `x ≤ n₁n₂ ≤ x + h√x` and `√x ≤ n₁ ≤ 2√x`. -/
noncomputable def balancedPairs (x h : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊) ×ˢ (Finset.Icc 1 ⌊x + h * Real.sqrt x⌋₊)).filter
    (fun q => x ≤ ((q.1 * q.2 : ℕ) : ℝ)
      ∧ ((q.1 * q.2 : ℕ) : ℝ) ≤ x + h * Real.sqrt x
      ∧ Real.sqrt x ≤ (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * Real.sqrt x)

/-- The signed balanced-pair sum. -/
noncomputable def signedPairSum (x h : ℝ) : ℝ :=
  ∑ q ∈ balancedPairs x h, ((moebius q.1 : ℤ) : ℝ) * ((moebius q.2 : ℤ) : ℝ)

/-- The squarefree balanced-pair count. -/
noncomputable def squarefreePairCount (x h : ℝ) : ℝ :=
  ∑ q ∈ balancedPairs x h,
    ((moebius q.1 : ℤ) : ℝ) ^ 2 * ((moebius q.2 : ℤ) : ℝ) ^ 2

/-- The balanced pairs of a given product sign. -/
noncomputable def signClass (x h : ℝ) (ε : ℤ) : Finset (ℕ × ℕ) :=
  (balancedPairs x h).filter (fun q => moebius q.1 * moebius q.2 = ε)

/-- The size of a sign class. -/
noncomputable def signClassCount (x h : ℝ) (ε : ℤ) : ℝ := ((signClass x h ε).card : ℝ)

/-- The pointwise product of two Möbius values is `0`, `1` or `-1`. -/
theorem moebius_pair_trichotomy (a b : ℕ) :
    moebius a * moebius b = 0 ∨ moebius a * moebius b = 1 ∨ moebius a * moebius b = -1 := by
  rcases moebius_trichotomy a with ha | ha | ha <;> rcases moebius_trichotomy b with hb | hb | hb <;>
    rw [ha, hb] <;> norm_num

/-- The signed weight is the difference of the two sign indicators. -/
theorem moebius_pair_eq_sub (a b : ℕ) :
    ((moebius a : ℤ) : ℝ) * ((moebius b : ℤ) : ℝ)
      = (if moebius a * moebius b = 1 then (1 : ℝ) else 0)
        - (if moebius a * moebius b = -1 then (1 : ℝ) else 0) := by
  rcases moebius_pair_trichotomy a b with h | h | h <;>
    rw [show ((moebius a : ℤ) : ℝ) * ((moebius b : ℤ) : ℝ)
        = ((moebius a * moebius b : ℤ) : ℝ) by push_cast; ring, h] <;>
    norm_num

/-- The squarefree weight is the sum of the two sign indicators. -/
theorem moebius_pair_sq_eq_add (a b : ℕ) :
    ((moebius a : ℤ) : ℝ) ^ 2 * ((moebius b : ℤ) : ℝ) ^ 2
      = (if moebius a * moebius b = 1 then (1 : ℝ) else 0)
        + (if moebius a * moebius b = -1 then (1 : ℝ) else 0) := by
  have hsq : ((moebius a : ℤ) : ℝ) ^ 2 * ((moebius b : ℤ) : ℝ) ^ 2
      = ((moebius a * moebius b : ℤ) : ℝ) ^ 2 := by push_cast; ring
  rcases moebius_pair_trichotomy a b with h | h | h <;> rw [hsq, h] <;> norm_num

/-- **The signed sum is the difference of the sign-class counts.** -/
theorem signedPairSum_eq (x h : ℝ) :
    signedPairSum x h = signClassCount x h 1 - signClassCount x h (-1) := by
  classical
  rw [signedPairSum, signClassCount, signClassCount, signClass, signClass]
  rw [Finset.sum_congr rfl (fun q _ => moebius_pair_eq_sub q.1 q.2)]
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one]

/-- **The squarefree count is the sum of the sign-class counts.** -/
theorem squarefreePairCount_eq (x h : ℝ) :
    squarefreePairCount x h = signClassCount x h 1 + signClassCount x h (-1) := by
  classical
  rw [squarefreePairCount, signClassCount, signClassCount, signClass, signClass]
  rw [Finset.sum_congr rfl (fun q _ => moebius_pair_sq_eq_add q.1 q.2)]
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one]

/-- **Card equation (7).**  If the squarefree pair count has a limiting density and the signed pair
sum vanishes, both sign classes have half the density. -/
theorem tendsto_signClass_of_limits {hh N : ℝ → ℝ} {q : ℝ}
    (hQ : Filter.Tendsto (fun x => squarefreePairCount x (hh x) / N x) Filter.atTop (nhds q))
    (hS : Filter.Tendsto (fun x => signedPairSum x (hh x) / N x) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun x => signClassCount x (hh x) 1 / N x) Filter.atTop (nhds (q / 2))
      ∧ Filter.Tendsto (fun x => signClassCount x (hh x) (-1) / N x)
        Filter.atTop (nhds (q / 2)) := by
  refine tendsto_sign_classes (Rp := fun x => signClassCount x (hh x) 1)
    (Rm := fun x => signClassCount x (hh x) (-1))
    (Q := fun x => squarefreePairCount x (hh x))
    (S := fun x => signedPairSum x (hh x)) (N := N) ?_ ?_ hQ hS
  · intro x
    exact (squarefreePairCount_eq x (hh x)).symm
  · intro x
    exact (signedPairSum_eq x (hh x)).symm

end RHTower.Sieve
