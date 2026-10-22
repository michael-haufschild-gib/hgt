import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationSelfSimilarityOfThePronicMeasure

/-!
# The work is a correlation with the source's own window means

The pronic adjoint of the dilation by `j` is an averaging operator: pairing a row with a dilation
moves the dilation onto the other factor as a sum over the fibre of horizons that the dilation
folds together,

`⟪u, v(⌊·/j⌋)⟫_T = ⟪F_j u, v⟫_T`,  `(F_j u)(m) = m(m+1) Σ_{⌊n/j⌋ = m} u(n)/(n(n+1))`
(`pronicPairing_rowDilate_eq`),

and by the exact self-similarity of the pronic measure the operator `F_j` is `1/j` times a genuine
average: on a complete fibre it returns `c/j` for a row that is constant `c` there
(`rowFibreAverage_const`).

Consequently the dilation form — hence the signed damping work, through the prime dilation — is the
correlation of the source with its own **window means**: for each scale `j` the source is averaged
over the blocks `[jm, jm+j−1]` of horizons, and the work weighs those averages by `Λ(j) j^{-ε}`
(`rowDilationForm_eq_fibreAverage_pairing`).

That is the shape analytic methods handle: a smoothing of the source against itself, with the prime
weights on the scales.  The obstruction of the continuation layer is the sign of that smoothed
correlation, not the size of any single prefix.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The pronic adjoint of a dilation -/

/-- The pronic adjoint of the dilation by `j`, at horizon `T`: the fibre sum, renormalised by the
pronic weight of the level. -/
def rowFibreAverage (j T : ℕ) (u : ℕ → ℝ) : ℕ → ℝ := fun m =>
  ((m : ℝ) * ((m : ℝ) + 1)) *
    ∑ n ∈ (Icc 1 T).filter (fun n => n / j = m), u n / ((n : ℝ) * ((n : ℝ) + 1))

/-- **The adjoint identity.**  A dilation on one side of the pronic pairing is a fibre average on
the other. -/
theorem pronicPairing_rowDilate_eq (j T : ℕ) (u v : ℕ → ℝ) (hv0 : v 0 = 0) :
    pronicPairing T u (rowDilate j v) = pronicPairing T (rowFibreAverage j T u) v := by
  have hmaps : ∀ n ∈ Icc 1 T, n / j ∈ range (T + 1) := by
    intro n hn
    rw [mem_Icc] at hn
    rw [mem_range]
    have := Nat.div_le_self n j
    omega
  rw [pronicPairing, ← Finset.sum_fiberwise_of_maps_to hmaps
    (fun n => u n * rowDilate j v n / ((n : ℝ) * ((n : ℝ) + 1)))]
  -- the fibre over `0` contributes nothing, and each other fibre is one level of the adjoint
  have hins : (range (T + 1) : Finset ℕ) = insert 0 (Icc 1 T) := by
    ext m
    rw [mem_range, Finset.mem_insert, mem_Icc]
    omega
  rw [hins, Finset.sum_insert (by simp)]
  have hzero : (∑ n ∈ (Icc 1 T).filter (fun n => n / j = 0),
      u n * rowDilate j v n / ((n : ℝ) * ((n : ℝ) + 1))) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_filter] at hn
    rw [rowDilate, hn.2, hv0]
    ring
  rw [hzero, zero_add, pronicPairing]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  rw [rowFibreAverage, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_filter] at hn
  have hn1 : 1 ≤ n := (mem_Icc.mp hn.1).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [rowDilate, hn.2]
  field_simp

/-- **The adjoint is `1/j` times an average.**  On a complete fibre the adjoint returns the constant
value divided by the scale: the exact self-similarity of the pronic measure. -/
theorem rowFibreAverage_const {j m T : ℕ} (hj : 1 ≤ j) (hm : 1 ≤ m) (c : ℝ)
    (hfibre : (Icc 1 T).filter (fun n => n / j = m) = Icc (j * m) (j * m + j - 1)) :
    rowFibreAverage j T (fun _ => c) m = c / (j : ℝ) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [rowFibreAverage, hfibre]
  have hmass : (∑ n ∈ Icc (j * m) (j * m + j - 1), c / ((n : ℝ) * ((n : ℝ) + 1))) =
      c * (1 / ((j : ℝ) * ((m : ℝ) * ((m : ℝ) + 1)))) := by
    rw [← sum_Icc_pronic_dilation_fibre hj hm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hmass]
  field_simp

/-! ## §2. The dilation form as a correlation with window means -/

/-- **The dilation form is the correlation of the row with its own window means.** -/
theorem rowDilationForm_eq_fibreAverage_pairing (ε : ℝ) (T : ℕ) (v : ℕ → ℝ) (hv0 : v 0 = 0) :
    rowDilationForm ε T v =
      ∑ j ∈ Icc 1 T, dampedPrimeWeight ε j *
        pronicPairing T (rowFibreAverage j T v) v := by
  -- first write the form as a sum over scales of pairings with dilations
  have hext : ∀ n ∈ Icc 1 T,
      (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) =
      ∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * rowDilate j v n := by
    intro n hn
    rw [mem_Icc] at hn
    have hsub : (Icc 1 n : Finset ℕ) ⊆ Icc 1 T := by
      intro j hj
      rw [mem_Icc] at hj ⊢
      exact ⟨hj.1, hj.2.trans hn.2⟩
    rw [← Finset.sum_subset hsub]
    · exact Finset.sum_congr rfl fun j _ => by rw [rowDilate]
    · intro j hjT hjn
      rw [mem_Icc] at hjT hjn
      have hjn' : n < j := by
        by_contra hcon
        exact hjn ⟨hjT.1, by omega⟩
      rw [rowDilate, Nat.div_eq_of_lt hjn', hv0]
      ring
  have hform : rowDilationForm ε T v =
      ∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * pronicPairing T v (rowDilate j v) := by
    rw [rowDilationForm]
    have hstep : ∀ n ∈ Icc 1 T,
        v n * (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * v (n / j)) /
            ((n : ℝ) * ((n : ℝ) + 1)) =
          ∑ j ∈ Icc 1 T, dampedPrimeWeight ε j *
            (v n * rowDilate j v n / ((n : ℝ) * ((n : ℝ) + 1))) := by
      intro n hn
      rw [hext n hn, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [pronicPairing, Finset.mul_sum]
  rw [hform]
  exact Finset.sum_congr rfl fun j _ => by
    rw [pronicPairing_rowDilate_eq j T v v hv0]

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
