import GaloisForLFunctions.RHTower.Sieve.GhsPerronSum
import GaloisForLFunctions.RHTower.Sieve.HalaszUniformDistance
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError

/-!
# The Perron step with the damped third factor

The size of the third factor on the range of integration is the one place where the arithmetic of the
multiplicative function can pay.  Under a uniform lower bound `δ` for the multiplicative distance of `f`
from every character `n^{it}`, `|t| ≤ T`, the corpus's damped estimate gives

`‖L(f, σ+it)‖ ≤ (1 + 1/(σ−1))·exp(7/2 + 2(σ−1)(log z + log 4) − δ²)`,

and truncating `f` at `L` costs the tail `L^{1−σ}/(σ−1)`.  Both terms carry the same factor `1/(σ−1)`, so
at `σ = 1 + (δ² + 1)/log L` they are of the same order and the saving `e^{−δ²}` survives the truncation.

Substituted into the Perron step of the recursion, this is the first place in the chain where the bound
falls below the trivial size: everything else — the sieve mean squares, the kernel, the dyadic split, the
truncation error — is unchanged.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The damped size of a truncated multiplicative Dirichlet series on a line: the damped Euler bound at
distance `δ` from the characters up to `z`, plus the truncation tail at `L`. -/
def dampedSize (σ δ : ℝ) (z L : ℕ) : ℝ :=
  (1 + 1 / (σ - 1)) * Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2)
    + ((L : ℝ)) ^ (1 - σ) / (σ - 1)

theorem dampedSize_nonneg {σ δ : ℝ} (hσ : 1 < σ) (z L : ℕ) : 0 ≤ dampedSize σ δ z L := by
  rw [dampedSize]
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  have h1 : (0 : ℝ) ≤ ((L : ℝ)) ^ (1 - σ) := Real.rpow_nonneg (Nat.cast_nonneg L) _
  have h2 : (0 : ℝ) ≤ 1 + 1 / (σ - 1) := by positivity
  positivity

/-- A truncated Dirichlet series is the partial sum of the twisted summands. -/
theorem LSeries_truncSeq_eq_sum_range {f : ℕ → ℂ} {L : ℕ} {s : ℂ} (hs : s ≠ 0) :
    LSeries (truncSeq f L) s = ∑ n ∈ Finset.range (L + 1), twistedSummand f s n := by
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 L := by simp
  rw [← sum_mul_cpow_neg_eq_LSeries (s := Finset.Icc 1 L) hs0
    (fun n hn => truncSeq_support hn)]
  have hrange : Finset.range (L + 1) = insert 0 (Finset.Icc 1 L) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hrange, Finset.sum_insert hs0]
  have hzero : twistedSummand f s 0 = 0 := by
    rw [twistedSummand, Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.2 hs), mul_zero]
  rw [hzero, zero_add]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [twistedSummand, truncSeq, if_pos hn]

/-- **The damped size of the truncated third factor.**  Under a uniform distance lower bound on the range,
the truncated series is at most the damped size plus the truncation tail. -/
theorem norm_LSeries_truncSeq_line_le_damped {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 1 ≤ z) {δ : ℝ} (hδ : 0 ≤ δ) {T : ℝ}
    (hunif : ∀ t : ℝ, |t| ≤ T →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)))
    {L : ℕ} (hL : 1 ≤ L) {t : ℝ} (ht : |t| ≤ T) :
    ‖LSeries (truncSeq f L) ((σ : ℂ) + (t : ℝ) * I)‖ ≤ dampedSize σ δ z L := by
  rw [dampedSize]
  have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
  have hs : ((σ : ℂ) + (t : ℝ) * I) ≠ 0 := by
    intro h
    rw [h] at hre
    simp only [Complex.zero_re] at hre
    exact absurd hre.symm (by linarith : σ ≠ 0)
  have hdamp := norm_tsum_twistedSummand_le_damped_of_uniform hf1 hmul hbdd hσ hz hδ hunif ht
  have htail := norm_tsum_sub_sum_range_le_pow (f := f) hbdd
    (s := (σ : ℂ) + (t : ℝ) * I) (by rw [hre]; exact hσ) hL
  rw [hre] at htail
  rw [LSeries_truncSeq_eq_sum_range hs]
  have hsplit : (∑ n ∈ Finset.range (L + 1), twistedSummand f ((σ : ℂ) + (t : ℝ) * I) n)
      = (∑' n : ℕ, twistedSummand f ((σ : ℂ) + (t : ℝ) * I) n)
        - ((∑' n : ℕ, twistedSummand f ((σ : ℂ) + (t : ℝ) * I) n)
            - ∑ n ∈ Finset.range (L + 1), twistedSummand f ((σ : ℂ) + (t : ℝ) * I) n) := by
    ring
  rw [hsplit]
  refine le_trans (norm_sub_le _ _) (add_le_add ?_ htail)
  exact hdamp

/-- **The Perron step of the recursion with the damped third factor.**  The `e^{−δ²}` saving of the
distance bound, carried through the Perron step unchanged. -/
theorem norm_sum_Icc_ghsTriple_damped_le {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {N₀ M L N : ℕ} (hprod : 1 ≤ N₀ * (M * L)) (hN : 1 ≤ N) (hL : 1 ≤ L)
    {σ t₀ δ : ℝ} (hσ : 1 < σ) (ht₀ : 1 ≤ t₀) (hδ : 0 ≤ δ) {z : ℕ} (hz : 1 ≤ z) (K : ℕ)
    (hunif : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)))
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) :
    ‖∑ n ∈ Finset.Icc 1 (min (N₀ * (M * L)) N),
        (LSeries.convolution (ghsOuter f N₀)
          (LSeries.convolution (ghsInner f M) (truncSeq f L))) n‖
      ≤ 2 * ((N : ℝ) + 1) * ((Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
              * (((N : ℝ) + 1 / 2)) ^ σ
              * (1 + Real.log ((N₀ * (M * L) : ℕ) : ℝ)) / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalProductBound (ghsOuter f N₀) (ghsInner f M)
                    (Finset.Icc 1 N₀) (Finset.Icc 1 M) σ ((N : ℝ) + 1 / 2) t₀
                    (dampedSize σ δ z L) zA YA zB YB K
                  + ((dampedSize σ δ z L) * ((N : ℝ) + 1 / 2) ^ σ / σ)
                      * (Real.sqrt (sieveMeanSquareConst (ghsOuter f N₀) (Finset.Icc 1 N₀) σ YA
                            + sieveMeanSquareRate (ghsOuter f N₀) (Finset.Icc 1 N₀) σ zA YA * t₀)
                          * Real.sqrt (sieveMeanSquareConst (ghsInner f M) (Finset.Icc 1 M) σ YB
                            + sieveMeanSquareRate (ghsInner f M) (Finset.Icc 1 M) σ zB YB
                                * t₀))) := by
  exact norm_sum_Icc_ghsTriple_of_bound_le hbdd hprod hN (dampedSize_nonneg hσ z L) hσ.le ht₀
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K
    (fun t ht => norm_LSeries_truncSeq_line_le_damped hf1 hmul hbdd hσ hz hδ hunif hL ht)

/-- **The Perron step of the recursion with the damped third factor at the near-diagonal truncation
error.**  The `e^{−δ²}` saving, carried through a truncation error whose only dependence on the length
of the sum is logarithmic. -/
theorem norm_sum_Icc_ghsTriple_damped_near_le {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {N₀ M L N : ℕ} (hprod : 1 ≤ N₀ * (M * L)) (hL : 1 ≤ L)
    {σ t₀ δ : ℝ} (hσ : 1 < σ) (ht₀ : 1 ≤ t₀) (hδ : 0 ≤ δ) {z : ℕ} (hz : 1 ≤ z) (K : ℕ)
    (hunif : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)))
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) :
    ‖∑ n ∈ Finset.Icc 1 (min (N₀ * (M * L)) N),
        (LSeries.convolution (ghsOuter f N₀)
          (LSeries.convolution (ghsInner f M) (truncSeq f L))) n‖
      ≤ ((Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
              * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((N₀ * (M * L) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalProductBound (ghsOuter f N₀) (ghsInner f M)
                    (Finset.Icc 1 N₀) (Finset.Icc 1 M) σ ((N : ℝ) + 1 / 2) t₀
                    (dampedSize σ δ z L) zA YA zB YB K
                  + ((dampedSize σ δ z L) * ((N : ℝ) + 1 / 2) ^ σ / σ)
                      * (Real.sqrt (sieveMeanSquareConst (ghsOuter f N₀) (Finset.Icc 1 N₀) σ YA
                            + sieveMeanSquareRate (ghsOuter f N₀) (Finset.Icc 1 N₀) σ zA YA * t₀)
                          * Real.sqrt (sieveMeanSquareConst (ghsInner f M) (Finset.Icc 1 M) σ YB
                            + sieveMeanSquareRate (ghsInner f M) (Finset.Icc 1 M) σ zB YB
                                * t₀))) :=
  norm_sum_Icc_ghsTriple_of_bound_near_le hbdd hprod (dampedSize_nonneg hσ z L) hσ.le ht₀
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K
    (fun _ ht => norm_LSeries_truncSeq_line_le_damped hf1 hmul hbdd hσ hz hδ hunif hL ht)

/-- **The Perron step of the recursion with the damped third factor, at per-block sieve levels and the
near-diagonal truncation error.**  All three improvements at once: the sieve level grows with the block,
the truncation error is free of its factor `N`, and the distance saving `e^{−δ²}` enters through
`dampedSize`. -/
theorem norm_sum_Icc_ghsTriple_damped_block_near_le {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n) (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {N₀ M L N : ℕ} (hprod : 1 ≤ N₀ * (M * L)) (hL : 1 ≤ L)
    {σ t₀ δ : ℝ} (hσ : 1 < σ) (ht₀ : 1 ≤ t₀) (hδ : 0 ≤ δ) {z : ℕ} (hz : 1 ≤ z) (K : ℕ)
    (hunif : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)))
    (ZA YlA ZB YlB : ℕ → ℕ)
    (hYA : ∀ j, 1 ≤ YlA j) (hYzA : ∀ j, YlA j ≤ ZA j) (hzA : ∀ j, 2 ≤ ZA j)
    (hlogA : ∀ j, 0 < Real.log (YlA j))
    (hYB : ∀ j, 1 ≤ YlB j) (hYzB : ∀ j, YlB j ≤ ZB j) (hzB : ∀ j, 2 ≤ ZB j)
    (hlogB : ∀ j, 0 < Real.log (YlB j)) :
    ‖∑ n ∈ Finset.Icc 1 (min (N₀ * (M * L)) N),
        (LSeries.convolution (ghsOuter f N₀)
          (LSeries.convolution (ghsInner f M) (truncSeq f L))) n‖
      ≤ ((Real.log ((N₀ * (M * L) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
              * (((N : ℝ) + 1 / 2)) ^ σ
              * (5 * (1 + Real.log ((N₀ * (M * L) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
              / (Real.pi * (t₀ * 2 ^ K))
          + (1 / (2 * Real.pi))
              * (2 * perronVerticalAffineProductBound σ ((N : ℝ) + 1 / 2) t₀
                    (dampedSize σ δ z L)
                    (blockAffineConst (ghsOuter f N₀) N₀ σ ZA YlA)
                    (blockAffineRate (ghsOuter f N₀) N₀ σ ZA YlA)
                    (blockAffineConst (ghsInner f M) M σ ZB YlB)
                    (blockAffineRate (ghsInner f M) M σ ZB YlB) K
                  + ((dampedSize σ δ z L) * ((N : ℝ) + 1 / 2) ^ σ / σ)
                      * (Real.sqrt (blockAffineConst (ghsOuter f N₀) N₀ σ ZA YlA
                            + blockAffineRate (ghsOuter f N₀) N₀ σ ZA YlA * t₀)
                          * Real.sqrt (blockAffineConst (ghsInner f M) M σ ZB YlB
                            + blockAffineRate (ghsInner f M) M σ ZB YlB * t₀))) :=
  norm_sum_Icc_ghsTriple_of_bound_block_near_le hbdd hprod (dampedSize_nonneg hσ z L) hσ.le ht₀
    ZA YlA ZB YlB hYA hYzA hzA hlogA hYB hYzB hzB hlogB K
    (fun _ ht => norm_LSeries_truncSeq_line_le_damped hf1 hmul hbdd hσ hz hδ hunif hL ht)

end RHTower.Sieve
end
