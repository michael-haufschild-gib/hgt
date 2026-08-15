import GaloisForLFunctions.RHTower.XiShiftedHardEdgeHalfCosineParseval

/-!
# The half-density factor shifts every frequency by one half

Multiplying a cosine polynomial by the half-density factor `cos(θ/2)` produces a cosine polynomial
in the half-integer frequencies, with the same degree bound:

`cos(θ/2)·∑_{j ≤ N} b_j cos(jθ) = ∑_{m ≤ N} c_m cos((m + 1/2)θ)`,

`c_m = b_m/2 + [m = 0]·b_0/2 + b_{m+1}/2`.

The product-to-sum identity is uniform in `j` — at `j = 0` the two half-frequencies coincide by
evenness — so the reindexing is a single shift of the summation range.  This is the identity that
puts the rational hard-edge test in the frame where the `L²` Bernstein inequality applies.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower

/-- Truncation of a coefficient family beyond the degree. -/
def truncCoeff (N : ℕ) (b : ℕ → ℝ) (j : ℕ) : ℝ := if j ≤ N then b j else 0

theorem truncCoeff_of_le {N : ℕ} (b : ℕ → ℝ) {j : ℕ} (hj : j ≤ N) :
    truncCoeff N b j = b j := if_pos hj

theorem truncCoeff_succ_self (N : ℕ) (b : ℕ → ℝ) : truncCoeff N b (N + 1) = 0 :=
  if_neg (by omega)

theorem cosPoly_truncCoeff (N : ℕ) (b : ℕ → ℝ) (θ : ℝ) :
    cosPoly N (truncCoeff N b) θ = cosPoly N b θ := by
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  rw [truncCoeff_of_le b (by omega)]

/-- The half-shifted coefficient family. -/
def halfShiftCoeff (N : ℕ) (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  truncCoeff N b m / 2 + (if m = 0 then truncCoeff N b 0 / 2 else 0)
    + truncCoeff N b (m + 1) / 2

/-- The uniform product-to-sum identity for the half-density factor. -/
theorem cos_half_mul_cos_nat (j : ℕ) (θ : ℝ) :
    Real.cos (θ / 2) * Real.cos ((j : ℝ) * θ)
      = (Real.cos (((j : ℝ) + 1 / 2) * θ) + Real.cos (((j : ℝ) - 1 / 2) * θ)) / 2 := by
  have hsum : ((j : ℝ) + 1 / 2) * θ = θ / 2 + (j : ℝ) * θ := by ring
  have hdiff : ((j : ℝ) - 1 / 2) * θ = -(θ / 2 - (j : ℝ) * θ) := by ring
  rw [hsum, hdiff, Real.cos_neg, Real.cos_add, Real.cos_sub]
  ring

/-- **The half-density shift.**  Multiplying a cosine polynomial by `cos(θ/2)` gives a half-integer
cosine polynomial of the same degree. -/
theorem cos_half_mul_cosPoly (N : ℕ) (b : ℕ → ℝ) (θ : ℝ) :
    Real.cos (θ / 2) * cosPoly N b θ = halfCosPoly N (halfShiftCoeff N b) θ := by
  rw [← cosPoly_truncCoeff N b θ]
  obtain ⟨t, htdef⟩ : ∃ t : ℕ → ℝ, t = truncCoeff N b := ⟨_, rfl⟩
  have hshift : halfShiftCoeff N b
      = fun m => t m / 2 + (if m = 0 then t 0 / 2 else 0) + t (m + 1) / 2 := by
    funext m
    rw [halfShiftCoeff, htdef]
  rw [← htdef, hshift, cosPoly, halfCosPoly, Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.range (N + 1),
      Real.cos (θ / 2) * (t j * Real.cos ((j : ℝ) * θ))
        = t j / 2 * Real.cos (((j : ℝ) + 1 / 2) * θ)
          + t j / 2 * Real.cos (((j : ℝ) - 1 / 2) * θ) := by
    intro j _
    rw [show Real.cos (θ / 2) * (t j * Real.cos ((j : ℝ) * θ))
        = t j * (Real.cos (θ / 2) * Real.cos ((j : ℝ) * θ)) by ring, cos_half_mul_cos_nat]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  -- the lowered family, reindexed
  have hlow : ∑ j ∈ Finset.range (N + 1), t j / 2 * Real.cos (((j : ℝ) - 1 / 2) * θ)
      = (t 0 / 2) * Real.cos (((0 : ℕ) + 1 / 2 : ℝ) * θ)
        + ∑ i ∈ Finset.range (N + 1), t (i + 1) / 2 * Real.cos (((i : ℝ) + 1 / 2) * θ) := by
    rw [Finset.sum_range_succ' (fun j => t j / 2 * Real.cos (((j : ℝ) - 1 / 2) * θ)) N]
    have hzero : t 0 / 2 * Real.cos ((((0 : ℕ) : ℝ) - 1 / 2) * θ)
        = (t 0 / 2) * Real.cos (((0 : ℕ) + 1 / 2 : ℝ) * θ) := by
      have hneg : (((0 : ℕ) : ℝ) - 1 / 2) * θ = -((((0 : ℕ) : ℝ) + 1 / 2) * θ) := by
        push_cast
        ring
      rw [hneg, Real.cos_neg]
    have hzeroN : t (N + 1) = 0 := by
      rw [htdef]
      exact truncCoeff_succ_self N b
    have htail : ∑ i ∈ Finset.range N,
        t (i + 1) / 2 * Real.cos (((((i + 1 : ℕ)) : ℝ) - 1 / 2) * θ)
        = ∑ i ∈ Finset.range (N + 1), t (i + 1) / 2 * Real.cos (((i : ℝ) + 1 / 2) * θ) := by
      rw [Finset.sum_range_succ, hzeroN]
      simp only [zero_div, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      push_cast
      ring
    rw [hzero, htail]
    ring
  rw [hlow]
  have hsingle : (t 0 / 2) * Real.cos (((0 : ℕ) + 1 / 2 : ℝ) * θ)
      = ∑ m ∈ Finset.range (N + 1),
        (if m = 0 then t 0 / 2 else 0) * Real.cos (((m : ℝ) + 1 / 2) * θ) := by
    have h := Finset.sum_eq_single (M := ℝ) (s := Finset.range (N + 1)) (a := 0)
      (f := fun m => (if m = 0 then t 0 / 2 else 0) * Real.cos (((m : ℝ) + 1 / 2) * θ))
      (fun m _ hm => by rw [if_neg hm, zero_mul])
      (fun hnot => absurd (Finset.mem_range.2 (by omega)) hnot)
    rw [h]
    norm_num
  rw [hsingle]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

end RHTower

end
