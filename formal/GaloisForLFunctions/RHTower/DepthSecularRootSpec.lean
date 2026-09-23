import GaloisForLFunctions.RHTower.DepthSecularConstraint

/-!
# Defining properties of the exact depth-`k` root

The depth-`k` root is defined by choice from the statement that a zero of the secular function
exists in the `k`-th gap.  So both of its defining properties — lying in the gap, and killing the
secular function — follow from that existence alone, with no need for the bracket machinery that
establishes existence in the first place.

Isolating this keeps the two concerns apart: *that* a root exists is an analytic fact about the
family, while *what* the root satisfies is definitional.
-/

open Set

noncomputable section

namespace RHTower

variable {d ℓ : ℕ → ℝ} {k : ℕ}

/-- The depth-`k` root lies in the `k`-th gap. -/
theorem depthSecularRoot_mem_Ioo
    (h : ∃ μ ∈ Ioo (d k) (d (k + 1)), depthSecular d ℓ k μ = 0) :
    depthSecularRoot d ℓ k ∈ Ioo (d k) (d (k + 1)) := by
  rw [depthSecularRoot, dif_pos h]
  exact h.choose_spec.1

/-- **The depth-`k` root kills the secular function.** -/
theorem depthSecular_depthSecularRoot_eq_zero
    (h : ∃ μ ∈ Ioo (d k) (d (k + 1)), depthSecular d ℓ k μ = 0) :
    depthSecular d ℓ k (depthSecularRoot d ℓ k) = 0 := by
  rw [depthSecularRoot, dif_pos h]
  exact h.choose_spec.2

/-- **The eigenvector at the depth-`k` root satisfies the constraint exactly.**  The existence of
the root is the only input beyond the scale floor and summability. -/
theorem tsum_mul_secularVector_depthSecularRoot_eq_zero {B : ℝ}
    (hB : ∀ j, B ≤ d (j + (k + 2))) (hsum : Summable fun j => ℓ j ^ (2 : ℕ))
    (hμB : depthSecularRoot d ℓ k < B)
    (h : ∃ μ ∈ Ioo (d k) (d (k + 1)), depthSecular d ℓ k μ = 0) :
    ∑' j : ℕ, ℓ j * secularVector d ℓ (depthSecularRoot d ℓ k) j = 0 :=
  tsum_mul_secularVector_eq_zero_of_depthSecular hB hsum hμB
    (depthSecular_depthSecularRoot_eq_zero h)

/-- **The normalized head defect at the exact depth-`k` root.**  Every hypothesis is either a
scale condition or the existence of the root; the head coordinate ordering supplies `d_0 < μ`. -/
theorem abs_sum_range_mul_secularVector_depthSecularRoot_div_le {B : ℝ}
    (hB : ∀ j, B ≤ d (j + (k + 2))) (hsum : Summable fun j => ℓ j ^ (2 : ℕ))
    (hμB : depthSecularRoot d ℓ k < B)
    (hhead : ∀ j, j ≤ k → d j ≤ d k) (hℓ0 : ℓ 0 ≠ 0)
    (h : ∃ μ ∈ Ioo (d k) (d (k + 1)), depthSecular d ℓ k μ = 0) :
    |∑ j ∈ Finset.range (k + 2),
        ℓ j * secularVector d ℓ (depthSecularRoot d ℓ k) j|
        / |secularVector d ℓ (depthSecularRoot d ℓ k) 0 * ℓ 0|
      ≤ (∑' j : ℕ, ℓ (j + (k + 2)) ^ (2 : ℕ)) * (depthSecularRoot d ℓ k - d 0)
          / ((B - depthSecularRoot d ℓ k) * ℓ 0 ^ (2 : ℕ)) := by
  have hmem := depthSecularRoot_mem_Ioo h
  have hd0 : d 0 < depthSecularRoot d ℓ k :=
    lt_of_le_of_lt (hhead 0 (Nat.zero_le k)) hmem.1
  exact abs_sum_range_mul_secularVector_div_le hB hsum hμB hd0 hℓ0
    (depthSecular_depthSecularRoot_eq_zero h)

/-! ## Discharging existence

Existence of the depth-`k` root is not an assumption to be carried: the bracket theorem proves it.
Everything above can therefore be restated with no existence hypothesis, at the cost of the
bracket's own structural inputs.
-/

/-- **Existence of the depth-`k` root, from the bracket.** -/
theorem exists_depthSecular_root
    (hk01 : d k < d (k + 1)) (hk12 : d (k + 1) < d (k + 2))
    (hkfloor : ∀ j, d (k + 2) ≤ d (j + (k + 2)))
    (hhead : ∀ j, j ≤ k → 0 ≤ d j ∧ d j ≤ d k)
    (hsum : Summable fun j => ℓ j ^ (2 : ℕ))
    (hS : flattenedCoords ℓ k 0 ≠ 0) (hℓk1 : ℓ (k + 1) ≠ 0)
    (hbr : d k < infiniteSecularRoot (flattenedScales d k 0) (flattenedCoords ℓ k)) :
    ∃ μ ∈ Ioo (d k) (d (k + 1)), depthSecular d ℓ k μ = 0 := by
  obtain ⟨hmem, hzero, _, _⟩ :=
    depthSecularRoot_bracket hk01 hk12 hkfloor hhead hsum hS hℓk1 hbr
  exact ⟨depthSecularRoot d ℓ k, hmem, hzero⟩

/-- **The normalized head defect, with existence discharged.**  No existence hypothesis remains:
the only inputs are the structural conditions of the bracket together with the scale floor. -/
theorem abs_sum_range_mul_secularVector_depthSecularRoot_div_le' {B : ℝ}
    (hk01 : d k < d (k + 1)) (hk12 : d (k + 1) < d (k + 2))
    (hkfloor : ∀ j, d (k + 2) ≤ d (j + (k + 2)))
    (hhead : ∀ j, j ≤ k → 0 ≤ d j ∧ d j ≤ d k)
    (hsum : Summable fun j => ℓ j ^ (2 : ℕ))
    (hS : flattenedCoords ℓ k 0 ≠ 0) (hℓk1 : ℓ (k + 1) ≠ 0)
    (hbr : d k < infiniteSecularRoot (flattenedScales d k 0) (flattenedCoords ℓ k))
    (hB : ∀ j, B ≤ d (j + (k + 2))) (hμB : depthSecularRoot d ℓ k < B) (hℓ0 : ℓ 0 ≠ 0) :
    |∑ j ∈ Finset.range (k + 2),
        ℓ j * secularVector d ℓ (depthSecularRoot d ℓ k) j|
        / |secularVector d ℓ (depthSecularRoot d ℓ k) 0 * ℓ 0|
      ≤ (∑' j : ℕ, ℓ (j + (k + 2)) ^ (2 : ℕ)) * (depthSecularRoot d ℓ k - d 0)
          / ((B - depthSecularRoot d ℓ k) * ℓ 0 ^ (2 : ℕ)) :=
  abs_sum_range_mul_secularVector_depthSecularRoot_div_le hB hsum hμB
    (fun j hj => (hhead j hj).2) hℓ0
    (exists_depthSecular_root hk01 hk12 hkfloor hhead hsum hS hℓk1 hbr)

end RHTower

end
