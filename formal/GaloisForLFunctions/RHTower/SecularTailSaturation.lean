import Mathlib

/-!
# Replacing the growth hypothesis by leakage saturation

The CCM constrained-prolate transfer controls the tail of the secular vector `v_j = ℓ_j/(d_j − μ)`
through a uniform exponential growth condition on the scale sequence,

```text
hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2) .
```

The genuine Slepian/Fuchs leakage does not satisfy it: `A_n = 4√π·8ⁿ(2π)^{n+1/2}/n!` rises to a peak
near prolate index `16π` and then decays factorially, so the required `C` diverges.  The mismatch is
one of quantifiers — Fuchs's asymptotic is valid for `n = o(c)`, while the transfer ranges over every
mode index at each aperture.

Growth is the wrong hypothesis for this job.  What actually controls the tail is **saturation**: past
the Fuchs window the prolate eigenvalues `λ_n(c)` collapse to `0`, so the leakage `d_j = 1 − λ_j`
saturates near `1` and is in particular bounded below.  With a positive floor, the tail of the
secular vector is dominated by the tail of the constraint coordinates, and that goes to zero by the
Bessel summability already available.

This module records the estimate, which needs no growth condition at all.
-/

namespace RHTower

/-- **Pointwise secular bound under a leakage floor.**  Wherever the leakage exceeds `dinf` and the
root lies below it, the secular coordinate is dominated by the constraint coordinate divided by the
gap. -/
theorem sq_secular_le_of_floor {ℓ d : ℕ → ℝ} {μ dinf : ℝ} {j : ℕ}
    (hsat : dinf ≤ d j) (hgap : μ < dinf) :
    (ℓ j / (d j - μ)) ^ 2 ≤ (ℓ j) ^ 2 / (dinf - μ) ^ 2 := by
  have hd : 0 < dinf - μ := by linarith
  have hdj : dinf - μ ≤ d j - μ := by linarith
  have hdjpos : 0 < d j - μ := lt_of_lt_of_le hd hdj
  rw [div_pow]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    (pow_le_pow_left₀ hd.le hdj 2)

/-- **Summability of the secular vector from a leakage floor.**  A positive floor on the leakage
turns Bessel summability of the constraint coordinates into summability of the secular coordinates,
with no condition on the growth of the scale sequence. -/
theorem summable_secular_of_floor {ℓ d : ℕ → ℝ} {μ dinf : ℝ}
    (hsat : ∀ j, dinf ≤ d j) (hgap : μ < dinf)
    (hsum : Summable fun j => (ℓ j) ^ 2) :
    Summable fun j => (ℓ j / (d j - μ)) ^ 2 := by
  have hd : 0 < dinf - μ := by linarith
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => sq_secular_le_of_floor (hsat j) hgap) ?_
  simpa [div_eq_mul_inv] using hsum.mul_right ((dinf - μ) ^ 2)⁻¹

/-- **The tail estimate.**  Under a leakage floor the secular tail is bounded by the constraint tail
divided by the squared gap, so it inherits the Bessel decay directly. -/
theorem tsum_secular_tail_le {ℓ d : ℕ → ℝ} {μ dinf : ℝ} (J : ℕ)
    (hsat : ∀ j, dinf ≤ d j) (hgap : μ < dinf)
    (hsum : Summable fun j => (ℓ j) ^ 2) :
    ∑' j : ℕ, (ℓ (j + J) / (d (j + J) - μ)) ^ 2
      ≤ (∑' j : ℕ, (ℓ (j + J)) ^ 2) / (dinf - μ) ^ 2 := by
  have hd : 0 < dinf - μ := by linarith
  have hshift : Summable fun j => (ℓ (j + J)) ^ 2 :=
    (summable_nat_add_iff J).mpr hsum
  have hle : ∀ j : ℕ, (ℓ (j + J) / (d (j + J) - μ)) ^ 2
      ≤ (ℓ (j + J)) ^ 2 / (dinf - μ) ^ 2 :=
    fun j => sq_secular_le_of_floor (hsat (j + J)) hgap
  have hrhs : Summable fun j : ℕ => (ℓ (j + J)) ^ 2 / (dinf - μ) ^ 2 := by
    simpa [div_eq_mul_inv] using hshift.mul_right ((dinf - μ) ^ 2)⁻¹
  calc ∑' j : ℕ, (ℓ (j + J) / (d (j + J) - μ)) ^ 2
      ≤ ∑' j : ℕ, (ℓ (j + J)) ^ 2 / (dinf - μ) ^ 2 :=
        Summable.tsum_le_tsum hle
          (Summable.of_nonneg_of_le (fun j => sq_nonneg _) hle hrhs) hrhs
    _ = (∑' j : ℕ, (ℓ (j + J)) ^ 2) / (dinf - μ) ^ 2 := by
        rw [← tsum_div_const]

end RHTower
