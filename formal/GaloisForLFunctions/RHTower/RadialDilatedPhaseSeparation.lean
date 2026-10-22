import GaloisForLFunctions.RHTower.CCM.CCMFirstRowStationaryPhase

/-!
# Two-index separation of the dilated radial phase speeds

The exterior radial phase of the prolate comparison equation, dilated by an index `r`, has speed

```text
d/dx ξ_s(r x) = r · √((r²x² − s)/(r²x² − 1)) .
```

For two indices `j ≥ k ≥ 2` and every radius `x ≥ 1` the two speeds separate by a fixed positive
multiple of the index gap, and their sum is at least the sum of the indices.  Neither statement needs
a derivative in the index: the squared speed is

```text
r² + (1 − s) r²/(r²x² − 1) ,
```

whose second term is decreasing in `r` and whose two-index difference is at most `(j² − k²)/9`,
because both factors of the denominator are at least `3`.  So the difference of squares is at least
`(8/9)(j² − k²)`, while the sum of speeds is at most `(4/3)(j + k)`; dividing gives the gap
`(2/3)(j − k)`.

This is the nonstationarity that makes an off-diagonal radial Gram entry `O(1/(c|j − k|))`: once
both indices are at least two, the difference phase never becomes stationary.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.RHTower

theorem four_le_sq_mul_sq {r x : ℝ} (hr : 2 ≤ r) (hx : 1 ≤ x) : (4 : ℝ) ≤ r ^ (2 : ℕ) * x ^ (2 : ℕ) := by
  have h1 : (4 : ℝ) ≤ r ^ (2 : ℕ) := by nlinarith
  have h2 : (1 : ℝ) ≤ x ^ (2 : ℕ) := by nlinarith
  nlinarith

/-- The speed of the radial phase dilated by the index `r`. -/
def dilatedPhaseSpeed (s r x : ℝ) : ℝ := r * xiSpeed s (r * x)

theorem dilatedPhaseSpeed_eq (s r x : ℝ) :
    dilatedPhaseSpeed s r x = r * Real.sqrt ((r ^ (2 : ℕ) * x ^ (2 : ℕ) - s) / (r ^ (2 : ℕ) * x ^ (2 : ℕ) - 1)) := by
  rw [dilatedPhaseSpeed, xiSpeed_mul]

/-- On the admissible range the dilated speed is at least the index. -/
theorem le_dilatedPhaseSpeed {s r x : ℝ} (hs1 : s ≤ 1 / 2)
    (hr : 2 ≤ r) (hx : 1 ≤ x) :
    r ≤ dilatedPhaseSpeed s r x := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  have hu2 : (4 : ℝ) ≤ r ^ (2 : ℕ) * x ^ (2 : ℕ) := four_le_sq_mul_sq hr hx
  have hden : (0 : ℝ) < r ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := by linarith
  have hratio : (1 : ℝ) ≤ (r ^ (2 : ℕ) * x ^ (2 : ℕ) - s) / (r ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) := by
    rw [le_div_iff₀ hden]
    linarith
  have hsqrt : (1 : ℝ) ≤ Real.sqrt ((r ^ (2 : ℕ) * x ^ (2 : ℕ) - s) / (r ^ (2 : ℕ) * x ^ (2 : ℕ) - 1)) := by
    have h := Real.sqrt_le_sqrt hratio
    rwa [Real.sqrt_one] at h
  rw [dilatedPhaseSpeed_eq]
  nlinarith

/-- On the admissible range the dilated speed is at most `4/3` times the index. -/
theorem dilatedPhaseSpeed_le {s r x : ℝ} (hs : 0 ≤ s)
    (hr : 2 ≤ r) (hx : 1 ≤ x) :
    dilatedPhaseSpeed s r x ≤ 4 / 3 * r := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  have hu2 : (4 : ℝ) ≤ r ^ (2 : ℕ) * x ^ (2 : ℕ) := four_le_sq_mul_sq hr hx
  have hden : (0 : ℝ) < r ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := by linarith
  have hratio : (r ^ (2 : ℕ) * x ^ (2 : ℕ) - s) / (r ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) ≤ (4 / 3 : ℝ) ^ (2 : ℕ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hbound : Real.sqrt ((r ^ (2 : ℕ) * x ^ (2 : ℕ) - s) / (r ^ (2 : ℕ) * x ^ (2 : ℕ) - 1)) ≤ 4 / 3 := by
    have h := Real.sqrt_le_sqrt hratio
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (4:ℝ)/3)] at h
  rw [dilatedPhaseSpeed_eq]
  nlinarith [Real.sqrt_nonneg ((r ^ (2 : ℕ) * x ^ (2 : ℕ) - s) / (r ^ (2 : ℕ) * x ^ (2 : ℕ) - 1))]

/-- The squared dilated speed, in the form that exposes its monotonicity in the index. -/
theorem dilatedPhaseSpeed_sq {s r x : ℝ} (hs1 : s ≤ 1 / 2)
    (hr : 2 ≤ r) (hx : 1 ≤ x) :
    dilatedPhaseSpeed s r x ^ (2 : ℕ) = r ^ (2 : ℕ) + (1 - s) * r ^ (2 : ℕ) / (r ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  have hu2 : (4 : ℝ) ≤ r ^ (2 : ℕ) * x ^ (2 : ℕ) := four_le_sq_mul_sq hr hx
  have hden : (0 : ℝ) < r ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := by linarith
  have hnum : (0 : ℝ) ≤ (r ^ (2 : ℕ) * x ^ (2 : ℕ) - s) / (r ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) := by
    apply div_nonneg _ hden.le
    linarith
  rw [dilatedPhaseSpeed_eq, mul_pow, Real.sq_sqrt hnum]
  field_simp
  ring

/-- **Two-index phase separation.**  For indices at least two the dilated speeds separate by a fixed
positive multiple of the index gap, uniformly in the radius and the turning parameter. -/
theorem sub_dilatedPhaseSpeed_ge {s j k x : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hk : 2 ≤ k) (hjk : k ≤ j) (hx : 1 ≤ x) :
    2 / 3 * (j - k) ≤ dilatedPhaseSpeed s j x - dilatedPhaseSpeed s k x := by
  have hj : (2 : ℝ) ≤ j := le_trans hk hjk
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (by norm_num) hk
  have hj0 : (0 : ℝ) < j := lt_of_lt_of_le (by norm_num) hj
  have huk : (4 : ℝ) ≤ k ^ (2 : ℕ) * x ^ (2 : ℕ) := four_le_sq_mul_sq hk hx
  have huj : (4 : ℝ) ≤ j ^ (2 : ℕ) * x ^ (2 : ℕ) := four_le_sq_mul_sq hj hx
  have hkden : (0 : ℝ) < k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := by linarith
  have hjden : (0 : ℝ) < j ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := by linarith
  have hjk2 : (0 : ℝ) ≤ j ^ (2 : ℕ) - k ^ (2 : ℕ) := by nlinarith
  have hsqj := dilatedPhaseSpeed_sq (s := s) hs1 hj hx
  have hsqk := dilatedPhaseSpeed_sq (s := s) hs1 hk hx
  -- the two-index difference of the correction terms
  have hkey : (1 - s) * k ^ (2 : ℕ) / (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) - (1 - s) * j ^ (2 : ℕ) / (j ^ (2 : ℕ) * x ^ (2 : ℕ) - 1)
      = (1 - s) * (j ^ (2 : ℕ) - k ^ (2 : ℕ)) / ((k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (j ^ (2 : ℕ) * x ^ (2 : ℕ) - 1)) := by
    rw [div_sub_div _ _ hkden.ne' hjden.ne']
    congr 1
    ring
  have h3k : (3 : ℝ) ≤ k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := by linarith
  have h3j : (3 : ℝ) ≤ j ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := by linarith
  have hprod : (9 : ℝ) ≤ (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (j ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) := by nlinarith [h3k, h3j]
  have hcorr : (1 - s) * k ^ (2 : ℕ) / (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) - (1 - s) * j ^ (2 : ℕ) / (j ^ (2 : ℕ) * x ^ (2 : ℕ) - 1)
      ≤ 1 / 9 * (j ^ (2 : ℕ) - k ^ (2 : ℕ)) := by
    rw [hkey, div_le_iff₀ (by positivity : (0:ℝ) < (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) * (j ^ (2 : ℕ) * x ^ (2 : ℕ) - 1))]
    nlinarith [hprod, hjk2]
  have hdiffsq : 8 / 9 * (j ^ (2 : ℕ) - k ^ (2 : ℕ))
      ≤ dilatedPhaseSpeed s j x ^ (2 : ℕ) - dilatedPhaseSpeed s k x ^ (2 : ℕ) := by
    rw [hsqj, hsqk]
    linarith
  have hsumle : dilatedPhaseSpeed s j x + dilatedPhaseSpeed s k x ≤ 4 / 3 * (j + k) := by
    have h1 := dilatedPhaseSpeed_le (s := s) hs hj hx
    have h2 := dilatedPhaseSpeed_le (s := s) hs hk hx
    linarith
  have hjpos := le_dilatedPhaseSpeed (s := s) hs1 hj hx
  have hkpos := le_dilatedPhaseSpeed (s := s) hs1 hk hx
  have hsumpos : (0 : ℝ) < dilatedPhaseSpeed s j x + dilatedPhaseSpeed s k x := by linarith
  have hfactor : dilatedPhaseSpeed s j x ^ (2 : ℕ) - dilatedPhaseSpeed s k x ^ (2 : ℕ)
      = (dilatedPhaseSpeed s j x - dilatedPhaseSpeed s k x)
        * (dilatedPhaseSpeed s j x + dilatedPhaseSpeed s k x) := by ring
  have hsq : (8 : ℝ) / 9 * (j ^ (2 : ℕ) - k ^ (2 : ℕ))
      ≤ (dilatedPhaseSpeed s j x - dilatedPhaseSpeed s k x)
        * (dilatedPhaseSpeed s j x + dilatedPhaseSpeed s k x) := by
    rw [← hfactor]; exact hdiffsq
  have hD0 : (0 : ℝ) ≤ dilatedPhaseSpeed s j x - dilatedPhaseSpeed s k x := by
    nlinarith [hsq, hsumpos, hjk2]
  have hjkpos : (0 : ℝ) < j + k := by linarith
  have hstep : 8 / 9 * ((j - k) * (j + k))
      ≤ 4 / 3 * (dilatedPhaseSpeed s j x - dilatedPhaseSpeed s k x) * (j + k) := by
    nlinarith [hsq, hsumle, hD0]
  nlinarith [hstep, hjkpos]

/-- The sum of two dilated speeds is at least the sum of the indices, so the sum phase is also
nonstationary. -/
theorem le_add_dilatedPhaseSpeed {s j k x : ℝ} (hs1 : s ≤ 1 / 2)
    (hk : 2 ≤ k) (hj : 2 ≤ j) (hx : 1 ≤ x) :
    j + k ≤ dilatedPhaseSpeed s j x + dilatedPhaseSpeed s k x := by
  have h1 := le_dilatedPhaseSpeed (s := s) hs1 hj hx
  have h2 := le_dilatedPhaseSpeed (s := s) hs1 hk hx
  linarith

end GaloisForLFunctions.RHTower

end
