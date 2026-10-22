import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovLcmExpansion
import GaloisForLFunctions.RHTower.Sieve.MoebiusScaledReindex

/-!
# Rescaling the long Barban–Vehov lcm kernels

The long lcm kernels sum over multiples `k ∈ (L, U]` of `e = lcm(q, r)`. Writing `k = e j` with
`j ∈ (⌊L/e⌋, ⌊U/e⌋]` turns each kernel into `1/e` times a harmonic sum over `j`, with logarithms
`log(k/r) = log(e/r) + log j` and `log(k/q) = log(e/q) + log j` split accordingly.

## Main results

- `sum_filter_dvd_Ioc_eq_sum_scaled`: a sum over multiples of `e` in `(L, U]` equals the sum over
  `j ∈ (⌊L/e⌋, ⌊U/e⌋]` of the values at `e j`.
- `log_lcmMul_natDiv_eq_add_log`: `log(lcm(q, r) j / r) = log(lcm(q, r) / r) + log j`.
- `barbanVehovLongHarmonicKernel_eq_scaled`: the harmonic kernel equals `(1/e) ∑_j 1/j`.
- `barbanVehovLongFirstLogKernel_eq_scaled`: the first log kernel equals
  `(1/e) ∑_j (log(e/r) + log j) / j`.
- `barbanVehovLongSecondLogKernel_eq_scaled`: the second log kernel equals
  `(1/e) ∑_j (log(e/q) + log j)(log(e/r) + log j) / j`.

## Hypotheses

All results are unconditional identities; they assume `0 < e`, respectively `0 < q`, `0 < r`
(and `0 < j` for the logarithm splitting).
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

/-- For `e > 0`, summing `f` over the multiples of `e` in `(L, U]` equals summing `f(e j)` over
`j ∈ (⌊L/e⌋, ⌊U/e⌋]`. -/
theorem sum_filter_dvd_Ioc_eq_sum_scaled
    {R : Type*} [AddCommMonoid R] {e L U : ℕ} (he : 0 < e) (f : ℕ → R) :
    ∑ k ∈ (Finset.Ioc L U).filter (fun k => e ∣ k), f k =
      ∑ j ∈ Finset.Ioc (L / e) (U / e), f (e * j) := by
  classical
  have hset : (Finset.Ioc L U).filter (fun k => e ∣ k) =
      (Finset.Ioc (L / e) (U / e)).image (fun j => e * j) := by
    ext k
    constructor
    · intro hk
      obtain ⟨hkIoc, hkdiv⟩ := Finset.mem_filter.mp hk
      obtain ⟨j, rfl⟩ := hkdiv
      obtain ⟨hL, hU⟩ := Finset.mem_Ioc.mp hkIoc
      refine Finset.mem_image.mpr ⟨j, Finset.mem_Ioc.mpr ⟨?_, ?_⟩, rfl⟩
      · exact (Nat.div_lt_iff_lt_mul he).mpr (by simpa [Nat.mul_comm] using hL)
      · exact (Nat.le_div_iff_mul_le he).mpr (by simpa [Nat.mul_comm] using hU)
    · intro hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hL, hU⟩ := Finset.mem_Ioc.mp hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, ⟨j, rfl⟩⟩
      · simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul he).mp hL
      · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le he).mp hU
  rw [hset]
  exact Finset.sum_image fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left he hxy

/-- For positive `q, r, j`, `log(lcm(q, r) j / r) = log(lcm(q, r) / r) + log j`. -/
theorem log_lcmMul_natDiv_eq_add_log
    {q r j : ℕ} (hq : 0 < q) (hr : 0 < r) (hj : 0 < j) :
    Real.log (((Nat.lcm q r * j / r : ℕ) : ℝ)) =
      Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) + Real.log j := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  have her : r ∣ Nat.lcm q r := Nat.dvd_lcm_right q r
  have herpos : 0 < Nat.lcm q r / r := Nat.div_pos (Nat.le_of_dvd he her) hr
  have hnat : Nat.lcm q r * j / r = (Nat.lcm q r / r) * j := by
    calc
      Nat.lcm q r * j / r = j * Nat.lcm q r / r := by rw [Nat.mul_comm]
      _ = j * (Nat.lcm q r / r) := Nat.mul_div_assoc j her
      _ = (Nat.lcm q r / r) * j := by rw [Nat.mul_comm]
  rw [hnat]
  push_cast
  exact Real.log_mul (by exact_mod_cast herpos.ne') (by exact_mod_cast hj.ne')

/-- For positive `q, r`, the long harmonic lcm kernel equals `(1/lcm(q, r)) ∑_j 1/j` over the
rescaled window. -/
theorem barbanVehovLongHarmonicKernel_eq_scaled
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongHarmonicKernel L U q r =
      1 / (Nat.lcm q r : ℝ) *
        ∑ j ∈ Finset.Ioc (L / Nat.lcm q r) (U / Nat.lcm q r), 1 / (j : ℝ) := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  rw [barbanVehovLongHarmonicKernel,
    sum_filter_dvd_Ioc_eq_sum_scaled he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjpos : 0 < j := by
    exact (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hj).1
  push_cast
  field_simp

/-- For positive `q, r`, the first log lcm kernel equals
`(1/lcm(q, r)) ∑_j (log(lcm(q, r)/r) + log j) / j` over the rescaled window. -/
theorem barbanVehovLongFirstLogKernel_eq_scaled
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongFirstLogKernel L U q r =
      1 / (Nat.lcm q r : ℝ) *
        ∑ j ∈ Finset.Ioc (L / Nat.lcm q r) (U / Nat.lcm q r),
          (Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) + Real.log j) / (j : ℝ) := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  rw [barbanVehovLongFirstLogKernel,
    sum_filter_dvd_Ioc_eq_sum_scaled he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjpos : 0 < j := by
    exact (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hj).1
  rw [log_lcmMul_natDiv_eq_add_log hq hr hjpos]
  push_cast
  field_simp

/-- For positive `q, r`, the second log lcm kernel equals
`(1/lcm(q, r)) ∑_j (log(lcm/q) + log j)(log(lcm/r) + log j) / j` over the rescaled window. -/
theorem barbanVehovLongSecondLogKernel_eq_scaled
    {L U q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    barbanVehovLongSecondLogKernel L U q r =
      1 / (Nat.lcm q r : ℝ) *
        ∑ j ∈ Finset.Ioc (L / Nat.lcm q r) (U / Nat.lcm q r),
          (Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) + Real.log j) *
              (Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) + Real.log j) /
            (j : ℝ) := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  rw [barbanVehovLongSecondLogKernel,
    sum_filter_dvd_Ioc_eq_sum_scaled he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjpos : 0 < j := by
    exact (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hj).1
  have hqlog : Real.log (((Nat.lcm q r * j / q : ℕ) : ℝ)) =
      Real.log (((Nat.lcm q r / q : ℕ) : ℝ)) + Real.log j := by
    simpa [Nat.lcm_comm] using log_lcmMul_natDiv_eq_add_log hr hq hjpos
  rw [log_lcmMul_natDiv_eq_add_log hq hr hjpos, hqlog]
  push_cast
  field_simp

end RHTower.Sieve

