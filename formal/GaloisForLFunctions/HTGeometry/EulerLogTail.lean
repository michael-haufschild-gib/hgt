import GaloisForLFunctions.HTGeometry.PrimaryFactorLogExpansion
import GaloisForLFunctions.HTGeometry.HelsonCubeRootNonContinuation

/-!
# The Euler logarithm and its quadratic tail

For `‖z‖ < 1` write

```text
-log(1-z) = z + logTail z ,      logTail z = ∑_{k ≥ 2} z^k / k .
```

The tail is what makes the Euler logarithm of a Helson zeta split into a *conditionally* convergent
prime layer `∑_p χ(p) p^{-s}` and an *absolutely* convergent remainder: `‖logTail z‖ = O(‖z‖²)`,
and `∑_p p^{-2σ}` converges for every `σ > 1/2`, while `∑_p p^{-σ}` does not.

The other fact proved here is the cube-root cancellation

```text
logTail z + logTail (ω z) + logTail (ω² z) = -log(1 - z³) ,
```

for a primitive cube root of unity `ω`.  The linear layer cancels identically because
`1 + ω + ω² = 0`, and every layer whose index is not a multiple of three cancels for the same
reason; the surviving layers reassemble the logarithm at `z³`.  This is the exact mechanism that
will remove the unknown boundary order from the Helson continuation estimate.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- The quadratic tail of the Euler logarithm. -/
def logTail (z : ℂ) : ℂ := -Complex.log (1 - z) - z

theorem hasSum_neg_log_sub {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ n / (n : ℂ)) (-Complex.log (1 - z)) :=
  Complex.hasSum_taylorSeries_neg_log hz

theorem hasSum_logTail {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (k + 2) / (((k + 2 : ℕ) : ℂ))) (logTail z) := by
  have h := hasSum_neg_log_sub hz
  have hhead : ∑ i ∈ Finset.range 2, z ^ i / (i : ℂ) = z := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  refine (hasSum_nat_add_iff (f := fun n : ℕ => z ^ n / (n : ℂ)) 2).mpr ?_
  rw [hhead, logTail]
  simpa using h

/-- The tail is quadratically small. -/
theorem norm_logTail_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖logTail z‖ ≤ ‖z‖ ^ 2 / (2 * (1 - ‖z‖)) := by
  have hnn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  have hmaj : ∀ k : ℕ, ‖z ^ (k + 2) / (((k + 2 : ℕ) : ℂ))‖ ≤ (1 / 2) * ‖z‖ ^ (k + 2) := by
    intro k
    rw [norm_div, norm_pow]
    have hk : ‖(((k + 2 : ℕ) : ℂ))‖ = ((k : ℝ) + 2) := by
      rw [Complex.norm_natCast]
      push_cast
      ring
    rw [hk]
    have hpos : (0:ℝ) < (k : ℝ) + 2 := by positivity
    rw [div_le_iff₀ hpos]
    have h2 : (2:ℝ) ≤ (k : ℝ) + 2 := by
      have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    nlinarith [pow_nonneg hnn (k + 2)]
  have hgeo : HasSum (fun k : ℕ => (1 / 2 : ℝ) * ‖z‖ ^ (k + 2))
      ((1 / 2 : ℝ) * (‖z‖ ^ 2 / (1 - ‖z‖))) := by
    have hg : HasSum (fun k : ℕ => ‖z‖ ^ k) (1 - ‖z‖)⁻¹ := hasSum_geometric_of_lt_one hnn hz
    have hg2 : HasSum (fun k : ℕ => ‖z‖ ^ 2 * ‖z‖ ^ k) (‖z‖ ^ 2 * (1 - ‖z‖)⁻¹) := hg.mul_left _
    have hfun : (fun k : ℕ => ‖z‖ ^ (k + 2)) = fun k : ℕ => ‖z‖ ^ 2 * ‖z‖ ^ k := by
      funext k
      rw [pow_add]
      ring
    have hg3 : HasSum (fun k : ℕ => ‖z‖ ^ (k + 2)) (‖z‖ ^ 2 / (1 - ‖z‖)) := by
      rw [hfun, div_eq_mul_inv]
      exact hg2
    exact hg3.mul_left _
  have hle := (hasSum_logTail hz).norm_le_of_bounded hgeo hmaj
  refine le_trans hle (le_of_eq ?_)
  field_simp


/-! ### The cube-root cancellation -/

theorem cubeRootUnit_sq : cubeRootUnit ^ 2 = (starRingEnd ℂ) cubeRootUnit := by
  have h1 := cubeRootUnit_add_conj
  have h2 := cubeRootUnit_mul_conj
  have hconj : (starRingEnd ℂ) cubeRootUnit = -1 - cubeRootUnit := by linear_combination h1
  rw [hconj]
  rw [hconj] at h2
  linear_combination -h2

theorem cubeRootUnit_pow_three : cubeRootUnit ^ 3 = 1 := by
  have h := cubeRootUnit_mul_conj
  rw [← cubeRootUnit_sq] at h
  calc cubeRootUnit ^ 3 = cubeRootUnit * cubeRootUnit ^ 2 := by ring
    _ = 1 := h

theorem one_add_cubeRootUnit_add_sq : 1 + cubeRootUnit + cubeRootUnit ^ 2 = 0 := by
  have h1 := cubeRootUnit_add_conj
  rw [← cubeRootUnit_sq] at h1
  linear_combination h1

theorem cubeRootUnit_pow_sum (n : ℕ) :
    1 + cubeRootUnit ^ n + (cubeRootUnit ^ 2) ^ n = if 3 ∣ n then 3 else 0 := by
  have h3 : cubeRootUnit ^ 3 = 1 := cubeRootUnit_pow_three
  have hmod : cubeRootUnit ^ n = cubeRootUnit ^ (n % 3) := by
    conv_lhs => rw [← Nat.div_add_mod n 3]
    rw [pow_add, pow_mul, h3, one_pow, one_mul]
  have h9 : (cubeRootUnit ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
  have hmod2 : (cubeRootUnit ^ 2) ^ n = (cubeRootUnit ^ 2) ^ (n % 3) := by
    conv_lhs => rw [← Nat.div_add_mod n 3]
    rw [pow_add, pow_mul, h9, one_pow, one_mul]
  have hdvd : (3 ∣ n) ↔ n % 3 = 0 := Nat.dvd_iff_mod_eq_zero
  rw [hmod, hmod2]
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h | h | h
  · rw [h, if_pos (hdvd.mpr h)]
    norm_num
  · rw [h, if_neg (fun hc => by rw [hdvd.mp hc] at h; exact absurd h (by norm_num))]
    have := one_add_cubeRootUnit_add_sq
    linear_combination this
  · rw [h, if_neg (fun hc => by rw [hdvd.mp hc] at h; exact absurd h (by norm_num))]
    have hkey : (cubeRootUnit ^ 2) ^ 2 = cubeRootUnit := by
      have : (cubeRootUnit ^ 2) ^ 2 = cubeRootUnit ^ 3 * cubeRootUnit := by ring
      rw [this, h3, one_mul]
    rw [hkey]
    have := one_add_cubeRootUnit_add_sq
    linear_combination this

/-- **The three rotated Euler logarithms reassemble the logarithm at the cube.** -/
theorem neg_log_cube_sum {z : ℂ} (hz : ‖z‖ < 1) :
    (-Complex.log (1 - z)) + (-Complex.log (1 - cubeRootUnit * z))
        + (-Complex.log (1 - cubeRootUnit ^ 2 * z))
      = -Complex.log (1 - z ^ 3) := by
  classical
  have hnorm1 : ‖cubeRootUnit * z‖ < 1 := by
    rw [norm_mul, norm_cubeRootUnit, one_mul]; exact hz
  have hnorm2 : ‖cubeRootUnit ^ 2 * z‖ < 1 := by
    rw [norm_mul, norm_pow, norm_cubeRootUnit, one_pow, one_mul]; exact hz
  have hnorm3 : ‖z ^ 3‖ < 1 := by
    rw [norm_pow]
    calc ‖z‖ ^ 3 ≤ ‖z‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg z) hz.le (by norm_num)
      _ = ‖z‖ := pow_one _
      _ < 1 := hz
  set f : ℕ → ℂ := fun n => (if 3 ∣ n then (3 : ℂ) else 0) * z ^ n / (n : ℂ) with hfdef
  have hsum : HasSum f ((-Complex.log (1 - z)) + (-Complex.log (1 - cubeRootUnit * z))
      + (-Complex.log (1 - cubeRootUnit ^ 2 * z))) := by
    refine (((hasSum_neg_log_sub hz).add (hasSum_neg_log_sub hnorm1)).add
      (hasSum_neg_log_sub hnorm2)).congr_fun fun n => ?_
    rw [hfdef]
    simp only
    rw [mul_pow, mul_pow, ← cubeRootUnit_pow_sum n]
    field_simp
  have hinj : Function.Injective (fun j : ℕ => 3 * j) := fun j k h => by
    simp only at h
    omega
  have hzero : ∀ n ∉ Set.range (fun j : ℕ => 3 * j), f n = 0 := by
    intro n hn
    have hnd : ¬ (3 ∣ n) := by
      intro ⟨k, hk⟩
      exact hn ⟨k, by show 3 * k = n; omega⟩
    rw [hfdef]
    simp only
    rw [if_neg hnd, zero_mul, zero_div]
  have hcomp : (f ∘ fun j : ℕ => 3 * j) = fun j : ℕ => (z ^ 3) ^ j / (j : ℂ) := by
    funext j
    rw [Function.comp_apply, hfdef]
    simp only
    rw [if_pos ⟨j, rfl⟩, ← pow_mul]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · norm_num
    · have hjne : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h3j : ((3 * j : ℕ) : ℂ) = 3 * (j : ℂ) := by push_cast; ring
      rw [h3j]
      field_simp
  have hcube := hasSum_neg_log_sub hnorm3
  have htrans := (Function.Injective.hasSum_iff (f := f) hinj hzero).mpr hsum
  rw [hcomp] at htrans
  exact (htrans.unique hcube)

/-- **The cube-root cancellation for the quadratic tail.** -/
theorem logTail_cube_sum {z : ℂ} (hz : ‖z‖ < 1) :
    logTail z + logTail (cubeRootUnit * z) + logTail (cubeRootUnit ^ 2 * z)
      = -Complex.log (1 - z ^ 3) := by
  have hlin : z + cubeRootUnit * z + cubeRootUnit ^ 2 * z = 0 := by
    have := one_add_cubeRootUnit_add_sq
    linear_combination z * this
  rw [logTail, logTail, logTail]
  rw [← neg_log_cube_sum hz]
  linear_combination -hlin

end GaloisForLFunctions.HTGeometry

end
