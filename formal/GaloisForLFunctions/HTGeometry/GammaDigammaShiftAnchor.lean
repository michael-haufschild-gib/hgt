import GaloisForLFunctions.HTGeometry.GammaStirlingCubicLog

/-!
# The digamma anchor: shifts become asymptotically invisible

Gauss's formula `ψ(s) = lim_n (log n − ∑_{j≤n} 1/(s+j))` has the `log n` in it *independently of
`s`*, so it cancels in a difference:

```text
ψ(s) − ψ(t) = lim_n ∑_{j≤n} (1/(t+j) − 1/(s+j)),
```

and the summand is `(s−t)/((s+j)(t+j))`.  For `s = z+N` and `t = 1+N` in the right half-plane the
denominators are at least `(N+j)(N+j+1)`, whose reciprocals telescope to `1/N`.  Hence

```text
‖ψ(z+N) − ψ(1+N)‖ ≤ ‖z−1‖ / N,
```

which is the anchor that makes the Stirling telescope converge to zero rather than to an unknown
constant.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-! ## The telescoping harmonic bound -/

theorem sum_inv_mul_succ_le (N : ℕ) (hN : 1 ≤ N) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (1 : ℝ) / (((N : ℝ) + j) * ((N : ℝ) + j + 1)) ≤ 1 / (N : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hkey : ∀ m : ℕ, ∑ j ∈ Finset.range m, (1 : ℝ) / (((N : ℝ) + j) * ((N : ℝ) + j + 1))
      = 1 / (N : ℝ) - 1 / ((N : ℝ) + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have h1 : (0 : ℝ) < (N : ℝ) + m := by positivity
        have h2 : (0 : ℝ) < (N : ℝ) + m + 1 := by positivity
        have hcast : ((N : ℝ) + (m + 1 : ℕ)) = (N : ℝ) + m + 1 := by push_cast; ring
        rw [hcast]
        field_simp
        ring
  rw [hkey]
  have hpos : (0 : ℝ) < (N : ℝ) + ((n + 1 : ℕ) : ℝ) := by positivity
  have hinv : (0 : ℝ) < 1 / ((N : ℝ) + ((n + 1 : ℕ) : ℝ)) := by positivity
  linarith

/-! ## The digamma difference is a convergent telescope -/

set_option maxHeartbeats 1000000 in
theorem norm_digamma_shift_sub_le {z : ℂ} (hz : 0 ≤ z.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖Complex.digamma (z + N) - Complex.digamma (1 + N)‖ ≤ ‖z - 1‖ / (N : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsre : 0 < (z + (N : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    linarith
  have htre : 0 < ((1 : ℂ) + (N : ℂ)).re := by
    rw [Complex.add_re, Complex.one_re, Complex.natCast_re]
    linarith
  have hA := RHTower.gauss_digamma hsre
  have hB := RHTower.gauss_digamma htre
  have hdiff : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
      ((1 : ℂ) / ((1 + (N : ℂ)) + (j : ℂ)) - 1 / ((z + (N : ℂ)) + (j : ℂ))))
      atTop (nhds (Complex.digamma (z + N) - Complex.digamma (1 + N))) := by
    have h := hA.sub hB
    refine h.congr fun n => ?_
    rw [Finset.sum_sub_distrib]
    ring
  refine le_of_tendsto (hdiff.norm) (Filter.Eventually.of_forall fun n => ?_)
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ‖(1 : ℂ) / ((1 + (N : ℂ)) + (j : ℂ)) - 1 / ((z + (N : ℂ)) + (j : ℂ))‖
        ≤ ‖z - 1‖ * ((1 : ℝ) / (((N : ℝ) + j) * ((N : ℝ) + j + 1))) := by
    intro j _
    have hs : ((z + (N : ℂ)) + (j : ℂ)) ≠ 0 := by
      intro h
      have hre : ((z + (N : ℂ)) + (j : ℂ)).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.add_re, Complex.natCast_re, Complex.natCast_re] at hre
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have ht : ((1 : ℂ) + (N : ℂ)) + (j : ℂ) ≠ 0 := by
      intro h
      have hre : (((1 : ℂ) + (N : ℂ)) + (j : ℂ)).re = 0 := by rw [h]; simp
      rw [Complex.add_re, Complex.add_re, Complex.one_re, Complex.natCast_re,
        Complex.natCast_re] at hre
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hid : (1 : ℂ) / ((1 + (N : ℂ)) + (j : ℂ)) - 1 / ((z + (N : ℂ)) + (j : ℂ))
        = (z - 1) / (((1 + (N : ℂ)) + (j : ℂ)) * ((z + (N : ℂ)) + (j : ℂ))) := by
      field_simp
      ring
    rw [hid, norm_div, norm_mul]
    have hsn : (N : ℝ) + j ≤ ‖(z + (N : ℂ)) + (j : ℂ)‖ := by
      refine le_trans ?_ (Complex.abs_re_le_norm _)
      rw [Complex.add_re, Complex.add_re, Complex.natCast_re, Complex.natCast_re]
      rw [le_abs]
      left
      linarith
    have htn : (N : ℝ) + j + 1 ≤ ‖((1 : ℂ) + (N : ℂ)) + (j : ℂ)‖ := by
      refine le_trans ?_ (Complex.abs_re_le_norm _)
      rw [Complex.add_re, Complex.add_re, Complex.one_re, Complex.natCast_re,
        Complex.natCast_re]
      rw [le_abs]
      left
      linarith
    have hden : (0 : ℝ) < ((N : ℝ) + j) * ((N : ℝ) + j + 1) := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      positivity
    have hprodpos : (0 : ℝ) < ‖((1 : ℂ) + (N : ℂ)) + (j : ℂ)‖ * ‖(z + (N : ℂ)) + (j : ℂ)‖ := by
      have h1 : (0 : ℝ) < ‖((1 : ℂ) + (N : ℂ)) + (j : ℂ)‖ := by
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        have := htn
        linarith
      have h2 : (0 : ℝ) < ‖(z + (N : ℂ)) + (j : ℂ)‖ := by
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        have := hsn
        linarith
      positivity
    rw [div_le_iff₀ hprodpos]
    have hmono : ((N : ℝ) + j) * ((N : ℝ) + j + 1)
        ≤ ‖((1 : ℂ) + (N : ℂ)) + (j : ℂ)‖ * ‖(z + (N : ℂ)) + (j : ℂ)‖ := by
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith [hsn, htn, hj, hN0]
    have hz1 : (0 : ℝ) ≤ ‖z - 1‖ := norm_nonneg _
    rw [mul_comm (‖z - 1‖ : ℝ) (1 / (((N : ℝ) + j) * ((N : ℝ) + j + 1))), mul_assoc]
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hden]
    nlinarith [hmono, hz1, hden]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hz1 : (0 : ℝ) ≤ ‖z - 1‖ := norm_nonneg _
  have hsum := sum_inv_mul_succ_le N hN n
  calc ‖z - 1‖ * ∑ j ∈ Finset.range (n + 1),
        (1 : ℝ) / (((N : ℝ) + j) * ((N : ℝ) + j + 1))
      ≤ ‖z - 1‖ * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left hsum hz1
    _ = ‖z - 1‖ / (N : ℝ) := by ring

end

end GaloisForLFunctions.HTGeometry
