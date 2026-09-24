import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros

/-!
# The matching lower bound `log y − 1/y ≤ Re ψ(y)`

The same shift-and-limit argument that gives `Re ψ(y) ≤ log y` gives the companion bound, once the
harmonic sum is bounded *above*: the first term is `1/y` and the rest is dominated by the integral,
because `1/(m+1) ≤ log(1 + 1/m)`.  Together,

```text
log y − 1/y ≤ Re ψ(y) ≤ log y     for every y > 0,
```

which is sharp to the order of the true asymptotic `log y − 1/(2y)` and, unlike
`norm_digamma_sub_log_le_of_re_pos`, carries no restriction on the size of the argument.
-/

open Complex GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- `1/(m+1) ≤ log (1 + 1/m)` for `m > 0`. -/
theorem inv_succ_le_log_one_add_inv {m : ℝ} (hm : 0 < m) :
    1 / (m + 1) ≤ Real.log (1 + 1 / m) := by
  have hu : (0 : ℝ) < 1 + 1 / m := by positivity
  have h := Real.log_le_sub_one_of_pos (x := 1 / (1 + 1 / m)) (by positivity)
  have hinv : Real.log (1 / (1 + 1 / m)) = -Real.log (1 + 1 / m) := by
    rw [one_div, Real.log_inv]
  rw [hinv] at h
  have hval : (1 : ℝ) / (1 + 1 / m) - 1 = -(1 / (m + 1)) := by
    field_simp
    ring
  rw [hval] at h
  linarith

/-- The harmonic sum is at most `1/y` plus the integral. -/
theorem harmonic_le_log_add_inv {y : ℝ} (hy : 0 < y) (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, 1 / (y + (k : ℝ))
      ≤ 1 / y + Real.log (y + ((n : ℝ) - 1)) - Real.log y := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hn with h1 | h1
    · have hn0 : n = 0 := by omega
      subst hn0
      simp
    · have hn1 : 1 ≤ n := by omega
      have ihn := ih hn1
      have hyn : (0 : ℝ) < y + ((n : ℝ) - 1) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        linarith
      have hstep : 1 / (y + (n : ℝ)) ≤ Real.log (y + (((n + 1 : ℕ) : ℝ) - 1))
          - Real.log (y + ((n : ℝ) - 1)) := by
        have hkey := inv_succ_le_log_one_add_inv hyn
        have hval : (1 : ℝ) + 1 / (y + ((n : ℝ) - 1)) = (y + (n : ℝ)) / (y + ((n : ℝ) - 1)) := by
          field_simp
          ring
        rw [hval, Real.log_div (by positivity) hyn.ne'] at hkey
        have hden : y + ((n : ℝ) - 1) + 1 = y + (n : ℝ) := by ring
        rw [hden] at hkey
        have hcast : y + (((n + 1 : ℕ) : ℝ) - 1) = y + (n : ℝ) := by push_cast; ring
        rw [hcast]
        linarith
      rw [Finset.sum_range_succ]
      linarith [ihn, hstep]

/-- **`log y − 1/y ≤ Re ψ(y)` for every `y > 0`.** -/
theorem log_sub_inv_le_re_digamma {y : ℝ} (hy : 0 < y) :
    Real.log y - 1 / y ≤ (Complex.digamma ((y : ℝ) : ℂ)).re := by
  have hstep : ∀ n : ℕ, 1 ≤ n → 2 ≤ (y + (n : ℝ)) →
      Real.log y - 1 / y - 3 / (y + (n : ℝ)) ≤ (Complex.digamma ((y : ℝ) : ℂ)).re := by
    intro n hn1 hn
    have hyn : (0 : ℝ) < y + (n : ℝ) := by linarith
    have hznorm : ‖(((y + (n : ℝ)) : ℝ) : ℂ)‖ = y + (n : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hyn]
    have hstir := norm_digamma_sub_log_le_of_re_pos
      (z := (((y + (n : ℝ)) : ℝ) : ℂ)) (by simp; linarith) (by rw [hznorm]; exact hn)
    rw [hznorm] at hstir
    have hlogre : (Complex.log ((((y + (n : ℝ)) : ℝ) : ℂ))).re = Real.log (y + (n : ℝ)) := by
      rw [Complex.log_re, hznorm]
    have hsh : Real.log (y + (n : ℝ)) - 3 / (y + (n : ℝ))
        ≤ (Complex.digamma ((((y + (n : ℝ)) : ℝ) : ℂ))).re := by
      have hle : -(3 / (y + (n : ℝ)))
          ≤ (Complex.digamma ((((y + (n : ℝ)) : ℝ) : ℂ))
              - Complex.log ((((y + (n : ℝ)) : ℝ) : ℂ))).re := by
        have := neg_abs_le ((Complex.digamma ((((y + (n : ℝ)) : ℝ) : ℂ))
          - Complex.log ((((y + (n : ℝ)) : ℝ) : ℂ))).re)
        have habs : |(Complex.digamma ((((y + (n : ℝ)) : ℝ) : ℂ))
            - Complex.log ((((y + (n : ℝ)) : ℝ) : ℂ))).re| ≤ 3 / (y + (n : ℝ)) :=
          le_trans (Complex.abs_re_le_norm _) hstir
        linarith [this, habs]
      rw [Complex.sub_re, hlogre] at hle
      linarith
    have hrec := re_digamma_shift hy n
    have hharm := harmonic_le_log_add_inv hy n hn1
    have hmono : Real.log (y + ((n : ℝ) - 1)) ≤ Real.log (y + (n : ℝ)) :=
      Real.log_le_log (by linarith [(by exact_mod_cast hn1 : (1:ℝ) ≤ (n:ℝ))]) (by linarith)
    linarith [hsh, hrec, hharm, hmono]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (max (max 1 (2 - y)) (3 / ε))
  have hn1' : (1 : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := by exact_mod_cast hn1'.le
  have hn2 : (2 : ℝ) - y < (n : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : (3 : ℝ) / ε < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hyn : (2 : ℝ) ≤ y + (n : ℝ) := by linarith
  have hyn0 : (0 : ℝ) < y + (n : ℝ) := by linarith
  have hsmall : 3 / (y + (n : ℝ)) ≤ ε := by
    rw [div_le_iff₀ hyn0]
    have h3 : (3 : ℝ) < ε * (n : ℝ) := by
      rw [div_lt_iff₀ hε] at hn3
      linarith
    nlinarith [hε, hy]
  linarith [hstep n hn1 hyn, hsmall]

end

end RHTower
