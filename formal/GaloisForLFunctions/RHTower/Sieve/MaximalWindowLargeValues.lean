import GaloisForLFunctions.RHTower.Sieve.LinearMeanSquareGeneric
import GaloisForLFunctions.RHTower.Sieve.MaximalWindowUniform

/-!
# The maximal-window mean square from one frequency mean square

Composing units 13 and 14.  Every level `ℓ = 2^j ≤ 2^J` and every translate `A + i·2^j`
(`i < 2^{J−j}`, so `i·2^j ≤ 2^J`) is covered by the same bound once the level is replaced by `2^J`
and the base by `A`, because

* `log(1 + 2^j/(A + i·2^j)) ≤ log(1 + 2^J/A)`,
* `(ε·2^j + 1)² ≤ (ε·2^J + 1)²`,
* `A + i·2^j ≤ B + 1 + 2^J`.

The result is a single unconditional inequality in which the *only* arithmetic quantity is the
frequency mean square

```text
I  ≥  ∫_{|w| ≤ W} ‖ ∑_{n ≤ M} f(n)·n^{2πiw} ‖² dw ,
```

with `M₂` the trivial global size, `W` the height, `ε` the block ratio and `K'` the number of blocks.
Supplying `I` for `f = μ` is the Matomäki–Radziwiłł estimate; everything else on the route is proved.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset

/-- **The maximal-window mean square, from one frequency mean square.** -/
theorem sum_maxWindowSq_succ_le_largeValues (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    {H J A B M K' : ℕ} {ε M₂ W I : ℝ}
    (hJ : H + 1 ≤ 2 ^ J) (hA : 0 < A) (hAB : A ≤ B + 1)
    (hε : 0 ≤ ε) (hW : 0 < W) (hM₂ : 0 ≤ M₂) (hI0 : 0 ≤ I)
    (hM : B + 2 ^ J + 1 + 2 ^ J < M + 1)
    (hcov : (A : ℝ) + ((B + 1 - A : ℕ) : ℝ) ≤ (A : ℝ) * (1 + ε) ^ K')
    (hI : (∫ w in Set.Icc (-W) W,
      ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ)) ≤ I)
    (h₂ : ∀ w : ℝ, ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ) ≤ M₂) :
    ∑ y ∈ Finset.Icc (A + 1) (B + 1), maxWindowSq f H y
      ≤ ((J : ℝ) + 1) * ((J : ℝ) + 1) * (2 ^ J : ℝ)
        * ((((B : ℝ) + 1 + ((2 ^ J : ℕ) : ℝ)) * (1 + ε) ^ K')
            * ((K' : ℝ) * blockCostG ((2 ^ J : ℕ) : ℝ) ε
                (2 * Real.log (1 + ((2 ^ J : ℕ) : ℝ) / (A : ℝ)) ^ (2 : ℕ) * I
                  + M₂ * (2 / (Real.pi ^ (2 : ℕ) * W))))) := by
  classical
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hone : (0 : ℝ) < 1 + ε := by linarith
  have hpowone : (1 : ℝ) ≤ (1 + ε) ^ K' := one_le_pow₀ (by linarith)
  set Gmax : ℝ := 2 * Real.log (1 + ((2 ^ J : ℕ) : ℝ) / (A : ℝ)) ^ (2 : ℕ) * I
    + M₂ * (2 / (Real.pi ^ (2 : ℕ) * W)) with hGmax
  have hlogJ : 0 ≤ Real.log (1 + ((2 ^ J : ℕ) : ℝ) / (A : ℝ)) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) / (A : ℝ) := by positivity
    linarith
  have hGmax0 : 0 ≤ Gmax := by
    rw [hGmax]
    have h1 : (0 : ℝ) ≤ 2 * Real.log (1 + ((2 ^ J : ℕ) : ℝ) / (A : ℝ)) ^ (2 : ℕ) * I :=
      mul_nonneg (by positivity) hI0
    have h2 : (0 : ℝ) ≤ M₂ * (2 / (Real.pi ^ (2 : ℕ) * W)) := by positivity
    linarith
  set C : ℝ := (((B : ℝ) + 1 + ((2 ^ J : ℕ) : ℝ)) * (1 + ε) ^ K')
      * ((K' : ℝ) * blockCostG ((2 ^ J : ℕ) : ℝ) ε Gmax) with hC
  have hcost0 : 0 ≤ blockCostG ((2 ^ J : ℕ) : ℝ) ε Gmax := blockCostG_nonneg hε hGmax0
  have hC0 : 0 ≤ C := by
    rw [hC]
    have hB0 : (0 : ℝ) ≤ (B : ℝ) + 1 + ((2 ^ J : ℕ) : ℝ) := by positivity
    have hpow0 : (0 : ℝ) ≤ (1 + ε) ^ K' := by positivity
    have hK0 : (0 : ℝ) ≤ (K' : ℝ) := Nat.cast_nonneg K'
    have : (0 : ℝ) ≤ (K' : ℝ) * blockCostG ((2 ^ J : ℕ) : ℝ) ε Gmax :=
      mul_nonneg hK0 hcost0
    exact mul_nonneg (mul_nonneg hB0 hpow0) this
  refine le_trans (sum_maxWindowSq_succ_le_uniform f hJ hC0 ?_) (le_of_eq (by rw [hC]))
  intro j hj i hi
  -- the translate and the level
  have hpowj : 2 ^ (J - j) * 2 ^ j = 2 ^ J := by
    rw [← pow_add]
    congr 1
    omega
  have hshift : i * 2 ^ j ≤ 2 ^ J := by
    calc i * 2 ^ j ≤ (2 ^ (J - j) - 1) * 2 ^ j := by
          exact Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ J := by
          have : (2 ^ (J - j) - 1) * 2 ^ j ≤ 2 ^ (J - j) * 2 ^ j :=
            Nat.mul_le_mul_right _ (by omega)
          omega
  have hlevel : (2 : ℕ) ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hj
  set A' : ℕ := A + i * 2 ^ j with hA'
  set B' : ℕ := B + i * 2 ^ j with hB'
  have hA'0 : 0 < A' := by omega
  have hA'ge : A ≤ A' := by omega
  have hA'R : (A : ℝ) ≤ (A' : ℝ) := by exact_mod_cast hA'ge
  have hA'0R : (0 : ℝ) < (A' : ℝ) := by exact_mod_cast hA'0
  have hA'B' : A' ≤ B' + 1 := by omega
  have hM' : B' + 1 + 2 ^ j < M + 1 := by omega
  have hsub : B' + 1 - A' = B + 1 - A := by omega
  have hcov' : (A' : ℝ) + ((B' + 1 - A' : ℕ) : ℝ) ≤ (A' : ℝ) * (1 + ε) ^ K' := by
    rw [hsub]
    have hexp : (A : ℝ) * ((1 + ε) ^ K' - 1) = (A : ℝ) * (1 + ε) ^ K' - (A : ℝ) := by ring
    have hgap : ((B + 1 - A : ℕ) : ℝ) ≤ (A : ℝ) * ((1 + ε) ^ K' - 1) := by
      rw [hexp]
      linarith [hcov]
    have hgrow : (A : ℝ) * ((1 + ε) ^ K' - 1) ≤ (A' : ℝ) * ((1 + ε) ^ K' - 1) :=
      mul_le_mul_of_nonneg_right hA'R (by linarith)
    have hexp' : (A' : ℝ) * ((1 + ε) ^ K' - 1) = (A' : ℝ) * (1 + ε) ^ K' - (A' : ℝ) := by ring
    rw [hexp'] at hgrow
    linarith
  have hbase := dyadicMeanSquare_le_largeValues f hf (ℓ := 2 ^ j) (A := A') (B := B')
    (M := M) (K' := K') (ε := ε) (M₂ := M₂) (W := W) (I := I)
    (by positivity) hA'0 hA'B' hε hW hM₂ hI0 hM' hcov' hI h₂
  refine le_trans hbase ?_
  -- uniformise the level and the base
  have hlogle : Real.log (1 + ((2 ^ j : ℕ) : ℝ) / (A' : ℝ))
      ≤ Real.log (1 + ((2 ^ J : ℕ) : ℝ) / (A : ℝ)) := by
    refine Real.log_le_log (by positivity) ?_
    have h1 : ((2 ^ j : ℕ) : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) := by exact_mod_cast hlevel
    have hstep1 : ((2 ^ j : ℕ) : ℝ) / (A' : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) / (A' : ℝ) :=
      div_le_div_of_nonneg_right h1 hA'0R.le
    have hstep2 : ((2 ^ J : ℕ) : ℝ) / (A' : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) / (A : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hA0 hA'R
    linarith
  have hlog0 : 0 ≤ Real.log (1 + ((2 ^ j : ℕ) : ℝ) / (A' : ℝ)) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) / (A' : ℝ) := by positivity
    linarith
  have hGle : 2 * Real.log (1 + ((2 ^ j : ℕ) : ℝ) / (A' : ℝ)) ^ (2 : ℕ) * I
      + M₂ * (2 / (Real.pi ^ (2 : ℕ) * W)) ≤ Gmax := by
    rw [hGmax]
    have hsq : Real.log (1 + ((2 ^ j : ℕ) : ℝ) / (A' : ℝ)) ^ (2 : ℕ)
        ≤ Real.log (1 + ((2 ^ J : ℕ) : ℝ) / (A : ℝ)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hlog0 hlogle 2
    have hmul := mul_le_mul_of_nonneg_right hsq hI0
    linarith
  have hcostle : blockCostG ((2 ^ j : ℕ) : ℝ) ε
      (2 * Real.log (1 + ((2 ^ j : ℕ) : ℝ) / (A' : ℝ)) ^ (2 : ℕ) * I
        + M₂ * (2 / (Real.pi ^ (2 : ℕ) * W)))
      ≤ blockCostG ((2 ^ J : ℕ) : ℝ) ε Gmax := by
    rw [blockCostG, blockCostG]
    have hlvl : ((2 ^ j : ℕ) : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) := by exact_mod_cast hlevel
    have hlogε : 0 ≤ Real.log (1 + ε) := Real.log_nonneg (by linarith)
    have hpair : (ε * ((2 ^ j : ℕ) : ℝ) + 1) ^ (2 : ℕ) ≤ (ε * ((2 ^ J : ℕ) : ℝ) + 1) ^ (2 : ℕ) := by
      have h0 : (0 : ℝ) ≤ ε * ((2 ^ j : ℕ) : ℝ) + 1 := by positivity
      have h1 : ε * ((2 ^ j : ℕ) : ℝ) + 1 ≤ ε * ((2 ^ J : ℕ) : ℝ) + 1 := by
        have := mul_le_mul_of_nonneg_left hlvl hε
        linarith
      exact pow_le_pow_left₀ h0 h1 2
    have hterm := mul_le_mul_of_nonneg_right hpair hlogε
    linarith [hGle, hterm]
  have hbase' : (A' : ℝ) * (1 + ε) ^ K' ≤ ((B : ℝ) + 1 + ((2 ^ J : ℕ) : ℝ)) * (1 + ε) ^ K' := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : (A' : ℝ) ≤ (B : ℝ) + 1 + ((2 ^ J : ℕ) : ℝ) := by
      have hnat : A' ≤ B + 1 + 2 ^ J := by omega
      have := (Nat.cast_le (α := ℝ)).2 hnat
      push_cast at this ⊢
      linarith
    exact this
  rw [hC]
  have hK0 : (0 : ℝ) ≤ (K' : ℝ) := Nat.cast_nonneg K'
  have hstep : (K' : ℝ) * blockCostG ((2 ^ j : ℕ) : ℝ) ε
      (2 * Real.log (1 + ((2 ^ j : ℕ) : ℝ) / (A' : ℝ)) ^ (2 : ℕ) * I
        + M₂ * (2 / (Real.pi ^ (2 : ℕ) * W)))
      ≤ (K' : ℝ) * blockCostG ((2 ^ J : ℕ) : ℝ) ε Gmax :=
    mul_le_mul_of_nonneg_left hcostle hK0
  have hpos : (0 : ℝ) ≤ (A' : ℝ) * (1 + ε) ^ K' := by positivity
  have hstep0 : (0 : ℝ) ≤ (K' : ℝ) * blockCostG ((2 ^ J : ℕ) : ℝ) ε Gmax :=
    mul_nonneg hK0 hcost0
  calc (A' : ℝ) * (1 + ε) ^ K' * ((K' : ℝ) * blockCostG ((2 ^ j : ℕ) : ℝ) ε
        (2 * Real.log (1 + ((2 ^ j : ℕ) : ℝ) / (A' : ℝ)) ^ (2 : ℕ) * I
          + M₂ * (2 / (Real.pi ^ (2 : ℕ) * W))))
      ≤ (A' : ℝ) * (1 + ε) ^ K' * ((K' : ℝ) * blockCostG ((2 ^ J : ℕ) : ℝ) ε Gmax) :=
        mul_le_mul_of_nonneg_left hstep hpos
    _ ≤ ((B : ℝ) + 1 + ((2 ^ J : ℕ) : ℝ)) * (1 + ε) ^ K'
          * ((K' : ℝ) * blockCostG ((2 ^ J : ℕ) : ℝ) ε Gmax) :=
        mul_le_mul_of_nonneg_right hbase' hstep0

end RHTower.Sieve

end
