import GaloisForLFunctions.RHTower.Sieve.DirichletSigmaTarget

/-!
# Simplifying the head off the line

The head of the rectangle estimate is the integral comparison `1 + ((C-1)^(1-σ) - 1)/(1-σ)
+ (C-1)^(-σ)`, whose middle term degenerates to `log (C-1)` as `σ → 1`.  The elementary inequality

```text
(x^a - 1)/a  ≤  x^a · log x      (x ≥ 1, a > 0)
```

bounds it uniformly by `C^(1-σ) · log C`, so the whole head is at most `2 + C^(1-σ) log C`.  At
`σ = 1` that is `2 + log C`, the head of the estimate on the line.
-/

namespace RHTower.Sieve

open Finset

/-- `(x^a - 1)/a ≤ x^a · log x` for `x ≥ 1` and `a > 0`; the difference quotient of `a ↦ x^a` at `0`
is dominated by its derivative at `a`. -/
theorem rpow_sub_one_div_le {x a : ℝ} (hx : 1 ≤ x) (ha : 0 < a) :
    (x ^ a - 1) / a ≤ x ^ a * Real.log x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  set u : ℝ := a * Real.log x with hu
  have hE : 0 < Real.exp u := Real.exp_pos u
  have hxa : x ^ a = Real.exp u := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    rw [hu]; ring
  have h := Real.add_one_le_exp (-u)
  rw [Real.exp_neg] at h
  have h4 := mul_le_mul_of_nonneg_right h hE.le
  rw [inv_mul_cancel₀ hE.ne'] at h4
  have h3 : Real.exp u - 1 ≤ u * Real.exp u := by nlinarith [h4]
  rw [hxa, div_le_iff₀ ha]
  calc Real.exp u - 1 ≤ u * Real.exp u := h3
    _ = Real.exp u * Real.log x * a := by rw [hu]; ring

/-- **The head, simplified.**  The integral comparison below the abscissa is at most
`2 + C^(1-σ) log C`. -/
theorem strip_head_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {C : ℕ} (hC : 3 ≤ C) :
    1 + (((C - 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ) + ((C - 1 : ℕ) : ℝ) ^ (-σ)
      ≤ 2 + ((C : ℕ) : ℝ) ^ (1 - σ) * Real.log ((C : ℕ) : ℝ) := by
  have hCm : (2 : ℝ) ≤ ((C - 1 : ℕ) : ℝ) := by
    have h : (2 : ℕ) ≤ C - 1 := by omega
    exact_mod_cast h
  have hCm1 : (1 : ℝ) ≤ ((C - 1 : ℕ) : ℝ) := by linarith
  have hCle : ((C - 1 : ℕ) : ℝ) ≤ ((C : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le C 1
  have ha : (0 : ℝ) < 1 - σ := by linarith
  have hA := rpow_sub_one_div_le hCm1 ha
  have hbase : ((C - 1 : ℕ) : ℝ) ^ (1 - σ) ≤ ((C : ℕ) : ℝ) ^ (1 - σ) :=
    Real.rpow_le_rpow (by linarith) hCle ha.le
  have hlogle : Real.log ((C - 1 : ℕ) : ℝ) ≤ Real.log ((C : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) hCle
  have hlognn : 0 ≤ Real.log ((C - 1 : ℕ) : ℝ) := Real.log_nonneg hCm1
  have hprod : ((C - 1 : ℕ) : ℝ) ^ (1 - σ) * Real.log ((C - 1 : ℕ) : ℝ)
      ≤ ((C : ℕ) : ℝ) ^ (1 - σ) * Real.log ((C : ℕ) : ℝ) :=
    mul_le_mul hbase hlogle hlognn (Real.rpow_nonneg (by linarith) _)
  have hB : ((C - 1 : ℕ) : ℝ) ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hCm1 (by linarith)
  linarith

/-- **Rectangle bound with the simplified head.** -/
theorem norm_dirichlet_sigma_littlewood_strip_head {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ht : 0 < t) {C R : ℕ} (hC : 3 ≤ C) (hR : 1 ≤ R) (K : ℕ) (hK : 2 ≤ K)
    (hstrip : 1 - σ ≤ 1 / (6 * (2 : ℝ) ^ K))
    (hfac0 : Nat.factorial (K - 1) ≤ C)
    (hlowTop : 8 * Real.pi * ((C * 2 ^ (R - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh0 : t ≤ 2 * Real.pi * 2 ^ K * ((C : ℕ) : ℝ) ^ (K - 1) * ((C : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (C * 2 ^ R), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 2 + ((C : ℕ) : ℝ) ^ (1 - σ) * Real.log ((C : ℕ) : ℝ) + (R : ℝ) * stripTargetEps C K := by
  have h := norm_dirichlet_sigma_littlewood_canonical hσ0 hσ1 ht hC hR K hK hstrip hfac0
    hlowTop hhigh0
  have hhead := strip_head_le hσ0 hσ1 hC
  linarith

end RHTower.Sieve
