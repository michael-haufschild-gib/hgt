import GaloisForLFunctions.HTGeometry.PolygammaLeadingAsymptotic
import GaloisForLFunctions.HTGeometry.DigammaFieldValuation

/-!
# The leading constant of a digamma jet monomial

Normalizing each jet by its own leading datum — `ψ` by the leading logarithm, `ψ⁽ʲ⁾` by `s^{-j}` for
`j ≥ 1` — makes every jet converge to an explicit nonzero constant: `1` for `ψ` and
`(−1)^{j−1}(j−1)!` for the higher jets.

A monomial in the jets therefore converges, after normalizing by `(log s)^{e₀}·s^{-Σ_{j≥1} j e_j}`,
to the product of those constants, which is again nonzero.  This is the leading datum of a monomial:
the pair `(e₀, Σ_{j≥1} j e_j)` together with a nonzero constant.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- The `j`-th digamma jet normalized by its own leading datum. -/
noncomputable def normJet (σ : ℝ) (j : ℕ) (t : ℝ) : ℂ :=
  if j = 0 then Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t
  else ((σ : ℂ) + (t : ℂ) * Complex.I) ^ j
    * iteratedDeriv j Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)

/-- The leading constant of the `j`-th digamma jet. -/
noncomputable def jetLeadingConst (j : ℕ) : ℂ :=
  if j = 0 then 1 else (-1 : ℂ) ^ (j - 1) * (((j - 1).factorial : ℕ) : ℂ)

@[simp] theorem jetLeadingConst_zero : jetLeadingConst 0 = 1 := by
  rw [jetLeadingConst, if_pos rfl]

@[simp] theorem jetLeadingConst_succ (m : ℕ) :
    jetLeadingConst (m + 1) = (-1 : ℂ) ^ m * ((m.factorial : ℕ) : ℂ) := by
  rw [jetLeadingConst, if_neg (by omega)]
  simp

/-- Every jet leading constant is nonzero. -/
theorem jetLeadingConst_ne_zero (j : ℕ) : jetLeadingConst j ≠ 0 := by
  cases j with
  | zero => simp
  | succ m =>
    rw [jetLeadingConst_succ]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)

/-- **Each normalized jet converges to its leading constant.** -/
theorem tendsto_normJet (hσ : 0 < σ) (j : ℕ) :
    Tendsto (normJet σ j) atTop (nhds (jetLeadingConst j)) := by
  cases j with
  | zero =>
    have h := tendsto_digamma_div_vertLog (σ := σ) hσ.le
    rw [jetLeadingConst_zero]
    refine h.congr (fun t => ?_)
    rw [normJet, if_pos rfl]
  | succ m =>
    have h := tendsto_pow_mul_iteratedDeriv_digamma_vertical hσ m
    rw [jetLeadingConst_succ]
    refine h.congr (fun t => ?_)
    rw [normJet, if_neg (by omega)]

/-- **The leading datum of a jet monomial.**  A monomial in the digamma jets, normalized jet by jet,
converges to the product of the jet leading constants. -/
theorem tendsto_prod_normJet (hσ : 0 < σ) {n : ℕ} (e : Fin (n + 1) → ℕ) :
    Tendsto (fun t : ℝ => ∏ j : Fin (n + 1), (normJet σ (j : ℕ) t) ^ (e j)) atTop
      (nhds (∏ j : Fin (n + 1), (jetLeadingConst (j : ℕ)) ^ (e j))) :=
  tendsto_finsetProd Finset.univ (fun j _ => ((tendsto_normJet hσ (j : ℕ)).pow (e j)))

/-- The leading constant of a jet monomial is nonzero. -/
theorem prod_jetLeadingConst_ne_zero {n : ℕ} (e : Fin (n + 1) → ℕ) :
    (∏ j : Fin (n + 1), (jetLeadingConst (j : ℕ)) ^ (e j)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (jetLeadingConst_ne_zero (j : ℕ)))

/-- **The leading datum of a finite sum of jet monomials at one dominance level.**  A finite
combination of monomials, each normalized by the same datum, converges to the corresponding
combination of leading constants. -/
theorem tendsto_sum_prod_normJet (hσ : 0 < σ) {n N : ℕ} (d : Fin N → ℂ)
    (e : Fin N → Fin (n + 1) → ℕ) :
    Tendsto (fun t : ℝ => ∑ α : Fin N, d α * ∏ j : Fin (n + 1), (normJet σ (j : ℕ) t) ^ (e α j))
      atTop (nhds (∑ α : Fin N, d α * ∏ j : Fin (n + 1), (jetLeadingConst (j : ℕ)) ^ (e α j))) :=
  tendsto_finsetSum Finset.univ
    (fun α _ => ((tendsto_prod_normJet hσ (e α)).const_mul (d α)))

end GaloisForLFunctions
