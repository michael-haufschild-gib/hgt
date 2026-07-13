import GaloisForLFunctions.WeightPolynomial

/-!
# The distinct-index permanent symbol and its non-degeneracy

At `r` distinct source scales the coefficient of a differential monomial `∏ₜ f^{(μₜ)}` is a
**permanent** of falling factorials, whose polynomial shape is

`permSymbolPoly μ = ∑_{π : Perm (Fin r)} ∏ₜ (descPochhammer ℤ (μₜ)) ∘ X_{π t}`.

Unlike the balanced (single-source) weight polynomial — which can vanish on a nonzero differential
polynomial (`weightPolynomial_class44_dependence`) — the permanent symbols over **distinct order
multisets** are linearly independent: the coefficient of the representative monomial `X^μ` in
`permSymbolPoly ν` is the number of permutations carrying `ν` to `μ`, nonzero only when `ν` and `μ`
are rearrangements.  Hence a nonzero combination of distinct-multiset symbols is a nonzero
polynomial, which — evaluated at distinct integer scales via `exists_injective_eval_ne_zero` — never
degenerates.  This is the leading symbol that survives the distinct-index probe.
-/

open MvPolynomial Finset Polynomial Equiv

namespace GaloisForLFunctions

variable {r : ℕ}

/-- The exponent monomial of the assignment `π`: variable `π t` receives order `μ t`. -/
noncomputable def permMon (μ : Fin r → ℕ) (π : Equiv.Perm (Fin r)) : Fin r →₀ ℕ :=
  ∑ t, Finsupp.single (π t) (μ t)

/-- The distinct-index permanent symbol as a multivariate polynomial. -/
noncomputable def permSymbolPoly (μ : Fin r → ℕ) : MvPolynomial (Fin r) ℤ :=
  ∑ π : Equiv.Perm (Fin r), ∏ t, (Polynomial.aeval (MvPolynomial.X (π t)) (descPochhammer ℤ (μ t)))

/-- Evaluating the assignment exponent at a variable reads the order on that variable's preimage. -/
theorem permMon_apply (μ : Fin r → ℕ) (π : Equiv.Perm (Fin r)) (j : Fin r) :
    permMon μ π j = μ (π.symm j) := by
  classical
  rw [permMon, Finsupp.finsetSum_apply, Finset.sum_eq_single (π.symm j)]
  · rw [Finsupp.single_apply, if_pos (by simp)]
  · intro t _ ht
    rw [Finsupp.single_apply, if_neg]
    intro h; exact ht (by rw [← h]; simp)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The assignment exponent has total mass equal to the total order. -/
theorem permMon_sum (μ : Fin r → ℕ) (π : Equiv.Perm (Fin r)) :
    ∑ j ∈ (permMon μ π).support, (permMon μ π) j = ∑ t, μ t := by
  classical
  have h1 : ∑ j ∈ (permMon μ π).support, (permMon μ π) j = ∑ j : Fin r, (permMon μ π) j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    rw [Finsupp.mem_support_iff, not_not] at hj
    exact hj
  rw [h1]
  simp_rw [permMon_apply]
  exact Equiv.sum_comp π.symm μ

/-- The assignment exponents are injective in the assignment: `permMon μ π` determines `π` when
read against `μ`, and equal `permMon`s over the same `μ` force equal permutations only up to the
`μ`-stabiliser.  What we need downstream is the coarser fact that `permMon μ π = permMon ν σ`
forces `μ ∘ π⁻¹ = ν ∘ σ⁻¹` pointwise. -/
theorem permMon_eq_iff (μ ν : Fin r → ℕ) (π σ : Equiv.Perm (Fin r)) :
    permMon μ π = permMon ν σ ↔ ∀ j, μ (π.symm j) = ν (σ.symm j) := by
  constructor
  · intro h j
    have := congrArg (fun (f : Fin r →₀ ℕ) => f j) h
    simpa [permMon_apply] using this
  · intro h
    ext j
    rw [permMon_apply, permMon_apply, h]

/-- A single-variable factor reads one univariate coefficient: the `m`-coefficient of
`(descPochhammer ℤ k) ∘ X_j` is the univariate coefficient `(descPochhammer ℤ k).coeff (m j)` when
`m` is supported on `j`, and `0` otherwise. -/
theorem coeff_aeval_X (j : Fin r) (q : Polynomial ℤ) (m : Fin r →₀ ℕ) :
    MvPolynomial.coeff m (Polynomial.aeval (MvPolynomial.X j) q)
      = if m = Finsupp.single j (m j) then q.coeff (m j) else 0 := by
  classical
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def, MvPolynomial.coeff_sum]
  have hstep : ∀ e ∈ q.support,
      MvPolynomial.coeff m ((algebraMap ℤ (MvPolynomial (Fin r) ℤ)) (q.coeff e) * MvPolynomial.X j ^ e)
        = if Finsupp.single j e = m then q.coeff e else 0 := by
    intro e _
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hstep]
  by_cases hm : m = Finsupp.single j (m j)
  · rw [if_pos hm]
    have hcond : ∀ e : ℕ, (Finsupp.single j e = m) ↔ (e = m j) := by
      intro e
      constructor
      · intro h; have := congrArg (fun f : Fin r →₀ ℕ => f j) h; simpa using this
      · intro h; subst h; exact hm.symm
    simp only [hcond]
    rw [Finset.sum_ite_eq' q.support (m j) q.coeff]
    by_cases hmem : m j ∈ q.support
    · rw [if_pos hmem]
    · rw [if_neg hmem]
      rw [Polynomial.mem_support_iff, not_not] at hmem
      exact hmem.symm
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro e _
    rw [if_neg]
    intro h
    exact hm (by rw [← h]; simp)

end GaloisForLFunctions
