import GaloisForLFunctions.HTGeometry.PermanentDistinctSymbol

/-!
# Products of falling factorials in separate variables are linearly independent

The permanent symbol sums the products `∏_s desc_{μ_s}(X_{π s})` over all assignments.  The
descending face argument needs the *unsummed* products themselves: the symbol

```text
descProdSymbol μ = ∏_s (descPochhammer ℤ (μ s)) ∘ X_s
```

has leading monomial `∏_s X_s^{μ_s}` with coefficient one, and every monomial it charges is
componentwise below `μ`.  Two order tuples with the same leading monomial are equal, so a finite
combination of these symbols vanishes only when every coefficient does — the maximal total order
carrying a nonzero coefficient would otherwise survive.

This is the separation of *jet orders* that runs after a node separation has fixed the dilation
tuple: the dilations enter an exponential-polynomial identity through the nodes, the jet orders
through these polynomials.
-/

open Finset

namespace GaloisForLFunctions

noncomputable section

variable {D : ℕ}

/-- The product of falling factorials, one per variable. -/
noncomputable def descProdSymbol (μ : Fin D → ℕ) : MvPolynomial (Fin D) ℤ :=
  ∏ s, Polynomial.aeval (MvPolynomial.X s) (descPochhammer ℤ (μ s))

/-- The coefficients of the symbol factorise over the variables. -/
theorem coeff_descProdSymbol (μ : Fin D → ℕ) (d : Fin D →₀ ℕ) :
    MvPolynomial.coeff d (descProdSymbol μ) = ∏ s, (descPochhammer ℤ (μ s)).coeff (d s) := by
  classical
  rw [descProdSymbol, coeff_prod_aeval_X (fun s => descPochhammer ℤ (μ s)) Finset.univ d,
    if_pos (fun j hj => absurd (Finset.mem_univ j) hj)]

/-- The symbol charges no monomial above its order. -/
theorem coeff_descProdSymbol_eq_zero_of_lt (μ : Fin D → ℕ) (d : Fin D →₀ ℕ)
    {s : Fin D} (hs : μ s < d s) : MvPolynomial.coeff d (descProdSymbol μ) = 0 := by
  classical
  rw [coeff_descProdSymbol]
  refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
  refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
  rw [descPochhammer_natDegree]
  exact hs

/-- The leading coefficient of the symbol is one. -/
theorem coeff_descProdSymbol_self (μ : Fin D → ℕ) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm μ) (descProdSymbol μ) = 1 := by
  classical
  rw [coeff_descProdSymbol]
  refine Finset.prod_eq_one fun s _ => ?_
  have hval : (Finsupp.equivFunOnFinite.symm μ : Fin D → ℕ) s = μ s := rfl
  rw [hval]
  calc (descPochhammer ℤ (μ s)).coeff (μ s)
      = (descPochhammer ℤ (μ s)).coeff (descPochhammer ℤ (μ s)).natDegree := by
        rw [descPochhammer_natDegree]
    _ = 1 := (monic_descPochhammer ℤ (μ s)).coeff_natDegree

/-- A symbol of total order at most `μ₀`'s charges the leading monomial of `μ₀` only if it is
`μ₀`. -/
theorem coeff_descProdSymbol_leading_eq_zero {μ μ₀ : Fin D → ℕ} (hne : μ ≠ μ₀)
    (hle : ∑ s, μ s ≤ ∑ s, μ₀ s) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm μ₀) (descProdSymbol μ) = 0 := by
  classical
  by_cases hdom : ∃ s, μ s < μ₀ s
  · obtain ⟨s, hs⟩ := hdom
    exact coeff_descProdSymbol_eq_zero_of_lt μ _ (by simpa using hs)
  · have hle' : ∀ t, μ₀ t ≤ μ t := fun t => not_lt.mp (not_exists.mp hdom t)
    have heq : μ₀ = μ := by
      by_contra hcontra
      obtain ⟨s, hs⟩ : ∃ s, μ₀ s ≠ μ s := by
        by_contra h2
        exact hcontra (funext fun t => by
          by_contra hne'
          exact h2 ⟨t, hne'⟩)
      have hlt : ∑ t, μ₀ t < ∑ t, μ t :=
        Finset.sum_lt_sum (fun t _ => hle' t)
          ⟨s, Finset.mem_univ s, lt_of_le_of_ne (hle' s) hs⟩
      omega
    exact absurd heq.symm hne

/-- **The falling-factorial products are linearly independent.**  A finite combination of the
symbols with a nonzero coefficient is a nonzero polynomial. -/
theorem descProdSymbol_combination_eq_zero {R : Type*} [CommRing R] [CharZero R]
    (T : Finset (Fin D → ℕ)) (c : (Fin D → ℕ) → R)
    (h : ∑ μ ∈ T, c μ • ((descProdSymbol μ).map (Int.castRingHom R)) = 0) :
    ∀ μ ∈ T, c μ = 0 := by
  classical
  by_contra hcon
  obtain ⟨μbad, hμbadT, hμbad⟩ : ∃ μ ∈ T, c μ ≠ 0 := by
    by_contra h2
    exact hcon fun μ hμ => by
      by_contra hne
      exact h2 ⟨μ, hμ, hne⟩
  set U : Finset (Fin D → ℕ) := T.filter (fun μ => c μ ≠ 0) with hU
  have hUne : U.Nonempty := ⟨μbad, Finset.mem_filter.mpr ⟨hμbadT, hμbad⟩⟩
  obtain ⟨μ₀, hμ₀U, hμ₀max⟩ := U.exists_max_image (fun μ => ∑ s, μ s) hUne
  obtain ⟨hμ₀T, hμ₀c⟩ := Finset.mem_filter.mp hμ₀U
  have hcoeff := congrArg
    (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm μ₀)) h
  rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum] at hcoeff
  have hterm : ∀ μ ∈ T, MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm μ₀)
      (c μ • ((descProdSymbol μ).map (Int.castRingHom R)))
      = if μ = μ₀ then c μ₀ else 0 := by
    intro μ hμT
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map]
    by_cases hμ : μ = μ₀
    · subst hμ
      rw [if_pos rfl, coeff_descProdSymbol_self]
      simp
    · rw [if_neg hμ]
      by_cases hc : c μ = 0
      · rw [hc, smul_eq_mul, zero_mul]
      · have hmem : μ ∈ U := Finset.mem_filter.mpr ⟨hμT, hc⟩
        rw [coeff_descProdSymbol_leading_eq_zero hμ (hμ₀max μ hmem)]
        simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' T μ₀ (fun _ => c μ₀),
    if_pos hμ₀T] at hcoeff
  exact hμ₀c hcoeff

/-- The symbol evaluates to the product of falling factorials. -/
theorem eval_descProdSymbol_map {R : Type*} [CommRing R] (μ : Fin D → ℕ) (k : Fin D → ℕ) :
    MvPolynomial.eval (fun s => ((k s : ℕ) : R)) ((descProdSymbol μ).map (Int.castRingHom R))
      = ∏ s, (((k s).descFactorial (μ s) : ℕ) : R) := by
  classical
  have halg : MvPolynomial.eval (fun s => ((k s : ℕ) : R))
      ((descProdSymbol μ).map (Int.castRingHom R))
      = MvPolynomial.aeval (R := ℤ) (fun s => ((k s : ℕ) : R)) (descProdSymbol μ) := by
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    congr 1
    exact (algebraMap_int_eq).symm
  rw [halg, descProdSymbol, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X, Polynomial.aeval_def,
    Polynomial.eval₂_eq_eval_map, ← algebraMap_int_eq, descPochhammer_map,
    descPochhammer_eval_eq_descFactorial]

end

end GaloisForLFunctions
