import GaloisForLFunctions.HTGeometry.MagnitudeConvolutionExtraction

/-!
# Flattening the jet monomials of a family of power series

The magnitude apparatus expands `coeff N (aeval (formalJets n F) Q)` by flattening a jet-exponent
profile into a tuple of derivative orders.  For a *family* of sources the same flattening is needed,
except that each slot of the flattened tuple must remember which member of the family it came from.

* `flatIndex` — the flattening of an exponent profile on any finite variable type, returning the
  variable attached to each slot;
* `prod_pow_eq_flatIndex` — a power product is the flat product over the slots;
* `coeff_prod_iterate_deriv_family` — the antidiagonal convolution for a product of iterated
  derivatives of *different* series;
* `familyJets`, `aeval_familyJets_monomial`, `coeff_aeval_familyJets_monomial_shift` — the jet
  vector of a family and the shifted coefficient of one of its monomials.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

noncomputable section

/-! ### Flattening an exponent profile on a finite variable type -/

/-- Canonical flattening of an exponent profile `e` on a finite variable type: slot `t` of
`Fin (∑ e)` carries the variable it was split off from. -/
noncomputable def flatIndex {σ : Type*} [Fintype σ] (e : σ → ℕ) : Fin (∑ j, e j) → σ :=
  fun i => ((Fintype.equivFinOfCardEq (by rw [Fintype.card_sigma]; simp :
      Fintype.card (Σ j : σ, Fin (e j)) = ∑ j, e j)).symm i).1

/-- A power product over a finite variable type is the flat product over its slots. -/
theorem prod_pow_eq_flatIndex {σ : Type*} [Fintype σ] {M : Type*} [CommMonoid M]
    (g : σ → M) (e : σ → ℕ) :
    ∏ j, (g j) ^ (e j) = ∏ t : Fin (∑ j, e j), g (flatIndex e t) := by
  classical
  set hcard : Fintype.card (Σ j : σ, Fin (e j)) = ∑ j, e j := by
    rw [Fintype.card_sigma]; simp
  set eqv := (Fintype.equivFinOfCardEq hcard).symm with heqv
  have hsig : ∏ j, (g j) ^ (e j) = ∏ p : (Σ j : σ, Fin (e j)), g p.1 := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hsig, ← Equiv.prod_comp eqv]
  rfl

/-! ### The convolution for a product of derivatives of different series -/

/-- **Family differential-monomial convolution.**  The `N`-th coefficient of `∏ₜ f_t^{(jₜ)}` is the
antidiagonal sum of falling-factorial-weighted products of the sources' coefficients. -/
theorem coeff_prod_iterate_deriv_family {r : ℕ} (f : Fin r → ℂ⟦X⟧) (j : Fin r → ℕ) (N : ℕ) :
    (coeff N) (∏ t, (⇑(d⁄dX ℂ))^[j t] (f t))
      = ∑ l ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N,
          ∏ t, (coeff (l t + j t)) (f t) * (((l t + j t).descFactorial (j t) : ℂ)) := by
  classical
  rw [coeff_prod]
  exact Finset.sum_congr rfl fun l _ =>
    Finset.prod_congr rfl fun t _ => coeff_iterate_deriv (f t) (j t) (l t)

/-! ### The jet vector of a family -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The formal jet vector of a family of power series: the point slot carries `X`, the slot
`(i, j)` the `j`-th formal derivative of the `i`-th member. -/
noncomputable def familyJets (n : ℕ) (f : ι → ℂ⟦X⟧) : Option (ι × Fin (n + 1)) → ℂ⟦X⟧
  | none => PowerSeries.X
  | some p => (⇑(d⁄dX ℂ))^[(p.2 : ℕ)] (f p.1)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem familyJets_none (n : ℕ) (f : ι → ℂ⟦X⟧) :
    familyJets n f none = PowerSeries.X := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem familyJets_some (n : ℕ) (f : ι → ℂ⟦X⟧) (p : ι × Fin (n + 1)) :
    familyJets n f (some p) = (⇑(d⁄dX ℂ))^[(p.2 : ℕ)] (f p.1) := rfl

omit [DecidableEq ι] in
/-- Evaluation of a jet monomial of a family. -/
theorem aeval_familyJets_monomial (n : ℕ) (f : ι → ℂ⟦X⟧)
    (m : Option (ι × Fin (n + 1)) →₀ ℕ) :
    aeval (familyJets n f) (monomial m (1 : ℂ))
      = PowerSeries.X ^ (m none)
        * ∏ p : ι × Fin (n + 1), ((⇑(d⁄dX ℂ))^[(p.2 : ℕ)] (f p.1)) ^ (m (some p)) := by
  classical
  rw [MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_option]
  rfl

omit [DecidableEq ι] in
/-- The `N`-th coefficient of a family jet monomial, shifted by its `X`-degree. -/
theorem coeff_aeval_familyJets_monomial_shift (n N : ℕ) (f : ι → ℂ⟦X⟧)
    (m : Option (ι × Fin (n + 1)) →₀ ℕ) :
    (coeff N) (aeval (familyJets n f) (monomial m (1 : ℂ)))
      = if m none ≤ N then
          (coeff (N - m none))
            (∏ p : ι × Fin (n + 1), ((⇑(d⁄dX ℂ))^[(p.2 : ℕ)] (f p.1)) ^ (m (some p)))
        else 0 := by
  rw [aeval_familyJets_monomial]
  split_ifs with h
  · rw [PowerSeries.coeff_X_pow_mul']
    simp [h]
  · rw [PowerSeries.coeff_X_pow_mul']
    simp [h]

end

end GaloisForLFunctions
