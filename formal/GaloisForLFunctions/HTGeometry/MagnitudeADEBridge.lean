import GaloisForLFunctions.HTGeometry.FormalMahlerDescent
import GaloisForLFunctions.HTGeometry.MagnitudeConvolutionExtraction

/-!
# Bridge from a formal ADE monomial to a differential-monomial tuple product

`analytic_mahler_descent` produces the annihilating relation as an `MvPolynomial (Fin (n+2)) ℂ`
evaluated on the formal jets `(X, F, F', …, F⁽ⁿ⁾)`.  To feed the magnitude-survival engine (which
speaks of `∏ₜ (d⁄dX)^[μₜ] F` over a `Fin d` tuple), each monomial is rewritten:

* `aeval_formalJets_monomial_eq` — a jet monomial evaluates to `Xᵐ⁰ · ∏ⱼ (F⁽ʲ⁾)^{m(j+1)}`;
* `flatten_jet_power_product` — the power product `∏ⱼ (F⁽ʲ⁾)^{eⱼ}` equals a flat product
  `∏_{i:Fin (∑ e)} (d⁄dX)^[μ i] F` over the enumerated order-multiset.

Together with the `Xᵐ⁰` coefficient shift, `coeff N` of a jet monomial becomes a `Fin d`
antidiagonal convolution, exactly the input to `coeff_prod_iterate_deriv`.
-/

open PowerSeries Finset MvPolynomial
open scoped Nat

namespace GaloisForLFunctions

/-- A formal-jet monomial evaluates to `Xᵐ⁰` times a power product of the derivative jets. -/
theorem aeval_formalJets_monomial_eq (n : ℕ) (F : ℂ⟦X⟧) (m : Fin (n + 2) →₀ ℕ) :
    aeval (formalJets n F) (monomial m (1 : ℂ))
      = (PowerSeries.X) ^ (m 0) * ∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (m j.succ) := by
  rw [aeval_monomial, map_one, one_mul, formalJets]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp)]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A power product of derivative jets flattens to a `Fin (∑ e)` tuple product of single jets,
enumerating each order `j` with multiplicity `eⱼ`. -/
theorem flatten_jet_power_product (n : ℕ) (F : ℂ⟦X⟧) (e : Fin (n + 1) → ℕ) :
    ∃ (μ : Fin (∑ j, e j) → ℕ),
      ∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (e j)
        = ∏ i : Fin (∑ j, e j), (⇑(d⁄dX ℂ))^[μ i] F := by
  classical
  have hcard : Fintype.card (Σ j : Fin (n + 1), Fin (e j)) = ∑ j, e j := by
    rw [Fintype.card_sigma]; simp
  set eqv : Fin (∑ j, e j) ≃ (Σ j : Fin (n + 1), Fin (e j)) :=
    (Fintype.equivFinOfCardEq hcard).symm with heqv
  refine ⟨fun i => ((eqv i).1 : ℕ), ?_⟩
  have hsig : ∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (e j)
      = ∏ p : (Σ j : Fin (n + 1), Fin (e j)), (⇑(d⁄dX ℂ))^[((p.1 : ℕ))] F := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hsig, ← Equiv.prod_comp eqv]

/-- Coefficient of a formal-ADE evaluation, expanded over the polynomial support: each monomial
contributes its `X^{m 0}`-shifted derivative power product. -/
theorem coeff_aeval_eq_support_sum (n N : ℕ) (F : ℂ⟦X⟧) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    (coeff N) (aeval (formalJets n F) Q)
      = ∑ m ∈ Q.support, MvPolynomial.coeff m Q
          * (coeff N) ((PowerSeries.X) ^ (m 0)
              * ∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (m j.succ)) := by
  rw [aeval_formalJets_as_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_eq_mul, aeval_formalJets_monomial_eq]

/-- Combined bridge: below the leading `X^{m 0}` shift, `coeff N` of a jet monomial is the
`(N − m 0)`-th coefficient of a flat `Fin d` product of derivative jets — exactly the input to
`coeff_prod_iterate_deriv`. -/
theorem coeff_aeval_monomial_flattened (n N : ℕ) (F : ℂ⟦X⟧) (m : Fin (n + 2) →₀ ℕ)
    (hm : m 0 ≤ N) :
    ∃ (μ : Fin (∑ j : Fin (n + 1), m j.succ) → ℕ),
      (coeff N) (aeval (formalJets n F) (monomial m (1 : ℂ)))
        = (coeff (N - m 0)) (∏ i : Fin (∑ j : Fin (n + 1), m j.succ), (⇑(d⁄dX ℂ))^[μ i] F) := by
  obtain ⟨μ, hμ⟩ := flatten_jet_power_product n F (fun j => m j.succ)
  refine ⟨μ, ?_⟩
  rw [aeval_formalJets_monomial_eq, hμ]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show m 0 + d = d + m 0 by omega, PowerSeries.coeff_X_pow_mul, Nat.add_sub_cancel]

end GaloisForLFunctions
