import GaloisForLFunctions.HTGeometry.DistinctIndexComplexSurvival
import GaloisForLFunctions.HTGeometry.MagnitudeADEBridge

/-!
# Formal hypertranscendence of a superlacunary gap series

A power series `F` with support on a superlacunary gap set satisfies no nonzero formal algebraic
differential relation `aeval (formalJets n F) Q = 0` with `Q ≠ 0` over `ℂ`.  The proof isolates the
top-degree fixed-`κ` group of monomials at a distinct-scale probe: the `Xᵐ⁰` shift aligns every order
in the group at one coefficient index, so the group contributes the complex permanent combination
`combination_permSymbolPolyC_ne_zero` (nonzero), while every other monomial vanishes by the window or
wrong-degree vanishing lemmas.

`flatten_jet_power_product_multiset` records the order-multiset of the flattened tuple, which supplies
the distinctness the permanent combination requires.
-/

open PowerSeries Finset MvPolynomial
open scoped Nat

namespace GaloisForLFunctions

/-- **Flattened order-multiset.**  A power product `∏ⱼ (F⁽ʲ⁾)^{eⱼ}` flattens to a `Fin (∑ e)` tuple of
single jets whose order-multiset is `∑ⱼ eⱼ • {j}` — each derivation order `j` occurs with multiplicity
`eⱼ`.  This determines `e` from the multiset, hence separates distinct power products. -/
theorem flatten_jet_power_product_multiset (n : ℕ) (F : ℂ⟦X⟧) (e : Fin (n + 1) → ℕ) :
    ∃ (μ : Fin (∑ j, e j) → ℕ),
      (∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (e j)
        = ∏ i : Fin (∑ j, e j), (⇑(d⁄dX ℂ))^[μ i] F)
      ∧ Multiset.map μ (Finset.univ : Finset (Fin (∑ j, e j))).val
          = ∑ j : Fin (n + 1), Multiset.replicate (e j) (j : ℕ) := by
  classical
  have hcard : Fintype.card (Σ j : Fin (n + 1), Fin (e j)) = ∑ j, e j := by
    rw [Fintype.card_sigma]; simp
  set eqv : Fin (∑ j, e j) ≃ (Σ j : Fin (n + 1), Fin (e j)) :=
    (Fintype.equivFinOfCardEq hcard).symm with heqv
  refine ⟨fun i => ((eqv i).1 : ℕ), ?_, ?_⟩
  · have hsig : ∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (e j)
        = ∏ p : (Σ j : Fin (n + 1), Fin (e j)), (⇑(d⁄dX ℂ))^[((p.1 : ℕ))] F := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hsig, ← Equiv.prod_comp eqv]
  · rw [show (Finset.univ : Finset (Fin (∑ j, e j))).val
          = Multiset.map eqv.symm (Finset.univ : Finset (Σ j : Fin (n + 1), Fin (e j))).val from by
        rw [← Finset.map_univ_equiv eqv.symm]; rfl]
    rw [Multiset.map_map,
      show (fun i => ((eqv i).1 : ℕ)) ∘ eqv.symm = fun p => ((p.1 : ℕ)) from by funext p; simp]
    ext k
    rw [Multiset.count_map, Multiset.count_sum']
    simp only [Multiset.count_replicate]
    rw [← Finset.filter_val, Finset.card_val, Finset.card_filter, ← Finset.univ_sigma_univ,
      Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : k = (j : ℕ) <;> simp [h, eq_comm]

/-- Arity-parameterized flattened order-multiset: for a target degree `D = ∑ e`. -/
theorem flatten_jet_power_product_multiset' (n : ℕ) (F : ℂ⟦X⟧) (e : Fin (n + 1) → ℕ) (D : ℕ)
    (hD : ∑ j, e j = D) :
    ∃ (μ : Fin D → ℕ),
      (∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (e j) = ∏ i : Fin D, (⇑(d⁄dX ℂ))^[μ i] F)
      ∧ Multiset.map μ (Finset.univ : Finset (Fin D)).val
          = ∑ j : Fin (n + 1), Multiset.replicate (e j) (j : ℕ) := by
  subst hD
  exact flatten_jet_power_product_multiset n F e

end GaloisForLFunctions
