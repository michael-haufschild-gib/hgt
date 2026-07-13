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

/-- The `N`-th coefficient of a jet monomial's evaluation is the `(N−m₀)`-th coefficient of the
derivative power product, shifted by the `X`-degree `m₀` (zero when `m₀ > N`). -/
theorem coeff_aeval_monomial_shift (n N : ℕ) (F : ℂ⟦X⟧) (m : Fin (n + 2) →₀ ℕ) :
    (coeff N) (aeval (formalJets n F) (monomial m (1 : ℂ)))
      = if m 0 ≤ N then
          (coeff (N - m 0)) (∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (m j.succ))
        else 0 := by
  rw [aeval_formalJets_monomial_eq]
  split_ifs with h
  · rw [PowerSeries.coeff_X_pow_mul']
    simp [h]
  · rw [PowerSeries.coeff_X_pow_mul']
    simp [h]

/-- `coeff N` of an ADE evaluation as a support sum of `X`-degree-shifted derivative-power
coefficients — the base form for magnitude domination. -/
theorem coeff_aeval_eq_shifted_sum (n N : ℕ) (F : ℂ⟦X⟧) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    (coeff N) (aeval (formalJets n F) Q)
      = ∑ m ∈ Q.support, MvPolynomial.coeff m Q
          * (if m 0 ≤ N then
              (coeff (N - m 0)) (∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (m j.succ))
             else 0) := by
  rw [coeff_aeval_eq_support_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [PowerSeries.coeff_X_pow_mul']

/-- The `M`-th coefficient of a derivative-jet power product equals that of its flattened
equal-degree tuple product. -/
theorem coeff_jet_power_eq_flat (n M : ℕ) (F : ℂ⟦X⟧) (e : Fin (n + 1) → ℕ) :
    ∃ (μ : Fin (∑ j, e j) → ℕ),
      (coeff M) (∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (e j))
        = (coeff M) (∏ i : Fin (∑ j, e j), (⇑(d⁄dX ℂ))^[μ i] F) := by
  obtain ⟨μ, hμ⟩ := flatten_jet_power_product n F e
  exact ⟨μ, by rw [hμ]⟩

/-- A jet monomial's `N`-th evaluation coefficient equals the `(N−m₀)`-th coefficient of a
flat single-jet product of degree `∑ⱼ m(j+1)` (zero when `m₀ > N`) — the atom-level bridge from a
formal ADE monomial to the flat differential-monomial form. -/
theorem coeff_aeval_monomial_eq_flat (n N : ℕ) (F : ℂ⟦X⟧) (m : Fin (n + 2) →₀ ℕ) :
    ∃ (μ : Fin (∑ j : Fin (n + 1), m j.succ) → ℕ),
      (coeff N) (aeval (formalJets n F) (monomial m (1 : ℂ)))
        = if m 0 ≤ N then
            (coeff (N - m 0)) (∏ i : Fin (∑ j : Fin (n + 1), m j.succ), (⇑(d⁄dX ℂ))^[μ i] F)
          else 0 := by
  obtain ⟨μ, hμ⟩ := coeff_jet_power_eq_flat n (N - m 0) F (fun j => m j.succ)
  refine ⟨μ, ?_⟩
  rw [coeff_aeval_monomial_shift]
  split_ifs with h
  · exact hμ
  · rfl

/-- Canonical flattening of a jet-order profile `e` into a `Fin (∑ e)` order tuple. -/
noncomputable def flatOrder {n : ℕ} (e : Fin (n + 1) → ℕ) : Fin (∑ j, e j) → ℕ :=
  fun i => (((Fintype.equivFinOfCardEq (by rw [Fintype.card_sigma]; simp :
      Fintype.card (Σ j : Fin (n + 1), Fin (e j)) = ∑ j, e j)).symm i).1 : ℕ)

theorem prod_jet_eq_flatOrder {n : ℕ} (F : ℂ⟦X⟧) (e : Fin (n + 1) → ℕ) :
    ∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (e j)
      = ∏ i : Fin (∑ j, e j), (⇑(d⁄dX ℂ))^[flatOrder e i] F := by
  classical
  set hcard : Fintype.card (Σ j : Fin (n + 1), Fin (e j)) = ∑ j, e j := by
    rw [Fintype.card_sigma]; simp
  set eqv := (Fintype.equivFinOfCardEq hcard).symm with heqv
  have hsig : ∏ j : Fin (n + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ (e j)
      = ∏ p : (Σ j : Fin (n + 1), Fin (e j)), (⇑(d⁄dX ℂ))^[((p.1 : ℕ))] F := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hsig, ← Equiv.prod_comp eqv]
  rfl

/-- Jet-monomial evaluation coefficient via the canonical flattening `flatOrder`. -/
theorem coeff_aeval_monomial_flatOrder (n N : ℕ) (F : ℂ⟦X⟧) (m : Fin (n + 2) →₀ ℕ) :
    (coeff N) (aeval (formalJets n F) (monomial m (1 : ℂ)))
      = if m 0 ≤ N then
          (coeff (N - m 0)) (∏ i : Fin (∑ j : Fin (n + 1), m j.succ),
            (⇑(d⁄dX ℂ))^[flatOrder (fun j => m j.succ) i] F)
        else 0 := by
  rw [coeff_aeval_monomial_shift]
  split_ifs with h
  · rw [prod_jet_eq_flatOrder]
  · rfl

/-- Jet-monomial evaluation coefficient fully expanded as an antidiagonal convolution sum over
the flattened order tuple — the atom-level `(shift, l)` form feeding magnitude domination. -/
theorem coeff_aeval_monomial_pair_sum (n N : ℕ) (F : ℂ⟦X⟧) (m : Fin (n + 2) →₀ ℕ) :
    (coeff N) (aeval (formalJets n F) (monomial m (1 : ℂ)))
      = if m 0 ≤ N then
          ∑ l ∈ (Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag
              (N - m 0),
            ∏ t, (coeff (l t + flatOrder (fun j => m j.succ) t)) F
              * (((l t + flatOrder (fun j => m j.succ) t).descFactorial
                  (flatOrder (fun j => m j.succ) t) : ℂ))
        else 0 := by
  rw [coeff_aeval_monomial_flatOrder]
  split_ifs with h
  · rw [coeff_prod_iterate_deriv]
  · rfl

/-- **Fully expanded ADE evaluation coefficient.**  `coeff N (aeval Q)` as a support sum of
complex coefficients times antidiagonal convolutions of the flattened order tuples — the complete
atom decomposition over `(monomial, shift, l)` feeding magnitude domination. -/
theorem coeff_aeval_eq_full_pair_sum (n N : ℕ) (F : ℂ⟦X⟧) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    (coeff N) (aeval (formalJets n F) Q)
      = ∑ m ∈ Q.support, MvPolynomial.coeff m Q *
          (if m 0 ≤ N then
            ∑ l ∈ (Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag
                (N - m 0),
              ∏ t, (coeff (l t + flatOrder (fun j => m j.succ) t)) F
                * (((l t + flatOrder (fun j => m j.succ) t).descFactorial
                    (flatOrder (fun j => m j.succ) t) : ℂ))
           else 0) := by
  rw [coeff_aeval_eq_shifted_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  split_ifs with h
  · rw [prod_jet_eq_flatOrder, coeff_prod_iterate_deriv]
  · rfl

end GaloisForLFunctions
