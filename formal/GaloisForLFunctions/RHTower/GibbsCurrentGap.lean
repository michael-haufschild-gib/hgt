import Mathlib
import GaloisForLFunctions.RHTower.GibbsParityFactorization

/-!
# The parity current is bounded below by the parity-point zero gap

Evaluating the complete factorization of the gas at the parity activity gives the exact
identity

  `‖J_S(x)‖ = e^{-x·m} · ∏_ζ ‖1 + ζ‖`,   `m = ∏ S`,

over the zeros with multiplicity.  Hence a zero-free disk about the parity point forces a
lower bound on the Möbius–Laplace current,

  `‖J_S(x)‖ ≥ e^{-x·m} · δ^{|S|}`   whenever every zero is at distance `≥ δ` from `-1`,

and, contrapositively, **anomalously small parity current forces a gas zero to condense
onto the parity point**, at an explicit rate.  Both directions hold at every coupling and
without any stability hypothesis: this is the two-sided form of the condensation law.
-/

namespace RHTower.GibbsGas

open Polynomial

/-- The leading coefficient of the gas is the Boltzmann weight of the full
configuration. -/
theorem gibbsPoly_leadingCoeff (S : Finset ℕ) (x : ℝ) :
    (gibbsPoly S x).leadingCoeff = gibbsWeight x S := by
  rw [Polynomial.leadingCoeff, gibbsPoly_natDegree, gibbsPoly_coeff_card]

/-- A uniform lower bound on the factors gives a lower bound on a multiset product. -/
theorem pow_le_prod_of_le (s : Multiset ℂ) (f : ℂ → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ ζ ∈ s, c ≤ f ζ) : c ^ s.card ≤ (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : c ≤ f a := h a (Multiset.mem_cons_self a s)
    have hs : ∀ ζ ∈ s, c ≤ f ζ := fun ζ hζ => h ζ (Multiset.mem_cons_of_mem hζ)
    have hprod : c ^ s.card ≤ (s.map f).prod := ih hs
    have hc0 : (0 : ℝ) ≤ c ^ s.card := pow_nonneg hc _
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc c ^ s.card * c ≤ (s.map f).prod * c := mul_le_mul_of_nonneg_right hprod hc
      _ ≤ (s.map f).prod * f a := by
          refine mul_le_mul_of_nonneg_left ha ?_
          exact le_trans hc0 hprod
      _ = f a * (s.map f).prod := by ring

/-- **The parity current in product form.**  Exact, at every coupling. -/
theorem norm_gibbs_current_eq (S : Finset ℕ) (x : ℝ) :
    ‖gibbsDiagC S x (-1)‖
      = Real.exp (-(x * ∏ p ∈ S, (p : ℝ)))
        * (((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod) := by
  rw [gibbsDiagC_eq_prod_roots, norm_mul, norm_multiset_prod_complex, Multiset.map_map,
    gibbsPoly_leadingCoeff, gibbsWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]
  congr 2
  refine Multiset.map_congr rfl fun ζ _ => ?_
  simp only [Function.comp_apply]
  rw [show (-1 : ℂ) - ζ = -(1 + ζ) from by ring, norm_neg]

/-- **A parity-point zero gap forces a lower bound on the current.**  If no zero of the gas
comes within `δ` of the parity point, the Möbius–Laplace current is at least
`e^{-x·m}·δ^{|S|}`. -/
theorem norm_gibbs_current_ge_of_gap (S : Finset ℕ) (x : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : ∀ ζ : ℂ, gibbsDiagC S x ζ = 0 → δ ≤ ‖1 + ζ‖) :
    Real.exp (-(x * ∏ p ∈ S, (p : ℝ))) * δ ^ S.card
      ≤ ‖gibbsDiagC S x (-1)‖ := by
  rw [norm_gibbs_current_eq]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hroot : ∀ ζ ∈ (gibbsPoly S x).roots, δ ≤ ‖1 + ζ‖ := by
    intro ζ hζ
    refine hgap ζ ?_
    rw [← gibbsPoly_eval]
    exact (Polynomial.mem_roots (gibbsPoly_ne_zero S x)).mp hζ
  have h := pow_le_prod_of_le (gibbsPoly S x).roots (fun ζ => ‖1 + ζ‖) hδ hroot
  rwa [gibbs_roots_card] at h

/-- **Anomalous cancellation forces condensation.**  A parity current below
`e^{-x·m}·δ^{|S|}` cannot occur unless some gas zero lies within `δ` of the parity
point. -/
theorem exists_zero_near_parity_of_small_current (S : Finset ℕ) (x : ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hsmall : ‖gibbsDiagC S x (-1)‖
      < Real.exp (-(x * ∏ p ∈ S, (p : ℝ))) * δ ^ S.card) :
    ∃ ζ : ℂ, gibbsDiagC S x ζ = 0 ∧ ‖1 + ζ‖ < δ := by
  by_contra hcon
  rw [not_exists] at hcon
  have hgap : ∀ ζ : ℂ, gibbsDiagC S x ζ = 0 → δ ≤ ‖1 + ζ‖ := by
    intro ζ hζ
    have := hcon ζ
    rw [not_and, not_lt] at this
    exact this hζ
  have := norm_gibbs_current_ge_of_gap S x hδ hgap
  linarith

/-- The partition function in the same product form: the two together are the condensation
law in its sharpest shape. -/
theorem norm_gibbs_partition_eq (S : Finset ℕ) (x : ℝ) :
    ‖gibbsDiagC S x 1‖
      = Real.exp (-(x * ∏ p ∈ S, (p : ℝ)))
        * (((gibbsPoly S x).roots.map (fun ζ => ‖1 - ζ‖)).prod) := by
  rw [gibbsDiagC_eq_prod_roots, norm_mul, norm_multiset_prod_complex, Multiset.map_map,
    gibbsPoly_leadingCoeff, gibbsWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]
  congr 2

end RHTower.GibbsGas
