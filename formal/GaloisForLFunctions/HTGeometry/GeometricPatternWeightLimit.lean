import GaloisForLFunctions.HTGeometry.GeometricPatternPhase
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Leading limits of finite ADE pattern-weight families

The grouped weight of each fixed bounded ADE pattern is a complex polynomial in the translation
index.  This module normalizes a finite family by its common maximal degree and proves convergence
to the corresponding top coefficients, with at least one nonzero limiting weight.
-/

namespace GaloisForLFunctions

open Filter Finset PowerSeries Polynomial Topology

noncomputable section

/-- A complex polynomial divided by its top real monomial tends to its leading coefficient. -/
theorem tendsto_complexPolynomial_eval_div_pow_natDegree (P : ℂ[X]) :
    Tendsto (fun t : ℝ => P.eval (t : ℂ) / (t : ℂ) ^ P.natDegree)
      atTop (𝓝 P.leadingCoeff) := by
  have hinv : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_inv_atTop_zero
  have hrev : Tendsto (fun t : ℝ => P.reverse.eval ((t⁻¹ : ℝ) : ℂ))
      atTop (𝓝 P.leadingCoeff) := by
    convert! P.reverse.continuous.continuousAt.tendsto.comp hinv using 1
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
  apply hrev.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  letI : Invertible (t : ℂ) := invertibleOfNonzero ht0
  have hreverse := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (t : ℂ) P
  have hinvcast : ⅟(t : ℂ) = ((t⁻¹ : ℝ) : ℂ) := by
    apply invOf_eq_right_inv
    norm_cast
    exact mul_inv_cancel₀ ht.ne'
  rw [hinvcast] at hreverse
  simp only [Polynomial.eval₂_id] at hreverse
  rw [← hreverse]
  field_simp

/-- Division by any monomial of degree at least the polynomial degree selects that coefficient. -/
theorem tendsto_complexPolynomial_eval_div_pow
    (P : ℂ[X]) {d : ℕ} (hd : P.natDegree ≤ d) :
    Tendsto (fun t : ℝ => P.eval (t : ℂ) / (t : ℂ) ^ d)
      atTop (𝓝 (P.coeff d)) := by
  by_cases heq : P.natDegree = d
  · subst d
    simpa only [Polynomial.coeff_natDegree] using
      tendsto_complexPolynomial_eval_div_pow_natDegree P
  · have hlt : P.natDegree < d := lt_of_le_of_ne hd heq
    let e := d - P.natDegree
    have he : 0 < e := by dsimp [e]; omega
    have hlead := tendsto_complexPolynomial_eval_div_pow_natDegree P
    have hinv : Tendsto (fun t : ℝ => ((t : ℂ) ^ e)⁻¹) atTop (𝓝 0) := by
      have hinv1 : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
        simpa [Function.comp_def] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_inv_atTop_zero
      have hpow := hinv1.pow e
      simpa [map_inv₀, he.ne'] using hpow
    have hmul := hlead.mul hinv
    have hmul0 : Tendsto
        (fun x : ℝ => P.eval (x : ℂ) / (x : ℂ) ^ P.natDegree *
          ((x : ℂ) ^ e)⁻¹) atTop (𝓝 0) := by
      simpa using hmul
    have hcoeff : P.coeff d = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    rw [hcoeff]
    apply hmul0.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hdecomp : P.natDegree + e = d := by dsimp [e]; omega
    rw [← hdecomp, pow_add]
    field_simp

/-- Natural translation indices have the same normalized polynomial limit. -/
theorem tendsto_complexPolynomial_eval_nat_div_pow
    (P : ℂ[X]) {d : ℕ} (hd : P.natDegree ≤ d) :
    Tendsto (fun q : ℕ => P.eval (q : ℂ) / (q : ℂ) ^ d)
      atTop (𝓝 (P.coeff d)) :=
  (tendsto_complexPolynomial_eval_div_pow P hd).comp tendsto_natCast_atTop_atTop

/-- Maximal degree of a finite polynomial family. -/
def finitePolynomialFamilyMaxDegree
    {α : Type*} [DecidableEq α] (S : Finset α) (P : α → ℂ[X]) : ℕ :=
  S.sup fun a => (P a).natDegree

/-- Limiting normalized weight of one member of a finite polynomial family. -/
def finitePolynomialFamilyLimit
    {α : Type*} [DecidableEq α] (S : Finset α) (P : α → ℂ[X])
    (a : α) : ℂ :=
  (P a).coeff (finitePolynomialFamilyMaxDegree S P)

theorem tendsto_finitePolynomialFamily_eval_nat_div_pow
    {α : Type*} [DecidableEq α] (S : Finset α) (P : α → ℂ[X])
    {a : α} (ha : a ∈ S) :
    Tendsto (fun q : ℕ =>
      (P a).eval (q : ℂ) / (q : ℂ) ^ finitePolynomialFamilyMaxDegree S P)
      atTop (𝓝 (finitePolynomialFamilyLimit S P a)) := by
  exact tendsto_complexPolynomial_eval_nat_div_pow (P a)
    (Finset.le_sup (f := fun x => (P x).natDegree) ha)

/-- If every polynomial on a nonempty finite family is nonzero, at least one normalized limiting
weight is nonzero. -/
theorem exists_ne_zero_finitePolynomialFamilyLimit
    {α : Type*} [DecidableEq α] (S : Finset α) (P : α → ℂ[X])
    (hS : S.Nonempty) (hP : ∀ a ∈ S, P a ≠ 0) :
    ∃ a ∈ S, finitePolynomialFamilyLimit S P a ≠ 0 := by
  obtain ⟨a, ha, hdegree⟩ :=
    Finset.exists_mem_eq_sup S hS (fun x => (P x).natDegree)
  refine ⟨a, ha, ?_⟩
  rw [finitePolynomialFamilyLimit, finitePolynomialFamilyMaxDegree, hdegree]
  exact Polynomial.leadingCoeff_ne_zero.mpr (hP a ha)

end

end GaloisForLFunctions
