import Mathlib

/-!
# The top symbol of an algebraic relation

Dividing an algebraic relation `∑ A_{b,c} F^b W^c = 0` by `F^d`, where `d` bounds every total degree
`b + c`, converts each monomial into `A_{b,c} T^c / F^{d-b-c}` with `T = W/F`.  The monomials of
maximal total degree lose their denominator entirely and assemble into the **top symbol**
`∑_{b+c=d} A_{b,c} T^c`; every other monomial keeps a denominator of at least `F`.

The result is an unconditional inequality: the top symbol is at most the remaining weight divided by
`‖F‖`.  Applied at a Wiman--Valiron point, where `‖F‖ = ‖f(z)‖` outgrows every power of the radius
and of the central index while `T = f'/f` is comparable with `ν/z`, it says that the top symbol is
small — the step that turns a differential equation into a relation between the central index and
the coefficients alone.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- **Dividing a monomial by a power of the value.**  With `T = W/F` a monomial of total degree
`b + c ≤ d` divided by `F^d` becomes `A T^c` divided by `F^{d-b-c}`. -/
theorem monomial_div_pow {A F W : ℂ} (hF : F ≠ 0) {b c d : ℕ} (h : b + c ≤ d) :
    A * F ^ b * W ^ c / F ^ d = A * (W / F) ^ c / F ^ (d - b - c) := by
  have hFsplit : (F : ℂ) ^ d = F ^ b * F ^ c * F ^ (d - b - c) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [div_pow, hFsplit]
  field_simp

/-- The top-degree part of a relation carries no denominator. -/
theorem monomial_div_pow_top {A F W : ℂ} (hF : F ≠ 0) {b c d : ℕ} (h : b + c = d) :
    A * F ^ b * W ^ c / F ^ d = A * (W / F) ^ c := by
  have hle : b + c ≤ d := le_of_eq h
  rw [monomial_div_pow hF hle]
  have hz : d - b - c = 0 := by omega
  rw [hz, pow_zero, div_one]

/-- **The top symbol is small.**  If an algebraic relation of total degree at most `d` holds at a
point where the value `F` has modulus at least one, then the top symbol evaluated at `T = W/F` is at
most the remaining weight divided by `‖F‖`. -/
theorem norm_topSymbol_le {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → ℂ} {F W : ℂ} {d : ℕ}
    (hF : F ≠ 0) (hF1 : 1 ≤ ‖F‖)
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∑ p ∈ S, A p * F ^ p.1 * W ^ p.2 = 0) :
    ‖∑ p ∈ S.filter (fun p => p.1 + p.2 = d), A p * (W / F) ^ p.2‖
      ≤ (∑ p ∈ S.filter (fun p => ¬ p.1 + p.2 = d), ‖A p‖ * ‖W / F‖ ^ p.2) / ‖F‖ := by
  classical
  have hFd : (F : ℂ) ^ d ≠ 0 := pow_ne_zero d hF
  have hFpos : (0 : ℝ) < ‖F‖ := lt_of_lt_of_le one_pos hF1
  -- divide the relation by `F ^ d`
  have hdiv : ∑ p ∈ S, A p * F ^ p.1 * W ^ p.2 / F ^ d = 0 := by
    rw [← Finset.sum_div, hrel, zero_div]
  have hterm : ∀ p ∈ S, A p * F ^ p.1 * W ^ p.2 / F ^ d
      = A p * (W / F) ^ p.2 / F ^ (d - p.1 - p.2) := fun p hp => monomial_div_pow hF (hdeg p hp)
  rw [Finset.sum_congr rfl hterm] at hdiv
  -- split into the top-degree part and the rest
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun p => p.1 + p.2 = d)
    (fun p => A p * (W / F) ^ p.2 / F ^ (d - p.1 - p.2))
  have htop : ∑ p ∈ S.filter (fun p => p.1 + p.2 = d),
        A p * (W / F) ^ p.2 / F ^ (d - p.1 - p.2)
      = ∑ p ∈ S.filter (fun p => p.1 + p.2 = d), A p * (W / F) ^ p.2 := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hpd : p.1 + p.2 = d := (Finset.mem_filter.mp hp).2
    have hz : d - p.1 - p.2 = 0 := by omega
    rw [hz, pow_zero, div_one]
  rw [htop] at hsplit
  -- the top symbol equals minus the remainder
  have heq : ∑ p ∈ S.filter (fun p => p.1 + p.2 = d), A p * (W / F) ^ p.2
      = -∑ p ∈ S.filter (fun p => ¬ p.1 + p.2 = d),
          A p * (W / F) ^ p.2 / F ^ (d - p.1 - p.2) := by
    rw [hdiv] at hsplit
    exact add_eq_zero_iff_eq_neg.mp hsplit
  rw [heq, norm_neg]
  -- bound the remainder termwise
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum ?_
  intro p hp
  have hne : ¬ p.1 + p.2 = d := (Finset.mem_filter.mp hp).2
  have hmem : p ∈ S := (Finset.mem_filter.mp hp).1
  have hle : p.1 + p.2 ≤ d := hdeg p hmem
  have hpos : 1 ≤ d - p.1 - p.2 := by omega
  have hnorm : ‖A p * (W / F) ^ p.2 / F ^ (d - p.1 - p.2)‖
      = ‖A p‖ * ‖W / F‖ ^ p.2 / ‖F‖ ^ (d - p.1 - p.2) := by
    rw [norm_div, norm_mul, norm_pow, norm_pow]
  rw [hnorm]
  have hden : ‖F‖ ≤ ‖F‖ ^ (d - p.1 - p.2) := by
    calc ‖F‖ = ‖F‖ ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ ‖F‖ ^ (d - p.1 - p.2) := pow_le_pow_right₀ hF1 hpos
  have hnum : (0 : ℝ) ≤ ‖A p‖ * ‖W / F‖ ^ p.2 := by positivity
  exact div_le_div_of_nonneg_left hnum hFpos hden

/-! ## Polynomial coefficients on a large circle -/

/-- **A polynomial is bounded by its coefficient sum times a power of the point.**  Outside the unit
disc every monomial of a polynomial is at most `‖z‖` to the top degree. -/
theorem norm_eval_le_of_one_le {p : Polynomial ℂ} {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖p.eval z‖ ≤ (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * ‖z‖ ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hile : i ≤ p.natDegree := by
    have := Finset.mem_range.mp hi
    omega
  have hpow : ‖z‖ ^ i ≤ ‖z‖ ^ p.natDegree := pow_le_pow_right₀ hz hile
  calc ‖p.coeff i * z ^ i‖ = ‖p.coeff i‖ * ‖z‖ ^ i := by rw [norm_mul, norm_pow]
    _ ≤ ‖p.coeff i‖ * ‖z‖ ^ p.natDegree := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)

end GaloisForLFunctions.HTGeometry
