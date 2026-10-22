import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysNormalizedIrreducible
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittGaloisIntegrallyClosed

/-!
# Root multiplicities of the reversed polynomial

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §1.

Reversal exchanges the normalization "constant coefficient `1`" with monicity, and it inverts the
roots: `X - r` becomes `1 - r X = (-r) (X - r⁻¹)`, whose second factor is again linear.  Since
reversal is multiplicative on a domain, `(X - r) ^ n ∣ p` is equivalent to
`(X - r⁻¹) ^ n ∣ p.reverse`, so the multiplicity of `r` in `p` equals the multiplicity of `r⁻¹` in
`p.reverse`.

This is the bridge between the atoms `(a)` of Deninger's `ℤ̲κ` — which are inverse roots of a
normalized polynomial — and minimal polynomials, whose root multiplicities are the degrees of
inseparability.
-/

namespace RHTower

open Polynomial

variable {K : Type*} [Field K]

/-- Reversal of a linear polynomial. -/
theorem deningerReverse_X_sub_C (r : K) :
    (Polynomial.X - Polynomial.C r).reverse = 1 - Polynomial.C r * Polynomial.X := by
  have hdeg : (Polynomial.X - Polynomial.C r).natDegree = 1 := Polynomial.natDegree_X_sub_C r
  ext n
  rw [Polynomial.coeff_reverse, hdeg]
  match n with
  | 0 => simp [Polynomial.revAt]
  | 1 =>
      simp only [Polynomial.revAt_le (by omega : (1:ℕ) ≤ 1)]
      simp [Polynomial.coeff_one]
  | (k + 2) =>
      have h1 : Polynomial.revAt 1 (k + 2) = k + 2 := Polynomial.revAt_eq_self_of_lt (by omega)
      rw [h1]
      simp [Polynomial.coeff_X, Polynomial.coeff_one]

/-- Reversal turns a linear factor into a linear factor at the inverse root. -/
theorem deningerReverse_X_sub_C_eq (r : K) (hr : r ≠ 0) :
    (Polynomial.X - Polynomial.C r).reverse
      = (-Polynomial.C r) * (Polynomial.X - Polynomial.C r⁻¹) := by
  rw [deningerReverse_X_sub_C]
  rw [mul_sub, neg_mul, neg_mul, ← Polynomial.C_mul, mul_inv_cancel₀ hr, Polynomial.C_1]
  ring

/-- Reversal is compatible with powers on a domain. -/
theorem deningerReverse_pow' (p : Polynomial K) (n : ℕ) :
    (p ^ n).reverse = p.reverse ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, ← Polynomial.C_1, Polynomial.reverse_C, Polynomial.C_1]
  | succ n ih =>
      rw [pow_succ, Polynomial.reverse_mul_of_domain, ih, pow_succ]

/-- If `(X - r) ^ n` divides `p` then `(X - r⁻¹) ^ n` divides `p.reverse`. -/
theorem deningerReverse_dvd_of_dvd {p : Polynomial K} {r : K} (hr : r ≠ 0) {n : ℕ}
    (h : (Polynomial.X - Polynomial.C r) ^ n ∣ p) :
    (Polynomial.X - Polynomial.C r⁻¹) ^ n ∣ p.reverse := by
  obtain ⟨s, rfl⟩ := h
  rw [Polynomial.reverse_mul_of_domain, deningerReverse_pow', deningerReverse_X_sub_C_eq r hr,
    mul_pow]
  exact ⟨(-Polynomial.C r) ^ n * s.reverse, by ring⟩

/-- **Root multiplicities of the reverse.**  For a polynomial with nonzero constant coefficient the
multiplicity of `r⁻¹` in the reverse is the multiplicity of `r`. -/
theorem deningerRootMultiplicity_reverse {p : Polynomial K} (hp0 : p.coeff 0 ≠ 0) {r : K}
    (hr : r ≠ 0) : p.reverse.rootMultiplicity r⁻¹ = p.rootMultiplicity r := by
  have hpne : p ≠ 0 := fun h => hp0 (by rw [h, Polynomial.coeff_zero])
  have hrevne : p.reverse ≠ 0 := deningerReverse_ne_zero hp0
  have hrev0 : p.reverse.coeff 0 ≠ 0 := by
    rw [deningerReverse_coeff_zero]
    exact Polynomial.leadingCoeff_ne_zero.2 hpne
  refine Nat.le_antisymm ?_ ?_
  · rw [Polynomial.le_rootMultiplicity_iff hpne]
    have hdvd : (Polynomial.X - Polynomial.C r⁻¹) ^ (p.reverse.rootMultiplicity r⁻¹)
        ∣ p.reverse := Polynomial.pow_rootMultiplicity_dvd _ _
    have := deningerReverse_dvd_of_dvd (p := p.reverse) (r := r⁻¹) (inv_ne_zero hr) hdvd
    rwa [inv_inv, deningerReverse_reverse hp0] at this
  · rw [Polynomial.le_rootMultiplicity_iff hrevne]
    exact deningerReverse_dvd_of_dvd hr (Polynomial.pow_rootMultiplicity_dvd _ _)

end RHTower
