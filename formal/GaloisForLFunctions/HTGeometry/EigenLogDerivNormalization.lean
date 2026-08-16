import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# Normalizing a chain-rule eigenvector by its logarithmic derivative

Let `Φ` be a ring endomorphism of a field satisfying the chain rule `D (Φ v) = Φ (D v) · ρ`
against a derivation `D` at the eigenvector itself, with `ρ` a `D`-constant.  An
eigenvector `Φ w · ρ = λ w` produces a *canonical* eigenvector with eigenvalue one, namely the
logarithmic derivative `D w / w`: the eigenvalue cancels between numerator and denominator, while
the derivative factor survives with the same exponent.

This is the step that removes the arbitrary eigenvalue from an eigen-tensor relation, so a descent
on the order of the eigenvector cannot terminate on a vacuous scalar identity.
-/

namespace GaloisForLFunctions.HTGeometry

variable {C E : Type*} [Field C] [Field E] [Algebra C E]

/-- The derivative of an eigenvector, again an eigenvector, with the derivative factor squared. -/
theorem deriv_eigen_of_chain_rule (D : Derivation C E E) (Φ : E →+* E) {ρ lam w : E}
    (hchain : D (Φ w) = Φ (D w) * ρ)
    (hρ : D ρ = 0) (hρ0 : ρ ≠ 0) (hlam : D lam = 0)
    (heig : Φ w * ρ = lam * w) :
    Φ (D w) * (ρ * ρ) = lam * D w := by
  have hΦw : Φ w = lam * w * ρ⁻¹ := by
    field_simp
    linear_combination heig
  have hinv : D (ρ⁻¹) = 0 := by
    rw [Derivation.leibniz_inv, hρ, smul_zero]
  have hlamw : D (lam * w) = lam * D w := by
    rw [Derivation.leibniz, hlam, smul_zero, add_zero, smul_eq_mul]
  have hDΦw : D (Φ w) = ρ⁻¹ * (lam * D w) := by
    rw [hΦw, Derivation.leibniz, hinv, smul_zero, zero_add, hlamw, smul_eq_mul]
  rw [hchain] at hDΦw
  field_simp at hDΦw
  rw [← hDΦw]
  ring

/-- **The logarithmic derivative is an eigenvector with eigenvalue one.** -/
theorem eigen_logDeriv_of_chain_rule (D : Derivation C E E) (Φ : E →+* E) {ρ lam w : E}
    (hchain : D (Φ w) = Φ (D w) * ρ)
    (hρ : D ρ = 0) (hρ0 : ρ ≠ 0) (hlam : D lam = 0) (hlam0 : lam ≠ 0) (hw0 : w ≠ 0)
    (heig : Φ w * ρ = lam * w) :
    Φ (D w / w) * ρ = D w / w := by
  have hΦinj : Function.Injective Φ := Φ.injective
  have hΦw0 : Φ w ≠ 0 := fun h => hw0 (hΦinj (by rw [h, map_zero]))
  have hderiv := deriv_eigen_of_chain_rule D Φ hchain hρ hρ0 hlam heig
  rw [map_div₀, div_mul_eq_mul_div, div_eq_div_iff hΦw0 hw0]
  have hkey : (Φ (D w) * ρ * w) * (ρ * lam) = (D w * Φ w) * (ρ * lam) := by
    linear_combination (w * lam) * hderiv - (D w * lam) * heig
  exact mul_right_cancel₀ (mul_ne_zero hρ0 hlam0) hkey

/-! ## The coefficient eigen-relations of a scaled substitution -/

/-- Composing with the scaling `X ↦ ρ·X` multiplies the `n`-th coefficient by `ρ^n`. -/
theorem coeff_comp_C_mul_X {F : Type*} [CommRing F] (p : Polynomial F) (a : F) (n : ℕ) :
    (p.comp (Polynomial.C a * Polynomial.X)).coeff n = a ^ n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, mul_add]
  | monomial k b =>
      rw [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul,
        Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial,
        Polynomial.coeff_monomial]
      by_cases h : n = k
      · subst h
        rw [if_pos rfl, if_pos rfl]
        ring
      · rw [if_neg (fun hk => h hk.symm), if_neg (fun hk => h hk.symm), mul_zero]

/-- **The coefficient eigen-relations.**  If applying `Φ` to the coefficients of `Q` and scaling
the variable by `ρ` multiplies `Q` by `ρ^d`, then every coefficient is an eigenvector of `Φ` with
eigenvalue a power of `ρ` determined by its position. -/
theorem coeff_eigen_of_comp_scale {F : Type*} [Field F] (Φ : F →+* F) {ρ : F}
    {Q : Polynomial F} {d : ℕ}
    (hQ : (Q.map Φ).comp (Polynomial.C ρ * Polynomial.X) = Polynomial.C (ρ ^ d) * Q) (j : ℕ) :
    Φ (Q.coeff j) * ρ ^ j = ρ ^ d * Q.coeff j := by
  have h := congrArg (fun p : Polynomial F => p.coeff j) hQ
  simp only [coeff_comp_C_mul_X, Polynomial.coeff_map, Polynomial.coeff_C_mul] at h
  linear_combination h

/-- Below the top degree the exponent gap is positive, so a nonzero coefficient is an eigenvector
with a genuinely nonzero power of the derivative factor. -/
theorem coeff_eigen_pow_of_comp_scale {F : Type*} [Field F] (Φ : F →+* F) {ρ : F} (hρ : ρ ≠ 0)
    {Q : Polynomial F} {d : ℕ}
    (hQ : (Q.map Φ).comp (Polynomial.C ρ * Polynomial.X) = Polynomial.C (ρ ^ d) * Q)
    {j : ℕ} (hj : j ≤ d) :
    Φ (Q.coeff j) = ρ ^ (d - j) * Q.coeff j := by
  have h := coeff_eigen_of_comp_scale Φ hQ j
  have hsplit : ρ ^ d = ρ ^ (d - j) * ρ ^ j := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit] at h
  have hjne : (ρ : F) ^ j ≠ 0 := pow_ne_zero j hρ
  exact mul_right_cancel₀ hjne (by linear_combination h)

end GaloisForLFunctions.HTGeometry
