import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Extending a derivation of the coefficients to polynomials

A derivation of a ring extends to polynomials over it by acting on each coefficient.  The Leibniz
rule survives because the coefficients of a product are convolutions, and a derivation distributes
over each convolution term.

This is what lets a partial derivative in the coefficient parameters be moved across extraction of
a coefficient in the polynomial variable.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A derivation of the coefficients, applied coefficientwise. -/
noncomputable def coeffwise (D : Derivation R A A) (f : Polynomial A) : Polynomial A :=
  ∑ k ∈ f.support, Polynomial.C (D (f.coeff k)) * Polynomial.X ^ k

@[simp]
theorem coeff_coeffwise (D : Derivation R A A) (f : Polynomial A) (m : ℕ) :
    (coeffwise D f).coeff m = D (f.coeff m) := by
  classical
  rw [coeffwise, Polynomial.finsetSum_coeff]
  by_cases hm : m ∈ f.support
  · rw [Finset.sum_eq_single m]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
    · intro h
      exact absurd hm h
  · have h0 : f.coeff m = 0 := Polynomial.notMem_support_iff.1 hm
    rw [h0, map_zero]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hbm : m ≠ b := fun hcon => hm (hcon ▸ hb)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hbm, mul_zero]

theorem coeffwise_add (D : Derivation R A A) (f g : Polynomial A) :
    coeffwise D (f + g) = coeffwise D f + coeffwise D g := by
  refine Polynomial.ext fun k => ?_
  rw [coeff_coeffwise, Polynomial.coeff_add, Polynomial.coeff_add, coeff_coeffwise,
    coeff_coeffwise, map_add]

theorem coeffwise_smul (D : Derivation R A A) (r : R) (f : Polynomial A) :
    coeffwise D (r • f) = r • coeffwise D f := by
  refine Polynomial.ext fun k => ?_
  rw [coeff_coeffwise, Polynomial.coeff_smul, Polynomial.coeff_smul, coeff_coeffwise,
    Derivation.map_smul]

theorem coeffwise_one (D : Derivation R A A) : coeffwise D (1 : Polynomial A) = 0 := by
  refine Polynomial.ext fun k => ?_
  rw [coeff_coeffwise, Polynomial.coeff_one, Polynomial.coeff_zero]
  by_cases hk : k = 0
  · rw [if_pos hk, Derivation.map_one_eq_zero]
  · rw [if_neg hk, map_zero]

theorem coeffwise_mul (D : Derivation R A A) (f g : Polynomial A) :
    coeffwise D (f * g) = f * coeffwise D g + g * coeffwise D f := by
  classical
  refine Polynomial.ext fun k => ?_
  rw [coeff_coeffwise, Polynomial.coeff_mul, map_sum, Polynomial.coeff_add,
    Polynomial.coeff_mul, Polynomial.coeff_mul]
  have hterm : ∀ x ∈ Finset.antidiagonal k,
      D (f.coeff x.1 * g.coeff x.2) =
        f.coeff x.1 * (coeffwise D g).coeff x.2 + D (f.coeff x.1) * g.coeff x.2 := by
    intro x _
    rw [Derivation.leibniz, coeff_coeffwise, smul_eq_mul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_nbij' (fun x => x.swap) (fun x => x.swap) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_antidiagonal] at hx ⊢
    rw [Prod.fst_swap, Prod.snd_swap]
    omega
  · intro x hx
    rw [Finset.mem_antidiagonal] at hx ⊢
    rw [Prod.fst_swap, Prod.snd_swap]
    omega
  · intro x _
    exact Prod.swap_swap x
  · intro x _
    exact Prod.swap_swap x
  · intro x _
    rw [coeff_coeffwise]
    exact mul_comm _ _

/-- **A derivation of the coefficients is a derivation of the polynomials.** -/
noncomputable def coeffwiseDerivation (D : Derivation R A A) :
    Derivation R (Polynomial A) (Polynomial A) where
  toFun := coeffwise D
  map_add' := coeffwise_add D
  map_smul' r f := coeffwise_smul D r f
  map_one_eq_zero' := coeffwise_one D
  leibniz' := coeffwise_mul D

@[simp]
theorem coeff_coeffwiseDerivation (D : Derivation R A A) (f : Polynomial A) (k : ℕ) :
    (coeffwiseDerivation D f).coeff k = D (f.coeff k) := coeff_coeffwise D f k

/-- **A coefficient of a power of a polynomial differentiates by the chain rule.** -/
theorem coeff_pow_coeffwise (D : Derivation R A A) (f : Polynomial A) (m k : ℕ) :
    D ((f ^ m).coeff k) = (m • (f ^ (m - 1) * coeffwiseDerivation D f)).coeff k := by
  have h := (coeffwiseDerivation D).leibniz_pow f m
  have hk := congrArg (fun p : Polynomial A => p.coeff k) h
  rw [coeff_coeffwiseDerivation] at hk
  simpa using hk

end GaloisForLFunctions.HTGeometry
