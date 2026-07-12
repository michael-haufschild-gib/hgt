import GaloisForLFunctions.RHTower.NonmonicSymmetricIntegral

/-!
# Integralizing a non-monic conjugate set

Discharges the monic-polynomial hypothesis of `nonmonic_symmetric_aeval_isInt` by constructing the
integralized polynomial explicitly.  If `μ ∈ ℤ[X]` is nonzero with leading coefficient `ℓ` and
complete complex root factorization `μ = ℓ·∏_j (X − β_j)`, then the algebraic integers `ℓ·β_j` are
exactly the roots of the monic `integralNormalization μ`:

`∏_j (X − ℓ·β_j) = (integralNormalization μ).map`.

The identity is purely formal.  `integralNormalization μ · C ℓ = scaleRoots μ ℓ` (mathlib), and
`scaleRoots` commutes with `map` and is multiplicative over a domain, so mapping to `ℂ` and using
`scaleRoots (X − C a) ℓ = X − C (ℓ·a)` gives `(integralNormalization μ).map · C ℓ = C ℓ · ∏_j (X − ℓ·β_j)`;
cancelling the nonzero `C ℓ` yields the claim.

Composing with `nonmonic_symmetric_aeval_isInt` removes the hypothesis entirely: for a symmetric
integer polynomial `φ` and any non-monic conjugate set, `ℓ^{deg φ}·φ(β) ∈ ℤ`
(`nonmonic_symmetric_aeval_isInt_of_factorization`).
-/

open Polynomial

namespace GaloisForLFunctions
namespace RHTower

/-- **The scaled roots are the roots of the integral normalization.**  For nonzero `μ ∈ ℤ[X]` with
leading coefficient `ℓ` and complete factorization `μ.map = C ℓ · ∏_j (X − β_j)`, the algebraic
integers `ℓ·β_j` are the complete root set of the monic `integralNormalization μ`. -/
theorem exists_integralized_monic {d : ℕ} (μ : ℤ[X]) (hμ0 : μ ≠ 0) (β : Fin d → ℂ)
    (hβ : μ.map (Int.castRingHom ℂ)
        = C ((μ.leadingCoeff : ℤ) : ℂ) * (Multiset.map (fun j => X - C (β j)) Finset.univ.val).prod) :
    (Multiset.map (fun j => X - C (((μ.leadingCoeff : ℤ) : ℂ) * β j)) Finset.univ.val).prod
      = (μ.integralNormalization).map (Int.castRingHom ℂ) := by
  set ℓ : ℤ := μ.leadingCoeff with hℓ
  have hℓ0 : ℓ ≠ 0 := by rw [hℓ]; exact Polynomial.leadingCoeff_ne_zero.mpr hμ0
  have hℓC0 : ((ℓ : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hℓ0
  have hmapℓ : (Int.castRingHom ℂ) ℓ = ((ℓ : ℤ) : ℂ) := rfl
  have hdist : ∀ s : Multiset ℂ[X],
      s.prod.scaleRoots ((ℓ : ℤ) : ℂ) = (s.map (fun p => p.scaleRoots ((ℓ : ℤ) : ℂ))).prod := by
    intro s
    induction s using Multiset.induction with
    | empty => rw [Multiset.prod_zero, Multiset.map_zero, Multiset.prod_zero, Polynomial.one_scaleRoots]
    | cons a s ih =>
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
        Polynomial.mul_scaleRoots_of_noZeroDivisors, ih]
  have hkey : (μ.integralNormalization).map (Int.castRingHom ℂ) * C ((ℓ : ℤ) : ℂ)
      = (μ.map (Int.castRingHom ℂ)).scaleRoots ((ℓ : ℤ) : ℂ) := by
    have h1 := Polynomial.integralNormalization_mul_C_leadingCoeff μ
    have h2 := congrArg (Polynomial.map (Int.castRingHom ℂ)) h1
    rw [Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_scaleRoots μ ℓ (Int.castRingHom ℂ) (by rw [hmapℓ]; exact hℓC0)] at h2
    rw [← hℓ] at h2
    simpa [hmapℓ] using h2
  rw [hβ, Polynomial.mul_scaleRoots_of_noZeroDivisors, Polynomial.scaleRoots_C, hdist,
    Multiset.map_map] at hkey
  have hfac : (Multiset.map ((fun p => p.scaleRoots ((ℓ : ℤ) : ℂ)) ∘ fun j => X - C (β j)) Finset.univ.val)
      = Multiset.map (fun j => X - C (((ℓ : ℤ) : ℂ) * β j)) Finset.univ.val := by
    apply Multiset.map_congr rfl
    intro j _
    simp only [Function.comp_apply, sub_eq_add_neg, ← C_neg]
    rw [Polynomial.X_add_C_scaleRoots,
      show (-β j * ((ℓ : ℤ) : ℂ)) = -(((ℓ : ℤ) : ℂ) * β j) from by ring]
  rw [hfac] at hkey
  have hCℓ : C ((ℓ : ℤ) : ℂ) ≠ 0 := Polynomial.C_ne_zero.mpr hℓC0
  have := mul_right_cancel₀ hCℓ (by rw [hkey]; ring :
    (μ.integralNormalization).map (Int.castRingHom ℂ) * C ((ℓ : ℤ) : ℂ)
      = (Multiset.map (fun j => X - C (((ℓ : ℤ) : ℂ) * β j)) Finset.univ.val).prod * C ((ℓ : ℤ) : ℂ))
  exact this.symm

/-- **Non-monic symmetric integrality, unconditional form.**  For a nonzero `μ ∈ ℤ[X]` with leading
coefficient `ℓ` and complete factorization `μ.map = C ℓ · ∏_j (X − β_j)`, and a symmetric integer
polynomial `φ`, the value `ℓ^{deg φ}·φ(β)` is a rational integer. -/
theorem nonmonic_symmetric_aeval_isInt_of_factorization {d : ℕ} (μ : ℤ[X]) (hμ0 : μ ≠ 0)
    (β : Fin d → ℂ)
    (hβ : μ.map (Int.castRingHom ℂ)
        = C ((μ.leadingCoeff : ℤ) : ℂ) * (Multiset.map (fun j => X - C (β j)) Finset.univ.val).prod)
    (φ : MvPolynomial (Fin d) ℤ) (hφ : φ.IsSymmetric) :
    ∃ m : ℤ, ((μ.leadingCoeff : ℤ) : ℂ) ^ φ.totalDegree * MvPolynomial.aeval β φ = (m : ℂ) :=
  nonmonic_symmetric_aeval_isInt μ.leadingCoeff β μ.integralNormalization
    (exists_integralized_monic μ hμ0 β hβ) φ hφ

end RHTower
end GaloisForLFunctions
