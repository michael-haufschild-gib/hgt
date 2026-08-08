import GaloisForLFunctions.HTGeometry.SymmetricConjugateIntegral
import GaloisForLFunctions.RHTower.ScaledSymmetricPolynomial

/-!
# Symmetric-function integrality over a non-monic conjugate set

The monic symmetric-function integrality `symmetric_aeval_conj_isInt` requires the conjugate set to
consist of algebraic integers (roots of a monic `ℤ`-polynomial).  For a general algebraic number the
minimal polynomial is not monic over `ℤ`; its roots `β₁,…,β_d` are algebraic but not algebraic
integers.  The remedy is the classical leading-coefficient factor: if `ℓ·β₁,…,ℓ·β_d` are the roots of
a monic `ν ∈ ℤ[X]`, then for every symmetric `φ ∈ ℤ[X₁,…,X_d]`,

`ℓ^{deg φ} · φ(β₁,…,β_d) ∈ ℤ`.

The proof composes the rescaling device (`exists_scaled_symmetric`), which produces a symmetric
`ψ ∈ ℤ[X₁,…,X_d]` with `ψ(ℓ·β) = ℓ^{deg φ}·φ(β)`, with the monic integrality lemma applied to the
algebraic integers `ℓ·β_j`.  This is the leading-coefficient bookkeeping that lets the
Lindemann–Weierstrass estimate run over exponents that are algebraic but not algebraic integers.
-/

open Polynomial

namespace GaloisForLFunctions
namespace RHTower

/-- **Non-monic symmetric-function integrality.**  If `ℓ·β₁,…,ℓ·β_d` are the complete root set of a
monic `ν ∈ ℤ[X]` and `φ` is a symmetric integer polynomial, then `ℓ^{deg φ}·φ(β) ∈ ℤ`.  Proved by
rescaling `φ` to a symmetric `ψ` with `ψ(ℓ·β) = ℓ^{deg φ}·φ(β)` and applying the monic integrality
lemma to the algebraic integers `ℓ·β_j`. -/
theorem nonmonic_symmetric_aeval_isInt {d : ℕ} (ℓ : ℤ) (β : Fin d → ℂ) (ν : ℤ[X])
    (hν : (Multiset.map (fun j => Polynomial.X - Polynomial.C ((ℓ : ℂ) * β j)) Finset.univ.val).prod
        = ν.map (Int.castRingHom ℂ))
    (φ : MvPolynomial (Fin d) ℤ) (hφ : φ.IsSymmetric) :
    ∃ m : ℤ, (ℓ : ℂ) ^ φ.totalDegree * MvPolynomial.aeval β φ = (m : ℂ) := by
  obtain ⟨ψ, hψsym, hψ⟩ := exists_scaled_symmetric ℓ φ hφ
  obtain ⟨m, hm⟩ := symmetric_aeval_conj_isInt ν (fun j => (ℓ : ℂ) * β j) hν ψ hψsym
  exact ⟨m, by rw [← hψ β]; exact hm⟩

end RHTower
end GaloisForLFunctions
