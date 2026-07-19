import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Complex.Basic

/-!
# Rescaling polynomial variables by nonzero constants

The genericity theorems are stated in kernel-moment coordinates, while the carrier freeness
predicate evaluates packet values, which differ from the moments by a factorial in each coordinate.
Since factorials are nonzero, the two coordinate systems differ by a diagonal rescaling of the
variables.

Such a rescaling is an algebra automorphism of the polynomial ring — its inverse rescales by the
reciprocals — so it preserves being nonzero, and it transports a vanishing statement in one
coordinate system to the other.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Diagonal rescaling of the polynomial variables. -/
def scaleSubst {σ : Type*} (c : σ → ℂ) :
    MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  MvPolynomial.bind₁ (fun s => MvPolynomial.C (c s) * MvPolynomial.X s)

@[simp]
theorem scaleSubst_X {σ : Type*} (c : σ → ℂ) (s : σ) :
    scaleSubst c (MvPolynomial.X s) = MvPolynomial.C (c s) * MvPolynomial.X s := by
  simp [scaleSubst]

/-- Rescaling by reciprocals undoes a rescaling. -/
theorem scaleSubst_scaleSubst {σ : Type*} (c : σ → ℂ) (hc : ∀ s, c s ≠ 0)
    (Q : MvPolynomial σ ℂ) :
    scaleSubst (fun s => (c s)⁻¹) (scaleSubst c Q) = Q := by
  classical
  have hcomp : ∀ s : σ,
      scaleSubst (fun s => (c s)⁻¹) (MvPolynomial.C (c s) * MvPolynomial.X s) =
        MvPolynomial.X s := by
    intro s
    rw [map_mul, scaleSubst_X]
    simp only [scaleSubst, MvPolynomial.bind₁_C_right]
    rw [← mul_assoc, ← MvPolynomial.C_mul, mul_inv_cancel₀ (hc s), MvPolynomial.C_1,
      one_mul]
  induction Q using MvPolynomial.induction_on with
  | C a => simp [scaleSubst]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p s hp => rw [map_mul, map_mul, hp, scaleSubst_X, hcomp s]

/-- **Rescaling preserves nonvanishing.**  A diagonal rescaling by nonzero constants carries a
nonzero polynomial to a nonzero polynomial. -/
theorem scaleSubst_ne_zero {σ : Type*} (c : σ → ℂ) (hc : ∀ s, c s ≠ 0)
    {Q : MvPolynomial σ ℂ} (hQ : Q ≠ 0) : scaleSubst c Q ≠ 0 := by
  intro hzero
  apply hQ
  rw [← scaleSubst_scaleSubst c hc Q, hzero, map_zero]

/-- Evaluating a rescaled polynomial is evaluating the original at the rescaled point. -/
theorem eval_scaleSubst {σ : Type*} (c : σ → ℂ) (Q : MvPolynomial σ ℂ) (y : σ → ℂ) :
    MvPolynomial.eval y (scaleSubst c Q) =
      MvPolynomial.eval (fun s => c s * y s) Q := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a => simp [scaleSubst]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p s hp => simp [map_mul, hp, scaleSubst_X]

/-- **Transport of nondegeneracy across a diagonal rescaling.**  If no nonzero polynomial vanishes
at the rescaled point, none vanishes at the original point either. -/
theorem eval_ne_zero_of_scaled {σ : Type*} (c : σ → ℂ) (hc : ∀ s, c s ≠ 0)
    (y : σ → ℂ)
    (h : ∀ Q : MvPolynomial σ ℂ, Q ≠ 0 → MvPolynomial.eval y Q ≠ 0)
    (Q : MvPolynomial σ ℂ) (hQ : Q ≠ 0) :
    MvPolynomial.eval (fun s => c s * y s) Q ≠ 0 := by
  rw [← eval_scaleSubst c Q y]
  exact h _ (scaleSubst_ne_zero c hc hQ)

end

end GaloisForLFunctions.HTGeometry
