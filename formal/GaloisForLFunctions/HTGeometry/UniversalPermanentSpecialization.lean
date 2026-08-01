import GaloisForLFunctions.HTGeometry.FiberPermanentIdentity
import GaloisForLFunctions.HTGeometry.UniversalPermanent

/-!
# Universal permanent specialization

The falling-factorial permanent governing an injective antidiagonal fiber is an exact
specialization of the universal matrix permanent.
-/

open Finset PowerSeries

namespace GaloisForLFunctions

/-- Matrix of complex falling-factorial polynomials used to specialize the universal permanent. -/
noncomputable def fallingFactorialPermanentMatrix {r : ℕ} (mu : Fin r → ℕ) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin r) ℂ) :=
  fun i j =>
    (Polynomial.aeval (MvPolynomial.X i) (descPochhammer ℤ (mu j))).map (Int.castRingHom ℂ)

/-- The complex falling-factorial symbol is the corresponding specialization of the universal
matrix permanent. -/
theorem universalPermanent_specialization {r : ℕ} (mu : Fin r → ℕ) :
    MvPolynomial.aeval
        (fun ij : Fin r × Fin r => fallingFactorialPermanentMatrix mu ij.1 ij.2)
        (PermanentRollout.permanent r) =
      (permSymbolPoly mu).map (Int.castRingHom ℂ) := by
  classical
  rw [PermanentRollout.permanent_aeval_eq_matrix_permanent]
  simp only [Matrix.permanent, fallingFactorialPermanentMatrix, permSymbolPoly, map_sum, map_prod]

/-- Evaluation of the universal specialization at natural scales is the complex
falling-factorial permanent. -/
theorem eval_universalPermanent_specialization {r : ℕ} (mu s : Fin r → ℕ) :
    MvPolynomial.eval (fun i => (s i : ℂ))
        (MvPolynomial.aeval
          (fun ij : Fin r × Fin r => fallingFactorialPermanentMatrix mu ij.1 ij.2)
          (PermanentRollout.permanent r)) =
      ∑ pi : Equiv.Perm (Fin r),
        ∏ t, (Nat.descFactorial (s (pi t)) (mu t) : ℂ) := by
  rw [universalPermanent_specialization, eval_map_permSymbolPoly_complex]

/-- The integer antidiagonal-fiber weight, cast to `ℂ`, is the value of the universal permanent
under the falling-factorial specialization and subsequent evaluation at the scale tuple. -/
theorem fiber_weight_eq_eval_universalPermanent {D : ℕ} (s : Fin D → ℕ)
    (hs : Function.Injective s) (mu : Fin D → ℕ) (hsmu : ∀ i t, mu t ≤ s i) :
    ((∑ l ∈ (Finset.univ.finsuppAntidiag (∑ t, (s t - mu t))).filter
        (fun l => key (fun t => l t + mu t) = key s),
      ∏ t, ((l t + mu t).descFactorial (mu t) : ℤ) : ℤ) : ℂ) =
      MvPolynomial.eval (fun i => (s i : ℂ))
        (MvPolynomial.aeval
          (fun ij : Fin D × Fin D => fallingFactorialPermanentMatrix mu ij.1 ij.2)
          (PermanentRollout.permanent D)) := by
  rw [fiber_perm_single s hs mu hsmu]
  push_cast
  exact (eval_universalPermanent_specialization mu s).symm

end GaloisForLFunctions
