import GaloisForLFunctions.HTGeometry.SectionValuePolynomial

/-!
# A section of the parameter line inside the algebra

The continuous section supplied by simple connectedness of `ℂ` has polynomial values, and those
values assemble into a `ℂ[X]`-algebra homomorphism `B → ℂ[X]` because each complex point is one and
a polynomial is determined by its values.  This is step (c) of the general simple connectedness of
the affine line, complete.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- **A section of the parameter line inside the algebra.**  A finite free `ℂ[X]`-algebra with
split fibres admits a `ℂ[X]`-algebra homomorphism to `ℂ[X]`. -/
theorem nonempty_algHom_of_splitFibres [Module.Free ℂ[X] B] [Module.Finite ℂ[X] B]
    {n : ℕ} (hn : 1 ≤ n) (e : Module.Basis (Fin n) ℂ[X] B) (h : SplitFibres B n) :
    Nonempty (B →ₐ[ℂ[X]] ℂ[X]) := by
  classical
  obtain ⟨σ, hσc, hσ⟩ := exists_continuous_section_of_splitFibres hn e h
  choose Q hQ using fun b : B => exists_polynomial_section_apply hn e h hσc hσ b
  have hext : ∀ p q : ℂ[X], (∀ s : ℂ, p.eval s = q.eval s) → p = q := fun p q hpq =>
    Polynomial.funext hpq
  refine ⟨{ toFun := Q
            map_one' := hext _ _ (fun s => by rw [← hQ 1 s]; simp)
            map_mul' := fun x y => hext _ _ (fun s => by
              rw [← hQ (x * y) s, Polynomial.eval_mul, ← hQ x s, ← hQ y s, map_mul])
            map_zero' := hext _ _ (fun s => by rw [← hQ 0 s]; simp)
            map_add' := fun x y => hext _ _ (fun s => by
              rw [← hQ (x + y) s, Polynomial.eval_add, ← hQ x s, ← hQ y s, map_add])
            commutes' := fun a => hext _ _ (fun s => by
              rw [← hQ (algebraMap ℂ[X] B a) s]
              have := AlgSpec.apply_algebraMap B (σ s) a
              rw [hσ s] at this
              exact this) }⟩

end

end GaloisForLFunctions.HTGeometry
