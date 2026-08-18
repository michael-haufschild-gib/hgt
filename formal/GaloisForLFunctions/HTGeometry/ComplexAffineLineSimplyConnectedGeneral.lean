import GaloisForLFunctions.HTGeometry.SplitFibreAlgHom
import GaloisForLFunctions.HTGeometry.MonicRelationNonzeroConstant
import GaloisForLFunctions.HTGeometry.AlgebraCharpoly

/-!
# Algebraic simple connectedness of the complex affine line, general form

A domain that is finite free over `ℂ[X]` and all of whose fibres are split has rank one: the
`ℂ[X]`-algebra map supplied by the section is injective, because a nonzero kernel element would
satisfy a monic relation with nonzero constant term that the map sends to zero, and it is surjective
because it fixes the base.

Unlike `AffineSpaceSimplyConnected`, no monogenic model is assumed — this is the form an abstract
étale cover can be fed to.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B] [IsScalarTower ℂ ℂ[X] B]

/-- **Algebraic simple connectedness of the affine line, general form.**  A domain that is finite
free over `ℂ[X]` and all of whose fibres are split has rank one. -/
theorem rank_eq_one_of_splitFibres [IsDomain B] [Module.Free ℂ[X] B] [Module.Finite ℂ[X] B]
    {n : ℕ} (hn : 1 ≤ n) (e : Module.Basis (Fin n) ℂ[X] B) (h : SplitFibres B n) : n = 1 := by
  classical
  obtain ⟨ψ⟩ := nonempty_algHom_of_splitFibres hn e h
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro k hk
    by_contra hkne
    obtain ⟨r, hrm, hrz, hr0⟩ := exists_monic_coeff_zero_ne_zero (A := ℂ[X]) hkne
      (algCharpoly ℂ[X] k).natDegree (algCharpoly ℂ[X] k) (algCharpoly_monic ℂ[X] k) rfl
      (aeval_algCharpoly ℂ[X] k)
    apply hr0
    have h1 : ψ (Polynomial.aeval k r) = Polynomial.aeval (ψ k) r :=
      (Polynomial.aeval_algHom_apply ψ k r).symm
    rw [hrz, map_zero, hk] at h1
    have h2 : Polynomial.aeval (0 : ℂ[X]) r = r.coeff 0 := by
      simp [Polynomial.coeff_zero_eq_eval_zero]
    rw [h2] at h1
    exact h1.symm
  have hsurj : Function.Surjective ψ := fun a => ⟨algebraMap ℂ[X] B a, ψ.commutes a⟩
  have hbij : Function.Bijective ψ := ⟨hinj, hsurj⟩
  let φ : B ≃ₗ[ℂ[X]] ℂ[X] :=
    { Equiv.ofBijective ψ hbij with
      map_add' := map_add _
      map_smul' := fun c x => by simp [Equiv.ofBijective, Algebra.smul_def] }
  have h1 : Module.finrank ℂ[X] B = n := by
    rw [Module.finrank_eq_card_basis e]; simp
  have h2 : Module.finrank ℂ[X] B = 1 := by
    rw [φ.finrank_eq, Module.finrank_self]
  omega

end

end GaloisForLFunctions.HTGeometry
