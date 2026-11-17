import GaloisForLFunctions.HTGeometry.SplitFiniteAlgebraDiscriminant
import Mathlib.Data.Complex.Basic

/-!
# Coordinate algebra symmetries of finite interpolation data

The algebraic step in Theorem 1 of A. Biswas, *On the automorphisms of Pick
bodies*, arXiv:2610.28972, identifies algebra automorphisms of interpolation
data with coordinate permutations. Here the coordinate characters already
proved for split finite algebras give a unique permutation, with no analytic
assumptions. This isolates the finite symmetry left after normalizing a
Pick-body automorphism at the origin.
-/

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.Pick

open HTGeometry
noncomputable section

/-- An automorphism of the finite coordinate algebra is a unique permutation. -/
theorem coordinate_automorphism (n : ℕ)
    (Φ : (Fin n → ℂ) ≃ₐ[ℂ] (Fin n → ℂ)) :
    ∃! σ : Equiv.Perm (Fin n), ∀ x i, Φ x i = x (σ i) := by
  classical
  choose f hf using fun i : Fin n =>
    exists_eval_of_algHom_pi ((Pi.evalAlgHom ℂ (fun _ : Fin n => ℂ) i).comp Φ.toAlgHom)
  have he (i : Fin n) (x : Fin n → ℂ) : Φ x i = x (f i) := hf i x
  have hinj : Function.Injective f := by
    intro i j hij
    have hall (y : Fin n → ℂ) : y i = y j := by
      calc
        y i = Φ (Φ.symm y) i := by rw [Φ.apply_symm_apply]
        _ = Φ.symm y (f i) := he i _
        _ = Φ.symm y (f j) := congrArg (Φ.symm y) hij
        _ = Φ (Φ.symm y) j := (he j _).symm
        _ = y j := congrFun (Φ.apply_symm_apply y) j
    by_contra hne
    have h := hall (Pi.single i 1)
    exact one_ne_zero (by
      simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] using h)
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨σ, fun x i => he i x, ?_⟩
  intro τ hτ
  apply Equiv.ext
  intro i
  by_contra hne
  have h := (hτ (Pi.single (σ i) 1) i).symm.trans (he i (Pi.single (σ i) 1))
  change (Pi.single (σ i) 1 : Fin n → ℂ) (τ i) =
    (Pi.single (σ i) 1 : Fin n → ℂ) (σ i) at h
  exact zero_ne_one (by simpa only [Pi.single_eq_of_ne hne, Pi.single_eq_same] using h)

/-- Every primitive coordinate idempotent is transported to one primitive coordinate. -/
theorem coordinate_idempotent_transport (n : ℕ)
    (Φ : (Fin n → ℂ) ≃ₐ[ℂ] (Fin n → ℂ)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ j,
      Φ (Pi.single j 1) = Pi.single (σ.symm j) 1 := by
  classical
  obtain ⟨σ, hσ, _⟩ := coordinate_automorphism n Φ
  refine ⟨σ, fun j => funext fun i => ?_⟩
  rw [hσ]
  simp only [Pi.single_apply, Equiv.apply_eq_iff_eq_symm_apply]

/-- Algebraic symmetry preserves the multiset of values, including multiplicity. -/
theorem coordinate_value_multiset (n : ℕ)
    (Φ : (Fin n → ℂ) ≃ₐ[ℂ] (Fin n → ℂ)) (x : Fin n → ℂ) :
    (Finset.univ.val.map (Φ x)) = Finset.univ.val.map x := by
  classical
  obtain ⟨σ, hσ, _⟩ := coordinate_automorphism n Φ
  have hfun : Φ x = x ∘ σ := funext fun i => hσ x i
  rw [hfun, ← Multiset.map_map]
  congr 1
  exact Multiset.map_univ_val_equiv σ

#print axioms coordinate_automorphism
#print axioms coordinate_idempotent_transport
#print axioms coordinate_value_multiset

end
end GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
