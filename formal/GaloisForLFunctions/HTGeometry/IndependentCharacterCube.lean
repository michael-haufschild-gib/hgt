import GaloisForLFunctions.HTGeometry.CircleCoordinateCube
import GaloisForLFunctions.HTGeometry.DivisibleExtension

/-!
# An abelian group with `m` independent elements carries an `m`-cube of characters

Real coordinates for a `ℤ`-independent family produce an `m`-parameter family of unitary characters
whose values at the `m` chosen elements are the `m` independent circle coordinates of the parameter.

Together with the cube obstruction this says: no continuous map into `ℝ^k` with `k < m` separates
the characters of this family — the geometric content of "a compact abelian group whose dual has
rank at least `m` has covering dimension at least `m`".
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

/-- The character of `Γ` attached to a parameter `v` through real coordinates `ψ`. -/
noncomputable def cubeChar {Γ : Type} [AddCommGroup Γ] {m : ℕ} (ψ : Γ →+ (Fin m → ℝ))
    (v : EuclideanSpace ℝ (Fin m)) (a : Γ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * ((∑ j, ψ a j * v j : ℝ) : ℂ))

/-- **The cube of characters attached to an independent family.** -/
theorem exists_character_cube {Γ : Type} [AddCommGroup Γ] {m : ℕ} (lam : Fin m → Γ)
    (hind : ∀ c : Fin m → ℤ, (∑ j, c j • lam j) = 0 → ∀ j, c j = 0) :
    ∃ Θ : EuclideanSpace ℝ (Fin m) → (Γ → ℂ),
      Continuous Θ ∧
      (∀ v a b, Θ v (a + b) = Θ v a * Θ v b) ∧
      (∀ v a, ‖Θ v a‖ = 1) ∧
      (∀ v j, Θ v (lam j) = Complex.exp ((Real.pi : ℂ) * Complex.I * (v j : ℂ))) := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_addMonoidHom_apply_eq_single lam hind
  refine ⟨cubeChar ψ, ?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun a => ?_
    refine Complex.continuous_exp.comp ?_
    refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    exact continuous_finsetSum _ fun j _ =>
      continuous_const.mul (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
  · intro v a b
    have hsum : ∑ j, ψ (a + b) j * v j = (∑ j, ψ a j * v j) + ∑ j, ψ b j * v j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : ψ (a + b) j = ψ a j + ψ b j := by
        rw [map_add]
        rfl
      rw [this]
      ring
    simp only [cubeChar, hsum]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · intro v a
    have hrw : (Real.pi : ℂ) * Complex.I * ((∑ j, ψ a j * v j : ℝ) : ℂ)
        = ((Real.pi * ∑ j, ψ a j * v j : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [cubeChar, hrw, Complex.norm_exp_ofReal_mul_I]
  · intro v j
    have hsum : ∑ j', ψ (lam j) j' * v j' = v j := by
      rw [Finset.sum_eq_single j]
      · rw [hψ j j]
        simp
      · intro j' _ hne
        rw [hψ j j']
        simp [Ne.symm hne]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [cubeChar, hsum]

/-- **The parameter cube embeds in the character space.** -/
theorem injOn_of_character_cube {Γ : Type} [AddCommGroup Γ] {m : ℕ}
    {Θ : EuclideanSpace ℝ (Fin m) → (Γ → ℂ)} {lam : Fin m → Γ}
    (hΘ : ∀ v j, Θ v (lam j) = Complex.exp ((Real.pi : ℂ) * Complex.I * (v j : ℂ))) :
    Set.InjOn Θ (unitCube m) := by
  intro v hv v' hv' heq
  refine eq_of_exp_pi_mul_I_eq hv hv' fun j => ?_
  rw [← hΘ v j, ← hΘ v' j, heq]

/-- **A group with `m` independent elements has a cube of characters that no continuous map into
`ℝ^k` with `k < m` can separate.** -/
theorem not_injOn_of_independent_family {Γ : Type} [AddCommGroup Γ] {k m : ℕ} (hkm : k < m)
    (lam : Fin m → Γ) (hind : ∀ c : Fin m → ℤ, (∑ j, c j • lam j) = 0 → ∀ j, c j = 0) :
    ∃ Θ : EuclideanSpace ℝ (Fin m) → (Γ → ℂ),
      Continuous Θ ∧
      (∀ v a b, Θ v (a + b) = Θ v a * Θ v b) ∧
      (∀ v a, ‖Θ v a‖ = 1) ∧
      Set.InjOn Θ (unitCube m) ∧
      ∀ h : (Γ → ℂ) → EuclideanSpace ℝ (Fin k),
        ContinuousOn (fun v => h (Θ v)) (unitCube m) → ¬ Set.InjOn h (Θ '' unitCube m) := by
  obtain ⟨Θ, hcont, hmul, hnorm, hval⟩ := exists_character_cube lam hind
  refine ⟨Θ, hcont, hmul, hnorm, injOn_of_character_cube hval, ?_⟩
  intro h hhcont hhinj
  refine not_injOn_unitCube hkm (fun v => h (Θ v)) hhcont ?_
  intro v hv v' hv' heq
  exact injOn_of_character_cube hval hv hv'
    (hhinj ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩ heq)

end GaloisForLFunctions.HTGeometry
