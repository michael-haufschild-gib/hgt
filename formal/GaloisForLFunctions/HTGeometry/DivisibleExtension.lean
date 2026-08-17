import Mathlib

/-!
# Real coordinates for an independent family in an abelian group

The additive group `ℝ^m` is divisible, hence an injective `ℤ`-module.  Therefore the map sending a
`ℤ`-independent family `λ₁, …, λ_m` of an abelian group to the standard basis of `ℝ^m` — defined on
the free group they generate — extends to the whole group.

This is the algebraic input to the fact that a compact abelian group with `m` rationally independent
characters carries an `m`-parameter family with independent circle coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **An independent family extends to real coordinates.** -/
theorem exists_addMonoidHom_apply_eq_single {Γ : Type} [AddCommGroup Γ] {m : ℕ} (lam : Fin m → Γ)
    (hind : ∀ c : Fin m → ℤ, (∑ j, c j • lam j) = 0 → ∀ j, c j = 0) :
    ∃ ψ : Γ →+ (Fin m → ℝ), ∀ j j', ψ (lam j) j' = if j = j' then 1 else 0 := by
  classical
  have hbaer : Module.Baer ℤ (Fin m → ℝ) := Module.Baer.of_divisible _
  have hinjmod : Module.Injective ℤ (Fin m → ℝ) := hbaer.injective
  set f : (Fin m → ℤ) →ₗ[ℤ] Γ := Fintype.linearCombination ℤ lam with hf
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    funext j
    have : ∑ j, c j • lam j = 0 := by
      rw [hf, Fintype.linearCombination_apply] at hc
      exact hc
    simpa using hind c this j
  set g : (Fin m → ℤ) →ₗ[ℤ] (Fin m → ℝ) :=
    AddMonoidHom.toIntLinearMap
      { toFun := fun c j => (c j : ℝ)
        map_zero' := by funext j; simp
        map_add' := by intro c c'; funext j; simp } with hg
  obtain ⟨ψ, hψ⟩ := hinjmod.out f hfinj g
  refine ⟨ψ.toAddMonoidHom, ?_⟩
  intro j j'
  have hfs : f (Pi.single j (1 : ℤ)) = lam j := by
    rw [hf, Fintype.linearCombination_apply_single, one_smul]
  have hgs : g (Pi.single j (1 : ℤ)) j' = if j = j' then 1 else 0 := by
    by_cases hjj : j = j'
    · subst hjj
      simp [hg]
    · simp [hg, hjj]
  have := hψ (Pi.single j (1 : ℤ))
  rw [hfs] at this
  show ψ (lam j) j' = _
  rw [this, hgs]

end GaloisForLFunctions.HTGeometry
