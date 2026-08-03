import GaloisForLFunctions.RHTower.DeningerBaumslagH2

/-!
# `H¹` with trivial rational coefficients, in mathlib's group cohomology

With a trivial action the `1`-coboundaries vanish, so `H¹` is the group of `1`-cocycles, and a
`1`-cocycle for a trivial action is exactly a homomorphism into the coefficients.  Composed with the
degree-one comparison of the packet, this makes clause 3 and the degree-one half of `(3)` literal
statements about `groupCohomology.H1`.

* `deningerCoboundaries₁_trivial` : the coboundaries vanish.
* `deningerH1Equiv` : `H¹` is the module of cocycles.
* `deningerCocycles₁Equiv` : cocycles are homomorphisms.
* `deningerBauFree_H1_equiv` : `H¹(Bau(F);ℚ) ≅ U`.
-/

namespace RHTower

open groupCohomology

section TrivialH1

variable {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module ℚ M]

/-- **With a trivial action the `1`-coboundaries vanish.** -/
theorem deningerCoboundaries₁_trivial :
    coboundaries₁ (Rep.trivial ℚ G M) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro _ ⟨m, rfl⟩
  refine Submodule.mem_bot _ |>.2 ?_
  refine funext fun g => ?_
  rw [d₀₁_hom_apply]
  show ((Rep.trivial ℚ G M).ρ g) m - m = 0
  simp

theorem deningerH1π_injective :
    Function.Injective (CategoryTheory.ConcreteCategory.hom (H1π (Rep.trivial ℚ G M))) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have h := (H1π_eq_zero_iff x).1 hx
  rw [deningerCoboundaries₁_trivial, Submodule.mem_bot] at h
  exact Subtype.ext h

theorem deningerH1π_surjective :
    Function.Surjective (CategoryTheory.ConcreteCategory.hom (H1π (Rep.trivial ℚ G M))) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- **`H¹` is the module of `1`-cocycles**, the coboundaries being zero. -/
noncomputable def deningerH1Equiv :
    (H1 (Rep.trivial ℚ G M) : Type) ≃ (cocycles₁ (Rep.trivial ℚ G M)) :=
  (Equiv.ofBijective _ ⟨deningerH1π_injective (G := G) (M := M),
    deningerH1π_surjective (G := G) (M := M)⟩).symm

theorem deningerCocycles₁_map_one (x : cocycles₁ (Rep.trivial ℚ G M)) : (x : G → M) 1 = 0 := by
  have h := (mem_cocycles₁_iff (A := Rep.trivial ℚ G M) (⇑x)).1 x.2 1 1
  rw [mul_one] at h
  have hρ : ((Rep.trivial ℚ G M).ρ 1) ((x : G → M) 1) = (x : G → M) 1 := by simp
  rw [hρ] at h
  have h2 : (x : G → M) 1 + 0 = (x : G → M) 1 + (x : G → M) 1 := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h2).symm

/-- **A `1`-cocycle for a trivial action is a homomorphism.** -/
def deningerCocycles₁Equiv :
    (cocycles₁ (Rep.trivial ℚ G M)) ≃ (G →* Multiplicative M) where
  toFun x :=
    { toFun := fun g => Multiplicative.ofAdd ((x : G → M) g)
      map_one' := congrArg Multiplicative.ofAdd (deningerCocycles₁_map_one x)
      map_mul' := by
        intro g h
        have hx := (mem_cocycles₁_iff (A := Rep.trivial ℚ G M) (⇑x)).1 x.2 g h
        show Multiplicative.ofAdd ((x : G → M) (g * h)) =
          Multiplicative.ofAdd ((x : G → M) g + (x : G → M) h)
        refine congrArg Multiplicative.ofAdd ?_
        rw [hx]
        show ((Rep.trivial ℚ G M).ρ g) ((x : G → M) h) + (x : G → M) g = _
        rw [show ((Rep.trivial ℚ G M).ρ g) ((x : G → M) h) = (x : G → M) h by simp]
        exact add_comm _ _ }
  invFun φ :=
    ⟨fun g => Multiplicative.toAdd (φ g), by
      rw [mem_cocycles₁_iff]
      intro g h
      show Multiplicative.toAdd (φ (g * h)) =
        ((Rep.trivial ℚ G M).ρ g) (Multiplicative.toAdd (φ h)) + Multiplicative.toAdd (φ g)
      rw [show ((Rep.trivial ℚ G M).ρ g) (Multiplicative.toAdd (φ h)) =
        Multiplicative.toAdd (φ h) by simp, map_mul]
      exact add_comm _ _⟩
  left_inv _ := rfl
  right_inv _ := rfl

end TrivialH1

section BaumslagH1

variable {ι : Type} {U : Type} [AddCommGroup U] [Module ℚ U] [Module.IsReflexive ℚ U]

/-- **`H¹(BR_U;ℚ) ≅ U`**, in mathlib's group cohomology.  The coboundaries vanish, the cocycles are
the homomorphisms, and clause 3 identifies those with `U`. -/
noncomputable def deningerBauFree_H1_equiv (b : Module.Basis ι ℚ (Module.Dual ℚ U)) :
    (H1 (Rep.trivial ℚ (DeningerBau (FreeGroup ι)) ℚ) : Type) ≃ U :=
  deningerH1Equiv.trans (deningerCocycles₁Equiv.trans (deningerBauFree_degreeOne_equiv b))

end BaumslagH1

end RHTower
