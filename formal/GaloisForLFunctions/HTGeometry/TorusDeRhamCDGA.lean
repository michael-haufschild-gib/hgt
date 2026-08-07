import GaloisForLFunctions.HTGeometry.CDGA
import GaloisForLFunctions.HTGeometry.CDGAFreeExterior
import GaloisForLFunctions.HTGeometry.SmoothPeriodicDGA

/-!
# The formality quasi-isomorphism of a torus

The smooth periodic forms with the wedge product and the exterior derivative are a commutative
differential graded algebra, and so is the exterior algebra of the dual of the covering space with
the zero differential.  Sending an element of the exterior power to the invariant form it defines is
a morphism of such algebras, and it is a quasi-isomorphism: injective because a constant form with a
periodic primitive vanishes, surjective because averaging writes every closed form as a constant one
plus an exact one.

* `torusDeRhamCDGA` : the de Rham algebra of the torus.
* `exteriorCDGA` : the exterior algebra of the dual of the covering space, with zero differential.
* `torusFormalityHom`, `torusFormality_isQuasiIso` : the comparison and the statement that it is a
  quasi-isomorphism.
-/

set_option maxSynthPendingDepth 3

namespace GaloisForLFunctions.HTGeometry

open exteriorPower Module
open scoped ContDiff

section Objects

variable {𝕜 : Type u} [RCLike 𝕜]

theorem exteriorMulOf_zero_left {M : Type*} [AddCommGroup M] [Module 𝕜 M] {a b n : ℕ}
    (h : a + b = n) (z : ⋀[𝕜]^b M) : exteriorMulOf h (0 : ⋀[𝕜]^a M) z = 0 := by
  have h0 : (0 : ⋀[𝕜]^a M) = (0 : 𝕜) • (0 : ⋀[𝕜]^a M) := by rw [zero_smul]
  rw [h0, exteriorMulOf_smul_left, zero_smul]

theorem exteriorMulOf_zero_right {M : Type*} [AddCommGroup M] [Module 𝕜 M] {a b n : ℕ}
    (h : a + b = n) (y : ⋀[𝕜]^a M) : exteriorMulOf h y (0 : ⋀[𝕜]^b M) = 0 := by
  have h0 : (0 : ⋀[𝕜]^b M) = (0 : 𝕜) • (0 : ⋀[𝕜]^b M) := by rw [zero_smul]
  rw [h0, exteriorMulOf_smul_right, zero_smul]

/-- **The exterior algebra of the dual of the covering space, with zero differential**: the free
commutative differential graded algebra on that dual placed in degree one. -/
noncomputable def exteriorCDGA (𝕜 : Type u) [RCLike 𝕜] (r : ℕ) :
    CDGAStructure 𝕜 (fun n => ⋀[𝕜]^n (Module.Dual 𝕜 (Fin r → 𝕜))) :=
  exteriorModuleCDGA 𝕜 (Module.Dual 𝕜 (Fin r → 𝕜))

/-- The unit of the exterior algebra of the dual. -/
noncomputable def exteriorCDGAUnit (𝕜 : Type u) [RCLike 𝕜] (r : ℕ) :
    CDGAUnit (exteriorCDGA 𝕜 r) :=
  exteriorModuleCDGAUnit 𝕜 (Module.Dual 𝕜 (Fin r → 𝕜))

/-- **The de Rham algebra of the torus**: the smooth periodic forms with the wedge product and the
exterior derivative. -/
noncomputable def torusDeRhamCDGA (p : 𝕜) (r : ℕ) :
    CDGAStructure 𝕜 (fun n => smoothPeriodicForms p r n) where
  mul h u v := smoothWedge p h u v
  d n u := smoothExtDerivMap p r n u
  mul_add_left h x x' y := smoothWedge_add_left p h x x' y
  mul_add_right h x y y' := smoothWedge_add_right p h x y y'
  mul_smul_left h c x y := smoothWedge_smul_left p h c x y
  mul_smul_right h c x y := smoothWedge_smul_right p h c x y
  mul_assoc h₁ h₂ h₃ h₄ x y z := smoothWedge_assoc p h₁ h₂ h₃ h₄ x y z
  mul_comm h h' x y := smoothWedge_comm p h h' x y
  d_add n x y := (smoothExtDerivMap p r n).map_add x y
  d_smul n c x := (smoothExtDerivMap p r n).map_smul c x
  d_d n x := LinearMap.congr_fun (smoothExtDerivMap_comp p r n) x
  d_mul h x y := smoothExtDerivMap_smoothWedge p h x y

end Objects

section Formality

variable {𝕜 : Type u} [RCLike 𝕜] {r n : ℕ}

/-- A constant form is a smooth periodic form. -/
theorem constantForm_mem_smoothPeriodicForms (p : 𝕜)
    (α : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) :
    (fun _ : Fin r → 𝕜 => α) ∈ smoothPeriodicForms p r n :=
  ⟨contDiff_const, fun _ _ => rfl⟩

/-- **The comparison morphism**: an element of the exterior power of the dual goes to the invariant
form it defines. -/
noncomputable def torusFormalityHom (p : 𝕜) (r : ℕ) :
    CDGAHom (exteriorCDGA 𝕜 r) (torusDeRhamCDGA p r) where
  toFun n y := ⟨fun _ => constantFormOfExterior 𝕜 r n y,
    constantForm_mem_smoothPeriodicForms p _⟩
  map_add n y z := by
    refine Subtype.ext ?_
    funext w
    exact congrArg (fun A => A) (map_add (constantFormOfExterior 𝕜 r n) y z)
  map_smul n c y := by
    refine Subtype.ext ?_
    funext w
    exact congrArg (fun A => A) (map_smul (constantFormOfExterior 𝕜 r n) c y)
  map_mul h y z := by
    refine Subtype.ext ?_
    funext w
    exact (wedgeForm_constantFormOfExterior h y z).symm
  map_d n y := by
    refine Subtype.ext ?_
    funext w
    show constantFormOfExterior 𝕜 r (n + 1) 0 = extDeriv (fun _ => constantFormOfExterior 𝕜 r n y) w
    rw [map_zero, extDeriv_const]

/-- **The comparison is a quasi-isomorphism**: the inclusion of the invariant forms into the de Rham
algebra of the torus induces an isomorphism on cohomology in every degree.  This is the formality
statement for a single torus, as a single morphism of commutative differential graded algebras. -/
theorem torusFormality_isQuasiIso {p : 𝕜} (hp : p ≠ 0) (r : ℕ) :
    (torusFormalityHom p r).IsQuasiIso := by
  classical
  intro n
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun ξ hξ => ?_
    refine Quotient.inductionOn' ξ ?_ hξ
    intro y hy
    have hzero : ((torusFormalityHom p r).cocyclesMap (n + 1) y) ∈
        (torusDeRhamCDGA p r).coboundaries n := (Submodule.Quotient.mk_eq_zero _).1 hy
    obtain ⟨θ, hθ⟩ := hzero
    have hsm : ContDiff 𝕜 ∞ (θ : PeriodicFormSpace 𝕜 r n) := θ.2.1
    have hper : ∀ (l : Fin r) (w : Fin r → 𝕜),
        (θ : PeriodicFormSpace 𝕜 r n) (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) =
          (θ : PeriodicFormSpace 𝕜 r n) w := θ.2.2
    have hval : ∀ w : Fin r → 𝕜,
        constantFormOfExterior 𝕜 r (n + 1)
            (y : ⋀[𝕜]^(n + 1) (Module.Dual 𝕜 (Fin r → 𝕜))) =
          extDeriv (θ : PeriodicFormSpace 𝕜 r n) w :=
      fun w => congrFun (congrArg Subtype.val hθ) w
    have hα : constantFormOfExterior 𝕜 r (n + 1)
        (y : ⋀[𝕜]^(n + 1) (Module.Dual 𝕜 (Fin r → 𝕜))) = 0 :=
      periodic_const_add_exact_unique (α' := 0) hp (hsm.differentiable (by simp))
        (hsm.continuous_fderiv (by simp)) hper fun w => by rw [zero_add]; exact hval w
    have hy0 : (y : ⋀[𝕜]^(n + 1) (Module.Dual 𝕜 (Fin r → 𝕜))) = 0 := by
      have hs := congrArg (constantFormOfExterior 𝕜 r (n + 1)).symm hα
      rwa [LinearEquiv.symm_apply_apply, map_zero] at hs
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨0, hy0⟩
  · intro ξ
    refine Quotient.inductionOn' ξ fun u => ?_
    have hsm : ContDiff 𝕜 ∞ ((u : smoothPeriodicForms p r (n + 1)) :
      PeriodicFormSpace 𝕜 r (n + 1)) := u.1.2.1
    have hper : ∀ (l : Fin r) (w : Fin r → 𝕜),
        ((u : smoothPeriodicForms p r (n + 1)) : PeriodicFormSpace 𝕜 r (n + 1))
            (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) =
          ((u : smoothPeriodicForms p r (n + 1)) : PeriodicFormSpace 𝕜 r (n + 1)) w := u.1.2.2
    have hclosed : ∀ w : Fin r → 𝕜,
        extDeriv ((u : smoothPeriodicForms p r (n + 1)) :
          PeriodicFormSpace 𝕜 r (n + 1)) w = 0 :=
      fun w => congrFun (congrArg Subtype.val u.2) w
    obtain ⟨α, η, hηsm, hηper, hdecomp⟩ :=
      periodic_closed_eq_const_add_exact_smooth hp hsm hper hclosed
    refine ⟨Submodule.Quotient.mk ⟨(constantFormOfExterior 𝕜 r (n + 1)).symm α, rfl⟩, ?_⟩
    refine (Submodule.Quotient.eq _).2 ?_
    refine ⟨⟨fun y => -η y, ?_, ?_⟩, ?_⟩
    · have hfun : (fun y : Fin r → 𝕜 => -η y) = (-1 : 𝕜) • η := by
        funext y
        rw [Pi.smul_apply, negOne_smul_alternating]
      rw [hfun]
      exact hηsm.const_smul (-1 : 𝕜)
    · intro l w
      show -η (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = -η w
      rw [hηper l w]
    · refine Subtype.ext ?_
      funext w
      show constantFormOfExterior 𝕜 r (n + 1)
            ((constantFormOfExterior 𝕜 r (n + 1)).symm α) -
          ((u : smoothPeriodicForms p r (n + 1)) : PeriodicFormSpace 𝕜 r (n + 1)) w =
        extDeriv (fun y => -η y) w
      rw [LinearEquiv.apply_symm_apply]
      have hneg : extDeriv (fun y : Fin r → 𝕜 => -η y) w = -extDeriv η w := by
        have hfun : (fun y : Fin r → 𝕜 => -η y) = (-1 : 𝕜) • η := by
          funext y
          rw [Pi.smul_apply, negOne_smul_alternating]
        rw [hfun, extDeriv_smul, negOne_smul_alternating]
      rw [hneg, hdecomp w]
      abel

end Formality

end GaloisForLFunctions.HTGeometry
