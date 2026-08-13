import GaloisForLFunctions.HTGeometry.ConstraintRelativity.ConormalPersistence
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Two-boundary Banach observer duality

This file formalizes the exact two-boundary quotient, its degree-minus-one cone law, the
continuous observer-descent sequence, the topological descent radical, and covariance of the
relative pairing under continuous linear coordinate changes.
-/

namespace HTGeometry.ConstraintRelativity

section TwoBoundary

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The two-boundary quotient map `x ↦ ([x]ₗ, [x]ᵣ)`. -/
noncomputable def twoBoundaryQuotient (Yₗ Yᵣ : Submodule 𝕜 E) :
    E →L[𝕜] (E ⧸ Yₗ) × (E ⧸ Yᵣ) :=
  (quotientCLM Yₗ).prod (quotientCLM Yᵣ)

@[simp] theorem twoBoundaryQuotient_apply (Yₗ Yᵣ : Submodule 𝕜 E) (x : E) :
    twoBoundaryQuotient Yₗ Yᵣ x =
      (Submodule.Quotient.mk x, Submodule.Quotient.mk x) := rfl

/-- **Card `(BHR.2)`.** The laws killed at both boundaries are their intersection. -/
theorem ker_twoBoundaryQuotient (Yₗ Yᵣ : Submodule 𝕜 E) :
    LinearMap.ker (twoBoundaryQuotient Yₗ Yᵣ : E →ₗ[𝕜] (E ⧸ Yₗ) × (E ⧸ Yᵣ)) =
      Yₗ ⊓ Yᵣ := by
  rw [twoBoundaryQuotient, ContinuousLinearMap.ker_prod]
  simp [quotientCLM]

/-- Degree-minus-one cohomology of the cone of a map between complexes concentrated in degree
zero.  In that degree there are no incoming boundaries, so this is literally the kernel. -/
abbrev twoTermConeMinusOneCohomology (Yₗ Yᵣ : Submodule 𝕜 E) : Type _ :=
  LinearMap.ker (twoBoundaryQuotient Yₗ Yᵣ : E →ₗ[𝕜] (E ⧸ Yₗ) × (E ⧸ Yᵣ))

/-- **Card `(BHR.4)`.** Degree-minus-one cone cohomology is the common retained law. -/
noncomputable def twoTermConeMinusOneEquiv (Yₗ Yᵣ : Submodule 𝕜 E) :
    twoTermConeMinusOneCohomology Yₗ Yᵣ ≃ₗ[𝕜] (Yₗ ⊓ Yᵣ : Submodule 𝕜 E) :=
  LinearEquiv.ofEq _ _ (ker_twoBoundaryQuotient Yₗ Yᵣ)

end TwoBoundary

/-! ## Continuous observer descent -/

section ContinuousObservers

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Continuous annihilator of a linear subspace. -/
abbrev continuousAnnihilator (Y : Submodule 𝕜 E) : Submodule 𝕜 (StrongDual 𝕜 E) :=
  StrongDual.polarSubmodule 𝕜 Y

theorem mem_continuousAnnihilator {Y : Submodule 𝕜 E} {φ : StrongDual 𝕜 E} :
    φ ∈ continuousAnnihilator Y ↔ ∀ y ∈ Y, φ y = 0 :=
  StrongDual.mem_polarSubmodule Y φ

/-- Restriction of a continuous functional to a subspace. -/
noncomputable def continuousRestrict (Y : Submodule 𝕜 E) :
    StrongDual 𝕜 E →ₗ[𝕜] StrongDual 𝕜 Y where
  toFun φ := φ.comp Y.subtypeL
  map_add' φ ψ := by ext; rfl
  map_smul' c φ := by ext; rfl

@[simp] theorem continuousRestrict_apply (Y : Submodule 𝕜 E)
    (φ : StrongDual 𝕜 E) (y : Y) : continuousRestrict Y φ y = φ y := rfl

theorem ker_continuousRestrict (Y : Submodule 𝕜 E) :
    LinearMap.ker (continuousRestrict Y) = continuousAnnihilator Y := by
  ext φ
  rw [LinearMap.mem_ker, mem_continuousAnnihilator]
  constructor
  · intro h y hy
    have := DFunLike.congr_fun h (⟨y, hy⟩ : Y)
    simpa using this
  · intro h
    ext y
    exact h y y.2

/-- Hahn--Banach makes restriction to a subspace surjective. -/
theorem continuousRestrict_surjective (Y : Submodule 𝕜 E) :
    Function.Surjective (continuousRestrict Y) := by
  intro ψ
  obtain ⟨φ, hφ, _⟩ := exists_extension_norm_eq Y ψ
  refine ⟨φ, ?_⟩
  ext y
  exact hφ y

theorem sup_continuousAnnihilator_le_inf (Yₗ Yᵣ : Submodule 𝕜 E) :
    continuousAnnihilator Yₗ ⊔ continuousAnnihilator Yᵣ ≤
      continuousAnnihilator (Yₗ ⊓ Yᵣ) := by
  rw [sup_le_iff]
  constructor
  · intro φ hφ
    rw [mem_continuousAnnihilator] at hφ ⊢
    exact fun y hy => hφ y hy.1
  · intro φ hφ
    rw [mem_continuousAnnihilator] at hφ ⊢
    exact fun y hy => hφ y hy.2

/-- Algebraic quotient of continuous observers by sums descending through either boundary. -/
abbrev twoBoundaryObserverQuotient (Yₗ Yᵣ : Submodule 𝕜 E) : Type _ :=
  StrongDual 𝕜 E ⧸ (continuousAnnihilator Yₗ ⊔ continuousAnnihilator Yᵣ)

/-- Restriction of an observer class to the common retained law. -/
noncomputable def twoBoundaryObserverRestriction (Yₗ Yᵣ : Submodule 𝕜 E) :
    twoBoundaryObserverQuotient Yₗ Yᵣ →ₗ[𝕜] StrongDual 𝕜 (Yₗ ⊓ Yᵣ : Submodule 𝕜 E) :=
  (continuousAnnihilator Yₗ ⊔ continuousAnnihilator Yᵣ).liftQ
    (continuousRestrict (Yₗ ⊓ Yᵣ))
    (sup_continuousAnnihilator_le_inf Yₗ Yᵣ)

@[simp] theorem twoBoundaryObserverRestriction_mk (Yₗ Yᵣ : Submodule 𝕜 E)
    (φ : StrongDual 𝕜 E) (x : (Yₗ ⊓ Yᵣ : Submodule 𝕜 E)) :
    twoBoundaryObserverRestriction Yₗ Yᵣ (Submodule.Quotient.mk φ) x = φ x := rfl

theorem twoBoundaryObserverRestriction_surjective (Yₗ Yᵣ : Submodule 𝕜 E) :
    Function.Surjective (twoBoundaryObserverRestriction Yₗ Yᵣ) := by
  intro ψ
  obtain ⟨φ, hφ⟩ := continuousRestrict_surjective (Yₗ ⊓ Yᵣ) ψ
  exact ⟨Submodule.Quotient.mk φ, by
    ext x
    exact DFunLike.congr_fun hφ x⟩

/-- **Card `(BHR.7)`, exactness at the observer quotient.** Its kernel is the image of the
topological descent radical. -/
theorem ker_twoBoundaryObserverRestriction (Yₗ Yᵣ : Submodule 𝕜 E) :
    LinearMap.ker (twoBoundaryObserverRestriction Yₗ Yᵣ) =
      Submodule.map
        (continuousAnnihilator Yₗ ⊔ continuousAnnihilator Yᵣ).mkQ
        (continuousAnnihilator (Yₗ ⊓ Yᵣ)) := by
  ext q
  induction q using Submodule.Quotient.induction_on with
  | H φ =>
      constructor
      · intro hφ
        have hr : continuousRestrict (Yₗ ⊓ Yᵣ) φ = 0 := hφ
        have hmem : φ ∈ continuousAnnihilator (Yₗ ⊓ Yᵣ) := by
          rw [← ker_continuousRestrict]
          exact hr
        exact ⟨φ, hmem, rfl⟩
      · rintro ⟨ψ, hψ, hq⟩
        rw [← hq]
        change continuousRestrict (Yₗ ⊓ Yᵣ) ψ = 0
        rw [ker_continuousRestrict]
        exact hψ

/-- Topological descent radical `(Yₗ ∩ Yᵣ)⊥ /(Yₗ⊥ + Yᵣ⊥)`. -/
abbrev topologicalDescentRadical (Yₗ Yᵣ : Submodule 𝕜 E) : Type _ :=
  continuousAnnihilator (Yₗ ⊓ Yᵣ) ⧸
    (continuousAnnihilator Yₗ ⊔ continuousAnnihilator Yᵣ).comap
      (continuousAnnihilator (Yₗ ⊓ Yᵣ)).subtype

/-- The radical quotient is canonically the kernel term in `(BHR.7)`. -/
noncomputable def topologicalDescentRadicalEquivKernel (Yₗ Yᵣ : Submodule 𝕜 E) :
    topologicalDescentRadical Yₗ Yᵣ ≃ₗ[𝕜]
      LinearMap.ker (twoBoundaryObserverRestriction Yₗ Yᵣ) := by
  let f : continuousAnnihilator (Yₗ ⊓ Yᵣ) →ₗ[𝕜]
      twoBoundaryObserverQuotient Yₗ Yᵣ :=
    (continuousAnnihilator Yₗ ⊔ continuousAnnihilator Yᵣ).mkQ.comp
      (continuousAnnihilator (Yₗ ⊓ Yᵣ)).subtype
  have hker : LinearMap.ker f =
      (continuousAnnihilator Yₗ ⊔ continuousAnnihilator Yᵣ).comap
        (continuousAnnihilator (Yₗ ⊓ Yᵣ)).subtype := by
    ext φ
    simp [f, Submodule.Quotient.mk_eq_zero]
  exact (Submodule.quotEquivOfEq _ _ hker).trans <|
    f.quotKerEquivRange.trans <|
      LinearEquiv.ofEq _ _ (ker_twoBoundaryObserverRestriction Yₗ Yᵣ).symm

/-- Every boundary-descending observer vanishes on every common retained law. -/
theorem boundaryObserver_vanishes_on_common
    {Yₗ Yᵣ : Submodule 𝕜 E} {φ : StrongDual 𝕜 E}
    (hφ : φ ∈ continuousAnnihilator Yₗ ⊔ continuousAnnihilator Yᵣ)
    {x : E} (hx : x ∈ Yₗ ⊓ Yᵣ) : φ x = 0 :=
  mem_continuousAnnihilator.mp
    (sup_continuousAnnihilator_le_inf Yₗ Yᵣ hφ) x hx

/-- **Card locality no-go.** Every nonzero common law is detected by a continuous observer that
cannot descend through the two boundary quotients. -/
theorem exists_detecting_nondescending_observer
    {Yₗ Yᵣ : Submodule 𝕜 E} {x : E} (hx : x ∈ Yₗ ⊓ Yᵣ) (hx0 : x ≠ 0) :
    ∃ φ : StrongDual 𝕜 E,
      φ x ≠ 0 ∧ φ ∉ continuousAnnihilator Yₗ ⊔ continuousAnnihilator Yᵣ := by
  obtain ⟨φ, _, hφx⟩ := exists_dual_vector 𝕜 x (norm_ne_zero_iff.mpr hx0)
  refine ⟨φ, ?_, ?_⟩
  · rw [hφx, RCLike.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr hx0
  · intro hdesc
    exact (boundaryObserver_vanishes_on_common hdesc hx) (by
      rw [hφx, RCLike.ofReal_ne_zero]
      exact norm_ne_zero_iff.mpr hx0)

end ContinuousObservers

/-! ## Covariance of the relative pairing -/

section Covariance

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Contragradient transport of a continuous observer. -/
noncomputable def transportObserver (T : E ≃L[𝕜] E) (φ : StrongDual 𝕜 E) :
    StrongDual 𝕜 E :=
  φ.comp T.symm.toContinuousLinearMap

theorem transportObserver_mem_annihilator (T : E ≃L[𝕜] E)
    {Y : Submodule 𝕜 E} {φ : StrongDual 𝕜 E} (hφ : φ ∈ continuousAnnihilator Y) :
    transportObserver T φ ∈ continuousAnnihilator (Y.map T.toLinearMap) := by
  rw [mem_continuousAnnihilator] at hφ ⊢
  rintro _ ⟨y, hy, rfl⟩
  simpa [transportObserver] using hφ y hy

/-- **Card `(BHR.18)`.** Co-moving law and observer transport preserves evaluation exactly. -/
theorem transportObserver_pairing (T : E ≃L[𝕜] E) (φ : StrongDual 𝕜 E) (x : E) :
    transportObserver T φ (T x) = φ x := by
  simp [transportObserver]

end Covariance

end HTGeometry.ConstraintRelativity
