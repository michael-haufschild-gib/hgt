import GaloisForLFunctions.HTGeometry.ConstraintRelativity.ConormalPersistence
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.FiniteReporterAdmission
import GaloisForLFunctions.HTGeometry.LocallyConvexDenseOfVanishingDual
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Two-boundary Banach observer duality

This file formalizes the exact two-boundary quotient, its degree-minus-one cone law, the
continuous observer-descent sequence, the topological descent radical, and covariance of the
relative pairing under continuous linear coordinate changes.
-/

namespace HTGeometry.ConstraintRelativity

local notation "𝕜" => ℂ

section TwoBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Continuous annihilator of a linear subspace. -/
noncomputable abbrev continuousAnnihilator (Y : Submodule 𝕜 E) :
    Submodule 𝕜 (StrongDual 𝕜 E) :=
  StrongDual.polarSubmodule 𝕜 Y

theorem mem_continuousAnnihilator {Y : Submodule 𝕜 E} {φ : StrongDual 𝕜 E} :
    φ ∈ continuousAnnihilator Y ↔ ∀ y ∈ Y, φ y = 0 :=
  StrongDual.mem_polarSubmodule 𝕜 Y φ

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
    (by
      rw [ker_continuousRestrict]
      exact sup_continuousAnnihilator_le_inf Yₗ Yᵣ)

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
        change ψ ∈ LinearMap.ker (continuousRestrict (Yₗ ⊓ Yᵣ))
        rw [ker_continuousRestrict]
        exact hψ

/-- Topological descent radical `(Yₗ ∩ Yᵣ)⊥ /(Yₗ⊥ + Yᵣ⊥)`, realized canonically as the image of
`(Yₗ ∩ Yᵣ)⊥` in the ambient observer quotient. -/
noncomputable abbrev topologicalDescentRadical (Yₗ Yᵣ : Submodule 𝕜 E) : Type _ :=
  Submodule.map
    (continuousAnnihilator Yₗ ⊔ continuousAnnihilator Yᵣ).mkQ
    (continuousAnnihilator (Yₗ ⊓ Yᵣ))

/-- The radical quotient is canonically the kernel term in `(BHR.7)`. -/
noncomputable def topologicalDescentRadicalEquivKernel (Yₗ Yᵣ : Submodule 𝕜 E) :
    topologicalDescentRadical Yₗ Yᵣ ≃ₗ[𝕜]
      LinearMap.ker (twoBoundaryObserverRestriction Yₗ Yᵣ) :=
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
  have hφne : φ x ≠ 0 := by
    rw [hφx, RCLike.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr hx0
  exact ⟨φ, hφne, fun hdesc => hφne (boundaryObserver_vanishes_on_common hdesc hx)⟩

/-! ### Weak-star descent radical -/

/-- The continuous annihilator, now equipped with the weak-star topology inherited from
`WeakDual`. -/
noncomputable def weakContinuousAnnihilator (Y : Submodule 𝕜 E) :
    Submodule 𝕜 (WeakDual 𝕜 E) :=
  (continuousAnnihilator Y).map StrongDual.toWeakDual.toLinearMap

theorem mem_weakContinuousAnnihilator {Y : Submodule 𝕜 E} {φ : WeakDual 𝕜 E} :
    φ ∈ weakContinuousAnnihilator Y ↔ ∀ y ∈ Y, φ y = 0 := by
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    simpa using (mem_continuousAnnihilator.mp hψ)
  · intro h
    refine ⟨WeakDual.toStrongDual φ, ?_, ?_⟩
    · exact mem_continuousAnnihilator.mpr h
    · rfl

theorem isClosed_weakContinuousAnnihilator (Y : Submodule 𝕜 E) :
    IsClosed (weakContinuousAnnihilator Y : Set (WeakDual 𝕜 E)) := by
  rw [show (weakContinuousAnnihilator Y : Set (WeakDual 𝕜 E)) =
      ⋂ y : Y, {φ | φ y = 0} by
    ext φ
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h y
      exact (mem_weakContinuousAnnihilator.mp h) y y.2
    · intro h
      exact mem_weakContinuousAnnihilator.mpr fun y hy => h ⟨y, hy⟩]
  exact isClosed_iInter fun y =>
    (isClosed_singleton : IsClosed ({0} : Set ℂ)).preimage
      (WeakDual.eval_continuous y.1)

/-- **Card `(BHR.8)`.** For closed boundary subspaces, the weak-star closure of the sum of their
continuous annihilators is exactly the annihilator of their intersection. -/
theorem weakStarClosure_sup_annihilator (Yₗ Yᵣ : Submodule 𝕜 E)
    (hYₗ : IsClosed (Yₗ : Set E)) (hYᵣ : IsClosed (Yᵣ : Set E)) :
    (weakContinuousAnnihilator Yₗ ⊔ weakContinuousAnnihilator Yᵣ).topologicalClosure =
      weakContinuousAnnihilator (Yₗ ⊓ Yᵣ) := by
  letI : IsScalarTower ℝ ℂ (StrongDual ℂ E) :=
    ⟨fun r c x => by
      apply ContinuousLinearMap.ext
      intro y
      simp only [smul_apply, Complex.real_smul]
      ring⟩
  letI : IsScalarTower ℝ ℂ (WeakDual ℂ E) :=
    ⟨fun r c x => by
      apply DFunLike.ext _ _
      intro y
      change (r : ℂ) * c * x y = (r : ℂ) * (c * x y)
      ring⟩
  letI : LocallyConvexSpace ℝ (WeakDual ℂ E) :=
    (topDualPairing ℂ E).weakBilin_withSeminorms.toLocallyConvexSpace
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · rw [sup_le_iff]
      constructor
      · intro φ hφ
        rw [mem_weakContinuousAnnihilator] at hφ ⊢
        exact fun y hy => hφ y hy.1
      · intro φ hφ
        rw [mem_weakContinuousAnnihilator] at hφ ⊢
        exact fun y hy => hφ y hy.2
    · exact isClosed_weakContinuousAnnihilator (Yₗ ⊓ Yᵣ)
  · intro φ hφ
    by_contra hnot
    let Sℂ : Submodule ℂ (WeakDual ℂ E) :=
      weakContinuousAnnihilator Yₗ ⊔ weakContinuousAnnihilator Yᵣ
    let Sℝ : Submodule ℝ (WeakDual ℂ E) := Sℂ.restrictScalars ℝ
    have hclosure :
        (Sℝ.topologicalClosure : Set (WeakDual ℂ E)) =
          (Sℂ.topologicalClosure : Set (WeakDual ℂ E)) := by
      rw [Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe]
      rfl
    have hφnot : φ ∉ Sℝ.topologicalClosure := by
      intro h
      apply hnot
      have h' : φ ∈ Sℂ.topologicalClosure := by
        have hs : φ ∈ (Sℝ.topologicalClosure : Set (WeakDual ℂ E)) := h
        rw [hclosure] at hs
        exact hs
      exact h'
    obtain ⟨f, hfS, hfφ⟩ :=
      HTGeometry.exists_dual_vanishing_of_notMem_closed_submodule_lcs
        Sℝ.topologicalClosure Sℝ.isClosed_topologicalClosure hφnot
    let g : StrongDual ℂ (WeakDual ℂ E) := StrongDual.extendRCLike f
    obtain ⟨x, hx⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℂ E) g
    have hg_eval : ∀ ψ : WeakDual ℂ E, g ψ = ψ x := by
      intro ψ
      have h := DFunLike.congr_fun hx ψ
      exact h.symm
    have hgS : ∀ ψ ∈ Sℂ, g ψ = 0 := by
      intro ψ hψ
      rw [StrongDual.extendRCLike_apply]
      have hψR : ψ ∈ Sℝ := hψ
      have hiψR : Complex.I • ψ ∈ Sℝ := by
        change Complex.I • ψ ∈ Sℂ
        exact Sℂ.smul_mem Complex.I hψ
      have hfI : f (RCLike.I • ψ) = 0 :=
        hfS _ (Sℝ.le_topologicalClosure hiψR)
      rw [hfS ψ (Sℝ.le_topologicalClosure hψR), hfI]
      simp
    have hxYₗ : x ∈ Yₗ := by
      by_contra hxnot
      obtain ⟨ψ, hψY, hψx⟩ :=
        HTGeometry.ConstraintMotiveRelativity.exists_continuous_annihilator_of_notMem_closure
          Yₗ (by rw [hYₗ.closure_eq]; exact hxnot)
      let ψw : WeakDual ℂ E := StrongDual.toWeakDual ψ
      have hψw : ψw ∈ Sℂ := by
        change ψw ∈ weakContinuousAnnihilator Yₗ ⊔ weakContinuousAnnihilator Yᵣ
        exact (le_sup_left : weakContinuousAnnihilator Yₗ ≤
          weakContinuousAnnihilator Yₗ ⊔ weakContinuousAnnihilator Yᵣ)
            ⟨ψ, mem_continuousAnnihilator.mpr hψY, rfl⟩
      apply hψx
      have hz : ψw x = 0 := (hg_eval ψw).symm.trans (hgS ψw hψw)
      simpa [ψw] using hz
    have hxYᵣ : x ∈ Yᵣ := by
      by_contra hxnot
      obtain ⟨ψ, hψY, hψx⟩ :=
        HTGeometry.ConstraintMotiveRelativity.exists_continuous_annihilator_of_notMem_closure
          Yᵣ (by rw [hYᵣ.closure_eq]; exact hxnot)
      let ψw : WeakDual ℂ E := StrongDual.toWeakDual ψ
      have hψw : ψw ∈ Sℂ := by
        change ψw ∈ weakContinuousAnnihilator Yₗ ⊔ weakContinuousAnnihilator Yᵣ
        exact (le_sup_right : weakContinuousAnnihilator Yᵣ ≤
          weakContinuousAnnihilator Yₗ ⊔ weakContinuousAnnihilator Yᵣ)
            ⟨ψ, mem_continuousAnnihilator.mpr hψY, rfl⟩
      apply hψx
      have hz : ψw x = 0 := (hg_eval ψw).symm.trans (hgS ψw hψw)
      simpa [ψw] using hz
    have hφx : φ x = 0 :=
      (mem_weakContinuousAnnihilator.mp hφ) x ⟨hxYₗ, hxYᵣ⟩
    have hgφ : g φ ≠ 0 := by
      intro hzero
      change StrongDual.extendRCLike f φ = 0 at hzero
      rw [StrongDual.extendRCLike_apply] at hzero
      have hre := congrArg Complex.re hzero
      exact hfφ (by simpa using hre)
    apply hgφ
    rw [hg_eval, hφx]

end ContinuousObservers

/-! ## Covariance of the relative pairing -/

section Covariance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

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

/-! ## Nested cut layer -/

section NestedCut

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- **Card `(BHR.12)`.** For nested cuts `M(b) ≤ M(a)`, the comparison-map kernel is the
literal intermediate quotient layer `M(a)/M(b)`, realized as its canonical image in `M/M(b)`. -/
theorem nestedCut_ker {Ma Mb : Submodule ℂ M} (h : Mb ≤ Ma) :
    LinearMap.ker (persistenceMap h) = Submodule.map Mb.mkQ Ma :=
  ker_persistenceMap h

end NestedCut

/-! ## Normal predual of a nested layer -/

section NormalPredualLayer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Normal functionals from a specified predual copy which annihilate a cut. -/
def normalAnnihilator (P : Submodule 𝕜 (StrongDual 𝕜 E)) (Y : Submodule 𝕜 E) :
    Submodule 𝕜 P where
  carrier := {ω | ∀ y ∈ Y, (ω.1 : StrongDual 𝕜 E) y = 0}
  zero_mem' := by simp
  add_mem' hω hη y hy := by simp [hω y hy, hη y hy]
  smul_mem' c ω hω y hy := by simp [hω y hy]

/-- Explicit additive structure avoids reducibility loops for the nested annihilator subtype. -/
noncomputable instance normalAnnihilatorAddCommGroup
    (P : Submodule 𝕜 (StrongDual 𝕜 E)) (Y : Submodule 𝕜 E) :
    AddCommGroup (normalAnnihilator P Y) :=
  @Submodule.addCommGroup ℂ P inferInstance P.addCommGroup P.module
    (normalAnnihilator P Y)

/-- The lower cut as a subspace of the upper cut. -/
def nestedLayerDenominator (Mb Ma : Submodule 𝕜 E) : Submodule 𝕜 Ma :=
  Mb.comap Ma.subtype

/-- Literal nested layer `Ma / Mb`. -/
abbrev NormalNestedLayer (Mb Ma : Submodule 𝕜 E) := Ma ⧸ nestedLayerDenominator Mb Ma

/-- Restrict a lower-cut-annihilating normal functional to the relative layer. -/
noncomputable def normalLayerRestriction
    (P : Submodule 𝕜 (StrongDual 𝕜 E)) (Mb Ma : Submodule 𝕜 E) :
    normalAnnihilator P Mb →ₗ[𝕜] Module.Dual 𝕜 (NormalNestedLayer Mb Ma) where
  toFun ω := (nestedLayerDenominator Mb Ma).liftQ
    { toFun := fun x => (ω.1.1 : StrongDual 𝕜 E) x.1
      map_add' := by intros; simp
      map_smul' := by intros; simp }
    (by
      intro x hx
      exact ω.2 x.1 hx)
  map_add' ω η := by
    ext x
    rfl
  map_smul' c ω := by
    ext x
    rfl

@[simp] theorem normalLayerRestriction_mk
    (P : Submodule 𝕜 (StrongDual 𝕜 E)) (Mb Ma : Submodule 𝕜 E)
    (ω : normalAnnihilator P Mb) (x : Ma) :
    normalLayerRestriction P Mb Ma ω (Submodule.Quotient.mk x) =
      (ω.1.1 : StrongDual 𝕜 E) x.1 := rfl

/-- Upper-cut annihilators include canonically among lower-cut annihilators. -/
def normalAnnihilatorInclusion
    (P : Submodule 𝕜 (StrongDual 𝕜 E)) {Mb Ma : Submodule 𝕜 E} (h : Mb ≤ Ma) :
    normalAnnihilator P Ma →ₗ[𝕜] normalAnnihilator P Mb where
  toFun ω := ⟨ω.1, fun y hy => ω.2 y (h hy)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Kernel of layer restriction is exactly the upper-cut annihilator. -/
theorem ker_normalLayerRestriction
    (P : Submodule 𝕜 (StrongDual 𝕜 E)) {Mb Ma : Submodule 𝕜 E} (h : Mb ≤ Ma) :
    LinearMap.ker (normalLayerRestriction P Mb Ma) =
      LinearMap.range (normalAnnihilatorInclusion P h) := by
  ext ω
  constructor
  · intro hω
    have hzero : ∀ x : Ma, (ω.1.1 : StrongDual 𝕜 E) x.1 = 0 := by
      intro x
      have hx := DFunLike.congr_fun hω (Submodule.Quotient.mk x)
      simpa using hx
    let η : normalAnnihilator P Ma := ⟨ω.1, fun y hy => hzero ⟨y, hy⟩⟩
    exact ⟨η, rfl⟩
  · rintro ⟨η, rfl⟩
    ext x
    exact η.2 x.1 x.2

/-- Realized normal functionals on the relative layer. -/
noncomputable abbrev normalNestedLayerPredual
    (P : Submodule 𝕜 (StrongDual 𝕜 E)) (Mb Ma : Submodule 𝕜 E) :=
  LinearMap.range (normalLayerRestriction P Mb Ma)

/-- **Card `(BHR.14)`, exact normal-predual quotient theorem.** Lower-cut normal annihilators
modulo upper-cut normal annihilators are canonically the normal functionals realized on the
relative layer. The representative pairing is `(BHR.15)` by `normalLayerRestriction_mk`. -/
noncomputable def normalAnnihilatorQuotientEquivLayerPredual
    (P : Submodule 𝕜 (StrongDual 𝕜 E)) (Mb Ma : Submodule 𝕜 E) :
    ((normalAnnihilator P Mb) ⧸ LinearMap.ker (normalLayerRestriction P Mb Ma)) ≃ₗ[𝕜]
      normalNestedLayerPredual P Mb Ma :=
  LinearMap.quotKerEquivRange (normalLayerRestriction P Mb Ma)

end NormalPredualLayer

/-! ## Isometric predual model of weak-star nested cuts -/

section QuotientIsometryTransport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A surjective linear isometry transports the quotient norm when it identifies the two
denominators. -/
theorem quotientNorm_transport
    (d : E ≃ₗᵢ[𝕜] F) (K : Submodule 𝕜 E) (K' : Submodule 𝕜 F)
    (hK : ∀ y : F, y ∈ K' ↔ d.symm y ∈ K) (x : E) :
    ‖(Submodule.Quotient.mk (d x) : F ⧸ K')‖ =
      ‖(Submodule.Quotient.mk x : E ⧸ K)‖ := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨m, hm, hmnorm⟩ :=
      Submodule.Quotient.norm_mk_lt (S := K) (Submodule.Quotient.mk x) hε
    have hmem : d m - d x ∈ K' := by
      refine (hK _).mpr ?_
      rw [← map_sub, LinearIsometryEquiv.symm_apply_apply]
      exact (Submodule.Quotient.eq K).mp hm
    have hmk : (Submodule.Quotient.mk (d m) : F ⧸ K') = Submodule.Quotient.mk (d x) :=
      (Submodule.Quotient.eq K').mpr hmem
    calc
      ‖(Submodule.Quotient.mk (d x) : F ⧸ K')‖
          = ‖(Submodule.Quotient.mk (d m) : F ⧸ K')‖ := by rw [hmk]
      _ ≤ ‖d m‖ := Submodule.Quotient.norm_mk_le K' _
      _ = ‖m‖ := d.norm_map m
      _ ≤ ‖(Submodule.Quotient.mk x : E ⧸ K)‖ + ε := le_of_lt hmnorm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨n, hn, hnnorm⟩ :=
      Submodule.Quotient.norm_mk_lt (S := K') (Submodule.Quotient.mk (d x)) hε
    have hmem : d.symm n - x ∈ K := by
      have hnk : n - d x ∈ K' := (Submodule.Quotient.eq K').mp hn
      have := (hK _).mp hnk
      rwa [map_sub, LinearIsometryEquiv.symm_apply_apply] at this
    have hmk : (Submodule.Quotient.mk (d.symm n) : E ⧸ K) = Submodule.Quotient.mk x :=
      (Submodule.Quotient.eq K).mpr hmem
    calc
      ‖(Submodule.Quotient.mk x : E ⧸ K)‖
          = ‖(Submodule.Quotient.mk (d.symm n) : E ⧸ K)‖ := by rw [hmk]
      _ ≤ ‖d.symm n‖ := Submodule.Quotient.norm_mk_le K _
      _ = ‖n‖ := d.symm.norm_map n
      _ ≤ ‖(Submodule.Quotient.mk (d x) : F ⧸ K')‖ + ε := le_of_lt hnnorm

/-- A surjective linear isometry identifying two submodules descends to an isometric linear
equivalence of their normed quotients. -/
noncomputable def quotientIsometryTransport
    (d : E ≃ₗᵢ[𝕜] F) (K : Submodule 𝕜 E) (K' : Submodule 𝕜 F)
    (hK : ∀ y : F, y ∈ K' ↔ d.symm y ∈ K) :
    (E ⧸ K) ≃ₗᵢ[𝕜] (F ⧸ K') where
  toLinearEquiv :=
    LinearEquiv.ofLinear
      (K.mapQ K' (d.toLinearEquiv : E →ₗ[𝕜] F) (fun x hx => by
        refine (hK _).mpr ?_
        simpa using hx))
      (K'.mapQ K (d.symm.toLinearEquiv : F →ₗ[𝕜] E) (fun y hy => (hK y).mp hy))
      (by
        refine LinearMap.ext fun q => ?_
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        show Submodule.Quotient.mk (d (d.symm y)) = _
        rw [LinearIsometryEquiv.apply_symm_apply]
        rfl)
      (by
        refine LinearMap.ext fun q => ?_
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        show Submodule.Quotient.mk (d.symm (d x)) = _
        rw [LinearIsometryEquiv.symm_apply_apply]
        rfl)
  norm_map' := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact quotientNorm_transport d K K' hK x

end QuotientIsometryTransport

section WeakStarPredualLayer

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- Weak-star closed cut presented as the annihilator in `P*` of a norm-closed predual
subspace. -/
noncomputable def weakStarCut (A : Submodule 𝕜 P) : Submodule 𝕜 (StrongDual 𝕜 P) :=
  continuousAnnihilator A

/-- Preannihilator of a dual subspace. -/
noncomputable def predualAnnihilator
    (Y : Submodule 𝕜 (StrongDual 𝕜 P)) : Submodule 𝕜 P where
  carrier := {x | ∀ φ ∈ Y, φ x = 0}
  zero_mem' := by simp
  add_mem' hx hy φ hφ := by simp [hx φ hφ, hy φ hφ]
  smul_mem' c x hx φ hφ := by simp [hx φ hφ]

/-- Hahn--Banach double-annihilator recovery: a norm-closed predual subspace is exactly the
preannihilator of its weak-star cut. -/
theorem predualAnnihilator_weakStarCut (A : Submodule 𝕜 P)
    (hA : IsClosed (A : Set P)) :
    predualAnnihilator (weakStarCut A) = A := by
  apply le_antisymm
  · intro x hx
    by_contra hnot
    obtain ⟨φ, hφA, hφx⟩ :=
      HTGeometry.ConstraintMotiveRelativity.exists_continuous_annihilator_of_notMem_closure
        A (by rw [hA.closure_eq]; exact hnot)
    exact hφx (hx φ (mem_continuousAnnihilator.mpr hφA))
  · intro x hx φ hφ
    exact (mem_continuousAnnihilator.mp hφ) x hx

/-- Predual quotient recovered canonically from two weak-star cuts. -/
abbrev weakStarNormalObserverQuotient (A B : Submodule 𝕜 P) :=
  (predualAnnihilator (weakStarCut B)) ⧸
    nestedLayerDenominator
      (predualAnnihilator (weakStarCut A))
      (predualAnnihilator (weakStarCut B))

/-- **Card `(BHR.14)`, isometric predual theorem.** For closed predual subspaces `A` and `B`,
the normal-observer quotient recovered from their weak-star annihilator cuts is canonically
linearly isometric to the literal relative layer `B/A` (with the denominator interpreted inside
`B`). -/
noncomputable def weakStarNormalObserverQuotientIsometry
    (A B : Submodule 𝕜 P) (hA : IsClosed (A : Set P)) (hB : IsClosed (B : Set P)) :
    weakStarNormalObserverQuotient A B ≃ₗᵢ[𝕜] NormalNestedLayer A B := by
  let PA := predualAnnihilator (weakStarCut A)
  let PB := predualAnnihilator (weakStarCut B)
  have hPA : PA = A := predualAnnihilator_weakStarCut A hA
  have hPB : PB = B := predualAnnihilator_weakStarCut B hB
  let d : PB ≃ₗᵢ[𝕜] B := LinearIsometryEquiv.ofEq PB B hPB
  exact quotientIsometryTransport d
    (nestedLayerDenominator PA PB) (nestedLayerDenominator A B) (by
      intro y
      change ((y : P) ∈ A) ↔ ((d.symm y : PB) : P) ∈ PA
      rw [hPA]
      rfl)

end WeakStarPredualLayer

/-! ## Finite thermofield countermodel -/

section FiniteThermofield

/-- Standard finite thermofield carrier `H ⊗ H̄`, in matrix coordinates. -/
abbrev ThermofieldSpace (n : ℕ) := (Fin n × Fin n) → ℂ

/-- Left boundary sector with first coordinate fixed at `i`. -/
def thermofieldLeftBoundary {n : ℕ} (i : Fin n) :
    Submodule ℂ (ThermofieldSpace n) where
  carrier := {x | ∀ p, p.1 ≠ i → x p = 0}
  zero_mem' := by simp
  add_mem' hx hy p hp := by simp [hx p hp, hy p hp]
  smul_mem' c x hx p hp := by simp [hx p hp]

/-- Right boundary sector with second coordinate fixed at `j`. -/
def thermofieldRightBoundary {n : ℕ} (j : Fin n) :
    Submodule ℂ (ThermofieldSpace n) where
  carrier := {x | ∀ p, p.2 ≠ j → x p = 0}
  zero_mem' := by simp
  add_mem' hx hy p hp := by simp [hx p hp, hy p hp]
  smul_mem' c x hx p hp := by simp [hx p hp]

/-- Matrix unit `eᵢ ⊗ ēⱼ`. -/
noncomputable def thermofieldBasis {n : ℕ} (i j : Fin n) : ThermofieldSpace n :=
  Pi.single (i, j) 1

/-- **Card `(BHR.23)`.** The two coordinate boundary sectors intersect in exactly one line. -/
theorem thermofield_boundary_intersection {n : ℕ} (i j : Fin n) :
    thermofieldLeftBoundary i ⊓ thermofieldRightBoundary j =
      ℂ ∙ thermofieldBasis i j := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_span_singleton]
    refine ⟨x (i, j), ?_⟩
    funext p
    by_cases hp : p = (i, j)
    · subst p
      simp [thermofieldBasis]
    · have hcoord : p.1 ≠ i ∨ p.2 ≠ j := by
        by_cases hleft : p.1 = i
        · exact Or.inr fun hright => hp (Prod.ext hleft hright)
        · exact Or.inl hleft
      rcases hcoord with hleft | hright
      · have hz := hx.1 p hleft
        simp [thermofieldBasis, hp, hz]
      · have hz := hx.2 p hright
        simp [thermofieldBasis, hp, hz]
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    constructor
    · intro p hp
      have hpair : p ≠ (i, j) := fun h => hp (congrArg Prod.fst h)
      simp [thermofieldBasis, hpair]
    · intro p hp
      have hpair : p ≠ (i, j) := fun h => hp (congrArg Prod.snd h)
      simp [thermofieldBasis, hpair]

/-- Diagonal modular flow associated to positive density eigenvalues `rᵢ`. -/
noncomputable def thermofieldModularFlow {n : ℕ} (r : Fin n → ℝ) (t : ℝ) :
    ThermofieldSpace n →ₗ[ℂ] ThermofieldSpace n where
  toFun x p :=
    Complex.exp (Complex.I * (t : ℂ) *
      ((Real.log (r p.1) : ℂ) - (Real.log (r p.2) : ℂ))) * x p
  map_add' x y := by ext p; simp [mul_add]
  map_smul' c x := by ext p; simp [mul_assoc, mul_left_comm]

/-- **Card `(BHR.24)`.** Every retained thermofield line is an exact modular eigenline with
frequency `log rᵢ - log rⱼ`. -/
theorem thermofieldModularFlow_basis {n : ℕ} (r : Fin n → ℝ) (t : ℝ) (i j : Fin n) :
    thermofieldModularFlow r t (thermofieldBasis i j) =
      Complex.exp (Complex.I * (t : ℂ) *
        ((Real.log (r i) : ℂ) - (Real.log (r j) : ℂ))) • thermofieldBasis i j := by
  funext p
  by_cases hp : p = (i, j)
  · subst p
    simp [thermofieldModularFlow, thermofieldBasis]
  · simp [thermofieldModularFlow, thermofieldBasis, hp]

/-- Both boundary quotients erase the thermofield matrix unit. -/
theorem thermofieldBasis_erased {n : ℕ} (i j : Fin n) :
    (Submodule.Quotient.mk (thermofieldBasis i j) :
        ThermofieldSpace n ⧸ thermofieldLeftBoundary i) = 0 ∧
      (Submodule.Quotient.mk (thermofieldBasis i j) :
        ThermofieldSpace n ⧸ thermofieldRightBoundary j) = 0 := by
  constructor <;> rw [Submodule.Quotient.mk_eq_zero]
  · intro p hp
    have hpair : p ≠ (i, j) := fun h => hp (congrArg Prod.fst h)
    simp [thermofieldBasis, hpair]
  · intro p hp
    have hpair : p ≠ (i, j) := fun h => hp (congrArg Prod.snd h)
    simp [thermofieldBasis, hpair]

end FiniteThermofield

end HTGeometry.ConstraintRelativity
