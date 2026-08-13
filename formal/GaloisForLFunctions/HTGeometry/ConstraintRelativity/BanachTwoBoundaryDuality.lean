import GaloisForLFunctions.HTGeometry.ConstraintRelativity.ConormalPersistence
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
