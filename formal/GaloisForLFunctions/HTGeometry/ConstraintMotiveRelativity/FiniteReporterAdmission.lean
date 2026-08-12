import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PrimeAugmentationCompletion

/-!
# Finite-reporter admission and hyperbolic reduction

A finite-dimensional space `L` of algebraic reporters on a chart `X₀` cuts out the constraint
`I = L^⊥`.  Along a dense linear map `j : X₀ → X` into a normed space, only the *admitted*
reporters — those factoring through a continuous functional on `X` — survive.

The completed constraint is the joint kernel of the admitted reporters, restriction along `j`
identifies the continuous annihilator of the completed constraint with the admitted reporter space,
and the algebraic and completed reductions of the cotangent double differ exactly by the perfect
hyperbolic pair built on `L/L_X`.
-/

namespace HTGeometry.ConstraintMotiveRelativity

section Separation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Hahn–Banach separation for subspaces.**  A point outside the closure of a subspace is
separated from it by a continuous functional annihilating the subspace.  A real separating
functional is bounded above on the subspace, hence vanishes on it, and its `ℂ`-extension inherits
both properties. -/
theorem exists_continuous_annihilator_of_notMem_closure (S : Submodule ℂ E) {x : E}
    (hx : x ∉ closure (S : Set E)) :
    ∃ φ : E →L[ℂ] ℂ, (∀ y ∈ S, φ y = 0) ∧ φ x ≠ 0 := by
  set T : Submodule ℝ E := (S.restrictScalars ℝ).topologicalClosure with hT
  have hTset : (T : Set E) = closure (S : Set E) := by
    rw [hT, Submodule.topologicalClosure_coe]
    rfl
  have hxT : x ∉ (T : Set E) := by rw [hTset]; exact hx
  obtain ⟨f, u, hfu, hux⟩ :=
    geometric_hahn_banach_closed_point (T.convex) (Submodule.isClosed_topologicalClosure _) hxT
  have hmemT : ∀ (t : ℝ) {a : E}, a ∈ S → t • a ∈ (T : Set E) := by
    intro t a ha
    exact Submodule.le_topologicalClosure _ ((S.restrictScalars ℝ).smul_mem t ha)
  have hzero : ∀ y ∈ S, f y = 0 := by
    intro y hy
    by_contra hne
    have h1 : f (((u + 1) / f y) • y) < u := hfu _ (hmemT ((u + 1) / f y) hy)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at h1
    linarith
  have hu0 : 0 < u := by
    have h0 : f (0 : E) < u := hfu 0 T.zero_mem
    simpa using h0
  refine ⟨StrongDual.extendRCLike (𝕜 := ℂ) f, fun y hy => ?_, ?_⟩
  · have hsmul : ∀ a : ℂ, f (a • y) = 0 := fun a => hzero _ (S.smul_mem a hy)
    rw [StrongDual.extendRCLike_apply, hzero y hy, hsmul]
    simp
  · intro hcon
    have := StrongDual.re_extendRCLike_apply (𝕜 := ℂ) f x
    rw [hcon] at this
    simp only [map_zero] at this
    linarith [this ▸ hux]

end Separation

section FiniteReporter

variable {X₀ : Type*} [AddCommGroup X₀] [Module ℂ X₀]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Restriction of a continuous reporter along `j`. -/
noncomputable def restrictAlong (j : X₀ →ₗ[ℂ] X) : (X →L[ℂ] ℂ) →ₗ[ℂ] Module.Dual ℂ X₀ where
  toFun φ := (φ : X →ₗ[ℂ] ℂ).comp j
  map_add' φ ψ := by ext x; simp
  map_smul' a φ := by ext x; simp

@[simp] theorem restrictAlong_apply (j : X₀ →ₗ[ℂ] X) (φ : X →L[ℂ] ℂ) (x : X₀) :
    restrictAlong j φ x = φ (j x) := rfl

/-- A continuous reporter is determined by its restriction along a dense map. -/
theorem restrictAlong_injective {j : X₀ →ₗ[ℂ] X} (hj : DenseRange j) :
    Function.Injective (restrictAlong j) := by
  intro φ ψ h
  have hcomp : (φ : X → ℂ) ∘ (j : X₀ → X) = (ψ : X → ℂ) ∘ (j : X₀ → X) := by
    funext x
    exact congrFun (congrArg DFunLike.coe h) x
  exact ContinuousLinearMap.coe_injective
    (LinearMap.coe_injective (hj.equalizer φ.continuous ψ.continuous hcomp))

/-- **`(FR.3)`.**  The admitted reporter subspace `L_X`: reporters of `L` that extend continuously
along `j`. -/
noncomputable def admitted (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀)) :
    Submodule ℂ (Module.Dual ℂ X₀) := L ⊓ LinearMap.range (restrictAlong j)

theorem mem_admitted_iff {j : X₀ →ₗ[ℂ] X} {L : Submodule ℂ (Module.Dual ℂ X₀)}
    {lam : Module.Dual ℂ X₀} :
    lam ∈ admitted j L ↔ lam ∈ L ∧ ∃ φ : X →L[ℂ] ℂ, ∀ x, φ (j x) = lam x := by
  constructor
  · rintro ⟨hL, φ, hφ⟩
    exact ⟨hL, φ, fun x => congrFun (congrArg DFunLike.coe hφ) x⟩
  · rintro ⟨hL, φ, hφ⟩
    exact ⟨hL, φ, by ext x; exact hφ x⟩

theorem admitted_le (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀)) :
    admitted j L ≤ L := inf_le_left

/-- The continuous annihilator of a subspace of `X`. -/
noncomputable def contAnnihilator (S : Submodule ℂ X) : Submodule ℂ (X →L[ℂ] ℂ) where
  carrier := {φ | ∀ y ∈ S, φ y = 0}
  zero_mem' := by intro y _; rfl
  add_mem' := by
    intro φ ψ hφ hψ y hy
    simp [hφ y hy, hψ y hy]
  smul_mem' := by
    intro a φ hφ y hy
    simp [hφ y hy]

@[simp] theorem mem_contAnnihilator {S : Submodule ℂ X} {φ : X →L[ℂ] ℂ} :
    φ ∈ contAnnihilator S ↔ ∀ y ∈ S, φ y = 0 := Iff.rfl

/-- **`(FR.15)`.**  A finite-dimensional reporter space is recovered from its constraint. -/
theorem dualAnnihilator_dualCoannihilator (L : Submodule ℂ (Module.Dual ℂ X₀))
    [FiniteDimensional ℂ L] : L.dualCoannihilator.dualAnnihilator = L :=
  Subspace.dualCoannihilator_dualAnnihilator_eq

/-- A continuous reporter whose restriction lies in `L` annihilates the constraint. -/
theorem apply_eq_zero_of_mem_dualCoannihilator {j : X₀ →ₗ[ℂ] X}
    {L : Submodule ℂ (Module.Dual ℂ X₀)} {φ : X →L[ℂ] ℂ} (hφ : restrictAlong j φ ∈ L)
    {x : X₀} (hx : x ∈ L.dualCoannihilator) : φ (j x) = 0 :=
  ((Submodule.mem_dualCoannihilator x).mp hx) _ hφ

/-- **`(FR.4)`.**  The completed constraint is the joint kernel of the admitted reporters. -/
theorem closure_map_dualCoannihilator (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀))
    [FiniteDimensional ℂ L] :
    closure ((L.dualCoannihilator.map j : Submodule ℂ X) : Set X)
      = {x : X | ∀ φ : X →L[ℂ] ℂ, restrictAlong j φ ∈ L → φ x = 0} := by
  apply Set.Subset.antisymm
  · intro x hx φ hφ
    have hsub : closure ((L.dualCoannihilator.map j : Submodule ℂ X) : Set X) ⊆ φ ⁻¹' {0} := by
      refine closure_minimal ?_ (IsClosed.preimage φ.continuous isClosed_singleton)
      rintro z hz
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
      exact apply_eq_zero_of_mem_dualCoannihilator hφ hy
    exact hsub hx
  · intro x hx
    by_contra hne
    obtain ⟨φ, hφ0, hφx⟩ :=
      exists_continuous_annihilator_of_notMem_closure (L.dualCoannihilator.map j) hne
    refine hφx (hx φ ?_)
    rw [← dualAnnihilator_dualCoannihilator L, Submodule.mem_dualAnnihilator]
    intro y hy
    exact hφ0 _ (Submodule.mem_map_of_mem hy)

/-- The restriction of a continuous annihilator of the completed constraint is admitted. -/
theorem restrictAlong_mem_admitted {j : X₀ →ₗ[ℂ] X} {L : Submodule ℂ (Module.Dual ℂ X₀)}
    [FiniteDimensional ℂ L] {φ : X →L[ℂ] ℂ}
    (hφ : φ ∈ contAnnihilator (L.dualCoannihilator.map j)) :
    restrictAlong j φ ∈ admitted j L := by
  refine ⟨?_, ⟨φ, rfl⟩⟩
  rw [← dualAnnihilator_dualCoannihilator L]
  exact (Submodule.mem_dualAnnihilator _).mpr fun y hy => hφ _ (Submodule.mem_map_of_mem hy)

/-- **`(FR.6)`, surjectivity.**  Every admitted reporter is the restriction of a continuous
annihilator of the completed constraint. -/
theorem exists_contAnnihilator_of_mem_admitted {j : X₀ →ₗ[ℂ] X}
    {L : Submodule ℂ (Module.Dual ℂ X₀)} {lam : Module.Dual ℂ X₀} (hlam : lam ∈ admitted j L) :
    ∃ φ ∈ contAnnihilator (L.dualCoannihilator.map j), restrictAlong j φ = lam := by
  obtain ⟨hL, φ, hφ⟩ := hlam
  refine ⟨φ, ?_, hφ⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  have : restrictAlong j φ z = 0 := ((Submodule.mem_dualCoannihilator z).mp hz) _ (hφ ▸ hL)
  exact this

/-- **`(FR.6)`.**  Restriction along a dense `j` is a linear isomorphism from the continuous
annihilator of the completed constraint onto the admitted reporter space. -/
noncomputable def resEquiv (j : X₀ →ₗ[ℂ] X) (hj : DenseRange j)
    (L : Submodule ℂ (Module.Dual ℂ X₀)) [FiniteDimensional ℂ L] :
    contAnnihilator (L.dualCoannihilator.map j) ≃ₗ[ℂ] admitted j L :=
  LinearEquiv.ofBijective
    ((restrictAlong j).restrict (p := contAnnihilator (L.dualCoannihilator.map j))
      (q := admitted j L) (fun _ hφ => restrictAlong_mem_admitted hφ))
    ⟨fun φ ψ h => Subtype.ext (restrictAlong_injective hj (Subtype.ext_iff.mp h)),
      fun lam => by
        obtain ⟨φ, hφmem, hφ⟩ := exists_contAnnihilator_of_mem_admitted lam.2
        exact ⟨⟨φ, hφmem⟩, Subtype.ext hφ⟩⟩

/-- **`(FR.7)`.**  The algebraic quotient is the dual of the reporter space. -/
noncomputable def algQuotEquiv (L : Submodule ℂ (Module.Dual ℂ X₀)) [FiniteDimensional ℂ L] :
    (X₀ ⧸ L.dualCoannihilator) ≃ₗ[ℂ] Module.Dual ℂ L :=
  LinearEquiv.ofBijective _ (Subspace.quotDualCoannihilatorToDual_bijective L)

/-! ### The completed quotient -/

/-- The bipolar description of the closure of a subspace: it is the joint kernel of the continuous
functionals annihilating the subspace. -/
theorem topologicalClosure_eq_ker_contAnnihilator (S : Submodule ℂ X) :
    ((S.topologicalClosure : Submodule ℂ X) : Set X)
      = {x : X | ∀ φ ∈ contAnnihilator S, φ x = 0} := by
  rw [Submodule.topologicalClosure_coe]
  apply Set.Subset.antisymm
  · intro x hx φ hφ
    have hsub : closure (S : Set X) ⊆ φ ⁻¹' {0} :=
      closure_minimal (fun z hz => hφ z hz) (IsClosed.preimage φ.continuous isClosed_singleton)
    exact hsub hx
  · intro x hx
    by_contra hne
    obtain ⟨φ, hφ0, hφx⟩ := exists_continuous_annihilator_of_notMem_closure S hne
    exact hφx (hx φ hφ0)

/-- **`(FR.16)`.**  Evaluation of the completed chart against the continuous annihilator. -/
noncomputable def evalCont (S : Submodule ℂ X) : X →ₗ[ℂ] Module.Dual ℂ (contAnnihilator S) where
  toFun x :=
    { toFun := fun φ => (φ : X →L[ℂ] ℂ) x
      map_add' := fun φ ψ => rfl
      map_smul' := fun a φ => rfl }
  map_add' x y := by ext φ; simp
  map_smul' a x := by ext φ; simp

@[simp] theorem evalCont_apply (S : Submodule ℂ X) (x : X) (φ : contAnnihilator S) :
    evalCont S x φ = (φ : X →L[ℂ] ℂ) x := rfl

theorem ker_evalCont (S : Submodule ℂ X) :
    LinearMap.ker (evalCont S) = S.topologicalClosure := by
  have hset := topologicalClosure_eq_ker_contAnnihilator S
  ext x
  constructor
  · intro hx
    refine (Set.ext_iff.mp hset x).mpr fun φ hφ => ?_
    exact congrFun (congrArg DFunLike.coe hx) ⟨φ, hφ⟩
  · intro hx
    have h := (Set.ext_iff.mp hset x).mp hx
    ext φ
    exact h φ.1 φ.2

/-- The continuous annihilator read inside the algebraic dual. -/
noncomputable def contAnnihilatorAlg (S : Submodule ℂ X) : Submodule ℂ (Module.Dual ℂ X) :=
  (contAnnihilator S).map (ContinuousLinearMap.coeLM ℂ)

/-- The two readings of the continuous annihilator agree. -/
noncomputable def contAnnihilatorAlgEquiv (S : Submodule ℂ X) :
    contAnnihilator S ≃ₗ[ℂ] contAnnihilatorAlg S :=
  Submodule.equivMapOfInjective _
    (fun _ _ h => ContinuousLinearMap.coe_injective h) (contAnnihilator S)

@[simp] theorem contAnnihilatorAlgEquiv_apply (S : Submodule ℂ X) (φ : contAnnihilator S) (x : X) :
    ((contAnnihilatorAlgEquiv S φ : Module.Dual ℂ X)) x = (φ : X →L[ℂ] ℂ) x := rfl

/-- **`(FR.4)`, bipolar form.**  The coannihilator of the continuous annihilator is the closure. -/
theorem dualCoannihilator_contAnnihilatorAlg (S : Submodule ℂ X) :
    (contAnnihilatorAlg S).dualCoannihilator = S.topologicalClosure := by
  have hset := topologicalClosure_eq_ker_contAnnihilator S
  ext x
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h
    exact (Set.ext_iff.mp hset x).mpr fun φ hφ => h _ ⟨φ, hφ, rfl⟩
  · rintro hx ψ ⟨φ, hφ, rfl⟩
    exact ((Set.ext_iff.mp hset x).mp hx) φ hφ

/-- **`(FR.16)`.**  Evaluation factors through the nondegenerate quotient pairing. -/
theorem evalCont_eq (S : Submodule ℂ X) (x : X) :
    evalCont S x = (contAnnihilatorAlgEquiv S).dualMap
      ((contAnnihilatorAlg S).quotDualCoannihilatorToDual (Submodule.Quotient.mk x)) := by
  ext φ
  rfl

/-- **`(FR.16)`.**  Evaluation against a finite-dimensional continuous annihilator is onto. -/
theorem evalCont_surjective (S : Submodule ℂ X) [FiniteDimensional ℂ (contAnnihilator S)] :
    Function.Surjective (evalCont S) := by
  haveI : Module.Finite ℂ (contAnnihilatorAlg S) :=
    Module.Finite.equiv (contAnnihilatorAlgEquiv S)
  intro ξ
  obtain ⟨y, hy⟩ := (Subspace.quotDualCoannihilatorToDual_bijective
    (contAnnihilatorAlg S)).2 ((contAnnihilatorAlgEquiv S).dualMap.symm ξ)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine ⟨x, ?_⟩
  rw [evalCont_eq, hy, LinearEquiv.apply_symm_apply]

/-- **`(FR.5)`.**  The completed quotient is the dual of the admitted reporter space. -/
noncomputable def completedQuotEquiv (j : X₀ →ₗ[ℂ] X) (hj : DenseRange j)
    (L : Submodule ℂ (Module.Dual ℂ X₀)) [FiniteDimensional ℂ L] :
    (X ⧸ (L.dualCoannihilator.map j).topologicalClosure) ≃ₗ[ℂ]
      Module.Dual ℂ (admitted j L) := by
  haveI : FiniteDimensional ℂ (admitted j L) := Submodule.finiteDimensional_of_le (admitted_le j L)
  haveI : FiniteDimensional ℂ (contAnnihilator (L.dualCoannihilator.map j)) :=
    LinearEquiv.finiteDimensional (resEquiv j hj L).symm
  exact (Submodule.quotEquivOfEq _ _ (ker_evalCont (L.dualCoannihilator.map j)).symm).trans
    ((LinearMap.quotKerEquivOfSurjective _
      (evalCont_surjective (L.dualCoannihilator.map j))).trans (resEquiv j hj L).dualMap.symm)

/-! ### The Chu mate and the reporter loss -/

/-- The admitted reporters as a subspace of `L`. -/
noncomputable def admittedIn (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀)) :
    Submodule ℂ L := Submodule.comap L.subtype (admitted j L)

/-- **`(FR.9)`.**  The contravariant reporter comparison `L_X ↪ L`. -/
noncomputable def iotaX (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀)) :
    admitted j L →ₗ[ℂ] L := Submodule.inclusion (admitted_le j L)

/-- **`(FR.8)`.**  The primal comparison `L^∨ → L_X^∨`, restriction of a law variable. -/
noncomputable def rhoX (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀)) :
    Module.Dual ℂ L →ₗ[ℂ] Module.Dual ℂ (admitted j L) := (iotaX j L).dualMap

/-- **`(FR.10)`.**  The Chu compatibility equation: the pair `(ρ_X, ι_X)` preserves evaluation. -/
theorem chu_compatibility (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀))
    (ξ : Module.Dual ℂ L) (lam : admitted j L) : rhoX j L ξ lam = ξ (iotaX j L lam) := rfl

theorem range_iotaX (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀)) :
    LinearMap.range (iotaX j L) = admittedIn j L := Submodule.range_inclusion _ _ _

/-- **`(FR.11)`, `(FR.14a)`.**  The kernel of the primal comparison is the dual of the reporter
loss `L/L_X`, by the perfect pairing `⟨ξ, [λ]⟩ = ξ(λ)`. -/
noncomputable def kerRhoEquiv (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀)) :
    Module.Dual ℂ (↥L ⧸ admittedIn j L) ≃ₗ[ℂ] LinearMap.ker (rhoX j L) := by
  refine (Submodule.dualQuotEquivDualAnnihilator (admittedIn j L)).trans (LinearEquiv.ofEq _ _ ?_)
  rw [← range_iotaX j L, ← LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  rfl

@[simp] theorem kerRhoEquiv_apply (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀))
    (ξ : Module.Dual ℂ (↥L ⧸ admittedIn j L)) (lam : L) :
    ((kerRhoEquiv j L ξ : Module.Dual ℂ L)) lam = ξ (Submodule.Quotient.mk lam) :=
  Submodule.dualQuotEquivDualAnnihilator_apply _ _ _

/-- **`(FR.11)`.**  The cokernel of the reporter comparison is the reporter loss `L/L_X`. -/
noncomputable def cokerIotaEquiv (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀)) :
    (↥L ⧸ LinearMap.range (iotaX j L)) ≃ₗ[ℂ] ↥L ⧸ admittedIn j L :=
  Submodule.quotEquivOfEq _ _ (range_iotaX j L)

/-- The transition is invertible exactly when every algebraic reporter is admitted. -/
theorem admittedIn_eq_top_iff (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀)) :
    admittedIn j L = ⊤ ↔ admitted j L = L := by
  rw [admittedIn, Submodule.comap_subtype_eq_top]
  exact ⟨fun h => le_antisymm (admitted_le j L) h, fun h => h.ge⟩

/-- The reporter loss vanishes exactly when every algebraic reporter is admitted. -/
theorem unique_loss_iff (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀)) :
    Nonempty (Unique (↥L ⧸ admittedIn j L)) ↔ admitted j L = L := by
  rw [Submodule.unique_quotient_iff_eq_top, admittedIn_eq_top_iff]

/-! ### Hyperbolic doubles -/

section Hyperbolic

variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- **`(FR.11a)`.**  The symmetric hyperbolic form on `ℍ(V) = V ⊕ V^∨`. -/
def hyperbolicPairing (u v : V × Module.Dual ℂ V) : ℂ := u.2 v.1 + v.2 u.1

/-- **`(FR.11a)`.**  The alternating cotangent form on `V ⊕ V^∨`. -/
def cotangentForm (u v : V × Module.Dual ℂ V) : ℂ := u.2 v.1 - v.2 u.1

variable {V}

theorem hyperbolicPairing_comm (u v : V × Module.Dual ℂ V) :
    hyperbolicPairing V u v = hyperbolicPairing V v u := by
  simp [hyperbolicPairing, add_comm]

theorem cotangentForm_antisymm (u v : V × Module.Dual ℂ V) :
    cotangentForm V u v = -cotangentForm V v u := by
  simp [cotangentForm]

theorem cotangentForm_self (u : V × Module.Dual ℂ V) : cotangentForm V u u = 0 := by
  simp [cotangentForm]

theorem hyperbolicPairing_sub_cotangentForm (u v : V × Module.Dual ℂ V) :
    hyperbolicPairing V u v - cotangentForm V u v = 2 * v.2 u.1 := by
  simp [hyperbolicPairing, cotangentForm]
  ring

/-- The constraint as an isotropic subspace of the cotangent double. -/
noncomputable def constraintIsotropic (I : Submodule ℂ V) :
    Submodule ℂ (V × Module.Dual ℂ V) := I.prod ⊥

theorem constraintIsotropic_isotropic {I : Submodule ℂ V} {u v : V × Module.Dual ℂ V}
    (hu : u ∈ constraintIsotropic I) (hv : v ∈ constraintIsotropic I) :
    cotangentForm V u v = 0 := by
  have h1 : u.2 = 0 := Submodule.mem_bot ℂ |>.mp (Submodule.mem_prod.mp hu).2
  have h2 : v.2 = 0 := Submodule.mem_bot ℂ |>.mp (Submodule.mem_prod.mp hv).2
  simp [cotangentForm, h1, h2]

/-- The orthogonal of a subspace of the double for the cotangent form. -/
noncomputable def formOrth (S : Submodule ℂ (V × Module.Dual ℂ V)) :
    Submodule ℂ (V × Module.Dual ℂ V) where
  carrier := {u | ∀ v ∈ S, cotangentForm V u v = 0}
  zero_mem' := by intro v _; simp [cotangentForm]
  add_mem' := by
    intro a b ha hb v hv
    have h1 := ha v hv
    have h2 := hb v hv
    simp only [cotangentForm, Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add] at *
    linear_combination h1 + h2
  smul_mem' := by
    intro c a ha v hv
    have h1 := ha v hv
    simp only [cotangentForm, Prod.smul_fst, Prod.smul_snd, LinearMap.smul_apply, map_smul,
      smul_eq_mul] at *
    linear_combination c * h1

theorem mem_formOrth {S : Submodule ℂ (V × Module.Dual ℂ V)} {u : V × Module.Dual ℂ V} :
    u ∈ formOrth S ↔ ∀ v ∈ S, cotangentForm V u v = 0 := Iff.rfl

/-- The symplectic orthogonal of a constraint is the whole chart paired with its annihilator. -/
theorem formOrth_constraintIsotropic (I : Submodule ℂ V) :
    formOrth (constraintIsotropic I) = (⊤ : Submodule ℂ V).prod I.dualAnnihilator := by
  ext u
  constructor
  · intro hu
    refine Submodule.mem_prod.mpr ⟨Submodule.mem_top,
      (Submodule.mem_dualAnnihilator _).mpr fun y hy => ?_⟩
    have h := hu (y, 0) (Submodule.mem_prod.mpr ⟨hy, Submodule.zero_mem _⟩)
    simpa [cotangentForm] using h
  · intro hu v hv
    have hu2 := (Submodule.mem_prod.mp hu).2
    have hv2 : v.2 = 0 := Submodule.mem_bot ℂ |>.mp (Submodule.mem_prod.mp hv).2
    have hv1 : v.1 ∈ I := (Submodule.mem_prod.mp hv).1
    simp [cotangentForm, hv2, (Submodule.mem_dualAnnihilator _).mp hu2 _ hv1]

/-- The reduction of the cotangent double modulo the constraint. -/
noncomputable def reductionMap (I : Submodule ℂ V) :
    (V × Module.Dual ℂ V) →ₗ[ℂ] (V ⧸ I) × Module.Dual ℂ V :=
  LinearMap.prodMap I.mkQ LinearMap.id

theorem ker_reductionMap (I : Submodule ℂ V) :
    LinearMap.ker (reductionMap I) = constraintIsotropic I := by
  rw [reductionMap, LinearMap.ker_prodMap, Submodule.ker_mkQ, LinearMap.ker_id]
  rfl

/-- The reduction is onto the reduced double `(V/I) ⊕ I^⊥`. -/
theorem reductionMap_surjOn (I : Submodule ℂ V) (z : (V ⧸ I) × I.dualAnnihilator) :
    ∃ u ∈ formOrth (constraintIsotropic I),
      reductionMap I u = (z.1, (z.2 : Module.Dual ℂ V)) := by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective I z.1
  refine ⟨(x, (z.2 : Module.Dual ℂ V)), ?_, ?_⟩
  · rw [formOrth_constraintIsotropic]
    exact Submodule.mem_prod.mpr ⟨Submodule.mem_top, z.2.2⟩
  · simp [reductionMap, hx]

end Hyperbolic

/-! ### The two reductions -/

/-- A continuous functional annihilates a subspace exactly when it annihilates its closure. -/
theorem contAnnihilator_topologicalClosure (S : Submodule ℂ X) :
    contAnnihilator S.topologicalClosure = contAnnihilator S := by
  ext φ
  refine ⟨fun h y hy => h y (Submodule.le_topologicalClosure _ hy), fun h y hy => ?_⟩
  have hset := topologicalClosure_eq_ker_contAnnihilator S
  exact ((Set.ext_iff.mp hset y).mp hy) φ h

/-- The continuous cotangent form on `X ⊕ X'`. -/
noncomputable def contCotangentForm (u v : X × (X →L[ℂ] ℂ)) : ℂ := u.2 v.1 - v.2 u.1

theorem contCotangentForm_antisymm (u v : X × (X →L[ℂ] ℂ)) :
    contCotangentForm u v = -contCotangentForm v u := by simp [contCotangentForm]

/-- The completed constraint as an isotropic subspace of the continuous double. -/
noncomputable def contConstraintIsotropic (N : Submodule ℂ X) :
    Submodule ℂ (X × (X →L[ℂ] ℂ)) := N.prod ⊥

/-- The orthogonal of a subspace of the continuous double. -/
noncomputable def contFormOrth (S : Submodule ℂ (X × (X →L[ℂ] ℂ))) :
    Submodule ℂ (X × (X →L[ℂ] ℂ)) where
  carrier := {u | ∀ v ∈ S, contCotangentForm u v = 0}
  zero_mem' := by intro v _; simp [contCotangentForm]
  add_mem' := by
    intro a b ha hb v hv
    have h1 := ha v hv
    have h2 := hb v hv
    simp only [contCotangentForm, Prod.fst_add, Prod.snd_add, _root_.add_apply,
      map_add] at *
    linear_combination h1 + h2
  smul_mem' := by
    intro c a ha v hv
    have h1 := ha v hv
    simp only [contCotangentForm, Prod.smul_fst, Prod.smul_snd, _root_.smul_apply,
      map_smul, smul_eq_mul] at *
    linear_combination c * h1

/-- The continuous symplectic orthogonal of the completed constraint. -/
theorem contFormOrth_contConstraintIsotropic (N : Submodule ℂ X) :
    contFormOrth (contConstraintIsotropic N) = (⊤ : Submodule ℂ X).prod (contAnnihilator N) := by
  ext u
  constructor
  · intro hu
    refine Submodule.mem_prod.mpr ⟨Submodule.mem_top, fun y hy => ?_⟩
    have h := hu (y, 0) (Submodule.mem_prod.mpr ⟨hy, Submodule.zero_mem _⟩)
    simpa [contCotangentForm] using h
  · intro hu v hv
    have hu2 := (Submodule.mem_prod.mp hu).2
    have hv2 : v.2 = 0 := Submodule.mem_bot ℂ |>.mp (Submodule.mem_prod.mp hv).2
    have hv1 : v.1 ∈ N := (Submodule.mem_prod.mp hv).1
    simp [contCotangentForm, hv2, hu2 _ hv1]

/-- **`(FR.12)`.**  The algebraic reduction of the cotangent double is the hyperbolic double on the
reporter dual, `ℍ(L^∨)`. -/
noncomputable def algReductionEquiv (L : Submodule ℂ (Module.Dual ℂ X₀)) [FiniteDimensional ℂ L] :
    ((X₀ ⧸ L.dualCoannihilator) × L.dualCoannihilator.dualAnnihilator)
      ≃ₗ[ℂ] Module.Dual ℂ L × Module.Dual ℂ (Module.Dual ℂ L) :=
  LinearEquiv.prodCongr (algQuotEquiv L)
    ((LinearEquiv.ofEq _ _ (dualAnnihilator_dualCoannihilator L)).trans (Module.evalEquiv ℂ L))

/-- **`(FR.13)`.**  The completed reduction is the hyperbolic double on the admitted reporter dual,
`ℍ(L_X^∨)`. -/
noncomputable def completedReductionEquiv (j : X₀ →ₗ[ℂ] X) (hj : DenseRange j)
    (L : Submodule ℂ (Module.Dual ℂ X₀)) [FiniteDimensional ℂ L] :
    ((X ⧸ (L.dualCoannihilator.map j).topologicalClosure)
        × contAnnihilator ((L.dualCoannihilator.map j).topologicalClosure))
      ≃ₗ[ℂ] Module.Dual ℂ (admitted j L)
        × Module.Dual ℂ (Module.Dual ℂ (admitted j L)) := by
  haveI : FiniteDimensional ℂ (admitted j L) := Submodule.finiteDimensional_of_le (admitted_le j L)
  exact LinearEquiv.prodCongr (completedQuotEquiv j hj L)
    (((LinearEquiv.ofEq _ _ (contAnnihilator_topologicalClosure _)).trans
      (resEquiv j hj L)).trans (Module.evalEquiv ℂ (admitted j L)))

/-- **`(FR.14)`.**  The loss of the doctrine transition is the perfect hyperbolic pair on the
reporter loss dual: `𝔎_X ≅ ℍ((L/L_X)^∨)`. -/
noncomputable def lossEquiv (j : X₀ →ₗ[ℂ] X) (L : Submodule ℂ (Module.Dual ℂ X₀))
    [FiniteDimensional ℂ L] :
    (LinearMap.ker (rhoX j L) × (↥L ⧸ admittedIn j L))
      ≃ₗ[ℂ] Module.Dual ℂ (↥L ⧸ admittedIn j L)
        × Module.Dual ℂ (Module.Dual ℂ (↥L ⧸ admittedIn j L)) :=
  LinearEquiv.prodCongr (kerRhoEquiv j L).symm (Module.evalEquiv ℂ (↥L ⧸ admittedIn j L))

/-! ### Serial doctrine composition -/

section Serial

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

/-- The relative quotient of a flag step, included into the total quotient. -/
noncomputable def flagIncl (A B : Submodule ℂ N) :
    (↥A ⧸ Submodule.comap A.subtype B) →ₗ[ℂ] N ⧸ B :=
  Submodule.mapQ _ _ A.subtype le_rfl

/-- The projection of total quotients along a flag step. -/
noncomputable def flagProj {A B : Submodule ℂ N} (h : B ≤ A) : (N ⧸ B) →ₗ[ℂ] N ⧸ A :=
  Submodule.mapQ B A LinearMap.id (by simpa using h)

theorem ker_flagIncl (A B : Submodule ℂ N) :
    LinearMap.ker (flagIncl A B) = ⊥ := by
  rw [flagIncl, Submodule.ker_mapQ]
  exact Submodule.mkQ_map_self _

theorem flagIncl_injective (A B : Submodule ℂ N) :
    Function.Injective (flagIncl A B) := LinearMap.ker_eq_bot.mp (ker_flagIncl A B)

theorem range_flagIncl (A B : Submodule ℂ N) :
    LinearMap.range (flagIncl A B) = A.map B.mkQ := by
  rw [flagIncl, Submodule.range_mapQ, Submodule.range_subtype]

theorem ker_flagProj {A B : Submodule ℂ N} (h : B ≤ A) :
    LinearMap.ker (flagProj h) = A.map B.mkQ := by
  rw [flagProj, Submodule.ker_mapQ, Submodule.comap_id]

theorem flagProj_surjective {A B : Submodule ℂ N} (h : B ≤ A) :
    Function.Surjective (flagProj h) := by
  rw [← LinearMap.range_eq_top, flagProj, Submodule.range_mapQ, LinearMap.range_id,
    Submodule.map_top, Submodule.range_mkQ]

/-- **`(FR.20)`.**  The stepwise and total reporter losses form a short exact sequence
`0 → L₁/L₂ → L₀/L₂ → L₀/L₁ → 0`. -/
theorem serial_exact {A B : Submodule ℂ N} (h : B ≤ A) :
    Function.Injective (flagIncl A B) ∧ Function.Surjective (flagProj h) ∧
      LinearMap.range (flagIncl A B) = LinearMap.ker (flagProj h) :=
  ⟨flagIncl_injective A B, flagProj_surjective h, (range_flagIncl A B).trans (ker_flagProj h).symm⟩

/-- **`(FR.21)`.**  The primal losses form the dual short exact sequence
`0 → (L₀/L₁)^∨ → (L₀/L₂)^∨ → (L₁/L₂)^∨ → 0`. -/
theorem serial_exact_dual {A B : Submodule ℂ N} (h : B ≤ A) :
    Function.Injective (flagProj h).dualMap ∧ Function.Surjective (flagIncl A B).dualMap ∧
      LinearMap.range (flagProj h).dualMap = LinearMap.ker (flagIncl A B).dualMap := by
  refine ⟨LinearMap.dualMap_injective_of_surjective (flagProj_surjective h),
    LinearMap.dualMap_surjective_of_injective (flagIncl_injective A B), ?_⟩
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _ (flagProj_surjective h),
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, ker_flagProj, range_flagIncl]

/-- **`(FR.22)`.**  The exact composition law for doctrine transitions. -/
theorem finrank_serial [FiniteDimensional ℂ N] {A B : Submodule ℂ N} (h : B ≤ A) :
    Module.finrank ℂ (N ⧸ B)
      = Module.finrank ℂ (N ⧸ A)
        + Module.finrank ℂ (↥A ⧸ Submodule.comap A.subtype B) := by
  have e1 : ((N ⧸ B) ⧸ (A.map B.mkQ)) ≃ₗ[ℂ] (N ⧸ A) :=
    (Submodule.quotEquivOfEq _ _ (ker_flagProj h).symm).trans
      (LinearMap.quotKerEquivOfSurjective _ (flagProj_surjective h))
  have e2 : (↥A ⧸ Submodule.comap A.subtype B) ≃ₗ[ℂ] (A.map B.mkQ) :=
    (LinearEquiv.ofInjective _ (flagIncl_injective A B)).trans
      (LinearEquiv.ofEq _ _ (range_flagIncl A B))
  have hkey := Submodule.finrank_quotient_add_finrank (A.map B.mkQ)
  rw [e1.finrank_eq, ← e2.finrank_eq] at hkey
  omega

/-- **`(FR.21a)`.**  The stepwise primal loss annihilates the stepwise reporter loss. -/
theorem flag_pairing_trivial {A B : Submodule ℂ N} (h : B ≤ A) {ξ : Module.Dual ℂ (N ⧸ B)}
    (hξ : ξ ∈ LinearMap.range (flagProj h).dualMap) {y : N ⧸ B} (hy : y ∈ A.map B.mkQ) :
    ξ y = 0 := by
  obtain ⟨η, rfl⟩ := hξ
  have hy0 : flagProj h y = 0 := LinearMap.mem_ker.mp ((ker_flagProj h).symm ▸ hy)
  rw [LinearMap.dualMap_apply, hy0, map_zero]

/-- **`(FR.21a)`.**  The canonical Lagrangian `𝔐 = (L₀/L₁)^∨ ⊕ (L₁/L₂)` inside the total loss. -/
noncomputable def serialLagrangian {A B : Submodule ℂ N} (h : B ≤ A) :
    Submodule ℂ ((N ⧸ B) × Module.Dual ℂ (N ⧸ B)) :=
  (A.map B.mkQ).prod (LinearMap.range (flagProj h).dualMap)

theorem serialLagrangian_isotropic {A B : Submodule ℂ N} (h : B ≤ A)
    {u v : (N ⧸ B) × Module.Dual ℂ (N ⧸ B)} (hu : u ∈ serialLagrangian h)
    (hv : v ∈ serialLagrangian h) : cotangentForm (N ⧸ B) u v = 0 := by
  have h1 := flag_pairing_trivial h (Submodule.mem_prod.mp hu).2 (Submodule.mem_prod.mp hv).1
  have h2 := flag_pairing_trivial h (Submodule.mem_prod.mp hv).2 (Submodule.mem_prod.mp hu).1
  simp [cotangentForm, h1, h2]

/-- The underlying pair of a product of submodules. -/
noncomputable def prodSubmoduleEquiv {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] (p : Submodule ℂ M₁) (q : Submodule ℂ M₂) :
    ↥(p.prod q) ≃ₗ[ℂ] ↥p × ↥q where
  toFun u := (⟨u.1.1, (Submodule.mem_prod.mp u.2).1⟩, ⟨u.1.2, (Submodule.mem_prod.mp u.2).2⟩)
  invFun z := ⟨((z.1 : M₁), (z.2 : M₂)), Submodule.mem_prod.mpr ⟨z.1.2, z.2.2⟩⟩
  left_inv u := by ext <;> rfl
  right_inv z := by ext <;> rfl
  map_add' u v := rfl
  map_smul' c u := rfl

/-- **`(FR.21a)`.**  The canonical Lagrangian has half the dimension of the total loss. -/
theorem finrank_serialLagrangian [FiniteDimensional ℂ N] {A B : Submodule ℂ N} (h : B ≤ A) :
    2 * Module.finrank ℂ (serialLagrangian h)
      = Module.finrank ℂ ((N ⧸ B) × Module.Dual ℂ (N ⧸ B)) := by
  have hR : Module.finrank ℂ (LinearMap.range (flagProj h).dualMap)
      = Module.finrank ℂ (N ⧸ A) := by
    rw [← (LinearEquiv.ofInjective _
      (LinearMap.dualMap_injective_of_surjective (flagProj_surjective h))).finrank_eq]
    exact Subspace.dual_finrank_eq
  have hL : Module.finrank ℂ (A.map B.mkQ)
      = Module.finrank ℂ (↥A ⧸ Submodule.comap A.subtype B) :=
    ((LinearEquiv.ofInjective _ (flagIncl_injective A B)).trans
      (LinearEquiv.ofEq _ _ (range_flagIncl A B))).finrank_eq.symm
  have hprod : Module.finrank ℂ (serialLagrangian h)
      = Module.finrank ℂ (A.map B.mkQ)
        + Module.finrank ℂ (LinearMap.range (flagProj h).dualMap) := by
    rw [serialLagrangian, (prodSubmoduleEquiv _ _).finrank_eq, Module.finrank_prod]
  have htot : Module.finrank ℂ ((N ⧸ B) × Module.Dual ℂ (N ⧸ B))
      = 2 * Module.finrank ℂ (N ⧸ B) := by
    rw [Module.finrank_prod, Subspace.dual_finrank_eq]
    ring
  rw [hprod, hL, hR, htot, finrank_serial h]
  ring

end Serial

end FiniteReporter

/-! ### The literal prime-port instantiation -/

section PrimePort

variable {P : Type*} [DecidableEq P] {p : ENNReal} [Fact (1 ≤ p)]

/-- **`(FR.23)`.**  The reporter line spanned by the prime augmentation. -/
noncomputable def augLine (P : Type*) [DecidableEq P] : Submodule ℂ (Module.Dual ℂ (P →₀ ℂ)) :=
  Submodule.span ℂ {(augment : Module.Dual ℂ (P →₀ ℂ))}

instance finiteDimensional_augLine : FiniteDimensional ℂ (augLine P) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _)

omit [DecidableEq P] in
theorem augment_ne_zero [Nonempty P] : (augment : Module.Dual ℂ (P →₀ ℂ)) ≠ 0 := by
  classical
  intro h
  obtain ⟨q⟩ := ‹Nonempty P›
  have h1 : augment (Finsupp.single q (1 : ℂ)) = 0 := by rw [h]; rfl
  rw [augment_apply] at h1
  simp at h1

/-- The reporter line is one dimensional. -/
noncomputable def augLineEquiv [Nonempty P] : ℂ ≃ₗ[ℂ] augLine P :=
  LinearEquiv.toSpanNonzeroSingleton ℂ (Module.Dual ℂ (P →₀ ℂ)) augment augment_ne_zero

/-- **`(FR.23)`.**  The constraint cut out by the augmentation line is the augmentation ideal. -/
theorem dualCoannihilator_augLine :
    (augLine P).dualCoannihilator = (augIdeal : Submodule ℂ (P →₀ ℂ)) := by
  ext x
  rw [Submodule.mem_dualCoannihilator, mem_augIdeal_iff]
  constructor
  · intro h
    exact h _ (Submodule.mem_span_singleton_self _)
  · intro h ψ hψ
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hψ
    simp [h]

/-- **`(FR.24)`.**  In `ℓ¹` the augmentation port is admitted: `L_X = L`. -/
theorem admitted_augLine_one :
    admitted (lpEmb P 1) (augLine P) = augLine P := by
  refine le_antisymm (admitted_le _ _) fun lam hlam => ?_
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hlam
  refine ⟨Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _), ⟨c • augCLM, ?_⟩⟩
  ext l
  simp [restrictAlong, augCLM_lpEmb]

/-- **`(FR.24)`.**  The `ℓ¹` transition has no reporter loss. -/
theorem unique_loss_augLine_one :
    Nonempty (Unique (↥(augLine P) ⧸ admittedIn (lpEmb P 1) (augLine P))) :=
  (unique_loss_iff _ _).mpr admitted_augLine_one

/-- **`(FR.25)`.**  In a chart carrying vectors of augmentation one and arbitrarily small norm the
port is erased: `L_X = 0`. -/
theorem admitted_augLine_eq_bot {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (emb : (P →₀ ℂ) →ₗ[ℂ] X)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ u : P →₀ ℂ, augment u = 1 ∧ ‖emb u‖ < ε) :
    admitted emb (augLine P) = ⊥ := by
  refine le_antisymm (fun lam hlam => ?_) bot_le
  obtain ⟨hL, φ, hφ⟩ := hlam
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hL
  have hvan : ∀ l ∈ (augIdeal : Submodule ℂ (P →₀ ℂ)), φ (emb l) = 0 := by
    intro l hl
    have h1 : φ (emb l) = lam l := congrFun (congrArg DFunLike.coe hφ) l
    rw [h1, ← hc]
    simp [mem_augIdeal_iff.mp hl]
  have hzero : ∀ l : P →₀ ℂ, φ (emb l) = 0 :=
    eq_zero_on_range_of_vanishing_on_augIdeal emb hsmall φ hvan
  refine Submodule.mem_bot ℂ |>.mpr ?_
  refine LinearMap.ext fun l => ?_
  rw [← congrFun (congrArg DFunLike.coe hφ) l]
  exact hzero l

/-- **`(FR.25)`.**  The `ℓ^p` charts with `p > 1` erase the augmentation port. -/
theorem admitted_augLine_lp_eq_bot [Infinite P] (hp : 1 < p.toReal) :
    admitted (lpEmb P p) (augLine P) = ⊥ :=
  admitted_augLine_eq_bot _ fun ε hε =>
    exists_small_spread_lp one_ne_zero_family (fun _ => norm_one) hp ε hε

/-- **`(FR.25)`.**  The `ℓ^∞` chart erases the augmentation port. -/
theorem admitted_augLine_top_eq_bot [Infinite P] :
    admitted (lpEmb P ⊤) (augLine P) = ⊥ :=
  admitted_augLine_eq_bot _ fun ε hε =>
    exists_small_spread_top one_ne_zero_family (fun _ => norm_one) ε hε

theorem admittedIn_eq_bot_of_admitted_eq_bot {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (emb : (P →₀ ℂ) →ₗ[ℂ] X) (h : admitted emb (augLine P) = ⊥) :
    admittedIn emb (augLine P) = ⊥ := by
  rw [admittedIn, h, Submodule.comap_bot, Submodule.ker_subtype]

/-- **`(FR.25)`.**  In an erasing chart the reporter loss is the full one-dimensional line, so the
transition loss is the hyperbolic plane `ℍ(ℂ)`. -/
noncomputable def loss_augLine_erasure [Nonempty P] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] (emb : (P →₀ ℂ) →ₗ[ℂ] X) (h : admitted emb (augLine P) = ⊥) :
    (↥(augLine P) ⧸ admittedIn emb (augLine P)) ≃ₗ[ℂ] ℂ :=
  (Submodule.quotEquivOfEqBot _ (admittedIn_eq_bot_of_admitted_eq_bot emb h)).trans
    augLineEquiv.symm

end PrimePort

end HTGeometry.ConstraintMotiveRelativity
