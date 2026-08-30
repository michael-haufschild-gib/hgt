import GaloisForLFunctions.HTGeometry.KSGNSWeightedProjection

open scoped CStarAlgebra

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {A B : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Complex-linear isometry `Bᵐᵒᵖ → B` used to expose the standard right-module convention. -/
private def mulOppositeUnopCLM : Bᵐᵒᵖ →L[ℂ] B :=
  { toLinearMap :=
      { toFun := MulOpposite.unop
        map_add' := by intro x y; rfl
        map_smul' := by intro q x; rfl }
    cont := (LinearIsometry.isometry
      ({ toLinearMap :=
          { toFun := MulOpposite.unop
            map_add' := by intro x y; rfl
            map_smul' := by intro q x; rfl }
         norm_map' := MulOpposite.norm_unop } : Bᵐᵒᵖ →ₗᵢ[ℂ] B)).continuous }

theorem continuous_ksgnsRightInner_pair (phi : A →CP B) :
    Continuous fun p : KSGNS phi × KSGNS phi =>
      (ksgnsRightInnerModuleData phi).inner p.1 p.2 := by
  exact mulOppositeUnopCLM.continuous.comp
    (continuous_ksgnsCompleted_inner_pair phi)

/-- A complete right Hilbert `B`-module in the exact algebraic convention used by KSGNS,
including bounded right multiplication. -/
structure CompleteRightHilbertModuleData (B E : Type*)
    [CStarAlgebra B] [NormedAddCommGroup E] [NormedSpace ℂ E] where
  toRightInnerModuleData : RightInnerModuleData B E
  rmul_smul_right : ∀ (q : ℂ) x b,
    toRightInnerModuleData.rmul x (q • b) =
      q • toRightInnerModuleData.rmul x b
  norm_eq_sqrt_norm_inner_self : ∀ x,
    ‖x‖ = Real.sqrt ‖toRightInnerModuleData.inner x x‖
  continuous_inner_pair : Continuous fun p : E × E =>
    toRightInnerModuleData.inner p.1 p.2
  rmulCLM : B → E →L[ℂ] E
  rmulCLM_apply : ∀ b x, rmulCLM b x = toRightInnerModuleData.rmul x b

instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Coe (CompleteRightHilbertModuleData B E) (RightInnerModuleData B E) :=
  ⟨CompleteRightHilbertModuleData.toRightInnerModuleData⟩

/-- A complete minimal pointed KSGNS presentation of `phi`.  Minimality is density of the exact
cyclic `π(A)ξB` span; all operator and module actions are bounded. -/
structure MinimalKSGNSPresentation (phi : A →CP B) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] where
  moduleData : CompleteRightHilbertModuleData B E
  act : A → E →L[ℂ] E
  xi : E
  act_one : ∀ x, act 1 x = x
  act_mul : ∀ a c x, act (a * c) x = act a (act c x)
  act_add : ∀ a c x, act (a + c) x = act a x + act c x
  act_smul_label : ∀ (q : ℂ) a x, act (q • a) x = q • act a x
  act_rmul : ∀ a x b,
    act a (moduleData.toRightInnerModuleData.rmul x b) =
      moduleData.toRightInnerModuleData.rmul (act a x) b
  act_adjoint : ∀ a x y,
    moduleData.toRightInnerModuleData.inner (act a x) y =
      moduleData.toRightInnerModuleData.inner x (act (star a) y)
  recover : ∀ a,
    moduleData.toRightInnerModuleData.inner xi (act a xi) = phi a
  minimal : Dense (Submodule.span ℂ {z | ∃ (a : A) (b : B),
    z = moduleData.toRightInnerModuleData.rmul (act a xi) b} : Set E)

namespace MinimalKSGNSPresentation

variable {phi : A →CP B} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Q : MinimalKSGNSPresentation (A := A) (B := B) phi E)

abbrev M : RightInnerModuleData B E := Q.moduleData.toRightInnerModuleData

/-- Cyclic algebraic span of a presentation. -/
def cyclicSpan : Submodule ℂ E :=
  Submodule.span ℂ {z | ∃ (a : A) (b : B), z = Q.M.rmul (Q.act a Q.xi) b}

theorem dense_cyclicSpan : Dense (Q.cyclicSpan : Set E) := Q.minimal

/-- Evaluation of the algebraic free KSGNS module in a pointed presentation. -/
def preMap : (A →₀ B) →ₗ[ℂ] E :=
  (Finsupp.lsum ℂ) fun a =>
    { toFun := fun b => Q.M.rmul (Q.act a Q.xi) b
      map_add' := fun b c => Q.M.rmul_add_right _ _ _
      map_smul' := fun q b => Q.moduleData.rmul_smul_right q _ b }

@[simp]
theorem preMap_single (a : A) (b : B) :
    Q.preMap (Finsupp.single a b) = Q.M.rmul (Q.act a Q.xi) b := by
  classical
  change (Finsupp.single a b).sum
      (fun i b => Q.M.rmul (Q.act i Q.xi) b) = _
  rw [Finsupp.sum_single_index]
  simpa using Q.moduleData.rmul_smul_right (0 : ℂ) (Q.act a Q.xi) (0 : B)

theorem inner_act_xi_act_xi (a c : A) :
    Q.M.inner (Q.act a Q.xi) (Q.act c Q.xi) = phi (star a * c) := by
  rw [Q.act_adjoint, ← Q.act_mul, Q.recover]

theorem inner_preMap_single_single (a c : A) (b d : B) :
    Q.M.inner (Q.preMap (Finsupp.single a b))
      (Q.preMap (Finsupp.single c d)) =
        star b * phi (star a * c) * d := by
  rw [Q.preMap_single, Q.preMap_single, Q.M.inner_rmul_right,
    Q.M.inner_rmul_left, Q.inner_act_xi_act_xi]

/-- Every minimal pointed presentation has exactly the canonical KSGNS Gram form. -/
theorem inner_preMap_preMap (x y : A →₀ B) :
    Q.M.inner (Q.preMap x) (Q.preMap y) = ksgnsPreInner phi x y := by
  classical
  induction x using Finsupp.induction_linear with
  | zero =>
      rw [map_zero, Q.M.inner_zero_left]
      simp [ksgnsPreInner]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [map_add, Q.M.inner_add_left, hx₁, hx₂, ksgnsPreInner_add_left]
  | single a b =>
      induction y using Finsupp.induction_linear with
      | zero =>
          rw [map_zero, Q.M.inner_zero_right]
          simp [ksgnsPreInner]
      | add y₁ y₂ hy₁ hy₂ =>
          rw [map_add, Q.M.inner_add_right, hy₁, hy₂, ksgnsPreInner_add_right]
      | single c d =>
          simpa using Q.inner_preMap_single_single a c b d

theorem preMap_eq_zero_of_mem_radical {x : A →₀ B}
    (hx : x ∈ ksgnsPreRadical phi) : Q.preMap x = 0 := by
  apply norm_eq_zero.mp
  rw [Q.moduleData.norm_eq_sqrt_norm_inner_self, Q.inner_preMap_preMap, hx x]
  simp

/-- Canonical map from the separated algebraic KSGNS quotient to any pointed presentation. -/
def separatedMap : KSGNSSeparated phi →ₗ[ℂ] E :=
  (ksgnsPreRadical phi).liftQ Q.preMap (by
    intro x hx
    exact Q.preMap_eq_zero_of_mem_radical hx)

@[simp]
theorem separatedMap_mk (x : A →₀ B) :
    Q.separatedMap (Submodule.Quotient.mk x) = Q.preMap x :=
  Submodule.liftQ_apply _ _ _

theorem inner_separatedMap (x y : KSGNSSeparated phi) :
    Q.M.inner (Q.separatedMap x) (Q.separatedMap y) =
      ksgnsSeparatedInner phi x y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ x y =>
      change Q.M.inner
        (Q.separatedMap (Submodule.Quotient.mk x))
        (Q.separatedMap (Submodule.Quotient.mk y)) =
          ksgnsSeparatedInner phi (Submodule.Quotient.mk x)
            (Submodule.Quotient.mk y)
      rw [Q.separatedMap_mk, Q.separatedMap_mk, Q.inner_preMap_preMap]
      rfl

theorem norm_separatedMap (x : KSGNSSeparated phi) :
    ‖Q.separatedMap x‖ = ‖x‖ := by
  rw [Q.moduleData.norm_eq_sqrt_norm_inner_self, Q.inner_separatedMap]
  symm
  have h := CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x
  change ‖x‖ = Real.sqrt ‖MulOpposite.op (ksgnsSeparatedInner phi x x)‖ at h
  rw [MulOpposite.norm_op] at h
  exact h

/-- Isometric algebraic comparison from the canonical separated quotient. -/
def separatedIsometry : KSGNSSeparated phi →ₗᵢ[ℂ] E where
  toLinearMap := Q.separatedMap
  norm_map' := Q.norm_separatedMap

/-- Continuous extension of the algebraic comparison to the complete canonical KSGNS module. -/
def canonicalMapCLM : KSGNS phi →L[ℂ] E :=
  completionExtendSL Q.separatedIsometry.toContinuousLinearMap

@[simp]
theorem canonicalMapCLM_coe (x : KSGNSSeparated phi) :
    Q.canonicalMapCLM (x : KSGNS phi) = Q.separatedMap x := by
  exact completionExtendSL_coe _ _

theorem norm_canonicalMapCLM (x : KSGNS phi) :
    ‖Q.canonicalMapCLM x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      (continuous_norm.comp Q.canonicalMapCLM.continuous) continuous_norm
  · intro x
    rw [Q.canonicalMapCLM_coe, Q.norm_separatedMap,
      UniformSpace.Completion.norm_coe]

/-- Isometric comparison from the canonical KSGNS module to a minimal presentation. -/
def canonicalIsometry : KSGNS phi →ₗᵢ[ℂ] E where
  toLinearMap := Q.canonicalMapCLM.toLinearMap
  norm_map' := Q.norm_canonicalMapCLM

@[simp]
theorem canonicalIsometry_coe (x : KSGNSSeparated phi) :
    Q.canonicalIsometry (x : KSGNS phi) = Q.separatedMap x :=
  Q.canonicalMapCLM_coe x

theorem canonicalIsometry_cyclic :
    Q.canonicalIsometry (ksgnsCyclic phi) = Q.xi := by
  rw [ksgnsCyclic, Q.canonicalIsometry_coe, ksgnsSeparatedCyclic,
    Q.separatedMap_mk, ksgnsPreCyclic, Q.preMap_single]
  rw [Q.act_one, Q.M.rmul_one]

theorem canonicalIsometry_rep_cyclic_rmul (a : A) (b : B) :
    Q.canonicalIsometry
        (MulOpposite.op b • ksgnsRepresentation phi a (ksgnsCyclic phi)) =
      Q.M.rmul (Q.act a Q.xi) b := by
  rw [ksgnsRepresentation_cyclic]
  change Q.canonicalIsometry
      (ksgnsCompletedActionCLM phi (MulOpposite.op b)
        ((Submodule.Quotient.mk (Finsupp.single a 1) : KSGNSSeparated phi) : KSGNS phi)) = _
  rw [ksgnsCompletedActionCLM_coe]
  change Q.canonicalIsometry
      ((MulOpposite.op b •
        (Submodule.Quotient.mk (Finsupp.single a 1) : KSGNSSeparated phi) :
          KSGNSSeparated phi) : KSGNS phi) = _
  rw [ksgnsSeparated_op_smul_mk, Q.canonicalIsometry_coe,
    Q.separatedMap_mk]
  simpa [ksgnsPreRmul_single] using Q.preMap_single a b

theorem preMap_lmul (a : A) (x : A →₀ B) :
    Q.preMap (ksgnsPreLmul a x) = Q.act a (Q.preMap x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [ksgnsPreLmul]
  | add x y hx hy =>
      rw [ksgnsPreLmul_add, map_add, map_add, hx, hy]
      exact (map_add (Q.act a) _ _).symm
  | single c d =>
      rw [ksgnsPreLmul_single, Q.preMap_single, Q.preMap_single,
        Q.act_rmul, Q.act_mul]

theorem preMap_rmul (x : A →₀ B) (b : B) :
    Q.preMap (ksgnsPreRmul x b) = Q.M.rmul (Q.preMap x) b := by
  classical
  induction x using Finsupp.induction_linear with
  | zero =>
      rw [map_zero]
      have hz : Q.M.rmul (0 : E) b = 0 := by
        simpa using Q.M.rmul_smul (0 : ℂ) Q.xi b
      simp [ksgnsPreRmul, hz]
  | add x y hx hy =>
      rw [show ksgnsPreRmul (x + y) b =
          ksgnsPreRmul x b + ksgnsPreRmul y b by
        exact map_add (ksgnsPreRmulLinear b) x y]
      rw [map_add, hx, hy, map_add Q.preMap, Q.M.rmul_add_left]
  | single a c =>
      rw [ksgnsPreRmul_single, Q.preMap_single, Q.preMap_single, Q.M.rmul_mul]

theorem separatedMap_lmul (a : A) (x : KSGNSSeparated phi) :
    Q.separatedMap (ksgnsSeparatedLmul phi a x) = Q.act a (Q.separatedMap x) := by
  induction x using Quotient.inductionOn with
  | _ x =>
      change Q.separatedMap
          (ksgnsSeparatedLmul phi a (Submodule.Quotient.mk x)) =
        Q.act a (Q.separatedMap (Submodule.Quotient.mk x))
      rw [ksgnsSeparatedLmul_mk, Q.separatedMap_mk, Q.separatedMap_mk,
        Q.preMap_lmul]

theorem separatedMap_rmul (b : B) (x : KSGNSSeparated phi) :
    Q.separatedMap (ksgnsSeparatedRmul phi b x) = Q.M.rmul (Q.separatedMap x) b := by
  induction x using Quotient.inductionOn with
  | _ x =>
      change Q.separatedMap
          (ksgnsSeparatedRmul phi b (Submodule.Quotient.mk x)) =
        Q.M.rmul (Q.separatedMap (Submodule.Quotient.mk x)) b
      rw [ksgnsSeparatedRmul_mk, Q.separatedMap_mk, Q.separatedMap_mk,
        Q.preMap_rmul]

theorem canonicalIsometry_act (a : A) (x : KSGNS phi) :
    Q.canonicalIsometry (ksgnsRepresentation phi a x) =
      Q.act a (Q.canonicalIsometry x) := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      (Q.canonicalIsometry.continuous.comp (ksgnsRepresentation phi a).continuous)
      ((Q.act a).continuous.comp Q.canonicalIsometry.continuous)
  · intro x
    rw [ksgnsRepresentation_coe, Q.canonicalIsometry_coe,
      Q.canonicalIsometry_coe, Q.separatedMap_lmul]

theorem canonicalIsometry_rmul (b : B) (x : KSGNS phi) :
    Q.canonicalIsometry (MulOpposite.op b • x) =
      Q.M.rmul (Q.canonicalIsometry x) b := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · apply isClosed_eq
    · exact
      (Q.canonicalIsometry.continuous.comp
        (ksgnsCompletedActionCLM phi (MulOpposite.op b)).continuous)
    · have heq : (fun y => Q.M.rmul (Q.canonicalIsometry y) b) =
          (fun y => Q.moduleData.rmulCLM b (Q.canonicalIsometry y)) := by
          funext y
          exact (Q.moduleData.rmulCLM_apply b (Q.canonicalIsometry y)).symm
      rw [heq]
      exact (Q.moduleData.rmulCLM b).continuous.comp Q.canonicalIsometry.continuous
  · intro x
    change Q.canonicalIsometry
        (ksgnsCompletedActionCLM phi (MulOpposite.op b) (x : KSGNS phi)) = _
    rw [ksgnsCompletedActionCLM_coe, Q.canonicalIsometry_coe,
      Q.canonicalIsometry_coe]
    change Q.separatedMap (ksgnsSeparatedRmul phi b x) = _
    rw [Q.separatedMap_rmul]

theorem inner_canonicalIsometry (x y : KSGNS phi) :
    Q.M.inner (Q.canonicalIsometry x) (Q.canonicalIsometry y) =
      (ksgnsRightInnerModuleData phi).inner x y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · apply isClosed_eq
    · exact Q.moduleData.continuous_inner_pair.comp
        ((Q.canonicalIsometry.continuous.comp continuous_fst).prodMk
          (Q.canonicalIsometry.continuous.comp continuous_snd))
    · exact continuous_ksgnsRightInner_pair phi
  · intro x y
    rw [Q.canonicalIsometry_coe, Q.canonicalIsometry_coe,
      Q.inner_separatedMap]
    change ksgnsSeparatedInner phi x y =
      MulOpposite.unop
        (ksgnsCompletedInnerSLM phi (x : KSGNS phi) (y : KSGNS phi))
    rw [ksgnsCompletedInnerSLM_coe_coe]
    rfl

theorem canonicalIsometry_surjective : Function.Surjective Q.canonicalIsometry := by
  have hrangeClosed : IsClosed (Set.range Q.canonicalIsometry) :=
    Q.canonicalIsometry.isometry.isClosedEmbedding.isClosed_range
  have hspan : (Q.cyclicSpan : Set E) ⊆ Set.range Q.canonicalIsometry := by
    intro z hz
    exact Submodule.span_induction (p := fun z _ => z ∈ Set.range Q.canonicalIsometry)
      (by
        rintro z ⟨a, b, rfl⟩
        exact ⟨MulOpposite.op b • ksgnsRepresentation phi a (ksgnsCyclic phi),
          Q.canonicalIsometry_rep_cyclic_rmul a b⟩)
      ⟨0, map_zero _⟩
      (by
        intro x y _ _ hx hy
        rcases hx with ⟨u, rfl⟩
        rcases hy with ⟨v, rfl⟩
        exact ⟨u + v, map_add _ _ _⟩)
      (by
        intro q x _ hx
        rcases hx with ⟨u, rfl⟩
        exact ⟨q • u, map_smul _ _ _⟩)
      hz
  have hclosure : closure (Q.cyclicSpan : Set E) ⊆ Set.range Q.canonicalIsometry :=
    closure_minimal hspan hrangeClosed
  intro y
  apply hclosure
  rw [Q.dense_cyclicSpan.closure_eq]
  exact Set.mem_univ y

/-- Canonical unitary equivalence from the constructed KSGNS module to any minimal pointed
presentation. -/
def canonicalUnitary : KSGNS phi ≃ₗᵢ[ℂ] E :=
  LinearIsometryEquiv.ofSurjective Q.canonicalIsometry Q.canonicalIsometry_surjective

@[simp]
theorem canonicalUnitary_apply (x : KSGNS phi) :
    Q.canonicalUnitary x = Q.canonicalIsometry x := rfl

@[simp]
theorem canonicalUnitary_cyclic :
    Q.canonicalUnitary (ksgnsCyclic phi) = Q.xi := Q.canonicalIsometry_cyclic

theorem canonicalUnitary_act (a : A) (x : KSGNS phi) :
    Q.canonicalUnitary (ksgnsRepresentation phi a x) =
      Q.act a (Q.canonicalUnitary x) := Q.canonicalIsometry_act a x

theorem canonicalUnitary_rmul (b : B) (x : KSGNS phi) :
    Q.canonicalUnitary (MulOpposite.op b • x) =
      Q.M.rmul (Q.canonicalUnitary x) b := Q.canonicalIsometry_rmul b x

/-- Weighted centered vector in an arbitrary minimal pointed presentation. -/
def weightedCentered (hunit : IsUnit (phi 1)) (a : A) : E :=
  Q.act a Q.xi - Q.M.rmul Q.xi (ksgnsOrderUnitInv phi hunit * phi a)

/-- Pointed unitary equivalence transports the weighted centered vector exactly. -/
theorem canonicalUnitary_weightedCentered (hunit : IsUnit (phi 1)) (a : A) :
    Q.canonicalUnitary (ksgnsWeightedCentered phi hunit a) =
      Q.weightedCentered hunit a := by
  rw [ksgnsWeightedCentered, weightedCentered, map_sub,
    Q.canonicalUnitary_act, Q.canonicalUnitary_rmul,
    Q.canonicalUnitary_cyclic]

/-- A pointed correspondence unitary from the canonical KSGNS construction to `Q`. -/
structure PointedUnitary where
  toLinearIsometryEquiv : KSGNS phi ≃ₗᵢ[ℂ] E
  map_cyclic : toLinearIsometryEquiv (ksgnsCyclic phi) = Q.xi
  map_act : ∀ a x,
    toLinearIsometryEquiv (ksgnsRepresentation phi a x) =
      Q.act a (toLinearIsometryEquiv x)
  map_rmul : ∀ b x,
    toLinearIsometryEquiv (MulOpposite.op b • x) =
      Q.M.rmul (toLinearIsometryEquiv x) b
  map_inner : ∀ x y,
    Q.M.inner (toLinearIsometryEquiv x) (toLinearIsometryEquiv y) =
      (ksgnsRightInnerModuleData phi).inner x y

instance : CoeFun Q.PointedUnitary (fun _ => KSGNS phi → E) :=
  ⟨fun U => U.toLinearIsometryEquiv⟩

/-- Canonical pointed correspondence unitary. -/
def canonicalPointedUnitary : Q.PointedUnitary where
  toLinearIsometryEquiv := Q.canonicalUnitary
  map_cyclic := Q.canonicalUnitary_cyclic
  map_act := Q.canonicalUnitary_act
  map_rmul := Q.canonicalUnitary_rmul
  map_inner := Q.inner_canonicalIsometry

theorem ksgns_cyclic_generator_eq_coe_single (a : A) (b : B) :
    MulOpposite.op b • ksgnsRepresentation phi a (ksgnsCyclic phi) =
      ((Submodule.Quotient.mk (Finsupp.single a b) : KSGNSSeparated phi) : KSGNS phi) := by
  rw [ksgnsRepresentation_cyclic]
  change ksgnsCompletedActionCLM phi (MulOpposite.op b)
      ((Submodule.Quotient.mk (Finsupp.single a 1) : KSGNSSeparated phi) : KSGNS phi) = _
  rw [ksgnsCompletedActionCLM_coe]
  congr 1
  simp

theorem pointedUnitary_coe_mk (U : Q.PointedUnitary) (x : A →₀ B) :
    U ((Submodule.Quotient.mk x : KSGNSSeparated phi) : KSGNS phi) =
      Q.preMap x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [Submodule.Quotient.mk_add, UniformSpace.Completion.coe_add,
        map_add, map_add, hx, hy]
  | single a b =>
      rw [← ksgns_cyclic_generator_eq_coe_single]
      change U.toLinearIsometryEquiv
          (MulOpposite.op b • ksgnsRepresentation phi a (ksgnsCyclic phi)) = _
      rw [U.map_rmul, U.map_act, U.map_cyclic, Q.preMap_single]

/-- Pointed KSGNS uniqueness: every pointed correspondence unitary is the canonical one. -/
theorem pointedUnitary_unique (U : Q.PointedUnitary) :
    U = Q.canonicalPointedUnitary := by
  cases U with
  | mk U hcyc hact hrmul hinner =>
      congr 1
      ext x
      refine UniformSpace.Completion.induction_on x ?_ ?_
      · exact isClosed_eq U.continuous Q.canonicalUnitary.continuous
      · intro x
        induction x using Quotient.inductionOn with
        | _ x =>
            change U
                ((Submodule.Quotient.mk x : KSGNSSeparated phi) : KSGNS phi) =
              Q.canonicalUnitary
                ((Submodule.Quotient.mk x : KSGNSSeparated phi) : KSGNS phi)
            rw [Q.pointedUnitary_coe_mk
              ⟨U, hcyc, hact, hrmul, hinner⟩, Q.canonicalUnitary_apply,
              Q.canonicalIsometry_coe, Q.separatedMap_mk]

/-- Existence and uniqueness of the pointed unitary equivalence from canonical KSGNS to any
minimal presentation. -/
theorem existsUnique_pointedUnitary : ∃! U : Q.PointedUnitary, True := by
  refine ⟨Q.canonicalPointedUnitary, trivial, ?_⟩
  intro U _
  exact Q.pointedUnitary_unique U

section BetweenPresentations

variable {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [CompleteSpace E₂]
    (Q₁ : MinimalKSGNSPresentation (A := A) (B := B) phi E₁)
    (Q₂ : MinimalKSGNSPresentation (A := A) (B := B) phi E₂)

/-- Pointed unitary equivalence between two arbitrary minimal KSGNS presentations. -/
structure PointedUnitaryBetween where
  toLinearIsometryEquiv : E₁ ≃ₗᵢ[ℂ] E₂
  map_cyclic : toLinearIsometryEquiv Q₁.xi = Q₂.xi
  map_act : ∀ a x,
    toLinearIsometryEquiv (Q₁.act a x) = Q₂.act a (toLinearIsometryEquiv x)
  map_rmul : ∀ b x,
    toLinearIsometryEquiv (Q₁.M.rmul x b) = Q₂.M.rmul (toLinearIsometryEquiv x) b
  map_inner : ∀ x y,
    Q₂.M.inner (toLinearIsometryEquiv x) (toLinearIsometryEquiv y) =
      Q₁.M.inner x y

instance : CoeFun (PointedUnitaryBetween Q₁ Q₂) (fun _ => E₁ → E₂) :=
  ⟨fun U => U.toLinearIsometryEquiv⟩

theorem canonicalUnitary_symm_act (a : A) (x : E₁) :
    Q₁.canonicalUnitary.symm (Q₁.act a x) =
      ksgnsRepresentation phi a (Q₁.canonicalUnitary.symm x) := by
  apply Q₁.canonicalUnitary.injective
  rw [Q₁.canonicalUnitary.apply_symm_apply, Q₁.canonicalUnitary_act,
    Q₁.canonicalUnitary.apply_symm_apply]

theorem canonicalUnitary_symm_rmul (b : B) (x : E₁) :
    Q₁.canonicalUnitary.symm (Q₁.M.rmul x b) =
      MulOpposite.op b • Q₁.canonicalUnitary.symm x := by
  apply Q₁.canonicalUnitary.injective
  rw [Q₁.canonicalUnitary.apply_symm_apply, Q₁.canonicalUnitary_rmul,
    Q₁.canonicalUnitary.apply_symm_apply]

/-- Canonical unitary between two minimal presentations, obtained through the canonical KSGNS
completion. -/
def canonicalUnitaryBetween : PointedUnitaryBetween Q₁ Q₂ where
  toLinearIsometryEquiv := Q₁.canonicalUnitary.symm.trans Q₂.canonicalUnitary
  map_cyclic := by
    change Q₂.canonicalUnitary (Q₁.canonicalUnitary.symm Q₁.xi) = Q₂.xi
    rw [← Q₁.canonicalUnitary_cyclic,
      Q₁.canonicalUnitary.symm_apply_apply, Q₂.canonicalUnitary_cyclic]
  map_act := by
    intro a x
    change Q₂.canonicalUnitary (Q₁.canonicalUnitary.symm (Q₁.act a x)) =
      Q₂.act a (Q₂.canonicalUnitary (Q₁.canonicalUnitary.symm x))
    rw [Q₁.canonicalUnitary_symm_act, Q₂.canonicalUnitary_act]
  map_rmul := by
    intro b x
    change Q₂.canonicalUnitary (Q₁.canonicalUnitary.symm (Q₁.M.rmul x b)) =
      Q₂.M.rmul (Q₂.canonicalUnitary (Q₁.canonicalUnitary.symm x)) b
    rw [Q₁.canonicalUnitary_symm_rmul, Q₂.canonicalUnitary_rmul]
  map_inner := by
    intro x y
    change Q₂.M.inner
        (Q₂.canonicalUnitary (Q₁.canonicalUnitary.symm x))
        (Q₂.canonicalUnitary (Q₁.canonicalUnitary.symm y)) = Q₁.M.inner x y
    rw [Q₂.canonicalUnitary_apply, Q₂.canonicalUnitary_apply,
      Q₂.inner_canonicalIsometry]
    have h := Q₁.inner_canonicalIsometry
      (Q₁.canonicalUnitary.symm x) (Q₁.canonicalUnitary.symm y)
    change Q₁.M.inner
      (Q₁.canonicalUnitary (Q₁.canonicalUnitary.symm x))
      (Q₁.canonicalUnitary (Q₁.canonicalUnitary.symm y)) = _ at h
    rw [Q₁.canonicalUnitary.apply_symm_apply,
      Q₁.canonicalUnitary.apply_symm_apply] at h
    exact h.symm

/-- Compose a unitary between presentations with the canonical unitary into its source. -/
def pullbackPointedUnitary (U : PointedUnitaryBetween Q₁ Q₂) : Q₂.PointedUnitary where
  toLinearIsometryEquiv := Q₁.canonicalUnitary.trans U.toLinearIsometryEquiv
  map_cyclic := by
    change U.toLinearIsometryEquiv (Q₁.canonicalUnitary (ksgnsCyclic phi)) = Q₂.xi
    rw [Q₁.canonicalUnitary_cyclic, U.map_cyclic]
  map_act := by
    intro a x
    change U.toLinearIsometryEquiv
        (Q₁.canonicalUnitary (ksgnsRepresentation phi a x)) =
      Q₂.act a (U.toLinearIsometryEquiv (Q₁.canonicalUnitary x))
    rw [Q₁.canonicalUnitary_act, U.map_act]
  map_rmul := by
    intro b x
    change U.toLinearIsometryEquiv
        (Q₁.canonicalUnitary (MulOpposite.op b • x)) =
      Q₂.M.rmul (U.toLinearIsometryEquiv (Q₁.canonicalUnitary x)) b
    rw [Q₁.canonicalUnitary_rmul, U.map_rmul]
  map_inner := by
    intro x y
    change Q₂.M.inner
        (U.toLinearIsometryEquiv (Q₁.canonicalUnitary x))
        (U.toLinearIsometryEquiv (Q₁.canonicalUnitary y)) =
      (ksgnsRightInnerModuleData phi).inner x y
    rw [U.map_inner, Q₁.canonicalUnitary_apply, Q₁.canonicalUnitary_apply,
      Q₁.inner_canonicalIsometry]

/-- Full two-presentation uniqueness. -/
theorem pointedUnitaryBetween_unique (U : PointedUnitaryBetween Q₁ Q₂) :
    U = canonicalUnitaryBetween Q₁ Q₂ := by
  have h := Q₂.pointedUnitary_unique (pullbackPointedUnitary Q₁ Q₂ U)
  cases U with
  | mk U hcyc hact hrmul hinner =>
      congr 1
      ext x
      have hx := congrArg
        (fun V : Q₂.PointedUnitary =>
          V (Q₁.canonicalUnitary.symm x)) h
      simpa [pullbackPointedUnitary, canonicalPointedUnitary,
        canonicalUnitaryBetween] using hx

/-- Any two minimal pointed KSGNS presentations admit exactly one pointed correspondence
unitary. -/
theorem existsUnique_pointedUnitaryBetween :
    ∃! U : PointedUnitaryBetween Q₁ Q₂, True := by
  refine ⟨canonicalUnitaryBetween Q₁ Q₂, trivial, ?_⟩
  intro U _
  exact pointedUnitaryBetween_unique Q₁ Q₂ U

end BetweenPresentations

end MinimalKSGNSPresentation

/-! ## Canonical construction is itself a complete minimal presentation -/

/-- Genuine complete right Hilbert-module data carried by the canonical KSGNS completion. -/
noncomputable def canonicalCompleteRightHilbertModuleData (phi : A →CP B) :
    CompleteRightHilbertModuleData B (KSGNS phi) where
  toRightInnerModuleData := ksgnsRightInnerModuleData phi
  rmul_smul_right := by
    intro q x b
    change MulOpposite.op (q • b) • x = q • MulOpposite.op b • x
    exact ksgnsCompleted_smul_op_smul phi q (MulOpposite.op b) x
  norm_eq_sqrt_norm_inner_self := by
    intro x
    have h := CStarModule.norm_eq_sqrt_norm_inner_self (A := Bᵐᵒᵖ) x
    change ‖x‖ = Real.sqrt ‖MulOpposite.unop
      (ksgnsCompletedInnerSLM phi x x)‖
    rw [← MulOpposite.norm_op (MulOpposite.unop
      (ksgnsCompletedInnerSLM phi x x))]
    simpa [ksgnsCompleted_inner_apply] using h
  continuous_inner_pair := continuous_ksgnsRightInner_pair phi
  rmulCLM b := ksgnsCompletedActionCLM phi (MulOpposite.op b)
  rmulCLM_apply := by
    intro b x
    rfl

/-- Canonical completed Paschke--KSGNS construction as a minimal pointed presentation. -/
noncomputable def canonicalMinimalKSGNSPresentation (phi : A →CP B) :
    MinimalKSGNSPresentation phi (KSGNS phi) where
  moduleData := canonicalCompleteRightHilbertModuleData phi
  act := ksgnsRepresentation phi
  xi := ksgnsCyclic phi
  act_one := by intro x; rw [ksgnsRepresentation_one]; rfl
  act_mul := by
    intro a c x
    exact congrArg (fun T : KSGNS phi →L[ℂ] KSGNS phi => T x)
      (ksgnsRepresentation_mul phi a c)
  act_add := by
    intro a c x
    exact congrArg (fun T : KSGNS phi →L[ℂ] KSGNS phi => T x)
      (ksgnsRepresentation_add phi a c)
  act_smul_label := by
    intro q a x
    exact congrArg (fun T : KSGNS phi →L[ℂ] KSGNS phi => T x)
      (ksgnsRepresentation_smul phi q a)
  act_rmul := by
    intro a x b
    exact ksgnsRepresentation_rmul phi a b x
  act_adjoint := by
    intro a x y
    exact congrArg MulOpposite.unop (ksgnsRepresentation_adjoint phi a x y)
  recover := ksgnsRight_inner_cyclic_rep_cyclic phi
  minimal := dense_ksgnsCyclicSpan phi

end GaloisForLFunctions.HTGeometry
