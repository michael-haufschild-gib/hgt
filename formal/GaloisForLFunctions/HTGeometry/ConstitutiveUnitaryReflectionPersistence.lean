import GaloisForLFunctions.HTGeometry.ConstitutiveUnitaryFormationRadical
import GaloisForLFunctions.HTGeometry.GeneralizedEigenspaceIntertwining
import GaloisForLFunctions.HTGeometry.PolynomialShiftDifference

namespace GaloisForLFunctions.HTGeometry

open Module

noncomputable section

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

theorem map_finiteUnipotentFormationSubmodule_le
    (T : V ≃ₗ[ℝ] V) (S : W ≃ₗ[ℝ] W) (f : V →ₗ[ℝ] W)
    (hf : ∀ v, f (T v) = S (f v)) :
    Submodule.map f (finiteUnipotentFormationSubmodule T) ≤
      finiteUnipotentFormationSubmodule S := by
  rintro _ ⟨v, hv, rfl⟩
  change v ∈ Module.End.genEigenspace T.toLinearMap 1 ⊤ at hv
  obtain ⟨n, hn⟩ := Module.End.mem_genEigenspace_top.mp hv
  change f v ∈ Module.End.genEigenspace S.toLinearMap 1 ⊤
  apply Module.End.mem_genEigenspace_top.mpr
  refine ⟨n, ?_⟩
  rw [LinearMap.mem_ker] at hn ⊢
  rw [← map_pow_sub_smul_of_intertwining T.toLinearMap S.toLinearMap f hf 1 n v]
  rw [hn, map_zero]

theorem map_unitaryFormationRadical_le
    (T : V ≃ₗ[ℝ] V) (S : W ≃ₗ[ℝ] W) (f : V →ₗ[ℝ] W)
    (hf : ∀ v, f (T v) = S (f v)) :
    Submodule.map f (unitaryFormationRadical T) ≤ unitaryFormationRadical S := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨f v, map_finiteUnipotentFormationSubmodule_le T S f hf ⟨v, hv, rfl⟩, ?_⟩
  change S (f v) - f v = f (T v - v)
  rw [map_sub, hf]

def unitaryFormationReflectionMap
    (T : V ≃ₗ[ℝ] V) (S : W ≃ₗ[ℝ] W) (f : V →ₗ[ℝ] W)
    (hf : ∀ v, f (T v) = S (f v)) :
    V ⧸ unitaryFormationRadical T →ₗ[ℝ]
      W ⧸ unitaryFormationRadical S :=
  Submodule.mapQ (unitaryFormationRadical T) (unitaryFormationRadical S) f
    (by
      intro v hv
      exact map_unitaryFormationRadical_le T S f hf ⟨v, hv, rfl⟩)

@[simp] theorem unitaryFormationReflectionMap_mk
    (T : V ≃ₗ[ℝ] V) (S : W ≃ₗ[ℝ] W) (f : V →ₗ[ℝ] W)
    (hf : ∀ v, f (T v) = S (f v)) (v : V) :
    unitaryFormationReflectionMap T S f hf (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (f v) := rfl

theorem unitaryFormationReflectionMap_id (T : V ≃ₗ[ℝ] V) :
    unitaryFormationReflectionMap T T (LinearMap.id)
        (fun _ => rfl) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on (unitaryFormationRadical T) q ?_
  intro v
  rfl

theorem unitaryFormationReflectionMap_comp
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (T : V ≃ₗ[ℝ] V) (S : W ≃ₗ[ℝ] W) (R : X ≃ₗ[ℝ] X)
    (f : V →ₗ[ℝ] W) (g : W →ₗ[ℝ] X)
    (hf : ∀ v, f (T v) = S (f v))
    (hg : ∀ w, g (S w) = R (g w)) :
    unitaryFormationReflectionMap T R (g.comp f)
        (fun v => by simp [hf, hg]) =
      (unitaryFormationReflectionMap S R g hg).comp
        (unitaryFormationReflectionMap T S f hf) := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on (unitaryFormationRadical T) q ?_
  intro v
  rfl

theorem unitaryFormationReflectionMap_not_injective_of_migrating_horizon
    (T : V ≃ₗ[ℝ] V) (S : W ≃ₗ[ℝ] W) (f : V →ₗ[ℝ] W)
    (hf : ∀ v, f (T v) = S (f v)) (v : V)
    (hv : v ∉ unitaryFormationRadical T)
    (hfv : f v ∈ unitaryFormationRadical S) :
    ¬ Function.Injective (unitaryFormationReflectionMap T S f hf) := by
  intro hinj
  have hzero : unitaryFormationReflectionMap T S f hf
      (Submodule.Quotient.mk v) = 0 := by
    rw [unitaryFormationReflectionMap_mk]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hfv
  have hmk : (Submodule.Quotient.mk v : V ⧸ unitaryFormationRadical T) = 0 := by
    apply hinj
    simpa using hzero
  exact hv ((Submodule.Quotient.mk_eq_zero _).mp hmk)

abbrev JordanFormationTwo := ℝ × ℝ
abbrev JordanFormationThree := (ℝ × ℝ) × ℝ

def jordanFormationTwo : JordanFormationTwo ≃ₗ[ℝ] JordanFormationTwo where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 - p.2, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' _ _ := by
    apply Prod.ext
    · dsimp
      ring
    · rfl
  map_smul' _ _ := by
    apply Prod.ext
    · dsimp
      ring
    · rfl

def jordanFormationThree : JordanFormationThree ≃ₗ[ℝ] JordanFormationThree where
  toFun p := ((p.1.1 + p.1.2, p.1.2 + p.2), p.2)
  invFun p := ((p.1.1 - p.1.2 + p.2, p.1.2 - p.2), p.2)
  left_inv _ := by ext <;> dsimp <;> ring
  right_inv _ := by ext <;> dsimp <;> ring
  map_add' _ _ := by ext <;> dsimp <;> ring
  map_smul' _ _ := by ext <;> dsimp <;> ring

def jordanFormationEmbed : JordanFormationTwo →ₗ[ℝ] JordanFormationThree where
  toFun p := ((p.1, p.2), 0)
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

def jordanFormationHeadTwo : JordanFormationTwo →ₗ[ℝ] ℝ where
  toFun p := p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def jordanFormationHeadThree : JordanFormationThree →ₗ[ℝ] ℝ where
  toFun p := p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem jordanFormationEmbed_intertwines (v : JordanFormationTwo) :
    jordanFormationEmbed (jordanFormationTwo v) =
      jordanFormationThree (jordanFormationEmbed v) := by
  ext <;> simp [jordanFormationEmbed, jordanFormationTwo, jordanFormationThree]

theorem jordanFormationHeadTwo_invariant (v : JordanFormationTwo) :
    jordanFormationHeadTwo (jordanFormationTwo v) = jordanFormationHeadTwo v := rfl

theorem jordanFormationHeadThree_invariant (v : JordanFormationThree) :
    jordanFormationHeadThree (jordanFormationThree v) = jordanFormationHeadThree v := rfl

def jordanFormationOldHorizon : JordanFormationTwo := (0, 1)
def jordanFormationNewPrimitive : JordanFormationThree := ((0, 0), 1)

theorem jordanFormation_unit_head_conservation :
    jordanFormationHeadTwo jordanFormationOldHorizon = 1 ∧
      jordanFormationHeadThree (jordanFormationEmbed jordanFormationOldHorizon) = 0 ∧
      jordanFormationHeadThree jordanFormationNewPrimitive = 1 := by
  norm_num [jordanFormationHeadTwo, jordanFormationHeadThree, jordanFormationEmbed,
    jordanFormationOldHorizon, jordanFormationNewPrimitive]

theorem jordanFormationOldHorizon_migrates_to_boundary :
    jordanFormationEmbed jordanFormationOldHorizon =
      linearFormationDisplacement jordanFormationThree jordanFormationNewPrimitive := by
  ext <;> simp [jordanFormationEmbed, jordanFormationOldHorizon,
    jordanFormationNewPrimitive, linearFormationDisplacement, jordanFormationThree]

theorem jordanFormationNewPrimitive_finite :
    jordanFormationNewPrimitive ∈
      finiteUnipotentFormationSubmodule jordanFormationThree := by
  rw [finiteUnipotentFormationSubmodule]
  apply Module.End.mem_genEigenspace_top.mpr
  refine ⟨3, ?_⟩
  rw [LinearMap.mem_ker]
  ext <;> norm_num [jordanFormationNewPrimitive, jordanFormationThree, pow_succ]

theorem jordanFormationTwo_all_finite (v : JordanFormationTwo) :
    v ∈ finiteUnipotentFormationSubmodule jordanFormationTwo := by
  rw [finiteUnipotentFormationSubmodule]
  apply Module.End.mem_genEigenspace_top.mpr
  refine ⟨2, ?_⟩
  rw [LinearMap.mem_ker]
  ext <;> norm_num [jordanFormationTwo, pow_succ]

theorem jordanFormationThree_all_finite (v : JordanFormationThree) :
    v ∈ finiteUnipotentFormationSubmodule jordanFormationThree := by
  rw [finiteUnipotentFormationSubmodule]
  apply Module.End.mem_genEigenspace_top.mpr
  refine ⟨3, ?_⟩
  rw [LinearMap.mem_ker]
  ext <;> norm_num [jordanFormationThree, pow_succ]

theorem jordanFormationTwo_radical_eq_head_ker :
    unitaryFormationRadical jordanFormationTwo = jordanFormationHeadTwo.ker := by
  apply le_antisymm
  · exact unitaryFormationRadical_le_reporter_ker jordanFormationTwo
      jordanFormationHeadTwo (LinearIsometryEquiv.refl ℝ ℝ)
      jordanFormationHeadTwo_invariant
  · rintro ⟨x, y⟩ hy
    change y = 0 at hy
    subst y
    refine ⟨(0, x), jordanFormationTwo_all_finite (0, x), ?_⟩
    ext <;> simp [linearFormationDisplacement, jordanFormationTwo]

theorem jordanFormationThree_radical_eq_head_ker :
    unitaryFormationRadical jordanFormationThree = jordanFormationHeadThree.ker := by
  apply le_antisymm
  · exact unitaryFormationRadical_le_reporter_ker jordanFormationThree
      jordanFormationHeadThree (LinearIsometryEquiv.refl ℝ ℝ)
      jordanFormationHeadThree_invariant
  · rintro ⟨⟨x, y⟩, z⟩ hz
    change z = 0 at hz
    subst z
    refine ⟨((0, x), y), jordanFormationThree_all_finite ((0, x), y), ?_⟩
    ext <;> simp [linearFormationDisplacement, jordanFormationThree]

def jordanFormationHeadTwoFactor :
    JordanFormationTwo ⧸ unitaryFormationRadical jordanFormationTwo →ₗ[ℝ] ℝ :=
  unitaryReporterSemisimpleFactor jordanFormationTwo jordanFormationHeadTwo
    (LinearIsometryEquiv.refl ℝ ℝ) jordanFormationHeadTwo_invariant

def jordanFormationHeadThreeFactor :
    JordanFormationThree ⧸ unitaryFormationRadical jordanFormationThree →ₗ[ℝ] ℝ :=
  unitaryReporterSemisimpleFactor jordanFormationThree jordanFormationHeadThree
    (LinearIsometryEquiv.refl ℝ ℝ) jordanFormationHeadThree_invariant

def jordanFormationHeadTwoRawSection : ℝ →ₗ[ℝ] JordanFormationTwo where
  toFun c := (0, c)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def jordanFormationHeadThreeRawSection : ℝ →ₗ[ℝ] JordanFormationThree where
  toFun c := ((0, 0), c)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def jordanFormationHeadTwoSection :
    ℝ →ₗ[ℝ] JordanFormationTwo ⧸ unitaryFormationRadical jordanFormationTwo :=
  (Submodule.mkQ (unitaryFormationRadical jordanFormationTwo)).comp
    jordanFormationHeadTwoRawSection

def jordanFormationHeadThreeSection :
    ℝ →ₗ[ℝ] JordanFormationThree ⧸ unitaryFormationRadical jordanFormationThree :=
  (Submodule.mkQ (unitaryFormationRadical jordanFormationThree)).comp
    jordanFormationHeadThreeRawSection

@[simp] theorem jordanFormationHeadTwoFactor_section (c : ℝ) :
    jordanFormationHeadTwoFactor (jordanFormationHeadTwoSection c) = c := by
  rw [jordanFormationHeadTwoSection]
  change jordanFormationHeadTwoFactor (Submodule.Quotient.mk (0, c)) = c
  rw [jordanFormationHeadTwoFactor, unitaryReporterSemisimpleFactor_mk]
  rfl

@[simp] theorem jordanFormationHeadThreeFactor_section (c : ℝ) :
    jordanFormationHeadThreeFactor (jordanFormationHeadThreeSection c) = c := by
  rw [jordanFormationHeadThreeSection]
  change jordanFormationHeadThreeFactor (Submodule.Quotient.mk ((0, 0), c)) = c
  rw [jordanFormationHeadThreeFactor, unitaryReporterSemisimpleFactor_mk]
  rfl

theorem jordanFormationHeadTwoSection_factor
    (q : JordanFormationTwo ⧸ unitaryFormationRadical jordanFormationTwo) :
    jordanFormationHeadTwoSection (jordanFormationHeadTwoFactor q) = q := by
  refine Submodule.Quotient.induction_on (unitaryFormationRadical jordanFormationTwo) q ?_
  rintro ⟨x, y⟩
  rw [jordanFormationHeadTwoSection, jordanFormationHeadTwoFactor,
    unitaryReporterSemisimpleFactor_mk]
  change Submodule.Quotient.mk (0, y) = Submodule.Quotient.mk (x, y)
  apply (Submodule.Quotient.eq (unitaryFormationRadical jordanFormationTwo)).mpr
  rw [jordanFormationTwo_radical_eq_head_ker]
  change jordanFormationHeadTwo ((0, y) - (x, y)) = 0
  simp [jordanFormationHeadTwo]

theorem jordanFormationHeadThreeSection_factor
    (q : JordanFormationThree ⧸ unitaryFormationRadical jordanFormationThree) :
    jordanFormationHeadThreeSection (jordanFormationHeadThreeFactor q) = q := by
  refine Submodule.Quotient.induction_on (unitaryFormationRadical jordanFormationThree) q ?_
  rintro ⟨⟨x, y⟩, z⟩
  rw [jordanFormationHeadThreeSection, jordanFormationHeadThreeFactor,
    unitaryReporterSemisimpleFactor_mk]
  change Submodule.Quotient.mk ((0, 0), z) = Submodule.Quotient.mk ((x, y), z)
  apply (Submodule.Quotient.eq (unitaryFormationRadical jordanFormationThree)).mpr
  rw [jordanFormationThree_radical_eq_head_ker]
  change jordanFormationHeadThree (((0, 0), z) - ((x, y), z)) = 0
  simp [jordanFormationHeadThree]

def jordanFormationHeadTwoEquiv :
    (JordanFormationTwo ⧸ unitaryFormationRadical jordanFormationTwo) ≃ₗ[ℝ] ℝ where
  toFun := jordanFormationHeadTwoFactor
  invFun := jordanFormationHeadTwoSection
  left_inv := jordanFormationHeadTwoSection_factor
  right_inv := jordanFormationHeadTwoFactor_section
  map_add' := map_add jordanFormationHeadTwoFactor
  map_smul' := map_smul jordanFormationHeadTwoFactor

def jordanFormationHeadThreeEquiv :
    (JordanFormationThree ⧸ unitaryFormationRadical jordanFormationThree) ≃ₗ[ℝ] ℝ where
  toFun := jordanFormationHeadThreeFactor
  invFun := jordanFormationHeadThreeSection
  left_inv := jordanFormationHeadThreeSection_factor
  right_inv := jordanFormationHeadThreeFactor_section
  map_add' := map_add jordanFormationHeadThreeFactor
  map_smul' := map_smul jordanFormationHeadThreeFactor

theorem jordanFormationReflectionMap_eq_zero :
    unitaryFormationReflectionMap jordanFormationTwo jordanFormationThree
        jordanFormationEmbed jordanFormationEmbed_intertwines = 0 := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on (unitaryFormationRadical jordanFormationTwo) q ?_
  intro v
  rw [unitaryFormationReflectionMap_mk]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [jordanFormationThree_radical_eq_head_ker]
  change jordanFormationHeadThree (jordanFormationEmbed v) = 0
  rfl

theorem jordanFormationOldHorizon_not_mem_radical :
    jordanFormationOldHorizon ∉ unitaryFormationRadical jordanFormationTwo := by
  rintro ⟨v, hv, hEq⟩
  have hsnd := congrArg Prod.snd hEq
  norm_num [jordanFormationOldHorizon, linearFormationDisplacement,
    jordanFormationTwo] at hsnd

theorem jordanFormationEmbeddedHorizon_mem_radical :
    jordanFormationEmbed jordanFormationOldHorizon ∈
      unitaryFormationRadical jordanFormationThree := by
  refine ⟨jordanFormationNewPrimitive, jordanFormationNewPrimitive_finite, ?_⟩
  exact jordanFormationOldHorizon_migrates_to_boundary.symm

theorem every_unitaryReporter_kills_jordanMigratedHorizon
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (r : JordanFormationThree →ₗ[ℝ] H) (U : H ≃ₗᵢ[ℝ] H)
    (hintertwine : ∀ v, r (jordanFormationThree v) = U (r v)) :
    r (jordanFormationEmbed jordanFormationOldHorizon) = 0 := by
  exact unitaryFormationRadical_le_reporter_ker
    jordanFormationThree r U hintertwine
      jordanFormationEmbeddedHorizon_mem_radical

theorem jordanFormationReflectionMap_not_injective :
    ¬ Function.Injective
      (unitaryFormationReflectionMap jordanFormationTwo jordanFormationThree
        jordanFormationEmbed jordanFormationEmbed_intertwines) :=
  unitaryFormationReflectionMap_not_injective_of_migrating_horizon
    jordanFormationTwo jordanFormationThree jordanFormationEmbed
    jordanFormationEmbed_intertwines jordanFormationOldHorizon
    jordanFormationOldHorizon_not_mem_radical
    jordanFormationEmbeddedHorizon_mem_radical

/-- The falling-factorial head is visible at degree `n`, but the same packet is
an exact shift-difference boundary once degree `n + 1` is admitted. -/
theorem polynomialFormation_head_becomes_nextBoundary
    {a : ℂ} (ha : a ≠ 0) (n : ℕ) :
    (fallPoly a n).coeff n = 1 ∧
      fallPoly a n ∈ LinearMap.range (shiftDiffPoly a) :=
  ⟨coeff_fallPoly_self a n, fallPoly_mem_range ha n⟩

end

end GaloisForLFunctions.HTGeometry
