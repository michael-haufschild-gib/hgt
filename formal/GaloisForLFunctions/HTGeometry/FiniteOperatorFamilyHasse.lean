import GaloisForLFunctions.HTGeometry.SelfAdjointFamilyCommonKernel

/-!
# Finite operator-family Hasse detection

A finite family of complex-linear operators is treated as a family of local places. Its simultaneous
profile has exactly the common kernel, and the sum of squared local norms is a definite global detector.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X J : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [FiniteDimensional ℂ X] [Fintype J]

/-- Simultaneous local outputs of a finite operator family. -/
def finiteOperatorFamilyHasseProfile (A : J → X →ₗ[ℂ] X) : X →ₗ[ℂ] (J → X) :=
  LinearMap.pi A

omit [FiniteDimensional ℂ X] [Fintype J] in
@[simp] theorem finiteOperatorFamilyHasseProfile_apply
    (A : J → X →ₗ[ℂ] X) (x : X) (j : J) :
    finiteOperatorFamilyHasseProfile A x j = A j x :=
  rfl

omit [Fintype J] in
/-- Simultaneous local vanishing is exactly membership in the common kernel. -/
theorem finiteOperatorFamilyHasseProfile_ker (A : J → X →ₗ[ℂ] X) :
    LinearMap.ker (finiteOperatorFamilyHasseProfile A) = familyCommonKernel A := by
  ext x
  rw [LinearMap.mem_ker, mem_familyCommonKernel]
  constructor
  · intro h j
    exact congrFun h j
  · intro h
    funext j
    exact h j

/-- Global vectors modulo simultaneous local invisibility. -/
abbrev FiniteOperatorFamilyHasseClass (A : J → X →ₗ[ℂ] X) :=
  X ⧸ familyCommonKernel A

/-- Local-global quotient equals space of realized simultaneous profiles. -/
noncomputable def finiteOperatorFamilyHasseEquivRealizedProfiles
    (A : J → X →ₗ[ℂ] X) :
    FiniteOperatorFamilyHasseClass A ≃ₗ[ℂ]
      LinearMap.range (finiteOperatorFamilyHasseProfile A) :=
  (Submodule.quotEquivOfEq _ _ (finiteOperatorFamilyHasseProfile_ker A).symm).trans
    (LinearMap.quotKerEquivRange _)

omit [Fintype J] in
@[simp] theorem finiteOperatorFamilyHasseEquivRealizedProfiles_mk
    (A : J → X →ₗ[ℂ] X) (x : X) :
    finiteOperatorFamilyHasseEquivRealizedProfiles A (Submodule.Quotient.mk x) =
      ⟨finiteOperatorFamilyHasseProfile A x, ⟨x, rfl⟩⟩ := by
  rfl

omit [Fintype J] in
/-- Two global vectors define same class exactly when all local outputs agree. -/
theorem finiteOperatorFamily_congr_hasse_iff
    (A : J → X →ₗ[ℂ] X) (x y : X) :
    x - y ∈ familyCommonKernel A ↔ ∀ j, A j x = A j y := by
  rw [← finiteOperatorFamilyHasseProfile_ker, LinearMap.mem_ker, map_sub, sub_eq_zero]
  constructor
  · intro h j
    exact congrFun h j
  · intro h
    funext j
    exact h j

omit [Fintype J] in
/-- A quotient class vanishes exactly when every local operator vanishes on its representative. -/
theorem finiteOperatorFamilyClass_eq_zero_hasse_iff
    (A : J → X →ₗ[ℂ] X) (x : X) :
    Submodule.Quotient.mk x = (0 : FiniteOperatorFamilyHasseClass A) ↔
      ∀ j, A j x = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, mem_familyCommonKernel]

omit [Fintype J] in
/-- Every nonzero local-global class has a local operator witness. -/
theorem finiteOperatorFamilyClass_ne_zero_iff_exists_localWitness
    (A : J → X →ₗ[ℂ] X) (x : X) :
    Submodule.Quotient.mk x ≠ (0 : FiniteOperatorFamilyHasseClass A) ↔
      ∃ j, A j x ≠ 0 := by
  rw [ne_eq, finiteOperatorFamilyClass_eq_zero_hasse_iff, not_forall]

/-- Sum of squared local-output norms. -/
def finiteOperatorFamilyHasseEnergy (A : J → X →ₗ[ℂ] X) (x : X) : ℝ :=
  ∑ j, ‖A j x‖ ^ (2 : ℕ)

omit [FiniteDimensional ℂ X] in
theorem finiteOperatorFamilyHasseEnergy_nonneg
    (A : J → X →ₗ[ℂ] X) (x : X) :
    0 ≤ finiteOperatorFamilyHasseEnergy A x := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [FiniteDimensional ℂ X] in
/-- Definite assembled detector: energy vanishes exactly when every local output vanishes. -/
theorem finiteOperatorFamilyHasseEnergy_eq_zero_iff
    (A : J → X →ₗ[ℂ] X) (x : X) :
    finiteOperatorFamilyHasseEnergy A x = 0 ↔ ∀ j, A j x = 0 := by
  rw [finiteOperatorFamilyHasseEnergy,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  constructor
  · intro h j
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (h j (Finset.mem_univ j)))
  · intro h j _
    rw [h j, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]

/-- Energy zero is equivalent to vanishing of local-global quotient class. -/
theorem finiteOperatorFamilyHasseEnergy_eq_zero_iff_class_eq_zero
    (A : J → X →ₗ[ℂ] X) (x : X) :
    finiteOperatorFamilyHasseEnergy A x = 0 ↔
      Submodule.Quotient.mk x = (0 : FiniteOperatorFamilyHasseClass A) := by
  rw [finiteOperatorFamilyHasseEnergy_eq_zero_iff,
    finiteOperatorFamilyClass_eq_zero_hasse_iff]

/-- A local-global class is nonzero exactly when its assembled local energy is positive. -/
theorem finiteOperatorFamilyHasseEnergy_pos_iff_class_ne_zero
    (A : J → X →ₗ[ℂ] X) (x : X) :
    0 < finiteOperatorFamilyHasseEnergy A x ↔
      Submodule.Quotient.mk x ≠ (0 : FiniteOperatorFamilyHasseClass A) := by
  constructor
  · intro hpos hclass
    exact (ne_of_gt hpos)
      ((finiteOperatorFamilyHasseEnergy_eq_zero_iff_class_eq_zero A x).mpr hclass)
  · intro hclass
    exact lt_of_le_of_ne (finiteOperatorFamilyHasseEnergy_nonneg A x) fun hzero =>
      hclass ((finiteOperatorFamilyHasseEnergy_eq_zero_iff_class_eq_zero A x).mp hzero.symm)

end

end GaloisForLFunctions.HTGeometry
