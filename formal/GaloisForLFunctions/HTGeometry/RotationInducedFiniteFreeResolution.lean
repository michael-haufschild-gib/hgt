import GaloisForLFunctions.HTGeometry.IntegerFlowLaurentResolution

/-!
# Finite free resolution over the concrete rotation algebra

For a finite-dimensional actual integer flow, the induced arithmetic module
has the exact presentation by right multiplication with V I - [T_1].
The independent Weyl basis transports the proved finite Laurent resolution;
its noncommutative phase correction is an explicit invertible row scaling.
Both maps are left-algebra equivariant. No projectivity of the quotient,
completed C*-module, or Chern pairing is asserted.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped Classical
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The clock phase twists the actual flow, rather than changing its source. -/
def rotationClockFlow (t : ℝ) (T : IntegerLinearFlow M) (a : ℤ) : IntegerLinearFlow M where
  toFun b := paperRotationPhase (((Multiplicative.toAdd b : ℤ) : ℝ) * t * (a : ℝ)) • T b
  map_one' := by simp
  map_mul' b c := by
    simp only [toAdd_mul, Int.cast_add, map_mul, smul_mul_smul_comm]
    rw [← paperRotationPhase_add]
    congr 2
    ring

/-- Ordered Weyl coefficients with values in the full source vector space. -/
abbrev RotationModuleCoefficients (M : Type*) [AddCommGroup M] := ℤ →₀ ℤ →₀ M

/-- Evaluate each outer clock row using its phase-twisted actual flow. -/
def rotationCoefficientEvaluation (t : ℝ) (T : IntegerLinearFlow M) :
    RotationModuleCoefficients M →ₗ[ℂ] (ℤ →₀ M) :=
  Finsupp.lsum ℂ fun a => (Finsupp.lsingle a).comp (integerFlowEvaluation (rotationClockFlow t T a))

/-- Shift-minus-flow in each Weyl row. -/
def rotationCoefficientRelation (t : ℝ) (T : IntegerLinearFlow M) :
    Module.End ℂ (RotationModuleCoefficients M) :=
  Finsupp.lsum ℂ fun a => (Finsupp.lsingle a).comp (integerFlowRelation (rotationClockFlow t T a))

@[simp] theorem rotationCoefficientEvaluation_single (t : ℝ) (T : IntegerLinearFlow M)
    (a : ℤ) (x : ℤ →₀ M) :
    rotationCoefficientEvaluation t T (Finsupp.single a x) =
      Finsupp.single a (integerFlowEvaluation (rotationClockFlow t T a) x) := by
  simp [rotationCoefficientEvaluation]

@[simp] theorem rotationCoefficientRelation_single (t : ℝ) (T : IntegerLinearFlow M)
    (a : ℤ) (x : ℤ →₀ M) :
    rotationCoefficientRelation t T (Finsupp.single a x) =
      Finsupp.single a (integerFlowRelation (rotationClockFlow t T a) x) := by
  simp [rotationCoefficientRelation]

@[simp] theorem rotationCoefficientEvaluation_apply (t : ℝ) (T : IntegerLinearFlow M)
    (x : RotationModuleCoefficients M) (a : ℤ) :
    rotationCoefficientEvaluation t T x a = integerFlowEvaluation (rotationClockFlow t T a) (x a) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | single b m => by_cases h : b = a <;> simp [h]

@[simp] theorem rotationCoefficientRelation_apply (t : ℝ) (T : IntegerLinearFlow M)
    (x : RotationModuleCoefficients M) (a : ℤ) :
    rotationCoefficientRelation t T x a = integerFlowRelation (rotationClockFlow t T a) (x a) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | single b m => by_cases h : b = a <;> simp [h]

/-- Exactness survives the outer Weyl clock, with finite support preserved. -/
theorem rotationCoefficientEvaluation_ker (t : ℝ) (T : IntegerLinearFlow M) :
    LinearMap.ker (rotationCoefficientEvaluation t T) =
      LinearMap.range (rotationCoefficientRelation t T) := by
  apply le_antisymm
  · intro x hx
    have hx0 : ∀ a, integerFlowEvaluation (rotationClockFlow t T a) (x a) = 0 := by
      intro a
      simpa only [rotationCoefficientEvaluation_apply, Finsupp.zero_apply] using
        congrArg (fun y : ℤ →₀ M => y a) hx
    have hr : ∀ a, ∃ y, integerFlowRelation (rotationClockFlow t T a) y = x a := by
      intro a
      have h : x a ∈ LinearMap.ker (integerFlowEvaluation (rotationClockFlow t T a)) := hx0 a
      rw [integerFlowEvaluation_ker] at h
      exact h
    choose f hf using hr
    let y : RotationModuleCoefficients M := Finsupp.onFinset x.support
      (fun a => if a ∈ x.support then f a else 0)
      (by intro a h; by_contra ha; exact h (if_neg ha))
    refine ⟨y, ?_⟩
    apply Finsupp.ext
    intro a
    rw [rotationCoefficientRelation_apply]
    change integerFlowRelation (rotationClockFlow t T a)
      (if a ∈ x.support then f a else 0) = x a
    by_cases ha : a ∈ x.support
    · rw [if_pos ha, hf]
    · rw [if_neg ha, map_zero, Finsupp.notMem_support_iff.mp ha]
  · rintro _ ⟨x, rfl⟩
    apply Finsupp.ext
    intro a
    simp

theorem rotationCoefficientRelation_injective (t : ℝ) (T : IntegerLinearFlow M) :
    Function.Injective (rotationCoefficientRelation t T) := by
  intro x y h
  apply Finsupp.ext
  intro a
  apply integerFlowRelation_injective (rotationClockFlow t T a)
  simpa only [rotationCoefficientRelation_apply] using
    congrArg (fun z : RotationModuleCoefficients M => z a) h

/-- A unit phase on each outer Weyl row. -/
def rotationCoefficientRowScale (t : ℝ) : Module.End ℂ (RotationModuleCoefficients M) :=
  Finsupp.lsum ℂ fun a => (Finsupp.lsingle a).comp
    (paperRotationPhase ((a : ℝ) * t) • (LinearMap.id : Module.End ℂ (ℤ →₀ M)))

@[simp] theorem rotationCoefficientRowScale_single (t : ℝ) (a : ℤ) (x : ℤ →₀ M) :
    rotationCoefficientRowScale t (Finsupp.single a x) =
      Finsupp.single a (paperRotationPhase ((a : ℝ) * t) • x) := by
  simp [rotationCoefficientRowScale]

@[simp] theorem rotationCoefficientRowScale_neg (t : ℝ) (x : RotationModuleCoefficients M) :
    rotationCoefficientRowScale (-t) (rotationCoefficientRowScale t x) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single a m =>
    simp only [rotationCoefficientRowScale_single, smul_smul, ← paperRotationPhase_add]
    rw [show (a : ℝ) * -t + (a : ℝ) * t = 0 by ring, paperRotationPhase_zero, one_smul]

def rotationCoefficientRowEquiv (t : ℝ) : RotationModuleCoefficients M ≃ₗ[ℂ] RotationModuleCoefficients M :=
  LinearEquiv.ofLinear (rotationCoefficientRowScale t) (rotationCoefficientRowScale (-t))
    (by apply LinearMap.ext; intro x; simpa only [LinearMap.comp_apply, LinearMap.id_apply, neg_neg] using
      rotationCoefficientRowScale_neg (-t) x)
    (by apply LinearMap.ext; intro x; exact rotationCoefficientRowScale_neg t x)

section FreeCoordinates
variable {ι : Type*} [Fintype ι]
variable (t : ℝ) (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)
variable (B : Module.Basis ι ℂ M)

/-- Genuine finite Weyl coordinates, using the proved independent operator basis. -/
def rotationFreeCoordinates :
    RotationModuleCoefficients M ≃ₗ[ℂ] (ι → paperRotationPolynomialAlgebra t) :=
  (Finsupp.curryLinearEquiv ℂ).symm ≪≫ₗ
    Finsupp.lcongr (Equiv.refl (ℤ × ℤ)) B.repr ≪≫ₗ
    (Finsupp.curryLinearEquiv ℂ).symm ≪≫ₗ
    Finsupp.domLCongr (Equiv.prodComm (ℤ × ℤ) ι) ≪≫ₗ
    Finsupp.curryLinearEquiv ℂ ≪≫ₗ
    Finsupp.lcongr (Equiv.refl ι) (paperRotationWords_linearIndependent t ht).linearCombinationEquiv ≪≫ₗ
    Finsupp.linearEquivFunOnFinite ℂ _ ι

@[simp] theorem rotationFreeCoordinates_basis (a b : ℤ) (i : ι) :
    rotationFreeCoordinates t ht B (Finsupp.single a (Finsupp.single b (B i))) =
      Pi.single i (paperRotationPolynomialWord t a b) := by
  have hw : (paperRotationWords_linearIndependent t ht).linearCombinationEquiv
      (Finsupp.single (a, b) 1) = paperRotationPolynomialWord t a b := by
    apply Subtype.ext
    simp only [LinearIndependent.linearCombinationEquiv_apply_coe,
      Finsupp.linearCombination_single, one_smul]
    rfl
  simp only [rotationFreeCoordinates, LinearEquiv.trans_apply, Finsupp.curryLinearEquiv_symm_apply,
    Finsupp.uncurry_single, Finsupp.lcongr_single, Equiv.refl_apply, B.repr_self,
    Finsupp.domLCongr_single, Equiv.prodComm_apply, Finsupp.curryLinearEquiv_apply,
    Finsupp.curry_single]
  change (Finsupp.linearEquivFunOnFinite ℂ (paperRotationPolynomialAlgebra t) ι)
    (Finsupp.single i ((paperRotationWords_linearIndependent t ht).linearCombinationEquiv
      (Finsupp.single (a, b) 1))) = _
  rw [hw, Finsupp.linearEquivFunOnFinite_single]

@[simp] theorem rotationFreeCoordinates_single (a b : ℤ) (m : M) (i : ι) :
    rotationFreeCoordinates t ht B (Finsupp.single a (Finsupp.single b m)) i =
      B.repr m i • paperRotationPolynomialWord t a b := by
  have hsum : Finsupp.single a (Finsupp.single b m) =
      ∑ j, B.repr m j • Finsupp.single a (Finsupp.single b (B j)) := by
    calc
      _ = ((Finsupp.lsingle a).comp (Finsupp.lsingle b) : M →ₗ[ℂ] _)
          (∑ j, B.repr m j • B j) := by rw [B.sum_repr]; rfl
      _ = _ := by simp only [map_sum, map_smul, LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [hsum, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, rotationFreeCoordinates_basis]
  simp [Pi.single_apply]


variable (T : IntegerLinearFlow M)

/-- The explicit right relation matrix V I - [T_1]_B on the actual finite free module. -/
def rotationInducedFreeRelation :
    Module.End ℂ (ι → paperRotationPolynomialAlgebra t) where
  toFun C i := C i * paperRotationPolynomialWord t 0 1 -
    ∑ j, (B.repr (T (Multiplicative.ofAdd 1) (B j)) i) • C j
  map_add' C D := by
    funext i
    simp only [Pi.add_apply, add_mul, smul_add, Finset.sum_add_distrib, sub_add_sub_comm]
  map_smul' z C := by
    funext i
    simp only [Pi.smul_apply, smul_mul_assoc, smul_sub, Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm _ _ _

/-- Right multiplication by the relation matrix is left-algebra equivariant. -/
theorem rotationInducedFreeRelation_equivariant (A : paperRotationPolynomialAlgebra t)
    (C : ι → paperRotationPolynomialAlgebra t) :
    rotationInducedFreeRelation t B T (fun i => A * C i) =
      fun i => A * rotationInducedFreeRelation t B T C i := by
  funext i
  simp only [rotationInducedFreeRelation, LinearMap.coe_mk, AddHom.coe_mk,
    mul_sub, Finset.mul_sum, mul_assoc, mul_smul_comm]

@[simp] theorem rotationInducedFreeRelation_single (i j : ι) (X : paperRotationPolynomialAlgebra t) :
    rotationInducedFreeRelation t B T (Pi.single i X) j =
      (Pi.single i (X * paperRotationPolynomialWord t 0 1) : ι → paperRotationPolynomialAlgebra t) j -
        (B.repr (T (Multiplicative.ofAdd 1) (B i)) j) • X := by
  simp [rotationInducedFreeRelation, Pi.single_apply]

private theorem freeCover_coordinates_basis (a b : ℤ) (i : ι) :
    rotationInducedFreeCover t ht T B
      (rotationFreeCoordinates t ht B (Finsupp.single a (Finsupp.single b (B i)))) =
        rotationCoefficientEvaluation t T (Finsupp.single a (Finsupp.single b (B i))) := by
  rw [rotationFreeCoordinates_basis]
  change (∑ j, rotationInducedRepresentation t ht T
    ((Pi.single i (paperRotationPolynomialWord t a b) : ι → _) j)
      (Finsupp.single 0 (B j))) = _
  rw [Finset.sum_eq_single i]
  · simp [rotationClockFlow]
  · intro j _ hji
    simp [hji]
  · simp

/-- The finite free cover is literally the coefficient evaluation under the Weyl basis. -/
theorem rotationInducedFreeCover_coordinates (C : RotationModuleCoefficients M) :
    rotationInducedFreeCover t ht T B (rotationFreeCoordinates t ht B C) =
      rotationCoefficientEvaluation t T C := by
  suffices h : (rotationInducedFreeCover t ht T B).comp
      (rotationFreeCoordinates t ht B).toLinearMap = rotationCoefficientEvaluation t T from
    congrArg (fun L : RotationModuleCoefficients M →ₗ[ℂ] (ℤ →₀ M) => L C) h
  apply Finsupp.lhom_ext'
  intro a
  apply Finsupp.lhom_ext'
  intro b
  apply B.ext
  intro i
  exact freeCover_coordinates_basis t ht B T a b i

private theorem freeRelation_coordinates_basis (a b : ℤ) (i : ι) :
    rotationInducedFreeRelation t B T
      (rotationFreeCoordinates t ht B (Finsupp.single a (Finsupp.single b (B i)))) =
      rotationFreeCoordinates t ht B
        (rotationCoefficientRelation t T
          (rotationCoefficientRowScale (-t) (Finsupp.single a (Finsupp.single b (B i))))) := by
  have hp : paperRotationPhase ((a : ℝ) * -t) * paperRotationPhase (t * (a : ℝ)) = 1 := by
    rw [← paperRotationPhase_add, show (a : ℝ) * -t + t * (a : ℝ) = 0 by ring,
      paperRotationPhase_zero]
  have hflow : rotationClockFlow t T a (Multiplicative.ofAdd 1) (B i) =
      paperRotationPhase (t * (a : ℝ)) • T (Multiplicative.ofAdd 1) (B i) := by
    change paperRotationPhase (((1 : ℤ) : ℝ) * t * (a : ℝ)) •
      T (Multiplicative.ofAdd 1) (B i) =
        paperRotationPhase (t * (a : ℝ)) • T (Multiplicative.ofAdd 1) (B i)
    rw [Int.cast_one, one_mul]
  have hq : (↑(paperRotationQuantumUnit t ^ a) : ℂ) = paperRotationPhase ((a : ℝ) * -t) := by
    rw [paperRotationQuantumUnit_zpow]
    congr 1
    ring
  funext j
  rw [rotationFreeCoordinates_basis, rotationInducedFreeRelation_single]
  simp only [rotationCoefficientRowScale_single, ← Finsupp.smul_single, map_smul,
    rotationCoefficientRelation_single, integerFlowRelation_single,
    Finsupp.single_sub, map_sub, Pi.smul_apply, Pi.sub_apply,
    rotationFreeCoordinates_basis, rotationFreeCoordinates_single]
  simp only [hflow, map_smul, Finsupp.smul_apply, smul_sub, smul_smul]
  change (Pi.single i (paperRotationPolynomialWord t a b * paperRotationPolynomialWord t 0 1) :
      ι → paperRotationPolynomialAlgebra t) j -
        (B.repr (T (Multiplicative.ofAdd 1) (B i)) j) • paperRotationPolynomialWord t a b =
    paperRotationPhase ((a : ℝ) * -t) •
      (Pi.single i (paperRotationPolynomialWord t a (b + 1)) : ι → paperRotationPolynomialAlgebra t) j -
      (paperRotationPhase ((a : ℝ) * -t) * (paperRotationPhase (t * (a : ℝ)) *
        B.repr (T (Multiplicative.ofAdd 1) (B i)) j)) • paperRotationPolynomialWord t a b
  rw [← mul_assoc, hp, one_mul]
  by_cases hij : i = j
  · subst j
    simp only [Pi.single_eq_same, paperRotationPolynomialWord_mul, mul_one, add_zero, hq]
  · simp [hij]

/-- Exact change of coordinates, including the noncommutative phase correction. -/
theorem rotationInducedFreeRelation_coordinates (C : RotationModuleCoefficients M) :
    rotationInducedFreeRelation t B T (rotationFreeCoordinates t ht B C) =
      rotationFreeCoordinates t ht B
        (rotationCoefficientRelation t T (rotationCoefficientRowScale (-t) C)) := by
  suffices h : (rotationInducedFreeRelation t B T).comp
      (rotationFreeCoordinates t ht B).toLinearMap =
      (rotationFreeCoordinates t ht B).toLinearMap.comp
        ((rotationCoefficientRelation t T).comp (rotationCoefficientRowScale (-t))) from
    congrArg (fun L : RotationModuleCoefficients M →ₗ[ℂ] (ι → paperRotationPolynomialAlgebra t) => L C) h
  apply Finsupp.lhom_ext'
  intro a
  apply Finsupp.lhom_ext'
  intro b
  apply B.ext
  intro i
  exact freeRelation_coordinates_basis t ht B T a b i

include ht in
/-- The concrete noncommutative relation matrix is injective. -/
theorem rotationInducedFreeRelation_injective :
    Function.Injective (rotationInducedFreeRelation t B T) := by
  intro X Y h
  obtain ⟨x, rfl⟩ := (rotationFreeCoordinates t ht B).surjective X
  obtain ⟨y, rfl⟩ := (rotationFreeCoordinates t ht B).surjective Y
  rw [rotationInducedFreeRelation_coordinates, rotationInducedFreeRelation_coordinates] at h
  have hxy := (rotationCoefficientRelation_injective t T)
    ((rotationFreeCoordinates t ht B).injective h)
  have hxy' : x = y := (rotationCoefficientRowEquiv (-t)).injective hxy
  rw [hxy']

/-- The displayed right matrix generates all relations of the arithmetic induced module. -/
theorem rotationInducedFreeCover_ker :
    LinearMap.ker (rotationInducedFreeCover t ht T B) =
      LinearMap.range (rotationInducedFreeRelation t B T) := by
  apply le_antisymm
  · intro X hX
    obtain ⟨x, rfl⟩ := (rotationFreeCoordinates t ht B).surjective X
    have hx : x ∈ LinearMap.ker (rotationCoefficientEvaluation t T) := by
      change rotationCoefficientEvaluation t T x = 0
      rw [← rotationInducedFreeCover_coordinates t ht B T]
      exact hX
    rw [rotationCoefficientEvaluation_ker] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨rotationFreeCoordinates t ht B (rotationCoefficientRowScale t y), ?_⟩
    rw [rotationInducedFreeRelation_coordinates, rotationCoefficientRowScale_neg, hy]
  · rintro _ ⟨X, rfl⟩
    obtain ⟨x, rfl⟩ := (rotationFreeCoordinates t ht B).surjective X
    change rotationInducedFreeCover t ht T B
      (rotationInducedFreeRelation t B T (rotationFreeCoordinates t ht B x)) = 0
    rw [rotationInducedFreeRelation_coordinates, rotationInducedFreeCover_coordinates]
    apply Finsupp.ext
    intro a
    simp

/-- A genuine length-one finite free resolution over the concrete irrational rotation algebra.
Both maps are proved left-algebra equivariant; every actual flow vector is retained. -/
theorem rotationInducedFiniteFreeResolution_exact :
    Function.Injective (rotationInducedFreeRelation t B T) ∧
      LinearMap.range (rotationInducedFreeRelation t B T) =
        LinearMap.ker (rotationInducedFreeCover t ht T B) ∧
      Function.Surjective (rotationInducedFreeCover t ht T B) :=
  ⟨rotationInducedFreeRelation_injective t ht B T,
    (rotationInducedFreeCover_ker t ht B T).symm,
    rotationInducedFreeCover_surjective t ht T B⟩

end FreeCoordinates
end
end GaloisForLFunctions.HTGeometry
