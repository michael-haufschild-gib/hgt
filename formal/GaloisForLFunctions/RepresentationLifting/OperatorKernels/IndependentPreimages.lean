import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt.CompatibleTowers
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Independent preimages and compatible backward orbits

The algebraic part of Proposition 3.1 of Aznay–Chabbabi–Zariouh,
*Independent Backward Preimages and Algebraic Radial Decompositions of Operators*
(arXiv:2611.06831), separates preimages under individual powers from coherent
backward orbits. Their compatibility defects lie in the corresponding kernels.

In finite dimension, the stable image is the invertible Fitting summand.
Every vector in it has a unique coherent backward orbit, although arbitrary
independent preimages may still differ by elements of the power kernels.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

open ArithmeticHodgeTheoryOfDegenerations.HodgeWitt

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- Preimages of the same initial vector under each power, with no compatibility imposed. -/
def independentPreimages (T : Module.End R M) : Submodule R (ℕ → M) where
  carrier := {x | ∀ n, (T ^ n) (x n) = x 0}
  zero_mem' := fun n => map_zero (T ^ n)
  add_mem' := by
    intro x y hx hy n
    exact (map_add (T ^ n) _ _).trans (congrArg₂ (· + ·) (hx n) (hy n))
  smul_mem' := by
    intro a x hx n
    exact (map_smul (T ^ n) a _).trans (congrArg (a • ·) (hx n))

/-- Vectors divisible by every power of the operator. -/
def stableImage (T : Module.End R M) : Submodule R M :=
  ⨅ n : ℕ, LinearMap.range (T ^ n)

/-- Every compatible orbit supplies independent preimages. -/
theorem backwardOrbits_le_independentPreimages (T : Module.End R M) :
    backwardOrbits T ≤ independentPreimages T := by
  intro x hx n
  simpa only [Nat.zero_add] using backwardOrbits_pow_apply T ⟨x, hx⟩ n 0

/-- The failure of adjacent preimages to match is killed by the earlier power. -/
theorem independentPreimages_defect_mem_ker (T : Module.End R M)
    (x : independentPreimages T) (n : ℕ) :
    T (x.1 (n + 1)) - x.1 n ∈ LinearMap.ker (T ^ n) := by
  rw [LinearMap.mem_ker, map_sub]
  change ((T ^ n) * T) (x.1 (n + 1)) - (T ^ n) (x.1 n) = 0
  rw [← pow_succ, x.2 (n + 1), x.2 n, sub_self]

/-- For an injective operator the kernel defects vanish, so all choices are coherent. -/
theorem independentPreimages_eq_backwardOrbits (T : Module.End R M)
    (hT : Function.Injective T) : independentPreimages T = backwardOrbits T := by
  apply le_antisymm _ (backwardOrbits_le_independentPreimages T)
  intro x hx n
  apply hT.iterate n
  rw [← Module.End.pow_apply, ← Module.End.pow_apply]
  change ((T ^ n) * T) (x (n + 1)) = (T ^ n) (x n)
  rw [← pow_succ, hx (n + 1), hx n]

/-- Evaluation forgets the independent choices and retains their common image. -/
def independentRoot (T : Module.End R M) : independentPreimages T →ₗ[R] M where
  toFun x := x.1 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Independent preimages exist exactly on the intersection of all power images. -/
theorem range_independentRoot (T : Module.End R M) :
    LinearMap.range (independentRoot T) = stableImage T := by
  classical
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact (Submodule.mem_iInf _).mpr fun n => ⟨x.1 n, x.2 n⟩
  · intro hv
    have h : ∀ n, ∃ y, (T ^ n) y = v := (Submodule.mem_iInf _).mp hv
    choose x hx using h
    have hzero : x 0 = v := hx 0
    exact ⟨⟨x, fun n => (hx n).trans hzero.symm⟩, hzero⟩

/-- All ambiguity in independent division is exactly a product of power kernels. -/
def independentRootKernelEquiv (T : Module.End R M) :
    LinearMap.ker (independentRoot T) ≃ₗ[R] (∀ n : ℕ, LinearMap.ker (T ^ n)) where
  toFun x n := ⟨x.1.1 n, by
    change (T ^ n) (x.1.1 n) = 0
    exact (x.1.2 n).trans x.2⟩
  invFun y := ⟨⟨fun n => (y n).1, by
    intro n
    have hzero : (y 0).1 = 0 := (y 0).2
    exact (y n).2.trans hzero.symm⟩, (y 0).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Nilpotence kills even unrelated preimages; no growth or coherence is needed. -/
theorem independentRoot_eq_zero_of_pow_eq_zero (T : Module.End R M)
    (n : ℕ) (hn : T ^ n = 0) (x : independentPreimages T) : x.1 0 = 0 := by
  rw [← x.2 n, hn]
  rfl

/-- The operator preserves its stable image. -/
def stableImageOperator (T : Module.End R M) : Module.End R (stableImage T) where
  toFun x := ⟨T x.1, by
    apply (Submodule.mem_iInf _).mpr
    intro n
    obtain ⟨y, hy⟩ := (Submodule.mem_iInf _).mp x.2 n
    refine ⟨T y, ?_⟩
    change ((T ^ n) * T) y = T x.1
    rw [← pow_succ, pow_succ', Module.End.mul_apply, hy]⟩
  map_add' _ _ := Subtype.ext (map_add T _ _)
  map_smul' _ _ := Subtype.ext (map_smul T _ _)

section FiniteDimensional

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The invertible Fitting summand has no transition torsion. -/
theorem stableImageOperator_injective (T : Module.End K V) :
    Function.Injective (stableImageOperator T) := by
  intro x y h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply (Submodule.disjoint_def.mp
    (T.isCompl_iSup_ker_pow_iInf_range_pow).disjoint) (x.1 - y.1)
  · apply Submodule.mem_iSup_of_mem 1
    change T (x.1 - y.1) = 0
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val h
  · exact (stableImage T).sub_mem x.2 y.2

/-- Restricting to the stable image turns any finite-dimensional operator into an automorphism. -/
def stableImageEquiv (T : Module.End K V) : stableImage T ≃ₗ[K] stableImage T :=
  LinearEquiv.ofBijective (stableImageOperator T)
    ⟨stableImageOperator_injective T,
      LinearMap.injective_iff_surjective.mp (stableImageOperator_injective T)⟩

/-- Coherent backward orbits evaluate into the stable image. -/
def backwardRoot (T : Module.End K V) : backwardOrbits T →ₗ[K] stableImage T where
  toFun x := ⟨x.1 0, backwardOrbits_mem_stableImage T x 0⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- In finite dimension, a coherent backward orbit is uniquely determined by its root. -/
theorem backwardRoot_injective (T : Module.End K V) :
    Function.Injective (backwardRoot T) := by
  intro x y h
  apply Subtype.ext
  funext n
  induction n with
  | zero => exact congrArg Subtype.val h
  | succ n ih =>
      have he := stableImageOperator_injective T
        (a₁ := ⟨x.1 (n + 1), backwardOrbits_mem_stableImage T x (n + 1)⟩)
        (a₂ := ⟨y.1 (n + 1), backwardOrbits_mem_stableImage T y (n + 1)⟩)
      apply congrArg (Subtype.val : stableImage T → V) ∘ he
      apply Subtype.ext
      exact (x.2 n).trans (ih.trans (y.2 n).symm)

/-- Inverting on the Fitting summand constructs a coherent orbit through every stable vector. -/
theorem backwardRoot_surjective (T : Module.End K V) :
    Function.Surjective (backwardRoot T) := by
  intro v
  let x := (backwardOrbitsEquiv (stableImageEquiv T)).symm v
  refine ⟨⟨fun n => (x.1 n).1, fun n => congrArg Subtype.val (x.2 n)⟩, ?_⟩
  exact congrArg (fun z : stableImage T => z)
    ((backwardOrbitsEquiv (stableImageEquiv T)).apply_symm_apply v)

/-- Independent divisibility and coherent divisibility have the same roots in finite dimension. -/
def backwardOrbitsStableImageEquiv (T : Module.End K V) :
    backwardOrbits T ≃ₗ[K] stableImage T :=
  LinearEquiv.ofBijective (backwardRoot T)
    ⟨backwardRoot_injective T, backwardRoot_surjective T⟩

end FiniteDimensional

#print axioms independentPreimages_defect_mem_ker
#print axioms independentPreimages_eq_backwardOrbits
#print axioms range_independentRoot
#print axioms independentRootKernelEquiv
#print axioms independentRoot_eq_zero_of_pow_eq_zero
#print axioms backwardOrbitsStableImageEquiv

end GaloisForLFunctions.RepresentationLifting.OperatorKernels
