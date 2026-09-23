import GaloisForLFunctions.HTGeometry.FiniteBlaschkeAdjointDefect
import GaloisForLFunctions.HTGeometry.FiniteExponentialHankel

open Complex
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Canonical initial-space realization of finite-Blaschke Hardy leakage. -/
def finiteBlaschkeLeakageCore (A B : FiniteBlaschke) :
    HardyDisk →L[ℂ] finiteBlaschkeModelSpace B :=
  (((finiteBlaschkeModelSpace B).starProjection).codRestrict
    (finiteBlaschkeModelSpace B)
    (fun x => (finiteBlaschkeModelSpace B).starProjection_apply_mem x)).comp
      (finiteBlaschkeMul A)

theorem adjoint_finiteBlaschkeLeakageCore_apply (A B : FiniteBlaschke)
    (y : finiteBlaschkeModelSpace B) :
    (finiteBlaschkeLeakageCore A B).adjoint y =
      (finiteBlaschkeMul A).adjoint (y : HardyDisk) := by
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (y : HardyDisk)
      ((finiteBlaschkeModelSpace B).starProjection (finiteBlaschkeMul A x)) =
    inner ℂ (y : HardyDisk) (finiteBlaschkeMul A x)
  let K : Submodule ℂ HardyDisk := finiteBlaschkeModelSpace B
  let z : HardyDisk := finiteBlaschkeMul A x
  have hperp : (inner ℂ (y : HardyDisk) (z - K.starProjection z) : ℂ) = 0 :=
    (K.mem_orthogonal _).1 (K.sub_starProjection_mem_orthogonal z) y y.property
  calc
    inner ℂ (y : HardyDisk) (K.starProjection z) =
        inner ℂ (y : HardyDisk) (K.starProjection z) + 0 := by rw [add_zero]
    _ = inner ℂ (y : HardyDisk) (K.starProjection z) +
        inner ℂ (y : HardyDisk) (z - K.starProjection z) := by rw [hperp]
    _ = inner ℂ (y : HardyDisk) (K.starProjection z +
        (z - K.starProjection z)) := by rw [inner_add_right]
    _ = inner ℂ (y : HardyDisk) z := by congr 1; abel

/-- Coprime numerator and denominator make the canonical leakage core onto the whole model space. -/
theorem finiteBlaschkeLeakageCore_surjective_of_coprime (A B : FiniteBlaschke)
    (hcop : HardyCoprimeWithFiniteBlaschke A.toMultiplier B) :
    Function.Surjective (finiteBlaschkeLeakageCore A B) := by
  have hAinj : Function.Injective
      ((ContinuousLinearMap.adjoint (finiteBlaschkeMul A)).toLinearMap.domRestrict
        (finiteBlaschkeModelSpace B)) := by
    simpa [finiteBlaschkeMul] using
      (adjoint_hardyMul_domRestrict_finiteBlaschkeModelSpace_injective_of_coprime
        A.toMultiplier B hcop)
  have hcoreAdj : Function.Injective (finiteBlaschkeLeakageCore A B).adjoint := by
    intro x y hxy
    apply hAinj
    change (finiteBlaschkeMul A).adjoint (x : HardyDisk) =
      (finiteBlaschkeMul A).adjoint (y : HardyDisk)
    simpa only [adjoint_finiteBlaschkeLeakageCore_apply] using hxy
  have hsurj : Function.Surjective (finiteBlaschkeLeakageCore A B).adjoint.adjoint :=
    adjoint_surjective_of_finiteDimensional_domain_injective
      (finiteBlaschkeLeakageCore A B).adjoint hcoreAdj
  simpa only [ContinuousLinearMap.adjoint_adjoint] using hsurj

/-- Exact finite leakage rank: coprime finite inner quotient has one leakage direction per
denominator zero, counted with multiplicity. -/
theorem finrank_range_finiteBlaschkeLeakageCore_of_coprime (A B : FiniteBlaschke)
    (hcop : HardyCoprimeWithFiniteBlaschke A.toMultiplier B) :
    Module.finrank ℂ (finiteBlaschkeLeakageCore A B).range = B.deg := by
  have hrange : (finiteBlaschkeLeakageCore A B).range = ⊤ :=
    LinearMap.range_eq_top.mpr (finiteBlaschkeLeakageCore_surjective_of_coprime A B hcop)
  calc
    Module.finrank ℂ (finiteBlaschkeLeakageCore A B).range =
        Module.finrank ℂ (finiteBlaschkeModelSpace B) :=
      LinearEquiv.finrank_eq (LinearEquiv.ofTop _ hrange)
    _ = B.deg := finrank_finiteBlaschkeModelSpace B

/-- Leakage-core norm is exactly the anti-causal Schur energy of the inner quotient. -/
theorem norm_sq_finiteBlaschkeLeakageCore (A B : FiniteBlaschke) (f : HardyDisk) :
    ‖finiteBlaschkeLeakageCore A B f‖ ^ (2 : ℕ) =
      ‖f‖ ^ (2 : ℕ) - ‖(finiteBlaschkeMul B).adjoint (finiteBlaschkeMul A f)‖ ^ (2 : ℕ) := by
  have hB := norm_sq_adjoint_finiteBlaschkeMul B (finiteBlaschkeMul A f)
  have hA := norm_finiteBlaschkeMul A f
  change ‖(finiteBlaschkeModelSpace B).starProjection (finiteBlaschkeMul A f)‖ ^ (2 : ℕ) = _
  rw [hA] at hB
  linarith

end GaloisForLFunctions.HTGeometry
