import GaloisForLFunctions.HTGeometry.FiniteBlaschkeModelSpaceProduct
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeAdjointDefect

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

namespace FiniteBlaschke

/-- Concatenation of finite Blaschke divisors, retaining every zero and multiplicity. -/
def append (B₀ B₁ : FiniteBlaschke) : FiniteBlaschke where
  deg := B₀.deg + B₁.deg
  zeros := Fin.append B₀.zeros B₁.zeros
  bound := max B₀.bound B₁.bound
  bound_nonneg := le_trans B₀.bound_nonneg (le_max_left _ _)
  bound_lt := max_lt B₀.bound_lt B₁.bound_lt
  zeros_le := by
    intro j
    refine Fin.addCases (motive := fun j =>
      ‖(Fin.append B₀.zeros B₁.zeros) j‖ ≤ max B₀.bound B₁.bound)
      (fun i => ?_) (fun i => ?_) j
    · simpa using le_trans (B₀.zeros_le i) (le_max_left B₀.bound B₁.bound)
    · simpa using le_trans (B₁.zeros_le i) (le_max_right B₀.bound B₁.bound)

@[simp] theorem deg_append (B₀ B₁ : FiniteBlaschke) :
    (append B₀ B₁).deg = B₀.deg + B₁.deg := rfl

theorem fn_append (B₀ B₁ : FiniteBlaschke) (z : ℂ) :
    (append B₀ B₁).fn z = B₀.fn z * B₁.fn z := by
  change (∏ j : Fin (B₀.deg + B₁.deg),
      blaschkeFactor (Fin.append B₀.zeros B₁.zeros j) z) =
    (∏ j : Fin B₀.deg, blaschkeFactor (B₀.zeros j) z) *
      ∏ j : Fin B₁.deg, blaschkeFactor (B₁.zeros j) z
  rw [Fin.prod_univ_add]
  simp [Fin.append]

theorem finiteBlaschkeMul_append (B₀ B₁ : FiniteBlaschke) (x : HardyDisk) :
    finiteBlaschkeMul (append B₀ B₁) x =
      finiteBlaschkeMul B₀ (finiteBlaschkeMul B₁ x) := by
  change hardyMul (append B₀ B₁).toMultiplier x =
    hardyMul B₀.toMultiplier (hardyMul B₁.toMultiplier x)
  calc
    _ = hardyMul (B₀.toMultiplier.mul B₁.toMultiplier) x := by
      apply hardyMul_congr
      intro z _
      exact fn_append B₀ B₁ z
    _ = _ := (hardyMul_mul B₀.toMultiplier B₁.toMultiplier x).symm

theorem finiteBlaschkeModelSpace_append_eq_sup (B₀ B₁ : FiniteBlaschke) :
    finiteBlaschkeModelSpace (append B₀ B₁) =
      finiteBlaschkeModelSpace B₀ ⊔
        (finiteBlaschkeModelSpace B₁).map
          ((finiteBlaschkeMul B₀ : HardyDisk →L[ℂ] HardyDisk) :
            HardyDisk →ₗ[ℂ] HardyDisk) := by
  have hmul : hardyMul (append B₀ B₁).toMultiplier =
      hardyMul (B₀.toMultiplier.mul B₁.toMultiplier) := by
    apply ContinuousLinearMap.ext
    intro x
    apply hardyMul_congr
    intro z _
    exact fn_append B₀ B₁ z
  change hardyMultiplierModelSpace (append B₀ B₁).toMultiplier =
    finiteBlaschkeModelSpace B₀ ⊔
      (finiteBlaschkeModelSpace B₁).map
        ((hardyMul B₀.toMultiplier : HardyDisk →L[ℂ] HardyDisk) :
          HardyDisk →ₗ[ℂ] HardyDisk)
  have hmodel : hardyMultiplierModelSpace (append B₀ B₁).toMultiplier =
      hardyMultiplierModelSpace (B₀.toMultiplier.mul B₁.toMultiplier) := by
    unfold hardyMultiplierModelSpace
    rw [hmul]
  rw [hmodel]
  exact hardyMultiplierModelSpace_mul_finiteBlaschke_eq_sup B₀ B₁

end FiniteBlaschke

end GaloisForLFunctions.HTGeometry
