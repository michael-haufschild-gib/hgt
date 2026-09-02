import GaloisForLFunctions.HTGeometry.FreeDifferentialClockShearOrbit
import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveInterleavingMetricSpace

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace DifferentialFieldAut

variable {C : Type u} [Field C] [CharZero C]

/-- Integer orbit of the standard projective point under the actual clock-shear action. -/
def freeClockShearProjectiveOrbitPoint (z : ℤ) :
    DiffOp.DifferentialVariationalProjectiveBuildingCarrier
      (JetField C (Fin 2)) (Fin 2) :=
  (freeClockShear (C := C) ^ z).projectiveBuildingAction
    (freeVariationalOreBasis (C := C) (r := 2))
    (freeClockShearProjectiveBasePoint (C := C))

theorem projectiveInterleavingDistance_base_freeClockShearProjectiveOrbitPoint
    (z : ℤ) :
    DiffOp.differentialVariationalProjectiveInterleavingDistance
        (freeClockShearProjectiveBasePoint (C := C))
        (freeClockShearProjectiveOrbitPoint (C := C) z) = z.natAbs := by
  cases z with
  | ofNat n =>
      exact projectiveInterleavingDistance_freeClockShear_pow_basePoint n
  | negSucc n =>
      let σ := freeClockShear (C := C)
      let b := freeVariationalOreBasis (C := C) (r := 2)
      let x := freeClockShearProjectiveBasePoint (C := C)
      have hIso := projectiveBuildingAction_interleavingDistance
        (σ ^ (n + 1)) b x
        ((σ⁻¹ ^ (n + 1)).projectiveBuildingAction b x)
      have hcancel :
          (σ ^ (n + 1)).projectiveBuildingAction b
              ((σ⁻¹ ^ (n + 1)).projectiveBuildingAction b x) = x := by
        rw [← projectiveBuildingAction_mul, inv_pow, inv_mul_cancel,
          projectiveBuildingAction_one]
      rw [hcancel,
        DiffOp.differentialVariationalProjectiveInterleavingDistance_comm] at hIso
      simpa [freeClockShearProjectiveOrbitPoint, σ, b, x] using hIso.symm.trans
        (projectiveInterleavingDistance_freeClockShear_pow_basePoint (C := C) (n + 1))

theorem projectiveInterleavingDistance_freeClockShearProjectiveOrbitPoint
    (m n : ℤ) :
    DiffOp.differentialVariationalProjectiveInterleavingDistance
        (freeClockShearProjectiveOrbitPoint (C := C) m)
        (freeClockShearProjectiveOrbitPoint (C := C) n) =
      (n - m).natAbs := by
  let σ := freeClockShear (C := C)
  let b := freeVariationalOreBasis (C := C) (r := 2)
  let x := freeClockShearProjectiveBasePoint (C := C)
  have hIso := projectiveBuildingAction_interleavingDistance
    (σ ^ (-m)) b
    (freeClockShearProjectiveOrbitPoint (C := C) m)
    (freeClockShearProjectiveOrbitPoint (C := C) n)
  have hm :
      (σ ^ (-m)).projectiveBuildingAction b
          (freeClockShearProjectiveOrbitPoint (C := C) m) = x := by
    simp only [σ, b, x]
    rw [freeClockShearProjectiveOrbitPoint, ← projectiveBuildingAction_mul,
      ← zpow_add, add_neg_cancel, zpow_zero, projectiveBuildingAction_one]
  have hn :
      (σ ^ (-m)).projectiveBuildingAction b
          (freeClockShearProjectiveOrbitPoint (C := C) n) =
        freeClockShearProjectiveOrbitPoint (C := C) (n - m) := by
    simp only [σ, b]
    rw [freeClockShearProjectiveOrbitPoint, ← projectiveBuildingAction_mul,
      ← zpow_add]
    congr 2
  rw [hm, hn] at hIso
  exact hIso.symm.trans
    (projectiveInterleavingDistance_base_freeClockShearProjectiveOrbitPoint (C := C) (n - m))

/-- The actual clock-shear orbit is an isometric embedding of the integer line. -/
theorem freeClockShearProjectiveOrbitPoint_isometry :
    Isometry (freeClockShearProjectiveOrbitPoint (C := C)) := by
  rw [isometry_iff_dist_eq]
  intro m n
  rw [DiffOp.dist_eq_differentialVariationalProjectiveInterleavingDistance,
    projectiveInterleavingDistance_freeClockShearProjectiveOrbitPoint,
    Int.dist_eq]
  calc
    ((n - m).natAbs : ℝ) =
        ((((n - m).natAbs : ℕ) : ℤ) : ℝ) := by norm_num
    _ = ((|n - m| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
    _ = ((|m - n| : ℤ) : ℝ) := by rw [abs_sub_comm]
    _ = |(m : ℝ) - (n : ℝ)| := by rw [Int.cast_abs, Int.cast_sub]

end DifferentialFieldAut

end

end GaloisForLFunctions.HTGeometry
