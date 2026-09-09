import GaloisForLFunctions.HTGeometry.CoordinateMetricPathDensity

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry.MetricPathDensity
noncomputable section
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

private theorem determinantSlope_add_smul (G H N : Mat) (z : ℂ) :
    determinantSlope G (H + z • N) = determinantSlope G H + z * determinantSlope G N := by
  simp [determinantSlope, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    mul_left_comm]

/-- The full volume-and-index variation is linear in the metric perturbation. -/
theorem testWeightSlope_add_smul (G H N M : Mat) (z : ℂ) :
    testWeightSlope G (H + z • N) M = testWeightSlope G H M + z • testWeightSlope G N M := by
  unfold testWeightSlope
  rw [determinantSlope_add_smul, add_div, mul_div_assoc, add_smul, mul_smul]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.transpose_add, Matrix.transpose_smul]
  module

/-- The actual mode derivative of the testing-weight variation retains only the first mode slot. -/
theorem testWeightSlope_path_hasDerivAt (G A B C D M : Mat) (i j : Fin d) :
    HasDerivAt (fun z => testWeightSlope G (path A B C D z) M i j)
      (testWeightSlope G B M i j) 0 := by
  have he : (fun z => testWeightSlope G (path A B C D z) M i j) =
      fun z : ℂ => testWeightSlope G A M i j + z * testWeightSlope G B M i j +
        z^2 * testWeightSlope G C M i j + z^3 * testWeightSlope G D M i j := by
    funext z
    simp only [path, testWeightSlope_add_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [he]
  have hd := ((((hasDerivAt_id (0 : ℂ)).mul_const (testWeightSlope G B M i j)).const_add
    (testWeightSlope G A M i j)).add
    ((hasDerivAt_pow 2 (0 : ℂ)).mul_const (testWeightSlope G C M i j))).add
    ((hasDerivAt_pow 3 (0 : ℂ)).mul_const (testWeightSlope G D M i j))
  convert! hd using 1
  simp

end
end GaloisForLFunctions.HTGeometry.MetricPathDensity
