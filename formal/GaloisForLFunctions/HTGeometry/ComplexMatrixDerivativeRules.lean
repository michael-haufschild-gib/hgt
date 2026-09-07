import GaloisForLFunctions.HTGeometry.ComplexCoordinateConnectionBianchi

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry.ComplexCoordinateConnection
open ScalarTwoJet Filter Topology
noncomputable section
variable {d n : ℕ}

/-- Actual entrywise matrix differentiation commutes with transpose. -/
theorem matrixPartial_transpose (M : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (x : Fin d → ℝ) (k : Fin d) :
    matrixPartial (fun y => (M y).transpose) x k = (matrixPartial M x k).transpose := rfl

/-- Matrix differentiation of an actual sum of differentiable fields. -/
theorem matrixPartial_add (M N : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (x : Fin d → ℝ) (hM : ∀ u v, DifferentiableAt ℝ (fun y => M y u v) x)
    (hN : ∀ u v, DifferentiableAt ℝ (fun y => N y u v) x) (k : Fin d) :
    matrixPartial (fun y => M y + N y) x k = matrixPartial M x k + matrixPartial N x k := by
  ext u v
  exact coordDeriv_add (hM u v) (hN u v) k

/-- Matrix differentiation of a difference retains both derivatives. -/
theorem matrixPartial_sub (M N : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (x : Fin d → ℝ) (hM : ∀ u v, DifferentiableAt ℝ (fun y => M y u v) x)
    (hN : ∀ u v, DifferentiableAt ℝ (fun y => N y u v) x) (k : Fin d) :
    matrixPartial (fun y => M y - N y) x k = matrixPartial M x k - matrixPartial N x k := by
  ext u v
  exact coordDeriv_sub (hM u v) (hN u v) k

/-- Noncommutative product rule for actual complex matrix fields on real coordinates. -/
theorem matrixPartial_mul (M N : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (x : Fin d → ℝ) (hM : ∀ u v, DifferentiableAt ℝ (fun y => M y u v) x)
    (hN : ∀ u v, DifferentiableAt ℝ (fun y => N y u v) x) (k : Fin d) :
    matrixPartial (fun y => M y * N y) x k = matrixPartial M x k * N x + M x * matrixPartial N x k := by
  ext u v
  simp only [matrixPartial, Matrix.mul_apply, Matrix.add_apply]
  rw [coordDeriv_sum (s := Finset.univ) (F := fun a y => M y u a * N y a v)
    (fun a _ => (hM u a).mul (hN a v))]
  simp_rw [coordDeriv_mul (hM u _) (hN _ v)]
  exact Finset.sum_add_distrib

/-- Equality on a neighborhood identifies the actual matrix coordinate derivatives. -/
theorem matrixPartial_congr (M N : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (x : Fin d → ℝ) (he : M =ᶠ[𝓝 x] N) (k : Fin d) : matrixPartial M x k = matrixPartial N x k := by
  ext u v
  have hc : (fun y => M y u v) =ᶠ[𝓝 x] (fun y => N y u v) :=
    he.mono (fun _ h => congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A u v) h)
  exact congrArg (fun L : (Fin d → ℝ) →L[ℝ] ℂ => L (Pi.single k (1 : ℝ))) (hc.fderiv_eq (𝕜 := ℝ))

/-- Actual C2 matrix fields have commuting ordered coordinate derivatives. -/
theorem matrixPartial_comm (M : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (x : Fin d → ℝ) (hM : ∀ u v, ContDiffAt ℝ 2 (fun y => M y u v) x) (k i : Fin d) :
    matrixPartial (fun y => matrixPartial M y i) x k = matrixPartial (fun y => matrixPartial M y k) x i := by
  ext u v
  exact coordDeriv_comm (hM u v) k i

end
end GaloisForLFunctions.HTGeometry.ComplexCoordinateConnection
