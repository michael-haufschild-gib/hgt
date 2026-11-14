import GaloisForLFunctions.EisensteinDegeneration.MatrixRegularity
import GaloisForLFunctions.HTGeometry.MatrixSemicircleDysonFormalBranch

/-!
# Pole detection by the formal matrix Dyson branch

The existing rescaled Dyson solution specializes to the identity matrix.
It therefore preserves the boundary vector and reflects divisibility by
every parameter power. The full vector regulator detects all finite poles,
even when particular scalar coordinates have additional cancellation.
-/

namespace GaloisForLFunctions.HTGeometry
open Matrix PowerSeries EisensteinDegeneration
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

private theorem matrixDysonFormalSeries_reduction (A : J → Matrix I I ℂ) :
    (matrixDysonFormalSeries A).map constantCoeff = 1 := by
  apply Matrix.ext
  intro i j
  change constantCoeff (matrixDysonFormalSeries A i j) = _
  rw [← coeff_zero_eq_constantCoeff, coeff_matrixDysonFormalSeries, matrixDysonFormalCoeff]

/-- The formal Dyson branch preserves the full boundary vector. Individual coordinates
may still vanish, but the complete vector loses no specialization data. -/
theorem matrixDysonFormalSeries_boundary (A : J → Matrix I I ℂ)
    (f : I → PowerSeries ℂ) :
    (fun i => constantCoeff ((matrixDysonFormalSeries A *ᵥ f) i)) =
      fun i => constantCoeff (f i) := by
  rw [matrix_mulVec_constantCoeff, matrixDysonFormalSeries_reduction, Matrix.one_mulVec]

/-- Every parameter-divisibility condition is preserved and reflected by the actual
formal matrix Dyson branch. -/
theorem matrixDysonFormalSeries_divisibility (A : J → Matrix I I ℂ)
    (m : ℕ) (f : I → PowerSeries ℂ) :
    (∀ i, X ^ m ∣ (matrixDysonFormalSeries A *ᵥ f) i) ↔ ∀ i, X ^ m ∣ f i := by
  apply (matrix_specialization_injective_iff _).mp ?_ m f
  rw [matrixDysonFormalSeries_reduction]
  intro x y h
  simpa only [Matrix.one_mulVec] using h

/-- The rescaled Dyson branch detects every finite Laurent pole without an analytic
convergence, positivity, or self-adjointness assumption. -/
theorem matrixDysonFormalSeries_detects_regular (A : J → Matrix I I ℂ)
    (m : ℕ) (f : I → PowerSeries ℂ) :
    (∀ i, Regular (HahnSeries.single (-(m : ℤ)) (1 : ℂ) *
      (((matrixDysonFormalSeries A *ᵥ f) i : PowerSeries ℂ) : LaurentSeries ℂ))) ↔
    ∀ i, Regular (HahnSeries.single (-(m : ℤ)) (1 : ℂ) *
      ((f i : PowerSeries ℂ) : LaurentSeries ℂ)) := by
  simpa only [regular_shift_iff] using matrixDysonFormalSeries_divisibility A m f

/-- No integral vector is lost under the formal Dyson action. -/
theorem matrixDysonFormalSeries_mulVec_injective (A : J → Matrix I I ℂ) :
    Function.Injective (matrixDysonFormalSeries A).mulVec := by
  intro f g h
  have hz : matrixDysonFormalSeries A *ᵥ (f - g) = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  have hd (m : ℕ) : ∀ i, X ^ m ∣ (f - g) i :=
    (matrixDysonFormalSeries_divisibility A m (f - g)).mp (by simp [hz])
  funext i
  apply PowerSeries.ext
  intro n
  have hc := PowerSeries.X_pow_dvd_iff.mp (hd (n + 1) i) n (Nat.lt_succ_self n)
  simpa only [Pi.sub_apply, map_sub, sub_eq_zero] using hc

end
end GaloisForLFunctions.HTGeometry
