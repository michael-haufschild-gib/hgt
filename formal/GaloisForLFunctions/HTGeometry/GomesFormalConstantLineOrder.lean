import GaloisForLFunctions.HTGeometry.GomesEvenOddFormalMatrix

/-!
# The exact formal matrix algebra that preserves the constant polynomial line

In the two-chain model, preservation of constants imposes one condition: the
lower-left formal entry has zero constant coefficient. This is a subalgebra over
the entire scalar formal-series center, and its entries have an exact four-term
form with the lower-left entry divisible by the formal variable.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K]

/-- Formal matrices whose lower-left entry vanishes at the formal origin. -/
def gomesFormalConstantLineOrder : Subalgebra (PowerSeries K)
    (Matrix (Fin 2) (Fin 2) (PowerSeries K)) where
  carrier := {M | PowerSeries.constantCoeff (M 1 0) = 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {A B} hA hB := by
    change PowerSeries.constantCoeff (A 1 0 + B 1 0) = 0
    rw [map_add, hA, hB, add_zero]
  mul_mem' {A B} hA hB := by
    change PowerSeries.constantCoeff ((A * B) 1 0) = 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, map_mul, hA, hB,
      zero_mul, mul_zero, add_zero]
  algebraMap_mem' F := by simp [Matrix.algebraMap_matrix_apply]

/-- Membership is exactly the one scalar observation on the lower-left entry. -/
theorem gomesFormalConstantLineOrder_mem_iff (M : Matrix (Fin 2) (Fin 2) (PowerSeries K)) :
    M ∈ gomesFormalConstantLineOrder K ↔ PowerSeries.constantCoeff (M 1 0) = 0 := Iff.rfl

/-- The scalar observation is equivalent to divisibility by the formal variable. -/
theorem gomesFormalConstantLineOrder_mem_iff_X_dvd (M : Matrix (Fin 2) (Fin 2) (PowerSeries K)) :
    M ∈ gomesFormalConstantLineOrder K ↔ (PowerSeries.X : PowerSeries K) ∣ M 1 0 := by
  rw [gomesFormalConstantLineOrder_mem_iff, PowerSeries.X_dvd_iff]

/-- Every allowed matrix has exactly one formal-variable factor in its lower-left parametrization. -/
theorem gomesFormalConstantLineOrder_mem_iff_matrix
    (M : Matrix (Fin 2) (Fin 2) (PowerSeries K)) :
    M ∈ gomesFormalConstantLineOrder K ↔
      ∃ a b c d : PowerSeries K, M = !![a, b; PowerSeries.X * c, d] := by
  rw [gomesFormalConstantLineOrder_mem_iff_X_dvd]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨M 0 0, M 0 1, c, M 1 1, ?_⟩
    apply Matrix.ext
    intro i j
    revert i j
    simp [Fin.forall_fin_two, hc]
  · rintro ⟨a, b, c, d, rfl⟩
    exact ⟨c, rfl⟩

/-- The unscaled even-to-odd transfer violates the exact boundary. -/
theorem gomesFormalConstantLineOrder_lowerTransfer_not_mem :
    ( !![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (PowerSeries K)) ∉ gomesFormalConstantLineOrder K := by
  rw [gomesFormalConstantLineOrder_mem_iff]
  simp

/-- The constant-line algebra is a proper part of the full two-chain matrix algebra. -/
theorem gomesFormalConstantLineOrder_ne_top : gomesFormalConstantLineOrder K ≠ ⊤ := by
  intro h
  apply gomesFormalConstantLineOrder_lowerTransfer_not_mem K
  rw [h]
  trivial

end GaloisForLFunctions.HTGeometry
