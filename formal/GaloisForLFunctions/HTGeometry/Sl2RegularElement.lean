import GaloisForLFunctions.HTGeometry.CassidySl2Graded

/-!
# A spanning subspace contains a regular element

The determinant is a quadratic form on `2 × 2` matrices.  If it vanishes on a `k`-subspace `L`, then
its polarisation vanishes on `L` as well — because `L` is closed under addition — and therefore the
determinant vanishes on the whole `U`-span of `L`.  A subspace whose `U`-span contains a matrix of
nonzero determinant must consequently contain one itself.

This is the first step of Cassidy's reduction: a Zariski-dense subalgebra of `sl₂(U)` contains a
regular semisimple element, which is what a conjugation to the diagonal starts from.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {U : Type*} [Field U]

/-- The polarisation of the determinant on `2 × 2` matrices. -/
def detPolar (X Y : Matrix (Fin 2) (Fin 2) U) : U :=
  X 0 0 * Y 1 1 + Y 0 0 * X 1 1 - X 0 1 * Y 1 0 - Y 0 1 * X 1 0

theorem det_add_detPolar (X Y : Matrix (Fin 2) (Fin 2) U) :
    (X + Y).det = X.det + Y.det + detPolar X Y := by
  simp only [Matrix.det_fin_two, detPolar, Matrix.add_apply]
  ring

theorem detPolar_comm (X Y : Matrix (Fin 2) (Fin 2) U) : detPolar X Y = detPolar Y X := by
  simp only [detPolar]
  ring

theorem detPolar_zero_left (Y : Matrix (Fin 2) (Fin 2) U) : detPolar 0 Y = 0 := by
  simp [detPolar]

theorem detPolar_add_left (X Y Z : Matrix (Fin 2) (Fin 2) U) :
    detPolar (X + Y) Z = detPolar X Z + detPolar Y Z := by
  simp only [detPolar, Matrix.add_apply]
  ring

theorem detPolar_smul_left (u : U) (X Y : Matrix (Fin 2) (Fin 2) U) :
    detPolar (u • X) Y = u * detPolar X Y := by
  simp only [detPolar, Matrix.smul_apply, smul_eq_mul]
  ring

theorem det_smul_two (u : U) (X : Matrix (Fin 2) (Fin 2) U) :
    (u • X).det = u ^ (2 : ℕ) * X.det := by
  simp only [Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **A subspace whose span contains a nondegenerate matrix contains one itself.** -/
theorem exists_det_ne_zero_of_mem_span
    {k : Type*} [Field k] [Algebra k U]
    (L : Submodule k (Matrix (Fin 2) (Fin 2) U))
    {Z : Matrix (Fin 2) (Fin 2) U}
    (hZ : Z ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)))
    (hZdet : Z.det ≠ 0) :
    ∃ X ∈ L, X.det ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hpolarL : ∀ X ∈ L, ∀ Y ∈ L, detPolar X Y = 0 := by
    intro X hX Y hY
    have hsum := hcon (X + Y) (L.add_mem hX hY)
    rw [det_add_detPolar, hcon X hX, hcon Y hY] at hsum
    simpa using hsum
  have hpolarSpan : ∀ Z' ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)),
      ∀ Y ∈ L, detPolar Z' Y = 0 := by
    intro Z' hZ'
    induction hZ' using Submodule.span_induction with
    | mem X hX => exact fun Y hY => hpolarL X hX Y hY
    | zero => exact fun Y _ => detPolar_zero_left Y
    | add A B _ _ hA hB =>
        exact fun Y hY => by rw [detPolar_add_left, hA Y hY, hB Y hY, add_zero]
    | smul u A _ hA => exact fun Y hY => by rw [detPolar_smul_left, hA Y hY, mul_zero]
  have hpolarBoth : ∀ Z' ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)),
      ∀ W ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)), detPolar Z' W = 0 := by
    intro Z' hZ' W hW
    induction hW using Submodule.span_induction with
    | mem Y hY => exact hpolarSpan Z' hZ' Y hY
    | zero => rw [detPolar_comm, detPolar_zero_left]
    | add A B _ _ hA hB => rw [detPolar_comm, detPolar_add_left, detPolar_comm A Z',
        detPolar_comm B Z', hA, hB, add_zero]
    | smul u A _ hA => rw [detPolar_comm, detPolar_smul_left, detPolar_comm A Z', hA, mul_zero]
  have hdetSpan : ∀ Z' ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)), Z'.det = 0 := by
    intro Z' hZ'
    induction hZ' using Submodule.span_induction with
    | mem X hX => exact hcon X hX
    | zero => simp
    | add A B hA' hB' hA hB =>
        rw [det_add_detPolar, hA, hB, hpolarBoth A hA' B hB']
        simp
    | smul u A _ hA => rw [det_smul_two, hA, mul_zero]
  exact hZdet (hdetSpan Z hZ)

end

end GaloisForLFunctions.HTGeometry
