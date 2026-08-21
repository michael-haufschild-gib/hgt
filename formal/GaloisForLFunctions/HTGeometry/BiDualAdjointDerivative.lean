import GaloisForLFunctions.HTGeometry.BiDualNumbers
import GaloisForLFunctions.HTGeometry.DifferentialTangentAdjoint

/-!
# The bracket is the derivative of the adjoint action

Over `C[ε, η]/(ε², η²)` the conjugate of `1 + εY` by `1 + ηX` is

`(1 + ηX)(1 + εY)(1 − ηX) = 1 + εY + εη(XY − YX)`,

an exact identity, because `ε² = η² = 0` while `εη` survives.  Both `1 ± ηX` and `1 + εY` are images
of tangent matrices under the two layer inclusions of the dual numbers, and those inclusions are
derivation- and constant-compatible, so a zero set closed under multiplication contains the product.

The commutator therefore appears as the `εη`-coefficient of a member of the zero set: this is the
statement that the Lie algebra of a differential algebraic group is closed under the bracket, before
the coefficient is extracted.

* `biMatrix`, `biMatrix_mul`;
* `etaMatrix_eq`, `epsMatrix_eq`;
* `adjointDerivative_mem_zeroSet`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [CommRing C] [Differential C]

/-- The matrix `a + bε + cη + dεη`. -/
def biMatrix (a b c d : Matrix (Fin 2) (Fin 2) C) : Matrix (Fin 2) (Fin 2) (BiDual C) :=
  fun i j => ⟨a i j, b i j, c i j, d i j⟩

omit [CommRing C] [Differential C] in
@[simp] theorem biMatrix_apply (a b c d : Matrix (Fin 2) (Fin 2) C) (i j : Fin 2) :
    biMatrix a b c d i j = ⟨a i j, b i j, c i j, d i j⟩ := rfl

omit [Differential C] in
/-- **Two independent infinitesimals multiply by the two-parameter first-order rule.** -/
theorem biMatrix_mul (a b c d a' b' c' d' : Matrix (Fin 2) (Fin 2) C) :
    biMatrix a b c d * biMatrix a' b' c' d'
      = biMatrix (a * a') (a * b' + b * a') (a * c' + c * a')
          (a * d' + d * a' + b * c' + c * b') := by
  refine Matrix.ext fun i j => ?_
  refine BiDual.ext ?_ ?_ ?_ ?_ <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_two] <;> ring

omit [Differential C] in
theorem etaMatrix_eq (X : Matrix (Fin 2) (Fin 2) C) :
    (fun i j => BiDual.etaFun (dualMatrix 1 X i j)) = biMatrix 1 0 X 0 := by
  funext i j
  refine BiDual.ext ?_ ?_ ?_ ?_ <;> simp [BiDual.etaFun, dualMatrix]

omit [Differential C] in
theorem epsMatrix_eq (Y : Matrix (Fin 2) (Fin 2) C) :
    (fun i j => BiDual.epsFun (dualMatrix 1 Y i j)) = biMatrix 1 Y 0 0 := by
  funext i j
  refine BiDual.ext ?_ ?_ ?_ ?_ <;> simp [BiDual.epsFun, dualMatrix]

variable (S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C))

/-- **The adjoint derivative.**  If `1 + ηX`, `1 − ηX` and `1 + ηY` lie in the zero set over the
dual numbers, and the zero set is closed under multiplication over `C[ε, η]/(ε², η²)`, then
`1 + εY + εη(XY − YX)` lies in the zero set there: the commutator is the `εη`-coefficient. -/
theorem adjointDerivative_mem_zeroSet
    (hmul : ∀ u ∈ matrixZeroSet (C := C) (A := BiDual C) S,
      ∀ v ∈ matrixZeroSet (C := C) (A := BiDual C) S,
      u * v ∈ matrixZeroSet (C := C) (A := BiDual C) S)
    {X Y : Matrix (Fin 2) (Fin 2) C}
    (hX : dualMatrix 1 X ∈ matrixZeroSet (C := C) (A := DualNumber C) S)
    (hXneg : dualMatrix 1 (-X) ∈ matrixZeroSet (C := C) (A := DualNumber C) S)
    (hY : dualMatrix 1 Y ∈ matrixZeroSet (C := C) (A := DualNumber C) S) :
    biMatrix 1 Y 0 (X * Y - Y * X) ∈ matrixZeroSet (C := C) (A := BiDual C) S := by
  have hetaTransfer : ∀ {g : Matrix (Fin 2) (Fin 2) (DualNumber C)},
      g ∈ matrixZeroSet (C := C) (A := DualNumber C) S →
      (fun i j => BiDual.etaFun (g i j)) ∈ matrixZeroSet (C := C) (A := BiDual C) S := by
    intro g hg
    exact matrixZeroSet_ringHom S (BiDual.etaHom (C := C))
      (fun a => BiDual.deriv_etaHom a) BiDual.etaHom_algebraMap hg
  have hepsTransfer : ∀ {g : Matrix (Fin 2) (Fin 2) (DualNumber C)},
      g ∈ matrixZeroSet (C := C) (A := DualNumber C) S →
      (fun i j => BiDual.epsFun (g i j)) ∈ matrixZeroSet (C := C) (A := BiDual C) S := by
    intro g hg
    exact matrixZeroSet_ringHom S (BiDual.epsHom (C := C))
      (fun a => BiDual.deriv_epsHom a) BiDual.epsHom_algebraMap hg
  have hg : biMatrix (1 : Matrix (Fin 2) (Fin 2) C) 0 X 0
      ∈ matrixZeroSet (C := C) (A := BiDual C) S := by
    rw [← etaMatrix_eq]
    exact hetaTransfer hX
  have hh : biMatrix (1 : Matrix (Fin 2) (Fin 2) C) 0 (-X) 0
      ∈ matrixZeroSet (C := C) (A := BiDual C) S := by
    rw [← etaMatrix_eq]
    exact hetaTransfer hXneg
  have hm : biMatrix (1 : Matrix (Fin 2) (Fin 2) C) Y 0 0
      ∈ matrixZeroSet (C := C) (A := BiDual C) S := by
    rw [← epsMatrix_eq]
    exact hepsTransfer hY
  have hcompute : biMatrix (1 : Matrix (Fin 2) (Fin 2) C) 0 X 0
        * biMatrix (1 : Matrix (Fin 2) (Fin 2) C) Y 0 0
        * biMatrix (1 : Matrix (Fin 2) (Fin 2) C) 0 (-X) 0
      = biMatrix 1 Y 0 (X * Y - Y * X) := by
    rw [biMatrix_mul, biMatrix_mul]
    congr 1 <;> simp [sub_eq_add_neg]
  rw [← hcompute]
  exact hmul _ (hmul _ hg _ hm) _ hh

end

end GaloisForLFunctions.HTGeometry
