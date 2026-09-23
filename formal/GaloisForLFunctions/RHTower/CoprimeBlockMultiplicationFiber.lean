import GaloisForLFunctions.RHTower.CoprimeBlockCarryTransgression

/-!
# Coprime block multiplication fibres

The dyadic and triadic deletion blocks form a `2 × 3` signed grid.  Every row and every column has
zero mass.  Multiplication is nevertheless noninjective on this grid: `(1, 2)` and `(2, 1)` land
in the same fibre with opposite weights.

The exact finite capstone records source data invisible to all row/column marginals.  The fibrewise
positive/negative masses retain one literal cancellation before signed aggregation.  Separately,
the squared integer mass is `12` before multiplication collapse and `10` afterwards, so the
collision cancellation defect is exactly `2`.  This is finite arithmetic, not a positivity
criterion or an analytic estimate.
-/

namespace RHTower

open scoped BigOperators

/-- Literal signed source on the `2 × 3` deletion grid. -/
def coprimeDeletionGridWeight (x : Fin 2 × Fin 3) : ℤ :=
  blockDeletionCoefficient 2 (x.1.val + 1) *
    blockDeletionCoefficient 3 (x.2.val + 1)

/-- Multiplication label of one grid cell. -/
def coprimeDeletionGridProduct (x : Fin 2 × Fin 3) : Fin 7 :=
  ⟨(x.1.val + 1) * (x.2.val + 1), by
    have hi : x.1.val + 1 ≤ 2 := x.1.isLt
    have hj : x.2.val + 1 ≤ 3 := x.2.isLt
    calc
      (x.1.val + 1) * (x.2.val + 1) ≤ 2 * 3 := Nat.mul_le_mul hi hj
      _ < 7 := by norm_num⟩

/-- Signed coefficient remaining in one multiplication fibre. -/
def coprimeDeletionProductFiberCoefficient (k : Fin 7) : ℤ :=
  ∑ x : Fin 2 × Fin 3,
    if coprimeDeletionGridProduct x = k then coprimeDeletionGridWeight x else 0

/-- Explicit residual coefficient table after multiplication collapse. -/
def coprimeDeletionProductFiberExpected (k : Fin 7) : ℤ :=
  match k.val with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => -2
  | 4 => -1
  | 5 => 0
  | _ => 2

/-- Positive source mass entering one multiplication fibre, before signed aggregation. -/
def coprimeDeletionProductFiberPositiveMass (k : Fin 7) : ℕ :=
  ∑ x : Fin 2 × Fin 3,
    if coprimeDeletionGridProduct x = k then (coprimeDeletionGridWeight x).toNat else 0

/-- Negative source mass entering one multiplication fibre, before signed aggregation. -/
def coprimeDeletionProductFiberNegativeMass (k : Fin 7) : ℕ :=
  ∑ x : Fin 2 × Fin 3,
    if coprimeDeletionGridProduct x = k then (-coprimeDeletionGridWeight x).toNat else 0

/-- Least number of opposite-sign unit cancellations forced inside one product fibre. -/
def coprimeDeletionProductFiberCancellation (k : Fin 7) : ℕ :=
  min (coprimeDeletionProductFiberPositiveMass k)
    (coprimeDeletionProductFiberNegativeMass k)

/-- Explicit cancellation-odometer table: only the product-`2` fibre fires. -/
def coprimeDeletionProductFiberCancellationExpected (k : Fin 7) : ℕ :=
  if k.val = 2 then 1 else 0

/-- Total least-action cancellation count over multiplication fibres. -/
def coprimeDeletionProductFiberTotalCancellation : ℕ :=
  ∑ k : Fin 7, coprimeDeletionProductFiberCancellation k

/-- Squared integer mass before multiplication fibres are identified. -/
def coprimeDeletionGridSquareMass : ℤ :=
  ∑ x : Fin 2 × Fin 3, coprimeDeletionGridWeight x ^ (2 : ℕ)

/-- Squared integer mass after equal products are identified and signed weights are added. -/
def coprimeDeletionProductFiberSquareMass : ℤ :=
  ∑ k : Fin 7, coprimeDeletionProductFiberCoefficient k ^ (2 : ℕ)

/-- Square-mass removed by signed cancellation inside multiplication fibres. -/
def coprimeDeletionMultiplicationCollisionDefect : ℤ :=
  coprimeDeletionGridSquareMass - coprimeDeletionProductFiberSquareMass

/-- Every row of the literal deletion grid has zero mass. -/
theorem coprimeDeletionGrid_rowSum_eq_zero (i : Fin 2) :
    ∑ j : Fin 3, coprimeDeletionGridWeight (i, j) = 0 := by
  fin_cases i <;>
    norm_num [coprimeDeletionGridWeight, blockDeletionCoefficient, Fin.sum_univ_succ]

/-- Every column of the literal deletion grid has zero mass. -/
theorem coprimeDeletionGrid_columnSum_eq_zero (j : Fin 3) :
    ∑ i : Fin 2, coprimeDeletionGridWeight (i, j) = 0 := by
  fin_cases j <;>
    norm_num [coprimeDeletionGridWeight, blockDeletionCoefficient, Fin.sum_univ_succ]

/-- The unique first nontrivial product collision cancels exactly. -/
theorem coprimeDeletionProductFiberCoefficient_two_eq_zero :
    coprimeDeletionProductFiberCoefficient ⟨2, by omega⟩ = 0 := by
  norm_num [coprimeDeletionProductFiberCoefficient, coprimeDeletionGridProduct,
    coprimeDeletionGridWeight, blockDeletionCoefficient, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

/- Complete multiplication-fibre coefficient classification for the six-cell grid. -/
set_option maxRecDepth 10000 in
theorem coprimeDeletionProductFiberCoefficient_eq_expected (k : Fin 7) :
    coprimeDeletionProductFiberCoefficient k =
      coprimeDeletionProductFiberExpected k := by
  fin_cases k <;>
    norm_num [coprimeDeletionProductFiberCoefficient,
      coprimeDeletionProductFiberExpected, coprimeDeletionGridProduct,
      coprimeDeletionGridWeight, blockDeletionCoefficient, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Fin.mk.injEq]

/- Complete cancellation-odometer classification for the six-cell grid. -/
set_option maxRecDepth 10000 in
theorem coprimeDeletionProductFiberCancellation_eq_expected (k : Fin 7) :
    coprimeDeletionProductFiberCancellation k =
      coprimeDeletionProductFiberCancellationExpected k := by
  fin_cases k <;>
    norm_num [coprimeDeletionProductFiberCancellation,
      coprimeDeletionProductFiberCancellationExpected,
      coprimeDeletionProductFiberPositiveMass,
      coprimeDeletionProductFiberNegativeMass, coprimeDeletionGridProduct,
      coprimeDeletionGridWeight, blockDeletionCoefficient, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Fin.mk.injEq]
  all_goals rfl

/-- Exactly one opposite-sign unit pair cancels before signed fibre aggregation. -/
theorem coprimeDeletionProductFiberTotalCancellation_eq_one :
    coprimeDeletionProductFiberTotalCancellation = 1 := by
  rw [coprimeDeletionProductFiberTotalCancellation]
  simp_rw [coprimeDeletionProductFiberCancellation_eq_expected]
  norm_num [coprimeDeletionProductFiberCancellationExpected, Fin.sum_univ_succ]
  all_goals
    have htwo : ({k | (k : ℕ) = 2} : Finset (Fin 7)) = {⟨2, by omega⟩} := by
      ext k
      fin_cases k <;> simp
    rw [htwo]
    simp

/-- Exact pre-collapse square mass. -/
theorem coprimeDeletionGridSquareMass_eq_twelve :
    coprimeDeletionGridSquareMass = 12 := by
  norm_num [coprimeDeletionGridSquareMass, coprimeDeletionGridWeight,
    blockDeletionCoefficient, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Exact post-collapse square mass. -/
theorem coprimeDeletionProductFiberSquareMass_eq_ten :
    coprimeDeletionProductFiberSquareMass = 10 := by
  rw [coprimeDeletionProductFiberSquareMass]
  simp_rw [coprimeDeletionProductFiberCoefficient_eq_expected]
  norm_num [coprimeDeletionProductFiberExpected, Fin.sum_univ_succ]

/-- Multiplication-fibre cancellation removes exactly two units of square mass. -/
theorem coprimeDeletionMultiplicationCollisionDefect_eq_two :
    coprimeDeletionMultiplicationCollisionDefect = 2 := by
  rw [coprimeDeletionMultiplicationCollisionDefect,
    coprimeDeletionGridSquareMass_eq_twelve,
    coprimeDeletionProductFiberSquareMass_eq_ten]
  norm_num

/--
Closed finite capstone: all linear marginals vanish, the source-retaining odometer records one
unit cancellation, one multiplication fibre cancels after aggregation, and the nonlinear collision
defect remains nonzero.
-/
theorem coprimeBlockMultiplicationFiber_closed :
    (∀ i : Fin 2, ∑ j : Fin 3, coprimeDeletionGridWeight (i, j) = 0) ∧
    (∀ j : Fin 3, ∑ i : Fin 2, coprimeDeletionGridWeight (i, j) = 0) ∧
    coprimeDeletionProductFiberCancellation ⟨2, by omega⟩ = 1 ∧
    coprimeDeletionProductFiberTotalCancellation = 1 ∧
    coprimeDeletionProductFiberCoefficient ⟨2, by omega⟩ = 0 ∧
    coprimeDeletionGridSquareMass = 12 ∧
    coprimeDeletionProductFiberSquareMass = 10 ∧
    coprimeDeletionMultiplicationCollisionDefect = 2 ∧
    coprimeDeletionMultiplicationCollisionDefect ≠ 0 := by
  exact ⟨coprimeDeletionGrid_rowSum_eq_zero,
    coprimeDeletionGrid_columnSum_eq_zero,
    coprimeDeletionProductFiberCancellation_eq_expected ⟨2, by omega⟩,
    coprimeDeletionProductFiberTotalCancellation_eq_one,
    coprimeDeletionProductFiberCoefficient_two_eq_zero,
    coprimeDeletionGridSquareMass_eq_twelve,
    coprimeDeletionProductFiberSquareMass_eq_ten,
    coprimeDeletionMultiplicationCollisionDefect_eq_two,
    coprimeDeletionMultiplicationCollisionDefect_eq_two ▸ by norm_num⟩

end RHTower
