import GaloisForLFunctions.HTGeometry.GomesPolynomialDerivativePowerCommutant
import GaloisForLFunctions.HTGeometry.GomesFormalSeriesOperatorAlgebra

/-!
# Explicit symmetries transferring derivative residue chains

Elementary formal matrices reconstruct actual polynomial operators. Their matrix-unit
laws expose nonzero nilpotent symmetries and the precise positive-order commutativity boundary.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]
variable (m : ℕ) [NeZero m]

/-- The actual symmetry transferring residue chain j into residue chain i. -/
def gomesDerivativePowerChainTransfer (i j : Fin m) : GomesPolynomialDerivativePowerCommutant K m :=
  (gomesPolynomialDerivativePowerCommutantEquiv K m).symm (Matrix.single i j 1)

/-- Each chain transfer has exactly its prescribed elementary formal matrix. -/
theorem gomesDerivativePowerChainTransfer_matrix (i j : Fin m) :
    gomesPolynomialDerivativePowerCommutantEquiv K m (gomesDerivativePowerChainTransfer K m i j) =
      Matrix.single i j 1 :=
  (gomesPolynomialDerivativePowerCommutantEquiv K m).apply_symm_apply _

/-- Matching residue-chain transfers compose to the direct transfer. -/
theorem gomesDerivativePowerChainTransfer_mul_same (i j k : Fin m) :
    gomesDerivativePowerChainTransfer K m i j * gomesDerivativePowerChainTransfer K m j k =
      gomesDerivativePowerChainTransfer K m i k := by
  apply (gomesPolynomialDerivativePowerCommutantEquiv K m).injective
  simp only [map_mul, gomesDerivativePowerChainTransfer_matrix, Matrix.single_mul_single_same, one_mul]

/-- The complete matrix-unit multiplication rule holds for the actual reconstructed operators. -/
theorem gomesDerivativePowerChainTransfer_mul (i j k l : Fin m) :
    gomesDerivativePowerChainTransfer K m i j * gomesDerivativePowerChainTransfer K m k l =
      if j = k then gomesDerivativePowerChainTransfer K m i l else 0 := by
  by_cases h : j = k
  · subst k
    simp only [ite_true, gomesDerivativePowerChainTransfer_mul_same]
  · rw [if_neg h]
    apply (gomesPolynomialDerivativePowerCommutantEquiv K m).injective
    simp only [map_mul, map_zero, gomesDerivativePowerChainTransfer_matrix,
      Matrix.single_mul_single_of_ne _ _ _ _ h]

/-- No elementary residue-chain transfer vanishes. -/
theorem gomesDerivativePowerChainTransfer_ne_zero (i j : Fin m) :
    gomesDerivativePowerChainTransfer K m i j ≠ 0 := by
  intro h
  have hm := congrArg (gomesPolynomialDerivativePowerCommutantEquiv K m) h
  rw [gomesDerivativePowerChainTransfer_matrix, map_zero] at hm
  have hc := congrArg (fun M : Matrix (Fin m) (Fin m) (PowerSeries K) => M i j) hm
  exact one_ne_zero (by simpa only [Matrix.single_apply_same, Matrix.zero_apply] using hc)

/-- Each residue-chain projection is idempotent. -/
theorem gomesDerivativePowerChainTransfer_idempotent (i : Fin m) :
    gomesDerivativePowerChainTransfer K m i i * gomesDerivativePowerChainTransfer K m i i =
      gomesDerivativePowerChainTransfer K m i i :=
  gomesDerivativePowerChainTransfer_mul_same K m i i i

/-- Exactly the transfers between different residue chains square to zero. -/
theorem gomesDerivativePowerChainTransfer_square_zero_iff (i j : Fin m) :
    gomesDerivativePowerChainTransfer K m i j * gomesDerivativePowerChainTransfer K m i j = 0 ↔
      i ≠ j := by
  constructor
  · intro h hij
    subst j
    rw [gomesDerivativePowerChainTransfer_idempotent] at h
    exact gomesDerivativePowerChainTransfer_ne_zero K m i i h
  · intro h
    rw [gomesDerivativePowerChainTransfer_mul, if_neg (Ne.symm h)]

/-- Opposite residue-chain transfers commute precisely when they coincide as one projection. -/
theorem gomesDerivativePowerChainTransfer_opposite_commute_iff (i j : Fin m) :
    gomesDerivativePowerChainTransfer K m i j * gomesDerivativePowerChainTransfer K m j i =
      gomesDerivativePowerChainTransfer K m j i * gomesDerivativePowerChainTransfer K m i j ↔
        i = j := by
  constructor
  · intro h
    by_contra hij
    rw [gomesDerivativePowerChainTransfer_mul_same, gomesDerivativePowerChainTransfer_mul_same] at h
    have hm := congrArg (gomesPolynomialDerivativePowerCommutantEquiv K m) h
    rw [gomesDerivativePowerChainTransfer_matrix, gomesDerivativePowerChainTransfer_matrix] at hm
    have hc := congrArg (fun M : Matrix (Fin m) (Fin m) (PowerSeries K) => M i i) hm
    exact one_ne_zero (by simpa only [Matrix.single_apply_same,
      Matrix.single_apply_of_row_ne (Ne.symm hij)] using hc)
  · rintro rfl
    rfl

/-- Among positive derivative orders, only the first derivative has a commutative full symmetry algebra. -/
theorem gomesPolynomialDerivativePowerCommutant_commutative_iff :
    (∀ E F : GomesPolynomialDerivativePowerCommutant K m, E * F = F * E) ↔ m = 1 := by
  constructor
  · intro h
    by_contra hm
    have hgreater : 1 < m := lt_of_le_of_ne (Nat.pos_of_neZero m) (Ne.symm hm)
    let i : Fin m := ⟨0, Nat.pos_of_neZero m⟩
    let j : Fin m := ⟨1, hgreater⟩
    have hij := (gomesDerivativePowerChainTransfer_opposite_commute_iff K m i j).mp
      (h (gomesDerivativePowerChainTransfer K m i j) (gomesDerivativePowerChainTransfer K m j i))
    exact Nat.zero_ne_one (congrArg Fin.val hij)
  · rintro rfl E F
    apply (gomesPolynomialDerivativePowerCommutantEquiv K 1).injective
    rw [map_mul, map_mul]
    apply Matrix.ext
    intro i j
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    subst j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, Fin.sum_univ_one]
    exact mul_comm _ _

/-- Chain transfers act on divided monomials exactly as their source and target labels prescribe. -/
theorem gomesDerivativePowerChainTransfer_basis (i j r : Fin m) (n : ℕ) :
    (gomesDerivativePowerChainTransfer K m i j).val
      (gomesDividedMonomialBasis K (n * m + r.val)) =
        if r = j then gomesDividedMonomialBasis K (n * m + i.val) else 0 := by
  have h0 : gomesFormalSeriesPolynomialOperator K (0 : PowerSeries K) = 0 :=
    (gomesFormalSeriesPolynomialAlgHom K).map_zero
  have h1 : gomesFormalSeriesPolynomialOperator K (1 : PowerSeries K) = 1 :=
    (gomesFormalSeriesPolynomialAlgHom K).map_one
  rw [gomesDerivativePowerChainTransfer, gomesPolynomialDerivativePowerCommutantEquiv_symm_apply,
    gomesPolynomialResidueChainEquiv_basis]
  have hs : (fun k : Fin m => ∑ l : Fin m,
      gomesFormalSeriesPolynomialOperator K ((Matrix.single i j 1 : Matrix (Fin m) (Fin m) (PowerSeries K)) k l)
        ((Pi.single r (gomesDividedMonomialBasis K n) : Fin m → K[X]) l)) =
      if r = j then Pi.single i (gomesDividedMonomialBasis K n) else 0 := by
    funext k
    by_cases hk : k = i
    · subst k
      by_cases hr : r = j
      · subst r
        simp [Matrix.single, apply_ite, ite_apply, h0, h1, Pi.single_apply]
      · simp [Matrix.single, apply_ite, ite_apply, h0, h1, Pi.single_apply, hr, Ne.symm hr]
    · simp [Matrix.single, ite_apply, Ne.symm hk, h0, Pi.single_apply]
  rw [hs]
  by_cases hr : r = j
  · rw [if_pos hr, if_pos hr]
    rw [← gomesPolynomialResidueChainEquiv_basis K m n i, LinearEquiv.symm_apply_apply]
  · rw [if_neg hr, if_neg hr, map_zero]

end GaloisForLFunctions.HTGeometry
