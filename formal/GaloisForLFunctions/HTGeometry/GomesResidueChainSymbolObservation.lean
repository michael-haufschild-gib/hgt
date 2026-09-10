import GaloisForLFunctions.HTGeometry.GomesPolynomialDerivativePowerCommutant

/-!
# Reading formal matrix symbols from polynomial outputs

Each formal matrix coefficient is an actual residue-chain output observation.
The constant coefficient in component zero is the original polynomial constant
coefficient, giving an especially direct first-row observation formula.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry

variable (K : Type*) [Field K] [CharZero K]
variable (m : ℕ) [NeZero m]

/-- The first residue component preserves the original polynomial constant coefficient. -/
theorem gomesPolynomialResidueChainEquiv_counit (P : K[X]) :
    (gomesPolynomialResidueChainEquiv K m P 0).coeff 0 = P.coeff 0 := by
  let q : (Fin m → K[X]) →ₗ[K] K :=
    { toFun v := (v 0).coeff 0
      map_add' v w := Polynomial.coeff_add _ _ _
      map_smul' c v := Polynomial.coeff_smul c (v 0) 0 }
  have h : q.comp (gomesPolynomialResidueChainEquiv K m).toLinearMap = Polynomial.lcoeff K 0 := by
    apply ((gomesDividedMonomialBasis K).reindex (Nat.divModEquiv m)).ext
    rintro ⟨n, r⟩
    rw [Module.Basis.reindex_apply, Nat.divModEquiv_symm_apply]
    change (gomesPolynomialResidueChainEquiv K m
      (gomesDividedMonomialBasis K (n * m + r.val)) 0).coeff 0 =
        (gomesDividedMonomialBasis K (n * m + r.val)).coeff 0
    rw [gomesPolynomialResidueChainEquiv_basis]
    cases n with
    | zero =>
        simp only [Nat.zero_mul, Nat.zero_add]
        by_cases hr : r = 0
        · subst r
          simp [gomesDividedMonomialBasis_coeff_zero]
        · have hrv : r.val ≠ 0 := fun h => hr (Fin.ext h)
          simp [Ne.symm hr, gomesDividedMonomialBasis_coeff_zero, hrv]
    | succ n =>
        have hindex : (n + 1) * m + r.val ≠ 0 :=
          Nat.ne_of_gt (Nat.add_pos_left (Nat.mul_pos (Nat.succ_pos n) (Nat.pos_of_neZero m)) r.val)
        by_cases hr : r = 0
        · subst r
          rw [Pi.single_apply, if_pos rfl, gomesDividedMonomialBasis_coeff_zero,
            if_neg (Nat.succ_ne_zero n), gomesDividedMonomialBasis_coeff_zero, if_neg hindex]
        · simp only [Pi.single_apply, Ne.symm hr, if_false, Polynomial.coeff_zero,
            gomesDividedMonomialBasis_coeff_zero, hindex]
  exact congrArg (fun L : K[X] →ₗ[K] K => L P) h

/-- Every formal matrix coefficient is a constant output observation in its target residue chain. -/
theorem gomesPolynomialDerivativePowerCommutant_matrix_coeff
    (E : GomesPolynomialDerivativePowerCommutant K m) (i j : Fin m) (n : ℕ) :
    PowerSeries.coeff n (gomesPolynomialDerivativePowerCommutantEquiv K m E i j) =
      (gomesPolynomialResidueChainEquiv K m
        (E.val (gomesDividedMonomialBasis K (n * m + j.val))) i).coeff 0 := by
  have h := congrArg
    (fun A : GomesPolynomialDerivativePowerCommutant K m =>
      gomesPolynomialResidueChainEquiv K m
        (A.val (gomesDividedMonomialBasis K (n * m + j.val))) i)
    ((gomesPolynomialDerivativePowerCommutantEquiv K m).symm_apply_apply E)
  rw [gomesPolynomialDerivativePowerCommutantEquiv_symm_apply,
    LinearEquiv.apply_symm_apply] at h
  simp [gomesPolynomialResidueChainEquiv_basis, Pi.single_apply, apply_ite] at h
  rw [← h, gomesFormalSeriesPolynomialOperator_coeff_zero]

/-- The complete first row of a symmetry's formal matrix is read directly from polynomial constants. -/
theorem gomesPolynomialDerivativePowerCommutant_matrix_first_row
    (E : GomesPolynomialDerivativePowerCommutant K m) (j : Fin m) (n : ℕ) :
    PowerSeries.coeff n (gomesPolynomialDerivativePowerCommutantEquiv K m E 0 j) =
      (E.val (gomesDividedMonomialBasis K (n * m + j.val))).coeff 0 := by
  rw [gomesPolynomialDerivativePowerCommutant_matrix_coeff, gomesPolynomialResidueChainEquiv_counit]

end GaloisForLFunctions.HTGeometry
