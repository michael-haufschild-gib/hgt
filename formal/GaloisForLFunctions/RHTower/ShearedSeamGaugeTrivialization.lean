import GaloisForLFunctions.RHTower.CutoffCochain

/-!
# Gauge trivialization of the sheared torsion seam

The matrix called the non-split sheared torsion presentation,

`A_shear = [[X^m,1],[0,1]]`,

is not a nontrivial module extension.  It is obtained from the split presentation
`A_split=diag(X^m,1)` by the unimodular row gauge `U=[[1,1],[0,1]]`.  This module proves the explicit
gauge equivalence and the exact transport law for the Fitting boundary:

`boundary(A_shear,Delta)=boundary(A_split,U⁻¹ Delta)`.

For the standard lower crossing, the transported defect is `[[-1,0],[1,0]]`.  It retains the same
nonzero Fitting class, but it is no longer a standard cutoff-crossing defect.  Thus the previously
observed difference between the split and sheared charts does not come from a non-split torsion
module.  It comes from holding the cutoff-crossing defect fixed while changing the target basis.
The live datum is the relative alignment of presentation, defect, and cutoff.

Functional-equation coefficient parity supplies a canonical static flag: its odd projector is
exactly the standard cutoff.  The absolute splitting gauge does not preserve that parity, and in
fact no parity-preserving row gauge can split the sheared presentation.  But the full local FE audit
also acts on the divisor coordinate by `X |-> -X`.  With the same canonical parity on source and
target, the sheared presentation is not an FE-semilinear intertwiner at all.  If target parity is
transported through the shear, the presentation becomes semilinearly equivariant but is explicitly
isomorphic to the split presentation.  Thus the current sheared Fitting object supplies no
simultaneous-gauge-invariant completed obstruction; a genuinely new FE-equivariant presentation is
still required.
-/

noncomputable section
namespace RHTower

open Matrix Polynomial

/-- The unimodular target-row gauge carrying the split presentation to the sheared chart. -/
def shearRowGauge : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  !![1, 1; 0, 1]

/-- The inverse target-row gauge. -/
def unshearRowGauge : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  !![1, -1; 0, 1]

theorem shearRowGauge_mul_unshearRowGauge :
    shearRowGauge * unshearRowGauge = 1 := by
  rw [shearRowGauge, unshearRowGauge, Matrix.mul_fin_two, Matrix.one_fin_two]
  norm_num

theorem unshearRowGauge_mul_shearRowGauge :
    unshearRowGauge * shearRowGauge = 1 := by
  rw [shearRowGauge, unshearRowGauge, Matrix.mul_fin_two, Matrix.one_fin_two]
  norm_num

/-- **The sheared presentation is split up to a unimodular row gauge.** -/
theorem shearTorsionPresentation_eq_rowGauge_mul_split (m : ℕ) :
    shearTorsionPresentation m =
      shearRowGauge * splitTorsionPresentation (R := ℚ) m := by
  rw [shearTorsionPresentation, shearRowGauge, splitTorsionPresentation,
    Matrix.mul_fin_two]
  norm_num

theorem splitTorsionPresentation_eq_unshear_mul_shear (m : ℕ) :
    splitTorsionPresentation (R := ℚ) m =
      unshearRowGauge * shearTorsionPresentation m := by
  rw [shearTorsionPresentation, unshearRowGauge, splitTorsionPresentation,
    Matrix.mul_fin_two]
  norm_num

/-- **Fitting transport law.**  Unshearing both the presentation and its defect preserves the
adjugate boundary trace. -/
theorem fittingBoundaryTrace_shear_eq_split_unshear (m : ℕ)
    (Delta : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    fittingBoundaryTrace (shearTorsionPresentation m) Delta =
      fittingBoundaryTrace (splitTorsionPresentation (R := ℚ) m)
        (unshearRowGauge * Delta) := by
  rw [fittingBoundaryTrace_shearTorsion_apply]
  rw [fittingBoundaryTrace, splitTorsionPresentation]
  have hadj : (!![(X : Polynomial ℚ) ^ m, 0; 0, 1]).adjugate =
      !![1, 0; 0, (X : Polynomial ℚ) ^ m] := by
    rw [Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have htransport : unshearRowGauge * Delta =
      !![Delta 0 0 - Delta 1 0, Delta 0 1 - Delta 1 1; Delta 1 0, Delta 1 1] := by
    rw [unshearRowGauge]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [hadj, htransport, Matrix.mul_fin_two, Matrix.trace_fin_two]
  simp

/-- The Fitting boundary class itself obeys the same transport law. -/
theorem fittingBoundaryClass_shear_eq_split_unshear (m : ℕ)
    (Delta : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    fittingBoundaryClass m (shearTorsionPresentation m) Delta =
      fittingBoundaryClass m (splitTorsionPresentation (R := ℚ) m)
        (unshearRowGauge * Delta) := by
  rw [fittingBoundaryClass, fittingBoundaryClass,
    fittingBoundaryTrace_shear_eq_split_unshear]

/-- The lower crossing acquires a diagonal component after the presentation is split. -/
theorem unshearRowGauge_mul_lowerCrossing :
    unshearRowGauge * polynomialLowerCrossing = !![-1, 0; 1, 0] := by
  rw [unshearRowGauge, polynomialLowerCrossing, Matrix.mul_fin_two]
  norm_num

/-- The transported lower defect is not a standard crossing for the unchanged cutoff. -/
theorem unshearedLowerCrossing_not_standardCrossBoundary :
    ¬ ∃ sigma : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
      unshearRowGauge * polynomialLowerCrossing = crossBoundary standardCutoff sigma := by
  rintro ⟨sigma, h⟩
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) => M 0 0) h
  rw [unshearRowGauge_mul_lowerCrossing] at h00
  simp [crossBoundary, standardCutoff, Matrix.mul_apply] at h00

/-- **Cutoff alignment is extra data.**  Standard cutoff-crossing is not invariant under the row
gauge that splits the sheared presentation. -/
theorem standardCrossBoundary_not_preserved_by_unshear :
    (∃ sigma : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        polynomialLowerCrossing = crossBoundary standardCutoff sigma) ∧
      ¬ ∃ sigma : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        unshearRowGauge * polynomialLowerCrossing = crossBoundary standardCutoff sigma :=
  ⟨⟨polynomialLowerCrossing, polynomialLowerCrossing_eq_crossBoundary⟩,
    unshearedLowerCrossing_not_standardCrossBoundary⟩

/-- Functional-equation parity on the coefficient plane: derivation odd, scalar direction even. -/
def feCoefficientParity : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  !![-1, 0; 0, 1]

/-- The projector onto the FE-odd coefficient line, derived from the involution. -/
def feOddProjector : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  Polynomial.C (1 / 2 : ℚ) • (1 - feCoefficientParity)

/-- The cutoff flag used by the lower-crossing algebra is precisely the canonical FE-odd flag. -/
theorem feOddProjector_eq_standardCutoff :
    feOddProjector = standardCutoff := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [feOddProjector, feCoefficientParity, standardCutoff, Matrix.one_fin_two]
  rw [← Polynomial.C_ofNat 2, ← Polynomial.C_mul]
  norm_num

/-- A row gauge respects the fixed FE coefficient flag when it commutes with FE parity. -/
def PreservesFECoefficientParity
    (V : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) : Prop :=
  V * feCoefficientParity = feCoefficientParity * V

/-- Every FE-parity-preserving row gauge has zero upper-right entry. -/
theorem preservesFECoefficientParity_upperRight_eq_zero
    {V : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)}
    (hV : PreservesFECoefficientParity V) : V 0 1 = 0 := by
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) => M 0 1) hV
  simp [feCoefficientParity, Matrix.mul_apply, Fin.sum_univ_two] at h01
  apply Polynomial.ext
  intro n
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff n) h01
  simp at hc
  simp only [Polynomial.coeff_zero]
  linarith

/-- **Relative non-splitting.**  Although the sheared presentation is absolutely row-equivalent to
the split one, no row gauge preserving the canonical FE coefficient parity can split it. -/
theorem no_feParityPreserving_rowGauge_splits_shear (m : ℕ) :
    ¬ ∃ V : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        PreservesFECoefficientParity V ∧
          shearTorsionPresentation m =
            V * splitTorsionPresentation (R := ℚ) m := by
  rintro ⟨V, hV, hsplit⟩
  have hzero := preservesFECoefficientParity_upperRight_eq_zero hV
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) => M 0 1) hsplit
  simp [shearTorsionPresentation, splitTorsionPresentation, Matrix.mul_apply,
    Fin.sum_univ_two, hzero] at h01

/-- FE sends the local coordinate at `rho` to the negative local coordinate at `1-rho`. -/
theorem fe_pairedLocalCoordinate (rho s : ℂ) :
    (1 - s) - (1 - rho) = -(s - rho) := by
  ring

/-- Entrywise action of the local-coordinate involution `X |-> -X`. -/
def reflectPolynomialMatrix
    (A : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  fun i j => (A i j).comp (-X)

theorem reflectPolynomialMatrix_mul
    (A B : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    reflectPolynomialMatrix (A * B) =
      reflectPolynomialMatrix A * reflectPolynomialMatrix B := by
  ext i j
  simp [reflectPolynomialMatrix, Matrix.mul_apply]

theorem reflectPolynomialMatrix_shearRowGauge :
    reflectPolynomialMatrix shearRowGauge = shearRowGauge := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflectPolynomialMatrix, shearRowGauge]

/-- A presentation intertwines source and target FE actions semilinearly when coefficient parity is
combined with `X |-> -X`. -/
def FESemilinearIntertwines
    (targetParity sourceParity A : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) : Prop :=
  targetParity * reflectPolynomialMatrix A = A * sourceParity

/-- A matrix coefficient parity defines a semilinear involution when applying it twice, together
with `X |-> -X`, is the identity. -/
def IsFESemilinearInvolution
    (R : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) : Prop :=
  R * reflectPolynomialMatrix R = 1

theorem feCoefficientParity_isFESemilinearInvolution :
    IsFESemilinearInvolution feCoefficientParity := by
  rw [IsFESemilinearInvolution]
  rw [feCoefficientParity]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectPolynomialMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The same coefficient parity on source and target does not make the sheared presentation an FE
semilinear object: the constant upper-right entry has the wrong parity. -/
theorem shearTorsionPresentation_not_selfFESemilinear (m : ℕ) :
    ¬ FESemilinearIntertwines feCoefficientParity feCoefficientParity
      (shearTorsionPresentation m) := by
  intro h
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) => M 0 1) h
  simp [reflectPolynomialMatrix, feCoefficientParity,
    shearTorsionPresentation, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- Source parity required by the order-`m` local equation under `X |-> -X`. -/
def splitSourceFEParity (m : ℕ) : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  !![-((-1 : Polynomial ℚ) ^ m), 0; 0, 1]

theorem splitSourceFEParity_isFESemilinearInvolution (m : ℕ) :
    IsFESemilinearInvolution (splitSourceFEParity m) := by
  rw [IsFESemilinearInvolution]
  have hsign : (((-1 : Polynomial ℚ) ^ m) ^ (2 : ℕ)) = 1 := by
    rw [← pow_mul]
    simp
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [splitSourceFEParity, reflectPolynomialMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  simpa [pow_two] using hsign

/-- The split presentation is semilinearly FE-equivariant with the order-dependent source parity. -/
theorem splitTorsionPresentation_feSemilinear (m : ℕ) :
    FESemilinearIntertwines feCoefficientParity (splitSourceFEParity m)
      (splitTorsionPresentation (R := ℚ) m) := by
  rw [FESemilinearIntertwines]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectPolynomialMatrix, feCoefficientParity, splitSourceFEParity,
      splitTorsionPresentation, Matrix.mul_apply, Fin.sum_univ_two]
  rw [show (-X : Polynomial ℚ) = (-1) * X by ring_nf, mul_pow]
  ring_nf

/-- Target FE parity transported through the splitting row gauge. -/
def shearedTargetFEParity : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  shearRowGauge * feCoefficientParity * unshearRowGauge

theorem shearedTargetFEParity_isFESemilinearInvolution :
    IsFESemilinearInvolution shearedTargetFEParity := by
  rw [IsFESemilinearInvolution]
  have hreflectUnshear : reflectPolynomialMatrix unshearRowGauge = unshearRowGauge := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reflectPolynomialMatrix, unshearRowGauge]
  have hreflectParity : reflectPolynomialMatrix feCoefficientParity = feCoefficientParity := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [reflectPolynomialMatrix, feCoefficientParity]
  have hreflectTarget : reflectPolynomialMatrix shearedTargetFEParity =
      shearedTargetFEParity := by
    rw [shearedTargetFEParity, reflectPolynomialMatrix_mul, reflectPolynomialMatrix_mul,
      reflectPolynomialMatrix_shearRowGauge, hreflectParity, hreflectUnshear]
  have hparity : feCoefficientParity * feCoefficientParity = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [feCoefficientParity, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hreflectTarget, shearedTargetFEParity]
  calc
    (shearRowGauge * feCoefficientParity * unshearRowGauge) *
        (shearRowGauge * feCoefficientParity * unshearRowGauge) =
      shearRowGauge * feCoefficientParity *
        (unshearRowGauge * shearRowGauge) * feCoefficientParity * unshearRowGauge := by
          simp only [Matrix.mul_assoc]
    _ = shearRowGauge * feCoefficientParity * 1 * feCoefficientParity * unshearRowGauge := by
          rw [unshearRowGauge_mul_shearRowGauge]
    _ = shearRowGauge * (feCoefficientParity * feCoefficientParity) * unshearRowGauge := by
          simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = shearRowGauge * 1 * unshearRowGauge := by rw [hparity]
    _ = 1 := by
      rw [Matrix.mul_one, shearRowGauge_mul_unshearRowGauge]

theorem shearedTargetFEParity_intertwines_rowGauge :
    shearedTargetFEParity * reflectPolynomialMatrix shearRowGauge =
      shearRowGauge * feCoefficientParity := by
  rw [reflectPolynomialMatrix_shearRowGauge, shearedTargetFEParity]
  rw [Matrix.mul_assoc, Matrix.mul_assoc,
    unshearRowGauge_mul_shearRowGauge, Matrix.mul_one]

/-- **Simultaneous transport trivializes the relative claim.**  With target FE parity transported
through the row gauge, the sheared presentation is FE-semilinearly equivariant and explicitly
isomorphic to the split presentation. -/
theorem shearTorsionPresentation_feSemilinear_transported (m : ℕ) :
    FESemilinearIntertwines shearedTargetFEParity (splitSourceFEParity m)
      (shearTorsionPresentation m) := by
  have hrow : shearedTargetFEParity * shearRowGauge =
      shearRowGauge * feCoefficientParity := by
    have h := shearedTargetFEParity_intertwines_rowGauge
    rw [reflectPolynomialMatrix_shearRowGauge] at h
    exact h
  rw [FESemilinearIntertwines, shearTorsionPresentation_eq_rowGauge_mul_split,
    reflectPolynomialMatrix_mul, reflectPolynomialMatrix_shearRowGauge]
  calc
    shearedTargetFEParity *
        (shearRowGauge * reflectPolynomialMatrix (splitTorsionPresentation (R := ℚ) m)) =
        (shearedTargetFEParity * shearRowGauge) *
          reflectPolynomialMatrix (splitTorsionPresentation (R := ℚ) m) := by
            rw [Matrix.mul_assoc]
    _ = (shearRowGauge * feCoefficientParity) *
          reflectPolynomialMatrix (splitTorsionPresentation (R := ℚ) m) := by
            rw [hrow]
    _ = shearRowGauge *
          (feCoefficientParity *
            reflectPolynomialMatrix (splitTorsionPresentation (R := ℚ) m)) := by
            rw [Matrix.mul_assoc]
    _ = shearRowGauge *
          (splitTorsionPresentation (R := ℚ) m * splitSourceFEParity m) := by
            rw [splitTorsionPresentation_feSemilinear m]
    _ = (shearRowGauge * splitTorsionPresentation (R := ℚ) m) *
          splitSourceFEParity m := by
            rw [Matrix.mul_assoc]

end RHTower
