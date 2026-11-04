import GaloisForLFunctions.ThetaCuspSections.FifthEvenEndpointBounds
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedFourPointParityWall

/-!
# A common cross-load for the fifth even source endpoints

The explicit two-coordinate load pays the origin Schur defect. At scale seven,
strict retained-model error bounds preserve its complementary positive margin.
-/

noncomputable section
open Matrix RHTower RHTower.ThetaCuspGaussianLimit
namespace GaloisForLFunctions.ThetaCuspSections.EvenFiveEndpoint

private def kernelMatrix (m : ℕ → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![m 0,m 1,kernelU m; m 1,m 2,kernelV m; kernelU m,kernelV m,kernelT m]

private theorem kernelMatrix_det (m : ℕ → ℝ) : (kernelMatrix m).det = kernelDet m := by
  norm_num [kernelMatrix,Matrix.det_fin_three,kernelDet,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  ring

private theorem kernel_inverse_pair (m : ℕ → ℝ) (p q : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, p i*(kernelMatrix m)⁻¹ i j*q j) =
      kernelAdjPair m p q/kernelDet m := by
  rw [Matrix.inv_def,Ring.inverse_eq_inv,kernelMatrix_det]
  simp only [kernelMatrix,Matrix.adjugate_fin_three_of,Matrix.smul_apply,smul_eq_mul]
  norm_num [Fin.sum_univ_succ,kernelAdjPair]
  ring
private theorem two_posDef {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.IsHermitian) (hfirst : 0 < A 0 0) (hdet : 0 < A.det) : A.PosDef := by
  have h10 : A 1 0 = A 0 1 := by
    have h := congrFun (congrFun hA 0) 1
    simpa only [Matrix.conjTranspose_apply,star_trivial] using h
  have he : A = RHTower.symmetricTwoByTwo (A 0 0) (A 0 1) (A 1 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [RHTower.symmetricTwoByTwo,h10]
  have hnum : 0 ≤ A 0 0*A 1 1-(A 0 1)^2 := by
    have hd := hdet.le
    rw [Matrix.det_fin_two,h10] at hd
    simpa only [pow_two] using hd
  have hps : A.PosSemidef := by
    rw [he]
    exact (RHTower.symmetricTwoByTwo_posSemidef_iff_det_nonneg_of_pos_left hfirst).mpr hnum
  exact hps.posDef_iff_det_ne_zero.mpr hdet.ne'

private theorem fromBlocks_posDef {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] {A : Matrix n n ℝ} (B : Matrix n m ℝ)
    (D : Matrix m m ℝ) (hA : A.PosDef) (hS : (D-Bᴴ*A⁻¹*B).PosDef) :
    (Matrix.fromBlocks A B Bᴴ D).PosDef := by
  letI : Invertible A := hA.isUnit.invertible
  have hps := (Matrix.PosDef.fromBlocks₁₁ B D hA).mpr hS.posSemidef
  apply hps.posDef_iff_det_ne_zero.mpr
  rw [Matrix.det_fromBlocks₁₁,Matrix.invOf_eq_nonsing_inv]
  exact mul_ne_zero hA.det_pos.ne' hS.det_pos.ne'
private theorem strict_entry_uniform (P : Matrix (Fin 5) (Fin 5) ℝ)
    (hP : ∀ i j, |P i j| < (1/32:ℝ)) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1/32 ∧ ∀ i j, |P i j| ≤ ε := by
  let f : Fin 5 × Fin 5 → ℝ := fun p => |P p.1 p.2|
  let ε := Finset.univ.sup' Finset.univ_nonempty f
  have hentry (i j : Fin 5) : |P i j| ≤ ε :=
    Finset.le_sup' f (Finset.mem_univ (i,j))
  refine ⟨ε,(abs_nonneg (P 0 0)).trans (hentry 0 0),?_,hentry⟩
  exact (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun p _ => hP p.1 p.2)
private theorem posDef_of_gram {M B : Matrix (Fin 5) (Fin 5) ℝ}
    (hB : B.det ≠ 0) (hgram : (Bᴴ*M*B).PosDef) : M.PosDef := by
  have hbinv : B*B⁻¹=1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB)
  have hinj : Function.Injective (B⁻¹).mulVec := by
    intro v w h
    have hh := congrArg (fun u => B*ᵥu) h
    simpa only [Matrix.mulVec_mulVec,hbinv,Matrix.one_mulVec] using hh
  have hback := hgram.conjTranspose_mul_mul_same hinj
  have he : (B⁻¹)ᴴ*(Bᴴ*M*B)*B⁻¹=M := by
    calc
      _ = (B*B⁻¹)ᴴ*M*(B*B⁻¹) := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = _ := by rw [hbinv]; simp
  rwa [he] at hback

private def paidDiagonal : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.diagonal (fun i => if i.val<3 then 1 else 5/32)

private theorem paidDiagonal_hermitian : paidDiagonal.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  by_cases hij : i=j
  · subst j
    simp [paidDiagonal]
  · simp [paidDiagonal,Matrix.conjTranspose_apply,Matrix.diagonal_apply_ne _ hij,
      Matrix.diagonal_apply_ne _ hij.symm]

private theorem paidDiagonal_floor (v : Fin 5 → ℝ) :
    (5/32:ℝ)*∑ i, v i^2 ≤ v ⬝ᵥ (paidDiagonal*ᵥv) := by
  simp only [paidDiagonal,dotProduct,Matrix.mulVec_diagonal,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h : (5/32:ℝ) ≤ if i.val<3 then 1 else 5/32 := by
    split_ifs <;> norm_num
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg (v i))
  nlinarith only [hm]
/-- The two coupled zero-flux load coordinates. -/
def loadMap : Matrix (Fin 2) (Fin 5) ℝ :=
  !![0,0,1,420,0; 0,0,0,1,1568]

/-- A symmetric cross-load on the two coupled coordinates. -/
def crossLoad (K : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  loadMapᴴ*K*loadMap

/-- Common-kernel columns followed by the dual load-complement columns. -/
def originBasis : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1,0,0,0,0; 0,1,0,0,0; 0,0,-420,1,-420; 0,0,1,0,1; 0,0,-1/1568,0,0]

private def coordinateMap : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1,0,0,0,0; 0,1,0,0,0; 0,0,0,0,-1568; 0,0,1,420,0; 0,0,0,1,1568]

private theorem coordinateMap_originBasis : coordinateMap*originBasis=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinateMap,originBasis,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]

private theorem originBasis_coordinateMap : originBasis*coordinateMap=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinateMap,originBasis,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]

private theorem sevenBasis_coordinate_triangular : (coordinateMap*sevenBasis).BlockTriangular id := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    norm_num [coordinateMap,sevenBasis,sevenVector,liftTail,projectTail,kernelTail,loadColumn,
      Matrix.mul_apply,Fin.sum_univ_succ]
    <;> ring

private theorem sevenBasis_coordinate_diagonal (i : Fin 5) :
    (coordinateMap*sevenBasis) i i = 1/Real.sqrt (diag i) := by
  fin_cases i <;>
    norm_num [coordinateMap,sevenBasis,sevenVector,liftTail,projectTail,kernelTail,loadColumn,
      Matrix.mul_apply,Fin.sum_univ_succ]
    <;> ring

private theorem sevenBasis_det_ne_zero : sevenBasis.det ≠ 0 := by
  have hpos : 0 < (coordinateMap*sevenBasis).det := by
    rw [Matrix.det_of_upperTriangular sevenBasis_coordinate_triangular]
    apply Finset.prod_pos
    intro i hi
    rw [sevenBasis_coordinate_diagonal]
    exact div_pos (by norm_num) (Real.sqrt_pos.2 (diag_pos i))
  intro hz
  rw [Matrix.det_mul,hz,mul_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- The explicit error-paid retained coefficient matrix is positive definite. -/
theorem crossCoefficient_posDef : paidSevenSchur.PosDef := by
  apply two_posDef paidSevenSchur_hermitian paid_seven_first_positive
  have h10 : paidSevenSchur 1 0=paidSevenSchur 0 1 := by
    have h := congrFun (congrFun paidSevenSchur_hermitian 0) 1
    simpa only [Matrix.conjTranspose_apply,star_trivial] using h
  rw [Matrix.det_fin_two,h10,← pow_two]
  exact paid_seven_det_positive

private abbrev originParameter : ℝ := thetaCuspSelfDualModularScale^2
private abbrev originCompensation : ℝ := thetaCuspCenterCompensationSource 0

private def originMomentMatrix (X : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => mOrigin X (i.val+j.val)

private theorem originCompensation_pos : 0 < originCompensation := by
  change 0 < thetaCuspCenterCompensationSource 0
  simp only [thetaCuspCenterCompensationSource,mul_zero,zero_mul,add_zero]
  exact mul_pos (by norm_num) (sq_pos_of_pos (thetaCuspFullSource_pos_all 0))

private theorem origin_moment_zero_pos : 0 < mOrigin originParameter 0 := by
  have hX := thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one
  have hx : originParameter-6 ≠ 0 := by
    dsimp only [originParameter]
    linarith only [hX]
  norm_num [mOrigin,EvenFiveOrigin.originMomentPolynomial]
  nlinarith only [sq_pos_of_ne_zero hx]

private theorem native_zero_polynomial :
    nativeShiftedMatrix 5 0 0 =
      (originCompensation/(3*mOrigin originParameter 0)) • originMomentMatrix originParameter := by
  ext i j
  simp only [Matrix.smul_apply,smul_eq_mul,originMomentMatrix]
  calc
    nativeShiftedMatrix 5 0 0 i j =
        originCompensation*(nativeShiftedMatrix 5 0 0 i j/originCompensation) := by
      field_simp [originCompensation_pos.ne']
    _ = originCompensation*(mOrigin originParameter (i.val+j.val)/(3*mOrigin originParameter 0)) := by
      rw [EvenFiveOrigin.native_normalized_zero]
      rfl
    _ = _ := by ring

private def correctedOriginPolynomial (X : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  originMomentMatrix X+(3*mOrigin X 0) • crossLoad paidSevenSchur

private theorem correctedOrigin_source :
    nativeShiftedMatrix 5 0 0+originCompensation • crossLoad paidSevenSchur =
      (originCompensation/(3*mOrigin originParameter 0)) •
        correctedOriginPolynomial originParameter := by
  rw [native_zero_polynomial]
  simp only [correctedOriginPolynomial,smul_add,smul_smul]
  congr 1
  congr 1
  field_simp [origin_moment_zero_pos.ne']
private def originBorder (X : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  fun i j => kernelBorder (mOrigin X) j i

private def originCorner (X : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => loadCorner (mOrigin X) i j+3*mOrigin X 0*paidSevenSchur i j

private theorem origin_kernel_posDef : (kernelMatrix (mOrigin originParameter)).PosDef := by
  have hs : 0 < originCompensation/(3*mOrigin originParameter 0) :=
    div_pos originCompensation_pos (mul_pos (by norm_num) origin_moment_zero_pos)
  have he : EvenFiveOrigin.coherentKernel 0 =
      (originCompensation/(3*mOrigin originParameter 0)) • kernelMatrix (mOrigin originParameter) := by
    rw [EvenFiveOrigin.coherentKernel,native_zero_polynomial,Matrix.mul_smul,Matrix.smul_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [EvenFiveOrigin.coherentKernelBasis,originMomentMatrix,kernelMatrix,
        kernelU,kernelV,kernelT,Matrix.mul_apply,Matrix.conjTranspose_apply,
        Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
      <;> ring
  have h := EvenFiveOrigin.coherentKernel_zero_posDef
  rw [he] at h
  have hback := h.smul (inv_pos.mpr hs)
  simpa only [smul_smul,inv_mul_cancel₀ hs.ne',one_smul] using hback

private theorem origin_kernel_det_pos : 0 < kernelDet (mOrigin originParameter) := by
  simpa only [kernelMatrix_det] using origin_kernel_posDef.det_pos

private theorem origin_paid_numerator_posDef : (paidGapNumerator originParameter).PosDef := by
  have hlo := thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one
  have hhi := thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths
  have hz : 0 ≤ 10*originParameter-191 := by
    dsimp only [originParameter]
    linarith only [hlo]
  have hzU : 10*originParameter-191 ≤ 1 := by
    dsimp only [originParameter]
    linarith only [hhi]
  have hX : ((10*originParameter-191)+191)/10 = originParameter := by ring
  have hfirst := paid_gap_first_positive _ hz hzU
  have hred := paid_gap_reduced_det_positive _ hz hzU
  rw [hX] at hfirst hred
  apply two_posDef (paidGapNumerator_hermitian _) hfirst
  have hsym : paidGapNumerator originParameter 1 0=paidGapNumerator originParameter 0 1 := by
    have h := congrFun (congrFun (paidGapNumerator_hermitian originParameter) 0) 1
    simpa only [Matrix.conjTranspose_apply,star_trivial] using h
  rw [Matrix.det_fin_two,hsym,← pow_two,paid_gap_det_factor]
  exact mul_pos origin_kernel_det_pos hred

private theorem origin_schur (X : ℝ) (hd : kernelDet (mOrigin X) ≠ 0) :
    originCorner X-(originBorder X)ᴴ*(kernelMatrix (mOrigin X))⁻¹*originBorder X =
      (kernelDet (mOrigin X))⁻¹ • paidGapNumerator X := by
  ext i j
  have hpair : ((originBorder X)ᴴ*(kernelMatrix (mOrigin X))⁻¹*originBorder X) i j =
      kernelAdjPair (mOrigin X) (kernelBorder (mOrigin X) i) (kernelBorder (mOrigin X) j)/
        kernelDet (mOrigin X) := by
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,originBorder,Finset.sum_mul]
    rw [Finset.sum_comm]
    exact kernel_inverse_pair _ _ _
  rw [Matrix.sub_apply,hpair]
  simp only [originCorner,Matrix.smul_apply,smul_eq_mul,paidGapNumerator,originSchurNumerator]
  field_simp [hd]
  ring

private theorem origin_schur_posDef :
    (originCorner originParameter-(originBorder originParameter)ᴴ*
      (kernelMatrix (mOrigin originParameter))⁻¹*originBorder originParameter).PosDef := by
  rw [origin_schur _ origin_kernel_det_pos.ne']
  exact origin_paid_numerator_posDef.smul (inv_pos.mpr origin_kernel_det_pos)
private def splitFive : Fin 3 ⊕ Fin 2 ≃ Fin 5 := finSumFinEquiv

private theorem loadMap_originBasis : loadMap*originBasis =
    (!![0,0,0,1,0; 0,0,0,0,1] : Matrix (Fin 2) (Fin 5) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [loadMap,originBasis,Matrix.mul_apply,Fin.sum_univ_succ]

private theorem origin_load_transform (K : Matrix (Fin 2) (Fin 2) ℝ) :
    originBasisᴴ*crossLoad K*originBasis =
      !![0,0,0,0,0; 0,0,0,0,0; 0,0,0,0,0;
        0,0,0,K 0 0,K 0 1; 0,0,0,K 1 0,K 1 1] := by
  calc
    _ = (loadMap*originBasis)ᴴ*K*(loadMap*originBasis) := by
      simp only [crossLoad,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := by
      rw [loadMap_originBasis]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ]

private theorem correctedOrigin_transform (X : ℝ) :
    (originBasisᴴ*correctedOriginPolynomial X*originBasis).submatrix splitFive splitFive =
      Matrix.fromBlocks (kernelMatrix (mOrigin X)) (originBorder X)
        (originBorder X)ᴴ (originCorner X) := by
  simp only [correctedOriginPolynomial,Matrix.mul_add,Matrix.add_mul,
    Matrix.mul_smul,Matrix.smul_mul,origin_load_transform]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [splitFive,finSumFinEquiv,Fin.castAdd,Fin.natAdd,Fin.castLE,
      originBasis,originMomentMatrix,originBorder,originCorner,kernelMatrix,
      kernelU,kernelV,kernelT,kernelBorder,loadCorner,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Fin.sum_univ_succ,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
    <;> ring

private theorem correctedOriginPolynomial_posDef :
    (correctedOriginPolynomial originParameter).PosDef := by
  have hb := fromBlocks_posDef (originBorder originParameter) (originCorner originParameter)
    origin_kernel_posDef origin_schur_posDef
  rw [← correctedOrigin_transform] at hb
  have hgram : (originBasisᴴ*correctedOriginPolynomial originParameter*originBasis).PosDef := by
    have h := hb.submatrix splitFive.symm.injective
    simpa using h
  exact posDef_of_gram (Matrix.det_ne_zero_of_left_inverse coordinateMap_originBasis) hgram

/-- The explicit positive cross-load repairs the complete fifth even source at the origin. -/
theorem origin_cross_load_posDef :
    (nativeShiftedMatrix 5 0 0+
      thetaCuspCenterCompensationSource 0 • crossLoad paidSevenSchur).PosDef := by
  rw [correctedOrigin_source]
  exact correctedOriginPolynomial_posDef.smul
    (div_pos originCompensation_pos (mul_pos (by norm_num) origin_moment_zero_pos))

private def hankelBilinear (m : ℕ → ℝ) (v w : Fin 5 → ℝ) : ℝ :=
  ∑ i : Fin 5, ∑ j : Fin 5, v i*w j*m (i.val+j.val)

theorem hankel_lift (m : ℕ → ℝ) (t u : Fin 3 → ℝ) (hd : headDet m ≠ 0) :
    hankelBilinear m (liftTail m t) (liftTail m u) =
      (∑ i : Fin 3, ∑ j : Fin 3, t i*u j*schur3 m i.val j.val)/headDet m := by
  norm_num [hankelBilinear,liftTail,Fin.sum_univ_succ]
  field_simp [hd]
  norm_num [schur3,adj,headDet]
  simp only [show (⟨2, by omega⟩ : Fin 3) = (2 : Fin 3) from rfl]
  ring
private theorem schur3_symm (m : ℕ → ℝ) (i j : ℕ) : schur3 m i j = schur3 m j i := by
  dsimp only [schur3,adj]
  rw [Nat.add_comm i j]
  ring

private theorem projectTail_zero (m : ℕ → ℝ) (b : Fin 2 → ℝ) :
    projectTail m b 0 = b 0-420*b 1+
      420*((b 0*crossZero m+b 1*(-420*crossZero m+crossOne m))/kernelNum m) := by
  change b 0-420*b 1-((b 0*crossZero m+b 1*(-420*crossZero m+crossOne m))/kernelNum m)*(-420) = _
  ring

private theorem projectTail_one (m : ℕ → ℝ) (b : Fin 2 → ℝ) :
    projectTail m b 1 = b 1-
      (b 0*crossZero m+b 1*(-420*crossZero m+crossOne m))/kernelNum m := by
  change b 1-((b 0*crossZero m+b 1*(-420*crossZero m+crossOne m))/kernelNum m)*1 = _
  ring

private theorem projectTail_two (m : ℕ → ℝ) (b : Fin 2 → ℝ) :
    projectTail m b 2 =
      ((b 0*crossZero m+b 1*(-420*crossZero m+crossOne m))/kernelNum m)/1568 := by
  change 0-((b 0*crossZero m+b 1*(-420*crossZero m+crossOne m))/kernelNum m)*(-1/1568) = _
  ring

private theorem kernelTail_zero : kernelTail 0 = -420 := rfl
private theorem kernelTail_one : kernelTail 1 = 1 := rfl
private theorem kernelTail_two : kernelTail 2 = -1/1568 := rfl

private theorem hankel_project (m : ℕ → ℝ) (b c : Fin 2 → ℝ)
    (hd : headDet m ≠ 0) (hk : kernelNum m ≠ 0) :
    hankelBilinear m (liftTail m (projectTail m b)) (liftTail m (projectTail m c)) =
      ∑ i : Fin 2, ∑ j : Fin 2, b i*c j*schur2 m i j := by
  rw [hankel_lift m _ _ hd]
  simp only [Fin.sum_univ_three,Fin.sum_univ_two,projectTail_zero,projectTail_one,
    projectTail_two]
  norm_num only [Fin.val_zero,Fin.val_one,Fin.val_ofNat]
  norm_num [schur2]
  field_simp [hd,hk]
  dsimp only [kernelNum,crossZero,crossOne]
  rw [schur3_symm m 1 0,schur3_symm m 2 0,schur3_symm m 2 1]
  ring

private theorem hankel_kernel (m : ℕ → ℝ) (hd : headDet m ≠ 0) :
    hankelBilinear m (liftTail m kernelTail) (liftTail m kernelTail) =
      kernelNum m/headDet m := by
  rw [hankel_lift m _ _ hd]
  norm_num [Fin.sum_univ_succ,kernelTail,kernelNum]
  rw [schur3_symm m 1 0,schur3_symm m 2 0,schur3_symm m 2 1]
  ring

private theorem hankel_kernel_project (m : ℕ → ℝ) (b : Fin 2 → ℝ)
    (hd : headDet m ≠ 0) (hk : kernelNum m ≠ 0) :
    hankelBilinear m (liftTail m kernelTail) (liftTail m (projectTail m b)) = 0 := by
  rw [hankel_lift m _ _ hd]
  simp only [Fin.sum_univ_three,Fin.sum_univ_two,projectTail_zero,projectTail_one,
    projectTail_two,kernelTail_zero,kernelTail_one,kernelTail_two]
  norm_num only [Fin.val_zero,Fin.val_one,Fin.val_ofNat]
  apply (div_eq_zero_iff).mpr
  left
  field_simp [hk]
  dsimp only [kernelNum,crossZero,crossOne]
  simp only [schur3_symm m 1 0,schur3_symm m 2 0,schur3_symm m 2 1]
  ring

private def headFirst (i : Fin 5) : ℝ := if i.val=0 then 1 else 0
private def headSecond (m : ℕ → ℝ) (i : Fin 5) : ℝ :=
  if i.val=0 then -m 1/m 0 else if i.val=1 then 1 else 0

private theorem hankelBilinear_symm (m : ℕ → ℝ) (v w : Fin 5 → ℝ) :
    hankelBilinear m v w = hankelBilinear m w v := by
  unfold hankelBilinear
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_comm j.val i.val]
  ring

private theorem hankel_first_first (m : ℕ → ℝ) :
    hankelBilinear m headFirst headFirst = m 0 := by
  norm_num [hankelBilinear,headFirst,Fin.sum_univ_succ]

private theorem hankel_first_second (m : ℕ → ℝ) (hm : m 0 ≠ 0) :
    hankelBilinear m headFirst (headSecond m) = 0 := by
  norm_num [hankelBilinear,headFirst,headSecond,Fin.sum_univ_succ]
  field_simp [hm]
  ring

private theorem hankel_second_second (m : ℕ → ℝ) (hm : m 0 ≠ 0) :
    hankelBilinear m (headSecond m) (headSecond m) = headDet m/m 0 := by
  norm_num [hankelBilinear,headSecond,Fin.sum_univ_succ]
  field_simp [hm]
  dsimp only [headDet]
  ring

private theorem hankel_first_lift (m : ℕ → ℝ) (t : Fin 3 → ℝ) (hd : headDet m ≠ 0) :
    hankelBilinear m headFirst (liftTail m t) = 0 := by
  norm_num [hankelBilinear,headFirst,liftTail,Fin.sum_univ_succ]
  simp only [show (⟨2, by omega⟩ : Fin 3) = (2 : Fin 3) from rfl]
  field_simp [hd]
  dsimp only [headDet]
  ring

private theorem hankel_second_lift (m : ℕ → ℝ) (t : Fin 3 → ℝ)
    (hm : m 0 ≠ 0) (hd : headDet m ≠ 0) :
    hankelBilinear m (headSecond m) (liftTail m t) = 0 := by
  norm_num [hankelBilinear,headSecond,liftTail,Fin.sum_univ_succ]
  simp only [show (⟨2, by omega⟩ : Fin 3) = (2 : Fin 3) from rfl]
  field_simp [hm,hd]
  dsimp only [headDet]
  ring


private theorem sevenRetainedRaw_eq_hankel (i j : Fin 5) :
    sevenRetainedRaw i j = hankelBilinear mSeven (sevenVector i) (sevenVector j) := by
  have hterm (u v : Fin 5) :
      sevenVector i u*sevenVector j v*
        (((thetaPairRadialEvenPolynomial 49 (u.val+v.val)).eval 14+
          8*retainedRatio*(thetaPairRadialEvenPolynomial 196 (u.val+v.val)).eval 35+
          16*retainedRatio^2*(thetaPairRadialEvenPolynomial 784 (u.val+v.val)).eval 56)/121) =
      (sevenVector i u*sevenVector j v*(thetaPairRadialEvenPolynomial 49 (u.val+v.val)).eval 14+
        8*retainedRatio*(sevenVector i u*sevenVector j v*(thetaPairRadialEvenPolynomial 196 (u.val+v.val)).eval 35)+
        16*retainedRatio^2*(sevenVector i u*sevenVector j v*(thetaPairRadialEvenPolynomial 784 (u.val+v.val)).eval 56))/121 := by
    ring
  simp only [sevenRetainedRaw,sevenPolynomial,hankelBilinear,mSeven]
  simp_rw [hterm]
  simp only [Finset.sum_div,Finset.sum_add_distrib,Finset.mul_sum]

private theorem mSeven_zero_pos : 0 < mSeven 0 := by
  have h := (lt_div_iff₀ loss_pos).mp (diag_pos 0)
  simpa only [zero_mul] using h

private theorem mSeven_head_pos : 0 < headDet mSeven := by
  have h := (lt_div_iff₀ (mul_pos mSeven_zero_pos loss_pos)).mp (diag_pos 1)
  simpa only [zero_mul] using h

private theorem mSeven_kernel_pos : 0 < kernelNum mSeven := by
  have h := (lt_div_iff₀ (mul_pos mSeven_head_pos loss_pos)).mp (diag_pos 2)
  simpa only [zero_mul] using h

private theorem gap_first_pos : 0 < gap 0 0 := (diag_pos 3)

private theorem retained_load_block (b c : Fin 2 → ℝ) :
    hankelBilinear mSeven (liftTail mSeven (projectTail mSeven b))
        (liftTail mSeven (projectTail mSeven c))/loss-
      (∑ a : Fin 2, ∑ d : Fin 2, b a*paidSevenSchur a d*c d) =
      (5/32)*(∑ a : Fin 2, ∑ d : Fin 2, b a*gap a d*c d) := by
  rw [hankel_project _ _ _ mSeven_head_pos.ne' mSeven_kernel_pos.ne']
  simp only [Fin.sum_univ_two,paidSevenSchur]
  ring

private theorem sevenVector_0 : sevenVector 0 = headFirst := rfl

private theorem sevenVector_1 : sevenVector 1 = headSecond mSeven := rfl

private theorem sevenVector_2 : sevenVector 2 = liftTail mSeven kernelTail := rfl

private theorem sevenVector_3 : sevenVector 3 = liftTail mSeven (projectTail mSeven (loadColumn 0)) := rfl

private theorem sevenVector_4 : sevenVector 4 = liftTail mSeven (projectTail mSeven (loadColumn 1)) := rfl

private theorem retained_paid_0_0 :
    sevenRetainedRaw 0 0/loss-sevenLoadRaw 0 0 = diag 0 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_0,hankel_first_first]
  norm_num [sevenLoadRaw,sevenLoad,diag]
  <;> ring

private theorem retained_paid_0_1 :
    sevenRetainedRaw 0 1/loss-sevenLoadRaw 0 1 = 0 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_0,sevenVector_1,hankel_first_second _ mSeven_zero_pos.ne']
  norm_num [sevenLoadRaw,sevenLoad,diag]
  <;> ring

private theorem retained_paid_0_2 :
    sevenRetainedRaw 0 2/loss-sevenLoadRaw 0 2 = 0 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_0,sevenVector_2,hankel_first_lift _ _ mSeven_head_pos.ne']
  norm_num [sevenLoadRaw,sevenLoad,diag]
  <;> ring

private theorem retained_paid_0_3 :
    sevenRetainedRaw 0 3/loss-sevenLoadRaw 0 3 = 0 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_0,sevenVector_3,hankel_first_lift _ _ mSeven_head_pos.ne']
  norm_num [sevenLoadRaw,sevenLoad,diag]
  <;> ring

private theorem retained_paid_0_4 :
    sevenRetainedRaw 0 4/loss-sevenLoadRaw 0 4 = 0 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_0,sevenVector_4,hankel_first_lift _ _ mSeven_head_pos.ne']
  norm_num [sevenLoadRaw,sevenLoad,diag]
  <;> ring

private theorem retained_paid_1_1 :
    sevenRetainedRaw 1 1/loss-sevenLoadRaw 1 1 = diag 1 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_1,hankel_second_second _ mSeven_zero_pos.ne']
  norm_num [sevenLoadRaw,sevenLoad,diag]
  <;> ring

private theorem retained_paid_1_2 :
    sevenRetainedRaw 1 2/loss-sevenLoadRaw 1 2 = 0 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_1,sevenVector_2,hankel_second_lift _ _ mSeven_zero_pos.ne' mSeven_head_pos.ne']
  norm_num [sevenLoadRaw,sevenLoad,diag]
  <;> ring

private theorem retained_paid_1_3 :
    sevenRetainedRaw 1 3/loss-sevenLoadRaw 1 3 = 0 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_1,sevenVector_3,hankel_second_lift _ _ mSeven_zero_pos.ne' mSeven_head_pos.ne']
  norm_num [sevenLoadRaw,sevenLoad,diag]
  <;> ring

private theorem retained_paid_1_4 :
    sevenRetainedRaw 1 4/loss-sevenLoadRaw 1 4 = 0 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_1,sevenVector_4,hankel_second_lift _ _ mSeven_zero_pos.ne' mSeven_head_pos.ne']
  norm_num [sevenLoadRaw,sevenLoad,diag]
  <;> ring

private theorem retained_paid_2_2 :
    sevenRetainedRaw 2 2/loss-sevenLoadRaw 2 2 = diag 2 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_2,hankel_kernel _ mSeven_head_pos.ne']
  norm_num [sevenLoadRaw,sevenLoad,diag]
  <;> ring

private theorem retained_paid_2_3 :
    sevenRetainedRaw 2 3/loss-sevenLoadRaw 2 3 = 0 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_2,sevenVector_3,hankel_kernel_project _ _ mSeven_head_pos.ne' mSeven_kernel_pos.ne']
  norm_num [sevenLoadRaw,sevenLoad,diag]
  <;> ring

private theorem retained_paid_2_4 :
    sevenRetainedRaw 2 4/loss-sevenLoadRaw 2 4 = 0 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_2,sevenVector_4,hankel_kernel_project _ _ mSeven_head_pos.ne' mSeven_kernel_pos.ne']
  norm_num [sevenLoadRaw,sevenLoad,diag]
  <;> ring

private theorem gap_reverse : gap 1 0=gap 0 1 := by
  norm_num [gap,schur2]
  ring

private theorem retained_paid_3_3 :
    sevenRetainedRaw 3 3/loss-sevenLoadRaw 3 3 = (5/32)*diag 3 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_3]
  change hankelBilinear mSeven (liftTail mSeven (projectTail mSeven (loadColumn 0)))
      (liftTail mSeven (projectTail mSeven (loadColumn 0)))/loss-
    (∑ a : Fin 2, ∑ b : Fin 2, loadColumn 0 a*paidSevenSchur a b*loadColumn 0 b) = _
  rw [retained_load_block]
  norm_num [loadColumn,diag,Fin.sum_univ_two]

private theorem retained_paid_3_4 :
    sevenRetainedRaw 3 4/loss-sevenLoadRaw 3 4 = 0 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_3,sevenVector_4]
  change hankelBilinear mSeven (liftTail mSeven (projectTail mSeven (loadColumn 0)))
      (liftTail mSeven (projectTail mSeven (loadColumn 1)))/loss-
    (∑ a : Fin 2, ∑ b : Fin 2, loadColumn 0 a*paidSevenSchur a b*loadColumn 1 b) = _
  rw [retained_load_block]
  norm_num [loadColumn,diag,Fin.sum_univ_two]
  field_simp [gap_first_pos.ne']
  ring

private theorem retained_paid_4_4 :
    sevenRetainedRaw 4 4/loss-sevenLoadRaw 4 4 = (5/32)*diag 4 := by
  rw [sevenRetainedRaw_eq_hankel,sevenVector_4]
  change hankelBilinear mSeven (liftTail mSeven (projectTail mSeven (loadColumn 1)))
      (liftTail mSeven (projectTail mSeven (loadColumn 1)))/loss-
    (∑ a : Fin 2, ∑ b : Fin 2, loadColumn 1 a*paidSevenSchur a b*loadColumn 1 b) = _
  rw [retained_load_block]
  norm_num [loadColumn,diag,Fin.sum_univ_two]
  rw [gap_reverse]
  field_simp [gap_first_pos.ne']
  ring


end GaloisForLFunctions.ThetaCuspSections.EvenFiveEndpoint
