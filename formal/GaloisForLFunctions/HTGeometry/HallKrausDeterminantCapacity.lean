import GaloisForLFunctions.HTGeometry.LinearHallTransversal
import GaloisForLFunctions.HTGeometry.CompactDetectorNearRadicalAlternative
import GaloisForLFunctions.HTGeometry.PositiveConeDeterminantMonotone
import GaloisForLFunctions.HTGeometry.ConstitutiveSelfDualFactorizationMatrixRay
import GaloisForLFunctions.HTGeometry.LocalPauliCapacityDegeneration

/-!
# Hall determinant certificates for finite Kraus families

Linear Hall expansion permits one independent image from every column of every unitary frame.
Summing the squared determinants of all such colored column selections gives a continuous,
strictly positive certificate on the compact unitary group, hence a uniform positive margin.
This is the finite-dimensional determinant-capacity input for matrix Dyson boundary analysis.
-/

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d κ : Type*} [Fintype d] [DecidableEq d] [Fintype κ] [DecidableEq κ]

/-- The columns of a unitary matrix, packaged as a basis of coordinate space. -/
def unitaryColumnBasis (U : Matrix.unitaryGroup d ℂ) : Module.Basis d ℂ (d → ℂ) := by
  let f : (d → ℂ) →ₗ[ℂ] (d → ℂ) := (U : Matrix d d ℂ).mulVecLin
  have hleft : (U : Matrix d d ℂ)ᴴ * (U : Matrix d d ℂ) = 1 := by
    have h := (Unitary.mem_iff.mp U.property).1
    rw [Matrix.star_eq_conjTranspose] at h
    exact h
  have hright : (U : Matrix d d ℂ) * (U : Matrix d d ℂ)ᴴ = 1 := by
    have h := (Unitary.mem_iff.mp U.property).2
    rw [Matrix.star_eq_conjTranspose] at h
    exact h
  have hinj : Function.Injective f := by
    intro x y hxy
    have h := congrArg (fun z ↦ (U : Matrix d d ℂ)ᴴ.mulVec z) hxy
    dsimp [f, Matrix.mulVecLin_apply] at h
    simp only [Matrix.mulVec_mulVec] at h
    rw [hleft] at h
    simpa using h
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨(U : Matrix d d ℂ)ᴴ.mulVec y, ?_⟩
    dsimp [f, Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, hright]
    simp
  exact (Pi.basisFun ℂ d).map (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

theorem unitaryColumnBasis_apply (U : Matrix.unitaryGroup d ℂ) (j : d) :
    unitaryColumnBasis U j = fun i ↦ (U : Matrix d d ℂ) i j := by
  ext i
  simp only [unitaryColumnBasis, Module.Basis.map_apply, LinearEquiv.ofBijective_apply,
    Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

/-- Matrix whose `j`th column applies the color `k j` to the `j`th column of `U`. -/
def hallSelectedColumnMatrix (A : κ → Matrix d d ℂ) (U : Matrix d d ℂ)
    (k : d → κ) : Matrix d d ℂ :=
  fun i j ↦ (A (k j) * U) i j

theorem hallSelectedColumnMatrix_col (A : κ → Matrix d d ℂ)
    (U : Matrix d d ℂ) (k : d → κ) (j : d) :
    (hallSelectedColumnMatrix A U k).col j =
      (A (k j)).mulVec (fun i ↦ U i j) := by
  ext i
  simp only [hallSelectedColumnMatrix, Matrix.col_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct]

/-- Every unitary frame has a colored Hall selection with nonzero determinant. -/
theorem exists_hallSelectedColumnMatrix_det_ne_zero
    (A : κ → Matrix d d ℂ)
    (hHall : LinearFamilyHall fun k ↦ (A k).mulVecLin)
    (U : Matrix.unitaryGroup d ℂ) :
    ∃ k : d → κ, (hallSelectedColumnMatrix A U k).det ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_linearIndependent_image_choice_of_hall
    (fun k ↦ (A k).mulVecLin) hHall (unitaryColumnBasis U)
  refine ⟨k, ?_⟩
  have hcols : LinearIndependent ℂ (hallSelectedColumnMatrix A U k).col := by
    have hk' : LinearIndependent ℂ
        (fun j ↦ (A (k j)).mulVec (fun i ↦ (U : Matrix d d ℂ) i j)) := by
      simpa only [unitaryColumnBasis_apply, Matrix.mulVecLin_apply] using hk
    have heq : (hallSelectedColumnMatrix A U k).col =
        fun j ↦ (A (k j)).mulVec (fun i ↦ (U : Matrix d d ℂ) i j) := by
      funext j
      exact hallSelectedColumnMatrix_col A U k j
    rw [heq]
    exact hk'
  have hunit : IsUnit (hallSelectedColumnMatrix A U k) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  exact (isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit))

/-- Sum of squared determinant certificates over every colored column selection. -/
def hallDeterminantCertificate (A : κ → Matrix d d ℂ) (U : Matrix d d ℂ) : ℝ :=
  ∑ k : d → κ, Complex.normSq (hallSelectedColumnMatrix A U k).det

theorem hallDeterminantCertificate_nonneg (A : κ → Matrix d d ℂ)
    (U : Matrix d d ℂ) :
    0 ≤ hallDeterminantCertificate A U :=
  Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

theorem hallDeterminantCertificate_pos_of_unitary
    (A : κ → Matrix d d ℂ)
    (hHall : LinearFamilyHall fun k ↦ (A k).mulVecLin)
    (U : Matrix d d ℂ) (hU : U ∈ Matrix.unitaryGroup d ℂ) :
    0 < hallDeterminantCertificate A U := by
  obtain ⟨k, hk⟩ := exists_hallSelectedColumnMatrix_det_ne_zero A hHall ⟨U, hU⟩
  exact Finset.sum_pos'
    (fun q _ ↦ Complex.normSq_nonneg (hallSelectedColumnMatrix A U q).det)
    ⟨k, Finset.mem_univ _, Complex.normSq_pos.mpr hk⟩

theorem continuous_hallDeterminantCertificate (A : κ → Matrix d d ℂ) :
    Continuous (hallDeterminantCertificate A) := by
  unfold hallDeterminantCertificate hallSelectedColumnMatrix
  fun_prop

/-- Compactness upgrades pointwise Hall selections to one uniform positive determinant margin. -/
theorem exists_pos_le_hallDeterminantCertificate
    [Nonempty d] (A : κ → Matrix d d ℂ)
    (hHall : LinearFamilyHall fun k ↦ (A k).mulVecLin) :
    ∃ c : ℝ, 0 < c ∧ ∀ U : Matrix d d ℂ,
      U ∈ Matrix.unitaryGroup d ℂ → c ≤ hallDeterminantCertificate A U := by
  apply exists_pos_compactMargin isCompact_matrixUnitaryGroup
  · exact ⟨1, by simp⟩
  · exact (continuous_hallDeterminantCertificate A).continuousOn
  · exact hallDeterminantCertificate_pos_of_unitary A hHall

/-! ## Positive-cone determinant floor -/

/-- Rank-one Gram matrix of one column. -/
def hallColumnOuter (B : Matrix d d ℂ) (j : d) : Matrix d d ℂ :=
  outerSelf (fun i ↦ star (B i j))

theorem hallColumnOuter_apply (B : Matrix d d ℂ) (j i l : d) :
    hallColumnOuter B j i l = B i j * star (B l j) := by
  simp [hallColumnOuter, outerSelf_apply]

/-- A diagonal congruence is the weighted sum of its column Gram matrices. -/
theorem mul_diagonal_mul_conjTranspose_eq_sum_hallColumnOuter
    (B : Matrix d d ℂ) (lam : d → ℝ) :
    B * Matrix.diagonal (fun j ↦ (lam j : ℂ)) * Bᴴ =
      ∑ j, ((lam j : ℂ) • hallColumnOuter B j) := by
  ext i l
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hallColumnOuter_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single j]
  · simp [mul_assoc]
    ring
  · intro q _ hq
    simp [hq]
  · simp

/-- Selecting one colored column in every eigendirection gives a positive sub-congruence of the
full Kraus sum. -/
theorem kraus_diagonal_sum_sub_hallSelected_posSemidef
    (A : κ → Matrix d d ℂ) (U : Matrix d d ℂ) (lam : d → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (k : d → κ) :
    ((∑ q, (A q * U) * Matrix.diagonal (fun j ↦ (lam j : ℂ)) * (A q * U)ᴴ) -
      hallSelectedColumnMatrix A U k * Matrix.diagonal (fun j ↦ (lam j : ℂ)) *
        (hallSelectedColumnMatrix A U k)ᴴ).PosSemidef := by
  let T : d → κ → Matrix d d ℂ := fun j q ↦
    ((lam j : ℂ) • hallColumnOuter (A q * U) j)
  have htotal :
      ∑ q, (A q * U) * Matrix.diagonal (fun j ↦ (lam j : ℂ)) * (A q * U)ᴴ =
        ∑ j, ∑ q, T j q := by
    simp_rw [mul_diagonal_mul_conjTranspose_eq_sum_hallColumnOuter]
    rw [Finset.sum_comm]
  have hselected :
      hallSelectedColumnMatrix A U k * Matrix.diagonal (fun j ↦ (lam j : ℂ)) *
          (hallSelectedColumnMatrix A U k)ᴴ = ∑ j, T j (k j) := by
    rw [mul_diagonal_mul_conjTranspose_eq_sum_hallColumnOuter]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
  rw [htotal, hselected]
  have heq : (∑ j, ∑ q, T j q) - ∑ j, T j (k j) =
      ∑ j, ∑ q ∈ (Finset.univ.erase (k j)), T j q := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (k j))]
    simp
  rw [heq]
  refine Finset.sum_induction _ Matrix.PosSemidef
    (fun X Y hX hY ↦ hX.add hY) Matrix.PosSemidef.zero ?_
  intro j _
  refine Finset.sum_induction _ Matrix.PosSemidef
    (fun X Y hX hY ↦ hX.add hY) Matrix.PosSemidef.zero ?_
  intro q _
  apply posSemidef_real_smul (outerSelf_posSemidef _)
  exact hlam j

/-- A selected diagonal congruence is positive semidefinite. -/
theorem hallSelected_diagonal_congruence_posSemidef
    (A : κ → Matrix d d ℂ) (U : Matrix d d ℂ) (lam : d → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (k : d → κ) :
    (hallSelectedColumnMatrix A U k * Matrix.diagonal (fun j ↦ (lam j : ℂ)) *
      (hallSelectedColumnMatrix A U k)ᴴ).PosSemidef := by
  rw [mul_diagonal_mul_conjTranspose_eq_sum_hallColumnOuter]
  refine Finset.sum_induction _ Matrix.PosSemidef
    (fun X Y hX hY ↦ hX.add hY) Matrix.PosSemidef.zero ?_
  intro j _
  apply posSemidef_real_smul (outerSelf_posSemidef _)
  exact hlam j

/-- Exact determinant of a selected eigencolumn congruence. -/
theorem det_hallSelected_diagonal_congruence
    (A : κ → Matrix d d ℂ) (U : Matrix d d ℂ) (lam : d → ℝ)
    (k : d → κ) :
    (hallSelectedColumnMatrix A U k * Matrix.diagonal (fun j ↦ (lam j : ℂ)) *
        (hallSelectedColumnMatrix A U k)ᴴ).det =
      (Complex.normSq (hallSelectedColumnMatrix A U k).det : ℂ) *
        ∏ j, (lam j : ℂ) := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose,
    Complex.normSq_eq_conj_mul_self]
  change ((hallSelectedColumnMatrix A U k).det * ∏ j, (lam j : ℂ)) *
      star (hallSelectedColumnMatrix A U k).det =
    star (hallSelectedColumnMatrix A U k).det *
      (hallSelectedColumnMatrix A U k).det * ∏ j, (lam j : ℂ)
  ring

/-- The Kraus image of a positive-definite matrix dominates every colored eigencolumn selection. -/
theorem hallSelected_congruence_det_le_krausSum_det
    (A : κ → Matrix d d ℂ) {X : Matrix d d ℂ} (hX : X.PosDef)
    (k : d → κ) :
    (Complex.normSq
        (hallSelectedColumnMatrix A hX.isHermitian.eigenvectorUnitary k).det : ℂ) * X.det ≤
      (∑ q, A q * X * (A q)ᴴ).det := by
  let U : Matrix d d ℂ := hX.isHermitian.eigenvectorUnitary
  let lam : d → ℝ := hX.isHermitian.eigenvalues
  let D : Matrix d d ℂ := Matrix.diagonal fun j ↦ (lam j : ℂ)
  let C : Matrix d d ℂ := hallSelectedColumnMatrix A U k
  have hlam : ∀ j, 0 ≤ lam j := fun j ↦ le_of_lt (hX.eigenvalues_pos j)
  have hspec : X = U * D * Uᴴ := by
    have h := isHermitian_eq_conj_diagonal hX.isHermitian
    rw [Matrix.star_eq_conjTranspose] at h
    simpa only [U, D, lam] using h
  have htotal : (∑ q, A q * X * (A q)ᴴ) =
      ∑ q, (A q * U) * D * (A q * U)ᴴ := by
    rw [hspec]
    apply Finset.sum_congr rfl
    intro q _
    simp only [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hCpsd : (C * D * Cᴴ).PosSemidef := by
    simpa only [C, D] using hallSelected_diagonal_congruence_posSemidef A U lam hlam k
  have htotalPsd : (∑ q, A q * X * (A q)ᴴ).PosSemidef :=
    posSemidef_krausSum hX.posSemidef A
  have hdiff : ((∑ q, A q * X * (A q)ᴴ) - C * D * Cᴴ).PosSemidef := by
    rw [htotal]
    simpa only [C, D] using kraus_diagonal_sum_sub_hallSelected_posSemidef A U lam hlam k
  have hdet := det_le_det_of_loewner hCpsd htotalPsd hdiff
  have hdetC : (C * D * Cᴴ).det =
      (Complex.normSq C.det : ℂ) * X.det := by
    rw [det_hallSelected_diagonal_congruence]
    have hXdet := hX.isHermitian.det_eq_prod_eigenvalues
    rw [hXdet]
    push_cast
    rfl
  rw [hdetC] at hdet
  simpa only [C, U] using hdet

/-- Some member of a nonempty finite real family is at least its average. -/
theorem exists_hallCertificateTerm_ge_average
    {J : Type*} [Fintype J] [Nonempty J] (f : J → ℝ) :
    ∃ j, (∑ i, f i) ≤ (Fintype.card J : ℝ) * f j := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image (Finset.univ : Finset J) f Finset.univ_nonempty
  refine ⟨j, ?_⟩
  calc
    (∑ i, f i) ≤ ∑ _i : J, f j :=
      Finset.sum_le_sum fun i _ ↦ hj i (Finset.mem_univ i)
    _ = (Fintype.card J : ℝ) * f j := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- A positive-definite complex matrix has strictly positive real determinant. -/
theorem posDef_det_realPart_pos {X : Matrix d d ℂ} (hX : X.PosDef) :
    0 < X.det.re := by
  have hdet := hX.isHermitian.det_eq_prod_eigenvalues
  have hprod : 0 < ∏ i, hX.isHermitian.eigenvalues i :=
    Finset.prod_pos fun i _ ↦ hX.eigenvalues_pos i
  rw [hdet]
  convert hprod using 1 <;> norm_cast

/-- The determinant of a positive-semidefinite complex matrix is its real-part embedding. -/
theorem posSemidef_det_eq_ofReal_re {X : Matrix d d ℂ} (hX : X.PosSemidef) :
    (X.det.re : ℂ) = X.det := by
  rw [hX.isHermitian.det_eq_prod_eigenvalues]
  norm_cast

/-- **Hall-to-capacity theorem.** A finite square Kraus family which is rank nondecreasing has a
uniform positive determinant floor on the entire positive-definite cone. -/
theorem exists_pos_hallKraus_det_floor
    [Nonempty d] (A : κ → Matrix d d ℂ)
    (hHall : LinearFamilyHall fun k ↦ (A k).mulVecLin) :
    ∃ c : ℝ, 0 < c ∧ ∀ X : Matrix d d ℂ, X.PosDef →
      c * X.det.re ≤ (∑ q, A q * X * (A q)ᴴ).det.re := by
  have hOne : (1 : Matrix d d ℂ) ∈ Matrix.unitaryGroup d ℂ := by simp
  obtain ⟨k₀, _hk₀⟩ := exists_hallSelectedColumnMatrix_det_ne_zero A hHall ⟨1, hOne⟩
  letI : Nonempty (d → κ) := ⟨k₀⟩
  obtain ⟨m, hmpos, hm⟩ := exists_pos_le_hallDeterminantCertificate A hHall
  let N : ℝ := Fintype.card (d → κ)
  have hNpos : 0 < N := by
    change 0 < (Fintype.card (d → κ) : ℝ)
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  refine ⟨m / N, div_pos hmpos hNpos, ?_⟩
  intro X hX
  let U : Matrix.unitaryGroup d ℂ := hX.isHermitian.eigenvectorUnitary
  obtain ⟨k, hk⟩ := exists_hallCertificateTerm_ge_average
    (fun q : d → κ ↦ Complex.normSq (hallSelectedColumnMatrix A U q).det)
  have hmU : m ≤ hallDeterminantCertificate A U := hm U U.property
  have havg : m / N ≤ Complex.normSq (hallSelectedColumnMatrix A U k).det := by
    have hmn : m ≤ N * Complex.normSq (hallSelectedColumnMatrix A U k).det :=
      hmU.trans (by simpa only [hallDeterminantCertificate, N] using hk)
    exact (div_le_iff₀' hNpos).2 (by simpa [mul_comm] using hmn)
  have hdetX : 0 ≤ X.det.re := le_of_lt (posDef_det_realPart_pos hX)
  have hselected := hallSelected_congruence_det_le_krausSum_det A hX k
  have hselectedReal' :
      Complex.normSq (hallSelectedColumnMatrix A U k).det * X.det.re ≤
        (∑ q, A q * X * (A q)ᴴ).det.re := by
    have hleft :
        ((Complex.normSq (hallSelectedColumnMatrix A U k).det * X.det.re : ℝ) : ℂ) =
          (Complex.normSq (hallSelectedColumnMatrix A U k).det : ℂ) * X.det := by
      rw [Complex.ofReal_mul, posSemidef_det_eq_ofReal_re hX.posSemidef]
    have htotalPsd : (∑ q, A q * X * (A q)ᴴ).PosSemidef :=
      posSemidef_krausSum hX.posSemidef A
    have hright : (((∑ q, A q * X * (A q)ᴴ).det.re : ℝ) : ℂ) =
        (∑ q, A q * X * (A q)ᴴ).det :=
      posSemidef_det_eq_ofReal_re htotalPsd
    rw [← hleft, ← hright] at hselected
    exact Complex.real_le_real.mp hselected
  exact (mul_le_mul_of_nonneg_right havg hdetX).trans hselectedReal'

end

end GaloisForLFunctions.HTGeometry
