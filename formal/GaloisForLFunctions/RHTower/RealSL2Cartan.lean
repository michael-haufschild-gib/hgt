import GaloisForLFunctions.RHTower.RealPrincipalSeriesDiagonalDerivative
import Mathlib.Analysis.Matrix.PosDef

/-!
# Cartan factorization of real `SL(2)`

Every element of `SL(2, ℝ)` is a product of a compact stabilizer element, a positive diagonal
one-parameter element, and another compact stabilizer element.  The proof uses the spectral
decomposition of `gᵀg`, positive square roots of its two eigenvalues, and an explicit reflection
correction for the orientation of the orthogonal spectral basis.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Matrix

theorem realSL2_orthogonal_svd (g : SL2R) :
    ∃ (ell : Fin 2 → ℝ) (D E Q H : Matrix (Fin 2) (Fin 2) ℝ),
      (∀ i, 0 < ell i) ∧ ell 0 * ell 1 = 1 ∧
      D = Matrix.diagonal (fun i => Real.sqrt (ell i)) ∧
      E = Matrix.diagonal (fun i => (Real.sqrt (ell i))⁻¹) ∧
      D * E = 1 ∧ E * D = 1 ∧ D * D = Matrix.diagonal ell ∧ D.det = 1 ∧
      Q.transpose * Q = 1 ∧ Q * Q.transpose = 1 ∧ H.transpose * H = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) = H * D * Q.transpose := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := g
  let M : Matrix (Fin 2) (Fin 2) ℝ := A.transpose * A
  have hMherm : M.IsHermitian := by
    dsimp [M]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.isHermitian_conjTranspose_mul_self A)
  let ell : Fin 2 → ℝ := hMherm.eigenvalues
  have hellnonneg (i : Fin 2) : 0 ≤ ell i := by
    dsimp [ell, M]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)
  have hdetM : M.det = 1 := by
    dsimp [M, A]
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe]
    norm_num
  have hprod : ell 0 * ell 1 = 1 := by
    change hMherm.eigenvalues 0 * hMherm.eigenvalues 1 = 1
    have hdetEigen := hMherm.det_eq_prod_eigenvalues
    norm_num [RCLike.ofReal] at hdetEigen
    rw [← hdetEigen]
    exact hdetM
  have hellpos (i : Fin 2) : 0 < ell i := by
    fin_cases i
    · by_contra hn
      have hz : ell 0 = 0 := le_antisymm (le_of_not_gt hn) (hellnonneg 0)
      simp [hz] at hprod
    · by_contra hn
      have hz : ell 1 = 0 := le_antisymm (le_of_not_gt hn) (hellnonneg 1)
      simp [hz] at hprod
  let D : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal (fun i => Real.sqrt (ell i))
  let E : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal (fun i => (Real.sqrt (ell i))⁻¹)
  have hDmulE : D * E = 1 := by
    rw [show D = Matrix.diagonal (fun i => Real.sqrt (ell i)) by rfl,
      show E = Matrix.diagonal (fun i => (Real.sqrt (ell i))⁻¹) by rfl,
      Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ne_of_gt (Real.sqrt_pos.2 (hellpos 0)), ne_of_gt (Real.sqrt_pos.2 (hellpos 1))]
  have hEmulD : E * D = 1 := by
    rw [show D = Matrix.diagonal (fun i => Real.sqrt (ell i)) by rfl,
      show E = Matrix.diagonal (fun i => (Real.sqrt (ell i))⁻¹) by rfl,
      Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ne_of_gt (Real.sqrt_pos.2 (hellpos 0)), ne_of_gt (Real.sqrt_pos.2 (hellpos 1))]
  have hDD : D * D = Matrix.diagonal ell := by
    rw [show D = Matrix.diagonal (fun i => Real.sqrt (ell i)) by rfl,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hellnonneg i)
  have hDdet : D.det = 1 := by
    rw [show D = Matrix.diagonal (fun i => Real.sqrt (ell i)) by rfl,
      Matrix.det_diagonal, Fin.prod_univ_two]
    calc
      Real.sqrt (ell 0) * Real.sqrt (ell 1) = Real.sqrt (ell 0 * ell 1) :=
        (Real.sqrt_mul (hellnonneg 0) (ell 1)).symm
      _ = 1 := by rw [hprod]; norm_num
  let Q : Matrix (Fin 2) (Fin 2) ℝ := hMherm.eigenvectorUnitary
  have hQleft : Q.transpose * Q = 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial Q]
    exact Unitary.coe_star_mul_self hMherm.eigenvectorUnitary
  have hQright : Q * Q.transpose = 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial Q]
    exact Unitary.coe_mul_star_self hMherm.eigenvectorUnitary
  have hQstar : star Q = Q.transpose := by
    change Qᴴ = Q.transpose
    exact Matrix.conjTranspose_eq_transpose_of_trivial Q
  have hMdiag : M = Q * (D * D) * Q.transpose := by
    calc
      M = Q * Matrix.diagonal ell * star Q := by
        simpa [Q, ell, Unitary.conjStarAlgAut_apply] using hMherm.spectral_theorem
      _ = Q * Matrix.diagonal ell * Q.transpose := by rw [hQstar]
      _ = Q * (D * D) * Q.transpose := by rw [hDD]
  let H : Matrix (Fin 2) (Fin 2) ℝ := A * Q * E
  have hEtranspose : E.transpose = E := by
    dsimp [E]
    rw [Matrix.diagonal_transpose]
  have hHorth : H.transpose * H = 1 := by
    calc
      H.transpose * H = E * Q.transpose * M * Q * E := by
        dsimp [H, M]
        simp [Matrix.transpose_mul, hEtranspose, mul_assoc]
      _ = E * Q.transpose * (Q * (D * D) * Q.transpose) * Q * E := by rw [hMdiag]
      _ = E * (Q.transpose * Q) * (D * D) * (Q.transpose * Q) * E := by
        noncomm_ring
      _ = E * (D * D) * E := by rw [hQleft]; simp
      _ = (E * D) * (D * E) := by noncomm_ring
      _ = 1 := by rw [hEmulD, hDmulE, mul_one]
  have hfactor : A = H * D * Q.transpose := by
    calc
      A = A * Q * E * D * Q.transpose := by simp [mul_assoc, hEmulD, hQright]
      _ = H * D * Q.transpose := by rfl
  exact ⟨ell, D, E, Q, H, hellpos, hprod, rfl, rfl, hDmulE, hEmulD, hDD, hDdet,
    hQleft, hQright, hHorth, hfactor⟩


theorem realSL2_matrix_relations_of_transpose_mul_self (g : SL2R)
    (horth : (g : Matrix (Fin 2) (Fin 2) ℝ).transpose * (g : Matrix (Fin 2) (Fin 2) ℝ) = 1) :
    (g : SL2R) 1 0 = -(g : SL2R) 0 1 ∧
      (g : SL2R) 1 1 = (g : SL2R) 0 0 := by
  have h00 := congr_fun (congr_fun horth 0) 0
  have h01 := congr_fun (congr_fun horth 0) 1
  have h11 := congr_fun (congr_fun horth 1) 1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
    Matrix.one_apply, ite_true, Fin.isValue] at h00 h01 h11
  have hdet := g.property
  rw [Matrix.det_fin_two] at hdet
  constructor <;> nlinarith [sq_nonneg ((g : SL2R) 1 1 - (g : SL2R) 0 0),
    sq_nonneg ((g : SL2R) 1 0 + (g : SL2R) 0 1)]

theorem exists_sphericalK_eq_of_transpose_mul_self (g : SL2R)
    (horth : (g : Matrix (Fin 2) (Fin 2) ℝ).transpose * (g : Matrix (Fin 2) (Fin 2) ℝ) = 1) :
    ∃ k : upperHalfPlaneStabilizer, (k : SL2R) = g := by
  rcases realSL2_matrix_relations_of_transpose_mul_self g horth with ⟨hg10, hg11⟩
  refine ⟨⟨g, ?_⟩, rfl⟩
  rw [MulAction.mem_stabilizer_iff]
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hden : (((g : SL2R) 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) +
      ((g : SL2R) 1 1 : ℂ)) ≠ 0 := by
    simpa [UpperHalfPlane.denom] using
      UpperHalfPlane.denom_ne_zero ((g : SL2R).mapGL ℝ) UpperHalfPlane.I
  apply (div_eq_iff hden).2
  norm_num [hg10, hg11]
  ring_nf
  rw [Complex.I_sq]
  ring


theorem realSL2_exists_compact_diagonal_compact (g : SL2R) :
    ∃ (k₁ k₂ : upperHalfPlaneStabilizer) (t : ℝ),
      g = (k₁ : SL2R) * (realPositiveDiagonalBorel t : SL2R) * (k₂ : SL2R) := by
  rcases realSL2_orthogonal_svd g with
    ⟨ell, D, E, Q, H, hellpos, hprod, hD, hE, hDmulE, hEmulD, hDD, hDdet,
      hQleft, hQright, hHorth, hfactor⟩
  let A : Matrix (Fin 2) (Fin 2) ℝ := g
  have hfactor' : A = H * D * Q.transpose := by simpa [A] using hfactor
  have hdetQsq : Q.det * Q.det = 1 := by
    have h := congr_arg Matrix.det hQleft
    simpa [Matrix.det_mul, Matrix.det_transpose] using h
  have hdetHQ : H.det * Q.det = 1 := by
    have h := congr_arg Matrix.det hfactor'
    dsimp [A] at h
    rw [Matrix.SpecialLinearGroup.det_coe, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, hDdet, mul_one] at h
    exact h.symm
  have hs0pos : 0 < Real.sqrt (ell 0) := Real.sqrt_pos.2 (hellpos 0)
  let t : ℝ := Real.log (Real.sqrt (ell 0))
  have hdt0 : Real.exp t = Real.sqrt (ell 0) := by
    dsimp [t]
    exact Real.exp_log hs0pos
  have hsprod : Real.sqrt (ell 0) * Real.sqrt (ell 1) = 1 := by
    calc
      Real.sqrt (ell 0) * Real.sqrt (ell 1) = Real.sqrt (ell 0 * ell 1) :=
        (Real.sqrt_mul (le_of_lt (hellpos 0)) (ell 1)).symm
      _ = 1 := by rw [hprod]; norm_num
  have hinv : (Real.sqrt (ell 0))⁻¹ = Real.sqrt (ell 1) := by
    rw [← one_div]
    apply (div_eq_iff (ne_of_gt hs0pos)).mpr
    simpa [mul_comm] using hsprod.symm
  have hdt1 : Real.exp (-t) = Real.sqrt (ell 1) := by
    calc
      Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
      _ = (Real.sqrt (ell 0))⁻¹ := by rw [hdt0]
      _ = Real.sqrt (ell 1) := hinv
  have hDdiag : D = (realPositiveDiagonalBorel t : SL2R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hD, realPositiveDiagonalBorel, hdt0, hdt1]
  rcases (mul_self_eq_one_iff.mp hdetQsq) with hQdet | hQdet
  · have hHdet : H.det = 1 := by simpa [hQdet] using hdetHQ
    let hSL : SL2R := ⟨H, hHdet⟩
    let qSL : SL2R := ⟨Q.transpose, by rw [Matrix.det_transpose, hQdet]⟩
    have hhSLorth : (hSL : Matrix (Fin 2) (Fin 2) ℝ).transpose * hSL = 1 := by
      simpa [hSL] using hHorth
    have hqSLorth : (qSL : Matrix (Fin 2) (Fin 2) ℝ).transpose * qSL = 1 := by
      simpa [qSL, Matrix.transpose_transpose] using hQright
    rcases exists_sphericalK_eq_of_transpose_mul_self hSL hhSLorth with ⟨k₁, hk₁⟩
    rcases exists_sphericalK_eq_of_transpose_mul_self qSL hqSLorth with ⟨k₂, hk₂⟩
    refine ⟨k₁, k₂, t, ?_⟩
    apply Subtype.ext
    change A = (k₁ : SL2R) * (realPositiveDiagonalBorel t : SL2R) * (k₂ : SL2R)
    rw [hk₁, hk₂]
    change A = H * ((realPositiveDiagonalBorel t : SL2R) : Matrix (Fin 2) (Fin 2) ℝ) * Q.transpose
    rw [← hDdiag]
    exact hfactor'
  · let J : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then (-1 : ℝ) else 1)
    have hJtranspose : J.transpose = J := by
      dsimp [J]
      rw [Matrix.diagonal_transpose]
    have hJJ : J * J = 1 := by
      rw [show J = Matrix.diagonal (fun i : Fin 2 => if i = 0 then (-1 : ℝ) else 1) by rfl,
        Matrix.diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num
    have hJdet : J.det = -1 := by
      rw [show J = Matrix.diagonal (fun i : Fin 2 => if i = 0 then (-1 : ℝ) else 1) by rfl,
        Matrix.det_diagonal, Fin.prod_univ_two]
      norm_num
    have hJDcomm : J * D = D * J := by
      rw [show J = Matrix.diagonal (fun i : Fin 2 => if i = 0 then (-1 : ℝ) else 1) by rfl,
        hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i <;> ring
    have hJDJ : J * D * J = D := by
      calc
        J * D * J = (D * J) * J := by rw [hJDcomm]
        _ = D * (J * J) := by noncomm_ring
        _ = D := by rw [hJJ, mul_one]
    have hHdet : H.det = -1 := by nlinarith [hdetHQ]
    let hSL : SL2R := ⟨H * J, by rw [Matrix.det_mul, hHdet, hJdet]; norm_num⟩
    let qSL : SL2R := ⟨J * Q.transpose, by
      rw [Matrix.det_mul, hJdet, Matrix.det_transpose, hQdet]
      norm_num⟩
    have hhSLorth : (hSL : Matrix (Fin 2) (Fin 2) ℝ).transpose * hSL = 1 := by
      change (H * J).transpose * (H * J) = 1
      calc
        (H * J).transpose * (H * J) = J.transpose * (H.transpose * H) * J := by
          simp only [Matrix.transpose_mul]
          noncomm_ring
        _ = 1 := by rw [hJtranspose, hHorth]; simpa using hJJ
    have hqSLorth : (qSL : Matrix (Fin 2) (Fin 2) ℝ).transpose * qSL = 1 := by
      change (J * Q.transpose).transpose * (J * Q.transpose) = 1
      calc
        (J * Q.transpose).transpose * (J * Q.transpose) =
            Q * (J.transpose * J) * Q.transpose := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
          noncomm_ring
        _ = 1 := by rw [hJtranspose, hJJ]; simpa using hQright
    rcases exists_sphericalK_eq_of_transpose_mul_self hSL hhSLorth with ⟨k₁, hk₁⟩
    rcases exists_sphericalK_eq_of_transpose_mul_self qSL hqSLorth with ⟨k₂, hk₂⟩
    refine ⟨k₁, k₂, t, ?_⟩
    apply Subtype.ext
    change A = (k₁ : SL2R) * (realPositiveDiagonalBorel t : SL2R) * (k₂ : SL2R)
    rw [hk₁, hk₂]
    change A = (H * J) * ((realPositiveDiagonalBorel t : SL2R) : Matrix (Fin 2) (Fin 2) ℝ) * (J * Q.transpose)
    rw [← hDdiag]
    calc
      A = H * D * Q.transpose := hfactor'
      _ = (H * J) * D * (J * Q.transpose) := by
        symm
        calc
          (H * J) * D * (J * Q.transpose) = H * (J * D * J) * Q.transpose := by
            noncomm_ring
          _ = H * D * Q.transpose := by rw [hJDJ]


end

end GaloisForLFunctions.RHTower
