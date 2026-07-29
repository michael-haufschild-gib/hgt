import GaloisForLFunctions.HTGeometry.ColorGramMinkowskiCone
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Instances.Matrix

/-!
# Continuous equivariant Gram-record rigidity

This file proves a specialized `3 × 2` invariant-theory bridge used by the causalization research
program.  A continuous Hermitian-valued record on complex `3 × 2` event matrices is forced to be a
real scalar multiple of the Gram matrix when it:

* forgets every left unitary `U(3)` frame; and
* transforms by congruence under every invertible right `GL(2, ℂ)` frame.

Positivity forces the scalar to be nonnegative, and a nonzero positive record forces it to be
positive.  The proof includes:

* the `2 × 2` Hermitian unitary-centralizer calculation;
* unitary completion of a `3 × 2` isometric frame;
* full-rank polar reduction through the matrix continuous functional calculus; and
* density of full-rank `3 × 2` matrices through a quadratic determinant perturbation.

This is classical invariant-theory and polar-decomposition mathematics.  It removes freedom in a
candidate local record map; it does not identify that map with a physical event record, construct
spacetime, or derive causalization dynamics.
-/

open Matrix
open scoped ComplexOrder Matrix MatrixOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Standard inclusion of two complex columns into three complex rows. -/
def colorStandardFrame : ColorEventMatrix :=
  !![(1 : ℂ), 0; 0, 1; 0, 0]

theorem colorStandardFrame_isometry :
    colorStandardFrameᴴ * colorStandardFrame = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorStandardFrame, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Diagonal unitary used to kill the off-diagonal entries of a fixed Hermitian matrix. -/
def twoPhaseFlip : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, -1]

/-- Unitary transposition of the two standard basis vectors. -/
def twoSwap : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; 1, 0]

theorem twoPhaseFlip_unitary : twoPhaseFlipᴴ * twoPhaseFlip = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoPhaseFlip, Matrix.mul_apply, Fin.sum_univ_succ]

theorem twoSwap_unitary : twoSwapᴴ * twoSwap = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoSwap, Matrix.mul_apply, Fin.sum_univ_succ]

/-- A Hermitian `2 × 2` matrix fixed by every unitary congruence is a real scalar identity. -/
theorem hermitianTwo_fixed_by_unitary_congruence_eq_real_smul_one
    (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H.IsHermitian)
    (hfix : ∀ V : Matrix (Fin 2) (Fin 2) ℂ,
      Vᴴ * V = 1 → Vᴴ * H * V = H) :
    ∃ c : ℝ, H = (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hflip := hfix twoPhaseFlip twoPhaseFlip_unitary
  have hswap := hfix twoSwap twoSwap_unitary
  have h01 : H 0 1 = 0 := by
    have h := congrFun₂ hflip 0 1
    simp [twoPhaseFlip, Matrix.mul_apply, Fin.sum_univ_succ] at h
    have hz : H 0 1 = -H 0 1 := h.symm
    have hadd : H 0 1 + H 0 1 = 0 :=
      eq_neg_iff_add_eq_zero.mp hz
    have htwo : (2 : ℂ) * H 0 1 = 0 := by
      simpa [two_mul] using hadd
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have h10 : H 1 0 = 0 := by
    have h := congrFun₂ hflip 1 0
    simp [twoPhaseFlip, Matrix.mul_apply, Fin.sum_univ_succ] at h
    have hz : H 1 0 = -H 1 0 := h.symm
    have hadd : H 1 0 + H 1 0 = 0 :=
      eq_neg_iff_add_eq_zero.mp hz
    have htwo : (2 : ℂ) * H 1 0 = 0 := by
      simpa [two_mul] using hadd
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hdiag : H 0 0 = H 1 1 := by
    have h := congrFun₂ hswap 0 0
    simpa [twoSwap, Matrix.mul_apply, Fin.sum_univ_succ] using h.symm
  have h00star : star (H 0 0) = H 0 0 := by
    simpa [Matrix.IsHermitian.apply] using hH.apply 0 0
  refine ⟨(H 0 0).re, ?_⟩
  have h00 : H 0 0 = ((H 0 0).re : ℂ) := by
    apply Complex.ext
    · simp
    · have hi := congrArg Complex.im h00star
      rw [Complex.star_def, Complex.conj_im] at hi
      have him : (H 0 0).im = 0 := by linarith
      simpa using him
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.smul_apply, Matrix.one_apply] using h00
  · simpa [Matrix.smul_apply, Matrix.one_apply] using h01
  · simpa [Matrix.smul_apply, Matrix.one_apply] using h10
  · simpa [Matrix.smul_apply, Matrix.one_apply] using hdiag.symm.trans h00

/-- The two columns of a color event, bundled in complex Euclidean space. -/
def colorColumns (Q : ColorEventMatrix) :
    Fin 2 → EuclideanSpace ℂ (Fin 3) :=
  fun j => WithLp.toLp 2 (Qᵀ j)

theorem colorColumns_orthonormal (Q : ColorEventMatrix)
    (hQ : Qᴴ * Q = 1) :
    Orthonormal ℂ (colorColumns Q) := by
  rw [orthonormal_iff_ite]
  intro i j
  calc
    inner ℂ (colorColumns Q i) (colorColumns Q j) =
        (Qᴴ * Q) i j := inner_matrix_col_col Q Q i j
    _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := congrFun₂ hQ i j
    _ = if i = j then 1 else 0 := by simp [Matrix.one_apply]

/-- Seed for completing two orthonormal columns to an orthonormal basis. -/
def colorCompletedSeed (Q : ColorEventMatrix) :
    Fin 3 → EuclideanSpace ℂ (Fin 3) :=
  ![colorColumns Q 0, colorColumns Q 1, 0]

/-- Every complex `3 × 2` isometric frame is the first two columns of a unitary matrix. -/
theorem color_isometry_has_unitary_completion (Q : ColorEventMatrix)
    (hQ : Qᴴ * Q = 1) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ,
      Uᴴ * U = 1 ∧ U * colorStandardFrame = Q := by
  let hcols : Orthonormal ℂ (colorColumns Q) :=
    colorColumns_orthonormal Q hQ
  have hpair :
      Pairwise fun i j =>
        inner ℂ (colorCompletedSeed Q i) (colorCompletedSeed Q j) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [colorCompletedSeed] at hij ⊢
    · exact hcols.inner_eq_zero (by decide)
    · exact hcols.inner_eq_zero (by decide)
  have hdim :
      Module.finrank ℂ (EuclideanSpace ℂ (Fin 3)) = Fintype.card (Fin 3) := by
    simp
  let b : OrthonormalBasis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis hdim (colorCompletedSeed Q)
  have hb0 : b 0 = colorColumns Q 0 := by
    have h :=
      InnerProductSpace.gramSchmidtOrthonormalBasis_apply_of_orthogonal
        (i := 0) hdim hpair
        (by simpa [colorCompletedSeed] using hcols.ne_zero 0)
    simpa [b, colorCompletedSeed, hcols.norm_eq_one] using h
  have hb1 : b 1 = colorColumns Q 1 := by
    have h :=
      InnerProductSpace.gramSchmidtOrthonormalBasis_apply_of_orthogonal
        (i := 1) hdim hpair
        (by simpa [colorCompletedSeed] using hcols.ne_zero 1)
    simpa [b, colorCompletedSeed, hcols.norm_eq_one] using h
  let U : Matrix (Fin 3) (Fin 3) ℂ :=
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis.toMatrix b
  refine ⟨U, ?_, ?_⟩
  · simp [U]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, colorStandardFrame, Matrix.mul_apply, Fin.sum_univ_succ,
        Module.Basis.toMatrix_apply, hb0, hb1, colorColumns,
        EuclideanSpace.basisFun_repr]

/-- Full-rank `3 × 2` polar reduction to a unitary left frame and positive invertible right frame. -/
theorem color_fullRank_polar_frame (X : ColorEventMatrix)
    (hX : Function.Injective X.mulVec) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℂ)
        (P : Matrix (Fin 2) (Fin 2) ℂ),
      Uᴴ * U = 1 ∧ IsUnit P ∧ P.IsHermitian ∧
        X = U * colorStandardFrame * P := by
  let G : Matrix (Fin 2) (Fin 2) ℂ := Xᴴ * X
  have hG : G.PosDef := by
    exact Matrix.PosDef.conjTranspose_mul_self X hX
  let P : Matrix (Fin 2) (Fin 2) ℂ := CFC.sqrt G
  have hPunit : IsUnit P := by
    exact (CFC.isUnit_sqrt_iff G hG.posSemidef.nonneg).2 hG.isUnit
  have hPherm : P.IsHermitian := by
    simpa [P, Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg G).star_eq
  have hPsq : P * P = G := by
    simpa [P, pow_two] using CFC.sq_sqrt G hG.posSemidef.nonneg
  have hPdet : IsUnit P.det :=
    P.isUnit_iff_isUnit_det.mp hPunit
  let Q : ColorEventMatrix := X * P⁻¹
  have hQ : Qᴴ * Q = 1 := by
    calc
      Qᴴ * Q = P⁻¹ᴴ * (Xᴴ * X) * P⁻¹ := by
        simp [Q, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = P⁻¹ * (P * P) * P⁻¹ := by
        rw [Matrix.conjTranspose_nonsing_inv, hPherm.eq, hPsq]
      _ = 1 := by
        rw [← Matrix.mul_assoc P⁻¹ P P,
          Matrix.nonsing_inv_mul P hPdet, one_mul,
          Matrix.mul_nonsing_inv P hPdet]
  obtain ⟨U, hU, hUQ⟩ := color_isometry_has_unitary_completion Q hQ
  refine ⟨U, P, hU, hPunit, hPherm, ?_⟩
  calc
    X = Q * P := by
      simp [Q, Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPdet]
    _ = U * colorStandardFrame * P := by rw [hUQ]

/-- Equivariant Hermitian records agree with a scalar Gram record on every full-rank event. -/
theorem equivariant_hermitian_record_eq_gram_of_injective
    (F : ColorEventMatrix → Matrix (Fin 2) (Fin 2) ℂ)
    (hherm : ∀ X, (F X).IsHermitian)
    (hleft : ∀ (U : Matrix (Fin 3) (Fin 3) ℂ) X,
      Uᴴ * U = 1 → F (U * X) = F X)
    (hright : ∀ X (A : Matrix (Fin 2) (Fin 2) ℂ),
      IsUnit A → F (X * A) = Aᴴ * F X * A) :
    ∃ c : ℝ, ∀ X, Function.Injective X.mulVec →
      F X = (c : ℂ) • (Xᴴ * X) := by
  let E : ColorEventMatrix := colorStandardFrame
  have hfix : ∀ V : Matrix (Fin 2) (Fin 2) ℂ,
      Vᴴ * V = 1 → Vᴴ * F E * V = F E := by
    intro V hV
    have hVunit : IsUnit V := by
      apply V.isUnit_iff_isUnit_det.mpr
      exact Matrix.isUnit_det_of_left_inverse hV
    have hEV : (E * V)ᴴ * (E * V) = 1 := by
      calc
        (E * V)ᴴ * (E * V) =
            Vᴴ * (Eᴴ * E) * V := by
              simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Vᴴ * V := by rw [show Eᴴ * E = 1 from colorStandardFrame_isometry]; simp
        _ = 1 := hV
    obtain ⟨U, hU, hUEV⟩ :=
      color_isometry_has_unitary_completion (E * V) hEV
    calc
      Vᴴ * F E * V = F (E * V) := (hright E V hVunit).symm
      _ = F (U * E) := by rw [hUEV]
      _ = F E := hleft U E hU
  obtain ⟨c, hc⟩ :=
    hermitianTwo_fixed_by_unitary_congruence_eq_real_smul_one
      (F E) (hherm E) hfix
  refine ⟨c, ?_⟩
  intro X hX
  obtain ⟨U, P, hU, hPunit, hPherm, hXfactor⟩ :=
    color_fullRank_polar_frame X hX
  have hgram : Xᴴ * X = Pᴴ * P := by
    calc
      Xᴴ * X =
          (U * E * P)ᴴ * (U * E * P) := by rw [hXfactor]
      _ = Pᴴ * (Eᴴ * (Uᴴ * U) * E) * P := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * P := by
        rw [hU]
        simp [show Eᴴ * E = 1 from colorStandardFrame_isometry]
  calc
    F X = F ((U * E) * P) := by rw [hXfactor]
    _ = Pᴴ * F (U * E) * P := hright (U * E) P hPunit
    _ = Pᴴ * F E * P := by rw [hleft U E hU]
    _ = Pᴴ * ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * P := by rw [hc]
    _ = (c : ℂ) • (Pᴴ * P) := by
      simp
    _ = (c : ℂ) • (Xᴴ * X) := by rw [hgram]

/-- Complements of finite complex sets are dense. -/
theorem dense_compl_finset_complex (s : Finset ℂ) :
    Dense ((s : Set ℂ)ᶜ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [show (((insert a s : Finset ℂ) : Set ℂ)ᶜ) =
          ({a}ᶜ ∩ ((s : Set ℂ)ᶜ)) by
        ext x
        simp]
      exact
        (dense_compl_singleton a).inter_of_isOpen_right ih s.isClosed.isOpen_compl

/-- Upper `2 × 2` square submatrix of a color event. -/
def colorTopSquare (X : ColorEventMatrix) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => X i.castSucc j

/-- Scalar diagonal perturbation of the upper square of a color event. -/
def colorScalarPerturb (X : ColorEventMatrix) (z : ℂ) :
    ColorEventMatrix :=
  X + z • colorStandardFrame

theorem colorTopSquare_scalarPerturb (X : ColorEventMatrix) (z : ℂ) :
    colorTopSquare (colorScalarPerturb X z) =
      z • (1 : Matrix (Fin 2) (Fin 2) ℂ) + colorTopSquare X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [colorTopSquare, colorScalarPerturb, colorStandardFrame] <;> ring

theorem color_mulVec_injective_of_topSquare_det_ne_zero
    (X : ColorEventMatrix) (hdet : (colorTopSquare X).det ≠ 0) :
    Function.Injective X.mulVec := by
  have htopUnit : IsUnit (colorTopSquare X) := by
    apply (colorTopSquare X).isUnit_iff_isUnit_det.mpr
    exact isUnit_iff_ne_zero.mpr hdet
  have htopInjective : Function.Injective (colorTopSquare X).mulVec :=
    Matrix.mulVec_injective_of_isUnit htopUnit
  intro v w hvw
  apply htopInjective
  ext i
  change (X *ᵥ v) i.castSucc = (X *ᵥ w) i.castSucc
  exact congrFun hvw i.castSucc

/-- Quadratic determinant polynomial of the scalar upper-square perturbation. -/
def colorPerturbDetPolynomial (X : ColorEventMatrix) : Polynomial ℂ :=
  Polynomial.X ^ 2 +
    Polynomial.C (colorTopSquare X 0 0 + colorTopSquare X 1 1) * Polynomial.X +
    Polynomial.C (colorTopSquare X).det

theorem colorPerturbDetPolynomial_coeff_two (X : ColorEventMatrix) :
    (colorPerturbDetPolynomial X).coeff 2 = 1 := by
  simp [colorPerturbDetPolynomial]

theorem colorPerturbDetPolynomial_ne_zero (X : ColorEventMatrix) :
    colorPerturbDetPolynomial X ≠ 0 := by
  intro hzero
  have hcoeff := colorPerturbDetPolynomial_coeff_two X
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  exact zero_ne_one hcoeff

theorem colorPerturbDetPolynomial_eval (X : ColorEventMatrix) (z : ℂ) :
    (colorPerturbDetPolynomial X).eval z =
      (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) + colorTopSquare X).det := by
  rw [Matrix.det_fin_two]
  simp [colorPerturbDetPolynomial]
  rw [Matrix.det_fin_two]
  ring

/-- Full-column-rank color event matrices form a dense subset. -/
theorem dense_color_mulVec_injective :
    Dense {X : ColorEventMatrix | Function.Injective X.mulVec} := by
  rw [dense_iff_inter_open]
  intro O hO hOne
  obtain ⟨X, hXO⟩ := hOne
  let p : Polynomial ℂ := colorPerturbDetPolynomial X
  have hpne : p ≠ 0 := colorPerturbDetPolynomial_ne_zero X
  have hroots :
      Dense (((p.roots.toFinset : Finset ℂ) : Set ℂ)ᶜ) :=
    dense_compl_finset_complex p.roots.toFinset
  let φ : ℂ → ColorEventMatrix := colorScalarPerturb X
  have hφ : Continuous φ := by
    change Continuous (fun z : ℂ => X + z • colorStandardFrame)
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hpreOpen : IsOpen (φ ⁻¹' O) :=
    hO.preimage hφ
  have hpreNonempty : (φ ⁻¹' O).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [φ, colorScalarPerturb] using hXO
  obtain ⟨z, hzRoots, hzO⟩ :=
    hroots.exists_mem_open hpreOpen hpreNonempty
  have hzEval : p.eval z ≠ 0 := by
    intro hz
    have hzMem : z ∈ p.roots :=
      (Polynomial.mem_roots hpne).2 hz
    exact hzRoots (Multiset.mem_toFinset.mpr hzMem)
  have hφInjective : Function.Injective (φ z).mulVec := by
    apply color_mulVec_injective_of_topSquare_det_ne_zero
    rw [colorTopSquare_scalarPerturb]
    rw [← colorPerturbDetPolynomial_eval]
    exact hzEval
  exact ⟨φ z, hzO, hφInjective⟩

/--
Continuous Hermitian records invariant under left `U(3)` and covariant under right `GL(2, ℂ)`
congruence are exactly real scalar multiples of `Xᴴ X`.
-/
theorem continuous_equivariant_hermitian_record_eq_gram
    (F : ColorEventMatrix → Matrix (Fin 2) (Fin 2) ℂ)
    (hcont : Continuous F)
    (hherm : ∀ X, (F X).IsHermitian)
    (hleft : ∀ (U : Matrix (Fin 3) (Fin 3) ℂ) X,
      Uᴴ * U = 1 → F (U * X) = F X)
    (hright : ∀ X (A : Matrix (Fin 2) (Fin 2) ℂ),
      IsUnit A → F (X * A) = Aᴴ * F X * A) :
    ∃ c : ℝ, ∀ X, F X = (c : ℂ) • (Xᴴ * X) := by
  obtain ⟨c, hc⟩ :=
    equivariant_hermitian_record_eq_gram_of_injective
      F hherm hleft hright
  have hgramContinuous :
      Continuous (fun X : ColorEventMatrix =>
        (c : ℂ) • (Xᴴ * X)) := by
    fun_prop
  have heq :
      F = fun X : ColorEventMatrix => (c : ℂ) • (Xᴴ * X) :=
    Continuous.ext_on dense_color_mulVec_injective
      hcont hgramContinuous (fun X hX => hc X hX)
  exact ⟨c, congrFun heq⟩

/-- Every nonnegative real scalar multiple of the color Gram matrix is positive semidefinite. -/
theorem nonneg_real_smul_colorGram_posSemidef
    (c : ℝ) (hc : 0 ≤ c) (X : ColorEventMatrix) :
    ((c : ℂ) • (Xᴴ * X)).PosSemidef := by
  let r : ℂ := Real.sqrt c
  let Y : ColorEventMatrix := r • X
  have hY := colorGramMatrix_posSemidef Y
  have heq : Yᴴ * Y = (c : ℂ) • (Xᴴ * X) := by
    simp [Y, r, Matrix.conjTranspose_smul]
    rw [smul_smul]
    congr 1
    simpa [pow_two] using Real.sq_sqrt hc
  rw [← heq, ← colorGramMatrix]
  exact hY

/-- A real scalar Gram record is positive for every event exactly when its scalar is nonnegative. -/
theorem real_smul_colorGram_posSemidef_all_iff (c : ℝ) :
    (∀ X : ColorEventMatrix, ((c : ℂ) • (Xᴴ * X)).PosSemidef) ↔ 0 ≤ c := by
  constructor
  · intro hpos
    have hscalar :
        ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
      simpa [colorStandardFrame_isometry] using hpos colorStandardFrame
    have hcomplex : (0 : ℂ) ≤ (c : ℂ) := by
      simpa [Matrix.smul_apply, Matrix.one_apply] using
        (hscalar.diag_nonneg (i := (0 : Fin 2)))
    exact RCLike.ofReal_nonneg.mp hcomplex
  · intro hc
    exact fun X => nonneg_real_smul_colorGram_posSemidef c hc X

/-- Positivity of every record forces the Gram scalar to be nonnegative. -/
theorem continuous_equivariant_positive_record_eq_nonneg_gram
    (F : ColorEventMatrix → Matrix (Fin 2) (Fin 2) ℂ)
    (hcont : Continuous F)
    (hherm : ∀ X, (F X).IsHermitian)
    (hpos : ∀ X, (F X).PosSemidef)
    (hleft : ∀ (U : Matrix (Fin 3) (Fin 3) ℂ) X,
      Uᴴ * U = 1 → F (U * X) = F X)
    (hright : ∀ X (A : Matrix (Fin 2) (Fin 2) ℂ),
      IsUnit A → F (X * A) = Aᴴ * F X * A) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ X, F X = (c : ℂ) • (Xᴴ * X) := by
  obtain ⟨c, hc⟩ :=
    continuous_equivariant_hermitian_record_eq_gram
      F hcont hherm hleft hright
  have hscalar :
      ((c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
    rw [← colorStandardFrame_isometry, ← hc colorStandardFrame]
    exact hpos colorStandardFrame
  have hcomplex : (0 : ℂ) ≤ (c : ℂ) := by
    simpa [Matrix.smul_apply, Matrix.one_apply] using
      (hscalar.diag_nonneg (i := (0 : Fin 2)))
  exact ⟨c, RCLike.ofReal_nonneg.mp hcomplex, hc⟩

/-- A nonzero positive equivariant record has a strictly positive Gram scalar. -/
theorem continuous_equivariant_nonzero_positive_record_eq_pos_gram
    (F : ColorEventMatrix → Matrix (Fin 2) (Fin 2) ℂ)
    (hcont : Continuous F)
    (hherm : ∀ X, (F X).IsHermitian)
    (hpos : ∀ X, (F X).PosSemidef)
    (hnonzero : ∃ X, F X ≠ 0)
    (hleft : ∀ (U : Matrix (Fin 3) (Fin 3) ℂ) X,
      Uᴴ * U = 1 → F (U * X) = F X)
    (hright : ∀ X (A : Matrix (Fin 2) (Fin 2) ℂ),
      IsUnit A → F (X * A) = Aᴴ * F X * A) :
    ∃ c : ℝ, 0 < c ∧ ∀ X, F X = (c : ℂ) • (Xᴴ * X) := by
  obtain ⟨c, hc0, hc⟩ :=
    continuous_equivariant_positive_record_eq_nonneg_gram
      F hcont hherm hpos hleft hright
  have hcne : c ≠ 0 := by
    intro hczero
    obtain ⟨X, hX⟩ := hnonzero
    apply hX
    simpa [hczero] using hc X
  exact ⟨c, lt_of_le_of_ne hc0 (Ne.symm hcne), hc⟩

end GaloisForLFunctions.HTGeometry
