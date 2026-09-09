import Mathlib.Algebra.Order.Archimedean.Real.Hom
import GaloisForLFunctions.HTGeometry.GomesSpecialOrthogonalCommutant
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real linear normalizer of the rotation group

The normalizer is exactly the positive scalar multiples of the orthogonal group in dimension
at least three. Even inclusion of the conjugated group suffices for this classification.

Mechanically extracted from the symmetry-first reconstruction problem in
Gomes, arXiv:2607.24901, Proposition 3 and its normalizer discussion.
https://arxiv.org/abs/2607.24901
-/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Orthogonal conjugation preserves orientation-preserving orthogonal transformations. -/
theorem orthogonal_conjugation_specialOrthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix.orthogonalGroup ι ℝ) (R : Matrix.specialOrthogonalGroup ι ℝ) :
    Q.val * R.val * Q.valᵀ ∈ Matrix.specialOrthogonalGroup ι ℝ := by
  have hQ := ((Matrix.mem_orthogonalGroup_iff _ _).mp Q.property)
  have hQt := ((Matrix.mem_orthogonalGroup_iff' _ _).mp Q.property)
  have hR := (Matrix.mem_specialOrthogonalGroup_iff.mp R.property)
  have hRt := (Matrix.mem_orthogonalGroup_iff' _ _).mp hR.1
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff']
    calc
      (Q.val * R.val * Q.valᵀ)ᵀ * (Q.val * R.val * Q.valᵀ) =
          Q.val * R.valᵀ * (Q.valᵀ * Q.val) * R.val * Q.valᵀ := by
            simp [Matrix.transpose_mul, mul_assoc]
      _ = Q.val * (R.valᵀ * R.val) * Q.valᵀ := by rw [hQt]; simp [mul_assoc]
      _ = 1 := by rw [hRt]; simpa using hQ
  · calc
      (Q.val * R.val * Q.valᵀ).det = (Q.val * Q.valᵀ).det := by
        simp only [Matrix.det_mul,hR.2,mul_one]
      _ = 1 := by rw [hQ,Matrix.det_one]

/-- Normalizing all rotations is equivalent to having a scalar Gram matrix. -/
theorem specialOrthogonal_normalizer_gram (n : ℕ)
    (A : (Matrix (Fin (n+3)) (Fin (n+3)) ℝ)ˣ) :
    (∀ R : Matrix.specialOrthogonalGroup (Fin (n+3)) ℝ,
      A.val * R.val * (A⁻¹).val ∈ Matrix.specialOrthogonalGroup (Fin (n+3)) ℝ) ↔
    A.valᵀ * A.val = (A.valᵀ * A.val) 0 0 •
      (1 : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) := by
  let G := A.valᵀ * A.val
  have hA : A.val * (A⁻¹).val = 1 := A.val_inv
  have hAi : (A⁻¹).val * A.val = 1 := A.inv_val
  have hmetric : (A⁻¹).valᵀ * G * (A⁻¹).val = 1 := by
    calc
      (A⁻¹).valᵀ * G * (A⁻¹).val =
          (A.val * (A⁻¹).val)ᵀ * (A.val * (A⁻¹).val) := by
            simp only [G,Matrix.transpose_mul,mul_assoc]
      _ = 1 := by rw [hA]; simp
  constructor
  · intro h
    apply (specialOrthogonal_matrix_commutant n G).mp
    intro R
    have hR := (Matrix.mem_specialOrthogonalGroup_iff.mp R.property).1
    have hRR := (Matrix.mem_orthogonalGroup_iff _ _).mp hR
    let B := A.val * R.val * (A⁻¹).val
    have hB : Bᵀ * B = 1 :=
      (Matrix.mem_orthogonalGroup_iff' _ _).mp ((Matrix.mem_specialOrthogonalGroup_iff.mp (h R)).1)
    have hBA : B * A.val = A.val * R.val := by
      dsimp [B]
      simp only [mul_assoc,hAi,mul_one]
    have hinv : R.valᵀ * G * R.val = G := by
      calc
        R.valᵀ * G * R.val = (A.val * R.val)ᵀ * (A.val * R.val) := by
          simp [G,Matrix.transpose_mul,mul_assoc]
        _ = (B * A.val)ᵀ * (B * A.val) := by rw [hBA]
        _ = A.valᵀ * (Bᵀ * B) * A.val := by simp [Matrix.transpose_mul,mul_assoc]
        _ = G := by rw [hB]; simp [G]
    calc
      G * R.val = (R.val * R.valᵀ) * G * R.val := by rw [hRR]; simp
      _ = R.val * (R.valᵀ * G * R.val) := by simp [mul_assoc]
      _ = R.val * G := by rw [hinv]
  · intro h R
    change G = G 0 0 • (1 : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) at h
    have hR := Matrix.mem_specialOrthogonalGroup_iff.mp R.property
    have hRt := (Matrix.mem_orthogonalGroup_iff' _ _).mp hR.1
    have hinv : R.valᵀ * G * R.val = G := by
      conv_lhs => rw [h]
      simp only [Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,hRt]
      exact h.symm
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    constructor
    · rw [Matrix.mem_orthogonalGroup_iff']
      calc
        (A.val * R.val * (A⁻¹).val)ᵀ * (A.val * R.val * (A⁻¹).val) =
            (A⁻¹).valᵀ * (R.valᵀ * G * R.val) * (A⁻¹).val := by
              simp [G,Matrix.transpose_mul,mul_assoc]
        _ = 1 := by rw [hinv]; exact hmetric
    · calc
        (A.val * R.val * (A⁻¹).val).det = (A.val * (A⁻¹).val).det := by
          simp only [Matrix.det_mul,hR.2,mul_one]
        _ = 1 := by rw [hA,Matrix.det_one]

/-- An invertible real matrix has scalar Gram matrix exactly when it is a positive homothety
followed by an orthogonal transformation. -/
theorem invertible_scalar_gram_iff_positive_orthogonal (n : ℕ)
    (A : (Matrix (Fin (n+3)) (Fin (n+3)) ℝ)ˣ) :
    A.valᵀ * A.val = (A.valᵀ * A.val) 0 0 •
      (1 : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) ↔
    ∃ r : ℝ, 0 < r ∧ ∃ Q : Matrix.orthogonalGroup (Fin (n+3)) ℝ, A.val = r • Q.val := by
  constructor
  · intro h
    let μ := (A.valᵀ * A.val) 0 0
    have hμn : 0 ≤ μ := by
      dsimp [μ]
      rw [Matrix.mul_apply]
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (A.val i 0))
    have hμ0 : μ ≠ 0 := by
      intro hz
      have hzero : A.valᵀ * A.val = 0 := by
        change A.valᵀ * A.val = μ • (1 : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) at h
        simpa only [hz,zero_smul] using h
      have hd := congrArg Matrix.det hzero
      have ha := (Matrix.isUnits_det_units A).ne_zero
      simp only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_zero] at hd
      exact (mul_ne_zero ha ha) hd
    have hμ : 0 < μ := lt_of_le_of_ne hμn (Ne.symm hμ0)
    let r := Real.sqrt μ
    have hr : 0 < r := Real.sqrt_pos.2 hμ
    have hrsq : r * r = μ := by simpa only [r,pow_two] using Real.sq_sqrt hμn
    have hcancel : r⁻¹ * r⁻¹ * μ = 1 := by rw [← hrsq]; field_simp
    let Q : Matrix (Fin (n+3)) (Fin (n+3)) ℝ := r⁻¹ • A.val
    have hQ : Q ∈ Matrix.orthogonalGroup (Fin (n+3)) ℝ := by
      rw [Matrix.mem_orthogonalGroup_iff']
      change (r⁻¹ • A.val)ᵀ * (r⁻¹ • A.val) = 1
      rw [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,h,smul_smul]
      change (r⁻¹ * r⁻¹ * μ) • (1 : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) = 1
      rw [hcancel,one_smul]
    refine ⟨r,hr,⟨Q,hQ⟩,?_⟩
    change A.val = r • (r⁻¹ • A.val)
    rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hr),one_smul]
  · rintro ⟨r,hr,Q,hQ⟩
    have hQt := (Matrix.mem_orthogonalGroup_iff' _ _).mp Q.property
    have hGram : A.valᵀ * A.val = (r*r) • (1 : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) := by
      rw [hQ,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,hQt]
    rw [hGram]
    simp

/-- The complete real linear normalizer of SO(n+3) is the positive scalar multiples of O(n+3). -/
theorem specialOrthogonal_linear_normalizer (n : ℕ)
    (A : (Matrix (Fin (n+3)) (Fin (n+3)) ℝ)ˣ) :
    (∀ R : Matrix.specialOrthogonalGroup (Fin (n+3)) ℝ,
      A.val * R.val * (A⁻¹).val ∈ Matrix.specialOrthogonalGroup (Fin (n+3)) ℝ) ↔
    ∃ r : ℝ, 0 < r ∧ ∃ Q : Matrix.orthogonalGroup (Fin (n+3)) ℝ, A.val = r • Q.val :=
  (specialOrthogonal_normalizer_gram n A).trans
    (invertible_scalar_gram_iff_positive_orthogonal n A)


/-- Allowing arbitrary real field automorphisms does not enlarge the linear normalizer:
real semilinear reconstruction still gives exactly a positive homothety and an orthogonal map. -/
theorem specialOrthogonal_real_semilinear_normalizer (n : ℕ) (σ : ℝ ≃+* ℝ)
    (A : (Matrix (Fin (n+3)) (Fin (n+3)) ℝ)ˣ) :
    (∀ R : Matrix.specialOrthogonalGroup (Fin (n+3)) ℝ,
      A.val * R.val.map σ * (A⁻¹).val ∈ Matrix.specialOrthogonalGroup (Fin (n+3)) ℝ) ↔
    ∃ r : ℝ, 0 < r ∧ ∃ Q : Matrix.orthogonalGroup (Fin (n+3)) ℝ, A.val = r • Q.val := by
  have hmap (M : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) : M.map σ = M := by
    ext i j
    exact Real.ringHom_apply σ (M i j)
  simpa only [hmap] using specialOrthogonal_linear_normalizer n A

end GaloisForLFunctions.HTGeometry
