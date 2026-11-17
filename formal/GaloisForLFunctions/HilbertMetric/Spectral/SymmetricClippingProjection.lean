import GaloisForLFunctions.HilbertMetric.Spectral.SymmetricClipping

/-!
# Frobenius projection onto a two-sided spectral interval

Symmetric clipping minimizes the Frobenius distance over all Hermitian
matrices between `-c I` and `c I`. The variational inequality also yields
a Pythagorean remainder, so the bound controls competing approximations.
-/

open Matrix RiemannGaussian.HermitianRankTrace
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.SymmetricClipping
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem trace_pair_specMap {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (B : Matrix ι ι ℂ) (f : ℝ → ℝ) :
    (trace (B * specMap hA f)).re =
      ∑ i, ((star (hA.eigenvectorUnitary : Matrix ι ι ℂ) * B *
        (hA.eigenvectorUnitary : Matrix ι ι ℂ)) i i).re * f (hA.eigenvalues i) := by
  rw [specMap, Unitary.conjStarAlgAut_apply, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp [← Matrix.mul_assoc, Matrix.mul_diagonal, trace, diag]

/-- The residual pairs nonpositively with every admissible displacement. -/
theorem matrix_variational {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (c : ℝ≥0)
    (hupper : (((c : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - B).PosSemidef)
    (hlower : (B - ((-(c : ℝ)) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef) :
    (trace ((B - matrix hA c) * (A - matrix hA c))).re ≤ 0 := by
  let V := hA.eigenvectorUnitary
  let T : Matrix ι ι ℂ := star (V : Matrix ι ι ℂ) * B * (V : Matrix ι ι ℂ)
  have hu : (((c : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - T).PosSemidef := by
    have h := hupper.conjTranspose_mul_mul_same (V : Matrix ι ι ℂ)
    simpa only [← star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Unitary.coe_star_mul_self, T] using h
  have hl : (T - ((-(c : ℝ)) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := by
    have h := hlower.conjTranspose_mul_mul_same (V : Matrix ι ι ℂ)
    simpa only [← star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Unitary.coe_star_mul_self, T] using h
  have hb (i : ι) : |(T i i).re| ≤ c := by
    have h₁ := (Complex.nonneg_iff.mp (hu.diag_nonneg (i := i))).1
    have h₂ := (Complex.nonneg_iff.mp (hl.diag_nonneg (i := i))).1
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, Complex.sub_re, Complex.neg_re, Complex.ofReal_re] at h₁ h₂
    exact abs_le.mpr ⟨by linarith only [h₂], by linarith only [h₁]⟩
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, error_eq_specMap,
    trace_pair_specMap, matrix, ← specMap_mul]
  change (∑ i, (T i i).re * (hA.eigenvalues i - clip c (hA.eigenvalues i))) -
    rtrace (specMap hA (clip c * (id - clip c))) ≤ 0
  rw [rtrace_specMap, ← Finset.sum_sub_distrib]
  apply Finset.sum_nonpos
  intro i _
  have h := clip_variational c (hA.eigenvalues i) (hb i)
  dsimp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  nlinarith only [h]

private theorem frobSq_sub {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    frobSq (A - B) = frobSq A + frobSq B - 2 * (trace (B * A)).re := by
  unfold frobSq
  rw [(hA.sub hB).eq, hA.eq, hB.eq]
  change (trace ((A - B) * (A - B))).re =
    (trace (A * A)).re + (trace (B * B)).re - 2 * (trace (B * A)).re
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [Matrix.trace_mul_comm A B]
  ring

/-- Every bounded Hermitian competitor pays its squared distance from the clip. -/
theorem matrix_pythagorean {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (c : ℝ≥0)
    (hupper : (((c : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - B).PosSemidef)
    (hlower : (B - ((-(c : ℝ)) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef) :
    frobSq (A - matrix hA c) + frobSq (B - matrix hA c) ≤ frobSq (A - B) := by
  have h := matrix_variational hA c hupper hlower
  have he : A - B = (A - matrix hA c) - (B - matrix hA c) := by abel
  rw [he, frobSq_sub (hA.sub (matrix_hermitian hA c))
    (hB.sub (matrix_hermitian hA c))]
  linarith only [h]

/-- Symmetric clipping is a best approximation in squared Frobenius distance. -/
theorem matrix_nearest {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (c : ℝ≥0)
    (hupper : (((c : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - B).PosSemidef)
    (hlower : (B - ((-(c : ℝ)) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef) :
    frobSq (A - matrix hA c) ≤ frobSq (A - B) := by
  have h := matrix_pythagorean hA hB c hupper hlower
  have hn : 0 ≤ frobSq (B - matrix hA c) := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues (hB.sub (matrix_hermitian hA c))]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith only [h, hn]

/-- Matrix clipping is firmly nonexpansive in the Frobenius inner product. -/
theorem matrix_firm {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (c : ℝ≥0) :
    frobSq (matrix hA c - matrix hB c) ≤
      (trace ((matrix hA c - matrix hB c) * (A - B))).re := by
  have ha := matrix_variational hA c (matrix_bounds hB c).1 (matrix_bounds hB c).2
  have hb := matrix_variational hB c (matrix_bounds hA c).1 (matrix_bounds hA c).2
  rw [frobSq, ((matrix_hermitian hA c).sub (matrix_hermitian hB c)).eq]
  change (trace ((matrix hA c - matrix hB c) * (matrix hA c - matrix hB c))).re ≤ _
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at ha hb ⊢
  rw [Matrix.trace_mul_comm (matrix hB c) (matrix hA c)] at ha ⊢
  linarith only [ha, hb]

/-- Spectral clipping never increases the Frobenius distance between two inputs. -/
theorem matrix_nonexpansive {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (c : ℝ≥0) :
    frobSq (matrix hA c - matrix hB c) ≤ frobSq (A - B) := by
  have hf := matrix_firm hA hB c
  have hd := (matrix_hermitian hA c).sub (matrix_hermitian hB c)
  have he := (hA.sub hB).sub hd
  have hn : 0 ≤ frobSq ((A - B) - (matrix hA c - matrix hB c)) := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues he]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [frobSq_sub (hA.sub hB) hd] at hn
  linarith only [hf, hn]

#print axioms matrix_variational
#print axioms matrix_pythagorean
#print axioms matrix_nearest
#print axioms matrix_firm
#print axioms matrix_nonexpansive

end
end GaloisForLFunctions.HilbertMetric.SymmetricClipping
