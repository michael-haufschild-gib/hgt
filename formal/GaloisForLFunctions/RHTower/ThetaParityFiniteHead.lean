import GaloisForLFunctions.RHTower.ThetaQuotientParityFeedback
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Physical theta parity heads

The literal even/odd Fourier matrices retain the directed column feedback.
Their eigenvalues lie in the operator-norm disk of the actual quotient operator,
uniformly in the head size. The proof uses exact Fourier pairings and does not
assert self-adjointness.
-/

open MeasureTheory Matrix
open scoped BigOperators InnerProductSpace
namespace RHTower
noncomputable section
local notation "H" => Lp ℂ 2 unitIntervalMeasure

/-- Literal even/odd Fourier head, retaining the directed column feedback. -/
def thetaParityHead (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks 0
    (fun m n => ((thetaCdfCosineGram (m + 1) (n + 1) - cdfAction (n + 1)) /
      (Real.pi * (n + 1)) : ℝ))
    (fun m n => (thetaCdfSineGram (m + 1) (n + 1) / (Real.pi * (n + 1)) : ℝ)) 0

/-- Unnormalized physical parity modes; their exact Gram matrix is `2I`. -/
def thetaParityHeadMode (N : ℕ) : Fin N ⊕ Fin N → H
  | Sum.inl n => unitFourierBasis (n + 1) + (1 : ℂ) • unitFourierBasis (-(n + 1))
  | Sum.inr n => unitFourierBasis (n + 1) + (-1 : ℂ) • unitFourierBasis (-(n + 1))

private theorem inner_positive_fourier_pair (m n : ℕ) (e d : ℝ) :
    inner ℂ (unitFourierBasis (m + 1) + (e : ℂ) • unitFourierBasis (-(m + 1)))
      (unitFourierBasis (n + 1) + (d : ℂ) • unitFourierBasis (-(n + 1))) =
      if m = n then (1 + (e : ℂ) * d) else 0 := by
  have hmn : ((m : ℤ) + 1 = (n : ℤ) + 1) ↔ m = n := by omega
  have h1 : (m : ℤ) + 1 ≠ -((n : ℤ) + 1) := by omega
  have h2 : -((m : ℤ) + 1) ≠ (n : ℤ) + 1 := by omega
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, inner_unitFourierBasis, hmn, h1, h2, if_false, neg_inj]
  split_ifs <;> ring

theorem inner_thetaParityHeadMode (N : ℕ) (i j : Fin N ⊕ Fin N) :
    inner ℂ (thetaParityHeadMode N i) (thetaParityHeadMode N j) = if i = j then 2 else 0 := by
  rcases i with i | i <;> rcases j with j | j
  · simpa [thetaParityHeadMode, Fin.ext_iff, show (1 : ℂ) + 1 = 2 by norm_num] using inner_positive_fourier_pair (i : ℕ) (j : ℕ) 1 1
  · simpa [thetaParityHeadMode] using inner_positive_fourier_pair (i : ℕ) (j : ℕ) 1 (-1)
  · simpa [thetaParityHeadMode] using inner_positive_fourier_pair (i : ℕ) (j : ℕ) (-1) 1
  · simpa [thetaParityHeadMode, Fin.ext_iff, show (1 : ℂ) + 1 = 2 by norm_num] using inner_positive_fourier_pair (i : ℕ) (j : ℕ) (-1) (-1)

theorem inner_thetaParityHead (N : ℕ) (i j : Fin N ⊕ Fin N) :
    inner ℂ (thetaParityHeadMode N i) (thetaQuotientOperator (thetaParityHeadMode N j)) =
      2 * thetaParityHead N i j := by
  rcases i with i | i <;> rcases j with j | j
  · have h := thetaQuotient_fourier_parity_pairing
      (m := (i : ℤ) + 1) (n := (j : ℤ) + 1) (by omega) (by omega) 1 1
    simpa [thetaParityHeadMode, thetaParityHead] using h
  · have h := thetaQuotient_fourier_parity_pairing
      (m := (i : ℤ) + 1) (n := (j : ℤ) + 1) (by omega) (by omega) 1 (-1)
    change inner ℂ (unitFourierBasis _ + _ • unitFourierBasis _)
      (thetaQuotientOperator (unitFourierBasis _ + _ • unitFourierBasis _)) =
      2 * (((thetaCdfCosineGram ((i : ℤ) + 1) ((j : ℤ) + 1) - cdfAction ((j : ℤ) + 1)) /
        (Real.pi * ((j : ℝ) + 1)) : ℝ) : ℂ)
    rw [show (j : ℝ) + 1 = (((j : ℤ) + 1 : ℤ) : ℝ) by push_cast; rfl,
      ← cdfQuotientMatrix_parity_sub]
    push_cast
    convert h using 1 <;> norm_num; ring
  · have h := thetaQuotient_fourier_parity_pairing
      (m := (i : ℤ) + 1) (n := (j : ℤ) + 1) (by omega) (by omega) (-1) 1
    change inner ℂ (unitFourierBasis _ + _ • unitFourierBasis _)
      (thetaQuotientOperator (unitFourierBasis _ + _ • unitFourierBasis _)) =
      2 * ((thetaCdfSineGram ((i : ℤ) + 1) ((j : ℤ) + 1) /
        (Real.pi * ((j : ℝ) + 1)) : ℝ) : ℂ)
    rw [show (j : ℝ) + 1 = (((j : ℤ) + 1 : ℤ) : ℝ) by push_cast; rfl,
      ← cdfQuotientMatrix_parity_sum]
    push_cast
    convert h using 1 <;> norm_num; ring
  · have h := thetaQuotient_fourier_parity_pairing
      (m := (i : ℤ) + 1) (n := (j : ℤ) + 1) (by omega) (by omega) (-1) (-1)
    simpa [thetaParityHeadMode, thetaParityHead] using h

private theorem norm_finite_compression_eigenvalue_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : E →L[ℂ] E) (v : ι → E) (A : Matrix ι ι ℂ)
    (hg : ∀ i j, inner ℂ (v i) (v j) = if i = j then 2 else 0)
    (ha : ∀ i j, inner ℂ (v i) (T (v j)) = 2 * A i j)
    {x : ι → ℂ} (hx : x ≠ 0) {z : ℂ} (he : A *ᵥ x = z • x) : ‖z‖ ≤ ‖T‖ := by
  let f : E := ∑ i, x i • v i
  have hi (i : ι) : inner ℂ (v i) f = 2 * x i := by
    simp [f, hg, mul_comm]
  have hf : f ≠ 0 := by
    intro hf
    apply hx
    funext i
    have h := hi i
    rw [hf, inner_zero_right] at h
    change x i = 0
    exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)
  have hTi (i : ι) : inner ℂ (v i) (T f) = 2 * (z * x i) := by
    have he' := congrFun he i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at he'
    calc
      inner ℂ (v i) (T f) = ∑ j, x j * (2 * A i j) := by
        simp only [f, map_sum, map_smul, inner_sum, inner_smul_right, ha]
      _ = 2 * (∑ j, A i j * x j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      _ = 2 * (z * x i) := by rw [he']
  have hs (g : E) : inner ℂ f g = ∑ i, (starRingEnd ℂ) (x i) * inner ℂ (v i) g := by
    simp only [f, sum_inner, inner_smul_left]
  have hr : inner ℂ f (T f) = z * inner ℂ f f := by
    rw [hs (T f), hs f, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hTi, hi]
    ring
  have heq : ‖z‖ * ‖f‖ ^ 2 = ‖inner ℂ f (T f)‖ := by
    rw [hr, norm_mul, inner_self_eq_norm_sq_to_K, norm_pow]
    simp
  have hbound : ‖z‖ * ‖f‖ ^ 2 ≤ ‖T‖ * ‖f‖ ^ 2 := by
    calc
      ‖z‖ * ‖f‖ ^ 2 = ‖inner ℂ f (T f)‖ := heq
      _ ≤ ‖f‖ * ‖T f‖ := norm_inner_le_norm _ _
      _ ≤ ‖f‖ * (‖T‖ * ‖f‖) := mul_le_mul_of_nonneg_left (T.le_opNorm f) (norm_nonneg _)
      _ = ‖T‖ * ‖f‖ ^ 2 := by ring
  exact le_of_mul_le_mul_right hbound (sq_pos_of_pos (norm_pos_iff.mpr hf))

/-- Uniform physical spectral bound, independent of the size of the Fourier head. -/
theorem norm_thetaParityHead_eigenvalue_le (N : ℕ) {x : (Fin N ⊕ Fin N) → ℂ}
    (hx : x ≠ 0) {z : ℂ} (he : thetaParityHead N *ᵥ x = z • x) :
    ‖z‖ ≤ ‖thetaQuotientOperator‖ :=
  norm_finite_compression_eigenvalue_le thetaQuotientOperator (thetaParityHeadMode N)
    (thetaParityHead N) (inner_thetaParityHeadMode N) (inner_thetaParityHead N) hx he

theorem norm_thetaParityHead_root_le (N : ℕ) {z : ℂ}
    (hz : (thetaParityHead N).charpoly.IsRoot z) : ‖z‖ ≤ ‖thetaQuotientOperator‖ := by
  have hh : Module.End.HasEigenvalue (thetaParityHead N).mulVecLin z :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly (thetaParityHead N).mulVecLin z).mpr (by
      simpa only [Matrix.charpoly_mulVecLin] using hz)
  obtain ⟨x, hx⟩ := hh.exists_hasEigenvector
  exact norm_thetaParityHead_eigenvalue_le N hx.2 hx.apply_eq_smul

end
end RHTower
