import GaloisForLFunctions.HTGeometry.FiniteMatrixOrthogonalSum
import GaloisForLFunctions.HTGeometry.HankelSuccessorSchurStrict
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspAllRankNativeTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedAllOrderIntegration

/-!
# Exact parity transfer for complete signed Hankel heads

An odd-zero moment sequence splits into its unshifted and once-shifted even-moment
heads, including odd full dimensions. The literal complete native reflection source
therefore has a positive-definite full signed head at every fixed rank on a cofinal ray.
-/

noncomputable section

open Filter Topology Matrix

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

/-- Interleave the even moments with their literal odd zeros. -/
def evenMomentSequence (m : ℕ → ℝ) (n : ℕ) : ℝ :=
  if Even n then m (n / 2) else 0

@[simp] theorem evenMomentSequence_even (m : ℕ → ℝ) (k : ℕ) :
    evenMomentSequence m (2 * k) = m k := by
  rw [evenMomentSequence, if_pos (show Even (2 * k) from ⟨k, by omega⟩)]
  congr 1
  omega

@[simp] theorem evenMomentSequence_odd (m : ℕ → ℝ) (k : ℕ) :
    evenMomentSequence m (2 * k + 1) = 0 := by
  apply if_neg
  rintro ⟨j, hj⟩
  omega

/-- Increasing even and odd coordinates give the two parity blocks of a full head. -/
def hankelParityIndex (N : ℕ) :
    Fin ((N + 1) / 2) ⊕ Fin (N / 2) → Fin N
  | Sum.inl i => ⟨2 * i.val, by omega⟩
  | Sum.inr i => ⟨2 * i.val + 1, by omega⟩

private theorem hankelParityIndex_bijective (N : ℕ) :
    Function.Bijective (hankelParityIndex N) := by
  constructor
  · intro a b h
    have hv := congrArg Fin.val h
    rcases a with a | a <;> rcases b with b | b
    · congr 1
      apply Fin.ext
      change 2 * a.val = 2 * b.val at hv
      omega
    · change 2 * a.val = 2 * b.val + 1 at hv
      omega
    · change 2 * a.val + 1 = 2 * b.val at hv
      omega
    · congr 1
      apply Fin.ext
      change 2 * a.val + 1 = 2 * b.val + 1 at hv
      omega
  · intro j
    by_cases hj : j.val % 2 = 0
    · refine ⟨Sum.inl ⟨j.val / 2, by omega⟩, ?_⟩
      apply Fin.ext
      change 2 * (j.val / 2) = j.val
      omega
    · refine ⟨Sum.inr ⟨j.val / 2, by omega⟩, ?_⟩
      apply Fin.ext
      change 2 * (j.val / 2) + 1 = j.val
      omega

/-- Exact parity permutation, valid also for empty and odd-dimensional heads. -/
def hankelParityEquiv (N : ℕ) :
    Fin ((N + 1) / 2) ⊕ Fin (N / 2) ≃ Fin N :=
  Equiv.ofBijective (hankelParityIndex N) (hankelParityIndex_bijective N)

/-- The entire signed head equals the two complete even-moment blocks after reindexing. -/
theorem finiteHankelMatrix_parity (m : ℕ → ℝ) (N : ℕ) :
    (finiteHankelMatrix (evenMomentSequence m) N).submatrix
      (hankelParityEquiv N) (hankelParityEquiv N) =
    matrixOrthogonalSum (finiteHankelMatrix m ((N + 1) / 2))
      (finiteHankelMatrix (fun k => m (k + 1)) (N / 2)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change evenMomentSequence m (2 * i.val + 2 * j.val) = m (i.val + j.val)
    rw [show 2 * i.val + 2 * j.val = 2 * (i.val + j.val) by omega,
      evenMomentSequence_even]
  · change evenMomentSequence m (2 * i.val + (2 * j.val + 1)) = 0
    rw [show 2 * i.val + (2 * j.val + 1) = 2 * (i.val + j.val) + 1 by omega,
      evenMomentSequence_odd]
  · change evenMomentSequence m ((2 * i.val + 1) + 2 * j.val) = 0
    rw [show (2 * i.val + 1) + 2 * j.val = 2 * (i.val + j.val) + 1 by omega,
      evenMomentSequence_odd]
  · change evenMomentSequence m ((2 * i.val + 1) + (2 * j.val + 1)) =
      m (i.val + j.val + 1)
    rw [show (2 * i.val + 1) + (2 * j.val + 1) = 2 * (i.val + j.val + 1) by omega,
      evenMomentSequence_even]

/-- The full determinant retains both parity determinants with no sign factor. -/
theorem det_finiteHankelMatrix_evenMomentSequence (m : ℕ → ℝ) (N : ℕ) :
    (finiteHankelMatrix (evenMomentSequence m) N).det =
      (finiteHankelMatrix m ((N + 1) / 2)).det *
      (finiteHankelMatrix (fun k => m (k + 1)) (N / 2)).det := by
  rw [← Matrix.det_submatrix_equiv_self (hankelParityEquiv N), finiteHankelMatrix_parity,
    matrixOrthogonalSum, Matrix.det_fromBlocks_zero₁₂]

/-- Strictness of a full signed head is exactly strictness of its two parity blocks. -/
theorem finiteHankelMatrix_evenMomentSequence_posDef_iff (m : ℕ → ℝ) (N : ℕ) :
    (finiteHankelMatrix (evenMomentSequence m) N).PosDef ↔
      (finiteHankelMatrix m ((N + 1) / 2)).PosDef ∧
      (finiteHankelMatrix (fun k => m (k + 1)) (N / 2)).PosDef := by
  constructor
  · intro h
    have hs := h.submatrix (hankelParityEquiv N).injective
    rw [finiteHankelMatrix_parity] at hs
    exact ⟨hs.submatrix Sum.inl_injective, hs.submatrix Sum.inr_injective⟩
  · rintro ⟨he, ho⟩
    have hs := matrixOrthogonalSum_posDef he ho
    rw [← finiteHankelMatrix_parity] at hs
    have h := hs.submatrix (hankelParityEquiv N).symm.injective
    have heq : ((finiteHankelMatrix (evenMomentSequence m) N).submatrix
        (hankelParityEquiv N) (hankelParityEquiv N)).submatrix
        (hankelParityEquiv N).symm (hankelParityEquiv N).symm =
        finiteHankelMatrix (evenMomentSequence m) N := by
      ext i j
      simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
    rwa [heq] at h

private theorem orthogonalSum_posSemidef {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (matrixOrthogonalSum A B).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hA.1.fromBlocks (by simp) hB.1, ?_⟩
  intro x
  rw [star_trivial, matrixOrthogonalSum_quadratic]
  exact add_nonneg (by simpa only [star_trivial] using
    hA.dotProduct_mulVec_nonneg (fun i => x (Sum.inl i)))
    (by simpa only [star_trivial] using
    hB.dotProduct_mulVec_nonneg (fun i => x (Sum.inr i)))

/-- Semidefiniteness also splits exactly, including all singular boundary cases. -/
theorem finiteHankelMatrix_evenMomentSequence_posSemidef_iff (m : ℕ → ℝ) (N : ℕ) :
    (finiteHankelMatrix (evenMomentSequence m) N).PosSemidef ↔
      (finiteHankelMatrix m ((N + 1) / 2)).PosSemidef ∧
      (finiteHankelMatrix (fun k => m (k + 1)) (N / 2)).PosSemidef := by
  constructor
  · intro h
    have hs := h.submatrix (hankelParityEquiv N)
    rw [finiteHankelMatrix_parity] at hs
    exact ⟨hs.submatrix Sum.inl, hs.submatrix Sum.inr⟩
  · rintro ⟨he, ho⟩
    have hs := orthogonalSum_posSemidef he ho
    rw [← finiteHankelMatrix_parity] at hs
    exact (Matrix.posSemidef_submatrix_equiv (hankelParityEquiv N)).mp hs

/-- Literal native signed jets are the odd-zero interleaving of the signed even moments. -/
theorem thetaCuspNativeSignedJet_eq_evenMomentSequence (x : ℝ) :
    thetaCuspNativeSignedJet x = evenMomentSequence
      (fun k => (-1 : ℝ) ^ k * thetaCuspNativeReflectionJet (2 * k) x) := by
  funext n
  have hI : (-Complex.I : ℂ) ^ (2 : ℕ) = ((-1 : ℝ) : ℂ) := by norm_num
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    rw [show n = 2 * k by omega, evenMomentSequence_even]
    simp only [thetaCuspNativeSignedJet, pow_mul, hI,
      ← Complex.ofReal_pow, Complex.ofReal_re]
  · obtain ⟨k, hk⟩ := ho
    rw [show n = 2 * k + 1 by omega, evenMomentSequence_odd]
    simp only [thetaCuspNativeSignedJet, pow_add, pow_mul, hI,
      ← Complex.ofReal_pow, pow_one, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.I_re, neg_zero, mul_zero,
      Complex.neg_im, Complex.I_im, zero_mul, sub_zero]

/-- Every fixed full signed Hankel head of the complete native source is eventually strict. -/
theorem nativeSignedHead_posDef_eventually (N : ℕ) :
    ∀ᶠ x : ℝ in atTop, (finiteHankelMatrix (thetaCuspNativeSignedJet x) N).PosDef := by
  filter_upwards [nativeShiftedMatrix_posDef_eventually ((N + 1) / 2) 0,
    nativeShiftedMatrix_posDef_eventually (N / 2) 1] with x he ho
  rw [thetaCuspNativeSignedJet_eq_evenMomentSequence,
    finiteHankelMatrix_evenMomentSequence_posDef_iff]
  exact ⟨he, ho⟩

#print axioms finiteHankelMatrix_parity
#print axioms det_finiteHankelMatrix_evenMomentSequence
#print axioms finiteHankelMatrix_evenMomentSequence_posDef_iff
#print axioms finiteHankelMatrix_evenMomentSequence_posSemidef_iff
#print axioms nativeSignedHead_posDef_eventually

end GaloisForLFunctions.CompletedArithmeticForms
