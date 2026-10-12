import GaloisForLFunctions.RHTower.PaperHeatHankelOperator
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminantSignLaw
import GaloisForLFunctions.HTGeometry.HilbertSchmidtBlockEigenvector

/-! # Finite sections retain the heat-Hankel inertia

Positive source scaling preserves the exact inertia of each native moment
section. The finite operators converge to the full signed operator in norm.
-/

namespace RHTower.PaperHeatHankel
noncomputable section
open Filter Topology Matrix GaloisForLFunctions.HTGeometry

/-- The literal prime-minus-Gamma moments retain the required polar correction. -/
theorem kernel_eq_archPrime (a : Time) (i j : ℕ) :
    kernel a (i,j) = (scale a i : ℂ) *
      (archPrimeMoment (i + j) a.val +
        2 * (-1 / 4 : ℂ) ^ (i + j) * Complex.exp ((a.val : ℂ) / 4)) * (scale a j : ℂ) := by
  rw [kernel, archPrimeMoment_eq a.property]
  ring

def sectionMatrix (a : Time) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => kernel a (i.val,j.val)

def sectionScale (a : Time) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => (scale a i.val : ℂ)

theorem sectionScale_isUnit (a : Time) (N : ℕ) : IsUnit (sectionScale a N) := by
  rw [Matrix.isUnit_iff_isUnit_det, sectionScale, Matrix.det_diagonal, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => Complex.ofReal_ne_zero.mpr (scale_pos a i.val).ne'

theorem sectionMatrix_congruence (a : Time) (N : ℕ) :
    sectionMatrix a N = Matrix.conjTranspose (sectionScale a N) *
      heatMomentSection a.val N * sectionScale a N := by
  ext i j
  simp only [sectionMatrix, sectionScale, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply, Complex.star_def,
    Complex.conj_ofReal]
  change (scale a i.val : ℂ) * xiHeatMoment (i.val + j.val) a.val * (scale a j.val : ℂ) =
    (scale a i.val : ℂ) * ((heatMomentArray a.val i.val j.val : ℝ) : ℂ) * (scale a j.val : ℂ)
  congr 2
  exact Complex.ext (by simp [heatMomentArray]) (by simp [im_xiHeatMoment])

theorem sectionMatrix_negativeIndex (a : Time) (N : ℕ) :
    hermNegIndex (sectionMatrix a N) = hermNegIndex (heatMomentSection a.val N) := by
  exact (congrArg hermNegIndex (sectionMatrix_congruence a N)).trans
    (negIndex_conjugate _ (sectionScale_isUnit a N))

theorem sectionMatrix_positiveIndex (a : Time) (N : ℕ) :
    hermPosIndex (sectionMatrix a N) = hermPosIndex (heatMomentSection a.val N) := by
  exact (congrArg hermPosIndex (sectionMatrix_congruence a N)).trans
    (posIndex_conjugate _ (sectionScale_isUnit a N))

theorem sectionMatrix_nullIndex (a : Time) (N : ℕ) :
    hermNullIndex (sectionMatrix a N) = hermNullIndex (heatMomentSection a.val N) := by
  exact (congrArg hermNullIndex (sectionMatrix_congruence a N)).trans
    (nullIndex_conjugate _ (sectionScale_isUnit a N))

theorem sectionMatrix_negativeIndex_stabilizes (a : Time) (hU : xiUpperFrequencies.Finite) :
    ∃ N₀, ∀ N ≥ N₀, hermNegIndex (sectionMatrix a N) = hU.toFinset.card := by
  simpa only [sectionMatrix_negativeIndex] using
    exists_hermNegIndex_heatMomentSection_eq a.property hU

theorem sectionMatrix_negativeIndex_unbounded (a : Time) (hU : xiUpperFrequencies.Infinite)
    (n : ℕ) : ∃ N₀, ∀ N ≥ N₀, n ≤ hermNegIndex (sectionMatrix a N) := by
  simpa only [sectionMatrix_negativeIndex] using
    exists_le_hermNegIndex_heatMomentSection_of_infinite a.property hU n

/-- Compactness permits arbitrarily many negative directions; bounded section
inertia is exactly finiteness of the off-line frequency set. -/
theorem sectionMatrix_index_bounded_iff_finite (a : Time) :
    (∃ B : ℕ, ∀ N, hermNegIndex (sectionMatrix a N) ≤ B) ↔ xiUpperFrequencies.Finite := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hU
    obtain ⟨N₀, hN₀⟩ := sectionMatrix_negativeIndex_unbounded a hU (B + 1)
    have h := hN₀ N₀ le_rfl
    have hb := hB N₀
    omega
  · intro hU
    refine ⟨hU.toFinset.card, fun N => ?_⟩
    rw [sectionMatrix_negativeIndex]
    exact hermNegIndex_heatMomentSection_le a.property hU N

def cutoff (a : Time) (s : Finset ℕ) : Space →L[ℂ] Space :=
  HilbertSchmidt.toOperator (HilbertSchmidt.isHS_truncKernel (kernel_isHS a) s)

theorem cutoff_single (a : Time) (s : Finset ℕ) (i j : ℕ) :
    cutoff a s (lp.single 2 j (1 : ℂ)) i =
      if i ∈ s ∧ j ∈ s then kernel a (i,j) else 0 :=
  HilbertSchmidt.toOperator_single _ _ _

theorem cutoff_hs_tendsto (a : Time) :
    Tendsto (fun s : Finset ℕ => HilbertSchmidt.hsNorm
      (kernel a - HilbertSchmidt.truncKernel (kernel a) s)) atTop (𝓝 0) :=
  HilbertSchmidt.tendsto_hsNorm_sub_truncKernel (kernel_isHS a)

theorem cutoff_norm_tendsto (a : Time) : Tendsto (cutoff a) atTop (𝓝 (operator a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact HilbertSchmidt.tendsto_norm_toOperator_truncKernel_sub (kernel_isHS a)

theorem cutoff_traceCost (a : Time) (s : Finset ℕ) : compactOperatorTraceCost Space (cutoff a s) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr
    (HilbertSchmidt.isHilbertSchmidt_toOperator _).isCompactOperator

end
end RHTower.PaperHeatHankel
