import GaloisForLFunctions.HeckeKreinToeplitz.KernelsOnGroupsAndTheirNegativeIndex
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanDefectCountsTheOuterEigenvalues
import GaloisForLFunctions.HTGeometry.ReductionPencilKPositivity

/-!
# Weighted compressions of group Gram matrices

Block weights define rectangular matrix compressions. They preserve positivity, never
increase negative index, and admit explicit double-sum entries.
-/

open Complex Matrix Finset
open scoped ComplexConjugate Classical ComplexOrder
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {G ι J : Type*} [Group G] [Fintype ι] [Fintype J]

/-- A rectangular matrix assigning the same weights to each disjoint block. -/
def kernelBlockWeights (w : J → ℂ) : Matrix (ι × J) ι ℂ :=
  fun p i => if p.1 = i then w p.2 else 0

/-- The Gram matrix obtained by combining each block with the prescribed weights. -/
def weightedKernelGram (k : G → ℂ) (x : ι × J → G) (w : J → ℂ) : Matrix ι ι ℂ :=
  (kernelBlockWeights (ι := ι) w)ᴴ * gram k x * kernelBlockWeights (ι := ι) w

/-- A weighted Gram entry is the sesquilinear double average of its kernel entries. -/
theorem weightedKernelGram_apply (k : G → ℂ) (x : ι × J → G) (w : J → ℂ) (a b : ι) :
    weightedKernelGram k x w a b =
      ∑ i, ∑ j, conj (w i) * w j * k ((x (a, i))⁻¹ * x (b, j)) := by
  have hleft (p : ι × J) :
      ((kernelBlockWeights (ι := ι) w)ᴴ * gram k x) a p =
        ∑ i, conj (w i) * k ((x (a, i))⁻¹ * x p) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Matrix.conjTranspose_apply, kernelBlockWeights, Complex.star_def,
      gram, apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [weightedKernelGram, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [hleft, kernelBlockWeights, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Orthogonal unit columns give the squared norm of their weights on the diagonal. -/
theorem weightedKernelGram_diagonal_of_orthonormal (k : G → ℂ)
    (x : ι × J → G) (w : J → ℂ) (a : ι)
    (h : ∀ i j, k ((x (a, i))⁻¹ * x (a, j)) = if i = j then 1 else 0) :
    weightedKernelGram k x w a a = ((∑ j, normSq (w j) : ℝ) : ℂ) := by
  rw [weightedKernelGram_apply]
  simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true,
    ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum]

/-- Rectangular Gram compression cannot increase the kernel's negative index. -/
theorem hermNegIndex_weightedKernelGram_le (k : G → ℂ) (x : ι × J → G) (w : J → ℂ) :
    (hermNegIndex (weightedKernelGram k x w) : ℕ∞) ≤ negIndex k :=
  (Nat.cast_le.mpr (negIndex_compress_le (gram k x) (kernelBlockWeights (ι := ι) w))).trans
    (hermNegIndex_gram_le_negIndex k x)

/-- Weighted compression retains Hermitian symmetry. -/
theorem weightedKernelGram_isHermitian {k : G → ℂ} (hk : IsHermKernel k)
    (x : ι × J → G) (w : J → ℂ) : (weightedKernelGram k x w).IsHermitian := by
  change ((kernelBlockWeights (ι := ι) w)ᴴ * gram k x * kernelBlockWeights (ι := ι) w)ᴴ = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, (gram_isHermitian hk x).eq, ← Matrix.mul_assoc]
  rfl

/-- Weighted compression retains positive semidefiniteness. -/
theorem weightedKernelGram_posSemidef {k : G → ℂ} (hk : IsPosDefKernel k)
    (x : ι × J → G) (w : J → ℂ) : (weightedKernelGram k x w).PosSemidef := by
  have hgram : (gram k x).PosSemidef := by
    apply posSemidef_of_matSesq_re_nonneg (gram_isHermitian hk.1 x)
    intro c
    rw [matSesq_eq_dotProduct]
    exact hk.hermQuad_nonneg x c
  exact hgram.conjTranspose_mul_mul_same (kernelBlockWeights (ι := ι) w)

/-- Kernel addition commutes with weighted Gram compression. -/
theorem weightedKernelGram_add (k l : G → ℂ) (x : ι × J → G) (w : J → ℂ) :
    weightedKernelGram (fun g => k g + l g) x w =
      weightedKernelGram k x w + weightedKernelGram l x w := by
  have h : gram (fun g => k g + l g) x = gram k x + gram l x := rfl
  simp only [weightedKernelGram, h, Matrix.mul_add, Matrix.add_mul]

/-- A positive matrix with constant diagonal has every entry bounded by that diagonal. -/
theorem norm_entry_le_constant_posSemidef_diagonal {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ i, A i i = (δ : ℂ)) (i j : ι) : ‖A i j‖ ≤ δ := by
  have he (a b : ι) : matSesq A (Pi.single b 1) (Pi.single a 1) = A a b := by
    simp [matSesq, Pi.single_apply]
  have h := matSesq_norm_sq_le hA (Pi.single j 1) (Pi.single i 1)
  rw [he, he, he, hd, hd, Complex.ofReal_re] at h
  nlinarith only [h, norm_nonneg (A i j), hδ]

#print axioms hermNegIndex_weightedKernelGram_le
#print axioms weightedKernelGram_posSemidef
#print axioms norm_entry_le_constant_posSemidef_diagonal
end GaloisForLFunctions.HeckeKreinToeplitz
