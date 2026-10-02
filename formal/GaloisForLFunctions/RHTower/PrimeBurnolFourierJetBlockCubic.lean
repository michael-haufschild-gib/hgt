import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetCellCubic

/-!
# Full-cubic linearization on Fourier channel blocks

The complete cubic has an exact scaled increment and a first-order limit, with its
quadratic remainder retained. Scalar two-channel polarization acts on arbitrary
finite depth blocks; the surviving skew block is computed exactly.
-/

open Complex Filter Topology Matrix
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

def burnolJetCubicLinearTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q K : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (Q-P)^2*K+(Q-P)*K*(Q-P)+K*(Q-P)^2

def burnolJetCubicQuadraticTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q K : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (Q-P)*K^2+K*(Q-P)*K+K^2*(Q-P)

theorem burnolJetCubic_scaled_increment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q K : Matrix ι ι ℂ) {s : ℂ} (hs : s≠0) :
    s • cubicProjectionAssociatorAlgebra (Q+s⁻¹ • K) Q P=
      burnolJetCubicLinearTerm P Q K+s⁻¹ • burnolJetCubicQuadraticTerm P Q K := by
  rw [burnolJetCubic_increment]
  simp only [burnolJetCubicLinearTerm,burnolJetCubicQuadraticTerm,pow_two,
    Matrix.mul_smul,Matrix.smul_mul,smul_add,smul_smul,mul_inv_cancel₀ hs,
    show s*(s⁻¹*s⁻¹)=s⁻¹ by field_simp,one_smul]
  abel

theorem burnolJetCubic_scaled_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : Matrix ι ι ℂ) (R : ℕ → Matrix ι ι ℂ) (s : ℕ → ℂ) (K : Matrix ι ι ℂ)
    (hs : ∀ n, s n≠0) (hinv : Tendsto (fun n => (s n)⁻¹) atTop (𝓝 0))
    (hK : Tendsto (fun n => s n • (R n-Q)) atTop (𝓝 K)) :
    Tendsto (fun n => s n • cubicProjectionAssociatorAlgebra (R n) Q P) atTop
      (𝓝 (burnolJetCubicLinearTerm P Q K)) := by
  have hlin : Continuous (burnolJetCubicLinearTerm P Q) := by
    unfold burnolJetCubicLinearTerm
    exact ((continuous_const.mul continuous_id).add
      ((continuous_const.mul continuous_id).mul continuous_const)).add
        (continuous_id.mul continuous_const)
  have hquad : Continuous (burnolJetCubicQuadraticTerm P Q) := by
    unfold burnolJetCubicQuadraticTerm
    exact ((continuous_const.mul (continuous_id.pow 2)).add
      ((continuous_id.mul continuous_const).mul continuous_id)).add
        ((continuous_id.pow 2).mul continuous_const)
  have h := (hlin.tendsto K |>.comp hK).add (hinv.smul (hquad.tendsto K |>.comp hK))
  rw [zero_smul,add_zero] at h
  apply h.congr'
  filter_upwards with n
  have he : R n=Q+(s n)⁻¹ • (s n • (R n-Q)) := by
    rw [smul_smul,inv_mul_cancel₀ (hs n),one_smul]
    abel
  have hh := burnolJetCubic_scaled_increment P Q (s n • (R n-Q)) (hs n)
  rw [← he] at hh
  exact hh.symm

def burnolJetBlockPolarization (N : ℕ) (u w : ℂ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ :=
  Matrix.fromBlocks (u • 1) (w • 1) (w • 1) ((1-u) • 1)

def burnolJetBlockSkew {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ := Matrix.fromBlocks 0 D (-D) 0

def burnolJetBlockDiagonal {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ := Matrix.fromBlocks D 0 0 D

def burnolJetBlockCross {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ := Matrix.fromBlocks 0 D D 0

theorem burnolJetBlockPolarization_actual (N : ℕ) (p : Nat.Primes) (a : ℝ) :
    burnolJetThetaMatrix N p a=burnolJetBlockPolarization N ((primeBurnolThetaVisibility a p : ℂ)^2)
      ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)) := by
  have h : (primeBurnolThetaVisibility a p : ℂ)^2+(primeBurnolThetaContrast a p : ℂ)^2=1 :=
    by exact_mod_cast primeBurnolThetaVisibility_sq_add_contrast_sq a p
  unfold burnolJetThetaMatrix burnolJetBlockPolarization
  congr 2
  linear_combination h

theorem burnolJetBlockPolarization_diagonal_commute {N : ℕ} (u w : ℂ) (G : Matrix (Fin N) (Fin N) ℂ) :
    burnolJetBlockPolarization N u w*burnolJetBlockDiagonal G=
      burnolJetBlockDiagonal G*burnolJetBlockPolarization N u w := by
  simp only [burnolJetBlockPolarization,burnolJetBlockDiagonal,Matrix.fromBlocks_multiply,
    Matrix.mul_smul,Matrix.smul_mul,mul_one,one_mul,mul_zero,zero_mul,add_zero,zero_add]

theorem burnolJetBlockPolarization_cross_commutator {N : ℕ} (u w : ℂ)
    (H : Matrix (Fin N) (Fin N) ℂ) :
    burnolJetBlockPolarization N u w*burnolJetBlockCross H-
      burnolJetBlockCross H*burnolJetBlockPolarization N u w=(2*u-1) • burnolJetBlockSkew H := by
  ext (i|i) (j|j) <;>
    simp [burnolJetBlockPolarization,burnolJetBlockCross,burnolJetBlockSkew,Matrix.fromBlocks_multiply] <;> ring

theorem burnolJetBlockDiagonal_mul_skew {N : ℕ} (G H : Matrix (Fin N) (Fin N) ℂ) :
    burnolJetBlockDiagonal G*burnolJetBlockSkew H=burnolJetBlockSkew (G*H) := by
  simp [burnolJetBlockDiagonal,burnolJetBlockSkew,Matrix.fromBlocks_multiply]

theorem burnolJetBlockSkew_isUnit {N : ℕ} (D : Matrix (Fin N) (Fin N) ℂ) (hD : IsUnit D) :
    IsUnit (burnolJetBlockSkew D) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hD
  refine ⟨⟨burnolJetBlockSkew D,-burnolJetBlockSkew D⁻¹,?_,?_⟩,rfl⟩
  · simp [burnolJetBlockSkew,Matrix.fromBlocks_multiply,Matrix.fromBlocks_neg,
      Matrix.mul_nonsing_inv D hd,Matrix.fromBlocks_one]
  · simp [burnolJetBlockSkew,Matrix.fromBlocks_multiply,Matrix.fromBlocks_neg,
      Matrix.nonsing_inv_mul D hd,Matrix.fromBlocks_one]

theorem burnolJetBlockDifference_eq (N : ℕ) (u w : ℂ) :
    burnolJetBlockPolarization N u w-burnolJetNeutralMatrix N=
      Matrix.fromBlocks ((u-1) • 1) (w • 1) (w • 1) ((1-u) • 1) := by
  ext (i|i) (j|j) <;>
    simp [burnolJetBlockPolarization,burnolJetNeutralMatrix,sub_mul]

theorem burnolJetBlockDifference_sq {N : ℕ} {u w : ℂ} (hw : w^2=u*(1-u)) :
    (burnolJetBlockPolarization N u w-burnolJetNeutralMatrix N)^2=
      (1-u) • (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ) := by
  rw [burnolJetBlockDifference_eq,pow_two,Matrix.fromBlocks_multiply]
  ext (i|i) (j|j) <;>
    simp [Matrix.one_apply] <;>
    split_ifs <;> (try simp_all) <;> ring_nf <;> linear_combination hw

theorem burnolJetBlockDifference_skew {N : ℕ} (u w : ℂ) (H : Matrix (Fin N) (Fin N) ℂ) :
    (burnolJetBlockPolarization N u w-burnolJetNeutralMatrix N)*burnolJetBlockSkew H=
      -(burnolJetBlockSkew H*(burnolJetBlockPolarization N u w-burnolJetNeutralMatrix N)) := by
  rw [burnolJetBlockDifference_eq]
  ext (i|i) (j|j) <;>
    simp [burnolJetBlockSkew,Matrix.fromBlocks_multiply] <;> ring

theorem burnolJetCubicLinearTerm_block_skew {N : ℕ} {u w : ℂ} (hw : w^2=u*(1-u))
    (H : Matrix (Fin N) (Fin N) ℂ) (k : ℂ) :
    burnolJetCubicLinearTerm (burnolJetNeutralMatrix N) (burnolJetBlockPolarization N u w)
      (k • burnolJetBlockSkew H)=(k*(1-u)) • burnolJetBlockSkew H := by
  have hmid : (burnolJetBlockPolarization N u w-burnolJetNeutralMatrix N)*burnolJetBlockSkew H*
      (burnolJetBlockPolarization N u w-burnolJetNeutralMatrix N)=-(1-u) • burnolJetBlockSkew H := by
    rw [burnolJetBlockDifference_skew,neg_mul,mul_assoc,← pow_two,
      burnolJetBlockDifference_sq hw,Matrix.mul_smul,mul_one,neg_smul]
  simp only [burnolJetCubicLinearTerm,burnolJetBlockDifference_sq hw,
    Matrix.smul_mul,Matrix.mul_smul,mul_one,one_mul,hmid,smul_smul]
  module

end RHTower
