import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetTwoDepthNormalization
import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetBlockCubic

/-!
# Surviving symbol of the actual two-depth complete cubic

The diagonal Gram block commutes with polarization exactly. The complete modular
increment therefore has a limit determined by the retained Fourier cross block.
Exact cubic linearization yields the skew symbol for every prime and parameter.
-/

open Complex Filter Topology Matrix
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

theorem burnolJetBlockSkew_continuous (N : ℕ) :
    Continuous (@burnolJetBlockSkew N) := by
  exact continuous_const.matrix_fromBlocks continuous_id continuous_id.neg continuous_const

theorem burnolJetBlockSkew_smul {N : ℕ} (s : ℂ) (H : Matrix (Fin N) (Fin N) ℂ) :
    burnolJetBlockSkew (s • H)=s • burnolJetBlockSkew H := by
  ext (i|i) (j|j) <;> simp [burnolJetBlockSkew]

theorem burnolJetBlockDiagonal_inverse {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ)
    (hG : IsUnit G) : (burnolJetBlockDiagonal G)⁻¹=burnolJetBlockDiagonal G⁻¹ := by
  apply Matrix.inv_eq_left_inv
  simp [burnolJetBlockDiagonal,Matrix.fromBlocks_multiply,
    Matrix.nonsing_inv_mul G ((Matrix.isUnit_iff_isUnit_det _).mp hG),Matrix.fromBlocks_one]

theorem primeBurnolTwoDepthNormalizedGram_inv_mul (p : Nat.Primes) (n : ℕ) :
    (primeBurnolTwoDepthNormalizedGram p n)⁻¹*primeBurnolTwoDepthNormalizedGram p n=1 := by
  rw [primeBurnolTwoDepthNormalizedGram_inverse,primeBurnolTwoDepthNormalizedGram_normalize,
    ← coe_primeBurnolFourierJetGramUnit]
  have hl : (primeBurnolLogFrequency (p,n) : ℂ)^3≠0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (primeBurnolLogFrequency_pos (p,n)).ne')
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ hl,one_smul]
  simp [mul_assoc]

theorem primeBurnolTwoDepthNormalizedGram_commutator (p : Nat.Primes) (n : ℕ) (u w : ℂ) :
    burnolJetBlockPolarization 2 u w*primeBurnolTwoDepthNormalizedGram p n-
      primeBurnolTwoDepthNormalizedGram p n*burnolJetBlockPolarization 2 u w=
        (2*u-1) • burnolJetBlockSkew (primeBurnolTwoDepthCrossBlock p n) := by
  have he : primeBurnolTwoDepthNormalizedGram p n=
      burnolJetBlockDiagonal (primeBurnolTwoDepthGramBlock p n)+
        burnolJetBlockCross (primeBurnolTwoDepthCrossBlock p n) := by
    rw [primeBurnolTwoDepthNormalizedGram_blocks]
    ext (i|i) (j|j) <;> simp [burnolJetBlockDiagonal,burnolJetBlockCross]
  rw [he,mul_add,add_mul,← burnolJetBlockPolarization_cross_commutator,
    burnolJetBlockPolarization_diagonal_commute]
  abel

theorem primeBurnolTwoDepthModular_scaled_tendsto (p : Nat.Primes) (u w : ℂ) :
    Tendsto (fun n => (primeBurnolLogFrequency (p,n) : ℂ) •
      ((primeBurnolTwoDepthNormalizedGram p n)⁻¹*burnolJetBlockPolarization 2 u w*
        primeBurnolTwoDepthNormalizedGram p n-burnolJetBlockPolarization 2 u w)) atTop
      (𝓝 ((2*u-1) • burnolJetBlockSkew (burnolTwoDepthLimitGram⁻¹*burnolTwoDepthLimitCross))) := by
  have hcross := ((burnolJetBlockSkew_continuous 2).tendsto burnolTwoDepthLimitCross).comp
    (primeBurnolTwoDepthCrossBlock_scaled_tendsto p)
  have hh := (primeBurnolTwoDepthNormalizedGram_inv_tendsto p).mul (hcross.const_smul (2*u-1))
  have hinv : burnolTwoDepthLimitFullGram⁻¹=burnolJetBlockDiagonal burnolTwoDepthLimitGram⁻¹ :=
    burnolJetBlockDiagonal_inverse burnolTwoDepthLimitGram burnolTwoDepthLimitGram_isUnit
  rw [hinv,Matrix.mul_smul,burnolJetBlockDiagonal_mul_skew] at hh
  apply hh.congr'
  filter_upwards with n
  let C := primeBurnolTwoDepthNormalizedGram p n
  let Q := burnolJetBlockPolarization 2 u w
  have hdiff : C⁻¹*Q*C-Q=C⁻¹*(Q*C-C*Q) := by
    dsimp only [C]
    simp only [mul_sub,← mul_assoc,primeBurnolTwoDepthNormalizedGram_inv_mul,one_mul]
  simp only [Function.comp_def]
  rw [hdiff,primeBurnolTwoDepthNormalizedGram_commutator]
  simp only [burnolJetBlockSkew_smul,Matrix.mul_smul,smul_smul]
  congr 1
  ring

theorem primeBurnolTwoDepthNormalizedCubic_scaled_tendsto (p : Nat.Primes) (a : ℝ) :
    Tendsto (fun n => (primeBurnolLogFrequency (p,n) : ℂ) •
      primeBurnolTwoDepthNormalizedCubic p n a) atTop
      (𝓝 (((2*(primeBurnolThetaVisibility a p : ℂ)^2-1)*
        (1-(primeBurnolThetaVisibility a p : ℂ)^2)) •
          burnolJetBlockSkew (burnolTwoDepthLimitGram⁻¹*burnolTwoDepthLimitCross))) := by
  let u := (primeBurnolThetaVisibility a p : ℂ)^2
  let w := (primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)
  have hsum : (primeBurnolThetaVisibility a p : ℂ)^2+(primeBurnolThetaContrast a p : ℂ)^2=1 :=
    by exact_mod_cast primeBurnolThetaVisibility_sq_add_contrast_sq a p
  have hw : w^2=u*(1-u) := by
    dsimp only [u,w]
    rw [show 1-(primeBurnolThetaVisibility a p : ℂ)^2=(primeBurnolThetaContrast a p : ℂ)^2
      by linear_combination -hsum,mul_pow]
  have hinv : Tendsto (fun n => (primeBurnolLogFrequency (p,n) : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero] using!
      (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_inv_atTop_zero.comp (primeBurnolLogFrequency_tendsto p))
  have hh := burnolJetCubic_scaled_tendsto (burnolJetNeutralMatrix 2)
    (burnolJetBlockPolarization 2 u w)
    (fun n => (primeBurnolTwoDepthNormalizedGram p n)⁻¹*burnolJetBlockPolarization 2 u w*
      primeBurnolTwoDepthNormalizedGram p n)
    (fun n => (primeBurnolLogFrequency (p,n) : ℂ))
    ((2*u-1) • burnolJetBlockSkew (burnolTwoDepthLimitGram⁻¹*burnolTwoDepthLimitCross))
    (fun n => Complex.ofReal_ne_zero.mpr (primeBurnolLogFrequency_pos (p,n)).ne') hinv
    (primeBurnolTwoDepthModular_scaled_tendsto p u w)
  rw [burnolJetCubicLinearTerm_block_skew hw] at hh
  simpa only [primeBurnolTwoDepthNormalizedCubic,burnolJetBlockPolarization_actual] using hh

end RHTower
