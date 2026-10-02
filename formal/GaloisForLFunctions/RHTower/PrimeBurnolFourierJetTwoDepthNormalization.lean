import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetTwoDepthGram

/-!
# Exact amplitude transport of the actual two-depth cubic

The normalized Gram is a scalar congruence by the actual nonzero Euler amplitudes.
The canonical modular action and complete cubic are transported by exact unit
conjugation. No bound on inverse amplitudes or limiting replacement is used.
-/

open Complex Filter Topology Matrix
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

theorem primeBurnolTwoDepthChannelAmplitude_ne_zero (p : Nat.Primes) (n : ℕ)
    (i : Fin 2 ⊕ Fin 2) : primeBurnolTwoDepthChannelAmplitude p n i≠0 := by
  cases i <;> exact primeBurnolAmplitude_ne_zero _

def primeBurnolTwoDepthAmplitudeUnit (p : Nat.Primes) (n : ℕ) :
    (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ)ˣ where
  val := Matrix.diagonal (primeBurnolTwoDepthChannelAmplitude p n)
  inv := Matrix.diagonal (fun i => (primeBurnolTwoDepthChannelAmplitude p n i)⁻¹)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [primeBurnolTwoDepthChannelAmplitude_ne_zero]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [primeBurnolTwoDepthChannelAmplitude_ne_zero]

theorem primeBurnolTwoDepthNormalizedGram_normalize (p : Nat.Primes) (n : ℕ) :
    primeBurnolTwoDepthNormalizedGram p n=(primeBurnolLogFrequency (p,n) : ℂ)^3 •
      ((↑((primeBurnolTwoDepthAmplitudeUnit p n)⁻¹) : Matrix _ _ ℂ)*
        primeBurnolFourierJetGram (primeBurnolTwoDepthPacket p n)*
          (↑((primeBurnolTwoDepthAmplitudeUnit p n)⁻¹) : Matrix _ _ ℂ)) := by
  ext i j
  simp [primeBurnolTwoDepthNormalizedGram,primeBurnolTwoDepthAmplitudeUnit,
    Matrix.diagonal_mul,Matrix.mul_diagonal]
  ring

theorem primeBurnolTwoDepthNormalizedGram_inverse (p : Nat.Primes) (n : ℕ) :
    (primeBurnolTwoDepthNormalizedGram p n)⁻¹=((primeBurnolLogFrequency (p,n) : ℂ)^3)⁻¹ •
      ((↑(primeBurnolTwoDepthAmplitudeUnit p n) : Matrix _ _ ℂ)*
        (↑((primeBurnolFourierJetGramUnit (primeBurnolTwoDepthPacket p n))⁻¹) : Matrix _ _ ℂ)*
          (↑(primeBurnolTwoDepthAmplitudeUnit p n) : Matrix _ _ ℂ)) := by
  have hl : (primeBurnolLogFrequency (p,n) : ℂ)^3≠0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (primeBurnolLogFrequency_pos (p,n)).ne')
  apply Matrix.inv_eq_left_inv
  rw [primeBurnolTwoDepthNormalizedGram_normalize,← coe_primeBurnolFourierJetGramUnit]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ hl,one_smul]
  simp [mul_assoc]

theorem primeBurnolTwoDepthAmplitudeUnit_theta (p : Nat.Primes) (n : ℕ) (a : ℝ) :
    sourceModularAutomorphism ((primeBurnolTwoDepthAmplitudeUnit p n)⁻¹)
      (burnolJetThetaMatrix 2 p a)=burnolJetThetaMatrix 2 p a := by
  change (↑(primeBurnolTwoDepthAmplitudeUnit p n) : Matrix _ _ ℂ)*burnolJetThetaMatrix 2 p a*
    (↑((primeBurnolTwoDepthAmplitudeUnit p n)⁻¹) : Matrix _ _ ℂ)=_
  ext (i|i) (j|j) <;>
    simp [primeBurnolTwoDepthAmplitudeUnit,Matrix.diagonal_mul,Matrix.mul_diagonal,
      burnolJetThetaMatrix,primeBurnolTwoDepthChannelAmplitude,Matrix.one_apply] <;>
    split_ifs <;> simp_all <;> field_simp [primeBurnolAmplitude_ne_zero]

theorem primeBurnolTwoDepthAmplitudeUnit_neutral (p : Nat.Primes) (n : ℕ) :
    sourceModularAutomorphism ((primeBurnolTwoDepthAmplitudeUnit p n)⁻¹)
      (burnolJetNeutralMatrix 2)=burnolJetNeutralMatrix 2 := by
  change (↑(primeBurnolTwoDepthAmplitudeUnit p n) : Matrix _ _ ℂ)*burnolJetNeutralMatrix 2*
    (↑((primeBurnolTwoDepthAmplitudeUnit p n)⁻¹) : Matrix _ _ ℂ)=_
  ext (i|i) (j|j) <;>
    simp [primeBurnolTwoDepthAmplitudeUnit,Matrix.diagonal_mul,Matrix.mul_diagonal,
      burnolJetNeutralMatrix,primeBurnolTwoDepthChannelAmplitude,Matrix.one_apply]
  split_ifs <;> simp_all [primeBurnolAmplitude_ne_zero]

theorem primeBurnolTwoDepthNormalizedGram_modular (p : Nat.Primes) (n : ℕ) (a : ℝ) :
    (primeBurnolTwoDepthNormalizedGram p n)⁻¹*burnolJetThetaMatrix 2 p a*
      primeBurnolTwoDepthNormalizedGram p n=
      sourceModularAutomorphism ((primeBurnolTwoDepthAmplitudeUnit p n)⁻¹)
        (sourceModularAutomorphism (primeBurnolFourierJetGramUnit (primeBurnolTwoDepthPacket p n))
          (burnolJetThetaMatrix 2 p a)) := by
  have hl : (primeBurnolLogFrequency (p,n) : ℂ)^3≠0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (primeBurnolLogFrequency_pos (p,n)).ne')
  let U := primeBurnolTwoDepthAmplitudeUnit p n
  let V := primeBurnolFourierJetGramUnit (primeBurnolTwoDepthPacket p n)
  let Q := burnolJetThetaMatrix 2 p a
  let d : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := ↑U
  let e : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := ↑(U⁻¹)
  let v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := ↑V
  let b : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := ↑(V⁻¹)
  have hQ : (↑U : Matrix _ _ ℂ)*Q*(↑(U⁻¹) : Matrix _ _ ℂ)=Q :=
    primeBurnolTwoDepthAmplitudeUnit_theta p n a
  rw [primeBurnolTwoDepthNormalizedGram_inverse,primeBurnolTwoDepthNormalizedGram_normalize,
    ← coe_primeBurnolFourierJetGramUnit]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ hl,one_smul]
  change d*b*d*Q*(e*v*e)=d*(b*Q*v)*e
  calc
    _ = d*b*(d*Q*e)*v*e := by simp only [mul_assoc]
    _ = _ := by rw [hQ]; simp only [mul_assoc]

def primeBurnolTwoDepthNormalizedCubic (p : Nat.Primes) (n : ℕ) (a : ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  cubicProjectionAssociatorAlgebra
    ((primeBurnolTwoDepthNormalizedGram p n)⁻¹*burnolJetThetaMatrix 2 p a*
      primeBurnolTwoDepthNormalizedGram p n)
    (burnolJetThetaMatrix 2 p a) (burnolJetNeutralMatrix 2)

theorem primeBurnolTwoDepthNormalizedCubic_conjugate (p : Nat.Primes) (n : ℕ) (a : ℝ) :
    primeBurnolTwoDepthNormalizedCubic p n a=
      sourceModularAutomorphism ((primeBurnolTwoDepthAmplitudeUnit p n)⁻¹)
        (primeBurnolFourierJetConstantThetaCubic (primeBurnolTwoDepthPacket p n) p a) := by
  rw [primeBurnolTwoDepthNormalizedCubic,primeBurnolTwoDepthNormalizedGram_modular]
  simp only [primeBurnolFourierJetConstantThetaCubic,cubicProjectionAssociatorAlgebra,map_sub,map_pow,
    primeBurnolTwoDepthAmplitudeUnit_theta,primeBurnolTwoDepthAmplitudeUnit_neutral]

end RHTower
