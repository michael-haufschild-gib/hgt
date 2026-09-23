import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanJacobi

/-!
# Diagonal rescaling of Jacobi decompositions

Exact real symmetric and complex Hermitian formulas transporting upper-unipotent Jacobi data
through invertible diagonal congruence.  Positivity and unipotence are preserved, while each
Jacobi diagonal is multiplied by the corresponding squared modulus.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped ComplexOrder

noncomputable section

variable {n : ℕ}

def realJacobiDiagonalRescaleU (g : Fin n → ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => (g i)⁻¹) * U * Matrix.diagonal g

def realJacobiDiagonalRescaleD (g d : Fin n → ℝ) : Fin n → ℝ :=
  fun i => d i * (g i) ^ (2 : ℕ)

theorem realJacobiDiagonalRescaleU_upper (g : Fin n → ℝ)
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : ∀ i j, j < i → U i j = 0) :
    ∀ i j, j < i → realJacobiDiagonalRescaleU g U i j = 0 := by
  intro i j hji
  rw [realJacobiDiagonalRescaleU, Matrix.mul_diagonal, Matrix.diagonal_mul, hU i j hji]
  ring

theorem realJacobiDiagonalRescaleU_unit (g : Fin n → ℝ) (hg : ∀ i, g i ≠ 0)
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : ∀ i, U i i = 1) :
    ∀ i, realJacobiDiagonalRescaleU g U i i = 1 := by
  intro i
  rw [realJacobiDiagonalRescaleU, Matrix.mul_diagonal, Matrix.diagonal_mul, hU i]
  simp [hg i]

theorem realJacobiDiagonalRescaleD_pos (g d : Fin n → ℝ)
    (hg : ∀ i, g i ≠ 0) (hd : ∀ i, 0 < d i) :
    ∀ i, 0 < realJacobiDiagonalRescaleD g d i := by
  intro i
  exact mul_pos (hd i) (sq_pos_of_ne_zero (hg i))

theorem realJacobiDiagonalRescale_form (g d : Fin n → ℝ)
    (hg : ∀ i, g i ≠ 0) (U : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.diagonal g * (Uᵀ * Matrix.diagonal d * U) * Matrix.diagonal g =
      (realJacobiDiagonalRescaleU g U)ᵀ *
        Matrix.diagonal (realJacobiDiagonalRescaleD g d) *
          realJacobiDiagonalRescaleU g U := by
  let G := Matrix.diagonal g
  let Gi := Matrix.diagonal fun i => (g i)⁻¹
  have hGiG : Gi * G = 1 := by
    dsimp only [Gi, G]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hg i]
    · simp [Matrix.diagonal, hij]
  have hGGi : G * Gi = 1 := by
    dsimp only [G, Gi]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hg i]
    · simp [Matrix.diagonal, hij]
  have hD : Matrix.diagonal (realJacobiDiagonalRescaleD g d) =
      G * Matrix.diagonal d * G := by
    dsimp only [G]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    simp [realJacobiDiagonalRescaleD]
    ring
  have hU : realJacobiDiagonalRescaleU g U = Gi * U * G := rfl
  rw [hU, hD]
  change G * (Uᵀ * Matrix.diagonal d * U) * G =
    (Gi * U * G)ᵀ * (G * Matrix.diagonal d * G) * (Gi * U * G)
  symm
  calc
    (Gi * U * G)ᵀ * (G * Matrix.diagonal d * G) * (Gi * U * G) =
        (G * Uᵀ * Gi) * (G * Matrix.diagonal d * G) * (Gi * U * G) := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
        Matrix.diagonal_transpose]
      dsimp only [G, Gi]
      simp only [Matrix.mul_assoc]
    _ = G * (Uᵀ * Matrix.diagonal d * U) * G := by
      calc
        _ = G * Uᵀ * (Gi * G) * Matrix.diagonal d * (G * Gi) * U * G := by
          simp only [Matrix.mul_assoc]
        _ = G * (Uᵀ * Matrix.diagonal d * U) * G := by
          rw [hGiG, hGGi]
          simp only [Matrix.mul_one, Matrix.mul_assoc]

def complexJacobiDiagonalRescaleU (z : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (star (z i))⁻¹) * U * Matrix.diagonal (star z)

def complexJacobiDiagonalRescaleD (z d : Fin n → ℂ) : Fin n → ℂ :=
  fun i => z i * d i * star (z i)

theorem complexJacobiDiagonalRescaleU_upper (z : Fin n → ℂ)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : ∀ i j, j < i → U i j = 0) :
    ∀ i j, j < i → complexJacobiDiagonalRescaleU z U i j = 0 := by
  intro i j hji
  rw [complexJacobiDiagonalRescaleU, Matrix.mul_diagonal, Matrix.diagonal_mul, hU i j hji]
  ring

theorem complexJacobiDiagonalRescaleU_unit (z : Fin n → ℂ) (hz : ∀ i, z i ≠ 0)
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : ∀ i, U i i = 1) :
    ∀ i, complexJacobiDiagonalRescaleU z U i i = 1 := by
  intro i
  rw [complexJacobiDiagonalRescaleU, Matrix.mul_diagonal, Matrix.diagonal_mul, hU i]
  simp [hz i]

theorem complexJacobiDiagonalRescaleD_pos (z d : Fin n → ℂ)
    (hz : ∀ i, z i ≠ 0) (hd : ∀ i, 0 < d i) :
    ∀ i, 0 < complexJacobiDiagonalRescaleD z d i := by
  intro i
  have hnorm : 0 < (Complex.normSq (z i) : ℂ) :=
    Complex.zero_lt_real.mpr (Complex.normSq_pos.mpr (hz i))
  have hfactor : complexJacobiDiagonalRescaleD z d i =
      (Complex.normSq (z i) : ℂ) * d i := by
    rw [complexJacobiDiagonalRescaleD]
    calc
      z i * d i * star (z i) = (z i * star (z i)) * d i := by ring
      _ = (Complex.normSq (z i) : ℂ) * d i := by
        exact congrArg (fun q : ℂ => q * d i) (Complex.mul_conj (z i))
  rw [hfactor]
  exact mul_pos hnorm (hd i)

theorem complexJacobiDiagonalRescale_form (z d : Fin n → ℂ)
    (hz : ∀ i, z i ≠ 0) (U : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.diagonal z * (Uᴴ * Matrix.diagonal d * U) * Matrix.diagonal (star z) =
      (complexJacobiDiagonalRescaleU z U)ᴴ *
        Matrix.diagonal (complexJacobiDiagonalRescaleD z d) *
          complexJacobiDiagonalRescaleU z U := by
  let G := Matrix.diagonal z
  let Gi := Matrix.diagonal fun i => (z i)⁻¹
  let H := Matrix.diagonal (star z)
  let Hi := Matrix.diagonal fun i => (star (z i))⁻¹
  have hGiG : Gi * G = 1 := by
    dsimp only [Gi, G]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hz i]
    · simp [Matrix.diagonal, hij]
  have hHHi : H * Hi = 1 := by
    dsimp only [H, Hi]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hz i]
    · simp [Matrix.diagonal, hij]
  have hD : Matrix.diagonal (complexJacobiDiagonalRescaleD z d) =
      G * Matrix.diagonal d * H := by
    dsimp only [G, H]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    rfl
  have hHstar : Hᴴ = G := by
    dsimp only [H, G]
    simp [Matrix.diagonal_conjTranspose]
  have hHistar : Hiᴴ = Gi := by
    dsimp only [Hi, Gi]
    rw [Matrix.diagonal_conjTranspose]
    apply congrArg Matrix.diagonal
    funext i
    simp
  have hU : complexJacobiDiagonalRescaleU z U = Hi * U * H := rfl
  rw [hU, hD]
  change G * (Uᴴ * Matrix.diagonal d * U) * H =
    (Hi * U * H)ᴴ * (G * Matrix.diagonal d * H) * (Hi * U * H)
  symm
  calc
    (Hi * U * H)ᴴ * (G * Matrix.diagonal d * H) * (Hi * U * H) =
        (G * Uᴴ * Gi) * (G * Matrix.diagonal d * H) * (Hi * U * H) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hHstar, hHistar]
      simp only [Matrix.mul_assoc]
    _ = G * (Uᴴ * Matrix.diagonal d * U) * H := by
      calc
        _ = G * Uᴴ * (Gi * G) * Matrix.diagonal d * (H * Hi) * U * H := by
          simp only [Matrix.mul_assoc]
        _ = G * (Uᴴ * Matrix.diagonal d * U) * H := by
          rw [hGiG, hHHi]
          simp only [Matrix.mul_one, Matrix.mul_assoc]

end

end GaloisForLFunctions.HTGeometry
