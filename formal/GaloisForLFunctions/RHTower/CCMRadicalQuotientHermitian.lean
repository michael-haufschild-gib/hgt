import GaloisForLFunctions.RHTower.HermitianDeterminantRH
import GaloisForLFunctions.RHTower.CCMDividedDifferenceInstantiation

/-!
# CCM radical quotients are ordinary Hermitian systems

A possibly singular semimetric has a rectangular Gram factor `T = Bᴴ B`.  If `B` is surjective
with right inverse `R` and `A` is self-adjoint for `T`, then the compressed operator `B A R` is
ordinary Hermitian.  If `A` preserves the full radical, the compression also intertwines `A` with
the honest radical quotient.

The real version connects the unconditional boundary-channel completion of every finite CCM
divided-difference matrix to an ordinary symmetric quotient, without a simple ground eigenvalue or
a parity choice.  Its complexified characteristic polynomial is real-rooted.  The last theorem
connects locally uniform convergence of these quotient characteristic polynomials directly to RH.
-/

open Complex
open scoped Matrix

namespace RHTower

variable {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- Compression of a semimetric-adjoint operator through a surjective complex Gram frame. -/
noncomputable def semimetricQuotientCompression
    (B : Matrix m n ℂ) (A : Matrix n n ℂ) (R : Matrix n m ℂ) :
    Matrix m m ℂ :=
  B * A * R

omit [DecidableEq n] in
/-- **Semimetric quotient law.** A right inverse turns metric adjointness for `Bᴴ B` into ordinary
Hermiticity after compression. -/
theorem semimetricQuotientCompression_isHermitian
    (B : Matrix m n ℂ) (A : Matrix n n ℂ) (R : Matrix n m ℂ)
    (hBR : B * R = 1)
    (hmetric : (Bᴴ * B) * A = Aᴴ * (Bᴴ * B)) :
    (semimetricQuotientCompression B A R).IsHermitian := by
  have hRB : Rᴴ * Bᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hBR, Matrix.conjTranspose_one]
  have hB : Bᴴ * (B * R) = Bᴴ := by rw [hBR, Matrix.mul_one]
  rw [Matrix.IsHermitian]
  simp only [semimetricQuotientCompression, Matrix.conjTranspose_mul]
  calc
    Rᴴ * (Aᴴ * Bᴴ) = Rᴴ * (Aᴴ * (Bᴴ * B)) * R := by
      calc
        Rᴴ * (Aᴴ * Bᴴ) = Rᴴ * (Aᴴ * (Bᴴ * (B * R))) := by rw [hB]
        _ = Rᴴ * (Aᴴ * (Bᴴ * B)) * R := by simp only [Matrix.mul_assoc]
    _ = Rᴴ * ((Bᴴ * B) * A) * R := by rw [hmetric]
    _ = B * A * R := by
      calc
        Rᴴ * ((Bᴴ * B) * A) * R = (Rᴴ * Bᴴ) * ((B * A) * R) := by
          simp only [Matrix.mul_assoc]
        _ = 1 * ((B * A) * R) := by rw [hRB]
        _ = B * A * R := by rw [Matrix.one_mul]

omit [DecidableEq n] in
/-- Every characteristic zero of a semimetric quotient compression is real. -/
theorem semimetricQuotientCompression_charpoly_zero_im_eq_zero
    (B : Matrix m n ℂ) (A : Matrix n n ℂ) (R : Matrix n m ℂ)
    (hBR : B * R = 1)
    (hmetric : (Bᴴ * B) * A = Aᴴ * (Bᴴ * B))
    {z : ℂ}
    (hz : (semimetricQuotientCompression B A R).charpoly.eval z = 0) :
    z.im = 0 := by
  exact hermitian_charpoly_zero_im_eq_zero
    (semimetricQuotientCompression_isHermitian B A R hBR hmetric) hz

omit [DecidableEq m] in
/-- Full-radical preservation makes the complex Hermitian compression the honest quotient
operator. -/
theorem semimetricQuotientCompression_intertwines
    (B : Matrix m n ℂ) (A : Matrix n n ℂ) (R : Matrix n m ℂ)
    (hradical : B * A * (1 - R * B) = 0) :
    semimetricQuotientCompression B A R * B = B * A := by
  have hradical' : (B * A) * (1 - R * B) = 0 := by
    simpa only [Matrix.mul_assoc] using hradical
  rw [Matrix.mul_sub, Matrix.mul_one] at hradical'
  have hBA : (B * A) * (R * B) = B * A := (sub_eq_zero.mp hradical').symm
  rw [semimetricQuotientCompression]
  calc
    (B * A * R) * B = (B * A) * (R * B) := by simp only [Matrix.mul_assoc]
    _ = B * A := hBA

/-- Normalized characteristic functions of a cofinal complex semimetric quotient family. -/
noncomputable def normalizedSemimetricQuotientCharpoly
    (ambient quotient : ℕ → ℕ)
    (B : ∀ k, Matrix (Fin (quotient k)) (Fin (ambient k)) ℂ)
    (A : ∀ k, Matrix (Fin (ambient k)) (Fin (ambient k)) ℂ)
    (R : ∀ k, Matrix (Fin (ambient k)) (Fin (quotient k)) ℂ)
    (u : ℕ → ℂ → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  u k z * (semimetricQuotientCompression (B k) (A k) (R k)).charpoly.eval z

/-- Locally uniform convergence of semimetric quotient determinants to `XiC` implies RH. -/
theorem riemannHypothesis_of_normalizedSemimetricQuotientCharpoly_tendstoLocallyUniformly
    {ambient quotient : ℕ → ℕ}
    {B : ∀ k, Matrix (Fin (quotient k)) (Fin (ambient k)) ℂ}
    {A : ∀ k, Matrix (Fin (ambient k)) (Fin (ambient k)) ℂ}
    {R : ∀ k, Matrix (Fin (ambient k)) (Fin (quotient k)) ℂ}
    {u : ℕ → ℂ → ℂ}
    (hBR : ∀ k, B k * R k = 1)
    (hmetric : ∀ k, ((B k)ᴴ * B k) * A k = (A k)ᴴ * ((B k)ᴴ * B k))
    (hu : ∀ k, Differentiable ℂ (u k))
    (hu0 : ∀ k z, u k z ≠ 0)
    (hconv : TendstoLocallyUniformly
      (normalizedSemimetricQuotientCharpoly ambient quotient B A R u) XiC Filter.atTop) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_normalizedHermitianCharpoly_tendstoLocallyUniformly
    (d := quotient)
    (A := fun k => semimetricQuotientCompression (B k) (A k) (R k))
    (u := u)
  · intro k
    exact semimetricQuotientCompression_isHermitian
      (B k) (A k) (R k) (hBR k) (hmetric k)
  · exact hu
  · exact hu0
  · have hfun :
        normalizedHermitianCharpoly quotient
            (fun k => semimetricQuotientCompression (B k) (A k) (R k)) u =
          normalizedSemimetricQuotientCharpoly ambient quotient B A R u := by
      funext k z
      rfl
    rw [hfun]
    exact hconv

/-- Real semimetric quotient compression. -/
noncomputable def realSemimetricQuotientCompression
    (B : Matrix m n ℝ) (A : Matrix n n ℝ) (R : Matrix n m ℝ) :
    Matrix m m ℝ :=
  B * A * R

omit [DecidableEq n] in
/-- Real form of the semimetric quotient law. -/
theorem realSemimetricQuotientCompression_transpose
    (B : Matrix m n ℝ) (A : Matrix n n ℝ) (R : Matrix n m ℝ)
    (hBR : B * R = 1)
    (hmetric : (B.transpose * B) * A = A.transpose * (B.transpose * B)) :
    (realSemimetricQuotientCompression B A R).transpose =
      realSemimetricQuotientCompression B A R := by
  have hRB : R.transpose * B.transpose = 1 := by
    rw [← Matrix.transpose_mul, hBR, Matrix.transpose_one]
  have hB : B.transpose * (B * R) = B.transpose := by rw [hBR, Matrix.mul_one]
  simp only [realSemimetricQuotientCompression, Matrix.transpose_mul]
  calc
    R.transpose * (A.transpose * B.transpose) =
        R.transpose * (A.transpose * (B.transpose * B)) * R := by
      calc
        R.transpose * (A.transpose * B.transpose) =
            R.transpose * (A.transpose * (B.transpose * (B * R))) := by rw [hB]
        _ = R.transpose * (A.transpose * (B.transpose * B)) * R := by
          simp only [Matrix.mul_assoc]
    _ = R.transpose * ((B.transpose * B) * A) * R := by rw [hmetric]
    _ = B * A * R := by
      calc
        R.transpose * ((B.transpose * B) * A) * R =
            (R.transpose * B.transpose) * ((B * A) * R) := by
          simp only [Matrix.mul_assoc]
        _ = 1 * ((B * A) * R) := by rw [hRB]
        _ = B * A * R := by rw [Matrix.one_mul]

omit [DecidableEq m] [DecidableEq n] in
/-- A real rectangular frame and its Gram matrix have the same kernel. -/
theorem realGram_mulVec_eq_zero_iff
    (B : Matrix m n ℝ) (x : n → ℝ) :
    (B.transpose * B) *ᵥ x = 0 ↔ B *ᵥ x = 0 := by
  have hker := Matrix.ker_mulVecLin_conjTranspose_mul_self B
  have hker' : LinearMap.ker (B.transpose * B).mulVecLin =
      LinearMap.ker B.mulVecLin := by
    simpa only [show Bᴴ = B.transpose by ext i j; simp] using hker
  change x ∈ LinearMap.ker (B.transpose * B).mulVecLin ↔
    x ∈ LinearMap.ker B.mulVecLin
  rw [hker']

omit [DecidableEq m] in
/-- Full-radical preservation makes the real symmetric compression the honest quotient
operator. -/
theorem realSemimetricQuotientCompression_intertwines
    (B : Matrix m n ℝ) (A : Matrix n n ℝ) (R : Matrix n m ℝ)
    (hradical : B * A * (1 - R * B) = 0) :
    realSemimetricQuotientCompression B A R * B = B * A := by
  have hradical' : (B * A) * (1 - R * B) = 0 := by
    simpa only [Matrix.mul_assoc] using hradical
  rw [Matrix.mul_sub, Matrix.mul_one] at hradical'
  have hBA : (B * A) * (R * B) = B * A := (sub_eq_zero.mp hradical').symm
  rw [realSemimetricQuotientCompression]
  calc
    (B * A * R) * B = (B * A) * (R * B) := by simp only [Matrix.mul_assoc]
    _ = B * A := hBA

omit [Fintype m] [DecidableEq m] in
/-- The complexification of a real symmetric matrix is Hermitian. -/
theorem realSymmetric_complexification_isHermitian
    (C : Matrix m m ℝ) (hC : C.transpose = C) :
    (C.map (algebraMap ℝ ℂ)).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  have hij := congr_fun (congr_fun hC j) i
  simpa using hij.symm

/-- Every complex characteristic zero of a real symmetric matrix is real. -/
theorem realSymmetric_complexification_charpoly_zero_im_eq_zero
    (C : Matrix m m ℝ) (hC : C.transpose = C) {z : ℂ}
    (hz : (C.map (algebraMap ℝ ℂ)).charpoly.eval z = 0) : z.im = 0 := by
  exact hermitian_charpoly_zero_im_eq_zero
    (realSymmetric_complexification_isHermitian C hC) hz

/-- Normalized characteristic functions of a cofinal real semimetric quotient family. -/
noncomputable def normalizedRealSemimetricQuotientCharpoly
    (ambient quotient : ℕ → ℕ)
    (B : ∀ k, Matrix (Fin (quotient k)) (Fin (ambient k)) ℝ)
    (A : ∀ k, Matrix (Fin (ambient k)) (Fin (ambient k)) ℝ)
    (R : ∀ k, Matrix (Fin (ambient k)) (Fin (quotient k)) ℝ)
    (u : ℕ → ℂ → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  u k z * ((realSemimetricQuotientCompression (B k) (A k) (R k)).map
    (algebraMap ℝ ℂ)).charpoly.eval z

/-- Real radical-quotient determinant convergence implies RH. -/
theorem riemannHypothesis_of_normalizedRealSemimetricQuotientCharpoly_tendstoLocallyUniformly
    {ambient quotient : ℕ → ℕ}
    {B : ∀ k, Matrix (Fin (quotient k)) (Fin (ambient k)) ℝ}
    {A : ∀ k, Matrix (Fin (ambient k)) (Fin (ambient k)) ℝ}
    {R : ∀ k, Matrix (Fin (ambient k)) (Fin (quotient k)) ℝ}
    {u : ℕ → ℂ → ℂ}
    (hBR : ∀ k, B k * R k = 1)
    (hmetric : ∀ k, ((B k).transpose * B k) * A k =
      (A k).transpose * ((B k).transpose * B k))
    (hu : ∀ k, Differentiable ℂ (u k))
    (hu0 : ∀ k z, u k z ≠ 0)
    (hconv : TendstoLocallyUniformly
      (normalizedRealSemimetricQuotientCharpoly ambient quotient B A R u) XiC
      Filter.atTop) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_normalizedHermitianCharpoly_tendstoLocallyUniformly
    (d := quotient)
    (A := fun k => (realSemimetricQuotientCompression (B k) (A k) (R k)).map
      (algebraMap ℝ ℂ))
    (u := u)
  · intro k
    apply realSymmetric_complexification_isHermitian
    exact realSemimetricQuotientCompression_transpose
      (B k) (A k) (R k) (hBR k) (hmetric k)
  · exact hu
  · exact hu0
  · have hfun :
        normalizedHermitianCharpoly quotient
            (fun k => (realSemimetricQuotientCompression (B k) (A k) (R k)).map
              (algebraMap ℝ ℂ)) u =
          normalizedRealSemimetricQuotientCharpoly ambient quotient B A R u := by
      funext k z
      rfl
    rw [hfun]
    exact hconv

/-- **Arbitrary-radical CCM quotient.** Boundary-channel completion plus a supplied surjective
Gram frame produces an ordinary symmetric quotient clock intertwining the full radical quotient. -/
theorem ccmBoundaryChannelCompletion_realSemimetricQuotient_exists
    (T D Gamma : Matrix n n ℝ) (eta beta : n → ℝ)
    (hT : T.transpose = T) (hD : D.transpose = D)
    (hG : Gamma.transpose = Gamma) (hTG : T * Gamma = Gamma * T)
    (hetaG : Gamma *ᵥ eta = eta) (hbetaG : Gamma *ᵥ beta = -beta)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta)
    (B : Matrix m n ℝ) (R : Matrix n m ℝ)
    (hBR : B * R = 1) (hGram : B.transpose * B = T) :
    ∃ A : Matrix n n ℝ,
      T * A = A.transpose * T ∧
      (realSemimetricQuotientCompression B A R).transpose =
        realSemimetricQuotientCompression B A R ∧
      realSemimetricQuotientCompression B A R * B = B * A := by
  obtain ⟨A, hmetricT, hradicalT⟩ :=
    ccmBoundaryChannelCompletion_exists T D Gamma eta beta
      hT hD hG hTG hetaG hbetaG hdisp
  have hmetric : (B.transpose * B) * A =
      A.transpose * (B.transpose * B) := by simpa only [hGram] using hmetricT
  have hBproj : B * (1 - R * B) = 0 := by
    calc
      B * (1 - R * B) = B - (B * R) * B := by
        rw [Matrix.mul_sub, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = B - (1 : Matrix m m ℝ) * B := by rw [hBR]
      _ = 0 := by simp
  have hradical : B * A * (1 - R * B) = 0 := by
    ext i j
    have hkB : B *ᵥ ((1 - R * B) *ᵥ Pi.single j 1) = 0 := by
      have hcol := congrArg
        (fun M : Matrix m n ℝ => M *ᵥ Pi.single j 1) hBproj
      simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using hcol
    have hkT : T *ᵥ ((1 - R * B) *ᵥ Pi.single j 1) = 0 := by
      rw [← hGram]
      exact (realGram_mulVec_eq_zero_iff B _).mpr hkB
    have hAkT := hradicalT _ hkT
    have hAkB : B *ᵥ (A *ᵥ ((1 - R * B) *ᵥ Pi.single j 1)) = 0 := by
      apply (realGram_mulVec_eq_zero_iff B _).mp
      rw [hGram]
      exact hAkT
    have hcol : (B * A * (1 - R * B)) *ᵥ Pi.single j 1 = 0 := by
      simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hAkB
    have hi := congrFun hcol i
    simpa [Matrix.mulVec, Pi.single_apply] using hi
  refine ⟨A, hmetricT,
    realSemimetricQuotientCompression_transpose B A R hBR hmetric, ?_⟩
  exact realSemimetricQuotientCompression_intertwines B A R hradical

/-- Concrete arbitrary-radical quotient connector for every reflection-graded CCM
divided-difference scalar shift. -/
theorem ccmDividedDifferenceShift_realSemimetricQuotient_exists
    (rho : n ≃ n) (hrho : ∀ i, rho (rho i) = i)
    (clock source diagonal : n → ℝ) (mu : ℝ)
    (hclockInjective : Function.Injective clock)
    (hclockOdd : ∀ i, clock (rho i) = -clock i)
    (hsourceOdd : ∀ i, source (rho i) = -source i)
    (hdiagonalEven : ∀ i, diagonal (rho i) = diagonal i)
    (B : Matrix m n ℝ) (R : Matrix n m ℝ)
    (hBR : B * R = 1)
    (hGram : B.transpose * B =
      ccmScalarShift (ccmDividedDifferenceMatrix clock source diagonal) mu) :
    ∃ A : Matrix n n ℝ,
      ccmScalarShift (ccmDividedDifferenceMatrix clock source diagonal) mu * A =
        A.transpose * ccmScalarShift
          (ccmDividedDifferenceMatrix clock source diagonal) mu ∧
      (realSemimetricQuotientCompression B A R).transpose =
        realSemimetricQuotientCompression B A R ∧
      realSemimetricQuotientCompression B A R * B = B * A := by
  apply ccmBoundaryChannelCompletion_realSemimetricQuotient_exists
    (T := ccmScalarShift (ccmDividedDifferenceMatrix clock source diagonal) mu)
    (D := ccmDiagonalClock clock) (Gamma := ccmReflectionMatrix rho)
    (eta := ccmConstantBoundary) (beta := source)
    (B := B) (R := R)
  · exact ccmScalarShift_transpose _ _
      (ccmDividedDifferenceMatrix_transpose clock source diagonal)
  · exact ccmDiagonalClock_transpose clock
  · exact ccmReflectionMatrix_transpose rho hrho
  · exact ccmScalarShift_commutes _ _ _
      (ccmReflectionMatrix_commutes_dividedDifference rho hrho clock source diagonal
        hclockOdd hsourceOdd hdiagonalEven)
  · exact ccmReflectionMatrix_constantBoundary_even rho
  · exact ccmReflectionMatrix_source_odd rho source hsourceOdd
  · apply ccmScalarShift_displacement
    exact ccmDividedDifference_displacement clock source diagonal hclockInjective
  · exact hBR
  · exact hGram

end RHTower
