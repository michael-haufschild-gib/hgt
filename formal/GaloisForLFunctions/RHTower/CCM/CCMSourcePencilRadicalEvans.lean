import GaloisForLFunctions.HTGeometry.RadicalQuotientEvansCoefficient
import GaloisForLFunctions.RHTower.CCM.CCMSourceResponseDeterminantDichotomy

/-!
# CCM source-pencil radical Evans law

For an active CCM source channel, displacement gives

`T (D c) = -beta`.

Consequently the semimetric action of the completed clock is the kernel-vector-free pencil

`T A = T D + |beta><alpha|`.

The universal radical-coefficient law then recovers the full quotient characteristic determinant
from the first surviving coefficient of

`T (D-z) + |beta><alpha|`.

Thus the finite quotient determinant is determined directly by the Weil matrix, diagonal clock,
and boundary displacement vectors. The chosen radical vector and quotient right inverse remain
only in the proof that this coefficient is the quotient determinant; neither occurs in the source
pencil to be taken through a cofinal limit.
-/

open Polynomial
open scoped Matrix ComplexOrder

namespace RHTower

variable {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

omit [DecidableEq n] in
/-- Active CCM displacement removes the selected radical vector from the semimetric action of the
completed clock. -/
theorem ccmSourceCompletion_semimetricAction
    (T D : Matrix n n ℂ) (c alpha beta : n → ℂ)
    (hboundary : T *ᵥ (D *ᵥ c) = -beta) :
    T * ccmSourceCompletion D c alpha =
      T * D + Matrix.vecMulVec beta (star alpha) := by
  rw [ccmSourceCompletion, Matrix.mul_sub, Matrix.mul_vecMulVec, hboundary]
  ext i j
  simp [Matrix.vecMulVec_apply]

/-- Metric adjointness automatically preserves the whole radical of a split complex Gram frame.
This discharges the quotient-invariance hypothesis without choosing a kernel basis. -/
theorem ccmMetricAdjoint_splitRadical
    (B : Matrix m n ℂ) (A : Matrix n n ℂ) (Rinv : Matrix n m ℂ)
    (hBR : B * Rinv = 1)
    (hmetric : (Bᴴ * B) * A = Aᴴ * (Bᴴ * B)) :
    B * A * (1 - Rinv * B) = 0 := by
  have hRB : Rinvᴴ * Bᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hBR, Matrix.conjTranspose_one]
  have hBP : B * (1 - Rinv * B) = 0 := by
    calc
      B * (1 - Rinv * B) = B - (B * Rinv) * B := by
        rw [Matrix.mul_sub, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hBR]; simp
  have hTP : (Bᴴ * B) * (1 - Rinv * B) = 0 := by
    rw [Matrix.mul_assoc, hBP, Matrix.mul_zero]
  have hTAP : (Bᴴ * B) * A * (1 - Rinv * B) = 0 := by
    rw [hmetric, Matrix.mul_assoc, hTP, Matrix.mul_zero]
  calc
    B * A * (1 - Rinv * B) =
        (1 : Matrix m m ℂ) * (B * A * (1 - Rinv * B)) := by rw [Matrix.one_mul]
    _ = (Rinvᴴ * Bᴴ) * (B * A * (1 - Rinv * B)) := by rw [hRB]
    _ = Rinvᴴ * ((Bᴴ * B) * A * (1 - Rinv * B)) := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hTAP, Matrix.mul_zero]

/-- A split complex Gram frame has a nonzero first radical coefficient. Hence source-pencil
extraction can be divided by its semimetric coefficient without an extra nondegeneracy premise. -/
theorem ccmSplitGram_lowestCoeff_ne_zero
    (B : Matrix m n ℂ) (Rinv : Matrix n m ℂ)
    (hle : Fintype.card m ≤ Fintype.card n)
    (hBR : B * Rinv = 1) :
    (Bᴴ * B).charpoly.coeff (Fintype.card n - Fintype.card m) ≠ 0 := by
  have hBvec : Function.Injective B.vecMul := by
    intro x y hxy
    have h := congrArg (fun v => v ᵥ* Rinv) hxy
    simpa only [Matrix.vecMul_vecMul, hBR, Matrix.vecMul_one] using h
  have hGpos : (B * Bᴴ).PosDef := Matrix.PosDef.mul_conjTranspose_self B hBvec
  have hGdet : Matrix.det (B * Bᴴ) ≠ 0 :=
    hGpos.posSemidef.posDef_iff_det_ne_zero.mp hGpos
  let k := Fintype.card n - Fintype.card m
  have hchar : (Bᴴ * B).charpoly = Polynomial.X ^ k * (B * Bᴴ).charpoly :=
    Matrix.charpoly_mul_comm_of_le Bᴴ B hle
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff k) hchar
  have hcoeff' :
      (Bᴴ * B).charpoly.coeff k = (B * Bᴴ).charpoly.coeff 0 := by
    simpa [k, Polynomial.coeff_X_pow_mul'] using hcoeff
  rw [hcoeff']
  intro hzero
  apply hGdet
  rw [Matrix.det_eq_sign_charpoly_coeff, hzero, mul_zero]

/-- Source-pencil extraction once active boundary transport and the Gram quotient are supplied. -/
theorem ccmSourceCompletion_sourcePencil_lowestCoeff
    (T D : Matrix n n ℂ) (c alpha beta : n → ℂ)
    (B : Matrix m n ℂ) (Rinv : Matrix n m ℂ) (z : ℂ)
    (hle : Fintype.card m ≤ Fintype.card n)
    (hGram : Bᴴ * B = T)
    (hradical : B * ccmSourceCompletion D c alpha * (1 - Rinv * B) = 0)
    (hboundary : T *ᵥ (D *ᵥ c) = -beta) :
    ((T * (D - z • 1) + Matrix.vecMulVec beta (star alpha)).charpoly).coeff
        (Fintype.card n - Fintype.card m) =
      Matrix.det
          (HTGeometry.splitQuotientCompression B (ccmSourceCompletion D c alpha) Rinv - z • 1) *
        T.charpoly.coeff (Fintype.card n - Fintype.card m) := by
  have hsource :
      (Bᴴ * B) * ccmSourceCompletion D c alpha =
        (Bᴴ * B) * D + Matrix.vecMulVec beta (star alpha) := by
    simpa only [hGram] using ccmSourceCompletion_semimetricAction T D c alpha beta hboundary
  have h := HTGeometry.splitQuotient_sourcePencil_lowestCoeff
    B Bᴴ (ccmSourceCompletion D c alpha) D Rinv
      (Matrix.vecMulVec beta (star alpha)) z hle hradical hsource
  simpa only [hGram] using h

/-- **CCM kernel-vector-free Evans coefficient law.** Rank-two displacement, active-source
normalization, and a split Gram frame identify the quotient characteristic determinant with the
first nonzero radical coefficient of the explicit CCM source pencil. Metric adjointness supplies
full-radical preservation automatically. -/
theorem ccmActiveSource_sourcePencil_lowestCoeff
    (T D : Matrix n n ℂ) (c alpha beta : n → ℂ)
    (B : Matrix m n ℂ) (Rinv : Matrix n m ℂ) (z : ℂ)
    (hle : Fintype.card m ≤ Fintype.card n)
    (hBR : B * Rinv = 1) (hGram : Bᴴ * B = T)
    (hT : T.IsHermitian) (hD : D.IsHermitian)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta (star alpha) - Matrix.vecMulVec alpha (star beta))
    (hTc : T *ᵥ c = 0)
    (halpha : star alpha ⬝ᵥ c = 1)
    (hbeta : star beta ⬝ᵥ c = 0) :
    ((T * (D - z • 1) + Matrix.vecMulVec beta (star alpha)).charpoly).coeff
        (Fintype.card n - Fintype.card m) =
      Matrix.det
          (HTGeometry.splitQuotientCompression B (ccmSourceCompletion D c alpha) Rinv - z • 1) *
        T.charpoly.coeff (Fintype.card n - Fintype.card m) := by
  have hboundary := ccmActiveSource_boundary T D alpha beta c hdisp hTc halpha hbeta
  have hmetricT := ccmSourceCompletion_metricAdjoint
    T D alpha beta c hT hD hdisp hboundary
  have hmetricB :
      (Bᴴ * B) * ccmSourceCompletion D c alpha =
        (ccmSourceCompletion D c alpha)ᴴ * (Bᴴ * B) := by
    simpa only [hGram] using hmetricT
  have hradical := ccmMetricAdjoint_splitRadical
    B (ccmSourceCompletion D c alpha) Rinv hBR hmetricB
  exact ccmSourceCompletion_sourcePencil_lowestCoeff
    T D c alpha beta B Rinv z hle hGram hradical hboundary

/-- **Normalized CCM Evans quotient formula.** The semimetric coefficient is nonzero, so the
active-source quotient determinant is literally the quotient of two ambient characteristic
coefficients. Its numerator is the kernel-vector-free CCM source pencil. -/
theorem ccmActiveSource_quotientDet_eq_sourcePencilCoeff_div
    (T D : Matrix n n ℂ) (c alpha beta : n → ℂ)
    (B : Matrix m n ℂ) (Rinv : Matrix n m ℂ) (z : ℂ)
    (hle : Fintype.card m ≤ Fintype.card n)
    (hBR : B * Rinv = 1) (hGram : Bᴴ * B = T)
    (hT : T.IsHermitian) (hD : D.IsHermitian)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta (star alpha) - Matrix.vecMulVec alpha (star beta))
    (hTc : T *ᵥ c = 0)
    (halpha : star alpha ⬝ᵥ c = 1)
    (hbeta : star beta ⬝ᵥ c = 0) :
    Matrix.det
        (HTGeometry.splitQuotientCompression B (ccmSourceCompletion D c alpha) Rinv - z • 1) =
      ((T * (D - z • 1) + Matrix.vecMulVec beta (star alpha)).charpoly).coeff
          (Fintype.card n - Fintype.card m) /
        T.charpoly.coeff (Fintype.card n - Fintype.card m) := by
  have hcoeff := ccmActiveSource_sourcePencil_lowestCoeff
    T D c alpha beta B Rinv z hle hBR hGram hT hD hdisp hTc halpha hbeta
  have hneB := ccmSplitGram_lowestCoeff_ne_zero B Rinv hle hBR
  have hneT : T.charpoly.coeff (Fintype.card n - Fintype.card m) ≠ 0 := by
    simpa only [← hGram] using hneB
  apply (eq_div_iff hneT).2
  exact hcoeff.symm

/-- **Branch-free CCM source-pencil Evans dichotomy.**  Reflection grading selects exactly one
active boundary channel.  In the source branch the quotient determinant is extracted from
`T(D-z)+|beta><eta|`; in the response branch it is extracted from
`T(D-z)-|eta><beta|`.  Both pencils are explicit in the original CCM data: neither contains the
selected radical vector or the quotient right inverse. -/
theorem ccmSourceResponse_quotientDet_eq_sourcePencilCoeff_div_dichotomy
    {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (clock beta : Fin N → ℂ) (G : Matrix (Fin N) (Fin N) ℂ)
    (B : Matrix m (Fin N) ℂ) (Rinv : Matrix (Fin N) m ℂ) (z : ℂ)
    (hle : Fintype.card m ≤ N)
    (hT : T.PosSemidef)
    (hD : (Matrix.diagonal clock).IsHermitian)
    (hclock : Function.Injective clock)
    (hdisp : Matrix.diagonal clock * T - T * Matrix.diagonal clock =
      Matrix.vecMulVec beta (star (fun _ : Fin N => (1 : ℂ))) -
        Matrix.vecMulVec (fun _ : Fin N => (1 : ℂ)) (star beta))
    (hkernel : ∃ k : Fin N → ℂ, T *ᵥ k = 0 ∧ k ≠ 0)
    (hG : G.IsHermitian) (hG2 : G * G = 1)
    (hTG : T * G = G * T)
    (hetaG : G *ᵥ (fun _ : Fin N => (1 : ℂ)) = fun _ => 1)
    (hbetaG : G *ᵥ beta = -beta)
    (hBR : B * Rinv = 1) (hGram : Bᴴ * B = T) :
    (∃ c : Fin N → ℂ,
      Matrix.det
          (HTGeometry.splitQuotientCompression B
              (ccmSourceCompletion (Matrix.diagonal clock) c
                (fun _ : Fin N => (1 : ℂ))) Rinv - z • 1) =
        ((T * (Matrix.diagonal clock - z • 1) +
            Matrix.vecMulVec beta (star (fun _ : Fin N => (1 : ℂ)))).charpoly).coeff
              (N - Fintype.card m) /
          T.charpoly.coeff (N - Fintype.card m)) ∨
    (∃ c : Fin N → ℂ,
      Matrix.det
          (HTGeometry.splitQuotientCompression B
              (ccmSourceCompletion (Matrix.diagonal clock) c beta) Rinv - z • 1) =
        ((T * (Matrix.diagonal clock - z • 1) +
            Matrix.vecMulVec (-(fun _ : Fin N => (1 : ℂ))) (star beta)).charpoly).coeff
              (N - Fintype.card m) /
          T.charpoly.coeff (N - Fintype.card m)) := by
  let eta : Fin N → ℂ := fun _ => 1
  have hle' : Fintype.card m ≤ Fintype.card (Fin N) := by simpa using hle
  have hcross : star beta ⬝ᵥ ccmRadicalProjection T eta = 0 :=
    ccmRadicalProjection_source_response_cross_zero
      T G eta beta hG hG2 hTG (by simpa [eta] using hetaG) hbetaG
  rcases ccmSourceResponse_radicalProjection_exclusive
      T clock beta hT hclock hdisp hkernel (by simpa [eta] using hcross) with
    ⟨hetaActive, hbetaZero⟩ | ⟨hetaZero, hbetaActive⟩
  · let c := ccmNormalizedRadicalProjection T eta
    have hTc : T *ᵥ c = 0 := ccmNormalizedRadicalProjection_mulVec_eq_zero T eta
    have hetaC : star eta ⬝ᵥ c = 1 :=
      ccmNormalizedRadicalProjection_pairing_eq_one T eta hetaActive
    have hbetaC : star beta ⬝ᵥ c = 0 :=
      ccmPairing_eq_zero_of_radicalProjection_eq_zero T beta c hbetaZero hTc
    refine Or.inl ⟨c, ?_⟩
    simpa [eta] using
      (ccmActiveSource_quotientDet_eq_sourcePencilCoeff_div
        T (Matrix.diagonal clock) c eta beta B Rinv z hle' hBR hGram
        hT.isHermitian hD (by simpa [eta] using hdisp) hTc hetaC hbetaC)
  · let c := ccmNormalizedRadicalProjection T beta
    have hTc : T *ᵥ c = 0 := ccmNormalizedRadicalProjection_mulVec_eq_zero T beta
    have hbetaC : star beta ⬝ᵥ c = 1 :=
      ccmNormalizedRadicalProjection_pairing_eq_one T beta hbetaActive
    have hetaC : star eta ⬝ᵥ c = 0 :=
      ccmPairing_eq_zero_of_radicalProjection_eq_zero T eta c hetaZero hTc
    have hdispResponse :
        Matrix.diagonal clock * T - T * Matrix.diagonal clock =
          Matrix.vecMulVec (-eta) (star beta) -
            Matrix.vecMulVec beta (star (-eta)) := by
      rw [show Matrix.diagonal clock * T - T * Matrix.diagonal clock =
        Matrix.vecMulVec beta (star eta) - Matrix.vecMulVec eta (star beta) by
          simpa [eta] using hdisp]
      ext i j
      simp [Matrix.vecMulVec_apply]
      ring
    have hminusEtaC : star (-eta) ⬝ᵥ c = 0 := by simp [hetaC]
    refine Or.inr ⟨c, ?_⟩
    simpa [eta] using
      (ccmActiveSource_quotientDet_eq_sourcePencilCoeff_div
        T (Matrix.diagonal clock) c beta (-eta) B Rinv z hle' hBR hGram
        hT.isHermitian hD hdispResponse hTc hbetaC hminusEtaC)

/-- Concrete connector from the actual scalar-shifted CCM divided-difference matrices to the
branch-free source-pencil coefficient dichotomy.  Reflection, displacement, and Hermitian clock
hypotheses are discharged from the source data. -/
theorem ccmDividedDifferenceShift_sourcePencilEvans_dichotomy
    {N : ℕ} (rho : Fin N ≃ Fin N) (hrho : ∀ i, rho (rho i) = i)
    (clock source diagonal : Fin N → ℝ) (mu : ℝ)
    (B : Matrix m (Fin N) ℂ) (Rinv : Matrix (Fin N) m ℂ) (z : ℂ)
    (hle : Fintype.card m ≤ N)
    (hclockInjective : Function.Injective clock)
    (hclockOdd : ∀ i, clock (rho i) = -clock i)
    (hsourceOdd : ∀ i, source (rho i) = -source i)
    (hdiagonalEven : ∀ i, diagonal (rho i) = diagonal i)
    (hT : ((ccmScalarShift (ccmDividedDifferenceMatrix clock source diagonal) mu).map
      (algebraMap ℝ ℂ)).PosSemidef)
    (hkernel : ∃ k : Fin N → ℂ,
      (ccmScalarShift (ccmDividedDifferenceMatrix clock source diagonal) mu).map
        (algebraMap ℝ ℂ) *ᵥ k = 0 ∧ k ≠ 0)
    (hBR : B * Rinv = 1)
    (hGram : Bᴴ * B =
      (ccmScalarShift (ccmDividedDifferenceMatrix clock source diagonal) mu).map
        (algebraMap ℝ ℂ)) :
    let T := (ccmScalarShift (ccmDividedDifferenceMatrix clock source diagonal) mu).map
      (algebraMap ℝ ℂ)
    let D := Matrix.diagonal (fun i => (clock i : ℂ))
    let eta : Fin N → ℂ := fun _ => 1
    let beta : Fin N → ℂ := fun i => source i
    (∃ c : Fin N → ℂ,
      Matrix.det
          (HTGeometry.splitQuotientCompression B (ccmSourceCompletion D c eta) Rinv - z • 1) =
        ((T * (D - z • 1) + Matrix.vecMulVec beta (star eta)).charpoly).coeff
              (N - Fintype.card m) /
          T.charpoly.coeff (N - Fintype.card m)) ∨
    (∃ c : Fin N → ℂ,
      Matrix.det
          (HTGeometry.splitQuotientCompression B (ccmSourceCompletion D c beta) Rinv - z • 1) =
        ((T * (D - z • 1) + Matrix.vecMulVec (-eta) (star beta)).charpoly).coeff
              (N - Fintype.card m) /
          T.charpoly.coeff (N - Fintype.card m)) := by
  dsimp only
  let Q := ccmDividedDifferenceMatrix clock source diagonal
  let T := (ccmScalarShift Q mu).map (algebraMap ℝ ℂ)
  let clockC : Fin N → ℂ := fun i => clock i
  let beta : Fin N → ℂ := fun i => source i
  let G := (ccmReflectionMatrix rho).map (algebraMap ℝ ℂ)
  have hDC : (Matrix.diagonal clockC).IsHermitian := by
    simpa [clockC, ccmDiagonalClock] using
      (realSymmetric_complexification_isHermitian (ccmDiagonalClock clock)
        (ccmDiagonalClock_transpose clock))
  have hclockC : Function.Injective clockC := by
    intro i j hij
    apply hclockInjective
    change (clock i : ℂ) = (clock j : ℂ) at hij
    exact_mod_cast hij
  have hdispC :
      Matrix.diagonal clockC * T - T * Matrix.diagonal clockC =
        Matrix.vecMulVec beta (star (fun _ : Fin N => (1 : ℂ))) -
          Matrix.vecMulVec (fun _ : Fin N => (1 : ℂ)) (star beta) := by
    have hreal := ccmScalarShift_displacement Q (ccmDiagonalClock clock)
      (Matrix.vecMulVec source ccmConstantBoundary -
        Matrix.vecMulVec ccmConstantBoundary source) mu
      (ccmDividedDifference_displacement clock source diagonal hclockInjective)
    have hmap := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ =>
      M.map (algebraMap ℝ ℂ)) hreal
    have hDmap : (ccmDiagonalClock clock).map (algebraMap ℝ ℂ) =
        Matrix.diagonal clockC := by
      ext i j
      by_cases hij : i = j <;>
        simp [ccmDiagonalClock, clockC, Matrix.diagonal, hij]
    have hRmap :
        (Matrix.vecMulVec source ccmConstantBoundary -
          Matrix.vecMulVec ccmConstantBoundary source).map (algebraMap ℝ ℂ) =
        Matrix.vecMulVec beta (star (fun _ : Fin N => (1 : ℂ))) -
          Matrix.vecMulVec (fun _ : Fin N => (1 : ℂ)) (star beta) := by
      ext i j
      simp [Matrix.vecMulVec_apply, ccmConstantBoundary, beta]
    change
      (ccmDiagonalClock clock * ccmScalarShift Q mu -
        ccmScalarShift Q mu * ccmDiagonalClock clock).map (algebraMap ℝ ℂ) =
      (Matrix.vecMulVec source ccmConstantBoundary -
        Matrix.vecMulVec ccmConstantBoundary source).map (algebraMap ℝ ℂ) at hmap
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul,
      hDmap, hRmap] at hmap
    simpa [T, Q] using hmap
  have hGC : G.IsHermitian :=
    realSymmetric_complexification_isHermitian _
      (ccmReflectionMatrix_transpose rho hrho)
  have hG2C : G * G = 1 := by
    ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (rho i)]
    · by_cases hij : i = j
      · subst j
        simp [G, ccmReflectionMatrix, hrho]
      · have hji : j ≠ i := Ne.symm hij
        simp [G, ccmReflectionMatrix, hrho, hij, hji]
    · intro b hb hne
      simp [G, ccmReflectionMatrix, hne]
    · simp
  have hTGC : T * G = G * T := by
    have hreal := ccmScalarShift_commutes Q (ccmReflectionMatrix rho) mu
      (ccmReflectionMatrix_commutes_dividedDifference rho hrho clock source diagonal
        hclockOdd hsourceOdd hdiagonalEven)
    have hmap := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ =>
      M.map (algebraMap ℝ ℂ)) hreal
    change (ccmScalarShift Q mu * ccmReflectionMatrix rho).map (algebraMap ℝ ℂ) =
      (ccmReflectionMatrix rho * ccmScalarShift Q mu).map (algebraMap ℝ ℂ) at hmap
    rw [Matrix.map_mul, Matrix.map_mul] at hmap
    simpa [T, G, Q] using hmap
  have hetaGC : G *ᵥ (fun _ : Fin N => (1 : ℂ)) = fun _ => 1 := by
    change (ccmReflectionMatrix rho).map (algebraMap ℝ ℂ) *ᵥ
        ((algebraMap ℝ ℂ) ∘ ccmConstantBoundary) =
      (algebraMap ℝ ℂ) ∘ ccmConstantBoundary
    funext i
    rw [← RingHom.map_mulVec]
    exact congrArg (algebraMap ℝ ℂ)
      (congr_fun (ccmReflectionMatrix_constantBoundary_even rho) i)
  have hbetaGC : G *ᵥ beta = -beta := by
    change (ccmReflectionMatrix rho).map (algebraMap ℝ ℂ) *ᵥ
        ((algebraMap ℝ ℂ) ∘ source) = -((algebraMap ℝ ℂ) ∘ source)
    funext i
    rw [← RingHom.map_mulVec]
    have hi := congr_fun (ccmReflectionMatrix_source_odd rho source hsourceOdd) i
    rw [hi]
    simp
  simpa [T, Q, clockC, beta] using
    (ccmSourceResponse_quotientDet_eq_sourcePencilCoeff_div_dichotomy
      T clockC beta G B Rinv z hle (by simpa [T, Q] using hT) hDC hclockC hdispC
      (by simpa [T, Q] using hkernel) hGC hG2C hTGC hetaGC hbetaGC hBR
      (by simpa [T, Q] using hGram))

end RHTower
