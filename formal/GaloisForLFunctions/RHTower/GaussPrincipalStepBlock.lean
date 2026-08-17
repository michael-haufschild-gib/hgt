import GaloisForLFunctions.RHTower.GaussPrincipalStep
import GaloisForLFunctions.RHTower.GaussMovingAmplitudeOperator
import GaloisForLFunctions.HTGeometry.OperatorPowerTelescope

/-!
# The principal step as an operator, and its powers

The exact factorization of the quasi-inner block says that on the twisted amplitude `e_n f` the
block acts as the scalar `p |d_n|²` times `e_n` times

`R_n = B S B^(-2) S* B`,

the *principal step*.  Bundling `R_n` as a continuous linear map turns the iteration into a power:

`G^r (e_n f) = (p |d_n|²)^r · e_n (R_n^r f)`.

Its model is `R_0 = M_(a_(δ_n))`, whose norm is at most `p`, and the telescoping bound for a
difference of operator powers reduces the deviation of `R_n^r` from `R_0^r` to the deviation of the
*operators* applied to the iterates of `R_n`.  `R_n` itself is never applied to an error term,
which matters because its norm grows with `n`.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology

noncomputable section

/-! ## The normalized blocks, bundled -/

/-- The normalized conjugate shifted block as a continuous linear map. -/
def gaussShiftedBlockOfCLM {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (n : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  (starRingEnd ℂ (gaussSampleValue k p n))⁻¹ •
    (fourierMulBlock (-n) ∘L gaussDiagonalBlockStar hm k p ∘L fourierMulBlock n)

theorem gaussShiftedBlockOfCLM_apply {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (n : ℤ)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussShiftedBlockOfCLM hm k p n u = gaussShiftedBlockOf hm k p n u := rfl

/-- The normalized unconjugated shifted block as a continuous linear map. -/
def gaussShiftedBlockDiagCLM {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (n : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  (gaussSampleValue k p n)⁻¹ •
    (fourierMulBlock (-n) ∘L gaussDiagonalBlock hm k p ∘L fourierMulBlock n)

theorem gaussShiftedBlockDiagCLM_apply {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (n : ℤ) (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussShiftedBlockDiagCLM hm k p n u = gaussShiftedBlockDiag hm k p n u := rfl

/-! ## The principal step -/

/-- The principal step `R_n = B S B^(-2) S* B`. -/
def gaussPrincipalStepBlock {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (n : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  gaussPrimeScaleBlock hp ∘L gaussShiftedBlockDiagCLM hm k p n ∘L
    gaussPrimeScaleInvSqBlock hp ∘L gaussShiftedBlockOfCLM hm k p n ∘L gaussPrimeScaleBlock hp

theorem gaussPrincipalStepBlock_apply {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (n : ℤ)
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussPrincipalStepBlock hm k p hp n f
      = gaussPrimeScaleBlock hp
          (gaussShiftedBlockDiag hm k p n
            (gaussPrimeScaleInvSqBlock hp
              (gaussShiftedBlockOf hm k p n (gaussPrimeScaleBlock hp f)))) := rfl

/-- **The iteration is a power of the principal step.** -/
theorem gaussQuasiInnerG_pow_fourierMulBlock {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {n : ℤ} (hn : n ≠ 0)
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (r : ℕ) :
    (gaussQuasiInnerG hm k p ^ r) (fourierMulBlock n f)
      = ((((p : ℝ) : ℂ) *
          (starRingEnd ℂ (gaussSampleValue k p n) * gaussSampleValue k p n)) ^ r) •
        fourierMulBlock n ((gaussPrincipalStepBlock hm k p hp n ^ r) f) := by
  induction r with
  | zero =>
      have h1 : (gaussQuasiInnerG hm k p ^ 0) (fourierMulBlock n f)
          = fourierMulBlock n f := by
        rw [pow_zero]
        rfl
      have h2 : (gaussPrincipalStepBlock hm k p hp n ^ 0) f = f := by
        rw [pow_zero]
        rfl
      rw [h1, h2, pow_zero, one_smul]
  | succ r ih =>
      have h1 : (gaussQuasiInnerG hm k p ^ (r + 1)) (fourierMulBlock n f)
          = gaussQuasiInnerG hm k p
              ((gaussQuasiInnerG hm k p ^ r) (fourierMulBlock n f)) := by
        rw [pow_succ']
        rfl
      have h2 : (gaussPrincipalStepBlock hm k p hp n ^ (r + 1)) f
          = gaussPrincipalStepBlock hm k p hp n
              ((gaussPrincipalStepBlock hm k p hp n ^ r) f) := by
        rw [pow_succ']
        rfl
      rw [h1, ih, map_smul, gaussQuasiInnerG_fourierMulBlock hm k p hp hn, smul_smul, h2,
        gaussPrincipalStepBlock_apply, pow_succ]

/-! ## The model and the telescoping bound -/

theorem norm_gaussMovingAmplitudeBlock_le {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ)) :
    ‖gaussMovingAmplitudeBlock hp δ‖ ≤ p :=
  MeasureTheory.norm_lpBoundedMulCLM_le _ _ _

/-- **The deviation of the iterated principal step from its model** is controlled by the deviation
of the operators on the iterates, with only powers of `p` in front. -/
theorem norm_gaussPrincipalStep_pow_sub_movingAmplitude_pow_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) (n : ℤ)
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (r : ℕ) :
    ‖(gaussPrincipalStepBlock hm k p hp n ^ r) f -
        (gaussMovingAmplitudeBlock hp
          ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)) ^ r) f‖
      ≤ ∑ i ∈ Finset.range r, (p : ℝ) ^ (r - 1 - i) *
          ‖(gaussPrincipalStepBlock hm k p hp n -
              gaussMovingAmplitudeBlock hp
                ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ)))
            ((gaussPrincipalStepBlock hm k p hp n ^ i) f)‖ := by
  refine (GaloisForLFunctions.HTGeometry.norm_pow_apply_sub_pow_apply_le
    (gaussPrincipalStepBlock hm k p hp n)
    (gaussMovingAmplitudeBlock hp ((gaussSamplePhase m p n : ℝ) : AddCircle (1 : ℝ))) f r).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gaussMovingAmplitudeBlock_le hp _) _

end

end RHTower
