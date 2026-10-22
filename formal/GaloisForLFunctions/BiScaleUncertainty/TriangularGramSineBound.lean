import GaloisForLFunctions.RHTower.CCM.CCMNilpotentContractionSine
import GaloisForLFunctions.HTGeometry.StrictlyLoweringFiltration
import GaloisForLFunctions.HTGeometry.FiniteExponentialHankel

/-!
# Sine bounds with explicit triangular Gram errors

A cross Gram matrix splits into a strictly upper triangular operator and an explicit
lower-diagonal error. The former is nilpotent by construction. Normalization at its actual
operator norm and the finite-chain sine inequality give an unconditional numerical-radius
bound. Applying this to finite synthesis controls synchronized packet energy without
assuming orthogonality, contractivity, or exact arithmetic zeros.
-/

open scoped BigOperators InnerProductSpace
open Complex ContinuousLinearMap
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

/-- Sharp finite nilpotent numerical-radius coefficient for a nonempty chain. -/
def chainSineFactor (n : ℕ) : ℝ := Real.cos (Real.pi / ((n : ℝ) + 2))

theorem chainSineFactor_nonneg (n : ℕ) : 0 ≤ chainSineFactor n := by
  apply Real.cos_nonneg_of_mem_Icc
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · have : 0 ≤ Real.pi / ((n : ℝ) + 2) := by positivity
    linarith [Real.pi_pos]
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 2)).mpr
    nlinarith [Real.pi_pos]

/-- The synchronized-chain coefficient is strictly below the independent-block coefficient. -/
theorem chainSineFactor_lt_one (n : ℕ) : chainSineFactor n < 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < Real.pi / ((n : ℝ)+2) := by positivity
  have hle : Real.pi / ((n : ℝ)+2) ≤ Real.pi := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n+2)).mpr
    nlinarith [Real.pi_pos]
  simpa only [chainSineFactor, Real.cos_zero] using
    Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (le_refl 0) hle hp

/-- The uniform gain factor remains positive at every finite nonempty chain length. -/
theorem synchronized_sine_gain_factor_pos (n : ℕ) : 0 < 1-chainSineFactor n :=
  sub_pos.mpr (chainSineFactor_lt_one n)

/-- The two-level sine coefficient has its exact symbolic value. -/
theorem chainSineFactor_one : chainSineFactor 1 = 1/2 := by
  simpa only [chainSineFactor, Nat.cast_one, show (1 : ℝ)+2=3 by ring] using Real.cos_pi_div_three


/-- Matrix action with the Euclidean, rather than coordinate supremum, norm. -/
def gramMatrixOperator {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    EuclideanSpace ℂ (Fin (n+1)) →L[ℂ] EuclideanSpace ℂ (Fin (n+1)) :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

theorem gramMatrixOperator_pow {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (k : ℕ) :
    gramMatrixOperator (M^k) = gramMatrixOperator M ^ k := by
  apply ContinuousLinearMap.coe_injective
  rw [ContinuousLinearMap.coe_pow]
  change Matrix.toLpLin 2 2 (M^k) = Matrix.toLpLin 2 2 M ^ k
  rw [Matrix.toLpLin_pow]

/-- Retain the cross entries permitted by strict triangular compatibility. -/
def strictUpperGram {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ := fun i j => if i < j then M i j else 0

/-- The discarded lower-diagonal entries measure violation of arithmetic triangularity. -/
def triangularGramError {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    EuclideanSpace ℂ (Fin (n+1)) →L[ℂ] EuclideanSpace ℂ (Fin (n+1)) :=
  gramMatrixOperator M - gramMatrixOperator (strictUpperGram M)

/-- Triangular truncation has finite nilpotence without a nilpotence premise. -/
theorem strictUpperGram_operator_pow {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    gramMatrixOperator (strictUpperGram M) ^ (n+1) = 0 := by
  rw [← gramMatrixOperator_pow]
  have htri : HTGeometry.StrictlyLowering.StrictlyUpper (strictUpperGram M) := by
    intro i j hji
    simp only [strictUpperGram, if_neg (show ¬i < j by omega)]
  rw [HTGeometry.StrictlyLowering.pow_eq_zero_of_strictlyUpper htri]
  ext x i
  simp [gramMatrixOperator]

/-- The sharp sine bound for the constructed triangular part at its actual operator scale. -/
theorem strictUpperGram_inner_bound {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (x : EuclideanSpace ℂ (Fin (n+1))) :
    ‖inner ℂ (gramMatrixOperator (strictUpperGram M) x) x‖ ≤
      chainSineFactor n * ‖gramMatrixOperator (strictUpperGram M)‖ * ‖x‖ ^ 2 := by
  let T := gramMatrixOperator (strictUpperGram M)
  by_cases hz : ‖T‖ = 0
  · have ht : T = 0 := norm_eq_zero.mp hz
    change ‖inner ℂ (T x) x‖ ≤ chainSineFactor n * ‖T‖ * ‖x‖ ^ 2
    simp [ht]
  · have hn : 0 < ‖T‖ := lt_of_le_of_ne (norm_nonneg T) (Ne.symm hz)
    let c : ℂ := (‖T‖ : ℂ)⁻¹
    have hc : ‖c‖ = ‖T‖⁻¹ := by simp [c]
    have hcontract : ‖c • T‖ ≤ 1 := by rw [norm_smul, hc]; simp [hz]
    have hnil : (c • T) ^ (n+1) = 0 := by
      rw [smul_pow, strictUpperGram_operator_pow]
      change c ^ (n+1) •
        (0 : EuclideanSpace ℂ (Fin (n+1)) →L[ℂ] EuclideanSpace ℂ (Fin (n+1))) = 0
      exact _root_.smul_zero
        (A := EuclideanSpace ℂ (Fin (n+1)) →L[ℂ] EuclideanSpace ℂ (Fin (n+1))) (c ^ (n+1))
    have hb := RHTower.norm_inner_nilpotent_contraction_le_sine (c • T) hcontract (n+1) hnil x
    have he : ((n+1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    rw [he] at hb
    simp only [smul_apply, inner_smul_left, norm_mul, Complex.norm_conj,
      hc] at hb
    change ‖T‖⁻¹ * ‖inner ℂ (T x) x‖ ≤ chainSineFactor n * ‖x‖ ^ 2 at hb
    have hmul := mul_le_mul_of_nonneg_left hb hn.le
    have heq : ‖T‖ * (‖T‖⁻¹ * ‖inner ℂ (T x) x‖) = ‖inner ℂ (T x) x‖ := by field_simp
    rw [heq] at hmul
    change ‖inner ℂ (T x) x‖ ≤ chainSineFactor n * ‖T‖ * ‖x‖ ^ 2
    nlinarith

/-- A robust sine bound retaining every forbidden cross entry as an explicit error. -/
theorem gram_inner_sine_error_bound {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (x : EuclideanSpace ℂ (Fin (n+1))) :
    ‖inner ℂ (gramMatrixOperator M x) x‖ ≤
      (chainSineFactor n * ‖gramMatrixOperator M‖ +
        (1 + chainSineFactor n) * ‖triangularGramError M‖) * ‖x‖ ^ 2 := by
  let C := gramMatrixOperator M
  let T := gramMatrixOperator (strictUpperGram M)
  let F := triangularGramError M
  have heq : C = T + F := by dsimp [C, T, F, triangularGramError]; abel
  have hT : ‖T‖ ≤ ‖C‖ + ‖F‖ := by
    have ht : T = C - F := by dsimp [C, T, F, triangularGramError]; abel
    rw [ht]
    exact norm_sub_le _ _
  have hmain := strictUpperGram_inner_bound M x
  have herr : ‖inner ℂ (F x) x‖ ≤ ‖F‖ * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖F x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (‖F‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (F.le_opNorm x) (norm_nonneg x)
      _ = _ := by ring
  have hsum : ‖inner ℂ (C x) x‖ ≤ ‖inner ℂ (T x) x‖ + ‖inner ℂ (F x) x‖ := by
    rw [heq, add_apply, inner_add_left]
    exact norm_add_le _ _
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hT (chainSineFactor_nonneg n)) (sq_nonneg ‖x‖)
  change ‖inner ℂ (C x) x‖ ≤
    (chainSineFactor n * ‖C‖ + (1+chainSineFactor n)*‖F‖)*‖x‖^2
  change ‖inner ℂ (T x) x‖ ≤ chainSineFactor n * ‖T‖ * ‖x‖ ^ 2 at hmain
  nlinarith

section Frames
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The full cross Gram matrix of two arbitrary finite vector families. -/
def frameCrossGram {n : ℕ} (v w : Fin (n+1) → H) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  fun i j => inner ℂ (v i) (w j)

/-- The cross Gram operator is the actual analysis-synthesis composition. -/
theorem gramMatrixOperator_frameCrossGram {n : ℕ} (v w : Fin (n+1) → H) :
    gramMatrixOperator (frameCrossGram v w) =
      (HTGeometry.finiteSynthesis v).adjoint.comp (HTGeometry.finiteSynthesis w) := by
  ext c i
  simp [gramMatrixOperator, frameCrossGram, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    HTGeometry.adjoint_finiteSynthesis_apply, HTGeometry.finiteSynthesis_apply,
    mul_comm]

/-- The exact scalar-diagonal defect of one family. -/
def frameGramDefect {n : ℕ} (v : Fin (n+1) → H) :
    EuclideanSpace ℂ (Fin (n+1)) →L[ℂ] EuclideanSpace ℂ (Fin (n+1)) :=
  gramMatrixOperator (frameCrossGram v v) - ((‖v 0‖ ^ 2 : ℝ) : ℂ) • 1

/-- Finite synthesis is bounded by the diagonal energy plus its actual Gram defect. -/
theorem finiteSynthesis_norm_sq_le_defect {n : ℕ} (v : Fin (n+1) → H) :
    ‖HTGeometry.finiteSynthesis v‖ ^ 2 ≤ ‖v 0‖ ^ 2 + ‖frameGramDefect v‖ := by
  have hid := ContinuousLinearMap.norm_adjoint_comp_self (HTGeometry.finiteSynthesis v)
  rw [← gramMatrixOperator_frameCrossGram] at hid
  have heq : gramMatrixOperator (frameCrossGram v v) =
      ((‖v 0‖ ^ 2 : ℝ) : ℂ) • 1 + frameGramDefect v := by
    unfold frameGramDefect; abel
  have hb := norm_add_le (((‖v 0‖ ^ 2 : ℝ) : ℂ) •
    (1 : EuclideanSpace ℂ (Fin (n+1)) →L[ℂ] EuclideanSpace ℂ (Fin (n+1))))
      (frameGramDefect v)
  rw [← heq, hid] at hb
  have he : ‖((‖v 0‖ ^ 2 : ℝ) : ℂ) •
      (1 : EuclideanSpace ℂ (Fin (n+1)) →L[ℂ] EuclideanSpace ℂ (Fin (n+1)))‖ = ‖v 0‖ ^ 2 := by
    simp [norm_smul]
  rw [he] at hb
  nlinarith

/-- Synchronized packets satisfy a robust sine bound, with the triangular error explicit. -/
theorem synchronized_frame_energy_bound {n : ℕ} (v w : Fin (n+1) → H)
    (c : EuclideanSpace ℂ (Fin (n+1))) :
    ‖HTGeometry.finiteSynthesis v c + HTGeometry.finiteSynthesis w c‖ ^ 2 ≤
      (‖HTGeometry.finiteSynthesis v‖ ^ 2 + ‖HTGeometry.finiteSynthesis w‖ ^ 2 +
        2 * chainSineFactor n * ‖HTGeometry.finiteSynthesis v‖ * ‖HTGeometry.finiteSynthesis w‖ +
        2 * (1 + chainSineFactor n) * ‖triangularGramError (frameCrossGram w v)‖) * ‖c‖ ^ 2 := by
  let A := HTGeometry.finiteSynthesis v
  let B := HTGeometry.finiteSynthesis w
  have hcross := gram_inner_sine_error_bound (frameCrossGram w v) c
  rw [gramMatrixOperator_frameCrossGram] at hcross
  have hpair : inner ℂ (((B.adjoint).comp A) c) c = inner ℂ (A c) (B c) :=
    B.adjoint_inner_left c (A c)
  change ‖inner ℂ (((B.adjoint).comp A) c) c‖ ≤ _ at hcross
  rw [hpair] at hcross
  have hn : ‖B.adjoint.comp A‖ ≤ ‖A‖ * ‖B‖ := by
    have hb := B.adjoint.opNorm_comp_le A
    rw [LinearIsometryEquiv.norm_map] at hb
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hn (chainSineFactor_nonneg n)) (sq_nonneg ‖c‖)
  have hre := Complex.re_le_norm (inner ℂ (A c) (B c))
  have hA : ‖A c‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖c‖ ^ 2 := by
    have h := A.le_opNorm c
    nlinarith [norm_nonneg (A c), norm_nonneg A, norm_nonneg c]
  have hB : ‖B c‖ ^ 2 ≤ ‖B‖ ^ 2 * ‖c‖ ^ 2 := by
    have h := B.le_opNorm c
    nlinarith [norm_nonneg (B c), norm_nonneg B, norm_nonneg c]
  change ‖A c+B c‖^2 ≤ _
  rw [norm_add_sq (𝕜 := ℂ)]
  change ‖A c‖ ^ 2 + 2 * (inner ℂ (A c) (B c)).re + ‖B c‖ ^ 2 ≤ _
  change ‖inner ℂ (A c) (B c)‖ ≤
    (chainSineFactor n * ‖B.adjoint.comp A‖ +
      (1+chainSineFactor n)*‖triangularGramError (frameCrossGram w v)‖)*‖c‖^2 at hcross
  change _ ≤ (‖A‖^2+‖B‖^2+2*chainSineFactor n*‖A‖*‖B‖+
    2*(1+chainSineFactor n)*‖triangularGramError (frameCrossGram w v)‖)*‖c‖^2
  nlinarith

end Frames

end
end GaloisForLFunctions.BiScaleUncertainty
