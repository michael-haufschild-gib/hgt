import GaloisForLFunctions.RHTower.XiShiftedHalfDensityMobiusSourceConnection

/-!
# Hard-edge reverse-Euler law for the adaptive completed arithmetic source

The adaptive mixed `P^sharp` source is formed in the reciprocal variable, while hard-edge
compactness uses the translated reciprocal coordinate `U = X⁻¹ - y`.  Reciprocal clearing at the
actual admission depth conjugates the source polynomial itself into one reverse-Euler landing:

`C_(y,M+N+2)(A(A,B)) = (M+N+2) S - (X+y) S'`,

where `S = C_(y,M)(A) C_(y,N)(B)`.  The coefficient is the combined admission depth, so this is a
cofinal source producer rather than a fixed reporter.  The literal rational--Gamma-minus-von
Mangoldt scalar is recovered exactly by the inverse clearing.

An explicit admitted affine amplitude makes the diagonal landing negative at an interior point.
Thus the producer cannot be replaced by the already-refuted pointwise-positive kernel route.
-/

open Complex Matrix Polynomial

namespace RHTower

noncomputable section

/-- Reciprocal clearing at mass `y` and admission depth `N`:
`(y+U)^N P((y+U)⁻¹)`, defined polynomially by coefficient reflection and translation. -/
def xiShiftedHardEdgeReciprocalClearing
    (y : ℝ) (N : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  (P.reflect N).comp (X + C y)

/-- Reverse-Euler source in the translated hard-edge coordinate. -/
def xiShiftedHardEdgeReverseEulerSource
    (y : ℝ) (d : ℕ) (S : Polynomial ℝ) : Polynomial ℝ :=
  (d : ℝ) • S - (X + C y) * S.derivative

/-- Inverse reciprocal chart on a depth-`N` cleared source. -/
def xiShiftedHardEdgeReciprocalUnclearing
    (y : ℝ) (N : ℕ) (S : Polynomial ℝ) : Polynomial ℝ :=
  (S.comp (X - C y)).reflect N

/-- Admission-sensitive bilinear hard-edge producer.  Both amplitudes enter before any completed
arithmetic scalar is read. -/
def xiShiftedHardEdgeAdaptiveBilinearSource
    (y : ℝ) (M N : ℕ) (A B : Polynomial ℝ) : Polynomial ℝ :=
  xiShiftedHardEdgeReverseEulerSource y (M + N + 2)
    (xiShiftedHardEdgeReciprocalClearing y M A *
      xiShiftedHardEdgeReciprocalClearing y N B)

/-- Clearing followed by the inverse reciprocal chart returns the original polynomial exactly. -/
theorem xiShiftedHardEdgeReciprocalUnclearing_clearing
    (y : ℝ) (N : ℕ) (P : Polynomial ℝ) :
    xiShiftedHardEdgeReciprocalUnclearing y N
        (xiShiftedHardEdgeReciprocalClearing y N P) = P := by
  simp only [xiShiftedHardEdgeReciprocalUnclearing,
    xiShiftedHardEdgeReciprocalClearing, Polynomial.comp_assoc]
  have hshift : (X + C y).comp (X - C y) = (X : Polynomial ℝ) := by
    simp
  rw [hshift, Polynomial.comp_X, Polynomial.reflect_reflect]

private theorem coeff_X_mul_derivative
    (P : Polynomial ℝ) (k : ℕ) :
    (X * P.derivative).coeff k = (k : ℝ) * P.coeff k := by
  cases k with
  | zero => simp
  | succ k =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      push_cast
      ring

/-- Coefficient reflection conjugates the forward Euler field to the reverse Euler field. -/
theorem reflect_X_mul_derivative_eq_reverseEuler
    {R : Polynomial ℝ} {D : ℕ} (hR : R.natDegree ≤ D) :
    (X * R.derivative).reflect D =
      (D : ℝ) • R.reflect D - X * (R.reflect D).derivative := by
  ext i
  rw [Polynomial.coeff_reflect, Polynomial.coeff_sub,
    Polynomial.coeff_smul, coeff_X_mul_derivative,
    coeff_X_mul_derivative, Polynomial.coeff_reflect]
  by_cases hiD : i ≤ D
  · rw [Polynomial.revAt_le hiD]
    rw [Nat.cast_sub hiD]
    ring
  · have hDi : D < i := Nat.lt_of_not_ge hiD
    rw [Polynomial.revAt_eq_self_of_lt hDi]
    have hzero : R.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hR hDi)
    rw [hzero]
    simp

/-- Multiplication by `X` spends one reflection degree and disappears after clearing. -/
theorem reflect_X_mul_eq_reflect
    {A : Polynomial ℝ} {M : ℕ} (hA : A.natDegree ≤ M) :
    (X * A).reflect (M + 1) = A.reflect M := by
  rw [show M + 1 = 1 + M by omega,
    Polynomial.reflect_mul X A (by simp) hA,
    Polynomial.reflect_one_X, one_mul]

/-- Reciprocal clearing is multiplicative when supplied the two actual degree bounds. -/
theorem xiShiftedHardEdgeReciprocalClearing_mul
    {A B : Polynomial ℝ} {M N : ℕ}
    (hA : A.natDegree ≤ M) (hB : B.natDegree ≤ N) (y : ℝ) :
    xiShiftedHardEdgeReciprocalClearing y (M + N) (A * B) =
      xiShiftedHardEdgeReciprocalClearing y M A *
        xiShiftedHardEdgeReciprocalClearing y N B := by
  simp only [xiShiftedHardEdgeReciprocalClearing]
  rw [Polynomial.reflect_mul A B hA hB, Polynomial.mul_comp]

/-- Reflection form of the adaptive bilinear source law. -/
theorem reflect_xiShiftedBoundaryAdaptiveBilinearShearPolynomial
    {A B : Polynomial ℝ} {M N : ℕ}
    (hA : A.natDegree ≤ M) (hB : B.natDegree ≤ N) :
    (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A B).reflect (M + N + 2) =
      ((M + N + 2 : ℕ) : ℝ) • (A.reflect M * B.reflect N) -
        X * (A.reflect M * B.reflect N).derivative := by
  rw [xiShiftedBoundaryAdaptiveBilinearShearPolynomial_eq_X_derivative]
  let R : Polynomial ℝ := (X * A) * (X * B)
  have hXA : (X * A).natDegree ≤ M + 1 := by
    calc
      (X * A).natDegree ≤ X.natDegree + A.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1 + M := by simpa using Nat.add_le_add_left hA 1
      _ = M + 1 := by omega
  have hXB : (X * B).natDegree ≤ N + 1 := by
    calc
      (X * B).natDegree ≤ X.natDegree + B.natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1 + N := by simpa using Nat.add_le_add_left hB 1
      _ = N + 1 := by omega
  have hR : R.natDegree ≤ M + N + 2 := by
    calc
      R.natDegree ≤ (X * A).natDegree + (X * B).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (M + 1) + (N + 1) := Nat.add_le_add hXA hXB
      _ = M + N + 2 := by omega
  rw [reflect_X_mul_derivative_eq_reverseEuler hR]
  have hreflect : R.reflect (M + N + 2) = A.reflect M * B.reflect N := by
    dsimp only [R]
    rw [show M + N + 2 = (M + 1) + (N + 1) by omega,
      Polynomial.reflect_mul (X * A) (X * B) hXA hXB,
      reflect_X_mul_eq_reflect hA, reflect_X_mul_eq_reflect hB]
  rw [hreflect]

/-- **Cofinal hard-edge arithmetic producer.** Reciprocal clearing conjugates the adaptive
bilinear completed source polynomial to the depth-dependent reverse-Euler landing. -/
theorem xiShiftedHardEdgeReciprocalClearing_adaptiveBilinearShear
    {A B : Polynomial ℝ} {M N : ℕ}
    (hA : A.natDegree ≤ M) (hB : B.natDegree ≤ N) (y : ℝ) :
    xiShiftedHardEdgeReciprocalClearing y (M + N + 2)
        (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A B) =
      xiShiftedHardEdgeAdaptiveBilinearSource y M N A B := by
  rw [xiShiftedHardEdgeReciprocalClearing,
    reflect_xiShiftedBoundaryAdaptiveBilinearShearPolynomial hA hB]
  simp only [xiShiftedHardEdgeAdaptiveBilinearSource,
    xiShiftedHardEdgeReverseEulerSource,
    xiShiftedHardEdgeReciprocalClearing, Polynomial.sub_comp,
    Polynomial.smul_comp, Polynomial.mul_comp,
    Polynomial.derivative_mul, Polynomial.derivative_comp]
  simp

/-- Diagonal source is the reverse-Euler landing of the square of the cleared admitted
amplitude. -/
theorem xiShiftedHardEdgeReciprocalClearing_adaptiveBilinearShear_self
    {A : Polynomial ℝ} {N : ℕ} (hA : A.natDegree ≤ N) (y : ℝ) :
    xiShiftedHardEdgeReciprocalClearing y (2 * N + 2)
        (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A A) =
      ((2 * N + 2 : ℕ) : ℝ) •
          (xiShiftedHardEdgeReciprocalClearing y N A) ^ (2 : ℕ) -
        2 • ((X + C y) * xiShiftedHardEdgeReciprocalClearing y N A *
          (xiShiftedHardEdgeReciprocalClearing y N A).derivative) := by
  rw [show 2 * N + 2 = N + N + 2 by omega,
    xiShiftedHardEdgeReciprocalClearing_adaptiveBilinearShear hA hA]
  simp only [xiShiftedHardEdgeAdaptiveBilinearSource,
    xiShiftedHardEdgeReverseEulerSource, Polynomial.derivative_mul,
    Polynomial.smul_eq_C_mul]
  ring

/-- **Literal arithmetic landing.** The rational--Gamma-minus-von Mangoldt bilinear formation is
exactly the reciprocal-chart pullback of its hard-edge reverse-Euler producer. -/
theorem xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_hardEdgeLanding
    {w : ℝ} (hw : 1 / 2 < w) {A B : Polynomial ℝ} {M N : ℕ}
    (hA : A.natDegree ≤ M) (hB : B.natDegree ≤ N) :
    xiShiftedAdaptiveBilinearCompletedArithmeticSource w A B =
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w)
        (xiShiftedHardEdgeReciprocalUnclearing (w ^ (2 : ℕ)) (M + N + 2)
          (xiShiftedHardEdgeAdaptiveBilinearSource (w ^ (2 : ℕ)) M N A B)) := by
  rw [xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_shear hw]
  rw [← xiShiftedHardEdgeReciprocalClearing_adaptiveBilinearShear hA hB (w ^ (2 : ℕ))]
  rw [xiShiftedHardEdgeReciprocalUnclearing_clearing]
  rfl

/-- **Adaptive mixed-amplitude/completed `P^sharp` source law.** The actual diagonal arithmetic
formation is produced by the admission-depth reverse-Euler shear before scalar aggregation. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_eq_hardEdgeLanding
    {w : ℝ} (hw : 1 / 2 < w) {A : Polynomial ℝ} {N : ℕ}
    (hA : A.natDegree ≤ N) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w A =
      HTGeometry.momentFunctional (xiShiftedRealMomentSequence w)
        (xiShiftedHardEdgeReciprocalUnclearing (w ^ (2 : ℕ)) (2 * N + 2)
          (xiShiftedHardEdgeAdaptiveBilinearSource (w ^ (2 : ℕ)) N N A A)) := by
  rw [← xiShiftedAdaptiveBilinearCompletedArithmeticSource_self_eq_mixed hw]
  simpa only [show N + N + 2 = 2 * N + 2 by omega] using
    xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_hardEdgeLanding
      hw hA hA

/-- The reverse-Euler landing of a squared affine hard-edge amplitude is strictly negative at an
explicit interior point. -/
theorem xiShiftedHardEdgeReverseEulerSource_affine_negative
    {y a : ℝ} (hy : 0 ≤ y) (ha : 0 < a) :
    (xiShiftedHardEdgeReverseEulerSource y 4
      (((X : Polynomial ℝ) - C a) ^ (2 : ℕ))).eval ((3 * a + y) / 2) < 0 := by
  simp only [xiShiftedHardEdgeReverseEulerSource, Polynomial.derivative_pow,
    Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
    sub_zero, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  norm_num
  nlinarith [sq_pos_of_pos (add_pos_of_pos_of_nonneg ha hy)]

/-- **Pointwise-positivity obstruction for the actual producer.** An admitted affine amplitude
already makes the diagonal cleared arithmetic source negative. -/
theorem xiShiftedHardEdgeAdaptiveBilinearSource_affine_negative
    {y : ℝ} (hy : 0 ≤ y) {a : ℝ} (ha : 0 < a) :
    let A : Polynomial ℝ := 1 - C (y + a) * X
    (xiShiftedHardEdgeReciprocalClearing y 4
      (xiShiftedBoundaryAdaptiveBilinearShearPolynomial A A)).eval
        ((3 * a + y) / 2) < 0 := by
  dsimp only
  let A : Polynomial ℝ := 1 - C (y + a) * X
  have hA : A.natDegree ≤ 1 := by
    dsimp only [A]
    calc
      (1 - C (y + a) * X).natDegree ≤
          max (1 : Polynomial ℝ).natDegree (C (y + a) * X).natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ ≤ 1 := by
        apply max_le
        · simp
        · exact le_trans Polynomial.natDegree_mul_le (by simp)
  rw [show 4 = 1 + 1 + 2 by omega,
    xiShiftedHardEdgeReciprocalClearing_adaptiveBilinearShear hA hA]
  have hclear : xiShiftedHardEdgeReciprocalClearing y 1 A = X - C a := by
    dsimp only [xiShiftedHardEdgeReciprocalClearing, A]
    rw [Polynomial.reflect_sub, Polynomial.reflect_one]
    have hterm : (C (y + a) * X : Polynomial ℝ).reflect 1 = C (y + a) := by
      rw [show (X : Polynomial ℝ) = X ^ (1 : ℕ) by simp,
        Polynomial.reflect_C_mul_X_pow]
      simp
    rw [hterm]
    simp
    ring
  simp only [xiShiftedHardEdgeAdaptiveBilinearSource]
  rw [hclear]
  simpa only [one_add_one_eq_two, Nat.reduceAdd, pow_two] using
    xiShiftedHardEdgeReverseEulerSource_affine_negative hy ha

end

end RHTower
