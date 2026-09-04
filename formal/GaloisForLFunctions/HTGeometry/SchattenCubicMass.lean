/-
# Exact cubic Schatten mass

For a Hilbert--Schmidt operator, the cubic moment of its absolute value is the exact third
Schatten mass.  For a self-adjoint operator, the absolute value of the cube is the cube of the
absolute value, so the nuclear norm of the cube is exactly the same mass.
-/
import GaloisForLFunctions.HTGeometry.NuclearTraceLaw
import GaloisForLFunctions.HTGeometry.OperatorDeterminantGraphClosure
import GaloisForLFunctions.HTGeometry.PositiveOperatorPowerMoment
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.HTGeometry.SchattenNorm
import GaloisForLFunctions.HTGeometry.SchattenPowerHilbertSchmidt
import GaloisForLFunctions.RHTower.ArithmeticDilationStageDeterminant

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The endomorphism and rectangular approximation-number definitions agree exactly. -/
theorem approxNumber_eq_rectApproxNumber (T : H →L[ℂ] H) (n : ℕ) :
    approxNumber T n = rectApproxNumber T n := by
  rfl

/-- Schatten norms are invariant under the Hilbert-space adjoint. -/
theorem schattenNorm_adjoint (p : ℝ) (T : H →L[ℂ] H) :
    GaloisForLFunctions.HTGeometry.schattenNorm p
        (ContinuousLinearMap.adjoint T) =
      GaloisForLFunctions.HTGeometry.schattenNorm p T := by
  unfold GaloisForLFunctions.HTGeometry.schattenNorm
  congr 1
  exact tsum_congr fun n => by
    rw [approxNumber_eq_rectApproxNumber, approxNumber_eq_rectApproxNumber,
      rectApproxNumber_adjoint]

/-- If an operator vanishes on the range of a right factor, so does its absolute value. -/
theorem absOp_mul_eq_zero_of_mul_eq_zero
    (A C : H →L[ℂ] H) (hAC : A * C = 0) :
    absOp A * C = 0 := by
  ext x
  have hACx := congrArg (fun T : H →L[ℂ] H => T x) hAC
  change A (C x) = 0 at hACx
  apply norm_eq_zero.mp
  change ‖absOp A (C x)‖ = 0
  rw [norm_absOp_apply, hACx, norm_zero]

/-- The corresponding left support law follows by adjunction. -/
theorem mul_absOp_eq_zero_of_mul_eq_zero
    (A C : H →L[ℂ] H)
    (hCadj : ContinuousLinearMap.adjoint C = C)
    (hAC : A * C = 0) :
    C * absOp A = 0 := by
  have hright := absOp_mul_eq_zero_of_mul_eq_zero A C hAC
  have hstar := congrArg ContinuousLinearMap.adjoint hright
  have hAbsAdj : ContinuousLinearMap.adjoint (absOp A) = absOp A :=
    isSelfAdjoint_absOp A
  change ContinuousLinearMap.adjoint (absOp A ∘L C) =
    ContinuousLinearMap.adjoint 0 at hstar
  rw [ContinuousLinearMap.adjoint_comp, hCadj, hAbsAdj] at hstar
  change C ∘L absOp A = 0
  simpa using hstar

/-- Absolute values of operators carried by complementary right projection sectors annihilate
one another in both orders. -/
theorem absOp_complementary_right_support
    (A B P : H →L[ℂ] H)
    (hP : IsIdempotentElem P)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hAP : A * P = A)
    (hBQ : B * (1 - P) = B) :
    absOp A * absOp B = 0 ∧ absOp B * absOp A = 0 := by
  have hPP : P * P = P := hP
  have hQadj : ContinuousLinearMap.adjoint (1 - P) = 1 - P := by
    rw [ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint_one, hPadj]
  have hAQ : A * (1 - P) = 0 := by noncomm_ring [hAP]
  have hBP : B * P = 0 := by
    calc
      B * P = B - B * (1 - P) := by noncomm_ring
      _ = 0 := by rw [hBQ, sub_self]
  have hAbsAQ : absOp A * (1 - P) = 0 :=
    absOp_mul_eq_zero_of_mul_eq_zero A (1 - P) hAQ
  have hQAbsA : (1 - P) * absOp A = 0 :=
    mul_absOp_eq_zero_of_mul_eq_zero A (1 - P) hQadj hAQ
  have hAbsBP : absOp B * P = 0 :=
    absOp_mul_eq_zero_of_mul_eq_zero B P hBP
  have hPAbsB : P * absOp B = 0 :=
    mul_absOp_eq_zero_of_mul_eq_zero B P hPadj hBP
  constructor
  · calc
      absOp A * absOp B = absOp A * ((1 - P) * absOp B) := by
        congr 1
        calc
          absOp B = (1 - P) * absOp B + P * absOp B := by noncomm_ring
          _ = (1 - P) * absOp B := by rw [hPAbsB, add_zero]
      _ = (absOp A * (1 - P)) * absOp B := by rw [mul_assoc]
      _ = 0 := by rw [hAbsAQ, zero_mul]
  · calc
      absOp B * absOp A = absOp B * (P * absOp A) := by
        congr 1
        calc
          absOp A = P * absOp A + (1 - P) * absOp A := by noncomm_ring
          _ = P * absOp A := by rw [hQAbsA, add_zero]
      _ = (absOp B * P) * absOp A := by rw [mul_assoc]
      _ = 0 := by rw [hAbsBP, zero_mul]

/-- The positive square root of an orthogonal energy sum is the sum of the two absolute values. -/
theorem absOp_eq_add_of_energy_eq_add
    (T A B : H →L[ℂ] H)
    (henergy : star T * T = star A * A + star B * B)
    (hAB : absOp A * absOp B = 0)
    (hBA : absOp B * absOp A = 0) :
    absOp T = absOp A + absOp B := by
  change CFC.sqrt (star T * T) = absOp A + absOp B
  apply CFC.sqrt_unique
  · calc
      (absOp A + absOp B) * (absOp A + absOp B) =
          star A * A + star B * B := by
            noncomm_ring [absOp_mul_self A, absOp_mul_self B, hAB, hBA]
      _ = star T * T := henergy.symm
  · exact add_nonneg (absOp_nonneg A) (absOp_nonneg B)

/-- Absolute value commutes with cubing on self-adjoint operators. -/
theorem absOp_cube_of_isSelfAdjoint (S : H →L[ℂ] H)
    (hS : IsSelfAdjoint S) :
    absOp (S ^ 3) = (absOp S) ^ 3 := by
  change CFC.sqrt (star (S ^ 3) * (S ^ 3)) = (absOp S) ^ 3
  apply CFC.sqrt_unique
  · have hSstar : star S = S := hS.star_eq
    have hA : absOp S * absOp S = S * S := by
      rw [absOp_mul_self, hSstar]
    have hSpowstar : star (S ^ 3) = S ^ 3 := by
      simp [hSstar]
    rw [hSpowstar]
    calc
      (absOp S) ^ 3 * (absOp S) ^ 3 =
          ((absOp S) * (absOp S)) ^ 3 := by noncomm_ring
      _ = (S * S) ^ 3 := by rw [hA]
      _ = S ^ 3 * S ^ 3 := by noncomm_ring
  · have hpos : (absOp S).IsPositive :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mp (absOp_nonneg S)
    have hpowpos : ((absOp S) ^ 3).IsPositive :=
      ⟨fun x y => hpos.inner_pow_left_eq_inner_pow_right 3 x y,
        fun x => by
          rw [ContinuousLinearMap.reApplyInnerSelf_apply,
            hpos.inner_pow_left_eq_inner_pow_right 3 x x]
          exact hpos.re_inner_pow_nonneg x 3⟩
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hpowpos

/-- Exact trace realization of the third Schatten mass. -/
theorem ofReal_schattenNorm_three_rpow_eq_opTrace_absOp_cube
    (S : H →L[ℂ] H) (hHS : S.IsHilbertSchmidt) :
    ((GaloisForLFunctions.HTGeometry.schattenNorm 3 S ^ (3 : ℝ) : ℝ) : ℂ) =
      opTrace ((absOp S) ^ 3) := by
  have hS2 : MemSchattenClass 2 S :=
    (memSchattenClass_two_iff_isHilbertSchmidt S).2 hHS
  have hAbsHS : (absOp S).IsHilbertSchmidt :=
    (isHilbertSchmidt_absOp_iff S).2 hHS
  have hAbs2 : MemSchattenClass 2 (absOp S) :=
    (memSchattenClass_two_iff_isHilbertSchmidt (absOp S)).2 hAbsHS
  obtain ⟨A, B, hA, hB, hfac⟩ :=
    GaloisForLFunctions.HTGeometry.exists_hilbertSchmidt_factorization_pow
      (p := 2) (T := absOp S) (a := 1) (b := 2)
      (by norm_num) hAbs2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hfac3 : (absOp S) ^ 3 = A ∘L B := by
    norm_num at hfac ⊢
    exact hfac
  have hcpt : IsCompactOperator S := hHS.isCompactOperator
  have hAbsCpt : IsCompactOperator (absOp S) := hAbsHS.isCompactOperator
  have hAbsSym : (absOp S).IsSymmetric :=
    isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_absOp S)
  have htrace : opTrace ((absOp S) ^ 3) =
      ∑' n, (((sgVal (absOp S) n : ℝ) : ℂ) ^ 3) :=
    opTrace_pow_eq_tsum_sgVal_pow hAbsCpt hAbsSym (m := 3)
      (by norm_num) hA hB hfac3
  rw [GaloisForLFunctions.HTGeometry.schattenNorm_rpow_eq_tsum
      (p := 3) (by norm_num), Complex.ofReal_tsum, htrace]
  apply tsum_congr
  intro n
  have hpos : (absOp S).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mp (absOp_nonneg S)
  have hsgnonneg : 0 ≤ sgVal (absOp S) n := sgVal_nonneg_of_isPositive hpos n
  have hsgabs := abs_sgVal_eq_singVal hAbsCpt hAbsSym n
  rw [abs_of_nonneg hsgnonneg, singVal_absOp,
    ← approxNumber_eq_singVal hcpt] at hsgabs
  rw [hsgabs]
  simp

/-- The nuclear norm of a self-adjoint Hilbert--Schmidt cube is its exact third Schatten mass. -/
theorem traceNorm_cube_eq_schattenNorm_three_rpow
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hHS : S.IsHilbertSchmidt) :
    traceNorm H (S ^ 3) =
      GaloisForLFunctions.HTGeometry.schattenNorm 3 S ^ (3 : ℝ) := by
  have hS2 : MemSchattenClass 2 S :=
    (memSchattenClass_two_iff_isHilbertSchmidt S).2 hHS
  have hS3 : MemSchattenClass 1 (S ^ 3) :=
    GaloisForLFunctions.HTGeometry.memSchattenClass_one_pow
      (p := 2) (by norm_num) hS2 (k := 3) (by norm_num) (by norm_num)
  apply Complex.ofReal_injective
  rw [ofReal_traceNorm_eq_opTrace_absOp hS3,
    absOp_cube_of_isSelfAdjoint S hS,
    ← ofReal_schattenNorm_three_rpow_eq_opTrace_absOp_cube S hHS]

/-- Orthogonal absolute-value channels add their exact cubic Schatten masses. -/
theorem traceNorm_cube_eq_add_schattenNorm_three_rpow
    (T A B : H →L[ℂ] H)
    (hTself : IsSelfAdjoint T) (hTHS : T.IsHilbertSchmidt)
    (hAHS : A.IsHilbertSchmidt) (hBHS : B.IsHilbertSchmidt)
    (henergy : star T * T = star A * A + star B * B)
    (hAB : absOp A * absOp B = 0)
    (hBA : absOp B * absOp A = 0) :
    traceNorm H (T ^ 3) =
      GaloisForLFunctions.HTGeometry.schattenNorm 3 A ^ (3 : ℝ) +
        GaloisForLFunctions.HTGeometry.schattenNorm 3 B ^ (3 : ℝ) := by
  have hT2 : MemSchattenClass 2 T :=
    (memSchattenClass_two_iff_isHilbertSchmidt T).2 hTHS
  have hT3 : MemSchattenClass 1 (T ^ 3) :=
    GaloisForLFunctions.HTGeometry.memSchattenClass_one_pow
      (p := 2) (by norm_num) hT2 (k := 3) (by norm_num) (by norm_num)
  have hAabsHS : (absOp A).IsHilbertSchmidt :=
    (isHilbertSchmidt_absOp_iff A).2 hAHS
  have hBabsHS : (absOp B).IsHilbertSchmidt :=
    (isHilbertSchmidt_absOp_iff B).2 hBHS
  have hA2 : MemSchattenClass 2 (absOp A) :=
    (memSchattenClass_two_iff_isHilbertSchmidt (absOp A)).2 hAabsHS
  have hB2 : MemSchattenClass 2 (absOp B) :=
    (memSchattenClass_two_iff_isHilbertSchmidt (absOp B)).2 hBabsHS
  have hA3 : MemSchattenClass 1 ((absOp A) ^ 3) :=
    GaloisForLFunctions.HTGeometry.memSchattenClass_one_pow
      (p := 2) (by norm_num) hA2 (k := 3) (by norm_num) (by norm_num)
  have hB3 : MemSchattenClass 1 ((absOp B) ^ 3) :=
    GaloisForLFunctions.HTGeometry.memSchattenClass_one_pow
      (p := 2) (by norm_num) hB2 (k := 3) (by norm_num) (by norm_num)
  have habs : absOp T = absOp A + absOp B :=
    absOp_eq_add_of_energy_eq_add T A B henergy hAB hBA
  have hcube : (absOp A + absOp B) ^ 3 = (absOp A) ^ 3 + (absOp B) ^ 3 := by
    noncomm_ring [hAB, hBA]
  apply Complex.ofReal_injective
  rw [ofReal_traceNorm_eq_opTrace_absOp hT3,
    absOp_cube_of_isSelfAdjoint T hTself, habs, hcube,
    opTrace_add_of_memSchattenClass_one hA3 hB3, Complex.ofReal_add,
    ofReal_schattenNorm_three_rpow_eq_opTrace_absOp_cube A hAHS,
    ofReal_schattenNorm_three_rpow_eq_opTrace_absOp_cube B hBHS]

end RHTower
