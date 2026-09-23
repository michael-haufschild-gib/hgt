import GaloisForLFunctions.RHTower.ConstrainedProlateSignedSpectrum

/-!
# Ordering of the actual signed prolate leakages

The constrained-prolate cards work with a leakage hierarchy `0 < d_0 ≤ d_1 ≤ d_2 ≤ …` for the
compressed-Fourier eigenvalues, and take that ordering from the classical prolate numbering.  For
the **actual** operator `P_a F P_a` the tree constructs its spectrum by the signed greedy
exhaustion, and there the ordering is not an assumption: the absolute signed value is the
constrained norm `orthSup` at that stage, and `orthSup` is antitone by construction because the
admissible set shrinks.

This module records that.  It gives, unconditionally and for the concrete operator, the antitone
law for `|χ_n|`, the resulting monotone law for the leakage `d_n = 1 - χ_n²`, and the two-sided
bound `0 ≤ d_n ≤ 1`.

Nothing here identifies the greedy enumeration with the classical `4j` prolate numbering; that is a
separate statement.  What is removed is the need to *assume* an ordering for the greedy family.
-/

open Filter

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The absolute signed greedy values are antitone: they are the constrained norms, and the
constrained norm decreases because its admissible set shrinks. -/
theorem abs_sgVal_antitone {S : H →L[ℂ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) : Antitone (fun n => |sgVal S n|) := by
  have habs : (fun n => |sgVal S n|) = fun n => orthSup S (sgVec S) n :=
    funext (abs_sgVal hcpt hsym)
  rw [habs]
  exact orthSup_antitone S (sgVec S)

end ContinuousLinearMap

namespace RHTower

noncomputable section

/-- The actual signed prolate eigenvalues decrease in absolute value. -/
theorem evenProlateSignedAbsValue_antitone (a : ℝ) (ha : 0 < a) :
    Antitone (fun n => |evenProlateSignedValue a n|) :=
  ContinuousLinearMap.abs_sgVal_antitone
    (isCompactOperator_evenTimeBandFourier a ha)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (adjoint_evenTimeBandFourier a))

/-- The leakage of the actual signed prolate spectrum, `d_n = 1 - χ_n²`. -/
def evenProlateSignedLeakage (a : ℝ) (n : ℕ) : ℝ :=
  1 - evenProlateSignedValue a n ^ (2 : ℕ)

/-- **The actual leakage hierarchy is monotone**, with no classical input: squaring an antitone
nonnegative sequence keeps it antitone, and subtracting from one reverses the order. -/
theorem evenProlateSignedLeakage_monotone (a : ℝ) (ha : 0 < a) :
    Monotone (evenProlateSignedLeakage a) := by
  intro m n hmn
  have habs := evenProlateSignedAbsValue_antitone a ha hmn
  have hsq : evenProlateSignedValue a n ^ (2 : ℕ) ≤ evenProlateSignedValue a m ^ (2 : ℕ) := by
    rw [← sq_abs (evenProlateSignedValue a n), ← sq_abs (evenProlateSignedValue a m)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  unfold evenProlateSignedLeakage
  linarith

theorem evenProlateSignedValue_sq_le_one (a : ℝ) (n : ℕ) :
    evenProlateSignedValue a n ^ (2 : ℕ) ≤ 1 := by
  rcases evenProlateSignedMode_norm_zero_or_one a n with hzero | hone
  · have : evenProlateSignedValue a n = 0 :=
      ContinuousLinearMap.sgVal_zero_of_dead hzero
    rw [this]
    norm_num
  · have happ := evenProlateConcentration_apply_signedMode a n
    have hnorm : ‖evenProlateConcentration a (evenProlateSignedMode a n)‖
        ≤ ‖evenProlateConcentration a‖ := by
      calc
        ‖evenProlateConcentration a (evenProlateSignedMode a n)‖
            ≤ ‖evenProlateConcentration a‖ * ‖evenProlateSignedMode a n‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ = ‖evenProlateConcentration a‖ := by rw [hone, mul_one]
    rw [happ, norm_smul] at hnorm
    have hsq : ‖((evenProlateSignedValue a n ^ (2 : ℕ) : ℝ) : ℂ)‖
        = evenProlateSignedValue a n ^ (2 : ℕ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [hsq, hone, mul_one] at hnorm
    exact hnorm.trans (norm_evenProlateConcentration_le_one a)

theorem evenProlateSignedLeakage_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ evenProlateSignedLeakage a n := by
  unfold evenProlateSignedLeakage
  linarith [evenProlateSignedValue_sq_le_one a n]

theorem evenProlateSignedLeakage_le_one (a : ℝ) (n : ℕ) :
    evenProlateSignedLeakage a n ≤ 1 := by
  unfold evenProlateSignedLeakage
  nlinarith [sq_nonneg (evenProlateSignedValue a n)]

/-- The actual leakage hierarchy exhausts: `d_n → 1`. -/
theorem evenProlateSignedLeakage_tendsto_one (a : ℝ) (ha : 0 < a) :
    Tendsto (evenProlateSignedLeakage a) atTop (nhds 1) := by
  have hz := evenProlateSignedValue_tendsto_zero a ha
  have hsq : Tendsto (fun n => evenProlateSignedValue a n ^ (2 : ℕ)) atTop (nhds 0) := by
    simpa using hz.pow 2
  unfold evenProlateSignedLeakage
  simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub hsq

end

end RHTower
