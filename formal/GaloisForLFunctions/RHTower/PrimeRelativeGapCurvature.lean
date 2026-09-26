import GaloisForLFunctions.HTGeometry.RelativeGapCurvature
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualFirstOrderGapFluctuation

/-!
# Exact curvature of consecutive relative prime gaps

The binary comparison of normalized prime spacings is a discrete logarithmic
curvature measurement. Distinct adjacent primes exclude its neutral state.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry

/-- Adjacent prime products measured against the central prime square. -/
def orderedPrimeStepDeterminant (n : ℕ) : ℝ :=
  stepDeterminant (nthPrimeSubtype n) (nthPrimeSubtype (n + 1))
    (nthPrimeSubtype (n + 2))

theorem orderedPrimeRelativeGap_eq_logRelativeStep (n : ℕ) :
    xiHeatCassiniOrderedPrimeRelativeGap n =
      logRelativeStep (Real.log (nthPrimeSubtype n : ℝ))
        (Real.log (nthPrimeSubtype (n + 1) : ℝ)) := by
  rw [← relativeStep_exp, Real.exp_log (nthPrimeSubtype_pos n),
    Real.exp_log (nthPrimeSubtype_pos (n + 1))]
  rfl

/-- The exact acceleration, including its normalization factor. -/
theorem orderedPrimeRelativeGap_difference (n : ℕ) :
    xiHeatCassiniOrderedPrimeRelativeGap (n + 1) -
      xiHeatCassiniOrderedPrimeRelativeGap n =
        orderedPrimeStepDeterminant n /
          ((nthPrimeSubtype n : ℝ) * (nthPrimeSubtype (n + 1) : ℝ)) := by
  unfold xiHeatCassiniOrderedPrimeRelativeGap xiHeatCassiniOrderedPrimeGap
    orderedPrimeStepDeterminant stepDeterminant
  simp only [Nat.add_assoc]
  field_simp [(nthPrimeSubtype_pos n).ne', (nthPrimeSubtype_pos (n + 1)).ne']
  ring

theorem orderedPrimeRelativeGap_lt_iff_log_curvature (n : ℕ) :
    xiHeatCassiniOrderedPrimeRelativeGap n <
      xiHeatCassiniOrderedPrimeRelativeGap (n + 1) ↔
        0 < logStepCurvature (Real.log (nthPrimeSubtype n : ℝ))
          (Real.log (nthPrimeSubtype (n + 1) : ℝ))
          (Real.log (nthPrimeSubtype (n + 2) : ℝ)) := by
  simp only [orderedPrimeRelativeGap_eq_logRelativeStep, Nat.add_assoc]
  exact logRelativeStep_lt_iff _ _ _

theorem orderedPrimeRelativeGap_lt_iff_determinant (n : ℕ) :
    xiHeatCassiniOrderedPrimeRelativeGap n <
      xiHeatCassiniOrderedPrimeRelativeGap (n + 1) ↔
        0 < orderedPrimeStepDeterminant n := by
  rw [← sub_pos, orderedPrimeRelativeGap_difference]
  exact div_pos_iff_of_pos_right
    (mul_pos (nthPrimeSubtype_pos n) (nthPrimeSubtype_pos (n + 1)))

/-- A geometric progression of three consecutive primes is impossible. -/
theorem orderedPrimeStepDeterminant_ne_zero (n : ℕ) :
    orderedPrimeStepDeterminant n ≠ 0 := by
  intro h
  have he : (nthPrimeSubtype n : ℝ) * (nthPrimeSubtype (n + 2) : ℝ) =
      (nthPrimeSubtype (n + 1) : ℝ) ^ (2 : ℕ) := by
    exact sub_eq_zero.mp h
  have hn : (nthPrimeSubtype n : ℕ) * (nthPrimeSubtype (n + 2) : ℕ) =
      (nthPrimeSubtype (n + 1) : ℕ) ^ (2 : ℕ) := by exact_mod_cast he
  have hd : (nthPrimeSubtype n : ℕ) ∣ (nthPrimeSubtype (n + 1) : ℕ) ^ (2 : ℕ) :=
    ⟨(nthPrimeSubtype (n + 2) : ℕ), hn.symm⟩
  have hd' := (nthPrimeSubtype n).prop.dvd_of_dvd_pow hd
  have heq := ((nthPrimeSubtype (n + 1)).prop.dvd_iff_eq
    (nthPrimeSubtype n).prop.ne_one).mp hd'
  exact (ne_of_lt (nthPrimeSubtype_strictMono (Nat.lt_succ_self n))) heq.symm

/-- Every prime impulse has a strict direction; no tie-breaking convention is needed. -/
theorem orderedPrimeRelativeGap_ne (n : ℕ) :
    xiHeatCassiniOrderedPrimeRelativeGap n ≠
      xiHeatCassiniOrderedPrimeRelativeGap (n + 1) := by
  intro h
  have hd := orderedPrimeRelativeGap_difference n
  rw [h, sub_self] at hd
  have hz := (div_eq_zero_iff).mp hd.symm
  rcases hz with hz | hz
  · exact orderedPrimeStepDeterminant_ne_zero n hz
  · exact (mul_ne_zero (nthPrimeSubtype_pos n).ne'
      (nthPrimeSubtype_pos (n + 1)).ne') hz

theorem orderedPrimeRelativeGap_dichotomy (n : ℕ) :
    xiHeatCassiniOrderedPrimeRelativeGap n < xiHeatCassiniOrderedPrimeRelativeGap (n + 1) ∨
      xiHeatCassiniOrderedPrimeRelativeGap (n + 1) < xiHeatCassiniOrderedPrimeRelativeGap n :=
  lt_or_gt_of_ne (orderedPrimeRelativeGap_ne n)

/-- Negating all prime values preserves every normalized step. -/
theorem orderedPrimeRelativeGap_negative_mirror (n : ℕ) :
    relativeStep (-(nthPrimeSubtype n : ℝ)) (-(nthPrimeSubtype (n + 1) : ℝ)) =
      xiHeatCassiniOrderedPrimeRelativeGap n := by
  rw [relativeStep_neg]
  rfl

end
end RHTower
