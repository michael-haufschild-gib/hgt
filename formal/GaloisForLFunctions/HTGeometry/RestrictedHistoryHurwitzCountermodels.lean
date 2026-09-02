import GaloisForLFunctions.Hurwitz.ContinuedJointHypertranscendence
import GaloisForLFunctions.HTGeometry.HurwitzMonodromyClosureLawstackResonanceRankLaw
import GaloisForLFunctions.HTGeometry.ConstitutiveCyclicProcessFourShadow
import GaloisForLFunctions.RHTower.XiDivisorMonodromyImage

/-!
# Hurwitz phase/radial countermodels for restricted history

This module formalizes Countertheorem 5.2 of the restricted-history card at its three stated
exponents.  Each continued Hurwitz function is hypertranscendental in the shift variable.  Their
monodromy phases separate exact periodicity from irrational recurrence, while adding `I` preserves
the phase and changes the radial modulus to `exp (2π)`, whose powers escape.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open HurwitzOrbit HurwitzJointLadder HurwitzZetaContinuation

def restrictedHistoryExponentZero : ℂ := 3 / 2
def restrictedHistoryExponentOne : ℂ := (Real.sqrt 2 : ℂ)
def restrictedHistoryExponentTwo : ℂ := (Real.sqrt 2 : ℂ) + Complex.I

theorem restrictedHistoryExponentZero_nonintegral (m : ℤ) :
    restrictedHistoryExponentZero ≠ (m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp [restrictedHistoryExponentZero] at hre
  have hm : (2 * m : ℤ) = 3 := by
    exact_mod_cast (show (2 : ℝ) * (m : ℝ) = 3 by linarith)
  omega

theorem restrictedHistoryExponentOne_nonintegral (m : ℤ) :
    restrictedHistoryExponentOne ≠ (m : ℂ) := by
  intro h
  have hre : Real.sqrt 2 = (m : ℝ) := by
    exact_mod_cast congrArg Complex.re h
  exact (irrational_sqrt_two.ne_rat (m : ℚ)) (by exact_mod_cast hre)

theorem restrictedHistoryExponentTwo_nonintegral (m : ℤ) :
    restrictedHistoryExponentTwo ≠ (m : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  norm_num [restrictedHistoryExponentTwo] at him

theorem restrictedHistoryExponentZero_gt_one :
    1 < restrictedHistoryExponentZero.re := by
  norm_num [restrictedHistoryExponentZero]

theorem restrictedHistoryExponentOne_gt_one :
    1 < restrictedHistoryExponentOne.re := by
  have hnonneg := Real.sqrt_nonneg 2
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [restrictedHistoryExponentOne, ofReal_re]
  nlinarith

theorem restrictedHistoryExponentTwo_gt_one :
    1 < restrictedHistoryExponentTwo.re := by
  simpa only [restrictedHistoryExponentTwo, restrictedHistoryExponentOne, add_re,
    ofReal_re, I_re, add_zero] using restrictedHistoryExponentOne_gt_one

/-- The continued Hurwitz function at `s = 3/2` is hypertranscendental in its shift. -/
theorem restrictedHistoryExponentZero_hypertranscendental
    (N : ℕ) (P : MvPolynomial (Fin 1 × Fin (N + 1)) (Polynomial ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => iteratedDeriv (jk.2 : ℕ)
          (continuedHzeta restrictedHistoryExponentZero) a) P = 0) :
    P = 0 := by
  apply continued_joint_hzeta_hypertranscendental_in_shift_of_integerResidueSeparated
    (s := fun _ : Fin 1 => restrictedHistoryExponentZero)
  · intro j m
    exact restrictedHistoryExponentZero_nonintegral m
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · simpa using hrel

/-- The continued Hurwitz function at `s = √2` is hypertranscendental in its shift. -/
theorem restrictedHistoryExponentOne_hypertranscendental
    (N : ℕ) (P : MvPolynomial (Fin 1 × Fin (N + 1)) (Polynomial ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => iteratedDeriv (jk.2 : ℕ)
          (continuedHzeta restrictedHistoryExponentOne) a) P = 0) :
    P = 0 := by
  apply continued_joint_hzeta_hypertranscendental_in_shift_of_integerResidueSeparated
    (s := fun _ : Fin 1 => restrictedHistoryExponentOne)
  · intro j m
    exact restrictedHistoryExponentOne_nonintegral m
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · simpa using hrel

/-- The continued Hurwitz function at `s = √2 + I` is hypertranscendental in its shift. -/
theorem restrictedHistoryExponentTwo_hypertranscendental
    (N : ℕ) (P : MvPolynomial (Fin 1 × Fin (N + 1)) (Polynomial ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => iteratedDeriv (jk.2 : ℕ)
          (continuedHzeta restrictedHistoryExponentTwo) a) P = 0) :
    P = 0 := by
  apply continued_joint_hzeta_hypertranscendental_in_shift_of_integerResidueSeparated
    (s := fun _ : Fin 1 => restrictedHistoryExponentTwo)
  · intro j m
    exact restrictedHistoryExponentTwo_nonintegral m
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · simpa using hrel

/-- Unit-circle phase of real Hurwitz monodromy. -/
def realHurwitzPhase (x : ℝ) : Circle :=
  ⟨monoScalar (x : ℂ), by
    change monoScalar (x : ℂ) ∈ Metric.sphere 0 1
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, RHTower.norm_monoScalar]
    simp⟩

/-- `s = 3/2` has an exact phase period of order two. -/
theorem restrictedHistoryExponentZero_phase_periodic :
    realHurwitzPhase (3 / 2) ^ 2 = 1 := by
  apply Subtype.ext
  change monoScalar ((3 / 2 : ℝ) : ℂ) ^ 2 = 1
  rw [monoScalar_pow_eq_one_iff_nat]
  refine ⟨3, ?_⟩
  norm_num

/-- `s = √2` has no nonzero natural phase period. -/
theorem restrictedHistoryExponentOne_phase_aperiodic (n : ℕ) (hn : 0 < n) :
    realHurwitzPhase (Real.sqrt 2) ^ n ≠ 1 := by
  intro h
  have hc : monoScalar (Real.sqrt 2 : ℂ) ^ n = 1 := congrArg Subtype.val h
  rw [monoScalar_pow_eq_one_iff_nat] at hc
  obtain ⟨m, hm⟩ := hc
  have hre : (n : ℝ) * Real.sqrt 2 = (m : ℝ) := by
    exact_mod_cast congrArg Complex.re hm
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt 2 = (m : ℝ) / (n : ℝ) := by
    field_simp
    linarith
  exact (irrational_sqrt_two.ne_rat ((m : ℚ) / (n : ℚ))) (by
    exact_mod_cast hsqrt)

/-- The irrational phase is nevertheless recurrent in the compact circle. -/
theorem restrictedHistoryExponentOne_phase_recurrent
    {U : Set Circle} (hU : U ∈ 𝓝 (1 : Circle)) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ realHurwitzPhase (Real.sqrt 2) ^ n ∈ U :=
  exists_pow_mem_of_compactSpace _ hU M

/-- `s = √2 + I` has exactly the same normalized phase as `s = √2`. -/
theorem restrictedHistoryExponentTwo_same_phase :
    realHurwitzPhase restrictedHistoryExponentTwo.re =
      realHurwitzPhase restrictedHistoryExponentOne.re := by
  simp [restrictedHistoryExponentTwo, restrictedHistoryExponentOne]

theorem restrictedHistoryExponentZero_monoScalar_norm :
    ‖monoScalar restrictedHistoryExponentZero‖ = 1 := by
  rw [RHTower.norm_monoScalar]
  simp [restrictedHistoryExponentZero]

theorem restrictedHistoryExponentOne_monoScalar_norm :
    ‖monoScalar restrictedHistoryExponentOne‖ = 1 := by
  rw [RHTower.norm_monoScalar]
  simp [restrictedHistoryExponentOne]

/-- The shifted exponent has monodromy modulus exactly `exp (2π)`. -/
theorem restrictedHistoryExponentTwo_monoScalar_norm :
    ‖monoScalar restrictedHistoryExponentTwo‖ = Real.exp (2 * Real.pi) := by
  rw [RHTower.norm_monoScalar]
  simp [restrictedHistoryExponentTwo]

/-- Powers of the shifted exponent's monodromy escape radially. -/
theorem restrictedHistoryExponentTwo_radial_escape :
    Tendsto (fun n : ℕ => ‖monoScalar restrictedHistoryExponentTwo ^ n‖)
      atTop atTop := by
  have hbase : 1 < Real.exp (2 * Real.pi) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by positivity)
  simpa [norm_pow, restrictedHistoryExponentTwo_monoScalar_norm] using
    tendsto_pow_atTop_atTop_of_one_lt hbase

end

end GaloisForLFunctions.HTGeometry
