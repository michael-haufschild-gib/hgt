import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampingAverageOfTheRelativeLossSuffices

/-!
# The work integral is the energy drop

The relative loss integrates to the logarithm of the energy ratio; the work itself integrates to the
energy *difference*.  Both faces are exact, and the additive one is the sharper tool for the
converse direction:

`∫_a^c 2 W_T(ε) dε = E_T(c) − E_T(a)`  (`integral_signedDampingWork_eq`).

Two consequences.

* **The additive dictionary.**  With an admitted right end, admission at `a` is equivalent to a
  horizon-free bound on the integral of the *negative* work over `[a, c]`
  (`admits_iff_bounded_neg_work_integral`).  Together with the multiplicative equivalence of
  `TheAveragedBudgetIsExactlyAdmission` this pins both integrated forms of the budget to the
  conclusion exactly.
* **The visibility witness.**  If a damping is *not* admitted, the work cannot stay above any fixed
  negative level on the interval: for every constant there is a horizon and a damping in `[a, c]`
  at which the work is below it (`exists_signedDampingWork_lt_of_not_admits`).  So failure of the
  continuation is always visible as deep negative work at a specific damping and horizon, never as
  a diffuse effect.
-/

open Set Filter Finset MeasureTheory RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The exact additive identity -/

theorem intervalIntegrable_signedDampingWork {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    IntervalIntegrable (fun ε => 2 * signedDampingWork ε T) volume a c := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hac]
  exact (continuousOn_const.mul ((continuousOn_signedDampingWork T).mono
    fun x hx => mem_Ioi.mpr (lt_of_lt_of_le ha hx.1)))

/-- **The work integral is the energy drop.** -/
theorem integral_signedDampingWork_eq {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    (∫ ε in a..c, 2 * signedDampingWork ε T) = dampedMobiusEnergy c T - dampedMobiusEnergy a T := by
  have hderiv : ∀ ε ∈ uIcc a c,
      HasDerivAt (fun x => dampedMobiusEnergy x T) (2 * signedDampingWork ε T) ε := by
    rw [uIcc_of_le hac]
    exact fun ε hε => hasDerivAt_dampedMobiusEnergy (lt_of_lt_of_le ha hε.1) T
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_signedDampingWork ha hac T)

/-! ## §2. The additive dictionary -/

/-- **Admission is a horizon-free bound on the integrated negative work.** -/
theorem admits_iff_bounded_neg_work_integral {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c) :
    Admits dampedMobiusEnergy a ↔
      ∃ C : ℝ, ∀ T : ℕ, (∫ ε in a..c, -(2 * signedDampingWork ε T)) ≤ C := by
  have hint : ∀ T : ℕ, (∫ ε in a..c, -(2 * signedDampingWork ε T)) =
      dampedMobiusEnergy a T - dampedMobiusEnergy c T := by
    intro T
    have h := integral_signedDampingWork_eq ha hac T
    rw [intervalIntegral.integral_neg, h]
    ring
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨max B 0, fun T => ?_⟩
    rw [hint T]
    have := dampedMobiusEnergy_nonneg c T
    linarith [(hB T).trans (le_max_left B 0)]
  · rintro ⟨C, hC⟩
    obtain ⟨B, hB⟩ := hc
    refine ⟨C + max B 0, fun T => ?_⟩
    have h := hC T
    rw [hint T] at h
    linarith [(hB T).trans (le_max_left B 0)]

/-! ## §3. The visibility witness -/

/-- **Escape is visible as deep negative work.**  If `a` is not admitted then, for every constant,
some horizon and some damping of `[a, c]` carry work below that constant: the failure of
continuation always has a witness at a named damping and horizon. -/
theorem exists_signedDampingWork_lt_of_not_admits {a c : ℝ} (ha : 0 < a) (hac : a < c)
    (hc : Admits dampedMobiusEnergy c) (hnot : ¬ Admits dampedMobiusEnergy a) (C : ℝ) :
    ∃ (T : ℕ) (ε : ℝ), ε ∈ Icc a c ∧ signedDampingWork ε T < -C := by
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hB⟩ := hc
  -- with the work bounded below on the interval, the energy at `a` is bounded
  refine hnot ⟨max B 0 + 2 * C * (c - a), fun T => ?_⟩
  have hge : ∀ ε ∈ Icc a c, -(2 * C) ≤ 2 * signedDampingWork ε T := by
    intro ε hε
    have := hcon T ε hε
    linarith
  have hmono : (∫ ε in a..c, -(2 * C)) ≤ ∫ ε in a..c, 2 * signedDampingWork ε T :=
    intervalIntegral.integral_mono_on hac.le
      (intervalIntegrable_const)
      (intervalIntegrable_signedDampingWork ha hac.le T) hge
  rw [intervalIntegral.integral_const, integral_signedDampingWork_eq ha hac.le T] at hmono
  have hBT := (hB T).trans (le_max_left B 0)
  have hsmul : (c - a) • (-(2 * C)) = -(2 * C * (c - a)) := by
    simp only [smul_eq_mul]
    ring
  rw [hsmul] at hmono
  linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
