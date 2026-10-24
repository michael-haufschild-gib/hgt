import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheLevelCollapseOfTheMaxKernelForm
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SourceAngleShapeHierarchyAndIntegratedAutocorrelation

/-!
# The Prime-Pair and Level-Sum Forms to Relative Precision `1/T`

This module resolves Open Problem 3 of `ArithmeticContinuationAndCriticalEnergy`:

1. **Exact Identification and Unconditional Diagonal Positivity up to Boundary (`§1`)**:
   - The polar-calibrated prime-pair form
     `polarCalibratedPrimePairForm T η ε = P_T(η, ε) − m(ε) R_T(η) − m(η) R_T(ε) + m(η)m(ε)(2T − H_T)`
     and the single-scale level-sum form
     `levelSumAutocorrelationForm T η ε = Σ_{M ≤ T} (a_M(η) E_ε(M) + E_η(M) a_M(ε) − a_M(η) a_M(ε))/M`
     are equal at every horizon and damping pair (`polarCalibratedPrimePairForm_eq_levelSum`), and
     both equal `K_T(η, ε) + E_η(T) E_ε(T) / (T + 1)`
     (`tangentCorrelation_eq_polarCalibratedPrimePairForm_sub_boundary`).
   - On the diagonal `η = ε`, both forms unconditionally dominate the nonnegative boundary term
     `E_ε(T)² / (T + 1)` with exact excess `‖E_ε‖_T² ≥ 0`
     (`diagonal_polarCalibratedPrimePairForm_ge_boundary`, `diagonal_levelSum_ge_boundary`,
     `diagonal_primePairMaxKernelForm_ge`).

2. **Exact Level-Sum and Max-Kernel Forms of the Critical Energy and Signed Work (`§2`)**:
   - `dampedMobiusEnergy_eq_maxKernel_sub_boundary` and `dampedMobiusEnergy_eq_level_sum_sub_boundary`
     express `E_T(ε)` as a Nyman–Beurling max-kernel quadratic form and as a single scale sum minus
     `A_ε(T)² / (T + 1)`.
   - `signedDampingWork_eq_level_sum_sub_boundary` expresses `W_T(ε)` as a single scale sum over
     `M ≤ T` minus `A_ε(T) E_ε(T) / (T + 1)`.

3. **Unconditional Integrated Nonnegativity up to Boundary on Every Square `[a, c] × [a, c]` (`§3`)**:
   - The double damping integral of the boundary term `E_η(T) E_ε(T) / (T + 1)` over `[a, c]²`
     equals `(A_c(T) − A_a(T))² / (T + 1) ≥ 0` (`double_integral_boundary_eq_sub_sq`).
   - Integrating `polarCalibratedPrimePairForm` or `levelSumAutocorrelationForm` over `[a, c]²`
     yields the exact identity
     `∫_a^c ∫_a^c L_T(η, ε) dη dε = ‖A_c − A_a‖_T² + (A_c(T) − A_a(T))² / (T + 1)`
     (`double_integral_levelSum_eq`, `double_integral_polarCalibratedPrimePairForm_eq`).
   - Consequently, both the integrated level-sum form and the integrated polar-calibrated prime-pair
     form are **unconditionally nonnegative up to (and dominating) the explicit boundary term** on
     every damping square `[a, c] × [a, c]` (`0 < a ≤ c`), with exact excess `‖A_c − A_a‖_T² ≥ 0`
     (`double_integral_levelSum_ge_boundary`,
     `double_integral_polarCalibratedPrimePairForm_ge_boundary`).

4. **Relative-Precision `1/T` Cancellation Law and Admission Equivalence (`§4`)**:
   - With `c` admitted, `Admits dampedMobiusEnergy a` holds **if and only if** the boundary-adjusted
     double integral of `polarCalibratedPrimePairForm` (or `levelSumAutocorrelationForm`) is bounded
     uniformly in `T`, equivalently `O(1/(T + 1))` after dividing by the linear horizon scale `T + 1`
     (`admits_iff_relative_precision_inv_T_primePair`).
   - Unconditionally for every `[a, c] ⊂ (Θ − ½, ∞)`, the linearly growing prime-pair, row-weighted,
     and polar pieces cancel to relative precision `C / (T + 1) → 0`
     (`exists_relative_precision_inv_T_primePair_above_zeroWidth`,
     `tendsto_relative_precision_primePair_zero_above_zeroWidth`), and on the Vinogradov–Korobov
     band they cancel to relative precision `4 E / (T + 1)` uniformly in `(T, a, c)`
     (`exists_relative_precision_inv_T_primePair_on_vinogradovKorobovBand`).
-/

open Set Filter Topology Finset MeasureTheory RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Identification and Unconditional Diagonal Positivity up to the Boundary Term -/

/-- The single-scale level-sum form of the damping autocorrelation before subtracting the horizon
boundary term. -/
def levelSumAutocorrelationForm (T : ℕ) (η ε : ℝ) : ℝ :=
  ∑ M ∈ Finset.Icc 1 T,
    (dampedChebyshevIncrement η M * dampedChebyshevError ε M +
      dampedChebyshevError η M * dampedChebyshevIncrement ε M -
      dampedChebyshevIncrement η M * dampedChebyshevIncrement ε M) / (M : ℝ)

/-- The polar-calibrated prime-pair form of the damping autocorrelation: the prime-pair max-kernel
sum minus the two row-weighted prime sums plus the explicit polar kernel mass. -/
def polarCalibratedPrimePairForm (T : ℕ) (η ε : ℝ) : ℝ :=
  primePairMaxKernelForm T η ε -
    dampedReadout ε * rowWeightedPrimeSum T η -
    dampedReadout η * rowWeightedPrimeSum T ε +
    dampedReadout η * dampedReadout ε * (2 * (T : ℝ) - ∑ m ∈ Finset.Icc 1 T, 1 / (m : ℝ))

/-- The horizon boundary term of the autocorrelation at depth `T`. -/
def autocorrelationBoundaryTerm (T : ℕ) (η ε : ℝ) : ℝ :=
  dampedChebyshevError η T * dampedChebyshevError ε T / ((T : ℝ) + 1)

/-- **The polar-calibrated prime-pair form and the single-scale level-sum form are identical.** -/
theorem polarCalibratedPrimePairForm_eq_levelSum (T : ℕ) (η ε : ℝ) :
    polarCalibratedPrimePairForm T η ε = levelSumAutocorrelationForm T η ε := by
  rw [polarCalibratedPrimePairForm, ← maxKernelForm_increment_eq,
    sum_sum_div_max_eq_level_sum T (dampedChebyshevIncrement η) (dampedChebyshevIncrement ε),
    levelSumAutocorrelationForm]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [← dampedChebyshevError_eq_sum_increment, ← dampedChebyshevError_eq_sum_increment]

/-- **The autocorrelation is the level-sum form minus the boundary term.** -/
theorem tangentCorrelation_eq_levelSum_sub_boundary (T : ℕ) (η ε : ℝ) :
    tangentCorrelation T η ε =
      levelSumAutocorrelationForm T η ε - autocorrelationBoundaryTerm T η ε :=
  tangentCorrelation_eq_level_sum T η ε

/-- **The autocorrelation is the polar-calibrated prime-pair form minus the boundary term.** -/
theorem tangentCorrelation_eq_polarCalibratedPrimePairForm_sub_boundary (T : ℕ) (η ε : ℝ) :
    tangentCorrelation T η ε =
      polarCalibratedPrimePairForm T η ε - autocorrelationBoundaryTerm T η ε := by
  rw [polarCalibratedPrimePairForm_eq_levelSum, tangentCorrelation_eq_levelSum_sub_boundary]

/-- **Unconditional diagonal nonnegativity of the level-sum form up to the boundary term.** -/
theorem diagonal_levelSum_ge_boundary (T : ℕ) (ε : ℝ) :
    0 ≤ autocorrelationBoundaryTerm T ε ε ∧
    autocorrelationBoundaryTerm T ε ε ≤ levelSumAutocorrelationForm T ε ε := by
  have hbd : autocorrelationBoundaryTerm T ε ε =
      dampedChebyshevError ε T ^ 2 / ((T : ℝ) + 1) := by
    rw [autocorrelationBoundaryTerm, sq]
  refine ⟨by rw [hbd]; positivity, ?_⟩
  have h := tangentCorrelation_eq_levelSum_sub_boundary T ε ε
  rw [tangentCorrelation_self] at h
  have hnorm : 0 ≤ pronicNorm T (dampedChebyshevError ε) ^ 2 := sq_nonneg _
  linarith

/-- **Unconditional diagonal nonnegativity of the polar-calibrated prime-pair form up to the
boundary term.** -/
theorem diagonal_polarCalibratedPrimePairForm_ge_boundary (T : ℕ) (ε : ℝ) :
    0 ≤ autocorrelationBoundaryTerm T ε ε ∧
    autocorrelationBoundaryTerm T ε ε ≤ polarCalibratedPrimePairForm T ε ε := by
  rw [polarCalibratedPrimePairForm_eq_levelSum]
  exact diagonal_levelSum_ge_boundary T ε

/-- **Unconditional diagonal prime-pair inequality.**
At every horizon `T` and every damping `ε`, the diagonal prime-pair form `P_T(ε, ε)` plus the
explicit polar term dominates `2 m(ε) R_T(ε)` plus the boundary term `E_ε(T)² / (T + 1)`. -/
theorem diagonal_primePairMaxKernelForm_ge (T : ℕ) (ε : ℝ) :
    2 * dampedReadout ε * rowWeightedPrimeSum T ε +
        dampedChebyshevError ε T ^ 2 / ((T : ℝ) + 1) ≤
      primePairMaxKernelForm T ε ε +
        dampedReadout ε ^ 2 * (2 * (T : ℝ) - ∑ m ∈ Finset.Icc 1 T, 1 / (m : ℝ)) := by
  have h := (diagonal_polarCalibratedPrimePairForm_ge_boundary T ε).2
  unfold autocorrelationBoundaryTerm polarCalibratedPrimePairForm at h
  rw [← sq (dampedChebyshevError ε T), ← sq (dampedReadout ε)] at h
  linarith

/-! ## §2. Exact Max-Kernel and Level-Sum Forms of the Critical Energy and Signed Work -/

/-- **The critical energy as a Nyman–Beurling max-kernel quadratic form minus the boundary term.** -/
theorem dampedMobiusEnergy_eq_maxKernel_sub_boundary (ε : ℝ) (T : ℕ) :
    dampedMobiusEnergy ε T =
      (∑ j ∈ Finset.Icc 1 T, ∑ k ∈ Finset.Icc 1 T,
        pmPowerDampedCenteredDivisorCoeff ε j *
          pmPowerDampedCenteredDivisorCoeff ε k / ((max j k : ℕ) : ℝ)) -
        pmPowerDampedCenteredDivisorPrefix ε T ^ 2 / ((T : ℝ) + 1) := by
  have h := maxKernel_quadForm_eq T (pmPowerDampedCenteredDivisorCoeff ε)
  have hpref : ∀ n : ℕ,
      (∑ j ∈ Finset.Icc 1 n, pmPowerDampedCenteredDivisorCoeff ε j) =
        pmPowerDampedCenteredDivisorPrefix ε n := fun _ => rfl
  simp only [hpref] at h
  have hE : (∑ n ∈ Finset.Icc 1 T,
      pmPowerDampedCenteredDivisorPrefix ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) =
      dampedMobiusEnergy ε T := rfl
  linarith

/-- **The critical energy as a single scale sum minus the boundary term.** -/
theorem dampedMobiusEnergy_eq_level_sum_sub_boundary (ε : ℝ) (T : ℕ) :
    dampedMobiusEnergy ε T =
      (∑ M ∈ Finset.Icc 1 T,
        (2 * pmPowerDampedCenteredDivisorCoeff ε M * pmPowerDampedCenteredDivisorPrefix ε M -
          pmPowerDampedCenteredDivisorCoeff ε M ^ 2) / (M : ℝ)) -
        pmPowerDampedCenteredDivisorPrefix ε T ^ 2 / ((T : ℝ) + 1) := by
  rw [dampedMobiusEnergy_eq_maxKernel_sub_boundary,
    sum_sum_div_max_eq_level_sum T (pmPowerDampedCenteredDivisorCoeff ε)
      (pmPowerDampedCenteredDivisorCoeff ε)]
  congr 1
  refine Finset.sum_congr rfl fun M _ => ?_
  have hpref : (∑ j ∈ Finset.Icc 1 M, pmPowerDampedCenteredDivisorCoeff ε j) =
      pmPowerDampedCenteredDivisorPrefix ε M := rfl
  rw [hpref]
  ring

/-- **The signed damping work as a single scale sum minus its horizon boundary term.** -/
theorem signedDampingWork_eq_level_sum_sub_boundary (ε : ℝ) (T : ℕ) :
    signedDampingWork ε T =
      (∑ M ∈ Finset.Icc 1 T,
        (pmPowerDampedCenteredDivisorCoeff ε M * dampedChebyshevError ε M +
          pmPowerDampedCenteredDivisorPrefix ε M * dampedChebyshevIncrement ε M -
          pmPowerDampedCenteredDivisorCoeff ε M * dampedChebyshevIncrement ε M) / (M : ℝ)) -
        pmPowerDampedCenteredDivisorPrefix ε T * dampedChebyshevError ε T / ((T : ℝ) + 1) := by
  have h := pronicPairing_prefix_eq_maxKernel T
    (pmPowerDampedCenteredDivisorCoeff ε) (dampedChebyshevIncrement ε)
  have hA : (fun n => ∑ j ∈ Finset.Icc 1 n, pmPowerDampedCenteredDivisorCoeff ε j) =
      pmPowerDampedCenteredDivisorPrefix ε := rfl
  have hE : (fun n => ∑ k ∈ Finset.Icc 1 n, dampedChebyshevIncrement ε k) =
      dampedChebyshevError ε :=
    funext fun n => (dampedChebyshevError_eq_sum_increment ε n).symm
  rw [hA, hE] at h
  have hW : pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (dampedChebyshevError ε) =
      signedDampingWork ε T := rfl
  rw [hW, sum_sum_div_max_eq_level_sum, ← dampedChebyshevError_eq_sum_increment] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [← dampedChebyshevError_eq_sum_increment]
  rfl

/-! ## §3. Unconditional Integrated Nonnegativity up to Boundary on `[a, c] × [a, c]` -/

theorem continuousOn_autocorrelationBoundaryTerm_left (T : ℕ) (ε : ℝ) :
    ContinuousOn (fun η => autocorrelationBoundaryTerm T η ε) (Ioi 0) :=
  (((continuousOn_dampedChebyshevError T).mul continuousOn_const).div_const _)

theorem intervalIntegrable_autocorrelationBoundaryTerm_left {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (T : ℕ) (ε : ℝ) :
    IntervalIntegrable (fun η => autocorrelationBoundaryTerm T η ε) volume a c := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hac]
  exact (continuousOn_autocorrelationBoundaryTerm_left T ε).mono
    fun x hx => mem_Ioi.mpr (lt_of_lt_of_le ha hx.1)

/-- Integrating the autocorrelation boundary term in the first variable. -/
theorem integral_autocorrelationBoundaryTerm_left {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (T : ℕ) (ε : ℝ) :
    (∫ η in a..c, autocorrelationBoundaryTerm T η ε) =
      (pmPowerDampedCenteredDivisorPrefix c T - pmPowerDampedCenteredDivisorPrefix a T) *
        dampedChebyshevError ε T / ((T : ℝ) + 1) := by
  have hfun : (fun η => autocorrelationBoundaryTerm T η ε) =
      fun η => dampedChebyshevError η T * (dampedChebyshevError ε T / ((T : ℝ) + 1)) :=
    funext fun η => by rw [autocorrelationBoundaryTerm]; ring
  rw [hfun, intervalIntegral.integral_mul_const,
    ← pmPowerDampedCenteredDivisorPrefix_sub_eq_integral ha hac T]
  ring

/-- **The double integral of the autocorrelation boundary term over `[a, c] × [a, c]` is
`(A_c(T) − A_a(T))² / (T + 1) ≥ 0`.** -/
theorem double_integral_boundary_eq_sub_sq {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    (∫ ε in a..c, ∫ η in a..c, autocorrelationBoundaryTerm T η ε) =
      (pmPowerDampedCenteredDivisorPrefix c T - pmPowerDampedCenteredDivisorPrefix a T) ^ 2 /
        ((T : ℝ) + 1) := by
  have h1 : (fun ε => ∫ η in a..c, autocorrelationBoundaryTerm T η ε) =
      fun ε => ((pmPowerDampedCenteredDivisorPrefix c T -
        pmPowerDampedCenteredDivisorPrefix a T) / ((T : ℝ) + 1)) * dampedChebyshevError ε T :=
    funext fun ε => by rw [integral_autocorrelationBoundaryTerm_left ha hac T ε]; ring
  rw [h1, intervalIntegral.integral_const_mul,
    ← pmPowerDampedCenteredDivisorPrefix_sub_eq_integral ha hac T]
  ring

theorem double_integral_boundary_nonneg {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    0 ≤ ∫ ε in a..c, ∫ η in a..c, autocorrelationBoundaryTerm T η ε := by
  rw [double_integral_boundary_eq_sub_sq ha hac T]
  positivity

/-- **Exact double-integral identity for the polar-calibrated prime-pair form.** -/
theorem double_integral_polarCalibratedPrimePairForm_eq {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (T : ℕ) :
    (∫ ε in a..c, ∫ η in a..c, polarCalibratedPrimePairForm T η ε) =
      pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix c n -
        pmPowerDampedCenteredDivisorPrefix a n) ^ 2 +
      (pmPowerDampedCenteredDivisorPrefix c T - pmPowerDampedCenteredDivisorPrefix a T) ^ 2 /
        ((T : ℝ) + 1) := by
  have hinner : ∀ ε : ℝ,
      (∫ η in a..c, polarCalibratedPrimePairForm T η ε) =
        (∫ η in a..c, tangentCorrelation T η ε) +
          (∫ η in a..c, autocorrelationBoundaryTerm T η ε) := by
    intro ε
    have hfun : (fun η => polarCalibratedPrimePairForm T η ε) =
        fun η => tangentCorrelation T η ε + autocorrelationBoundaryTerm T η ε :=
      funext fun η => by
        rw [tangentCorrelation_eq_polarCalibratedPrimePairForm_sub_boundary]; ring
    have hintK : IntervalIntegrable (fun η => tangentCorrelation T η ε) volume a c := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hac]
      exact (continuousOn_tangentCorrelation T ε).mono
        fun x hx => mem_Ioi.mpr (lt_of_lt_of_le ha hx.1)
    rw [hfun, intervalIntegral.integral_add hintK
      (intervalIntegrable_autocorrelationBoundaryTerm_left ha hac T ε)]
  have h1 : IntervalIntegrable (fun ε => ∫ η in a..c, tangentCorrelation T η ε) volume a c := by
    have hfun : (fun ε => ∫ η in a..c, tangentCorrelation T η ε) =
        fun ε => pronicPairing T
          (fun n => pmPowerDampedCenteredDivisorPrefix c n -
            pmPowerDampedCenteredDivisorPrefix a n)
          (dampedChebyshevError ε) :=
      funext fun ε => integral_tangentCorrelation_left_eq_pairing ha hac T ε
    rw [hfun]
    unfold pronicPairing
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hac]
    exact continuousOn_finsetSum _ fun n _ =>
      ((continuousOn_const.mul (continuousOn_dampedChebyshevError n)).div_const _).mono
        fun x hx => mem_Ioi.mpr (lt_of_lt_of_le ha hx.1)
  have h2 : IntervalIntegrable
      (fun ε => ∫ η in a..c, autocorrelationBoundaryTerm T η ε) volume a c := by
    have hfun : (fun ε => ∫ η in a..c, autocorrelationBoundaryTerm T η ε) =
        fun ε => (pmPowerDampedCenteredDivisorPrefix c T -
          pmPowerDampedCenteredDivisorPrefix a T) *
          dampedChebyshevError ε T / ((T : ℝ) + 1) :=
      funext fun ε => integral_autocorrelationBoundaryTerm_left ha hac T ε
    rw [hfun]
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hac]
    exact ((continuousOn_const.mul (continuousOn_dampedChebyshevError T)).div_const _).mono
      fun x hx => mem_Ioi.mpr (lt_of_lt_of_le ha hx.1)
  rw [show (fun ε => ∫ η in a..c, polarCalibratedPrimePairForm T η ε) =
      fun ε => (∫ η in a..c, tangentCorrelation T η ε) +
        (∫ η in a..c, autocorrelationBoundaryTerm T η ε) from funext hinner,
    intervalIntegral.integral_add h1 h2,
    double_integral_tangentCorrelation_eq_pronicNorm_sub_sq ha hac T,
    double_integral_boundary_eq_sub_sq ha hac T]

/-- **Exact double-integral identity for the single-scale level-sum form.** -/
theorem double_integral_levelSum_eq {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    (∫ ε in a..c, ∫ η in a..c, levelSumAutocorrelationForm T η ε) =
      pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix c n -
        pmPowerDampedCenteredDivisorPrefix a n) ^ 2 +
      (pmPowerDampedCenteredDivisorPrefix c T - pmPowerDampedCenteredDivisorPrefix a T) ^ 2 /
        ((T : ℝ) + 1) := by
  have hfun : (fun ε => ∫ η in a..c, levelSumAutocorrelationForm T η ε) =
      fun ε => ∫ η in a..c, polarCalibratedPrimePairForm T η ε :=
    funext fun ε => by
      congr 1; ext η; exact (polarCalibratedPrimePairForm_eq_levelSum T η ε).symm
  rw [hfun, double_integral_polarCalibratedPrimePairForm_eq ha hac T]

/-- **Unconditional integrated nonnegativity of the polar-calibrated prime-pair form up to the
boundary term.**
On every damping square `[a, c] × [a, c]` (`0 < a ≤ c`) and at every horizon `T : ℕ`, the double
integral of `polarCalibratedPrimePairForm` dominates the double integral of the boundary term,
which is itself nonnegative. -/
theorem double_integral_polarCalibratedPrimePairForm_ge_boundary {a c : ℝ} (ha : 0 < a)
    (hac : a ≤ c) (T : ℕ) :
    0 ≤ (∫ ε in a..c, ∫ η in a..c, autocorrelationBoundaryTerm T η ε) ∧
    (∫ ε in a..c, ∫ η in a..c, autocorrelationBoundaryTerm T η ε) ≤
      (∫ ε in a..c, ∫ η in a..c, polarCalibratedPrimePairForm T η ε) := by
  refine ⟨double_integral_boundary_nonneg ha hac T, ?_⟩
  rw [double_integral_boundary_eq_sub_sq ha hac T,
    double_integral_polarCalibratedPrimePairForm_eq ha hac T]
  have h : 0 ≤ pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix c n -
      pmPowerDampedCenteredDivisorPrefix a n) ^ 2 := sq_nonneg _
  linarith

/-- **Unconditional integrated nonnegativity of the single-scale level-sum form up to the boundary
term.** -/
theorem double_integral_levelSum_ge_boundary {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    0 ≤ (∫ ε in a..c, ∫ η in a..c, autocorrelationBoundaryTerm T η ε) ∧
    (∫ ε in a..c, ∫ η in a..c, autocorrelationBoundaryTerm T η ε) ≤
      (∫ ε in a..c, ∫ η in a..c, levelSumAutocorrelationForm T η ε) := by
  refine ⟨double_integral_boundary_nonneg ha hac T, ?_⟩
  rw [double_integral_boundary_eq_sub_sq ha hac T, double_integral_levelSum_eq ha hac T]
  have h : 0 ≤ pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix c n -
      pmPowerDampedCenteredDivisorPrefix a n) ^ 2 := sq_nonneg _
  linarith

/-! ## §4. Relative-Precision `1/T` Cancellation Law and Admission Equivalence -/

/-- The boundary-subtracted double integral of the polar-calibrated prime-pair form equals the
double integral of the tangent autocorrelation. -/
theorem double_integral_polarCalibrated_sub_boundary_eq {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (T : ℕ) :
    (∫ ε in a..c, ∫ η in a..c, polarCalibratedPrimePairForm T η ε) -
        (∫ ε in a..c, ∫ η in a..c, autocorrelationBoundaryTerm T η ε) =
      ∫ ε in a..c, ∫ η in a..c, tangentCorrelation T η ε := by
  rw [double_integral_polarCalibratedPrimePairForm_eq ha hac T,
    double_integral_boundary_eq_sub_sq ha hac T,
    double_integral_tangentCorrelation_eq_pronicNorm_sub_sq ha hac T]
  ring

/-- **Admission is equivalent to relative-precision `1/(T + 1)` cancellation of the integrated
polar-calibrated prime-pair form against its boundary term.**
Since `P_T`, `m R_T`, and `m²(2T − H_T)` each grow linearly in `T`, dividing by `T + 1` measures
their cancellation on the relative `1/T` scale. -/
theorem admits_iff_relative_precision_inv_T_primePair {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c) :
    Admits dampedMobiusEnergy a ↔
      ∃ C : ℝ, ∀ T : ℕ,
        ((∫ ε in a..c, ∫ η in a..c, polarCalibratedPrimePairForm T η ε) -
          (∫ ε in a..c, ∫ η in a..c, autocorrelationBoundaryTerm T η ε)) / ((T : ℝ) + 1) ≤
            C / ((T : ℝ) + 1) := by
  rw [admits_iff_bounded_double_integral_tangentCorrelation ha hac hc]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun T => ?_⟩
    rw [double_integral_polarCalibrated_sub_boundary_eq ha hac T]
    exact div_le_div_of_nonneg_right (hC T) (by positivity)
  · rintro ⟨C, hC⟩
    refine ⟨C, fun T => ?_⟩
    have hT := hC T
    rw [double_integral_polarCalibrated_sub_boundary_eq ha hac T,
      div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (T : ℝ) + 1)] at hT
    exact hT

/-- **Unconditional Relative-Precision `1/T` Cancellation of the Prime-Pair Form Above `Θ − ½`.**
For every compact interval `[a, c] ⊂ (Θ − ½, ∞)`, there exists `C ≥ 0` such that at every horizon
`T : ℕ`, the linearly growing prime-pair, row-weighted, and polar pieces cancel up to the boundary
term to relative precision `C / (T + 1)`:
`0 ≤ (∫_a^c ∫_a^c polarCalibratedPrimePairForm − ∫_a^c ∫_a^c boundary) / (T + 1) ≤ C / (T + 1)`. -/
theorem exists_relative_precision_inv_T_primePair_above_zeroWidth {a c : ℝ}
    (ha : zetaZeroAbscissa - 1 / 2 < a) (hac : a ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      0 ≤ ((∫ ε in a..c, ∫ η in a..c, polarCalibratedPrimePairForm T η ε) -
            (∫ ε in a..c, ∫ η in a..c, autocorrelationBoundaryTerm T η ε)) / ((T : ℝ) + 1) ∧
      ((∫ ε in a..c, ∫ η in a..c, polarCalibratedPrimePairForm T η ε) -
        (∫ ε in a..c, ∫ η in a..c, autocorrelationBoundaryTerm T η ε)) / ((T : ℝ) + 1) ≤
          C / ((T : ℝ) + 1) := by
  have ha0 : 0 < a := by linarith [half_le_zetaZeroAbscissa]
  obtain ⟨C, hC⟩ := exists_double_integral_tangentCorrelation_le_of_zetaZeroAbscissa_sub_half_lt ha hac
  refine ⟨max C 0, le_max_right C 0, fun T => ?_⟩
  rw [double_integral_polarCalibrated_sub_boundary_eq ha0 hac T]
  refine ⟨div_nonneg (double_integral_tangentCorrelation_nonneg ha0 hac T) (by positivity), ?_⟩
  exact div_le_div_of_nonneg_right ((hC T).trans (le_max_left C 0)) (by positivity)

/-- **The relative-precision normalized prime-pair residual tends to `0` as `T → ∞` above `Θ − ½`.** -/
theorem tendsto_relative_precision_primePair_zero_above_zeroWidth {a c : ℝ}
    (ha : zetaZeroAbscissa - 1 / 2 < a) (hac : a ≤ c) :
    Tendsto (fun T : ℕ =>
      ((∫ ε in a..c, ∫ η in a..c, polarCalibratedPrimePairForm T η ε) -
        (∫ ε in a..c, ∫ η in a..c, autocorrelationBoundaryTerm T η ε)) / ((T : ℝ) + 1))
      atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_relative_precision_inv_T_primePair_above_zeroWidth ha hac
  have hlim : Tendsto (fun T : ℕ => C / ((T : ℝ) + 1)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  exact squeeze_zero (fun T => (hC T).1) (fun T => (hC T).2) hlim

/-- **Unconditional Relative-Precision `1/T` Prime-Pair Cancellation on the Vinogradov–Korobov Band.**
For every floor `ε₀ > 0`, there exists `E ≥ 0` such that for all `T : ℕ` and all
`[a, c] ⊆ [ε₀, 1/2]` in the Vinogradov–Korobov band `a ≥ 1/2 − κ σ(T)/(480 log T)`,
`0 ≤ (∫_a^c ∫_a^c polarCalibratedPrimePairForm − ∫_a^c ∫_a^c boundary) / (T + 1) ≤ 4 E / (T + 1)`. -/
theorem exists_relative_precision_inv_T_primePair_on_vinogradovKorobovBand
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ (T : ℕ) (a c : ℝ), ε₀ ≤ a → a ≤ c → c ≤ 1 / 2 →
        1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ a →
          0 ≤ ((∫ ε in a..c, ∫ η in a..c, polarCalibratedPrimePairForm T η ε) -
                (∫ ε in a..c, ∫ η in a..c, autocorrelationBoundaryTerm T η ε)) / ((T : ℝ) + 1) ∧
          ((∫ ε in a..c, ∫ η in a..c, polarCalibratedPrimePairForm T η ε) -
            (∫ ε in a..c, ∫ η in a..c, autocorrelationBoundaryTerm T η ε)) / ((T : ℝ) + 1) ≤
              (4 * E) / ((T : ℝ) + 1) := by
  obtain ⟨E, hE0, hE⟩ := exists_double_integral_tangentCorrelation_le_on_vinogradovKorobovBand hε₀
  refine ⟨E, hE0, fun T a c ha_ge hac hc2 hband => ?_⟩
  have ha0 : 0 < a := hε₀.trans_le ha_ge
  rw [double_integral_polarCalibrated_sub_boundary_eq ha0 hac T]
  have hb := hE T a c ha_ge hac hc2 hband
  exact ⟨div_nonneg hb.1 (by positivity),
    div_le_div_of_nonneg_right hb.2 (by positivity)⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
