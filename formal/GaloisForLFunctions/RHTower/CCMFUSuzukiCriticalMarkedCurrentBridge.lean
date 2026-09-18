import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalRemainderVariation
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeMarkedRectangularCurrent

/-!
# Exact critical CCM-FU / marked-current bridge

The critical CCM-FU reporter and the coefficient-faithful marked rectangular current have the
same literal prime coefficients.  This module isolates their only mismatch: deterministic
discretization of the polar channel.  No arithmetic term is bounded, made positive, or replaced.

Thus a bound for the polar defect transports the *same signed source* between the two reporters;
the remaining global signed marked-current seam remains the RH-bearing datum.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

private theorem sum_range_eq_sum_Icc_shift_three
    {K : ℕ} (hK : 3 ≤ K) (F : ℕ → ℝ) :
    (∑ j ∈ Finset.range (K - 2), F j) =
      ∑ k ∈ Finset.Icc 3 K, F (k - 3) := by
  refine Finset.sum_bij (fun j _ => j + 3) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
    omega
  · intro a _ha b _hb hab
    omega
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    refine ⟨b - 3, ?_, by omega⟩
    simp only [Finset.mem_range]
    omega
  · intro j hj
    congr 1

private theorem criticalMellinAtomWeight_eq_div_sqrt_local
    (k : ℕ) :
    criticalMellinAtomWeight k =
      ArithmeticFunction.vonMangoldt k / Real.sqrt k := by
  unfold criticalMellinAtomWeight
  have hk0 : (0 : ℝ) ≤ k := by positivity
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hk0,
    ← Real.sqrt_eq_rpow]
  ring

private theorem criticalMultiplier_prime_term_eq_marked
    (H : ℝ) (k : ℕ) :
    (ArithmeticFunction.vonMangoldt k / (k : ℝ)) * Real.sqrt k *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log k) =
      criticalMellinAtomWeight k *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log k) := by
  rw [criticalMellinAtomWeight_eq_div_sqrt_local]
  by_cases hk : k = 0
  · subst k
    norm_num
  · have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hsqrt : (Real.sqrt (k : ℝ)) ^ 2 = (k : ℝ) :=
      Real.sq_sqrt hkpos.le
    field_simp [hkpos.ne', (Real.sqrt_pos.2 hkpos).ne']
    rw [hsqrt]

private theorem one_lt_log_nat_of_three_le {k : ℕ} (hk : 3 ≤ k) :
    1 < Real.log (k : ℝ) := by
  calc
    1 < Real.log (3 : ℝ) :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
    _ ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hk)

private theorem ccmFU_critical_prime_sum_eq_marked_prime_sum
    {H : ℝ} (hH : 2 ≤ H) :
    (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
      (ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)) *
        suzukiCheckpointCriticalTriangularMultiplier H j) =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        if 1 < Real.log (k : ℝ) then
          criticalMellinAtomWeight k *
            ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log k)
        else 0 := by
  have hlog3 : Real.log (3 : ℝ) ≤ H := by
    calc
      Real.log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 2 := by norm_num
      _ ≤ H := hH
  have hexp3 : (3 : ℝ) ≤ Real.exp H := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.mpr hlog3
  have hN : 3 ≤ ⌊Real.exp H⌋₊ := by
    exact (Nat.le_floor_iff (Real.exp_pos H).le).mpr hexp3
  unfold suzukiCheckpointEventIndex
  have hset : Finset.Icc 2 ⌊Real.exp H⌋₊ = insert 2 (Finset.Icc 3 ⌊Real.exp H⌋₊) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [sum_range_eq_sum_Icc_shift_three hN]
  rw [hset]
  rw [Finset.sum_insert (by simp [Finset.mem_Icc])]
  have hlog2 : ¬ 1 < Real.log (2 : ℝ) := by
    have htwo : Real.log (2 : ℝ) ≤ 2 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    norm_num at htwo ⊢
    linarith
  have hlog2' : ¬ 1 < Real.log ((2 : ℕ) : ℝ) := by simpa using hlog2
  rw [if_neg hlog2']
  rw [zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [if_pos (one_lt_log_nat_of_three_le hk3)]
  unfold suzukiCheckpointCriticalTriangularMultiplier
  rw [show k - 3 + 3 = k by omega]
  simpa [mul_assoc] using criticalMultiplier_prime_term_eq_marked H k

/-- Deterministic discrepancy between CCM-FU's logarithmic polar cells and the continuous polar
channel of the coefficient-faithful marked current.  It contains no arithmetic source. -/
def ccmFUSuzukiCriticalMarkedPolarDefect (H : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
    (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ)) *
      suzukiCheckpointCriticalTriangularMultiplier H j) -
    (∫ h in 1..H,
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
        (2 * Real.cosh (h / 2))) -
    suzukiCheckpointCriticalMertensDeviation 0 *
      suzukiCheckpointCriticalTriangularMultiplier H 0

/-- At physical horizons, CCM-FU's literal critical action and the marked rectangular current
have identical prime coefficients.  Their sole difference is the deterministic polar
discretization defect. -/
theorem ccmThirdGradeMarkedCurrent_eq_ccmFU_criticalAction_add_polarDefect
    {H : ℝ} (hH : 2 ≤ H) :
    ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent 1 H =
      suzukiCheckpointCriticalVariationAction suzukiCheckpointCriticalMertensDeviation H +
        ccmFUSuzukiCriticalMarkedPolarDefect H := by
  rw [ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent_eq_window
    (by norm_num) (by linarith)]
  unfold ccmGuinandWeilPrimePolarWeightedWindow
  rw [suzukiCheckpointCriticalMertensDeviationVariationAction_eq_weightedPrimePolar]
  have hsplit :
      (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
        (ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ) -
          (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ))) *
          suzukiCheckpointCriticalTriangularMultiplier H j) =
        (∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
          (ArithmeticFunction.vonMangoldt (j + 3) / ((j + 3 : ℕ) : ℝ)) *
            suzukiCheckpointCriticalTriangularMultiplier H j) -
          ∑ j ∈ Finset.range (suzukiCheckpointEventIndex H - 2),
            (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ)) *
              suzukiCheckpointCriticalTriangularMultiplier H j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hsplit]
  rw [ccmFU_critical_prime_sum_eq_marked_prime_sum hH]
  unfold ccmFUSuzukiCriticalMarkedPolarDefect
  ring

end GaloisForLFunctions.RHTower
