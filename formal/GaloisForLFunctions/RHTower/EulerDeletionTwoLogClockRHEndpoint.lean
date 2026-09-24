import GaloisForLFunctions.RHTower.EulerDeletionTwoLogClockLocalization
import GaloisForLFunctions.RHTower.EulerDeletionSignedResidueCovariance

/-!
# The two-logarithm signed quotient is an RH-strength carrier

The only hypothesis in the final receiver is a cofinal polylogarithmic
ceiling for the exact signed paired-Möbius conditional quotient. All other
terms, including the complete martingale and physical high-clock leakage,
are discharged unconditionally here. The missing quotient bound is not
asserted.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology

namespace RHTower.DeletionResidueMartingale

/-- Even without convergence of the full drift, its RH-bearing energy is
controlled by one two-logarithm signed source projection. -/
theorem predictableDrift_energy_le_two_twoLogClockProjection_add_log (N : ℕ) :
    ‖predictableDrift N‖ ^ (2 : ℕ) ≤
      2 * ‖(historySpace (twoLogClockThreshold N)).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) +
      6 * (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) + 4 := by
  let s := sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N
  let m := martingalePart N
  let d := predictableDrift N
  have hs : s = m + d := source_eq_martingale_add_drift N
  have hd : d = s - m := by rw [hs]; abel
  have htri : ‖d‖ ≤ ‖s‖ + ‖m‖ := by
    rw [hd]
    exact norm_sub_le _ _
  have hsq := (sq_le_sq₀ (norm_nonneg d) (by positivity : 0 ≤ ‖s‖ + ‖m‖)).mpr htri
  have hmart : ‖m‖ ^ (2 : ℕ) ≤ 2 := martingalePart_sq_le_two N
  have hsource := source_energy_le_twoLogClockProjection_energy_add_log N
  dsimp [s, m, d] at hsq hmart hsource ⊢
  nlinarith [sq_nonneg (‖sourceVec
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖ - ‖martingalePart N‖)]

theorem twoLogClockThreshold_le_log_budget {N : ℕ} (hN : 3 ≤ N) :
    (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) ≤
      (2 / Real.log 2 + 1) * Real.log (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hNpluspos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hlog : 1 ≤ Real.log (N : ℝ) :=
    (Real.le_log_iff_exp_le hNpos).mpr <|
      Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  have hNplusSqNat : N + 1 ≤ N ^ 2 := by nlinarith
  have hNplusSq : (((N + 1 : ℕ) : ℝ)) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast hNplusSqNat
  have hlogplus : Real.log (((N + 1 : ℕ) : ℝ)) ≤
      2 * Real.log (N : ℝ) := by
    calc
      _ ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log hNpluspos hNplusSq
      _ = 2 * Real.log (N : ℝ) := by rw [Real.log_pow]; ring
  have hlogtwopos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hnatlog : (Nat.log2 (N + 1) : ℝ) ≤
      Real.logb 2 (((N + 1 : ℕ) : ℝ)) := Real.log2_le_logb _
  have hrealLog : Real.logb 2 (((N + 1 : ℕ) : ℝ)) ≤
      2 * Real.log (N : ℝ) / Real.log 2 := by
    change Real.log (((N + 1 : ℕ) : ℝ)) / Real.log 2 ≤ _
    exact div_le_div_of_nonneg_right hlogplus hlogtwopos.le
  calc
    (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) = (Nat.log2 (N + 1) : ℝ) + 1 := by
      push_cast; ring
    _ ≤ Real.logb 2 (((N + 1 : ℕ) : ℝ)) + 1 := by linarith
    _ ≤ 2 * Real.log (N : ℝ) / Real.log 2 + Real.log (N : ℝ) := by
      linarith
    _ = (2 / Real.log 2 + 1) * Real.log (N : ℝ) := by ring

/-- A cofinal polylogarithmic ceiling for the one literal signed quotient
field at the critical two-logarithm clock implies RH. This theorem does not
assume a zero-dependent datum and does not supply that arithmetic ceiling. -/
theorem riemannHypothesis_of_cofinally_log_bounded_twoLogClockSourceProjection
    (hprojection : ∃ q : ℕ, ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      ‖(historySpace (twoLogClockThreshold N)).starProjection
        (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)‖ ^ (2 : ℕ) ≤
        B * Real.log (N : ℝ) ^ q) : RiemannHypothesis := by
  apply DeletionSignedResidueCovariance.riemannHypothesis_of_cofinally_log_bounded_energy
  obtain ⟨q, B, hB⟩ := hprojection
  let C : ℝ := 2 / Real.log 2 + 1
  refine ⟨q + 1, 2 * |B| + 6 * C + 4, fun K => ?_⟩
  obtain ⟨N, hKN, hNproj⟩ := hB (max K 3)
  refine ⟨N, (le_max_left K 3).trans hKN, ?_⟩
  have hN3 : 3 ≤ N := (le_max_right K 3).trans hKN
  let x : ℝ := Real.log (N : ℝ)
  have hx : 1 ≤ x := by
    dsimp [x]
    exact (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < N)).mpr <|
      Real.exp_one_lt_three.le.trans (by exact_mod_cast hN3)
  have hxpow : (0 : ℝ) ≤ x ^ q := pow_nonneg (by linarith) _
  have hxpowone : 1 ≤ x ^ q := one_le_pow₀ hx
  have hqle : x ^ q ≤ x ^ (q + 1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right hxpow hx
  have hxle : x ≤ x ^ (q + 1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_left (by linarith : 0 ≤ x) hxpowone
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    have h : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hH := twoLogClockThreshold_le_log_budget hN3
  change (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) ≤ C * x at hH
  have hBcomp : B * x ^ q ≤ |B| * x ^ (q + 1) := by
    calc
      _ ≤ |B| * x ^ q := mul_le_mul_of_nonneg_right (le_abs_self B) hxpow
      _ ≤ |B| * x ^ (q + 1) := mul_le_mul_of_nonneg_left hqle (abs_nonneg B)
  have hHcomp : (((Nat.log2 (N + 1) + 1 : ℕ) : ℝ)) ≤
      C * x ^ (q + 1) :=
    hH.trans (mul_le_mul_of_nonneg_left hxle hCnonneg)
  have hfour : (4 : ℝ) ≤ 4 * x ^ (q + 1) := by nlinarith [hqle, hxpowone, hx]
  have henergy := predictableDrift_energy_le_two_twoLogClockProjection_add_log N
  rw [DeletionSignedResidueCovariance.energy_eq_predictableDrift_norm_sq]
  dsimp [x] at hBcomp hHcomp hfour
  nlinarith [hNproj, hBcomp, hHcomp, hfour]

end RHTower.DeletionResidueMartingale
