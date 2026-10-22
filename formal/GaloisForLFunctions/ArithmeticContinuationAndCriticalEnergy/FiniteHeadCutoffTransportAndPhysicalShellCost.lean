import GaloisForLFunctions.RHTower.PMRamanujanComplementarySourceBounds

/-!
# Finite-head cutoff transport and physical shell cost

The actual Ramanujan truncation error pays every denominator-cutoff change on a
compatible sequence of growing heads. The exact energy balance retains its signed
cross term and the new physical shell. No bound on the sum of those shells is asserted.

`Q` denotes the last denominator, hence the existing cumulative prefix is indexed
by `Q - 1`. The comparison source retains its full infinite-density centering.
-/

open Finset RHTower

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- The finite constant in the owned cofactor truncation estimate. -/
def ramanujanCutoffErrorConstant (ε β : ℝ) : ℝ :=
  (∑' m : ℕ, (m : ℝ) ^ (-(1 + ε - β))) ^ 2

theorem ramanujanCutoffErrorConstant_nonneg (ε β : ℝ) :
    0 ≤ ramanujanCutoffErrorConstant ε β := sq_nonneg _

/-- Error against the fully centered arithmetic source, measured on one finite head. -/
def ramanujanCutoffHeadErrorEnergy (ε : ℝ) (Q T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T,
    ‖pmPowerDampedRamanujanCumulativePrefix ε (Q - 1) n -
      pmPowerDampedDivisorRemainder ε n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- The actual change of denominator cutoff on the same physical head. -/
def ramanujanCutoffTransportEnergy (ε : ℝ) (Q R T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T,
    ‖pmPowerDampedRamanujanCumulativePrefix ε (R - 1) n -
      pmPowerDampedRamanujanCumulativePrefix ε (Q - 1) n‖ ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1))

/-- The new physical observations, at the new denominator cutoff. -/
def ramanujanPhysicalShellEnergy (ε : ℝ) (R T U : ℕ) : ℝ :=
  ∑ n ∈ Ioc T U,
    ‖pmPowerDampedRamanujanCumulativePrefix ε (R - 1) n‖ ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))

theorem ramanujanPhysicalShellEnergy_nonneg (ε : ℝ) (R T U : ℕ) :
    0 ≤ ramanujanPhysicalShellEnergy ε R T U :=
  sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (by positivity)

private theorem pronic_energy_le_of_norm_le_mul (f : ℕ → ℂ) (T : ℕ)
    {c : ℝ} (hc : 0 ≤ c) (hf : ∀ n ∈ Icc 1 T, ‖f n‖ ≤ (n : ℝ) * c) :
    (∑ n ∈ Icc 1 T, ‖f n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      (T : ℝ) * c ^ 2 := by
  calc
    _ ≤ ∑ _n ∈ Icc 1 T, c ^ 2 := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) * ((n : ℝ) + 1))).2
      calc
        ‖f n‖ ^ 2 ≤ ((n : ℝ) * c) ^ 2 :=
          sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr (hf n hn)
        _ ≤ c ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) := by
          nlinarith [mul_nonneg (le_of_lt hn0) (sq_nonneg c)]
    _ = _ := by simp

/-- The existing pointwise source error gives a quantitative growing-head energy bound. -/
theorem ramanujanCutoffHeadErrorEnergy_le {ε β : ℝ} (hε : 0 < ε)
    (hβ : 0 ≤ β) (hβε : β < ε) {Q T : ℕ} (hQ : 0 < Q) (hTQ : T ≤ Q) :
    ramanujanCutoffHeadErrorEnergy ε Q T ≤
      (T : ℝ) * ((Q : ℝ) ^ (-β) * ramanujanCutoffErrorConstant ε β) ^ 2 := by
  apply pronic_energy_le_of_norm_le_mul _ T (mul_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg Q) _) (ramanujanCutoffErrorConstant_nonneg ε β))
  intro n hn
  simpa only [ramanujanCutoffErrorConstant, mul_assoc] using
    norm_pmPowerDampedRamanujanCumulativePrefix_sub_remainder_le hε hβ hβε hQ
      ((mem_Icc.mp hn).2.trans hTQ)

/-- Two complete cutoffs are close on any head below both cutoffs. -/
theorem ramanujanCutoffTransportEnergy_le {ε β : ℝ} (hε : 0 < ε)
    (hβ : 0 ≤ β) (hβε : β < ε) {Q R T : ℕ}
    (hQ : 0 < Q) (hR : 0 < R) (hTQ : T ≤ Q) (hTR : T ≤ R) :
    ramanujanCutoffTransportEnergy ε Q R T ≤
      (T : ℝ) * (((Q : ℝ) ^ (-β) + (R : ℝ) ^ (-β)) *
        ramanujanCutoffErrorConstant ε β) ^ 2 := by
  apply pronic_energy_le_of_norm_le_mul _ T (by
    exact mul_nonneg (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Q) _)
      (Real.rpow_nonneg (Nat.cast_nonneg R) _)) (ramanujanCutoffErrorConstant_nonneg ε β))
  intro n hn
  have hq := norm_pmPowerDampedRamanujanCumulativePrefix_sub_remainder_le
    hε hβ hβε hQ ((mem_Icc.mp hn).2.trans hTQ)
  have hr := norm_pmPowerDampedRamanujanCumulativePrefix_sub_remainder_le
    hε hβ hβε hR ((mem_Icc.mp hn).2.trans hTR)
  calc
    _ ≤ ‖pmPowerDampedRamanujanCumulativePrefix ε (R - 1) n -
        pmPowerDampedDivisorRemainder ε n‖ +
        ‖pmPowerDampedRamanujanCumulativePrefix ε (Q - 1) n -
          pmPowerDampedDivisorRemainder ε n‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by dsimp [ramanujanCutoffErrorConstant]; nlinarith

/-- Cutoff transport is controlled in the finite-head norm itself. -/
theorem sqrt_ramanujanCutoffTransportEnergy_le {ε β : ℝ} (hε : 0 < ε)
    (hβ : 0 ≤ β) (hβε : β < ε) {Q R T : ℕ}
    (hQ : 0 < Q) (hR : 0 < R) (hTQ : T ≤ Q) (hTR : T ≤ R) :
    Real.sqrt (ramanujanCutoffTransportEnergy ε Q R T) ≤
      Real.sqrt T * (((Q : ℝ) ^ (-β) + (R : ℝ) ^ (-β)) *
        ramanujanCutoffErrorConstant ε β) := by
  have h := Real.sqrt_le_sqrt (ramanujanCutoffTransportEnergy_le hε hβ hβε hQ hR hTQ hTR)
  rw [Real.sqrt_mul (Nat.cast_nonneg T), Real.sqrt_sq (by
    exact mul_nonneg (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Q) _)
      (Real.rpow_nonneg (Nat.cast_nonneg R) _)) (ramanujanCutoffErrorConstant_nonneg ε β))] at h
  exact h

/-- The stage identity keeps the signed old-head work and the new physical shell separate. -/
theorem ramanujanCutoff_stage_energy_eq (ε : ℝ) (Q R : ℕ) {T U : ℕ} (hTU : T ≤ U) :
    pmPowerDampedRamanujanPrefixEnergy ε (R - 1) U =
      pmPowerDampedRamanujanPrefixEnergy ε (Q - 1) T +
        2 * (∑ n ∈ Icc 1 T,
          (pmPowerDampedRamanujanCumulativePrefix ε (Q - 1) n *
            (starRingEnd ℂ) (pmPowerDampedRamanujanCumulativePrefix ε (R - 1) n -
              pmPowerDampedRamanujanCumulativePrefix ε (Q - 1) n)).re /
                ((n : ℝ) * ((n : ℝ) + 1))) +
        ramanujanCutoffTransportEnergy ε Q R T + ramanujanPhysicalShellEnergy ε R T U := by
  have hsplit := sum_Ioc_consecutive (fun n : ℕ =>
    ‖pmPowerDampedRamanujanCumulativePrefix ε (R - 1) n‖ ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))) (Nat.zero_le T) hTU
  have hi (V : ℕ) : Ioc 0 V = Icc 1 V := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  rw [hi T, hi U] at hsplit
  rw [pmPowerDampedRamanujanPrefixEnergy, ← hsplit]
  congr 1
  simp only [pmPowerDampedRamanujanPrefixEnergy, ramanujanCutoffTransportEnergy,
    mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  have h (u v : ℂ) : ‖v‖ ^ 2 = ‖u‖ ^ 2 + ‖v - u‖ ^ 2 +
      2 * (u * (starRingEnd ℂ) (v - u)).re := by
    have hv : u + (v - u) = v := by ring
    simpa only [hv, Complex.normSq_eq_norm_sq] using Complex.normSq_add u (v - u)
  rw [h (pmPowerDampedRamanujanCumulativePrefix ε (Q - 1) n)]
  ring

private theorem dyadic_head_scale (m j : ℕ) (ε : ℝ) :
    Real.sqrt ((2 : ℕ) ^ j) * (((2 : ℕ) ^ (m * j) : ℕ) : ℝ) ^ (-(ε / 2)) =
      ((2 : ℝ) ^ ((1 - (m : ℝ) * ε) / 2)) ^ j := by
  rw [Real.sqrt_eq_rpow]
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

/-- A single geometric majorant works for every successive cutoff change. -/
theorem sqrt_ramanujanCutoffTransportEnergy_dyadic_le {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : 1 ≤ m) (j : ℕ) :
    Real.sqrt (ramanujanCutoffTransportEnergy ε (2 ^ (m * j))
      (2 ^ (m * (j + 1))) (2 ^ j)) ≤
        (2 * ramanujanCutoffErrorConstant ε (ε / 2)) *
          ((2 : ℝ) ^ ((1 - (m : ℝ) * ε) / 2)) ^ j := by
  have hTQ : 2 ^ j ≤ (2 : ℕ) ^ (m * j) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have hQR : (2 : ℕ) ^ (m * j) ≤ 2 ^ (m * (j + 1)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h := sqrt_ramanujanCutoffTransportEnergy_le hε (by positivity : 0 ≤ ε / 2)
    (by linarith : ε / 2 < ε) (by positivity : 0 < (2 : ℕ) ^ (m * j))
    (by positivity : 0 < (2 : ℕ) ^ (m * (j + 1))) hTQ (hTQ.trans hQR)
  have hp : (((2 : ℕ) ^ (m * (j + 1)) : ℕ) : ℝ) ^ (-(ε / 2)) ≤
      (((2 : ℕ) ^ (m * j) : ℕ) : ℝ) ^ (-(ε / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hQR) (by linarith)
  calc
    _ ≤ Real.sqrt ((2 : ℕ) ^ j) *
        (2 * ((((2 : ℕ) ^ (m * j) : ℕ) : ℝ) ^ (-(ε / 2))) *
          ramanujanCutoffErrorConstant ε (ε / 2)) := h.trans (by
      gcongr
      linarith)
    _ = _ := by rw [← dyadic_head_scale]; ring

/-- The actual common-head transition norms are summable at a sufficient cutoff depth. -/
theorem summable_sqrt_ramanujanCutoffTransportEnergy_dyadic {ε : ℝ} (hε : 0 < ε)
    {m : ℕ} (hm : 1 ≤ m) (hmε : 1 < (m : ℝ) * ε) :
    Summable (fun j : ℕ => Real.sqrt (ramanujanCutoffTransportEnergy ε
      (2 ^ (m * j)) (2 ^ (m * (j + 1))) (2 ^ j))) := by
  have hgeo : Summable (fun j : ℕ => ((2 : ℝ) ^ ((1 - (m : ℝ) * ε) / 2)) ^ j) :=
    summable_geometric_iff_norm_lt_one.mpr (by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  exact Summable.of_nonneg_of_le (fun _ => Real.sqrt_nonneg _) (fun j =>
    sqrt_ramanujanCutoffTransportEnergy_dyadic_le hε hm j)
      (hgeo.mul_left (2 * ramanujanCutoffErrorConstant ε (ε / 2)))

/-- Every positive damping has a deterministic depth paying all denominator transitions. -/
theorem exists_summable_ramanujanCutoffTransport_depth {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ 1 < (m : ℝ) * ε ∧
      Summable (fun j : ℕ => Real.sqrt (ramanujanCutoffTransportEnergy ε
        (2 ^ (m * j)) (2 ^ (m * (j + 1))) (2 ^ j))) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (1 / ε))
  have hm1 : 1 ≤ m := by exact_mod_cast (le_max_left 1 (1 / ε)).trans hm.le
  have hmε : 1 < (m : ℝ) * ε := (div_lt_iff₀ hε).mp
    ((le_max_right 1 (1 / ε)).trans_lt hm)
  exact ⟨m, hm1, hmε, summable_sqrt_ramanujanCutoffTransportEnergy_dyadic hε hm1 hmε⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
