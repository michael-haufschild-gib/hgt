import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalMarkedCurrentBridge
import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalLogPolarCellQuadrature
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeMatchedQuadrature

/-!
# Exact finite decomposition of the critical CCM-FU polar defect

The literal CCM-FU / marked-current discrepancy is deterministic.  This module exposes it as
summable internal logarithmic-cell quadrature, a fixed lower edge, a moving terminal tile, the
already harmless incoming polar branch, and the base coefficient.  Prime terms are absent from
this decomposition because their coefficients were matched exactly before this step.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Outgoing exponential half of the literal third-grade polar profile. -/
def ccmFUSuzukiCriticalOutgoingPolarProfile (H h : ℝ) : ℝ :=
  Real.exp (h / 2) * ccmGuinandWeilThirdGradeCesaroTriangularWeight H h

/-- Fixed lower physical edge left by the logarithmic right-endpoint tiling. -/
def ccmFUSuzukiCriticalOutgoingPolarLowerEdge (H : ℝ) : ℝ :=
  ∫ h in Real.log (2 : ℝ)..(1 : ℝ), ccmFUSuzukiCriticalOutgoingPolarProfile H h

/-- Terminal physical tile between the last integer logarithmic node and the moving wall. -/
def ccmFUSuzukiCriticalOutgoingPolarTerminal (H : ℝ) : ℝ :=
  ∫ h in Real.log ((⌊Real.exp H⌋₊ : ℕ) : ℝ)..H,
    ccmFUSuzukiCriticalOutgoingPolarProfile H h

/-- The lower fixed physical edge is uniformly controlled by its literal logarithmic wall. -/
theorem abs_ccmFUSuzukiCriticalOutgoingPolarLowerEdge_le
    {H : ℝ} (hH : 2 ≤ H) :
    |ccmFUSuzukiCriticalOutgoingPolarLowerEdge H| ≤
      (Real.exp (1 / 2) * (32 / (Real.log 2) ^ 3)) * (1 - Real.log 2) := by
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hH0 : 0 < H := by linarith
  have hpoint : ∀ h ∈ uIoc (Real.log (2 : ℝ)) 1,
      ‖ccmFUSuzukiCriticalOutgoingPolarProfile H h‖ ≤
        Real.exp (1 / 2) * (32 / (Real.log 2) ^ 3) := by
    intro h hh
    rw [uIoc_of_le hlog2] at hh
    have hhpos : 0 < h := hlog2pos.trans_le hh.1.le
    have hfac0 : 0 ≤ 1 - h / H := by
      rw [sub_nonneg, div_le_one hH0]
      exact hh.2.trans (one_le_two.trans hH)
    have hfac1 : 1 - h / H ≤ 1 := by
      have : 0 ≤ h / H := by positivity
      linarith
    have hpow : (Real.log 2) ^ 3 ≤ h ^ 3 :=
      pow_le_pow_left₀ hlog2pos.le hh.1.le 3
    have hbase0 : 0 ≤ 32 / h ^ 3 := by positivity
    have hbase : 32 / h ^ 3 ≤ 32 / (Real.log 2) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos hlog2pos 3) hpow
    have hW0 : 0 ≤ ccmGuinandWeilThirdGradeCesaroTriangularWeight H h := by
      unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
        ccmGuinandWeilThirdGradeWeight
      positivity
    have hW : ccmGuinandWeilThirdGradeCesaroTriangularWeight H h ≤
        32 / (Real.log 2) ^ 3 := by
      unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
        ccmGuinandWeilThirdGradeWeight
      calc
        32 / h ^ 3 * (1 - h / H) ≤
            (32 / (Real.log 2) ^ 3) * (1 - h / H) :=
          mul_le_mul_of_nonneg_right hbase hfac0
        _ ≤ (32 / (Real.log 2) ^ 3) * 1 :=
          mul_le_mul_of_nonneg_left hfac1 (by positivity)
        _ = 32 / (Real.log 2) ^ 3 := by ring
    have hExp : Real.exp (h / 2) ≤ Real.exp (1 / 2) := by
      apply Real.exp_le_exp.mpr
      linarith [hh.2]
    dsimp only [ccmFUSuzukiCriticalOutgoingPolarProfile]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hW0]
    exact mul_le_mul hExp hW hW0 (Real.exp_pos _).le
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlog2)] at hint
  unfold ccmFUSuzukiCriticalOutgoingPolarLowerEdge
  exact hint

private theorem one_lt_log_nat_of_three_le {k : ℕ} (hk : 3 ≤ k) :
    1 < Real.log (k : ℝ) := by
  calc
    1 < Real.log (3 : ℝ) :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
    _ ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hk)

private theorem exp_half_log_nat {k : ℕ} (hk : 0 < k) :
    Real.exp (Real.log (k : ℝ) / 2) = Real.sqrt k := by
  rw [← Real.log_sqrt (by exact_mod_cast hk.le), Real.exp_log]
  exact Real.sqrt_pos.mpr (by exact_mod_cast hk)

/-- The last floor-to-wall outgoing polar tile has a fixed physical bound. -/
theorem abs_ccmFUSuzukiCriticalOutgoingPolarTerminal_le
    {H : ℝ} (hH : 2 ≤ H) :
    |ccmFUSuzukiCriticalOutgoingPolarTerminal H| ≤ 32 := by
  let N : ℕ := ⌊Real.exp H⌋₊
  have hlog3H : Real.log (3 : ℝ) ≤ H := by
    calc
      Real.log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 2 := by norm_num
      _ ≤ H := hH
  have hexp3 : (3 : ℝ) ≤ Real.exp H := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.mpr hlog3H
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    exact Nat.le_floor hexp3
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : Real.log (N : ℝ) ≤ H := by
    apply (Real.log_le_iff_le_exp hNpos).mpr
    dsimp only [N]
    exact Nat.floor_le (Real.exp_pos H).le
  have h1N : 1 ≤ Real.log (N : ℝ) :=
    (one_lt_log_nat_of_three_le hN3).le
  have hHlogN1 : H < Real.log ((N + 1 : ℕ) : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (by exact_mod_cast (by omega : 0 < N + 1))).2
    dsimp only [N]
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (Real.exp H)
  have hNsqrt : Real.sqrt ((N + 1 : ℕ) : ℝ) ≤ N := by
    have hNreal : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    have hpoly : ((N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
      rw [Nat.cast_add, Nat.cast_one]
      nlinarith [sq_nonneg ((N : ℝ) - 1)]
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · simpa only [Nat.cast_add, Nat.cast_one] using hpoly
  have hwidth : H - Real.log (N : ℝ) ≤ 1 / (N : ℝ) := by
    calc
      H - Real.log (N : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) - Real.log (N : ℝ) := by
        linarith
      _ ≤ 1 / (N : ℝ) := by
        simpa only [Nat.add_sub_cancel] using
          (log_nat_step_nonneg_le_inv_pred (k := N + 1) (by omega : 3 ≤ N + 1)).2
  have hpoint : ∀ h ∈ uIoc (Real.log (N : ℝ)) H,
      ‖ccmFUSuzukiCriticalOutgoingPolarProfile H h‖ ≤ 32 * N := by
    intro h hh
    rw [uIoc_of_le hlogN] at hh
    have hW := ccmFU_triangular_weight_nonneg_le_32 hH (h1N.trans hh.1.le) hh.2
    have hExp : Real.exp (h / 2) ≤ N := by
      calc
        Real.exp (h / 2) ≤ Real.exp (H / 2) := by
          apply Real.exp_le_exp.mpr
          linarith [hh.2]
        _ ≤ Real.exp (Real.log ((N + 1 : ℕ) : ℝ) / 2) := by
          apply Real.exp_le_exp.mpr
          linarith
        _ = Real.sqrt ((N + 1 : ℕ) : ℝ) :=
          exp_half_log_nat (by omega : 0 < N + 1)
        _ ≤ N := hNsqrt
    dsimp only [ccmFUSuzukiCriticalOutgoingPolarProfile]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hW.1]
    calc
      Real.exp (h / 2) * ccmGuinandWeilThirdGradeCesaroTriangularWeight H h ≤
          (N : ℝ) * 32 :=
        mul_le_mul hExp hW.2 hW.1 hNpos.le
      _ = 32 * N := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlogN)] at hint
  unfold ccmFUSuzukiCriticalOutgoingPolarTerminal
  change |∫ h in Real.log (N : ℝ)..H,
      ccmFUSuzukiCriticalOutgoingPolarProfile H h| ≤ 32
  calc
    |∫ h in Real.log (N : ℝ)..H,
        ccmFUSuzukiCriticalOutgoingPolarProfile H h| ≤
      (32 * N) * (H - Real.log (N : ℝ)) := by simpa only [mul_comm] using hint
    _ ≤ (32 * N) * (1 / (N : ℝ)) := by gcongr
    _ = 32 := by field_simp [hNpos.ne']

/-- The only initial outgoing cell left outside the summable `k ≥ 4` tail has a fixed literal
bound. -/
theorem abs_ccmFUSuzukiCriticalOutgoingPolarCell_three_le
    {H : ℝ} (hH : 2 ≤ H) :
    |ccmFUSuzukiCriticalOutgoingPolarCellError H 3| ≤
      2 * (Real.log 3 - Real.log 2) * Real.sqrt 3 *
        (32 / (Real.log 2) ^ 3) := by
  let C : ℝ := 32 / (Real.log 2) ^ 3
  let delta : ℝ := Real.log 3 - Real.log 2
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2lt3 : Real.log (2 : ℝ) < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hlog3le2 : Real.log (3 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hdelta0 : 0 ≤ delta := sub_nonneg.mpr hlog2lt3.le
  have hW : ∀ h ∈ uIoc (Real.log (2 : ℝ)) (Real.log 3),
      0 ≤ ccmGuinandWeilThirdGradeCesaroTriangularWeight H h ∧
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h ≤ C := by
    intro h hh
    rw [uIoc_of_le hlog2lt3.le] at hh
    have hhpos : 0 < h := hlog2pos.trans_le hh.1.le
    have hh2 : h ≤ 2 := hh.2.trans hlog3le2
    have hH0 : 0 < H := by linarith
    have hfac0 : 0 ≤ 1 - h / H := by
      rw [sub_nonneg, div_le_one hH0]
      exact hh2.trans hH
    have hfac1 : 1 - h / H ≤ 1 := by
      have : 0 ≤ h / H := by positivity
      linarith
    have hpow : (Real.log 2) ^ 3 ≤ h ^ 3 :=
      pow_le_pow_left₀ hlog2pos.le hh.1.le 3
    have hbase : 32 / h ^ 3 ≤ C := by
      dsimp only [C]
      exact div_le_div_of_nonneg_left (by norm_num) (pow_pos hlog2pos 3) hpow
    unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
      ccmGuinandWeilThirdGradeWeight
    constructor
    · positivity
    · calc
        32 / h ^ 3 * (1 - h / H) ≤ C * (1 - h / H) :=
          mul_le_mul_of_nonneg_right hbase hfac0
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hfac1 (by dsimp only [C]; positivity)
        _ = C := by ring
  have hlog3mem : Real.log (3 : ℝ) ∈ uIoc (Real.log (2 : ℝ)) (Real.log 3) := by
    rw [uIoc_of_le hlog2lt3.le]
    exact ⟨hlog2lt3, le_rfl⟩
  have hnodeW := (hW _ hlog3mem).2
  have hnodeW0 := (hW _ hlog3mem).1
  have hprofile : ∀ h ∈ uIoc (Real.log (2 : ℝ)) (Real.log 3),
      ‖ccmFUSuzukiCriticalOutgoingPolarProfile H h‖ ≤ Real.sqrt 3 * C := by
    intro h hh
    rw [uIoc_of_le hlog2lt3.le] at hh
    have hExp : Real.exp (h / 2) ≤ Real.sqrt 3 := by
      have heq := exp_half_log_nat (k := 3) (by norm_num : 0 < 3)
      norm_num at heq
      rw [← heq]
      apply Real.exp_le_exp.mpr
      linarith [hh.2]
    have hW' := hW h (by simpa only [uIoc_of_le hlog2lt3.le] using hh)
    dsimp only [ccmFUSuzukiCriticalOutgoingPolarProfile]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hW'.1]
    exact mul_le_mul hExp hW'.2 hW'.1 (Real.sqrt_nonneg _)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hprofile
  rw [Real.norm_eq_abs, abs_of_nonneg hdelta0] at hint
  unfold ccmFUSuzukiCriticalOutgoingPolarCellError
  norm_num only [Nat.cast_ofNat, Nat.reduceSub]
  change |delta * Real.sqrt 3 *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log 3) -
        ∫ h in Real.log 2..Real.log 3,
          ccmFUSuzukiCriticalOutgoingPolarProfile H h| ≤ _
  have hnode0 : 0 ≤ delta * Real.sqrt 3 *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log 3) :=
    mul_nonneg (mul_nonneg hdelta0 (Real.sqrt_nonneg _)) hnodeW0
  calc
    |delta * Real.sqrt 3 * ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log 3) -
        ∫ h in Real.log 2..Real.log 3,
          ccmFUSuzukiCriticalOutgoingPolarProfile H h| ≤
      |delta * Real.sqrt 3 * ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log 3)| +
        |∫ h in Real.log 2..Real.log 3,
          ccmFUSuzukiCriticalOutgoingPolarProfile H h| := abs_sub _ _
    _ = delta * Real.sqrt 3 * ccmGuinandWeilThirdGradeCesaroTriangularWeight H (Real.log 3) +
        |∫ h in Real.log 2..Real.log 3,
          ccmFUSuzukiCriticalOutgoingPolarProfile H h| := by rw [abs_of_nonneg hnode0]
    _ ≤ delta * Real.sqrt 3 * C + (Real.sqrt 3 * C) * delta := by
      apply add_le_add
      · gcongr
      · simpa only [delta] using hint
    _ = 2 * delta * Real.sqrt 3 * C := by ring
    _ = 2 * (Real.log 3 - Real.log 2) * Real.sqrt 3 *
        (32 / (Real.log 2) ^ 3) := by rfl

/-- Exact literal decomposition of the critical CCM-FU / marked-current polar defect.  The
large outgoing polar masses cancel cellwise before any bound: only the right-endpoint quadrature
errors remain in the finite sum. -/
theorem ccmFUSuzukiCriticalMarkedPolarDefect_eq_cellSum_add_lower_sub_terminal_sub_incoming_sub_base
    {H : ℝ} (hH : 2 ≤ H) :
    ccmFUSuzukiCriticalMarkedPolarDefect H =
      (∑ j ∈ Finset.range (⌊Real.exp H⌋₊ - 2),
        ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3)) +
        ccmFUSuzukiCriticalOutgoingPolarLowerEdge H -
          ccmFUSuzukiCriticalOutgoingPolarTerminal H -
          ccmThirdGradeCesaroIncomingPolarTail 1 H -
          suzukiCheckpointCriticalMertensDeviation 0 *
            suzukiCheckpointCriticalTriangularMultiplier H 0 := by
  let N : ℕ := ⌊Real.exp H⌋₊
  let f : ℝ → ℝ := ccmFUSuzukiCriticalOutgoingPolarProfile H
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlog3H : Real.log (3 : ℝ) ≤ H := by
    calc
      Real.log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 2 := by norm_num
      _ ≤ H := hH
  have hexp3 : (3 : ℝ) ≤ Real.exp H := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.mpr hlog3H
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    exact Nat.le_floor hexp3
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : Real.log (N : ℝ) ≤ H := by
    apply (Real.log_le_iff_le_exp hNpos).mpr
    dsimp only [N]
    exact Nat.floor_le (Real.exp_pos H).le
  have h1N : 1 ≤ Real.log (N : ℝ) :=
    (one_lt_log_nat_of_three_le hN3).le
  have hsumDiscrete :
      (∑ j ∈ Finset.range (N - 2),
        (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ)) *
          Real.sqrt (j + 3 : ℕ) *
            ccmGuinandWeilThirdGradeCesaroTriangularWeight H
              (Real.log ((j + 3 : ℕ) : ℝ))) =
        (∑ j ∈ Finset.range (N - 2),
          ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3)) +
          (∫ h in Real.log (2 : ℝ)..Real.log (N : ℝ), f h) := by
    calc
      (∑ j ∈ Finset.range (N - 2),
          (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ)) *
            Real.sqrt (j + 3 : ℕ) *
              ccmGuinandWeilThirdGradeCesaroTriangularWeight H
                (Real.log ((j + 3 : ℕ) : ℝ))) =
          ∑ j ∈ Finset.range (N - 2),
            (ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3) +
              ∫ h in Real.log ((j + 2 : ℕ) : ℝ)..Real.log ((j + 3 : ℕ) : ℝ), f h) := by
        apply Finset.sum_congr rfl
        intro j _
        unfold ccmFUSuzukiCriticalOutgoingPolarCellError
        dsimp only [f, ccmFUSuzukiCriticalOutgoingPolarProfile]
        have hleft : j + 3 - 1 = j + 2 := by omega
        rw [hleft]
        ring
      _ = (∑ j ∈ Finset.range (N - 2),
          ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3)) +
          ∫ h in Real.log (2 : ℝ)..Real.log (N : ℝ), f h := by
        dsimp only [f, ccmFUSuzukiCriticalOutgoingPolarProfile]
        rw [Finset.sum_add_distrib,
          sum_range_ccmFU_outgoingPolar_log_cells H (N - 2)]
        have hN : N - 2 + 2 = N := by omega
        simp only [hN]
  have hf1N : IntervalIntegrable f volume 1 (Real.log (N : ℝ)) := by
    have hcont : ContinuousOn f (Icc 1 (Real.log (N : ℝ))) := by
      intro h hh
      dsimp only [f, ccmFUSuzukiCriticalOutgoingPolarProfile]
      exact (((by fun_prop : Continuous fun x : ℝ => Real.exp (x / 2)).continuousAt.mul
        (hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight
          (ne_of_gt (zero_lt_one.trans_le hh.1))).continuousAt).continuousWithinAt)
    have hcont' : ContinuousOn f (uIcc 1 (Real.log (N : ℝ))) := by
      simpa only [uIcc_of_le h1N] using hcont
    exact hcont'.intervalIntegrable
  have hfterm : IntervalIntegrable f volume (Real.log (N : ℝ)) H := by
    have hcont : ContinuousOn f (Icc (Real.log (N : ℝ)) H) := by
      intro h hh
      dsimp only [f, ccmFUSuzukiCriticalOutgoingPolarProfile]
      exact (((by fun_prop : Continuous fun x : ℝ => Real.exp (x / 2)).continuousAt.mul
        (hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight
          (ne_of_gt (zero_lt_one.trans_le (h1N.trans hh.1)))).continuousAt).continuousWithinAt)
    have hcont' : ContinuousOn f (uIcc (Real.log (N : ℝ)) H) := by
      simpa only [uIcc_of_le hlogN] using hcont
    exact hcont'.intervalIntegrable
  have hflow : IntervalIntegrable f volume (Real.log (2 : ℝ)) 1 := by
    have hcont : ContinuousOn f (Icc (Real.log (2 : ℝ)) 1) := by
      intro h hh
      dsimp only [f, ccmFUSuzukiCriticalOutgoingPolarProfile]
      have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      exact (((by fun_prop : Continuous fun x : ℝ => Real.exp (x / 2)).continuousAt.mul
        (hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight
          (ne_of_gt (hlog2pos.trans_le hh.1))).continuousAt).continuousWithinAt)
    have hcont' : ContinuousOn f (uIcc (Real.log (2 : ℝ)) 1) := by
      simpa only [uIcc_of_le hlog2] using hcont
    exact hcont'.intervalIntegrable
  have hparts1 := intervalIntegral.integral_add_adjacent_intervals hflow hf1N
  have hparts2 := intervalIntegral.integral_add_adjacent_intervals hf1N hfterm
  have hOut :
      (∫ h in Real.log (2 : ℝ)..Real.log (N : ℝ), f h) -
        (∫ h in 1..H, f h) =
          ccmFUSuzukiCriticalOutgoingPolarLowerEdge H -
            ccmFUSuzukiCriticalOutgoingPolarTerminal H := by
    dsimp only [ccmFUSuzukiCriticalOutgoingPolarLowerEdge,
      ccmFUSuzukiCriticalOutgoingPolarTerminal]
    dsimp only [f] at hparts1 hparts2 ⊢
    linarith
  have hWcont : ContinuousOn
      (ccmGuinandWeilThirdGradeCesaroTriangularWeight H) (Icc 1 H) := by
    intro h hh
    exact (hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight
      (ne_of_gt (zero_lt_one.trans_le hh.1))).continuousAt.continuousWithinAt
  have hplus : IntervalIntegrable f volume 1 H := by
    have hcont : ContinuousOn f (Icc 1 H) := by
      intro h hh
      dsimp only [f, ccmFUSuzukiCriticalOutgoingPolarProfile]
      exact (((by fun_prop : Continuous fun x : ℝ => Real.exp (x / 2)).continuousAt.mul
        (hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight
          (ne_of_gt (zero_lt_one.trans_le hh.1))).continuousAt).continuousWithinAt)
    have hcont' : ContinuousOn f (uIcc 1 H) := by
      simpa only [uIcc_of_le (one_le_two.trans hH)] using hcont
    exact hcont'.intervalIntegrable
  have hminus : IntervalIntegrable (fun h : ℝ => Real.exp (-(h / 2)) *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H h) volume 1 H := by
    have hcont : ContinuousOn (fun h : ℝ => Real.exp (-(h / 2)) *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h) (Icc 1 H) :=
      (by fun_prop : Continuous fun h : ℝ => Real.exp (-(h / 2))).continuousOn.mul hWcont
    have hcont' : ContinuousOn (fun h : ℝ => Real.exp (-(h / 2)) *
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h) (uIcc 1 H) := by
      simpa only [uIcc_of_le (one_le_two.trans hH)] using hcont
    exact hcont'.intervalIntegrable
  have hpolar :
      (∫ h in 1..H,
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h *
          (2 * Real.cosh (h / 2))) =
        (∫ h in 1..H, f h) + ccmThirdGradeCesaroIncomingPolarTail 1 H := by
    rw [ccmThirdGradeCesaroIncomingPolarTail,
      ← intervalIntegral.integral_add hplus hminus]
    apply intervalIntegral.integral_congr
    intro h _
    dsimp only [f, ccmFUSuzukiCriticalOutgoingPolarProfile]
    rw [Real.cosh_eq]
    ring
  unfold ccmFUSuzukiCriticalMarkedPolarDefect
  unfold suzukiCheckpointEventIndex
  unfold suzukiCheckpointCriticalTriangularMultiplier
  change _ = _
  have hsource :
      (∑ j ∈ Finset.range (N - 2),
        (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ)) *
          (Real.sqrt (j + 3 : ℕ) *
            ccmGuinandWeilThirdGradeCesaroTriangularWeight H
              (Real.log ((j + 3 : ℕ) : ℝ)))) =
        ∑ j ∈ Finset.range (N - 2),
          (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ)) *
            Real.sqrt (j + 3 : ℕ) *
              ccmGuinandWeilThirdGradeCesaroTriangularWeight H
                (Real.log ((j + 3 : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [show ⌊Real.exp H⌋₊ = N by rfl, hsource, hsumDiscrete, hpolar]
  dsimp only [f] at hOut
  linarith

/-- The literal CCM-FU / marked-current polar normalization defect is uniformly bounded.  This
is a deterministic reporter equivalence only: it preserves, rather than estimates, the common
signed prime--polar arithmetic current. -/
theorem exists_uniform_bound_ccmFUSuzukiCriticalMarkedPolarDefect :
    ∃ C : ℝ, ∀ H : ℝ, 2 ≤ H →
      |ccmFUSuzukiCriticalMarkedPolarDefect H| ≤ C := by
  let S : ℝ := ∑' m : ℕ, (((m - 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
  let L : ℝ := (Real.exp (1 / 2) * (32 / (Real.log 2) ^ 3)) * (1 - Real.log 2)
  let A : ℝ := 2 * (Real.log 3 - Real.log 2) * Real.sqrt 3 *
    (32 / (Real.log 2) ^ 3)
  let B : ℝ := |suzukiCheckpointCriticalMertensDeviation 0| * (32 * Real.sqrt 3)
  refine ⟨A + 224 * S + L + 32 + 64 + B, ?_⟩
  intro H hH
  let N : ℕ := ⌊Real.exp H⌋₊
  have hlog3H : Real.log (3 : ℝ) ≤ H := by
    calc
      Real.log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 2 := by norm_num
      _ ≤ H := hH
  have hexp3 : (3 : ℝ) ≤ Real.exp H := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.mpr hlog3H
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    exact Nat.le_floor hexp3
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : Real.log (N : ℝ) ≤ H := by
    apply (Real.log_le_iff_le_exp hNpos).mpr
    dsimp only [N]
    exact Nat.floor_le (Real.exp_pos H).le
  have htail :
      |∑ j ∈ Finset.range (N - 3),
          ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 4)| ≤ 224 * S := by
    apply abs_sum_range_ccmFU_outgoingPolarCellError_shift_four_le_tsum hH
    intro j hj
    have hjN : j + 4 ≤ N := by
      have := Finset.mem_range.mp hj
      omega
    calc
      Real.log ((j + 4 : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hjN)
      _ ≤ H := hlogN
  have hsplit :
      (∑ j ∈ Finset.range (N - 2),
        ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3)) =
        ccmFUSuzukiCriticalOutgoingPolarCellError H 3 +
          ∑ j ∈ Finset.range (N - 3),
            ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 4) := by
    let F : ℕ → ℝ := fun j => ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3)
    have hset : Finset.range (N - 2) =
        insert 0 ((Finset.range (N - 3)).image (fun j : ℕ => j + 1)) := by
      ext j
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_image]
      constructor
      · intro hj
        by_cases h0 : j = 0
        · exact Or.inl h0
        · right
          refine ⟨j - 1, ?_, by omega⟩
          omega
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · omega
        · omega
    have hne : 0 ∉ (Finset.range (N - 3)).image (fun j : ℕ => j + 1) := by simp
    have hinj : Set.InjOn (fun j : ℕ => j + 1) (↑(Finset.range (N - 3)) : Set ℕ) := by
      intro a ha b hb hab
      exact Nat.add_right_cancel hab
    have himage := Finset.sum_image (f := F) hinj
    rw [hset, Finset.sum_insert hne, himage]
  have hcells :
      |∑ j ∈ Finset.range (N - 2),
        ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3)| ≤ A + 224 * S := by
    rw [hsplit]
    calc
      |ccmFUSuzukiCriticalOutgoingPolarCellError H 3 +
          ∑ j ∈ Finset.range (N - 3),
            ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 4)| ≤
          |ccmFUSuzukiCriticalOutgoingPolarCellError H 3| +
            |∑ j ∈ Finset.range (N - 3),
              ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 4)| := abs_add_le _ _
      _ ≤ A + 224 * S := by
        apply add_le_add
        · simpa only [A] using abs_ccmFUSuzukiCriticalOutgoingPolarCell_three_le hH
        · exact htail
  have hlower : |ccmFUSuzukiCriticalOutgoingPolarLowerEdge H| ≤ L := by
    simpa only [L] using abs_ccmFUSuzukiCriticalOutgoingPolarLowerEdge_le hH
  have hterminal : |ccmFUSuzukiCriticalOutgoingPolarTerminal H| ≤ 32 :=
    abs_ccmFUSuzukiCriticalOutgoingPolarTerminal_le hH
  have hincoming : |ccmThirdGradeCesaroIncomingPolarTail 1 H| ≤ 64 := by
    simpa only [one_pow, div_one] using
      abs_ccmThirdGradeCesaroIncomingPolarTail_le (b := 1) (by norm_num) (one_le_two.trans hH)
  have hbase : |suzukiCheckpointCriticalMertensDeviation 0 *
      suzukiCheckpointCriticalTriangularMultiplier H 0| ≤ B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_suzukiCheckpointCriticalTriangularMultiplier_zero_le hH)
      (abs_nonneg _)
  rw [ccmFUSuzukiCriticalMarkedPolarDefect_eq_cellSum_add_lower_sub_terminal_sub_incoming_sub_base hH]
  have htri :
      |(∑ j ∈ Finset.range (N - 2),
          ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3)) +
          ccmFUSuzukiCriticalOutgoingPolarLowerEdge H -
          ccmFUSuzukiCriticalOutgoingPolarTerminal H -
          ccmThirdGradeCesaroIncomingPolarTail 1 H -
          suzukiCheckpointCriticalMertensDeviation 0 *
            suzukiCheckpointCriticalTriangularMultiplier H 0| ≤
        |∑ j ∈ Finset.range (N - 2),
          ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3)| +
          |ccmFUSuzukiCriticalOutgoingPolarLowerEdge H| +
          |ccmFUSuzukiCriticalOutgoingPolarTerminal H| +
          |ccmThirdGradeCesaroIncomingPolarTail 1 H| +
          |suzukiCheckpointCriticalMertensDeviation 0 *
            suzukiCheckpointCriticalTriangularMultiplier H 0| := by
    calc
      _ ≤ |(∑ j ∈ Finset.range (N - 2),
          ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3)) +
          ccmFUSuzukiCriticalOutgoingPolarLowerEdge H -
          ccmFUSuzukiCriticalOutgoingPolarTerminal H -
          ccmThirdGradeCesaroIncomingPolarTail 1 H| +
          |suzukiCheckpointCriticalMertensDeviation 0 *
            suzukiCheckpointCriticalTriangularMultiplier H 0| := abs_sub _ _
      _ ≤ |(∑ j ∈ Finset.range (N - 2),
          ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3)) +
          ccmFUSuzukiCriticalOutgoingPolarLowerEdge H -
          ccmFUSuzukiCriticalOutgoingPolarTerminal H| +
          |ccmThirdGradeCesaroIncomingPolarTail 1 H| +
          |suzukiCheckpointCriticalMertensDeviation 0 *
            suzukiCheckpointCriticalTriangularMultiplier H 0| := by
        gcongr
        exact abs_sub _ _
      _ ≤ |(∑ j ∈ Finset.range (N - 2),
          ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3)) +
          ccmFUSuzukiCriticalOutgoingPolarLowerEdge H| +
          |ccmFUSuzukiCriticalOutgoingPolarTerminal H| +
          |ccmThirdGradeCesaroIncomingPolarTail 1 H| +
          |suzukiCheckpointCriticalMertensDeviation 0 *
            suzukiCheckpointCriticalTriangularMultiplier H 0| := by
        gcongr
        exact abs_sub _ _
      _ ≤ |∑ j ∈ Finset.range (N - 2),
          ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3)| +
          |ccmFUSuzukiCriticalOutgoingPolarLowerEdge H| +
          |ccmFUSuzukiCriticalOutgoingPolarTerminal H| +
          |ccmThirdGradeCesaroIncomingPolarTail 1 H| +
          |suzukiCheckpointCriticalMertensDeviation 0 *
            suzukiCheckpointCriticalTriangularMultiplier H 0| := by
        gcongr
        exact abs_add_le _ _
  change |(∑ j ∈ Finset.range (N - 2),
    ccmFUSuzukiCriticalOutgoingPolarCellError H (j + 3)) +
    ccmFUSuzukiCriticalOutgoingPolarLowerEdge H -
    ccmFUSuzukiCriticalOutgoingPolarTerminal H -
    ccmThirdGradeCesaroIncomingPolarTail 1 H -
    suzukiCheckpointCriticalMertensDeviation 0 *
      suzukiCheckpointCriticalTriangularMultiplier H 0| ≤ _
  exact htri.trans (by linarith)

end GaloisForLFunctions.RHTower
