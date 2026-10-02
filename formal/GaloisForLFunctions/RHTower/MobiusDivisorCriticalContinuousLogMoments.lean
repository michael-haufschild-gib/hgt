import GaloisForLFunctions.RHTower.MobiusDivisorCriticalLogMoments
import GaloisForLFunctions.RHTower.CriticalAbelSourceRealIntegral

/-!
# Continuous logarithmic moments of the literal critical step source

The discrete absolute moments extend to the actual floor source on the whole
positive ray. Unit cells retain the source exactly; summability controls their
integral norms. This is the domination input for the old-cutoff Abel transfer.
-/

noncomputable section
open Filter Topology MeasureTheory Set
namespace RHTower

private def criticalStepLogMoment (k : ℕ) (x : ℝ) : ℝ :=
  |psiDefect ⌊x⌋₊| * Real.log x ^ k / x ^ (2 : ℕ)

private theorem floor_unit_cell {n : ℕ} {x : ℝ}
    (hx : x ∈ Ico ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ)) :
    ⌊x⌋₊ = n + 1 := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  apply (Nat.floor_eq_iff (hn.le.trans hx.1)).mpr
  refine ⟨hx.1, ?_⟩
  convert hx.2 using 1
  push_cast
  ring

private theorem criticalStepLogMoment_cell_integrable (k n : ℕ) :
    IntegrableOn (criticalStepLogMoment k)
      (Ico ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hcont : ContinuousOn
      (fun x : ℝ => |psiDefect (n + 1)| * Real.log x ^ k / x ^ (2 : ℕ))
      (Icc ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ)) := by
    apply (continuousOn_const.mul
      ((continuousOn_id.log (fun x hx => (hn.trans_le hx.1).ne')).pow k)).div
      (continuousOn_id.pow 2)
    intro x hx
    exact pow_ne_zero _ (hn.trans_le hx.1).ne'
  apply (hcont.integrableOn_Icc.mono_set Ico_subset_Icc_self).congr_fun
  · intro x hx
    simp only [criticalStepLogMoment, floor_unit_cell hx]
  · exact measurableSet_Ico

private theorem criticalStepLogMoment_cell_bound (k : ℕ) {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : x ∈ Ico ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ)) :
    ‖criticalStepLogMoment k x‖ ≤
      (2 : ℝ) ^ k * (|psiDefect (n + 1)| * Real.log (n + 1 : ℕ) ^ k /
        ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  have hn2 : (2 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (show 2 ≤ n + 1 by omega)
  have hn0 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hx0 : 0 < x := hn0.trans_le hx.1
  have hln : 0 ≤ Real.log (n + 1 : ℕ) := Real.log_nonneg (by linarith)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith [hx.1])
  have hxup : x ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
    have hh := hx.2
    push_cast at hh ⊢
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hl : Real.log x ≤ 2 * Real.log (n + 1 : ℕ) := by
    have hb := Real.log_le_log hx0 hxup
    rw [Real.log_mul (by norm_num) hn0.ne'] at hb
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn2
    linarith
  rw [criticalStepLogMoment, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), floor_unit_cell hx]
  calc
    |psiDefect (n + 1)| * Real.log x ^ k / x ^ (2 : ℕ) ≤
        |psiDefect (n + 1)| * (2 * Real.log (n + 1 : ℕ)) ^ k /
          ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by
      gcongr
      exact hx.1
    _ = _ := by rw [mul_pow]; ring

/-- Every absolute logarithmic moment of the actual floor source is integrable
at its first Mellin boundary. -/
theorem integrableOn_psiDefect_floor_log_moment (k : ℕ) :
    IntegrableOn
      (fun x : ℝ => |psiDefect ⌊x⌋₊| * Real.log x ^ k / x ^ (2 : ℕ))
      (Ioi (1 : ℝ)) := by
  let S : ℕ → Set ℝ := fun n => Ico ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ)
  have hs : Summable (fun n : ℕ =>
      (2 : ℝ) ^ k * (|psiDefect (n + 1)| * Real.log (n + 1 : ℕ) ^ k /
        ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))) :=
    ((summable_nat_add_iff 1).mpr (summable_psiDefect_log_moment k)).mul_left _
  have hint : Summable (fun n : ℕ => ∫ x in S n, ‖criticalStepLogMoment k x‖) := by
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    have hm := integral_mono_ae (criticalStepLogMoment_cell_integrable k n).norm
      (integrable_const ((2 : ℝ) ^ k *
        (|psiDefect (n + 1)| * Real.log (n + 1 : ℕ) ^ k /
          ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
        exact criticalStepLogMoment_cell_bound k hn hx)
    have hvol : volume.real (Ico ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ)) = 1 := by
      norm_num [Real.volume_real_Ico, Nat.cast_add]
    simpa only [setIntegral_const, hvol, one_smul] using hm
  have hi := integrableOn_iUnion_of_summable_integral_norm
    (criticalStepLogMoment_cell_integrable k) hint
  apply hi.mono_set
  intro x hx
  have hx0 : 0 ≤ x := (lt_trans zero_lt_one hx).le
  have hn : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx.le)
  refine mem_iUnion.mpr ⟨⌊x⌋₊ - 1, ?_⟩
  rw [Nat.sub_add_cancel hn, show ⌊x⌋₊ - 1 + 2 = ⌊x⌋₊ + 1 by omega]
  exact ⟨Nat.floor_le hx0, by exact_mod_cast Nat.lt_floor_add_one x⟩

end RHTower
