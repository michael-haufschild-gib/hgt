import GaloisForLFunctions.BiScaleUncertainty.DivisorEnergyCompletion

/-!
# An explicit completed state escaping square-summable traces

For the full divisor family, unit cell 1 has a constant nonzero trace tail.
Finite linear ramps approximate that state with exact squared physical error
1/(n+1). Both the state and the approximating old data are actual producers.
-/

noncomputable section
open Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def fullDivisorEscape (d : ℕ) : DivisorEnergyData d Set.univ :=
  ⟨lp.single 2 1 1, (mem_divisorCellSpace_univ d _).mpr (by simp [lp.single_apply])⟩

theorem fullDivisorEscape_extension (d : ℕ) :
    divisorEnergyExtension d Set.univ (fullDivisorEscape d) = unitCell 1 := by
  change unitCellSynthesis (lp.single 2 1 1) = _
  rw [unitCellSynthesis_single, one_smul]

theorem fullDivisorEscape_norm (d : ℕ) :
    ‖divisorEnergyExtension d Set.univ (fullDivisorEscape d)‖ = 1 := by
  rw [(divisorEnergyExtension d Set.univ).norm_map]
  change ‖(lp.single 2 1 (1 : ℝ) : TraceData)‖ = 1
  simp

theorem fullDivisorEscape_trace (d k : ℕ) :
    divisorCompletedTrace d Set.univ (fullDivisorEscape d) k = if k = 0 then 0 else 1 := by
  rw [divisorCompletedTrace, ← primitive_unitCellSynthesis, ← inner_prefixCell]
  change inner ℝ (prefixCell (k+1)) (unitCellSynthesis (lp.single 2 1 1)) = _
  rw [unitCellSynthesis_single, one_smul, inner_prefixCell_unitCell]
  split_ifs <;> first | omega | rfl

theorem fullDivisorEscape_not_memℓp (d : ℕ) :
    ¬ Memℓp (divisorCompletedTrace d Set.univ (fullDivisorEscape d)) 2 := by
  intro h
  let v : TraceData := ⟨divisorCompletedTrace d Set.univ (fullDivisorEscape d), h⟩
  have hz := traceData_tail_constant_zero v 1 1 (fun n => by
    change divisorCompletedTrace d Set.univ (fullDivisorEscape d) (1+n) = 1
    rw [fullDivisorEscape_trace, if_neg (by omega)])
  exact one_ne_zero hz

theorem unitCell_one_not_divisorGrid_range (d : ℕ) :
    unitCell 1 ∉ Set.range (divisorGridExtension d Set.univ) := by
  rw [← fullDivisorEscape_extension d, divisorEnergy_recovery_iff]
  exact fullDivisorEscape_not_memℓp d

def fullDivisorRampRaw (n : ℕ) : TraceData :=
  intervalTraceData 1 (n+1) (fun j => 1-(j : ℝ)/((n : ℝ)+1))

theorem fullDivisorRampRaw_zero (n : ℕ) : fullDivisorRampRaw n 0 = 0 := by
  apply intervalTraceData_off
  intro j _
  omega

theorem fullDivisorRampRaw_succ (n k : ℕ) :
    fullDivisorRampRaw n (k+1) = if k < n+1 then 1-(k : ℝ)/((n : ℝ)+1) else 0 := by
  simpa only [Nat.add_comm 1 k] using
    intervalTraceData_at 1 (n+1) k (fun j => 1-(j : ℝ)/((n : ℝ)+1))

def fullDivisorRamp (d n : ℕ) : DivisorGridData d Set.univ :=
  ⟨fullDivisorRampRaw n, (mem_divisorGridDataSpace_iff d Set.univ _).mpr (by
    intro k hk
    have hk0 : k = 0 := by
      by_contra hn
      exact hk (divisorGrid_univ_active d k (by omega))
    rw [hk0, fullDivisorRampRaw_zero])⟩

theorem fullDivisorRamp_gradient (n : ℕ) :
    traceGradient (fullDivisorRampRaw n) = lp.single 2 1 1 -
      (1 / ((n : ℝ)+1)) • intervalTraceData 2 (n+1) (fun _ => 1) := by
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  apply lp.ext
  funext k
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  cases k with
  | zero =>
      rw [traceGradient_zero, fullDivisorRampRaw_zero,
        intervalTraceData_off 2 (n+1) 0 _ (by intro j _; omega)]
      simp [lp.single_apply]
  | succ k =>
      rw [traceGradient_succ, fullDivisorRampRaw_succ]
      cases k with
      | zero =>
          rw [fullDivisorRampRaw_zero,
            intervalTraceData_off 2 (n+1) 1 _ (by intro j _; omega)]
          simp [lp.single_apply]
      | succ j =>
          rw [fullDivisorRampRaw_succ,
            show j+1+1 = 2+j by omega, intervalTraceData_at]
          have hj1 : 2+j ≠ 1 := by omega
          simp only [lp.single_apply, Pi.single_eq_of_ne hj1, zero_sub]
          by_cases hj : j < n+1
          · simp only [if_pos hj]
            by_cases hjn : j+1 < n+1
            · rw [if_pos hjn]
              push_cast
              field_simp [hn]
              <;> ring
            · rw [if_neg hjn]
              have he : j = n := by omega
              subst j
              field_simp [hn]
              <;> ring
          · simp only [if_neg hj, if_neg (by omega : ¬ j+1 < n+1)]
            ring

/-- An unconditional exact error for finite arithmetic trace producers. -/
theorem fullDivisorRamp_error (d n : ℕ) :
    ‖divisorGridExtension d Set.univ (fullDivisorRamp d n) - unitCell 1‖^2 =
      1 / ((n : ℝ)+1) := by
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  have hc : unitCell 1 = unitCellSynthesis (lp.single 2 1 1) := by
    rw [unitCellSynthesis_single, one_smul]
  change ‖unitCellSynthesis (traceGradient (fullDivisorRampRaw n)) - unitCell 1‖^2 = _
  rw [hc, ← map_sub, unitCellSynthesis.norm_map, fullDivisorRamp_gradient]
  have he : (lp.single 2 1 (1 : ℝ) -
      (1 / ((n : ℝ)+1)) • intervalTraceData 2 (n+1) (fun _ => 1)) - lp.single 2 1 1 =
      -((1 / ((n : ℝ)+1)) • intervalTraceData 2 (n+1) (fun _ => 1)) := by abel
  rw [he, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, intervalTraceData_norm_sq]
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Nat.cast_add, Nat.cast_one]
  field_simp [hn]

theorem fullDivisorRamp_error_tendsto (d : ℕ) :
    Tendsto (fun n => ‖divisorGridExtension d Set.univ (fullDivisorRamp d n) - unitCell 1‖^2)
      atTop (𝓝 0) := by
  simp only [fullDivisorRamp_error]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
