import GaloisForLFunctions.HTGeometry.FiniteLawPositiveApproximation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Exact logarithmic boundary profiles for positive finite-law approximations -/

namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Law

open Filter
open scoped Topology

variable {α : Type*} [Fintype α] [Nonempty α]

noncomputable def zeroMassIndicator (Q : Law α) (i : α) : ℝ := by
  classical
  exact if Q i = 0 then 1 else 0

noncomputable def boundaryLogValue (Q : Law α) (w : α → ℝ) (i : α) : ℝ := by
  classical
  exact if Q i = 0 then Real.log (uniform α i / w i) else Real.log (Q i / w i)

theorem tendsto_uniformApproximation_apply (Q : Law α) (i : α) :
    Tendsto (fun n : ℕ => Q.uniformApproximation n i) atTop (𝓝 (Q i)) := by
  have ht := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h := (ht.mul_const (uniform α i)).add
    (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub ht).mul_const (Q i))
  simpa only [uniformApproximation_apply, zero_mul, sub_zero, one_mul, zero_add] using h

theorem uniformApproximation_log_eq_of_zero (Q : Law α) (w : α → ℝ)
    (i : α) (hw : 0 < w i) (hi : Q i = 0) (n : ℕ) :
    Real.log (Q.uniformApproximation n i / w i) =
      Real.log (uniform α i / w i) - Real.log ((n : ℝ) + 1) := by
  rw [uniformApproximation_apply, hi, mul_zero, add_zero]
  have hU : 0 < uniform α i := by rw [uniform_apply]; positivity
  rw [show (1 / ((n : ℝ) + 1)) * uniform α i / w i =
      (uniform α i / w i) / ((n : ℝ) + 1) by ring,
    Real.log_div (div_pos hU hw).ne' (by positivity)]

theorem tendsto_uniformApproximation_log_of_pos (Q : Law α) (w : α → ℝ)
    (i : α) (hw : 0 < w i) (hi : 0 < Q i) :
    Tendsto (fun n : ℕ => Real.log (Q.uniformApproximation n i / w i))
      atTop (𝓝 (Real.log (Q i / w i))) :=
  (Real.continuousAt_log (div_pos hi hw).ne').tendsto.comp
    ((tendsto_uniformApproximation_apply Q i).div_const (w i))

theorem tendsto_uniformApproximation_renormalized_log (Q : Law α) (w : α → ℝ)
    (i : α) (hw : 0 < w i) :
    Tendsto (fun n : ℕ => Real.log (Q.uniformApproximation n i / w i) +
      Real.log ((n : ℝ) + 1) * Q.zeroMassIndicator i)
      atTop (𝓝 (Q.boundaryLogValue w i)) := by
  classical
  by_cases hi : Q i = 0
  · have heq (n : ℕ) : Real.log (Q.uniformApproximation n i / w i) +
        Real.log ((n : ℝ) + 1) * Q.zeroMassIndicator i = Q.boundaryLogValue w i := by
      rw [uniformApproximation_log_eq_of_zero Q w i hw hi]
      simp only [zeroMassIndicator, boundaryLogValue, hi, if_pos, mul_one, sub_add_cancel]
    simpa only [heq] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => Q.boundaryLogValue w i) atTop (𝓝 (Q.boundaryLogValue w i)))
  · have hpos : 0 < Q i := lt_of_le_of_ne (Q.nonneg i) (Ne.symm hi)
    simpa only [zeroMassIndicator, boundaryLogValue, hi, if_false, mul_zero, add_zero] using
      tendsto_uniformApproximation_log_of_pos Q w i hw hpos

theorem tendsto_uniformApproximation_log_atBot_iff (Q : Law α) (w : α → ℝ)
    (i : α) (hw : 0 < w i) :
    Tendsto (fun n : ℕ => Real.log (Q.uniformApproximation n i / w i)) atTop atBot ↔
      Q i = 0 := by
  constructor
  · intro h
    by_contra hi
    have hpos : 0 < Q i := lt_of_le_of_ne (Q.nonneg i) (Ne.symm hi)
    exact (not_tendsto_atBot_of_tendsto_nhds
      (tendsto_uniformApproximation_log_of_pos Q w i hw hpos)) h
  · intro hi
    have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop := by
      have h : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp
          ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
      simpa only [Nat.cast_add, Nat.cast_one] using h
    refine tendsto_atBot.mpr (fun b => ?_)
    filter_upwards [tendsto_atTop.mp hlog (Real.log (uniform α i / w i) - b)] with n hn
    rw [uniformApproximation_log_eq_of_zero Q w i hw hi]
    linarith

end GaloisForLFunctions.HTGeometry.FourierLLogL.Law
