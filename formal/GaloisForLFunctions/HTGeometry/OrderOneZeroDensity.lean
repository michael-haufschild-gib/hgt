/-
# Jensen's inequality turns an order-one envelope into an order-one zero density

An entire function with the growth envelope `‖f z‖ ≤ exp (C (1+‖z‖) log (2+‖z‖))` and `f 0 ≠ 0`
has at most `K (1+r) log (2+r)` zeros, with multiplicity, in the disc of radius `r`.

Jensen's inequality on the pair of radii `r < 2r` bounds the divisor mass of the small disc by
`log (M / ‖f 0‖) / log 2` with `M` the maximum modulus on the large circle; the envelope bounds
`log M` by `4 C (1+r) log (2+r)`, and the fixed constant `-log ‖f 0‖` is absorbed because
`(1+r) log (2+r) ≥ 1` for `r ≥ 1`.
-/
import GaloisForLFunctions.HTGeometry.OrderOneConvergenceExponent
import GaloisForLFunctions.HTGeometry.QuadraticSubtypeHadamard

noncomputable section

open Filter Topology Set Metric

namespace GaloisForLFunctions.CountableDivisor

open GaloisForLFunctions.EntireZeroDivisor GaloisForLFunctions.QuadraticSubtypeHadamard

/-- **Jensen's counting bound at order one.**  The zero-copy divisor of an entire function with an
order-one growth envelope has order-one density. -/
theorem orderOneDensityIdx_zeroCopyPoint {f : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    OrderOneDensityIdx (zeroCopyPoint f) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(4 * C + |Real.log ‖f 0‖|) / Real.log 2, by positivity, fun r hr => ?_⟩
  have hrpos : (0 : ℝ) < r := by linarith
  have hRpos : (0 : ℝ) < 2 * r := by linarith
  set M : ℝ := Real.exp (C * (1 + 2 * r) * Real.log (2 + 2 * r)) with hM
  have hshape : (0 : ℝ) ≤ C * (1 + 2 * r) * Real.log (2 + 2 * r) := by
    have hlog : (0 : ℝ) ≤ Real.log (2 + 2 * r) := Real.log_nonneg (by linarith)
    have h1 : (0 : ℝ) ≤ C * (1 + 2 * r) := by positivity
    positivity
  have hM1 : (1 : ℝ) ≤ M := by rw [hM]; exact Real.one_le_exp hshape
  have hsphere : ∀ z ∈ Metric.sphere (0 : ℂ) |2 * r|, ‖f z‖ ≤ M := by
    intro z hz
    have hzn : ‖z‖ = 2 * r := by
      have := Metric.mem_sphere.mp hz
      rw [dist_zero_right] at this
      rw [this, abs_of_pos hRpos]
    rw [hM, ← hzn]
    exact hbound z
  have hjensen := hf.mono (Set.subset_univ _) |>.sum_divisor_le
    (r := r) (R := 2 * r) (M := M) (by rwa [abs_of_pos hrpos])
    (by rw [abs_of_pos hrpos, abs_of_pos hRpos]; linarith) hM1 hf0 hsphere
  rw [abs_of_pos hrpos] at hjensen
  have hratio : Real.log (2 * r / r) = Real.log 2 := by
    congr 1
    field_simp
  rw [hratio] at hjensen
  have hcount : ((divisorIdxCount (zeroCopyPoint f) r : ℕ) : ℝ)
      = ((∑ᶠ u : ℂ, (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r)) u : ℤ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) (divisorIdxCount_eq hf r)
  rw [hcount]
  refine le_trans hjensen ?_
  have hlogM : Real.log (M / ‖f 0‖) = C * (1 + 2 * r) * Real.log (2 + 2 * r) - Real.log ‖f 0‖ := by
    rw [Real.log_div (by positivity) (norm_ne_zero_iff.mpr hf0), hM, Real.log_exp]
  rw [hlogM]
  -- the envelope term
  have hlogr : (0 : ℝ) ≤ Real.log (2 + r) := Real.log_nonneg (by linarith)
  have hlogrge : (1 : ℝ) ≤ Real.log (2 + r) := by
    have h3 : Real.log 3 ≤ Real.log (2 + r) := Real.log_le_log (by norm_num) (by linarith)
    have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
      have := Real.exp_one_lt_d9
      have hmono : Real.log (Real.exp 1) ≤ Real.log 3 :=
        Real.log_le_log (Real.exp_pos 1) (by linarith)
      rwa [Real.log_exp] at hmono
    linarith
  have hdouble : Real.log (2 + 2 * r) ≤ 2 * Real.log (2 + r) := by
    have hsq : (2 : ℝ) + 2 * r ≤ (2 + r) ^ 2 := by nlinarith
    calc Real.log (2 + 2 * r) ≤ Real.log ((2 + r) ^ 2) :=
          Real.log_le_log (by linarith) hsq
      _ = 2 * Real.log (2 + r) := by
          rw [Real.log_pow]; push_cast; ring
  have henv : C * (1 + 2 * r) * Real.log (2 + 2 * r) ≤ 4 * C * ((1 + r) * Real.log (2 + r)) := by
    have h1 : C * (1 + 2 * r) ≤ 2 * C * (1 + r) := by nlinarith
    have hlognn : (0 : ℝ) ≤ Real.log (2 + 2 * r) := Real.log_nonneg (by linarith)
    calc C * (1 + 2 * r) * Real.log (2 + 2 * r)
        ≤ (2 * C * (1 + r)) * Real.log (2 + 2 * r) := by
          exact mul_le_mul_of_nonneg_right h1 hlognn
      _ ≤ (2 * C * (1 + r)) * (2 * Real.log (2 + r)) := by
          refine mul_le_mul_of_nonneg_left hdouble ?_
          positivity
      _ = 4 * C * ((1 + r) * Real.log (2 + r)) := by ring
  have hshapege : (1 : ℝ) ≤ (1 + r) * Real.log (2 + r) := by nlinarith
  have habs : -Real.log ‖f 0‖ ≤ |Real.log ‖f 0‖| * ((1 + r) * Real.log (2 + r)) := by
    have h1 : -Real.log ‖f 0‖ ≤ |Real.log ‖f 0‖| := neg_le_abs _
    nlinarith [abs_nonneg (Real.log ‖f 0‖)]
  have hkey : (C * (1 + 2 * r) * Real.log (2 + 2 * r) - Real.log ‖f 0‖) / Real.log 2
      ≤ ((4 * C + |Real.log ‖f 0‖|) * ((1 + r) * Real.log (2 + r))) / Real.log 2 :=
    (div_le_div_iff_of_pos_right hlog2).mpr (by nlinarith [henv, habs])
  refine le_trans hkey (le_of_eq ?_)
  field_simp

end GaloisForLFunctions.CountableDivisor
