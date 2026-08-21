import Mathlib.Analysis.SpecialFunctions.Log.Basic
example (x y : ℝ) (hy : 0 < y) (h : Real.exp x < y) : x ≤ Real.log y := by
  have h2 := Real.log_le_log (Real.exp_pos x) h.le
  rwa [Real.log_exp] at h2
