import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Polynomial growth against exponential decay

A single term of the exponential series gives `u^N ≤ N! e^{cu} / c^N` for `u ≥ 0`, hence the
explicit bound `u^N e^{-cu} ≤ N!/c^N`.  Absorbing two extra powers turns any bound of the shape
`C |t|^N e^{-c|t|}` into a multiple of the integrable weight `(1+t²)⁻¹`, which is what a
domination argument for a vertical contour integral consumes.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A power is dominated by an exponential, with an explicit constant. -/
theorem pow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    u ^ N * Real.exp (-(c * u)) ≤ (N.factorial : ℝ) / c ^ N := by
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos N
  have hbase := Real.pow_div_factorial_le_exp (c * u) (by positivity) N
  have hcu : (c * u) ^ N = c ^ N * u ^ N := mul_pow _ _ _
  rw [hcu, div_le_iff₀ hfac] at hbase
  have hexp : (0 : ℝ) < Real.exp (-(c * u)) := Real.exp_pos _
  have hkey : c ^ N * u ^ N * Real.exp (-(c * u))
      ≤ Real.exp (c * u) * (N.factorial : ℝ) * Real.exp (-(c * u)) :=
    mul_le_mul_of_nonneg_right hbase (le_of_lt hexp)
  have hcancel : Real.exp (c * u) * (N.factorial : ℝ) * Real.exp (-(c * u))
      = (N.factorial : ℝ) := by
    rw [mul_comm (Real.exp (c * u)) ((N.factorial : ℝ)), mul_assoc, ← Real.exp_add]
    simp
  rw [hcancel] at hkey
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < c ^ N)]
  calc u ^ N * Real.exp (-(c * u)) * c ^ N = c ^ N * u ^ N * Real.exp (-(c * u)) := by ring
    _ ≤ (N.factorial : ℝ) := hkey

/-- **Exponential decay dominates the Cauchy weight.**  A bound of the shape `C |t|^N e^{-c|t|}` is
a multiple of `(1+t²)⁻¹`. -/
theorem polyExp_le_inv_one_add_sq {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (N : ℕ) (t : ℝ) :
    C * |t| ^ N * Real.exp (-(c * |t|))
      ≤ (C * Real.exp c * (((N + 2).factorial : ℝ) / c ^ (N + 2))) * (1 + t ^ 2)⁻¹ := by
  have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hu : (0 : ℝ) ≤ 1 + |t| := by linarith
  have hexp : (0 : ℝ) < Real.exp (-(c * |t|)) := Real.exp_pos _
  rw [le_mul_inv_iff₀ hden]
  have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
    have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    nlinarith [abs_nonneg t]
  have hpow : |t| ^ N ≤ (1 + |t|) ^ N := pow_le_pow_left₀ habs (by linarith) N
  have hstep : C * |t| ^ N * Real.exp (-(c * |t|)) * (1 + t ^ 2)
      ≤ C * (1 + |t|) ^ N * Real.exp (-(c * |t|)) * (1 + |t|) ^ 2 := by
    have h1 : C * |t| ^ N * Real.exp (-(c * |t|)) ≤ C * (1 + |t|) ^ N * Real.exp (-(c * |t|)) := by
      have := mul_le_mul_of_nonneg_left hpow hC
      exact mul_le_mul_of_nonneg_right this (le_of_lt hexp)
    have h2 : (0 : ℝ) ≤ C * (1 + |t|) ^ N * Real.exp (-(c * |t|)) := by positivity
    calc C * |t| ^ N * Real.exp (-(c * |t|)) * (1 + t ^ 2)
        ≤ C * (1 + |t|) ^ N * Real.exp (-(c * |t|)) * (1 + t ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hden)
      _ ≤ C * (1 + |t|) ^ N * Real.exp (-(c * |t|)) * (1 + |t|) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq h2
  refine hstep.trans ?_
  have hshift : Real.exp (-(c * |t|)) = Real.exp c * Real.exp (-(c * (1 + |t|))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcollect : C * (1 + |t|) ^ N * Real.exp (-(c * |t|)) * (1 + |t|) ^ 2
      = C * Real.exp c * ((1 + |t|) ^ (N + 2) * Real.exp (-(c * (1 + |t|)))) := by
    rw [hshift, pow_add]
    ring
  rw [hcollect]
  have hbound := pow_mul_exp_neg_le hc (N + 2) hu
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end GaloisForLFunctions.HTGeometry
