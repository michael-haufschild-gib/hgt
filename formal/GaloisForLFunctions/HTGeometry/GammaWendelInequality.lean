/-
# Wendel's inequality for the Gamma function

Log-convexity of `Γ` pins the ratio `Γ(x+a)/Γ(x)` between `x/(x+a)^{1-a}` and `x^a` for
`0 ≤ a ≤ 1`.  Both bounds are asymptotically `x^a`, so the ratio is asymptotically `x^a` -- the
statement a root-growth computation on a lattice of arbitrary spacing needs, and the only Gamma
asymptotic it needs.

Main results:
* `Gamma_add_le` — the upper half of Wendel's inequality.
* `le_Gamma_add` — the lower half.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

open Real Set

namespace GaloisForLFunctions.HTGeometry

/-- **Wendel's upper bound**: `Γ(x+a) ≤ Γ(x)·x^a` for `0 ≤ a ≤ 1`. -/
theorem Gamma_add_le {x a : ℝ} (hx : 0 < x) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.Gamma (x + a) ≤ Real.Gamma x * x ^ a := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hxmem : x ∈ Ioi (0 : ℝ) := hx
  have hx1mem : (x + 1) ∈ Ioi (0 : ℝ) := hx1
  have hcomb : (1 - a) • x + a • (x + 1) = x + a := by
    simp only [smul_eq_mul]
    ring
  have hconv := convexOn_log_Gamma.2 hxmem hx1mem (by linarith : (0:ℝ) ≤ 1 - a) ha0
    (by ring : (1 - a) + a = 1)
  rw [hcomb] at hconv
  have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hGxa : 0 < Real.Gamma (x + a) := Real.Gamma_pos_of_pos (by linarith)
  have hGx1 : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hx.ne'
  have hlog : Real.log (Real.Gamma (x + a))
      ≤ Real.log (Real.Gamma x) + a * Real.log x := by
    have h := hconv
    simp only [Function.comp_apply, smul_eq_mul] at h
    rw [hGx1, Real.log_mul hx.ne' hGx.ne'] at h
    linarith
  have hexp : Real.Gamma (x + a) ≤ Real.exp (Real.log (Real.Gamma x) + a * Real.log x) := by
    calc Real.Gamma (x + a) = Real.exp (Real.log (Real.Gamma (x + a))) :=
          (Real.exp_log hGxa).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  refine le_trans hexp (le_of_eq ?_)
  rw [Real.exp_add, Real.exp_log hGx, Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- **Wendel's lower bound**: `Γ(x)·x ≤ Γ(x+a)·(x+a)^{1-a}` for `0 ≤ a ≤ 1`. -/
theorem le_Gamma_add {x a : ℝ} (hx : 0 < x) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.Gamma x * x ≤ Real.Gamma (x + a) * (x + a) ^ (1 - a) := by
  have hxa : (0 : ℝ) < x + a := by linarith
  have hxa1 : (0 : ℝ) < x + 1 + a := by linarith
  have hcomb : a • (x + a) + (1 - a) • (x + 1 + a) = x + 1 := by
    simp only [smul_eq_mul]
    ring
  have hconv := convexOn_log_Gamma.2 (hxa : (x + a) ∈ Ioi (0:ℝ))
    (hxa1 : (x + 1 + a) ∈ Ioi (0:ℝ)) ha0 (by linarith : (0:ℝ) ≤ 1 - a)
    (by ring : a + (1 - a) = 1)
  rw [hcomb] at hconv
  have hGx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hGxa : 0 < Real.Gamma (x + a) := Real.Gamma_pos_of_pos hxa
  have hGx1 : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hx.ne'
  have hshift : Real.Gamma (x + 1 + a) = (x + a) * Real.Gamma (x + a) := by
    have : x + 1 + a = (x + a) + 1 := by ring
    rw [this, Real.Gamma_add_one hxa.ne']
  have hlog : Real.log (x * Real.Gamma x)
      ≤ Real.log (Real.Gamma (x + a)) + (1 - a) * Real.log (x + a) := by
    have h := hconv
    simp only [Function.comp_apply, smul_eq_mul] at h
    rw [hGx1, hshift, Real.log_mul hxa.ne' hGxa.ne'] at h
    linarith
  have hpos : 0 < x * Real.Gamma x := mul_pos hx hGx
  have hexp : x * Real.Gamma x
      ≤ Real.exp (Real.log (Real.Gamma (x + a)) + (1 - a) * Real.log (x + a)) := by
    calc x * Real.Gamma x = Real.exp (Real.log (x * Real.Gamma x)) := (Real.exp_log hpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  have hfin : Real.exp (Real.log (Real.Gamma (x + a)) + (1 - a) * Real.log (x + a))
      = Real.Gamma (x + a) * (x + a) ^ (1 - a) := by
    rw [Real.exp_add, Real.exp_log hGxa, Real.rpow_def_of_pos hxa]
    congr 1
    ring
  rw [mul_comm]
  exact le_trans hexp (le_of_eq hfin)

end GaloisForLFunctions.HTGeometry
