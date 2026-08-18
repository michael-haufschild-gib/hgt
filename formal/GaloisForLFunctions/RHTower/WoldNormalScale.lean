import GaloisForLFunctions.RHTower.AcceleratedWoldType

/-!
# The Wold normal scale

`prime-valuation-dyadic-fermion-normal-cone-law`, equation `(17)`.

Mertens' third theorem says the ordinary-prime Wold boundary volume `a_x = ∏_{p ≤ x}(1 - p^{-1})`
satisfies `a_x log x → e^{-γ}`.  Consequently the critical normal coordinate `u = c log x` is
exactly `e^{-γ} c / a_x` up to a factor tending to one: the Wold volume *is* the critical scale.
-/

open Filter Topology

namespace RHTower

/-- **`(17)`: the Wold boundary volume is the critical normal scale.** -/
theorem tendsto_woldNormalScale :
    Tendsto (fun N : ℕ => Real.exp (-Real.eulerMascheroniConstant)
        / (mertensPrimeProductBelow N * Real.log N)) atTop (nhds 1) := by
  have hne : Real.exp (-Real.eulerMascheroniConstant) ≠ 0 := (Real.exp_pos _).ne'
  have h := tendsto_const_nhds (x := Real.exp (-Real.eulerMascheroniConstant))
    (f := atTop (α := ℕ)) |>.div tendsto_mertensPrimeProductBelow_mul_log hne
  rwa [div_self hne] at h

/-- The normal coordinate `u = c log x` read in the Wold coordinate. -/
theorem tendsto_woldNormalCoordinate {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun N : ℕ => (Real.exp (-Real.eulerMascheroniConstant) * c
        / mertensPrimeProductBelow N) / (c * Real.log N)) atTop (nhds 1) := by
  refine tendsto_woldNormalScale.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have hmert : mertensPrimeProductBelow N ≠ 0 := (mertensPrimeProductBelow_pos N).ne'
  field_simp

end RHTower
