import GaloisForLFunctions.RHTower.Sieve.ChebyshevSharpSelfRateOne
import GaloisForLFunctions.PNTPlus.MediumPNT

/-!
# The exponent-`1/2` estimate in the shape of `MediumPNT`

`Chebyshev.psi_eq_sum_range` identifies `ψ` with the partial sum of the von Mangoldt function, so
the width-`1/log` contour's conclusion becomes a statement about `ψ` in the same `IsBigO` form the
vendored `MediumPNT` uses:

```text
ψ - id  =O[atTop]  x · exp( -c √(log x) ),
```

against `MediumPNT`'s `x · exp(-c (log x)^{1/10})`.
-/

namespace RHTower.Sieve

open Filter Topology Asymptotics ArithmeticFunction

/-- **The prime number theorem with a square-root-logarithmic error term.**  Same shape as the
vendored `MediumPNT`, with the exponent `1/2` in place of `1/10`. -/
theorem chebyshevPsi_sub_id_isBigO :
    ∃ c > 0, (Chebyshev.psi - id) =O[atTop]
      fun x : ℝ => x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨B, hB, hrate⟩ := exists_abs_sum_vonMangoldt_sub_self_kappa_one_rate
  refine ⟨1 / 960000, by norm_num, Asymptotics.IsBigO.of_bound B ?_⟩
  filter_upwards [hrate, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  have hexp : (0 : ℝ) < Real.exp (-(1 / 960000) * Real.sqrt (Real.log N)) := Real.exp_pos _
  have hgnorm : ‖N * Real.exp (-(1 / 960000) * Real.sqrt (Real.log N))‖
      = N * Real.exp (-(1 / 960000) * Real.sqrt (Real.log N)) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hcongr : Real.exp (-(Real.sqrt (Real.log N) / 960000))
      = Real.exp (-(1 / 960000) * Real.sqrt (Real.log N)) := by
    congr 1
    ring
  rw [Pi.sub_apply, id_eq, Chebyshev.psi_eq_sum_range, Real.norm_eq_abs, hgnorm]
  rw [hcongr] at hN
  linarith [hN]

end RHTower.Sieve
