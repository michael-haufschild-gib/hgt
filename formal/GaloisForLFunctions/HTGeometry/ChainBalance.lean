import GaloisForLFunctions.HTGeometry.TunableDuhamel

/-!
# The chaining balance is achievable

A tunable transfer step with parameter `ε` multiplies the kernel bound by `√(1 + ε)` and admits a
step length proportional to `√ε`: smaller `ε` means slower growth but shorter steps.  Reaching every
point of `ℂ` by chaining needs both — the growth factors must have bounded product, and the step
lengths must have divergent sum.

Those demands are compatible.  With `εₙ = 1/(n+1)²` the parameters are summable, so the growth
factors are controlled, while `√εₙ = 1/(n+1)` is not summable, so the chain reaches arbitrarily far.
This is why the fixed constant `2` of the current transfer is the obstruction and not the geometry:
`ε = 1` is simply the wrong point on this trade-off.
-/

open scoped BigOperators

namespace HTGeometry

/-- **The two chaining demands are compatible.**  There are positive parameters that are summable
while their square roots are not. -/
theorem exists_summable_sqrt_not_summable :
    ∃ e : ℕ → ℝ, (∀ n, 0 < e n) ∧ Summable e ∧ ¬ Summable fun n => Real.sqrt (e n) := by
  refine ⟨fun n => (1 : ℝ) / ((n : ℝ) + 1) ^ 2, fun n => by positivity, ?_, ?_⟩
  · have hbase : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    have hshift := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hbase
    refine hshift.congr fun n => ?_
    push_cast
    ring
  · have hharm : ¬ Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) := by
      intro hc
      refine Real.not_summable_one_div_natCast ?_
      refine (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) 1).mp ?_
      refine hc.congr fun n => ?_
      push_cast
      ring
    intro hc
    refine hharm ?_
    refine hc.congr fun n => ?_
    show Real.sqrt ((1 : ℝ) / ((n : ℝ) + 1) ^ 2) = (1 : ℝ) / ((n : ℝ) + 1)
    have hid : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 = ((1 : ℝ) / ((n : ℝ) + 1)) ^ 2 := by
      field_simp
    rw [hid, Real.sqrt_sq (by positivity)]

end HTGeometry
