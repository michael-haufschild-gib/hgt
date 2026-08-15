import GaloisForLFunctions.RHTower.CCMRadialProlateDefect

/-!
# The exterior radial normal-form potential is a `1/x²` symbol

After the Liouville transform the exterior radial prolate equation reads `W'' + (c² − ψ)W = 0`, and
the potential `ψ` is the corpus's `lgNormalFormDefect s c (radialProlateQ s c)`, already known to
satisfy `|ψ| ≤ 40/(x² − 1)` uniformly in the bandwidth — the aperture cancels exactly in the normal
form, so no `c` survives in the potential.

Beyond the second dilation `x² − 1 ≥ (3/4)x²`, so the same bound reads

```text
|ψ(x)| ≤ 54/x² ,
```

which is the short-range decay the interaction picture consumes: it is what makes the amplitudes
move by `O(1/c)` and the transported derivative a genuine `1/x²` symbol.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **The normal-form potential is a `1/x²` symbol beyond the second dilation.** -/
theorem abs_lgNormalFormDefect_radialProlate_le_sq {s c x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 2 ≤ x) :
    |lgNormalFormDefect s c (radialProlateQ s c) x| ≤ 54 / x ^ 2 := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hxsq : (4 : ℝ) ≤ x ^ 2 := by nlinarith
  have hd : (0 : ℝ) < x ^ 2 - 1 := by linarith
  have hbase := abs_lgNormalFormDefect_radialProlate_le (s := s) (c := c) hs0 hs1 hx1
  refine hbase.trans ?_
  rw [div_le_div_iff₀ hd (by positivity)]
  nlinarith [hxsq]

end GaloisForLFunctions.RHTower

end
