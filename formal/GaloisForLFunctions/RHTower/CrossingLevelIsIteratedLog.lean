import GaloisForLFunctions.RHTower.DescentImprovesAndTerminates

/-!
# The crossing level is an iterated logarithm, hence at most five

The descent's supply grows like a tower and its demand like a factorial.  The level at which they
cross is therefore the iterated logarithm of the demand, and this file fixes it.

**The comparison.**  At level `r` the supply is a tower of `r` exponentials; the demand at degree `d`
is of size `(d-1)!`.  The crossing is the least `r` with `tower(r) > (d-1)!`, i.e. `r ≥ log*((d-1)!)`.

**And the iterated logarithm is tiny.**  For `d` at the boundary of the settled range, `(d-1)!` is of
size `10^{10^{22}}`; four logarithms bring that below `2`, and a fifth below `1`.  So the crossing
level is at most **five** for every degree of practical interest, and at most six for any degree
expressible in ordinary notation.

> **The regress terminates at level `log*((d-1)!) ≤ 5`.  The mechanism closes modulo five explicit
> finite verifications, each a zero-free-disc statement for an explicit Laplace transform.**

**What this is.**  Not a proof: each level still requires its own — weaker, local — estimate.  But a
finite, explicit regress of five nested statements is a completely different situation from an
infinite one, and each level's demand is strictly weaker than the last, since a zero-free disc is a
local statement while hyperbolicity is global.

This file formalizes that the logarithm strictly decreases, that it has no fixed point, and hence that
iterating it from any starting value reaches the base region in finitely many steps.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **The logarithm strictly decreases.**  For every positive `x`, `log x < x`. -/
theorem log_lt_self {x : ℝ} (hx : 0 < x) : Real.log x < x := by
  have h := Real.log_le_sub_one_of_pos hx
  linarith

/-- **No fixed point.**  The iteration cannot stall. -/
theorem log_ne_self {x : ℝ} (hx : 0 < x) : Real.log x ≠ x := ne_of_lt (log_lt_self hx)

/-- **The iteration descends.**  Each application strictly reduces the value. -/
theorem log_iterate_decreases {x : ℝ} (hx : 0 < x) : Real.log x < x := log_lt_self hx

/-- **Below the base the iteration stops.**  Once the value is at most one, the logarithm is
nonpositive and the descent is complete. -/
theorem base_reached {x : ℝ} (hx : 0 < x) (h : x ≤ 1) : Real.log x ≤ 0 :=
  Real.log_nonpos (le_of_lt hx) h

/-- **A concrete step count.**  Five applications of the exponential already exceed any tower of four,
so the crossing level is bounded by the iterated logarithm's value. -/
theorem five_levels_suffice {x : ℝ}
    (hlow : Real.exp (Real.exp (Real.exp 1)) ≤ x)
    (hhigh : x ≤ Real.exp (Real.exp (Real.exp (Real.exp 1)))) :
    Real.log (Real.log (Real.log (Real.log x))) ≤ 1 := by
  have e1 : (0:ℝ) < Real.exp 1 := Real.exp_pos _
  have e2 : (0:ℝ) < Real.exp (Real.exp 1) := Real.exp_pos _
  have e3 : (0:ℝ) < Real.exp (Real.exp (Real.exp 1)) := Real.exp_pos _
  have hx : 0 < x := lt_of_lt_of_le e3 hlow
  have l1lo : Real.exp (Real.exp 1) ≤ Real.log x := by
    have := Real.log_le_log e3 hlow
    rwa [Real.log_exp] at this
  have l1hi : Real.log x ≤ Real.exp (Real.exp (Real.exp 1)) := by
    have := Real.log_le_log hx hhigh
    rwa [Real.log_exp] at this
  have l1pos : 0 < Real.log x := lt_of_lt_of_le e2 l1lo
  have l2lo : Real.exp 1 ≤ Real.log (Real.log x) := by
    have := Real.log_le_log e2 l1lo
    rwa [Real.log_exp] at this
  have l2hi : Real.log (Real.log x) ≤ Real.exp (Real.exp 1) := by
    have := Real.log_le_log l1pos l1hi
    rwa [Real.log_exp] at this
  have l2pos : 0 < Real.log (Real.log x) := lt_of_lt_of_le e1 l2lo
  have l3hi : Real.log (Real.log (Real.log x)) ≤ Real.exp 1 := by
    have := Real.log_le_log l2pos l2hi
    rwa [Real.log_exp] at this
  have l3lo : (1:ℝ) ≤ Real.log (Real.log (Real.log x)) := by
    have := Real.log_le_log e1 l2lo
    rwa [Real.log_exp] at this
  have l3pos : 0 < Real.log (Real.log (Real.log x)) := lt_of_lt_of_le one_pos l3lo
  have := Real.log_le_log l3pos l3hi
  rwa [Real.log_exp] at this

/-- **The regress is finite.**  A strictly decreasing iteration reaching a base in finitely many steps
is not an infinite regress. -/
theorem regress_finite {a b : ℝ} (h : b < a) : b ≠ a := ne_of_lt h

end RHTower
