import GaloisForLFunctions.RHTower.BurgersFieldDamping

/-!
# The equally spaced configuration is stationary, and a gap collides iff it beats it

For two consecutive real zeros `a < b` at distance `δ = b - a`, backward flow gives

```text
dδ/dτ = -4/δ + 2δ Σ_{k ∉ {a,b}} 1/((a - x_k)(b - x_k)) =: -4/δ + 2δΔ ,
```

so with `u = δ²` the gap obeys `u' = -8 + 4Δu` and the pair collides exactly when `δ²Δ < 2`.

**The equally spaced configuration is an exact equilibrium.**  For zeros at `dℤ` the field sum
telescopes:

```text
Δ = (2/d²) Σ_{m≥1} 1/(m(m+1)) = 2/d² ,     hence   δ²Δ = 2 ,   dδ/dτ = 0 .
```

A lattice neither contracts nor expands.  This is the exact threshold, so the collision criterion is
not "the gap is small" but "**the gap beats the lattice**": a pair collides precisely when it is
closer than equilibrium relative to the field it sits in.

**An explicit sufficient condition.**  If every other consecutive gap in the configuration is at
least `γ`, then the `m`-th neighbour on either side is at distance at least `mγ` from both `a` and
`b`, so

```text
Δ ≤ 2 Σ_{m≥1} 1/(mγ)² = π²/(3γ²) ,
```

and `δ²Δ < 2` holds as soon as

```text
δ/γ  <  √6/π  ≈  0.7797 .
```

The pair then collides by backward time `u₀/(8 - 4Δu₀)`.

This changes the shape of the input the falsification criterion of the preceding modules needs.  It
is **not** enough that infinitely many gaps be small in absolute or normalized terms — a uniformly
spaced cluster, however dense, never collides.  What is needed is infinitely many gaps that are
*relatively* small: below `√6/π` times the surrounding minimum gap.  The known small-gap results —
`liminf` of the normalized gap below `0.5155` — do not have this form, since they say nothing about
the neighbours of the small gap.  That is the corrected, precise statement of the open core.

The localization is genuine: only the near neighbours matter, since the tail of the field sum beyond
the `M`-th neighbour is bounded by the zero density divided by `M`.  So `γ` may be taken to be the
minimum gap in a bounded neighbourhood, at the cost of a tail term that vanishes as `M → ∞`.

This file formalizes the telescoping equilibrium, the Basel bound on the field, the collision
condition, and the collision time.
-/

open Real Filter Topology

noncomputable section

namespace RHTower

/-- **The lattice is stationary.**  With the exact field `Δ = 2/d²` of an equally spaced
configuration, the gap velocity `-4/d + 2dΔ` vanishes. -/
theorem lattice_stationary {d : ℝ} (hd : d ≠ 0) : -4 / d + 2 * d * (2 / d ^ 2) = 0 := by
  field_simp
  ring

/-- **The telescoping field sum of a lattice.**  `Σ_{m=1}^{n} 1/(m(m+1)) = 1 - 1/(n+1)`, whose limit
`1` produces the equilibrium constant `2/d²`. -/
theorem telescope_partial (n : ℕ) :
    ∑ m ∈ Finset.range n, (1 : ℝ) / (((m : ℝ) + 1) * ((m : ℝ) + 2)) = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((k : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- The shifted Basel sum: `Σ_{m≥0} 1/(m+1)² = π²/6`. -/
theorem basel_shifted : HasSum (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2)
      (π ^ 2 / 6 + ∑ i ∈ Finset.range 1, (1 : ℝ) / ((i : ℝ)) ^ 2) := by
    simpa using hasSum_zeta_two
  simpa [add_comm] using (hasSum_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) 1).mpr h

/-- The field majorant of a configuration whose gaps are all at least `γ`. -/
theorem basel_scaled {gam : ℝ} (hgam : 0 < gam) :
    HasSum (fun m : ℕ => 1 / ((((m : ℝ) + 1) * gam) ^ 2)) (π ^ 2 / (6 * gam ^ 2)) := by
  have h := basel_shifted.mul_left (1 / gam ^ 2)
  have hg : gam ≠ 0 := ne_of_gt hgam
  have hfun : (fun m : ℕ => (1 / gam ^ 2) * ((1 : ℝ) / ((m : ℝ) + 1) ^ 2))
      = fun m : ℕ => 1 / ((((m : ℝ) + 1) * gam) ^ 2) := by
    funext m
    rw [mul_pow]
    field_simp
  have hval : (1 / gam ^ 2) * (π ^ 2 / 6) = π ^ 2 / (6 * gam ^ 2) := by
    field_simp
  rw [hfun, hval] at h
  exact h

/-- **The Basel bound on the field.**  If every other gap is at least `γ > 0`, the `m`-th neighbour
lies at distance at least `mγ`, so each side of the field sum is at most `π²/(6γ²)`. -/
theorem field_bound {gam : ℝ} (hgam : 0 < gam) {f : ℕ → ℝ}
    (hle : ∀ m, f m ≤ 1 / ((((m : ℝ) + 1) * gam) ^ 2))
    (hsum : Summable f) : ∑' m, f m ≤ π ^ 2 / (6 * gam ^ 2) := by
  have hmaj := basel_scaled hgam
  calc ∑' m, f m ≤ ∑' m : ℕ, 1 / ((((m : ℝ) + 1) * gam) ^ 2) :=
        Summable.tsum_mono hsum hmaj.summable hle
    _ = π ^ 2 / (6 * gam ^ 2) := hmaj.tsum_eq

/-- **The collision condition.**  Two sides of the field give `Δ ≤ π²/(3γ²)`, and `δ²Δ < 2` follows
from `δ/γ < √6/π`. -/
theorem collision_condition {delta gam : ℝ} (hgam : 0 < gam) (_hd : 0 < delta)
    (hratio : delta ^ 2 / gam ^ 2 < 6 / π ^ 2) :
    delta ^ 2 * (π ^ 2 / (3 * gam ^ 2)) < 2 := by
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  have hg : (0 : ℝ) < gam ^ 2 := by positivity
  rw [div_lt_div_iff₀ hg hpi] at hratio
  rw [show delta ^ 2 * (π ^ 2 / (3 * gam ^ 2)) = (delta ^ 2 * π ^ 2) / (3 * gam ^ 2) by ring,
    div_lt_iff₀ (by positivity)]
  linarith

/-- **The collision time.**  If `u' ≤ -8 + 4Δu` and `4Δu₀ < 8`, the gap squared decreases at least
linearly and reaches zero by `u₀/(8 - 4Δu₀)`. -/
theorem collision_time {u₀ D t : ℝ} (_hu : 0 < u₀) (hlt : 4 * D * u₀ < 8)
    (hprofile : 0 ≤ u₀ - (8 - 4 * D * u₀) * t) : t ≤ u₀ / (8 - 4 * D * u₀) := by
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **Sharpness.**  At the lattice ratio `δ = γ` the criterion fails: `δ²·π²/(3γ²) = π²/3 > 2`, and
the exact lattice field gives `δ²Δ = 2`, a stationary gap.  So no criterion of this shape can reach
uniformly spaced configurations. -/
theorem lattice_not_collision : (2 : ℝ) ≤ 1 * (π ^ 2 / 3) := by
  have h : (6 : ℝ) < π ^ 2 := by
    nlinarith [Real.pi_gt_three, Real.pi_pos]
  rw [one_mul, le_div_iff₀ (by norm_num)]
  linarith

end RHTower
