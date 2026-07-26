import GaloisForLFunctions.RHTower.CoverageLatticeHasACorner

/-!
# The zero-shift column carries the whole equivalence, and no shift theorem touches it

The Jensen polynomial of degree `d` and shift `n` built from a sequence `γ` is
`J^{d,n}(X) = Σ_j C(d,j) γ(n+j) X^j`.  This file isolates the analytic fact behind the classical
Jensen–Pólya statement and draws the consequence for the coverage lattice.

**The rescaling.**  For fixed `j`,

```text
C(d,j) / d^j  =  d(d-1)···(d-j+1) / (j! · d^j)  ⟶  1/j!      as `d → ∞`,
```

and the same quantity is bounded by `1/j!` for **every** `d`.  So `J^{d,0}(X/d)` has coefficients
dominated by those of

```text
F(X) = Σ_j γ(j) X^j / j! ,
```

and converging to them termwise — hence locally uniform convergence when `F` is entire.

**The classical consequence.**  By Hurwitz's theorem, if every `J^{d,0}` is hyperbolic then the limit
`F` has only real zeros; conversely a Laguerre–Pólya `F` makes every Jensen polynomial hyperbolic.
For the Riemann sequence this is Jensen's criterion: **the shift-zero column alone is equivalent to
the hypothesis.**

**The consequence for the lattice.**  The unconditional theorems live in `n ≥ N(d)`.  Their
intersection with the shift-zero column is exactly `{d : N(d) = 0}`, i.e. nothing beyond where the
threshold is already vacuous.

> **The subfamily that is equivalent to the hypothesis is precisely the one the shift theorems never
> reach.  Every large-shift result is, with respect to the equivalence, contained in the direction
> that was already free.**

This file formalizes the uniform domination `j! · C(d,j) ≤ d^j`, the termwise limit `C(d,j)/d^j →
1/j!`, and the disjointness of the shift-zero column from the unconditional region.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **Uniform domination.**  `j! · C(d,j) ≤ d^j`, since the falling factorial is at most `d^j`. -/
theorem factorial_mul_choose_le_pow (d j : ℕ) : j.factorial * d.choose j ≤ d ^ j := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow d j

/-- The real form: the rescaled binomial coefficient never exceeds `1/j!`. -/
theorem choose_div_pow_le (d j : ℕ) (hd : 0 < d) :
    ((d.choose j : ℝ)) / (d : ℝ) ^ j ≤ 1 / (j.factorial : ℝ) := by
  have hdpos : (0 : ℝ) < (d : ℝ) ^ j := by positivity
  have hfac : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast j.factorial_pos
  rw [div_le_div_iff₀ hdpos hfac, one_mul]
  have := factorial_mul_choose_le_pow d j
  have : ((j.factorial * d.choose j : ℕ) : ℝ) ≤ ((d ^ j : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at this
  linarith

/-- **The shifted denominator tends to one.**  `(d - j)/d → 1`. -/
theorem sub_div_tendsto_one (j : ℕ) :
    Tendsto (fun d : ℕ => ((d - j : ℕ) : ℝ) / (d : ℝ)) atTop (𝓝 1) := by
  have hcast : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun d : ℕ => (j : ℝ) / (d : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcast
  have hlim : Tendsto (fun d : ℕ => 1 - (j : ℝ) / (d : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hz
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (max j 1)] with d hd
  have hjd : j ≤ d := le_trans (le_max_left j 1) hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : 1 ≤ d := le_trans (le_max_right j 1) hd
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  rw [Nat.cast_sub hjd]
  field_simp

/-- **The termwise limit.**  For fixed `j`, the falling factorial over `d^j` tends to one. -/
theorem descFactorial_div_pow_tendsto_one :
    ∀ j : ℕ, Tendsto (fun d : ℕ => ((d.descFactorial j : ℝ)) / (d : ℝ) ^ j) atTop (𝓝 1)
  | 0 => by simp
  | j + 1 => by
      have ih := descFactorial_div_pow_tendsto_one j
      have hstep := sub_div_tendsto_one j
      have hprod : Tendsto
          (fun d : ℕ => (((d - j : ℕ) : ℝ) / (d : ℝ)) * ((d.descFactorial j : ℝ) / (d : ℝ) ^ j))
          atTop (𝓝 1) := by simpa using hstep.mul ih
      refine hprod.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with d hd
      have hdne : ((d : ℝ)) ≠ 0 := by
        have : (0 : ℕ) < d := hd
        exact_mod_cast Nat.pos_iff_ne_zero.mp this
      rw [Nat.descFactorial_succ]
      push_cast
      field_simp
      ring

/-- **The rescaled Jensen coefficient converges to the exponential-generating coefficient.** -/
theorem choose_div_pow_tendsto (j : ℕ) :
    Tendsto (fun d : ℕ => ((d.choose j : ℝ)) / (d : ℝ) ^ j) atTop
      (𝓝 (1 / (j.factorial : ℝ))) := by
  have hfac : (j.factorial : ℝ) ≠ 0 := by
    exact_mod_cast j.factorial_ne_zero
  have h := (descFactorial_div_pow_tendsto_one j).div_const (j.factorial : ℝ)
  refine h.congr ?_
  intro d
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

/-- **The shift-zero column meets the unconditional region only where the threshold is vacuous.** -/
theorem zeroShift_meets_regionA_iff {N : ℕ → ℕ} {d : ℕ} :
    regionA N d 0 ↔ N d = 0 := by
  constructor
  · intro h; exact Nat.le_zero.mp h
  · intro h; simp [regionA, h]

/-- Hence a positive threshold at some degree leaves that degree's shift-zero instance untouched by
every unconditional shift theorem. -/
theorem zeroShift_untouched {N : ℕ → ℕ} {d : ℕ} (hN : 0 < N d) : ¬ regionA N d 0 := by
  intro h
  exact absurd (zeroShift_meets_regionA_iff.mp h) (Nat.ne_of_gt hN)

end RHTower
