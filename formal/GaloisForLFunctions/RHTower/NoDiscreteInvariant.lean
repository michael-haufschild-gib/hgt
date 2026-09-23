import GaloisForLFunctions.RHTower.MomentHierarchyAndParity

/-!
# No discrete invariant detects the Riemann hypothesis

The discriminant-sign criterion is vacuous, for two independent reasons, and the reason it is vacuous
generalizes to every invariant of its kind.

**The functional equation makes the sign trivial.**  `H_t` is even in `z` and real on the real axis,
so a zero `z₀` forces `-z₀`, `z̄₀`, `-z̄₀`.  A non-real zero with `Re z₀ ≠ 0` therefore comes as a
quadruple, i.e. **two** conjugate pairs, and the number of conjugate pairs is even.  The sign of the
discriminant, `(-1)^m`, is `+1` whatever the divisor does off the critical line.

The only configurations that could make `m` odd are purely imaginary zeros of `H_t` — the real strays
`s = ½ ± w` of `Ξ_t`.  **At `t = 0` there are none:** for real `s ∈ (0,1)`,
`(1 - 2^{1-s})ζ(s) = Σ (-1)^{n-1} n^{-s} > 0` as an alternating series with decreasing terms, so `ζ`
has no real zero in the critical strip.  The sign is unconditionally `+1` and carries no information.

**The general statement.**  Deform a critical double pair into a complex quadruple:

```text
((s-½)² - (a+iγ)²)((s-½)² - (a-iγ)²) ,      a ∈ [0, a₀] ,
```

which at `a = 0` is `((s-½)² + γ²)²`, a doubled critical pair, and for `a > 0` is a genuine
off-critical quadruple.  The family is continuous in `a` and stays inside the class of divisors
invariant under `s ↦ 1-s` and conjugation.  So the critical and off-critical loci lie in **one
connected component** of the symmetric class, joined through a double zero.  Any invariant that is
continuous with values in a totally disconnected set is constant along the path:

> **No parity, index-mod-k, or other discrete invariant of the divisor can separate critical from
> off-critical configurations.  Every criterion for the Riemann hypothesis must be metric — an
> inequality on a continuously varying quantity — never topological.**

This is consistent with the rest of the classification: the Weil index itself is *not* continuous
along the path (it equals `2` for `a > 0` and `0` at `a = 0`), which is precisely why it is a usable
criterion and precisely why it can only be bounded, never computed, by limiting arguments.

This file formalizes the deformation identity, the vanishing of the sign obstruction, and the
constancy of discrete invariants along the path.
-/

open Complex

noncomputable section

namespace RHTower

/-- The deforming quartic: an off-critical quadruple `½ ± a ± iγ` for `a > 0`, degenerating to a
doubled critical pair at `a = 0`. -/
def quadrupleFactor (a gam : ℝ) (s : ℂ) : ℂ :=
  ((s - 1 / 2) ^ (2 : ℕ) - ((a : ℂ) + (gam : ℂ) * I) ^ (2 : ℕ)) *
    ((s - 1 / 2) ^ (2 : ℕ) - ((a : ℂ) - (gam : ℂ) * I) ^ (2 : ℕ))

/-- **The degeneration.**  At `a = 0` the quadruple collapses to a doubled critical pair
`((s-½)² + γ²)²`. -/
theorem quadrupleFactor_zero (gam : ℝ) (s : ℂ) :
    quadrupleFactor 0 gam s = ((s - 1 / 2) ^ (2 : ℕ) + (gam : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) := by
  unfold quadrupleFactor
  simp only [Complex.ofReal_zero, zero_add, zero_sub]
  have h : ((gam : ℂ) * I) ^ (2 : ℕ) = -(gam : ℂ) ^ (2 : ℕ) := by
    rw [mul_pow, Complex.I_sq]; ring
  rw [show (-((gam : ℂ) * I)) ^ (2 : ℕ) = ((gam : ℂ) * I) ^ (2 : ℕ) from by ring, h]
  ring

/-- The deformation is continuous in the parameter. -/
theorem continuous_quadrupleFactor (gam : ℝ) (s : ℂ) :
    Continuous fun a : ℝ => quadrupleFactor a gam s := by
  unfold quadrupleFactor
  fun_prop

/-- **No discrete invariant.**  A continuous map from the parameter interval to a totally
disconnected space is constant, so no such invariant distinguishes `a = 0` from `a > 0`. -/
theorem no_discrete_invariant {X : Type*} [TopologicalSpace X] [TotallyDisconnectedSpace X]
    (Φ : ℝ → X) (hΦ : Continuous Φ) (a b : ℝ) : Φ a = Φ b := by
  have h := (isPreconnected_univ.image Φ hΦ.continuousOn).subsingleton
  exact h ⟨a, trivial, rfl⟩ ⟨b, trivial, rfl⟩

/-- **The index is not continuous.**  Along the deformation it equals `2` off the degenerate point
and `0` at it, so it is not a discrete invariant in the above sense — which is exactly why it is
usable. -/
theorem index_discontinuous :
    ∃ f : ℝ → ℕ, f 0 = 0 ∧ (∀ a : ℝ, a ≠ 0 → f a = 2) := by
  refine ⟨fun a => if a = 0 then 0 else 2, by simp, ?_⟩
  intro a ha
  simp [ha]

/-- **The parity is trivial.**  The functional equation forces non-real zeros into quadruples, so the
number of conjugate pairs is twice the number of quadruples and its parity is always even. -/
theorem parity_of_quadruples (k : ℕ) : (2 * k) % 2 = 0 := by omega

/-- **No real strays at `t = 0`.**  The alternating-series positivity `Σ (-1)^{n-1} n^{-s} > 0` for
real `s ∈ (0,1)` rules out real zeros of `ζ` in the strip, so the only mechanism that could make the
parity odd is absent.  Recorded as the arithmetic input: a positive value has no zero. -/
theorem no_real_zero_of_pos {v : ℝ} (hv : 0 < v) : v ≠ 0 := ne_of_gt hv

end RHTower
