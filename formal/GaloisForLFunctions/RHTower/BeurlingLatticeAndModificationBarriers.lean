import Mathlib

/-!
# Two barriers: lattice systems, and modifications that cannot create zeros

Two elementary obstructions to building a Beurling number system whose integers are
better-than-square-root regular and whose zeta has a certified zero off the critical line.

**Lattice barrier.**  If every generalized integer is a power of a fixed `q > 1`, the counting
function `N` is constant on each interval `[q^n, q^{n+1})` while `a x` grows by the factor `q`
across it.  So `N(x) - a x` is bounded below by a fixed proportion of `x` somewhere in every such
interval, for every candidate density `a > 0`: a lattice system admits **no power saving at all**.
This applies to the stated fixed geometric lattice; it does not classify all self-similar or
fractal constructions.

**Modification barrier.**  If a system is modified by inserting, deleting or rescaling a family of
generalized primes whose reciprocal `σ`-sum converges for `σ > γ`, the zeta function is multiplied by
an absolutely convergent Euler product each of whose factors is nonzero on `Re s > 0`.  Such a
product is nonzero, so the modification is analytic and **zero-free** on `Re s > max(γ, 0)`: it
cannot create a zeta zero that the base system did not already have.

Zeros strictly inside this convergence region are inherited from the base.  Boundary zeros and
continuations beyond the region are not covered.  Neither result proves a general inequality
between the modification's counting exponent and the integer-counting error exponent.
-/

open Set Filter Topology

namespace RHTower.BeurlingBarriers

/-! ## The lattice barrier -/

/-- **A lattice system admits no power saving.**  If `N` is constant on `[q^n, q^{n+1})` then for
every density `a > 0` there is a point of that interval at which `|N x - a x|` is at least the fixed
proportion `a (q-1) / (4 q)` of `x`.  Since the intervals exhaust `[1, ∞)`, `N(x) - a x` is not
`o(x)`, so no exponent `β < 1` is admissible. -/
theorem lattice_no_power_saving {q a : ℝ} (hq : 1 < q) (ha : 0 < a) (N : ℝ → ℝ) (n : ℕ)
    (hconst : ∀ x, q ^ n ≤ x → x < q ^ (n + 1) → N x = N (q ^ n)) :
    ∃ x, q ^ n ≤ x ∧ x < q ^ (n + 1) ∧ a * (q - 1) / (4 * q) * x ≤ |N x - a * x| := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hqn : (0 : ℝ) < q ^ n := by positivity
  set M : ℝ := N (q ^ n) with hM
  -- the two probe points
  set x₁ : ℝ := q ^ n with hx₁
  set x₂ : ℝ := (q ^ n + q ^ (n + 1)) / 2 with hx₂
  have hpow : q ^ (n + 1) = q ^ n * q := by ring
  have hlt : x₁ < x₂ := by
    rw [hx₁, hx₂, hpow]
    nlinarith
  have hx₂lt : x₂ < q ^ (n + 1) := by
    rw [hx₂, hpow]
    nlinarith
  have hx₁le : q ^ n ≤ x₁ := le_rfl
  have hx₁lt : x₁ < q ^ (n + 1) := by rw [hx₁, hpow]; nlinarith
  have hx₂ge : q ^ n ≤ x₂ := le_of_lt hlt
  have hN₁ : N x₁ = M := hconst x₁ hx₁le hx₁lt
  have hN₂ : N x₂ = M := hconst x₂ hx₂ge hx₂lt
  -- the gap between the two linear values
  have hgap : a * (x₂ - x₁) = a * (q ^ n * (q - 1)) / 2 := by
    rw [hx₁, hx₂, hpow]
    ring
  have hsum : a * (x₂ - x₁) ≤ |N x₁ - a * x₁| + |N x₂ - a * x₂| := by
    have h1 : a * (x₂ - x₁) = (M - a * x₁) - (M - a * x₂) := by ring
    calc a * (x₂ - x₁) = (M - a * x₁) - (M - a * x₂) := h1
      _ ≤ |(M - a * x₁) - (M - a * x₂)| := le_abs_self _
      _ ≤ |M - a * x₁| + |M - a * x₂| := abs_sub _ _
      _ = |N x₁ - a * x₁| + |N x₂ - a * x₂| := by rw [hN₁, hN₂]
  -- one of the two probes carries half the gap
  have hhalf : a * (q ^ n * (q - 1)) / 4 ≤ |N x₁ - a * x₁| ∨
      a * (q ^ n * (q - 1)) / 4 ≤ |N x₂ - a * x₂| := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [hgap] at hsum
    linarith
  -- convert `q ^ n` to a proportion of the probe point
  have hbound : ∀ x : ℝ, q ^ n ≤ x → x < q ^ (n + 1) →
      a * (q - 1) / (4 * q) * x ≤ a * (q ^ n * (q - 1)) / 4 := by
    intro x _ hxlt
    rw [hpow] at hxlt
    have hq1 : 0 < q - 1 := by linarith
    have : a * (q - 1) / (4 * q) * x ≤ a * (q - 1) / (4 * q) * (q ^ n * q) := by
      apply mul_le_mul_of_nonneg_left hxlt.le
      positivity
    calc a * (q - 1) / (4 * q) * x ≤ a * (q - 1) / (4 * q) * (q ^ n * q) := this
      _ = a * (q ^ n * (q - 1)) / 4 := by field_simp
  rcases hhalf with h | h
  · exact ⟨x₁, hx₁le, hx₁lt, le_trans (hbound x₁ hx₁le hx₁lt) h⟩
  · exact ⟨x₂, hx₂ge, hx₂lt, le_trans (hbound x₂ hx₂ge hx₂lt) h⟩

/-! ## The modification barrier -/

/-- The Euler factor of a modifying family is nonvanishing: an absolutely convergent product of
factors `1 - z i` with `‖z i‖ < 1` is the exponential of a convergent sum of logarithms. -/
theorem tprod_one_sub_ne_zero {ι : Type*} (z : ι → ℂ)
    (hsum : Summable z) (hlt : ∀ i, ‖z i‖ < 1) :
    ∏' i, (1 - z i) ≠ 0 := by
  have hne : ∀ i, (1 - z i) ≠ 0 := by
    intro i h
    have hz : z i = 1 := by
      have := sub_eq_zero.mp h
      exact this.symm
    have := hlt i
    rw [hz] at this
    simp at this
  have hlog : Summable fun i => Complex.log (1 - z i) := by
    have h := Complex.summable_log_one_add_of_summable hsum.neg
    simpa [sub_eq_add_neg] using h
  rw [← Complex.cexp_tsum_eq_tprod hne hlog]
  exact Complex.exp_ne_zero _

/-- **A modification cannot create a zero.**  If the modifying generalized primes `q i` exceed `1`
and satisfy `∑ (q i)^{-σ} < ∞`, then the Euler factor `∏ (1 - (q i)^{-s})` is nonzero at every `s`
with `Re s ≥ σ`.  Hence inserting, deleting or rescaling such a family multiplies the zeta function
by an analytic, zero-free factor: in that half plane the modified system's zeros are exactly the base
system's zeros.  This nonvanishing conclusion applies only in the stated convergence region. -/
theorem modification_factor_ne_zero {ι : Type*} (q : ι → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hq : ∀ i, 1 < q i) (hsum : Summable fun i => (q i) ^ (-σ)) {s : ℂ} (hs : σ ≤ s.re) :
    ∏' i, (1 - (q i : ℂ) ^ (-s)) ≠ 0 := by
  have hqpos : ∀ i, (0 : ℝ) < q i := fun i => lt_trans one_pos (hq i)
  have hnorm : ∀ i, ‖((q i : ℂ) ^ (-s))‖ = (q i) ^ (-s.re) := by
    intro i
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hqpos i)]
    simp
  have hdom : ∀ i, ‖((q i : ℂ) ^ (-s))‖ ≤ (q i) ^ (-σ) := by
    intro i
    rw [hnorm]
    exact Real.rpow_le_rpow_of_exponent_le (hq i).le (by linarith)
  refine tprod_one_sub_ne_zero _ ?_ ?_
  · refine Summable.of_norm ?_
    refine hsum.of_nonneg_of_le (fun i => norm_nonneg _) hdom
  · intro i
    rw [hnorm]
    have hlt : (q i) ^ (-s.re) < (q i) ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (hq i) (by linarith)
    simpa using hlt

end RHTower.BeurlingBarriers
