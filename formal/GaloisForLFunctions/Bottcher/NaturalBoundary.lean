/-
# Böttcher tower — the natural-boundary engine (connected case)

The Julia set `J_c = ∂K_c` is a natural boundary of the inverse Böttcher coordinate `φ_c`: it does
not continue analytically across any `z₀ ∈ J_c`. This file packages the *harmonic* half of that
obstruction, isolating the single dynamical input.

If `φ_c` continued across `z₀ ∈ J_c` to a nonvanishing analytic `g` on a ball `B = ball z₀ r`, then
`u = log‖g‖` is harmonic on `B`, equals the Green's function `G_c ≥ 0` on the basin side (where
`‖φ_c‖ = exp G_c ≥ 1`), and `u(z₀) = 0` (since `‖φ_c‖ → 1` at `J_c`). The **minimum principle**
(`harmonic_eqOn_zero_of_nonneg`) then forces `u ≡ 0` on `B` — i.e. `‖g‖ ≡ 1` — contradicting `‖g‖ > 1`
on the (nonempty) basin part of `B`. The whole argument needs `‖g‖ ≥ 1` on **all** of `B`: on the
basin side this is `G_c ≥ 0`, but on the `K_c` side it is the genuine dynamical content (a hypothetical
continuation maps the `K_c` side *inside* the unit disk only if the local picture is smooth, which the
nonexceptional hypothesis `c ∉ {0,-2}` forbids). That `‖g‖ ≥ 1` fact is the lone remaining input,
carried here as a hypothesis.

New file (hRigid connected lane); consumes `HarmonicMinPrinciple`.
-/
import GaloisForLFunctions.Bottcher.HarmonicMinPrinciple

open Complex Metric Topology Set InnerProductSpace

/-- **Natural-boundary engine (harmonic half).** A nonvanishing analytic `g` on a ball `B = ball z₀ r`
with `‖g‖ ≥ 1` throughout, `‖g z₀‖ = 1`, and `‖g‖ > 1` somewhere on `B`, is impossible. Instantiated
with `g =` the hypothetical analytic continuation of `φ_c` across `z₀ ∈ J_c`, this is the natural
boundary: `‖g z₀‖ = 1` because `‖φ_c‖ → 1` at `J_c`, `‖g‖ > 1` on the basin side (`G_c > 0`), and the
remaining `‖g‖ ≥ 1` everywhere is the dynamical input. The proof: `u = log‖g‖` is harmonic, `≥ 0`,
vanishes at the interior point `z₀`, so the minimum principle forces `u ≡ 0` (`‖g‖ ≡ 1`),
contradicting `‖g‖ > 1` somewhere. -/
theorem no_unit_min_of_analytic {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hgan : AnalyticOnNhd ℂ g (ball z₀ r))
    (hgne : ∀ z ∈ ball z₀ r, g z ≠ 0)
    (hge1 : ∀ z ∈ ball z₀ r, 1 ≤ ‖g z‖)
    (hz₀1 : ‖g z₀‖ = 1)
    (hbasin : ∃ z ∈ ball z₀ r, 1 < ‖g z‖) :
    False := by
  set u : ℂ → ℝ := fun z => Real.log ‖g z‖ with hu
  have hz0mem : z₀ ∈ ball z₀ r := mem_ball_self hr
  -- u is harmonic on the ball (log-modulus of a nonvanishing analytic function)
  have huharm : HarmonicOnNhd u (ball z₀ r) :=
    fun z hz => (hgan z hz).harmonicAt_log_norm (hgne z hz)
  -- u ≥ 0 (since ‖g‖ ≥ 1)
  have hunn : ∀ z ∈ ball z₀ r, 0 ≤ u z := fun z hz => Real.log_nonneg (hge1 z hz)
  -- u z₀ = 0 (since ‖g z₀‖ = 1)
  have hu0 : u z₀ = 0 := by rw [hu]; simp only; rw [hz₀1, Real.log_one]
  -- minimum principle: u ≡ 0 on the (preconnected) ball
  have hzero : EqOn u 0 (ball z₀ r) :=
    harmonic_eqOn_zero_of_nonneg isOpen_ball (convex_ball z₀ r).isPreconnected huharm hunn
      hz0mem hu0
  -- contradiction with ‖g‖ > 1 somewhere
  obtain ⟨z, hz, hz1⟩ := hbasin
  have : u z = 0 := hzero hz
  rw [hu] at this
  simp only at this
  have hpos : 0 < Real.log ‖g z‖ := Real.log_pos hz1
  linarith
