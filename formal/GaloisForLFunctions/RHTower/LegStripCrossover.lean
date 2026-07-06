/-
# The crossover `G` derived, and the marginal locus as a curve

The edge-law family `ρ(κ,a) = 2κ√a` (`rhoFamily`) has, at the harmonic carrier `κ(c) = c/π²`, the single
physical value `ρ(κ(2), π²/16) = 1/π`. Two constructions turn that point into genuine one-parameter
objects.

* `crossover_derivation` : along the finite-size curve `c(d) = 2 − ξ/√d` (so `ξ = (2−c)√d` fixed), the
  off-marginal edge margin `κ(c)·[(π²/8)(c−2) + (π/2)/√d]` scaled by `√d` converges to
  `crossoverG ξ = 1/π − ξ/4`. This **derives** the crossover slope `−1/4` from the local factor `κ` and
  the curvature `Φ'(2) = −π²/8`, joining the two boundary constants `G(0) = 1/π` and `G'(ξ) = −1/4`.
* `rhoOfCarrier_marginal_curve` : the deformed carrier `a(c) = π²/(4c²)` keeps `ρ(κ(c), a(c)) = 1/π`
  marginal for **every** `c > 0`. So the marginal locus of the `ρ`-skeleton is a curve, and the physical
  point `(κ(2), π²/16)` is one point of a one-parameter family of marginal carriers.
-/
import GaloisForLFunctions.RHTower.LegStripEdgeFamily
open Real Filter Topology
noncomputable section
namespace RHTower

/-- **The crossover slope, derived from `κ` and `Φ'(2)`.** Along `c(d) = 2 − ξ/√d`, the off-marginal
edge margin scaled by `√d` converges to `crossoverG ξ = 1/π − ξ/4`. -/
theorem crossover_derivation (ξ : ℝ) :
    Tendsto (fun d : ℝ =>
      localFactor (2 - ξ/Real.sqrt d) *
        ((π^2/8)*((2 - ξ/Real.sqrt d) - 2) + (π/2)/Real.sqrt d) * Real.sqrt d)
      atTop (𝓝 (crossoverG ξ)) := by
  have hsqrt : Tendsto (fun d : ℝ => 1/Real.sqrt d) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_sqrt_atTop
  have hmain : Tendsto (fun d : ℝ => crossoverG ξ + (ξ^2/8 - ξ/(2*π))*(1/Real.sqrt d)) atTop
      (𝓝 (crossoverG ξ + (ξ^2/8 - ξ/(2*π))*0)) :=
    Tendsto.const_add _ (Tendsto.const_mul _ hsqrt)
  rw [mul_zero, add_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hs : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd
  rw [localFactor, crossoverG]
  field_simp
  ring

/-- The deformed carrier `a(c) = π²/(4c²)` whose locus is the marginal curve `ρ = 1/π`. -/
def marginalShell (c : ℝ) : ℝ := π^2/(4*c^2)

/-- **The marginal locus is a curve.** The deformed carrier `a(c) = π²/(4c²)` is marginal
`ρ(κ(c), a(c)) = 1/π` for every `c > 0` — a one-parameter family of marginal carriers. -/
theorem rhoOfCarrier_marginal_curve {c : ℝ} (hc : 0 < c) :
    rhoOfCarrier c (marginalShell c) = 1/π := by
  rw [rhoOfCarrier_eq, marginalShell,
    show (π^2/(4*c^2) : ℝ) = (π/(2*c))^2 by ring, Real.sqrt_sq (by positivity)]
  field_simp

/-- The physical shell coefficient `π²/16` is the marginal carrier at `c = 2`. -/
theorem marginalShell_two : marginalShell 2 = π^2/16 := by rw [marginalShell]; ring

/-- The marginal locus in the abstract `(κ, a)` skeleton: `a = 1/(4π²κ²)` gives `ρ(κ,a) = 1/π`. -/
theorem rhoFamily_marginal_locus {κ : ℝ} (hκ : 0 < κ) :
    rhoFamily κ (1/(4*π^2*κ^2)) = 1/π := by
  rw [rhoFamily, show (1/(4*π^2*κ^2) : ℝ) = (1/(2*π*κ))^2 by ring, Real.sqrt_sq (by positivity)]
  field_simp

end RHTower
