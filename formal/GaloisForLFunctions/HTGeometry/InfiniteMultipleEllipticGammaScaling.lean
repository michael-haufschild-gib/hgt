import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaCollapse

/-!
# The two-coordinate scaling boundary

A moving coordinate and the collapsing forward coordinate multiply to the nome product, which tends
to zero.  Hence their limits multiply to zero: the two axes of the scaling boundary cannot both be
nonzero, and at least one of the two halves of every finite section collapses to one.

The collapse statement holds along an arbitrary filter and at moving points, because the uniform
smallness estimate for the finite sections is uniform in the nome set as well as in the coordinate.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

/-- **Moving-point collapse.**  Whenever the coordinate tends to zero, the finite sections tend to
one — along any filter, with no uniformity extracted from the exhaustion theorem. -/
theorem tendsto_finiteNomeSection_one_of_tendsto_zero {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    {l : Filter (Finset ι)} {t : Finset ι → ℂ} (ht : Tendsto t l (𝓝 0)) :
    Tendsto (fun S => finiteNomeSection g p S (t S)) l (𝓝 1) := by
  have hn0 : Tendsto (fun S => ‖t S‖) l (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mp ht
  have hmaj : Tendsto (fun S =>
      Real.exp (Real.exp g * ‖t S‖ ^ (g + 1) * occupationMassPow g p) - 1) l (𝓝 0) := by
    have hcomp : Tendsto (fun S =>
        Real.exp g * ‖t S‖ ^ (g + 1) * occupationMassPow g p) l (𝓝 0) := by
      have h := (hn0.pow (g + 1)).const_mul (Real.exp g)
      simpa using h.mul_const (occupationMassPow g p)
    have h := (Real.continuous_exp.tendsto 0).comp hcomp
    simpa using h.sub_const 1
  have hev : ∀ᶠ S in l, ‖t S‖ ≤ 1 := by
    have hb := hn0.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hb] with S hS
    exact hS
  have hkey : Tendsto (fun S => finiteNomeSection g p S (t S) - 1) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun S => norm_nonneg _) ?_ hmaj
    filter_upwards [hev] with S hS
    exact norm_finiteNomeSection_sub_one_le g p hp_lt hsum S hS
  simpa using hkey.add_const 1

/-- **The scaling boundary.**  A moving coordinate and its forward partner multiply to the nome
product, so their limits multiply to zero: no finite two-coordinate scaling keeps both axes away
from the origin. -/
theorem scalingBoundary_mul_eq_zero {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    {xS : Finset ι → ℂ} (hxS : ∀ S, xS S ≠ 0) {x y : ℂ}
    (hx : Tendsto xS atTop (𝓝 x))
    (hy : Tendsto (fun S => (∏ a ∈ S, p a) / xS S) atTop (𝓝 y)) :
    x * y = 0 := by
  have hQ := tendsto_nomeProduct_atTop_zero g p hp_lt hsum
  have hprod : Tendsto (fun S : Finset ι => xS S * ((∏ a ∈ S, p a) / xS S)) atTop
      (𝓝 (x * y)) := hx.mul hy
  have heq : ∀ S : Finset ι, xS S * ((∏ a ∈ S, p a) / xS S) = ∏ a ∈ S, p a := by
    intro S
    have h := hxS S
    field_simp
  rw [tendsto_congr heq] at hprod
  exact tendsto_nhds_unique hprod hQ

/-- **At most one gamma half survives.**  Whatever finite two-coordinate scaling is chosen, one of
the two halves of the finite sections collapses to one. -/
theorem scalingBoundary_half_collapses {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    {xS : Finset ι → ℂ} (hxS : ∀ S, xS S ≠ 0) {x y : ℂ}
    (hx : Tendsto xS atTop (𝓝 x))
    (hy : Tendsto (fun S => (∏ a ∈ S, p a) / xS S) atTop (𝓝 y)) :
    Tendsto (fun S => finiteNomeSection g p S (xS S)) atTop (𝓝 1) ∨
      Tendsto (fun S => finiteNomeSection g p S ((∏ a ∈ S, p a) / xS S)) atTop (𝓝 1) := by
  rcases mul_eq_zero.mp (scalingBoundary_mul_eq_zero g p hp_lt hsum hxS hx hy) with hx0 | hy0
  · left
    exact tendsto_finiteNomeSection_one_of_tendsto_zero g p hp_lt hsum (hx0 ▸ hx)
  · right
    exact tendsto_finiteNomeSection_one_of_tendsto_zero g p hp_lt hsum (hy0 ▸ hy)

/-- The forward collapse of the fixed-coordinate case is the constant instance of the moving one. -/
theorem tendsto_forwardNomeFactor_one' {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) (x : ℂ) :
    Tendsto (fun S : Finset ι => forwardNomeFactor g p S x) atTop (𝓝 1) := by
  refine tendsto_finiteNomeSection_one_of_tendsto_zero g p hp_lt hsum ?_
  simpa using (tendsto_nomeProduct_atTop_zero g p hp_lt hsum).div_const x

end HTGeometry
