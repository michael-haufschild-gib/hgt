import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The leading Taylor coefficient of the friable Möbius expansion

The friable expansion of a multiplicative function is organised by the Taylor coefficients of

`s ↦ s^z 𝓕(1+s) / (1+s)`

at `s = 0`, where `𝓕` is the Dirichlet series and `z` its zeta exponent.  For `f = μ` one has
`𝓕 = ζ⁻¹` and `z = -1`, so the expanded function is

`s⁻¹ ζ(1+s)⁻¹ / (1+s) = ((1+s)·(s ζ(1+s)))⁻¹`,

and the simple pole of `ζ` at `1` makes `s ζ(1+s) → 1`.  Hence the leading coefficient is `a₀ = 1`:
the friable main term for Möbius carries no extra constant.
-/

namespace RHTower

open Filter Topology ArithmeticFunction

/-- **Dirichlet series of Möbius.**  In the half-plane of absolute convergence it is the
reciprocal of the zeta function. -/
private theorem LSeries_moebius_eq_inv_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s = (riemannZeta s)⁻¹ := by
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  field_simp at h ⊢
  linear_combination h

/-- The residue of `ζ` at one, transported to the origin. -/
theorem tendsto_mul_riemannZeta_add_one :
    Tendsto (fun s : ℂ => s * riemannZeta (1 + s)) (𝓝[≠] 0) (𝓝 1) := by
  have hshift : Tendsto (fun s : ℂ => 1 + s) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℂ => 1 + s) (𝓝 (0 : ℂ)) (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_id
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcon
      exact hs (Set.mem_singleton_iff.2 (by linear_combination hcon))
  have hcomp := riemannZeta_residue_one.comp hshift
  refine hcomp.congr ?_
  intro s
  simp only [Function.comp_apply]
  ring_nf

/-- **The leading Taylor coefficient is one.**  With `𝓕 = ζ⁻¹` and zeta exponent `-1`, the expanded
function tends to `1` at the origin. -/
theorem tendsto_mobiusFriableTaylor :
    Tendsto (fun s : ℂ => ((1 + s) * (s * riemannZeta (1 + s)))⁻¹) (𝓝[≠] 0) (𝓝 1) := by
  have h1 : Tendsto (fun s : ℂ => (1 : ℂ) + s) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have : Tendsto (fun s : ℂ => 1 + s) (𝓝 (0 : ℂ)) (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_id
    simpa using this.mono_left nhdsWithin_le_nhds
  have h2 := tendsto_mul_riemannZeta_add_one
  have hmul : Tendsto (fun s : ℂ => (1 + s) * (s * riemannZeta (1 + s))) (𝓝[≠] 0) (𝓝 (1 * 1)) :=
    h1.mul h2
  rw [one_mul] at hmul
  simpa using hmul.inv₀ one_ne_zero

/-- The expanded function is exactly `s^{-1} 𝓕(1+s)/(1+s)` on the half-plane of convergence. -/
theorem mobiusFriableTaylor_eq {s : ℂ} (hs : 0 < s.re) :
    s⁻¹ * LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (1 + s) / (1 + s)
      = ((1 + s) * (s * riemannZeta (1 + s)))⁻¹ := by
  have hre : 1 < (1 + s).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  rw [LSeries_moebius_eq_inv_riemannZeta hre]
  rw [mul_inv, mul_inv]
  ring

end RHTower
