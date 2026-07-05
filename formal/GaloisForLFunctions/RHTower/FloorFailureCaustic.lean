/-
Concrete caustic floor-failure density bound on the deterministic line.

Instantiating the unconditional sharp bound at the block small-ball law `block_smallball_caustic`
(with conditioning `w = 0`): under the caustic geometry — four dominant primes in strict position
with radius, margin, and split windows — the Cesàro upper time density of any `[0,1]`-observable
supported on the vertical floor-failure set `{‖F‖ ≤ t₀}` is at most the explicit four-phase
constant `(2π)⁻⁴·fourPhaseConst`. This exposes the small-ball numeral directly on the `t`-line.
-/
import GaloisForLFunctions.RHTower.FloorFailureUnconditional

open MeasureTheory intervalIntegral Filter Topology Complex Finset
open scoped Classical

namespace RHTower

open Weyl SteinhausModel Sublevel

/-- **Concrete caustic floor-failure density bound.** Under the caustic geometry (four dominant
primes in strict position, radius/margin/split windows), the Cesàro upper time density of any
`[0,1]`-observable supported on the vertical floor-failure set `{‖F‖ ≤ t₀}` is at most the
explicit four-phase small-ball constant `(2π)⁻⁴·fourPhaseConst`, on the deterministic line. -/
theorem floorFailure_timeDensity_le_caustic
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (a : ℕ → ℝ)
    {t₀ σ0 sstar : ℝ} {J : ℕ}
    (p1 p2 p3 p4 : ℕ) (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) (hp3 : p3 ∈ s) (hp4 : p4 ∈ s)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hA : (a p4 : ℂ) ≠ 0) (hB : (a p3 : ℂ) ≠ 0) (hC : (a p2 : ℂ) ≠ 0) (hD : (a p1 : ℂ) ≠ 0)
    (hρB : ‖(a p3 : ℂ)‖ < ‖(a p4 : ℂ)‖) (hr0 : 0 < t₀)
    (hr2 : 2 * t₀ ≤ ‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((‖(a p4 : ℂ)‖ + ‖(a p3 : ℂ)‖) ^ 2 - (‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) ^ 2) / 3)
    (hJ : ((‖(a p4 : ℂ)‖ + ‖(a p3 : ℂ)‖) ^ 2 - (‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) ^ 2) / 3
        < 2 ^ J * σ0)
    (hHσ0 : 2 * (t₀ * (2 * ‖(a p4 : ℂ)‖ + t₀)
        / ((‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) * ‖(a p3 : ℂ)‖))
        ≤ σ0 * causticKappa ‖(a p4 : ℂ)‖ ‖(a p3 : ℂ)‖)
    (hss : 0 < sstar) (hss2 : 2 * sstar ≤ ‖(a p1 : ℂ)‖)
    (fail : ℝ → ℝ) (hfail0 : ∀ τ, 0 ≤ fail τ) (hfle1 : ∀ τ, fail τ ≤ 1)
    (hfsupp : ∀ τ, t₀ < ‖dpoly a s τ‖ → fail τ = 0)
    (hfail_int : ∀ T : ℝ, IntervalIntegrable fail volume 0 T) :
    cesaroUpperDensity fail
      ≤ (ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4
          * Sublevel.fourPhaseConst (a p4 : ℂ) (a p3 : ℂ) (a p2 : ℂ) (a p1 : ℂ)
              t₀ σ0 sstar J).toReal := by
  have hs1 : ∀ n ∈ s, 1 ≤ n := fun n hn => le_of_lt (hs n hn).one_lt
  set B : ENNReal := ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4
      * Sublevel.fourPhaseConst (a p4 : ℂ) (a p3 : ℂ) (a p2 : ℂ) (a p1 : ℂ) t₀ σ0 sstar J with hBdef
  have hBtop : B ≠ ⊤ := by
    rw [hBdef]
    apply ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    unfold Sublevel.fourPhaseConst
    finiteness
  have hmodel : steinhausMeasure {ω : Omega | ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ≤ t₀} ≤ B := by
    have hc := block_smallball_caustic s hs a 0 p1 p2 p3 p4 hp1 hp2 hp3 hp4
      h12 h13 h14 h23 h24 h34 hA hB hC hD hρB hr0 hr2 hσ0 hσ0G hJ hHσ0 hss hss2
    simpa only [zero_add, hBdef] using hc
  have ht0R : t₀ ≤ ∑ n ∈ s, |a n| := by
    have hnp4 : ‖(a p4 : ℂ)‖ = |a p4| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 : t₀ ≤ |a p4| := by
      rw [← hnp4]
      nlinarith [hr2, norm_nonneg (a p3 : ℂ), hr0.le]
    have h2 : |a p4| ≤ ∑ n ∈ s, |a n| :=
      Finset.single_le_sum (f := fun n => |a n|) (fun n _ => abs_nonneg _) hp4
    linarith
  exact floorFailure_timeDensity_le_unconditional a s hs1 t₀ (le_of_lt hr0) ht0R B hBtop hmodel
    fail hfail0 hfle1 hfsupp hfail_int

end RHTower
