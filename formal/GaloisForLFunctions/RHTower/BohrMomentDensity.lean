/-
From the even-moment tower to the sharp floor-failure density bound.

The even-moment Bohr tower (`tendsto_evenMoment_average_steinhaus`) equates each `‖F‖^{2k}`
time average with the model `2k`-th moment. Linearity extends this to any polynomial in
`‖F‖²`, and a polynomial majorant of the failure indicator then bounds the Cesàro upper time
density by the polynomial's model expectation. Driving a majorant family to the indicator
(`δ → 0`) collapses the bound onto the exact model small-ball measure.

* `tendsto_polyMoment_average_steinhaus` — time average of `∑_j c_j ‖F‖^{2j}` converges to
  the model expectation `∑_j c_j · E‖∑ aₙ Xₙ‖^{2j}`.
* `cesaroUpperDensity_le_polyMoment` — an observable dominated by such a polynomial has upper
  density at most that model expectation.
* `floorFailure_timeDensity_le_sharp` — given a family of polynomial majorants whose model
  expectation approximates the model small-ball measure `B` to within every `δ > 0`, the
  Cesàro upper time density of any `[0,1]`-observable supported on `{‖F‖ ≤ t₀}` is at most
  `B.toReal`. The `δ → 0` collapse is the last step to the sharp bound (with `B` supplied by
  the block small-ball law).
-/
import GaloisForLFunctions.RHTower.BohrMoments
import GaloisForLFunctions.RHTower.FloorFailureDensity

open MeasureTheory intervalIntegral Filter Topology Complex Finset
open scoped Classical

namespace RHTower

open Weyl SteinhausModel

/-- **Polynomial moment time average.** For polynomial coefficients `c` and degree `d`, the
Cesàro time average of `∑_j c_j ‖F‖^{2j}` converges to `∑_j c_j · E‖∑ aₙ Xₙ‖^{2j}` — the
model expectation of the same polynomial in `‖F‖²`, by linearity over the even-moment tower. -/
theorem tendsto_polyMoment_average_steinhaus
    (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (d : ℕ) (c : ℕ → ℝ) :
    Tendsto (fun U : ℝ =>
        U⁻¹ * ∫ t in (0:ℝ)..U, ∑ j ∈ range (d + 1), c j * ‖dpoly a s t‖ ^ (2 * j)) atTop
      (𝓝 (∑ j ∈ range (d + 1),
        c j * ∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * j) ∂steinhausMeasure)) := by
  have hcont : ∀ j : ℕ, Continuous (fun t : ℝ => c j * ‖dpoly a s t‖ ^ (2 * j)) := by
    intro j
    have := continuous_dpoly a s
    fun_prop
  have hrw : ∀ U : ℝ,
      U⁻¹ * ∫ t in (0:ℝ)..U, ∑ j ∈ range (d + 1), c j * ‖dpoly a s t‖ ^ (2 * j)
        = ∑ j ∈ range (d + 1), c j * (U⁻¹ * ∫ t in (0:ℝ)..U, ‖dpoly a s t‖ ^ (2 * j)) := by
    intro U
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont j).intervalIntegrable 0 U),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul]
    ring
  simp_rw [hrw]
  apply tendsto_finsetSum
  intro j _
  have hev := tendsto_evenMoment_average_steinhaus a s hs j
  have h2 : Tendsto (fun U : ℝ => U⁻¹ * ∫ t in (0:ℝ)..U, ‖dpoly a s t‖ ^ (2 * j)) atTop
      (𝓝 (∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * j) ∂steinhausMeasure)) := by
    simpa only [div_eq_inv_mul] using hev
  exact h2.const_mul (c j)

/-- **Density bound from a polynomial majorant.** If the line failure observable is dominated
by a polynomial `∑_j c_j ‖F‖^{2j}` in the squared carrier, its Cesàro upper time density is at
most the model expectation `∑_j c_j · E‖∑ aₙ Xₙ‖^{2j}` of that polynomial. -/
theorem cesaroUpperDensity_le_polyMoment
    (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (d : ℕ) (c : ℕ → ℝ)
    (fail : ℝ → ℝ) (hfail0 : ∀ τ, 0 ≤ fail τ)
    (hfg : ∀ τ, fail τ ≤ ∑ j ∈ range (d + 1), c j * ‖dpoly a s τ‖ ^ (2 * j))
    (hfail_int : ∀ T : ℝ, IntervalIntegrable fail volume 0 T) :
    cesaroUpperDensity fail
      ≤ ∑ j ∈ range (d + 1),
          c j * ∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * j) ∂steinhausMeasure := by
  set g : ℝ → ℝ := fun τ => ∑ j ∈ range (d + 1), c j * ‖dpoly a s τ‖ ^ (2 * j) with hgdef
  have hgconv := tendsto_polyMoment_average_steinhaus a s hs d c
  have hgcont : Continuous g := by
    rw [hgdef]
    have := continuous_dpoly a s
    fun_prop
  have hg_int : ∀ T : ℝ, IntervalIntegrable g volume 0 T :=
    fun T => hgcont.intervalIntegrable 0 T
  calc cesaroUpperDensity fail
      ≤ cesaroUpperDensity g :=
        cesaroUpperDensity_mono fail g hfail0 hfg hfail_int hg_int hgconv
    _ = ∑ j ∈ range (d + 1),
          c j * ∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * j) ∂steinhausMeasure :=
        hgconv.limsup_eq

/-- **Sharp floor-failure density from a polynomial-majorant family.** If for every `δ > 0`
there is a polynomial in `‖F‖²` that majorizes the line failure indicator and whose model
expectation is within `δ` of the model small-ball measure `B`, then the Cesàro upper time
density of any `[0,1]`-observable supported on `{‖F‖ ≤ t₀}` is at most `B.toReal`. Driving
`δ → 0` collapses the polynomial-majorant tower onto the exact model measure. -/
theorem floorFailure_timeDensity_le_sharp
    (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (t₀ : ℝ) (B : ENNReal) (hBtop : B ≠ ⊤)
    (hmodel : steinhausMeasure {ω : Omega | ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ≤ t₀} ≤ B)
    (fail : ℝ → ℝ) (hfail0 : ∀ τ, 0 ≤ fail τ) (hfle1 : ∀ τ, fail τ ≤ 1)
    (hfsupp : ∀ τ, t₀ < ‖dpoly a s τ‖ → fail τ = 0)
    (hfail_int : ∀ T : ℝ, IntervalIntegrable fail volume 0 T)
    (hApprox : ∀ δ : ℝ, 0 < δ → ∃ (d : ℕ) (c : ℕ → ℝ),
      (∀ τ : ℝ, ‖dpoly a s τ‖ ≤ t₀ → 1 ≤ ∑ j ∈ range (d + 1), c j * ‖dpoly a s τ‖ ^ (2 * j)) ∧
      (∀ τ : ℝ, 0 ≤ ∑ j ∈ range (d + 1), c j * ‖dpoly a s τ‖ ^ (2 * j)) ∧
      (∑ j ∈ range (d + 1),
          c j * ∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * j) ∂steinhausMeasure)
        ≤ (steinhausMeasure {ω : Omega | ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ≤ t₀}).toReal + δ) :
    cesaroUpperDensity fail ≤ B.toReal := by
  have hfin : steinhausMeasure {ω : Omega | ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ≤ t₀} ≠ ⊤ :=
    measure_ne_top _ _
  have htoReal : (steinhausMeasure {ω : Omega | ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ≤ t₀}).toReal
      ≤ B.toReal := (ENNReal.toReal_le_toReal hfin hBtop).mpr hmodel
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨d, c, hmaj, hnn, hclose⟩ := hApprox δ hδ
  have hfg : ∀ τ, fail τ ≤ ∑ j ∈ range (d + 1), c j * ‖dpoly a s τ‖ ^ (2 * j) := by
    intro τ
    by_cases hc : ‖dpoly a s τ‖ ≤ t₀
    · exact le_trans (hfle1 τ) (hmaj τ hc)
    · rw [hfsupp τ (not_le.mp hc)]; exact hnn τ
  have hdens := cesaroUpperDensity_le_polyMoment a s hs d c fail hfail0 hfg hfail_int
  calc cesaroUpperDensity fail
      ≤ ∑ j ∈ range (d + 1),
          c j * ∫ ω, ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ^ (2 * j) ∂steinhausMeasure := hdens
    _ ≤ (steinhausMeasure {ω : Omega | ‖∑ n ∈ s, (a n : ℂ) * X n ω‖ ≤ t₀}).toReal + δ := hclose
    _ ≤ B.toReal + δ := by linarith [htoReal]

end RHTower
