import GaloisForLFunctions.RHTower.ZetaPartialSumIsolatedZeroHeightsAndUniformPairReturns

/-!
# Targets with an interior zero are not approximated by zeta at positive density

Let `closedBall ρ₀ r` lie in `1/2 < Re s < 1` (with `r ≤ (Re ρ₀ − 1/2)/2`, `r ≤ (1 − Re ρ₀)/2`), and
let `g : ℂ → ℂ` be any function with a zero in the open disc and `|g| ≥ m > 0` on the boundary
circle.  If `ζ(· + iτ)` is within `ε ≤ m/2` of `g` on the closed disc, the minimum-modulus principle
forces a zero of `ζ` in `ball ρ₀ r + iτ` (`exists_zero_of_mem_zetaTargetReturnSet`); zero-forcing
shift sets have density zero, so

  the heights at which `ζ(· + iτ)` approximates `g` on the disc have density zero
  (`eventually_volume_zetaTargetReturnSet_le`, `not_pos_upperDensity_zetaTargetReturnSet`).

This is the sharp complement of universality: targets approached by the orbit of `ζ` at positive
density of heights have no isolated zero in the disc.  Two corpus laws are instances: the self-return
set `zetaReturnSet` around an off-line zero of `ζ` (`zetaReturnSet_eq_zetaTargetReturnSet`,
`eventually_volume_zetaReturnSet_le_of_zero`) and the pole-shifted return set of a partial sum
vanishing in the disc (`poleShiftedReturnSet_eq_zetaTargetReturnSet`).
-/

open Complex Filter Topology MeasureTheory Set Metric
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

namespace RHTower

/-- Heights at which `ζ(· + iτ)` is within `ε` of the target `g` on `K`. -/
def zetaTargetReturnSet (g : ℂ → ℂ) (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {τ : ℝ | ∀ z ∈ K, ‖riemannZeta (z + τ * I) - g z‖ < ε}

theorem zetaReturnSet_eq_zetaTargetReturnSet (K : Set ℂ) (ε : ℝ) :
    zetaReturnSet K ε = zetaTargetReturnSet riemannZeta K ε := rfl

theorem poleShiftedReturnSet_eq_zetaTargetReturnSet (M : ℕ) (K : Set ℂ) (ε : ℝ) :
    poleShiftedReturnSet M K ε =
      zetaTargetReturnSet (edPoly (fun _ => 1) (Finset.Icc 1 M)) K ε := rfl

/-- Approximating a target with an interior zero forces a zero of `ζ` in the translated disc. -/
theorem exists_zero_of_mem_zetaTargetReturnSet {g : ℂ → ℂ} {ρ₀ : ℂ} {r m ε τ : ℝ} (hr : 0 < r)
    (hre : ∀ s ∈ closedBall ρ₀ r, s.re < 1) (hw : ∃ w ∈ ball ρ₀ r, g w = 0)
    (hm : ∀ z ∈ sphere ρ₀ r, m ≤ ‖g z‖) (hε : ε ≤ m / 2)
    (hτ : τ ∈ zetaTargetReturnSet g (closedBall ρ₀ r) ε) :
    ∃ z ∈ ball ρ₀ r, riemannZeta (z + τ * I) = 0 := by
  obtain ⟨w, hw, hw0⟩ := hw
  have hdiff : DifferentiableOn ℂ (fun s => riemannZeta (s + τ * I)) (closedBall ρ₀ r) := by
    intro s hs
    have hne : s + τ * I ≠ 1 := by
      intro h
      have h' := congrArg Complex.re h
      simp at h'
      linarith [hre s hs]
    exact ((differentiableAt_riemannZeta hne).comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
  refine exists_zero_of_exists_norm_lt_sphere_on hr hdiff hw fun z hz => ?_
  have h1 := hτ w (ball_subset_closedBall hw)
  rw [hw0, sub_zero] at h1
  have h2 := hτ z (sphere_subset_closedBall hz)
  have h3 := hm z hz
  have h4 := norm_sub_norm_le (g z) (riemannZeta (z + τ * I))
  rw [norm_sub_rev] at h4
  show ‖riemannZeta (w + τ * I)‖ < ‖riemannZeta (z + τ * I)‖
  linarith

/-- **Targets with an interior zero are approximated only on a density-zero set of heights.** -/
theorem eventually_volume_zetaTargetReturnSet_le {g : ℂ → ℂ} {ρ₀ : ℂ} {r m ε : ℝ} (hr : 0 < r)
    (hr2 : r ≤ (ρ₀.re - 1 / 2) / 2) (hr3 : r ≤ (1 - ρ₀.re) / 2)
    (hw : ∃ w ∈ ball ρ₀ r, g w = 0) (hm : ∀ z ∈ sphere ρ₀ r, m ≤ ‖g z‖) (hε : ε ≤ m / 2)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T in atTop, volume (zetaTargetReturnSet g (closedBall ρ₀ r) ε ∩ Icc 0 T) ≤
      ENNReal.ofReal (κ * T) := by
  have hre : ∀ s ∈ closedBall ρ₀ r, s.re < 1 := fun s hs => by
    have := re_le_of_mem_closedBall hs
    linarith
  exact eventually_volume_inter_Icc_le_of_forces_zero hr hr2 hr3
    (fun τ hτ => exists_zero_of_mem_zetaTargetReturnSet hr hre hw hm hε hτ) hκ

/-- **Orbit-closure form.**  No target with a zero in the open disc and a positive floor on the
boundary circle is approached by `ζ` on the disc with positive upper density of heights. -/
theorem not_pos_upperDensity_zetaTargetReturnSet {g : ℂ → ℂ} {ρ₀ : ℂ} {r m ε : ℝ} (hr : 0 < r)
    (hr2 : r ≤ (ρ₀.re - 1 / 2) / 2) (hr3 : r ≤ (1 - ρ₀.re) / 2)
    (hw : ∃ w ∈ ball ρ₀ r, g w = 0) (hm : ∀ z ∈ sphere ρ₀ r, m ≤ ‖g z‖) (hε : ε ≤ m / 2) :
    ¬ ∃ κ > 0, ∃ᶠ T : ℝ in atTop,
      ENNReal.ofReal (κ * T) ≤ volume (zetaTargetReturnSet g (closedBall ρ₀ r) ε ∩ Icc 0 T) := by
  rintro ⟨κ, hκ, hfreq⟩
  obtain ⟨T, hT1, hT2, hT0⟩ := (hfreq.and_eventually
    ((eventually_volume_zetaTargetReturnSet_le hr hr2 hr3 hw hm hε (half_pos hκ)).and
      (eventually_gt_atTop 0))).exists
  have h := hT1.trans hT2
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  nlinarith

/-- The self-return law around an off-line zero is the instance `g = ζ`: with an isolating disc
`closedBall ρ₀ r` on whose circle `|ζ| ≥ m`, the self-return set within `ε ≤ m/2` has density
zero. -/
theorem eventually_volume_zetaReturnSet_le_of_zero {ρ₀ : ℂ} {r m ε : ℝ} (hr : 0 < r)
    (hr2 : r ≤ (ρ₀.re - 1 / 2) / 2) (hr3 : r ≤ (1 - ρ₀.re) / 2) (hρ₀ : riemannZeta ρ₀ = 0)
    (hm : ∀ z ∈ sphere ρ₀ r, m ≤ ‖riemannZeta z‖) (hε : ε ≤ m / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T in atTop, volume (zetaReturnSet (closedBall ρ₀ r) ε ∩ Icc 0 T) ≤
      ENNReal.ofReal (κ * T) := by
  rw [zetaReturnSet_eq_zetaTargetReturnSet]
  exact eventually_volume_zetaTargetReturnSet_le hr hr2 hr3 ⟨ρ₀, mem_ball_self hr, hρ₀⟩ hm hε hκ

end RHTower
