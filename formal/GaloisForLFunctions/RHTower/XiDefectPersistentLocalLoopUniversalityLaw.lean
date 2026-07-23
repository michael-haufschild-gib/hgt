import GaloisForLFunctions.RHTower.QuadrantSeamConservation
import GaloisForLFunctions.RHTower.XiDescentAllRungLocalLoopDeckChargeUniversalityLaw
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# Xi-defect persistent local-loop universality

The failed quadrant--seam transport route left a positive defect object: a right-half Xi zero of
odd local order.  The later all-rung local-loop theorem supplies its exact intrinsic detector.
A defect is precisely an open-strip Xi zero whose rung-one deck character stays nontrivial on
every sufficiently small circle after square descent.
-/

open Complex Set

namespace RHTower

/-- A descended Xi point has a persistently nontrivial rung-one deck character if every
sufficiently small positive circle around it has nontrivial character. -/
def PersistentXiDefectLoop (ρ : ℂ) : Prop :=
  ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
    deckChar 2
      (loopCharge 1
        (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
          (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi)) ≠ 1

/-- Point charge and persistent descended small-loop charge are equivalent once the right-half
zero is fixed. -/
theorem xiDefect_iff_rightHalfZero_persistentLoop (ρ : ℂ) :
    XiDefect ρ ↔ ρ ∈ rightHalf ∧ xi ρ = 0 ∧ PersistentXiDefectLoop ρ := by
  constructor
  · intro hdefect
    refine ⟨hdefect.1, hdefect.2.1, ?_⟩
    obtain ⟨R₀, hR₀, hloop⟩ :=
      deckChar_loopCharge_xiDescent_center_sq hdefect.1 1
    refine ⟨R₀, hR₀, ?_⟩
    intro r hr hrR
    have heq :
        deckChar 2
          (loopCharge 1
            (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
              (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi)) =
          carrierCharge xi 1 ρ := by
      simpa using (hloop r hr hrR).2
    rw [heq]
    exact hdefect.2.2
  · rintro ⟨hright, hzero, R₀, hR₀, hpersistent⟩
    refine ⟨hright, hzero, ?_⟩
    obtain ⟨R₁, hR₁, hloop⟩ :=
      deckChar_loopCharge_xiDescent_center_sq hright 1
    let r : ℝ := min R₀ R₁ / 2
    have hr : 0 < r := by
      dsimp [r]
      positivity
    have hrR₀ : r < R₀ := by
      dsimp [r]
      have hmin : 0 < min R₀ R₁ := lt_min hR₀ hR₁
      nlinarith [min_le_left R₀ R₁]
    have hrR₁ : r < R₁ := by
      dsimp [r]
      have hmin : 0 < min R₀ R₁ := lt_min hR₀ hR₁
      nlinarith [min_le_right R₀ R₁]
    have hnontrivial := hpersistent r hr hrR₀
    have heq :
        deckChar 2
          (loopCharge 1
            (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
              (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi)) =
          carrierCharge xi 1 ρ := by
      simpa using (hloop r hr hrR₁).2
    rw [heq] at hnontrivial
    exact hnontrivial

/-- **Xi-defect persistent local-loop universality law.**  Xi defects are exactly open-critical-
strip zeros simultaneously detected by persistent nontrivial descended rung-one loop character
and odd analytic order.  This is the strongest positive local law surviving the failed
quadrant--seam terminal-dichotomy route. -/
theorem xiDefect_persistentLoop_openStrip_oddOrderUniversality (ρ : ℂ) :
    XiDefect ρ ↔
      ρ.re ∈ Ioo (1 / 2 : ℝ) 1 ∧
      xi ρ = 0 ∧
      PersistentXiDefectLoop ρ ∧
      Odd (analyticOrderAt xi ρ).toNat := by
  constructor
  · intro hdefect
    have hstrip := xi_zero_re_mem_open_unit hdefect.2.1
    have hpersistent :=
      (xiDefect_iff_rightHalfZero_persistentLoop ρ).mp hdefect |>.2.2
    have hodd := (xiDefect_charge_iff_odd ρ).mp hdefect.2.2
    exact ⟨⟨mem_rightHalf.mp hdefect.1, hstrip.2⟩,
      hdefect.2.1, hpersistent, hodd⟩
  · rintro ⟨hstrip, hzero, hpersistent, _hodd⟩
    apply (xiDefect_iff_rightHalfZero_persistentLoop ρ).mpr
    exact ⟨mem_rightHalf.mpr hstrip.1, hzero, hpersistent⟩

end RHTower
