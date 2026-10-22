import GaloisForLFunctions.ScaleSignedIncidenceCriticality.AUniformDeficitBoundAlreadyPassesTheGate
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheDepthIsHalfTheDeficitGrowthRate

/-!
# Subexponential subsidies are harmless

`AnArchimedeanSubsidyDestroysTheCriterion` shows a subsidy growing with the *frequency* admits a
weight of maximal defect and removes the criterion. `AUniformDeficitBoundAlreadyPassesTheGate` shows
a *constant* subsidy keeps the trans-Nyquist gate intact. The question is where the dividing line
runs, and it is not size but growth in the aperture.

Here the constant level of that theorem is replaced by one growing **linearly** in the aperture, and
the gate still holds: for any `C, D ≥ 0` the off-line lattice fails the level-`(C a + D)`
certificate at some aperture (`exists_aperture_not_weilFloorAtLevel_linear`), because its ground
energy grows exponentially — `ℓ e^{δ(2a−ℓ)}` of
`SquareRootThreshold.latticeFloor_aperture_bounds` — while the subsidy grows only linearly. Hence
`linearDeficit_separates_the_transNyquist_pair`: the reading still separates the pair every bounded
reading identifies.

`whichSubsidiesAreHarmless` states the dichotomy. A mechanism may lose an amount of energy growing
linearly with its aperture and still decide the trans-Nyquist pair; it may not lose an amount
growing with the frequency of its test, because that is what the all-ones weight already satisfies.
The relevant comparison is therefore against the exponential `e^{2δa}` of the off-line ground
energy, and any subsidy below it — constant, linear, polynomial — is harmless.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. A linearly growing level is still outgrown -/

/-- **The lattice ground energy outgrows a linear subsidy.** -/
theorem exists_aperture_not_weilFloorAtLevel_linear {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ a : ℝ, L / 2 < a ∧
      ¬ WeilFloorAtLevel (offLineLatticeConfig hL hδ hδ') a (C * a + D) := by
  have hCL : 0 ≤ C * L := mul_nonneg hC hL.le
  set K : ℝ := 2 + C / 2 + L + C * L / 2 + D with hK
  have hK0 : 0 < K := by simp only [hK]; linarith
  set s : ℝ := max 1 (4 * K / (L * δ ^ 2)) with hs
  have hs1 : (1 : ℝ) ≤ s := le_max_left _ _
  have hsbig : 4 * K / (L * δ ^ 2) ≤ s := le_max_right _ _
  have hslack : K ≤ L * δ ^ 2 * s / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have h := hsbig
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < L * δ ^ 2)] at h
    nlinarith [h]
  have hquad : K * s ≤ L * δ ^ 2 * s ^ 2 / 4 := by
    have h := mul_le_mul_of_nonneg_left hslack (by linarith : (0 : ℝ) ≤ s)
    nlinarith [h]
  have haL : L / 2 < (s + L) / 2 := by linarith
  have ha0 : (0 : ℝ) < (s + L) / 2 := by linarith
  refine ⟨(s + L) / 2, haL, ?_⟩
  rw [offLineLattice_weilFloor_iff hL hδ hδ' haL]
  have hdeep := (latticeFloor_aperture_bounds hL hδ ha0).2
  have hsa : 2 * ((s + L) / 2) - L = s := by ring
  have hexp : 1 + δ * s + (δ * s) ^ 2 / 4 ≤ Real.exp (δ * s) :=
    one_add_add_sq_quarter_le_exp (by positivity)
  have hmul : L * (1 + δ * s + (δ * s) ^ 2 / 4) ≤ L * Real.exp (δ * s) :=
    mul_le_mul_of_nonneg_left hexp hL.le
  have e1 : 0 ≤ (s - 1) * L := mul_nonneg (by linarith) hL.le
  have e2 : 0 ≤ (s - 1) * (C * L) := mul_nonneg (by linarith) hCL
  have e3 : 0 ≤ (s - 1) * D := mul_nonneg (by linarith) hD
  have e4 : 0 < L * (δ * s) := by positivity
  have hkey : C * ((s + L) / 2) + D <
      L * Real.exp (δ * (2 * ((s + L) / 2) - L)) - 2 * ((s + L) / 2) - L := by
    rw [hsa]
    simp only [hK] at hquad
    nlinarith [hmul, hquad, e1, e2, e3, e4]
  exact not_le.mpr (by linarith)

/-! ### 2. The gate still holds -/

/-- A linearly growing deficit allowance, held at every aperture. -/
def linearDeficit (C D : ℝ) (Z : TemperedZeroConfig) : Prop :=
  ∀ a : ℝ, 0 < a → WeilFloorAtLevel Z.1 a (C * a + D)

/-- The on-line lattice satisfies it. -/
theorem linearDeficit_onLineLattice {L C D : ℝ} (hL : 0 < L) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    linearDeficit C D (onLineLattice hL) := by
  intro a ha f hf hfs _ _
  have hpos : 0 ≤ ((onLineLattice hL).1.W f f).re := re_W_onLineLatticeConfig_nonneg hL f
  have hint : (0 : ℝ) ≤ ∫ u, ‖f u‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  have hlev : (0 : ℝ) ≤ C * a + D := by positivity
  nlinarith

/-- No off-line lattice does. -/
theorem not_linearDeficit_offLineLattice {L δ C D : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ¬ linearDeficit C D (offLineLattice hL hδ hδ') := by
  intro h
  obtain ⟨a, ha, hnot⟩ := exists_aperture_not_weilFloorAtLevel_linear hL hδ hδ' hC hD
  exact hnot (h a (by linarith))

/-- **The gate holds under a linear subsidy.** -/
theorem linearDeficit_separates_the_transNyquist_pair {L C D : ℝ} (hL : 0 < L) (hC : 0 ≤ C)
    (hD : 0 ≤ D) :
    linearDeficit C D (offLineLattice hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl) ≠
      linearDeficit C D (onLineLattice hL) := by
  intro heq
  exact not_linearDeficit_offLineLattice hL (by norm_num) le_rfl hC hD
    (heq ▸ linearDeficit_onLineLattice hL hC hD)

/-! ### 3. The dichotomy -/

/-- **Which subsidies are harmless.** A deficit allowance growing linearly in the aperture still
separates the trans-Nyquist pair; the comparison that matters is against the exponential growth of
the off-line ground energy, not against any absolute size. -/
theorem whichSubsidiesAreHarmless {L C D : ℝ} (hL : 0 < L) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    linearDeficit C D (onLineLattice hL) ∧
      (∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ hδ' : δ ≤ 1 / 2,
        ¬ linearDeficit C D (offLineLattice hL hδ hδ')) ∧
      linearDeficit C D (offLineLattice hL (by norm_num : (0 : ℝ) < 1 / 2) le_rfl) ≠
        linearDeficit C D (onLineLattice hL) :=
  ⟨linearDeficit_onLineLattice hL hC hD,
    fun _ hδ hδ' => not_linearDeficit_offLineLattice hL hδ hδ' hC hD,
    linearDeficit_separates_the_transNyquist_pair hL hC hD⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
