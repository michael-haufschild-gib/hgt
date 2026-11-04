import GaloisForLFunctions.ZeroConfigurationGeometry.TheCameraAndTheTilt
import GaloisForLFunctions.SquareRootThreshold.NyquistResolutionOfTheWeilForm

/-!
# Hiding needs near-collisions

Where can a cancelling cluster live? `FiniteModificationsAreSeenAtEveryAperture` shows it must be
infinite. For configurations on the line, Ingham's inequality gives the second constraint: the
resolution theorem `SquareRootThreshold.eq_of_weil_eq_of_separated` identifies `g`-separated
configurations at every aperture `a > π/(2g)`.

* **Near-collisions** (`exists_near_pair_of_onLine_mimic`). If two distinct tempered on-line
  configurations are mimics at aperture `a`, then for every scale `g > π/(2a)` their union contains
  two distinct points at height distance `< g`.

So a cancelling cluster must contain near-collisions at the resolution scale `π/(2a)` of the
camera. That is exactly where the image reads gaps only at second order
(`TheSquaredGapIsReadAtSecondOrder`): hiding and the coalescent channel are the same regime. The
lattice pair `{½ + 2πik/L}` (double) against `{½ + πik/L}` (simple) attains the scale
(`lattice_resolution_sharp`).
-/

open Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- **Hiding needs near-collisions.** -/
theorem exists_near_pair_of_onLine_mimic {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2)
    (hon' : ∀ ρ ∈ Z'.carrier, ρ.re = 1 / 2) (hne : Z.carrier ≠ Z'.carrier) {a : ℝ} (ha : 0 < a)
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) {g : ℝ} (hg : π / (2 * a) < g) :
    ∃ ρ ∈ Z.carrier ∪ Z'.carrier, ∃ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ ≠ ρ' ∧ |ρ.im - ρ'.im| < g := by
  by_contra h
  push Not at h
  have hg0 : 0 < g := lt_of_le_of_lt (by positivity) hg
  have hga : π / (2 * g) < a := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hg
    linarith
  exact hne (eq_of_weil_eq_of_separated Z Z' hZ hZ' hon hon' hg0
    (fun ρ hρ ρ' hρ' hne' => h ρ hρ ρ' hρ' hne') hga (fun f hf hfs => hW f ⟨hf, hfs⟩)).1

end GaloisForLFunctions.ZeroConfigurationGeometry
