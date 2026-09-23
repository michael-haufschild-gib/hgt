import GaloisForLFunctions.RHTower.XiPoissonShellClasses
import GaloisForLFunctions.HTGeometry.TrigPolynomialPhaseSelection
import GaloisForLFunctions.HTGeometry.GeometricAmplitudeDominance

/-!
# The three-way split of the bottom shell

For a displacement `l` of maximal modulus the shell is the disjoint union of the class at `l`, the
class at `-l`, and a remainder whose copies have strictly smaller `|Im alpha^|`.  Since all heights on
a shell agree, `‖alpha^‖ = sqrt (g_1^(2 : ℕ) + (Im alpha^)^(2 : ℕ))` is strictly increasing in `|Im alpha^|`, so
the remainder's moduli are strictly below the class modulus -- the gap that
`GeometricAmplitudeDominance` needs.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

theorem xiPoissonBottomHeight_pos : 0 < xiPoissonBottomHeight := by
  have h1 : ‖xiPoissonPoint xiPoissonBottomCopy‖ ≤ (xiPoissonPoint xiPoissonBottomCopy).re + 1 / 2 :=
    norm_xiPoissonPoint_le _
  have h2 : ‖xiPoissonPoint xiPoissonBottomCopy‖ = ‖xiSpectralPoint xiPoissonBottomCopy‖ :=
    norm_xiPoissonPoint _
  have h3 : (4 : ℝ) < ‖xiSpectralPoint xiPoissonBottomCopy‖ :=
    four_lt_norm_xiSpectralPoint _
  have : xiPoissonBottomHeight = (xiPoissonPoint xiPoissonBottomCopy).re := rfl
  rw [this]
  linarith [h1, h2 ▸ h3]

/-- On the bottom shell the Poisson modulus is determined by the displacement. -/
theorem norm_xiPoissonPoint_of_mem_bottomShell {q : XiZeroCopy} (hq : q ∈ xiPoissonBottomShell) :
    ‖xiPoissonPoint q‖ =
      Real.sqrt (xiPoissonBottomHeight ^ (2 : ℕ) + (xiPoissonPoint q).im ^ (2 : ℕ)) := by
  have hre : (xiPoissonPoint q).re = xiPoissonBottomHeight := mem_xiPoissonBottomShell.mp hq
  rw [Complex.norm_def, Complex.normSq_apply, hre]
  congr 1
  ring

/-- The remainder of the shell after removing the two extreme displacement classes. -/
def xiShellRest (l : ℝ) : Finset XiZeroCopy :=
  xiPoissonBottomShell.filter
    (fun q => (xiPoissonPoint q).im ≠ l ∧ (xiPoissonPoint q).im ≠ -l)

/-- **The three-way split.** -/
theorem xiPoissonBottomShell_split {l : ℝ} (hl : l ≠ 0) (f : XiZeroCopy → ℂ) :
    ∑ q ∈ xiPoissonBottomShell, f q =
      (∑ q ∈ xiShellClass l, f q) + (∑ q ∈ xiShellClass (-l), f q) +
        ∑ q ∈ xiShellRest l, f q := by
  classical
  have hne : l ≠ -l := by
    intro h
    apply hl
    linarith [h]
  have h1 :
      (∑ q ∈ xiPoissonBottomShell.filter (fun q => (xiPoissonPoint q).im = l), f q) +
        (∑ q ∈ xiPoissonBottomShell.filter (fun q => ¬ ((xiPoissonPoint q).im = l)), f q) =
        ∑ q ∈ xiPoissonBottomShell, f q :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have h2 :
      (∑ q ∈ (xiPoissonBottomShell.filter (fun q => ¬ ((xiPoissonPoint q).im = l))).filter
          (fun q => (xiPoissonPoint q).im = -l), f q) +
        (∑ q ∈ (xiPoissonBottomShell.filter (fun q => ¬ ((xiPoissonPoint q).im = l))).filter
          (fun q => ¬ ((xiPoissonPoint q).im = -l)), f q) =
        ∑ q ∈ xiPoissonBottomShell.filter (fun q => ¬ ((xiPoissonPoint q).im = l)), f q :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hA : (xiPoissonBottomShell.filter (fun q => ¬ ((xiPoissonPoint q).im = l))).filter
      (fun q => (xiPoissonPoint q).im = -l) = xiShellClass (-l) := by
    rw [Finset.filter_filter, xiShellClass]
    refine Finset.filter_congr ?_
    intro q _
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      intro hcon
      exact hne hcon.symm
  have hB : (xiPoissonBottomShell.filter (fun q => ¬ ((xiPoissonPoint q).im = l))).filter
      (fun q => ¬ ((xiPoissonPoint q).im = -l)) = xiShellRest l := by
    rw [Finset.filter_filter, xiShellRest]
  rw [hA, hB] at h2
  rw [← h1, ← h2]
  simp only [xiShellClass]
  ring

/-- Copies in the remainder have strictly smaller modulus. -/
theorem norm_lt_of_mem_xiShellRest {l : ℝ}
    (hmax : ∀ q ∈ xiPoissonBottomShell, |(xiPoissonPoint q).im| ≤ |l|)
    {q : XiZeroCopy} (hq : q ∈ xiShellRest l) :
    ‖xiPoissonPoint q‖ < Real.sqrt (xiPoissonBottomHeight ^ (2 : ℕ) + l ^ (2 : ℕ)) := by
  classical
  have hmem : q ∈ xiPoissonBottomShell ∧
      ((xiPoissonPoint q).im ≠ l ∧ (xiPoissonPoint q).im ≠ -l) := by
    simpa [xiShellRest] using hq
  obtain ⟨hs, hne₁, hne₂⟩ := hmem
  have hle : |(xiPoissonPoint q).im| ≤ |l| := hmax q hs
  have hlt : |(xiPoissonPoint q).im| < |l| := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      rcases abs_eq_abs.mp h with h' | h'
      · exact hne₁ h'
      · exact hne₂ h'
  have hsq : (xiPoissonPoint q).im ^ (2 : ℕ) < l ^ (2 : ℕ) := by
    have habs : 0 ≤ |(xiPoissonPoint q).im| := abs_nonneg _
    have h1 : |(xiPoissonPoint q).im| ^ (2 : ℕ) < |l| ^ (2 : ℕ) := by nlinarith [hlt, habs]
    rwa [sq_abs, sq_abs] at h1
  rw [norm_xiPoissonPoint_of_mem_bottomShell hs]
  exact Real.sqrt_lt_sqrt (by positivity) (by linarith)

end

end RHTower
