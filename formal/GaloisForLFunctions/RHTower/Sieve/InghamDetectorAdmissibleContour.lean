import GaloisForLFunctions.RHTower.Sieve.InghamDetectorRightEdgeNonvanishing
import GaloisForLFunctions.RHTower.Sieve.InghamDetectorWeightedLittlewood
import GaloisForLFunctions.RHTower.Sieve.InghamFixedGabrielBudget

/-!
# Unconditional admissible contours for Ingham's detector

Zeros of a nonzero entire function are finite in a compact rectangle.  Two prescribed nonempty
height intervals therefore contain ordinates avoiding every zero in the rectangle.  Applied to
Ingham's detector after its fixed right edge has become uniformly nonzero, this removes every
zero-free-boundary premise from the weighted Littlewood mass inequality.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

/-- Two separated height intervals contain horizontal slices avoiding all zeros of a nonzero
entire function over a fixed real interval. -/
theorem exists_horizontal_slices_avoiding_entire_zeros
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ z : ℂ, f z ≠ 0)
    {c d A₁ B₁ A₂ B₂ : ℝ}
    (hcd : c < d) (hA₁B₁ : A₁ < B₁) (hB₁A₂ : B₁ < A₂) (hA₂B₂ : A₂ < B₂) :
    ∃ T₁ ∈ Set.Ioo A₁ B₁, ∃ T₂ ∈ Set.Ioo A₂ B₂,
      (∀ x ∈ Set.uIcc c d, f ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.uIcc c d, f ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) := by
  classical
  let z₁ : ℂ := (c : ℂ) + (A₁ : ℂ) * I
  let z₂ : ℂ := (d : ℂ) + (B₂ : ℂ) * I
  let hfinite : {z ∈ (Set.uIcc z₁.re z₂.re ×ℂ Set.uIcc z₁.im z₂.im) |
      f z = 0}.Finite := entire_zeros_closedRectangle_finite hf hne z₁ z₂
  let Z : Finset ℂ := hfinite.toFinset
  let F : Finset ℝ := Z.image Complex.im
  obtain ⟨T₁, hT₁, hT₁avoid⟩ :=
    (Set.Ioo_infinite hA₁B₁).exists_notMem_finset F
  obtain ⟨T₂, hT₂, hT₂avoid⟩ :=
    (Set.Ioo_infinite hA₂B₂).exists_notMem_finset F
  refine ⟨T₁, hT₁, T₂, hT₂, ?_, ?_⟩
  · intro x hx hzero
    have hxI : x ∈ Set.Icc c d := by
      simpa [Set.uIcc_of_le hcd.le] using hx
    have hA₁B₂ : A₁ ≤ B₂ := (hA₁B₁.trans (hB₁A₂.trans hA₂B₂)).le
    have hT₁I : T₁ ∈ Set.Icc A₁ B₂ :=
      ⟨hT₁.1.le, (hT₁.2.trans (hB₁A₂.trans hA₂B₂)).le⟩
    let z : ℂ := (x : ℂ) + (T₁ : ℂ) * I
    have hzK : z ∈ (Set.uIcc z₁.re z₂.re ×ℂ Set.uIcc z₁.im z₂.im) := by
      apply Complex.mem_reProdIm.mpr
      simpa [z, z₁, z₂, Set.uIcc_of_le hcd.le, Set.uIcc_of_le hA₁B₂] using
        And.intro hxI hT₁I
    have hzZ : z ∈ Z := by
      change z ∈ hfinite.toFinset
      rw [Set.Finite.mem_toFinset, Set.mem_sep_iff]
      exact ⟨hzK, hzero⟩
    apply hT₁avoid
    apply Finset.mem_image.mpr
    refine ⟨z, hzZ, ?_⟩
    simp [z]
  · intro x hx hzero
    have hxI : x ∈ Set.Icc c d := by
      simpa [Set.uIcc_of_le hcd.le] using hx
    have hA₁B₂ : A₁ ≤ B₂ := (hA₁B₁.trans (hB₁A₂.trans hA₂B₂)).le
    have hT₂I : T₂ ∈ Set.Icc A₁ B₂ :=
      ⟨(hA₁B₁.trans (hB₁A₂.trans hT₂.1)).le, hT₂.2.le⟩
    let z : ℂ := (x : ℂ) + (T₂ : ℂ) * I
    have hzK : z ∈ (Set.uIcc z₁.re z₂.re ×ℂ Set.uIcc z₁.im z₂.im) := by
      apply Complex.mem_reProdIm.mpr
      simpa [z, z₁, z₂, Set.uIcc_of_le hcd.le, Set.uIcc_of_le hA₁B₂] using
        And.intro hxI hT₂I
    have hzZ : z ∈ Z := by
      change z ∈ hfinite.toFinset
      rw [Set.Finite.mem_toFinset, Set.mem_sep_iff]
      exact ⟨hzK, hzero⟩
    apply hT₂avoid
    apply Finset.mem_image.mpr
    refine ⟨z, hzZ, ?_⟩
    simp [z]

end

end RHTower

namespace RHTower.Sieve

noncomputable section

/-- Admissible detector contours can use any fixed counting edge strictly right of `1`; this edge
is independent of the right edge previously used in Gabriel interpolation. -/
theorem eventually_exists_inghamDetector_admissibleContour_at_rightEdge
    {c beta : ℝ} (hcbeta : c < beta) (hbeta : 1 < beta) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ H : ℝ,
      ∃ T₁ ∈ Set.Ioo (-|H| - 2) (-|H| - 1),
        ∃ T₂ ∈ Set.Ioo |H| (|H| + 1),
          (∀ x ∈ Set.uIcc c beta,
            inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
          (∀ x ∈ Set.uIcc c beta,
            inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
          (∀ t ∈ Set.uIcc T₁ T₂,
            inghamDetector X ((beta : ℂ) + (t : ℂ) * I) ≠ 0) ∧
          2 * Real.pi *
              (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                  ((c : ℂ) + (T₁ : ℂ) * I)
                  ((beta : ℂ) + (T₂ : ℂ) * I),
                ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c)) ≤
            inghamLittlewoodBoundary X c beta T₁ T₂ := by
  filter_upwards [eventually_inghamDetector_ne_zero_on_rightEdge hbeta] with X hright
  intro H
  have hne : ∃ z : ℂ, inghamDetector X z ≠ 0 := by
    refine ⟨(beta : ℂ) + (0 : ℂ) * I, ?_⟩
    exact hright 0
  obtain ⟨T₁, hT₁, T₂, hT₂, hbot, htop⟩ :=
    RHTower.exists_horizontal_slices_avoiding_entire_zeros
      (c := c) (d := beta)
      (A₁ := -|H| - 2) (B₁ := -|H| - 1) (A₂ := |H|) (B₂ := |H| + 1)
      (inghamDetector_analyticOnNhd_univ X) hne hcbeta
      (by linarith) (by have := abs_nonneg H; linarith) (by linarith)
  have hT : T₁ < T₂ := by
    have := abs_nonneg H
    linarith [hT₁.2, hT₂.1]
  have hright' : ∀ t ∈ Set.uIcc T₁ T₂,
      inghamDetector X ((beta : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t _
    exact hright t
  refine ⟨T₁, hT₁, T₂, hT₂, hbot, htop, hright', ?_⟩
  exact two_pi_mul_zetaZeroMass_le_inghamLittlewoodBoundary X hcbeta hT
    hbot htop hright'

/-- For every large cutoff and every requested height scale, one can select horizontal detector
edges in adjacent unit intervals so that all boundary hypotheses of weighted Littlewood are met.
The conclusion includes the resulting unconditional weighted zeta-zero mass inequality. -/
theorem eventually_exists_inghamDetector_admissibleContour :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ H : ℝ,
      ∃ T₁ ∈ Set.Ioo (-|H| - 2) (-|H| - 1),
        ∃ T₂ ∈ Set.Ioo |H| (|H| + 1),
          (∀ x ∈ Set.uIcc inghamFixedGabrielSigma inghamPowerSavingRightEdge,
            inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
          (∀ x ∈ Set.uIcc inghamFixedGabrielSigma inghamPowerSavingRightEdge,
            inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
          (∀ t ∈ Set.uIcc T₁ T₂,
            inghamDetector X ((inghamPowerSavingRightEdge : ℂ) + (t : ℂ) * I) ≠ 0) ∧
          2 * Real.pi *
              (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                  ((inghamFixedGabrielSigma : ℂ) + (T₁ : ℂ) * I)
                  ((inghamPowerSavingRightEdge : ℂ) + (T₂ : ℂ) * I),
                ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                  (w.re - inghamFixedGabrielSigma)) ≤
            inghamLittlewoodBoundary X inghamFixedGabrielSigma
              inghamPowerSavingRightEdge T₁ T₂ := by
  filter_upwards [eventually_inghamDetector_ne_zero_on_powerSavingRightEdge] with X hright
  intro H
  have hcd : inghamFixedGabrielSigma < inghamPowerSavingRightEdge := by
    norm_num [inghamFixedGabrielSigma, inghamPowerSavingRightEdge]
  have hne : ∃ z : ℂ, inghamDetector X z ≠ 0 := by
    refine ⟨(inghamPowerSavingRightEdge : ℂ) + (0 : ℂ) * I, ?_⟩
    exact hright 0
  obtain ⟨T₁, hT₁, T₂, hT₂, hbot, htop⟩ :=
    RHTower.exists_horizontal_slices_avoiding_entire_zeros
      (c := inghamFixedGabrielSigma) (d := inghamPowerSavingRightEdge)
      (A₁ := -|H| - 2) (B₁ := -|H| - 1) (A₂ := |H|) (B₂ := |H| + 1)
      (inghamDetector_analyticOnNhd_univ X) hne hcd
      (by linarith) (by have := abs_nonneg H; linarith) (by linarith)
  have hT : T₁ < T₂ := by
    have := abs_nonneg H
    linarith [hT₁.2, hT₂.1]
  have hright' : ∀ t ∈ Set.uIcc T₁ T₂,
      inghamDetector X
        ((inghamPowerSavingRightEdge : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t _
    exact hright t
  refine ⟨T₁, hT₁, T₂, hT₂, hbot, htop, hright', ?_⟩
  exact two_pi_mul_zetaZeroMass_le_inghamLittlewoodBoundary X hcd hT
    hbot htop hright'

end


end RHTower.Sieve
