import GaloisForLFunctions.KodairaParshinAbc.DegreeZeroClassesHaveVanishingTateHeight
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.WindowNaiveHeights

/-!
# Window Rosati forms of degree zero

The window integral Rosati forms `q_x(ξ) = τ_x(ξ ⋆ ξ′)` of the corpus
(`CohomologyOfWindowsOfSpecZ.windowRosati`) are homogeneous of degree two on the window
correspondences.  The two height principles for classes on a curve apply to them verbatim:

* **negative degree** — a window form bounded above on the window correspondences is `≤ 0` there
  (`windowRosati_nonpos_of_bounded_above`); together with the windowed Tate law, a window form that
  is bounded above and has a naive height vanishes (`windowRosati_eq_zero_of_naiveHeight_of_bounded`);
* **degree zero** — if `|q_x| ≤ ε q_y + B_ε` on the window correspondences for every `ε > 0`,
  then `q_x = 0` there (`windowRosati_eq_zero_of_degree_zero`); if `q_x - c q_y` satisfies this
  bound, then `q_x = c q_y` (`windowRosati_eq_smul_of_degree_zero`).
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc

open CohomologyOfWindowsOfSpecZ

theorem windowRosati_two_nsmul (x : ℝ → ℝ) (A a : ℝ) (ξ : windowCorr A a) :
    windowRosati x ((2 • ξ : windowCorr A a) : ℝ →₀ ℤ) = 4 * windowRosati x ξ := by
  rw [AddSubgroup.coe_nsmul, windowRosati_nsmul]
  norm_num

/-- **Negative degree**: a window Rosati form bounded above on the window correspondences is
nonpositive there. -/
theorem windowRosati_nonpos_of_bounded_above (x : ℝ → ℝ) (A a : ℝ) {B : ℝ}
    (hB : ∀ ξ ∈ windowCorr A a, windowRosati x ξ ≤ B) :
    ∀ ξ ∈ windowCorr A a, windowRosati x ξ ≤ 0 := fun ξ hξ =>
  nonpos_of_two_nsmul_of_bounded_above (q := fun η : windowCorr A a => windowRosati x η)
    (windowRosati_two_nsmul x A a) (fun η => hB η η.2) ⟨ξ, hξ⟩

/-- A window form with a naive height that is bounded above vanishes on the window
correspondences. -/
theorem windowRosati_eq_zero_of_naiveHeight_of_bounded (x : ℝ → ℝ) (A a : ℝ)
    (hnaive : ∃ h : windowCorr A a → ℝ, ∃ K B : ℝ, (∀ ξ, -K ≤ h ξ) ∧
        ∀ ξ, |h ξ - windowRosati x ξ| ≤ B)
    {B : ℝ} (hB : ∀ ξ ∈ windowCorr A a, windowRosati x ξ ≤ B) :
    ∀ ξ ∈ windowCorr A a, windowRosati x ξ = 0 := fun ξ hξ =>
  le_antisymm (windowRosati_nonpos_of_bounded_above x A a hB ξ hξ)
    ((exists_window_naiveHeight_iff x A a).mp hnaive ξ hξ)

/-- **Degree zero**: if `|q_x| ≤ ε q_y + B_ε` on the window correspondences for every `ε > 0`,
then `q_x` vanishes there. -/
theorem windowRosati_eq_zero_of_degree_zero (x y : ℝ → ℝ) (A a : ℝ)
    (hcor : ∀ ε > 0, ∃ B, ∀ ξ ∈ windowCorr A a, |windowRosati x ξ| ≤ ε * windowRosati y ξ + B) :
    ∀ ξ ∈ windowCorr A a, windowRosati x ξ = 0 := fun ξ hξ =>
  eq_zero_of_two_nsmul_of_degree_zero (q := fun η : windowCorr A a => windowRosati x η)
    (qM := fun η : windowCorr A a => windowRosati y η) (windowRosati_two_nsmul x A a)
    (windowRosati_two_nsmul y A a)
    (fun ε hε => by
      obtain ⟨B, hB⟩ := hcor ε hε
      exact ⟨B, fun η => hB η η.2⟩) ⟨ξ, hξ⟩

/-- **Proportionality**: if `|q_x - c q_y| ≤ ε q_y + B_ε` on the window correspondences for every
`ε > 0`, then `q_x = c q_y` there. -/
theorem windowRosati_eq_smul_of_degree_zero (x y : ℝ → ℝ) (A a c : ℝ)
    (hcor : ∀ ε > 0, ∃ B, ∀ ξ ∈ windowCorr A a,
      |windowRosati x ξ - c * windowRosati y ξ| ≤ ε * windowRosati y ξ + B) :
    ∀ ξ ∈ windowCorr A a, windowRosati x ξ = c * windowRosati y ξ := fun ξ hξ => by
  have h := eq_zero_of_two_nsmul_of_degree_zero
    (q := fun η : windowCorr A a => windowRosati x η - c * windowRosati y η)
    (qM := fun η : windowCorr A a => windowRosati y η)
    (fun η => by simp only [windowRosati_two_nsmul]; ring) (windowRosati_two_nsmul y A a)
    (fun ε hε => by
      obtain ⟨B, hB⟩ := hcor ε hε
      exact ⟨B, fun η => hB η η.2⟩) ⟨ξ, hξ⟩
  simp only at h
  linarith

end GaloisForLFunctions.KodairaParshinAbc
