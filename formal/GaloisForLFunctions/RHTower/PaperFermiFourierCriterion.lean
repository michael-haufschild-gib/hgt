import GaloisForLFunctions.RHTower.PaperFermiFourierEnergy
import GaloisForLFunctions.RHTower.PaperFermiFourierReconstruction

/-! # Full-frequency approximation and the native FZZ obstruction

One coefficient vector must control every frequency cutoff. The cutoff cannot be
selected before the approximation when transporting an off-line witness floor.
These results construct neither an approximating sequence nor a zero-free strip.
-/

namespace RHTower
noncomputable section
open MeasureTheory Filter Topology Set

def PaperFermiSpectralApproximation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℝ),
    (∀ j, 1 ≤ a j) ∧ ∀ N, paperFermiSpectralError c a N < ε

theorem paperFermiError_bound_iff {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ) (B : ℝ) :
    paperFermiError c a ≤ B ↔ ∀ N, paperFermiSpectralError c a N ≤ B := by
  constructor
  · intro h N
    exact (paperFermiSpectralError_le c a N).trans h
  · intro h
    exact le_of_tendsto (paperFermiSpectralError_tendsto c a) (Eventually.of_forall h)

theorem paperFermiSpectralApproximation_iff :
    PaperFermiSpectralApproximation ↔
      ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℝ),
        (∀ j, 1 ≤ a j) ∧
          (∫ t in Ioc (0 : ℝ) 1, ‖dyadicHaar t - fermiNymanCombination c a t‖ ^ 2) < ε := by
  constructor
  · intro h ε hε
    obtain ⟨n, c, a, ha, hb⟩ := h (ε / 2) (by positivity)
    refine ⟨n, c, a, ha, ?_⟩
    have he := (paperFermiError_bound_iff c a (ε / 2)).mpr (fun N => (hb N).le)
    exact lt_of_le_of_lt he (by linarith)
  · intro h ε hε
    obtain ⟨n, c, a, ha, he⟩ := h ε hε
    exact ⟨n, c, a, ha, fun N => (paperFermiSpectralError_le c a N).trans_lt he⟩

theorem paperFermiSpectralApproximation_RH :
    PaperFermiSpectralApproximation → RiemannHypothesis := fun h =>
  riemannHypothesis_of_dyadicHaar_approximable (paperFermiSpectralApproximation_iff.mp h)

/-- Failure of RH exposes a positive floor shared by every admissible finite combination. -/
theorem paperFermiError_dichotomy : RiemannHypothesis ∨
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℝ),
      (∀ j, 1 ≤ a j) → δ ≤ paperFermiError c a := by
  by_cases h : RiemannHypothesis
  · exact Or.inl h
  right
  obtain ⟨ρ, hζ, h1, h2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis h
  refine ⟨(2 * ρ.re - 1) * ‖(1 - (2 : ℂ) ^ (1 - ρ)) / ρ‖ ^ 2, ?_, ?_⟩
  · have hρ : ρ ≠ 0 := by
      intro h0
      rw [h0, Complex.zero_re] at h1
      linarith
    have hn := norm_pos_iff.mpr (div_ne_zero (one_sub_two_cpow_ne_zero h2) hρ)
    have hr : 0 < 2 * ρ.re - 1 := by linarith
    positivity
  · intro n c a ha
    exact dyadicHaar_approximation_floor hζ h1 h2 c a ha

/-- The uniform error floor becomes a cofinal spectral floor for each coefficient vector. -/
theorem paperFermiSpectralError_dichotomy : RiemannHypothesis ∨
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → ℝ),
      (∀ j, 1 ≤ a j) → ∀ᶠ N in atTop, δ < paperFermiSpectralError c a N := by
  rcases paperFermiError_dichotomy with h | ⟨δ, hδ, hf⟩
  · exact Or.inl h
  right
  refine ⟨δ / 2, by positivity, ?_⟩
  intro n c a ha
  have hlt : δ / 2 < paperFermiError c a := lt_of_lt_of_le (by linarith) (hf n c a ha)
  exact (paperFermiSpectralError_tendsto c a).eventually (eventually_gt_nhds hlt)

end
end RHTower
