import GaloisForLFunctions.RHTower.LevinsonWindowEdgeUnconditional
import GaloisForLFunctions.RHTower.LevinsonAdmissibleHeight

/-!
# Levinson's counting step with every hypothesis discharged

Heights at which the detector misses the whole segment `[½,4]` are dense, so the two horizontal-edge
conditions can be met inside any prescribed pair of intervals.  Once they are, the window inequality
holds with no further assumption, and Levinson's method is reduced to a single quantity: the number
of zeros of `G♯ = (s−1)²(ζ + λζ′)` inside `[½,4]×[T₁,T₂]`, counted with multiplicity.

Every other ingredient — the archimedean main term, the right edge, the two horizontal edges, the
critical-line zeros of the detector, the passage from phase advance to sign changes, and from sign
changes to odd-order critical ordinates and singleton horizontal fibres — is unconditional.
-/

open Complex Set MeasureTheory

noncomputable section

namespace RHTower

/-- **The Levinson window with no hypothesis at all.**  Admissible heights can be chosen in any two
prescribed intervals, and after that the only undetermined quantity is the number of zeros of the
entire detector inside `[½,4]×[T₁,T₂]`. -/
theorem exists_levinson_admissible_window :
    ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, lam < 0 → |lam| ≤ 1 →
      ∀ a₁ b₁ a₂ b₂ : ℝ, 20 ≤ a₁ → a₁ < b₁ → b₁ ≤ a₂ → a₂ < b₂ →
      ∃ T₁ ∈ Set.Ioo a₁ b₁, ∃ T₂ ∈ Set.Ioo a₂ b₂, ∀ n : ℕ,
        (∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (Set.uIcc (1 / 2 : ℝ) 4 ×ℂ Set.uIcc T₁ T₂) ∧
            levinsonGEntire (lam : ℂ) z = 0) →
          ((n : ℝ) + 2) * Real.pi + Real.pi + (T₂ - T₁) * (6 / T₁ ^ 2)
              + c * Real.log T₁ + c * Real.log T₂
              + 2 * Real.pi *
                (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire (lam : ℂ)) w).toNat : ℝ))
            ≤ gammaHardyTheta T₂ - gammaHardyTheta T₁) →
        n ≤ xiOddFiberCount T₂ := by
  obtain ⟨c, hc, hmain⟩ := exists_levinson_window_edge_bound_unconditional
  refine ⟨c, hc, ?_⟩
  intro lam hlam0 hlam a₁ b₁ a₂ b₂ h20 hab₁ hmid hab₂
  have hlamC : ((lam : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_lt hlam0
  obtain ⟨T₁, hT₁mem, _, hT₁G⟩ :=
    exists_levinsonG_admissible_height' (lam := (lam : ℂ)) hlamC (by linarith : (0 : ℝ) < a₁) hab₁
  obtain ⟨T₂, hT₂mem, _, hT₂G⟩ :=
    exists_levinsonG_admissible_height' (lam := (lam : ℂ)) hlamC
      (by linarith : (0 : ℝ) < a₂) hab₂
  have huIcc : Set.uIcc (1 / 2 : ℝ) 4 = Set.Icc (1 / 2 : ℝ) 4 := uIcc_of_le (by norm_num)
  refine ⟨T₁, hT₁mem, T₂, hT₂mem, ?_⟩
  refine hmain lam hlam0 hlam T₁ T₂ (by linarith [hT₁mem.1]) (by linarith [hT₁mem.2, hT₂mem.1])
    ?_ ?_
  · rw [← huIcc]; exact hT₁G
  · rw [← huIcc]; exact hT₂G

/-- The same, delivered as the singleton-fibre bound of `horizontal-singleton-zero-fibers`. -/
theorem exists_levinson_admissible_window_singleton :
    ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, lam < 0 → |lam| ≤ 1 →
      ∀ a₁ b₁ a₂ b₂ : ℝ, 20 ≤ a₁ → a₁ < b₁ → b₁ ≤ a₂ → a₂ < b₂ →
      ∃ T₁ ∈ Set.Ioo a₁ b₁, ∃ T₂ ∈ Set.Ioo a₂ b₂, ∀ n : ℕ,
        (∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (Set.uIcc (1 / 2 : ℝ) 4 ×ℂ Set.uIcc T₁ T₂) ∧
            levinsonGEntire (lam : ℂ) z = 0) →
          ((n : ℝ) + 2) * Real.pi + Real.pi + (T₂ - T₁) * (6 / T₁ ^ 2)
              + c * Real.log T₁ + c * Real.log T₂
              + 2 * Real.pi *
                (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire (lam : ℂ)) w).toNat : ℝ))
            ≤ gammaHardyTheta T₂ - gammaHardyTheta T₁) →
        (3 / 2 : ℝ) * (n : ℝ) - (xiPosZeroCount T₂ : ℝ) / 2
          ≤ (xiSingletonFiberCount T₂ : ℝ) := by
  obtain ⟨c, hc, hmain⟩ := exists_levinson_admissible_window
  refine ⟨c, hc, ?_⟩
  intro lam hlam0 hlam a₁ b₁ a₂ b₂ h20 hab₁ hmid hab₂
  obtain ⟨T₁, hT₁, T₂, hT₂, hcount⟩ := hmain lam hlam0 hlam a₁ b₁ a₂ b₂ h20 hab₁ hmid hab₂
  refine ⟨T₁, hT₁, T₂, hT₂, fun n hn => ?_⟩
  have h1 := hcount n hn
  have h2 := three_mul_xiOddFiberCount_le T₂
  have hR : (3 : ℝ) * (n : ℝ)
      ≤ 2 * (xiSingletonFiberCount T₂ : ℝ) + (xiPosZeroCount T₂ : ℝ) := by
    have : 3 * n ≤ 2 * xiSingletonFiberCount T₂ + xiPosZeroCount T₂ := by omega
    exact_mod_cast this
  linarith

end RHTower

end
