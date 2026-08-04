import GaloisForLFunctions.HTGeometry.WaveDominationFactors
import GaloisForLFunctions.HTGeometry.WaveCauchyUniqueness

/-!
# Factor-wise domination is closed under differences

The dominating function the estimate needs is one for the difference of two solutions, while the
factor bounds are given for each solution separately. Adding the dominating functions bridges the
two: a difference is bounded by the sum of the bounds, and square integrability is preserved by
addition.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Sub

variable {d : ℕ} {u₁ u₂ : ℝ × (Fin d → ℝ) → ℝ}

theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + -b| := by rw [sub_eq_add_neg]
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

/-- **The dominating function for a difference, from factor bounds for each solution.** -/
theorem exists_bound_of_factor_memLp_sub (hu₁ : ContDiff ℝ ∞ u₁) (hu₂ : ContDiff ℝ ∞ u₂)
    (t : ℝ) {gT₁ gTT₁ gU₁ gT₂ gTT₂ gU₂ : (Fin d → ℝ) → ℝ}
    {gS₁ gST₁ gS₂ gST₂ : Fin d → (Fin d → ℝ) → ℝ}
    (hgT₁ : MemLp gT₁ 2 (volume : Measure (Fin d → ℝ)))
    (hgTT₁ : MemLp gTT₁ 2 (volume : Measure (Fin d → ℝ)))
    (hgU₁ : MemLp gU₁ 2 (volume : Measure (Fin d → ℝ)))
    (hgS₁ : ∀ i : Fin d, MemLp (gS₁ i) 2 (volume : Measure (Fin d → ℝ)))
    (hgST₁ : ∀ i : Fin d, MemLp (gST₁ i) 2 (volume : Measure (Fin d → ℝ)))
    (hgT₂ : MemLp gT₂ 2 (volume : Measure (Fin d → ℝ)))
    (hgTT₂ : MemLp gTT₂ 2 (volume : Measure (Fin d → ℝ)))
    (hgU₂ : MemLp gU₂ 2 (volume : Measure (Fin d → ℝ)))
    (hgS₂ : ∀ i : Fin d, MemLp (gS₂ i) 2 (volume : Measure (Fin d → ℝ)))
    (hgST₂ : ∀ i : Fin d, MemLp (gST₂ i) 2 (volume : Measure (Fin d → ℝ)))
    (hT₁ : ∀ s ∈ Metric.ball t 1, ∀ x, |waveDirDeriv (timeDir d) u₁ (s, x)| ≤ gT₁ x)
    (hTT₁ : ∀ s ∈ Metric.ball t 1, ∀ x,
      |waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u₁) (s, x)| ≤ gTT₁ x)
    (hU₁ : ∀ s ∈ Metric.ball t 1, ∀ x, |u₁ (s, x)| ≤ gU₁ x)
    (hS₁ : ∀ (i : Fin d), ∀ s ∈ Metric.ball t 1, ∀ x,
      |waveDirDeriv (spaceDir d i) u₁ (s, x)| ≤ gS₁ i x)
    (hST₁ : ∀ (i : Fin d), ∀ s ∈ Metric.ball t 1, ∀ x,
      |waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u₁) (s, x)| ≤ gST₁ i x)
    (hT₂ : ∀ s ∈ Metric.ball t 1, ∀ x, |waveDirDeriv (timeDir d) u₂ (s, x)| ≤ gT₂ x)
    (hTT₂ : ∀ s ∈ Metric.ball t 1, ∀ x,
      |waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u₂) (s, x)| ≤ gTT₂ x)
    (hU₂ : ∀ s ∈ Metric.ball t 1, ∀ x, |u₂ (s, x)| ≤ gU₂ x)
    (hS₂ : ∀ (i : Fin d), ∀ s ∈ Metric.ball t 1, ∀ x,
      |waveDirDeriv (spaceDir d i) u₂ (s, x)| ≤ gS₂ i x)
    (hST₂ : ∀ (i : Fin d), ∀ s ∈ Metric.ball t 1, ∀ x,
      |waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u₂) (s, x)| ≤ gST₂ i x) :
    ∃ bound : (Fin d → ℝ) → ℝ, Integrable bound (volume : Measure (Fin d → ℝ)) ∧
      ∀ s ∈ Metric.ball t 1, ∀ x : Fin d → ℝ,
        ‖waveDirDeriv (timeDir d) (energyDensity fun q => u₁ q - u₂ q) (s, x)‖ ≤ bound x := by
  have hsub : ∀ (v : ℝ × (Fin d → ℝ)) (p : ℝ × (Fin d → ℝ)),
      waveDirDeriv v (fun q => u₁ q - u₂ q) p
        = waveDirDeriv v u₁ p - waveDirDeriv v u₂ p :=
    fun v p => waveDirDeriv_sub hu₁ hu₂ v p
  have hsub2 : ∀ (v w : ℝ × (Fin d → ℝ)) (p : ℝ × (Fin d → ℝ)),
      waveDirDeriv v (waveDirDeriv w fun q => u₁ q - u₂ q) p
        = waveDirDeriv v (waveDirDeriv w u₁) p - waveDirDeriv v (waveDirDeriv w u₂) p := by
    intro v w p
    rw [waveDirDeriv_sub_fun hu₁ hu₂ w]
    exact waveDirDeriv_sub (contDiff_dirDeriv hu₁ w) (contDiff_dirDeriv hu₂ w) v p
  refine exists_bound_of_factor_memLp (hu₁.sub hu₂) t
    (gT := fun x => gT₁ x + gT₂ x) (gTT := fun x => gTT₁ x + gTT₂ x)
    (gU := fun x => gU₁ x + gU₂ x) (gS := fun i x => gS₁ i x + gS₂ i x)
    (gST := fun i x => gST₁ i x + gST₂ i x)
    (hgT₁.add hgT₂) (hgTT₁.add hgTT₂) (hgU₁.add hgU₂)
    (fun i => (hgS₁ i).add (hgS₂ i)) (fun i => (hgST₁ i).add (hgST₂ i))
    (fun s hs x => ?_) (fun s hs x => ?_) (fun s hs x => ?_)
    (fun i s hs x => ?_) (fun i s hs x => ?_)
  · rw [hsub]
    exact le_trans (abs_sub_le_add _ _) (add_le_add (hT₁ s hs x) (hT₂ s hs x))
  · rw [hsub2]
    exact le_trans (abs_sub_le_add _ _) (add_le_add (hTT₁ s hs x) (hTT₂ s hs x))
  · show |u₁ (s, x) - u₂ (s, x)| ≤ gU₁ x + gU₂ x
    exact le_trans (abs_sub_le_add _ _) (add_le_add (hU₁ s hs x) (hU₂ s hs x))
  · rw [hsub]
    exact le_trans (abs_sub_le_add _ _) (add_le_add (hS₁ i s hs x) (hS₂ i s hs x))
  · rw [hsub2]
    exact le_trans (abs_sub_le_add _ _) (add_le_add (hST₁ i s hs x) (hST₂ i s hs x))

end Sub

end GaloisForLFunctions.HTGeometry
