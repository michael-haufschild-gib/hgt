import GaloisForLFunctions.HTGeometry.GaussianCoordinateStripSampling
import Mathlib.Data.Finset.Max

/-!
# Sampling finite packets without suppressing multiplicities

A maximizing representative in each occupied cell bounds the whole packet.
The exact number of samples in that cell remains as a factor.
-/

open scoped Real NNReal
noncomputable section
namespace GaloisForLFunctions

/-- A single in-cell grid controls every finite packet, with all cell multiplicities retained. -/
theorem exists_gaussianPacket_maximizing_grid {ι : Type*} (F : Finset ι)
    (cell : ι → ℕ) (P : Polynomial ℝ) (R : ℝ≥0) (a : ℝ) (h : ℝ≥0)
    (s : ι → Set.Icc (0 : ℝ) 1) (δ : ι → Set.Icc (-(R : ℝ)) R) :
    ∃ s' : ℕ → Set.Icc (0 : ℝ) 1,
      ∃ δ' : ℕ → Set.Icc (-(R : ℝ)) R,
        (∑ q ∈ F, ‖entirePolynomialGaussianVerticalError P
          (a + ((cell q : ℝ) + (s q : ℝ)) * h) (δ q)‖ ^ 2) ≤
        ∑ j ∈ Finset.range (F.sup cell + 1),
          ((F.filter (fun q => cell q = j)).card : ℝ) *
            ‖entirePolynomialGaussianVerticalError P
              (a + ((j : ℝ) + (s' j : ℝ)) * h) (δ' j)‖ ^ 2 := by
  classical
  let e (q : ι) := ‖entirePolynomialGaussianVerticalError P
    (a + ((cell q : ℝ) + (s q : ℝ)) * h) (δ q)‖ ^ 2
  have hex (j : ℕ) : ∃ x : Set.Icc (0 : ℝ) 1,
      ∃ y : Set.Icc (-(R : ℝ)) R,
      ∀ q ∈ F, cell q = j →
        e q ≤ ‖entirePolynomialGaussianVerticalError P
          (a + ((j : ℝ) + (x : ℝ)) * h) y‖ ^ 2 := by
    by_cases hn : (F.filter (fun q => cell q = j)).Nonempty
    · obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image
        (F.filter (fun q => cell q = j)) e hn
      refine ⟨s p, δ p, fun q hq hj => ?_⟩
      have hm := hmax q (Finset.mem_filter.mpr ⟨hq, hj⟩)
      have hpj := (Finset.mem_filter.mp hp).2
      simpa only [e, hpj] using hm
    · refine ⟨⟨0, by simp⟩, ⟨0, neg_nonpos.mpr R.coe_nonneg, R.coe_nonneg⟩, ?_⟩
      intro q hq hj
      exact False.elim (hn ⟨q, Finset.mem_filter.mpr ⟨hq, hj⟩⟩)
  choose s' δ' hs using hex
  refine ⟨s', δ', ?_⟩
  have hmaps : ∀ q ∈ F, cell q ∈ Finset.range (F.sup cell + 1) := by
    intro q hq
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hq))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ ∑ _q ∈ F.filter (fun q => cell q = j),
        ‖entirePolynomialGaussianVerticalError P
          (a + ((j : ℝ) + (s' j : ℝ)) * h) (δ' j)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      exact hs j q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end GaloisForLFunctions
