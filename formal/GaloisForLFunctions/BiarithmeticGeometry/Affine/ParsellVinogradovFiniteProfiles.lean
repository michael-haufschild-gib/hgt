import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovSmoothCovering
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovCutoffProfiles
import GaloisForLFunctions.BiarithmeticGeometry.Affine.IntegerOrderedPartitions

/-!
# A finite family of normalized covering profiles

An ordered cutoff on an integer interval depends, in its own frame, only
on its distance from the interval's lower endpoint. Displacements at least
four times the grid density give zero product with the leading cutoff.
Truncating those factors leaves only `4 * (q + 1)` possible profiles,
independent of scale, direction, and the size of the covering grid.
-/

open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.CoordinateCubeCutoff
open GaloisForLFunctions.BiarithmeticGeometry.FiniteOrderedPartitions
open GaloisForLFunctions.BiarithmeticGeometry.IntegerWindowCounts

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- A finite list of prefix lengths sufficient for normalized ordered cutoffs. -/
def cutoffProfileIndices (q : ℕ) : Finset ℤ := Finset.Icc 0 (4 * (q + 1 : ℤ) - 1)

/-- The finite profile family has cardinality four times the grid density. -/
theorem card_cutoffProfileIndices (q : ℕ) :
    (cutoffProfileIndices q).card = 4 * (q + 1) := by
  rw [cutoffProfileIndices, Int.card_Icc]
  omega

/-- In its own frame, an ordered covering weight is a prefix profile. -/
theorem coveringWeight_comp_frame_profile (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i : ℤ) (hi : i ∈ dimensionCoveringGrid r q ε)
    (x : AffineAxisSpace r k) :
    coveringWeight r k q ε δ i
      (momentFrame r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) x) =
        cutoffProfile r k q
          (i + ⌊(q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) / |ε| + 1⌋) x := by
  have hi' := (Finset.mem_Icc.mp hi).2
  unfold coveringWeight dimensionCoveringGrid integerWindow
  rw [orderedWeight_Icc _ _ i hi', frameCutoff_comp_frame r k ε hε]
  unfold cutoffProfile
  rw [show i - (0 - ⌊(q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) / |ε| + 1⌋) =
    i + ⌊(q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) / |ε| + 1⌋ by omega]
  congr 1
  apply Finset.prod_congr rfl
  intro m _
  rw [frameCutoff_integer_parallelFrame r k q ε hε]
  have hm : ((i : ℝ) - ((i - m : ℤ) : ℝ)) / (q + 1 : ℝ) =
      (m : ℝ) / (q + 1 : ℝ) := by rw [Int.cast_sub]; ring
  rw [hm]

/-- All normalized factors at displacement at least four grid-density units can be deleted. -/
theorem cutoffProfile_truncate (r k q : ℕ) (L : ℤ) :
    cutoffProfile r (k + 1) q L =
      cutoffProfile r (k + 1) q (min L (4 * (q + 1 : ℤ) - 1)) := by
  funext x
  apply mul_prod_Icc_truncate
  intro m hm
  have hd : (0 : ℝ) < q + 1 := by positivity
  have hm' : (4 : ℝ) * (q + 1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (show (4 : ℤ) * (q + 1 : ℤ) ≤ m by omega)
  have ht : 4 ≤ |(m : ℝ) / (q + 1 : ℝ)| :=
    ((le_div_iff₀ hd).mpr hm').trans (le_abs_self _)
  exact cubeCutoff_mul_vertical_translate_eq_zero r k _ ht x

/-- Every ordered cutoff belongs to one fixed finite profile family after normalization. -/
theorem exists_cutoffProfile_of_coveringWeight (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i : ℤ) (hi : i ∈ dimensionCoveringGrid r q ε) :
    ∃ N ∈ cutoffProfileIndices q, ∀ x : AffineAxisSpace r (k + 1),
      coveringWeight r (k + 1) q ε δ i
        (momentFrame r (k + 1) ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) x) =
          cutoffProfile r (k + 1) q N x := by
  have hi' := (Finset.mem_Icc.mp hi).1
  have hL : 0 ≤ i + ⌊(q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) / |ε| + 1⌋ := by
    change 0 - ⌊(q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) / |ε| + 1⌋ ≤ i at hi'
    omega
  refine ⟨min (i + ⌊(q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) / |ε| + 1⌋)
    (4 * (q + 1 : ℤ) - 1), ?_, ?_⟩
  · apply Finset.mem_Icc.mpr
    exact ⟨le_min hL (by omega), min_le_right _ _⟩
  · intro x
    rw [coveringWeight_comp_frame_profile r (k + 1) q ε hε δ i hi]
    exact congrFun (cutoffProfile_truncate r k q _) x

/-- At unit grid density, four fixed profiles suffice for every nondegenerate covering. -/
theorem exists_four_cutoffProfiles (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i : ℤ) (hi : i ∈ dimensionCoveringGrid r 0 ε) :
    ∃ N ∈ Finset.Icc (0 : ℤ) 3, ∀ x : AffineAxisSpace r (k + 1),
      coveringWeight r (k + 1) 0 ε δ i (momentFrame r (k + 1) ε δ (ε * (i : ℝ)) x) =
        cutoffProfile r (k + 1) 0 N x := by
  simpa only [cutoffProfileIndices, Nat.cast_zero, zero_add, mul_one, div_one,
    show (4 : ℤ) - 1 = 3 by norm_num] using
      exists_cutoffProfile_of_coveringWeight r k 0 ε hε δ i hi


end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
