import GaloisForLFunctions.RHTower.VonMangoldtHardyGramScaling

/-!
# Eventual strictness of the scaled von Mangoldt Hardy Gram

Every positive-scale source Gram is positive semidefinite.  For a finite packet of distinct
right-half-plane nodes, residue scaling independently proves that its determinant is eventually
nonzero as the scale approaches the Hardy boundary.  These two facts force eventual positive
definiteness, and hence strict positivity of the determinant.
-/

open scoped ComplexConjugate ComplexOrder
open Filter Set Complex

noncomputable section

namespace RHTower

/-- **Scaled von Mangoldt Hardy strictness law.**  Every finite distinct positive-node packet of
the scaled von Mangoldt source is eventually strictly positive definite at the Hardy boundary. -/
theorem eventually_scaledVonMangoldtPrimeRightHalfPlaneGram_posDef
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re)
    (hwinj : Function.Injective w) :
    ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      (scaledVonMangoldtPrimeRightHalfPlaneGram t w).PosDef := by
  filter_upwards
    [eventually_det_scaledVonMangoldtPrimeRightHalfPlaneGram_ne_zero w hw hwinj,
      self_mem_nhdsWithin] with t hdet ht
  exact ((scaledVonMangoldtPrimeRightHalfPlaneGram_posSemidef w hw ht).posDef_iff_det_ne_zero).2
    hdet

/-- The corresponding finite scaled von Mangoldt Gram determinant is eventually strictly
positive, not merely nonzero. -/
theorem eventually_det_scaledVonMangoldtPrimeRightHalfPlaneGram_pos
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re)
    (hwinj : Function.Injective w) :
    ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      0 < (scaledVonMangoldtPrimeRightHalfPlaneGram t w).det := by
  filter_upwards
    [eventually_scaledVonMangoldtPrimeRightHalfPlaneGram_posDef w hw hwinj] with t ht
  exact ht.det_pos

end RHTower
