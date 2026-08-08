import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryExtension

/-!
# First-crossing law for shifted Xi Hankel faces

Far-right strict positivity means any loss of a fixed finite Hankel cone must be approached from
the right.  At such a one-sided local minimum, the exact null-quadratic derivative is nonnegative.
The terminal-flux identity then fixes the sign of the null polynomial's first omitted pairing.

For a first singular degree, the preceding block's positive definiteness also forces the null
polynomial to have nonzero leading coefficient.  Hence zero flux is equivalent to zero omitted
coupling, and any transversal crossing certifies failure of the next principal block.
-/

open Matrix
open Set

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- A differentiable function has nonnegative derivative at a one-sided local minimum on the
right half-line. -/
theorem hasDerivAt_nonneg_of_isLocalMinOn_Ici
    {f : ℝ → ℝ} {f' y : ℝ}
    (hd : HasDerivAt f f' y) (hmin : IsLocalMinOn f (Ici y) y) :
    0 ≤ f' := by
  have htan : (1 : ℝ) ∈ posTangentConeAt (Ici y) y := by
    rw [one_mem_posTangentConeAt_iff_mem_closure]
    have hinter : Ioi y ∩ Ici y = Ioi y := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Ici]
      constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, h.le⟩
    rw [hinter, closure_Ioi]
    exact self_mem_Ici
  have h := hmin.hasFDerivWithinAt_nonneg
    hd.hasFDerivAt.hasFDerivWithinAt htan
  simpa [hasDerivAt_iff_hasFDerivAt] using h

/-- At a right-hand first crossing, the leading coefficient and first omitted Xi pairing have
nonpositive product. -/
theorem xiShiftedHankelFirstCrossing_terminal_product_nonpos
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hmin : IsLocalMinOn
      (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c) (Ici y) y) :
    c (Fin.last n) * xiShiftedHankelFirstOmittedCoupling y (n + 1) c ≤ 0 := by
  have hd := hasDerivAt_xiShiftedMomentHankelQuadratic_of_kernel_succ hy n c hc
  have hnonneg := hasDerivAt_nonneg_of_isLocalMinOn_Ici hd hmin
  have hweight : 0 < 2 * (n : ℝ) + 1 := by positivity
  nlinarith

/-- A first singular shifted-Xi null polynomial has nonzero leading coefficient. -/
theorem xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0) :
    c (Fin.last n) ≠ 0 := by
  exact hankelNullVector_terminal_ne_zero_of_head_posDef
    (fun k => (xiShiftedReciprocalMoment y k).re) n c hhead hcne hc

/-- On a first singular degree, null flux vanishes exactly when the first omitted Xi coupling
vanishes. -/
theorem xiShiftedHankelNullFlux_eq_zero_iff_firstOmittedCoupling_eq_zero
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0) :
    (-(2 * (n : ℝ) + 1) * c (Fin.last n) *
        xiShiftedHankelFirstOmittedCoupling y (n + 1) c = 0) ↔
      xiShiftedHankelFirstOmittedCoupling y (n + 1) c = 0 := by
  have hweight : -(2 * (n : ℝ) + 1) ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt (by positivity))
  have hlead := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    y n c hhead hcne hc
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hprefix | hcoupling
    · rcases mul_eq_zero.mp hprefix with hw | hl
      · exact (hweight hw).elim
      · exact (hlead hl).elim
    · exact hcoupling
  · intro h
    rw [h]
    ring

/-- Any nonstationary null flux is a certificate that the next shifted-Xi principal block is not
positive semidefinite. -/
theorem xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_nullFlux_ne_zero
    (y : ℝ) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hflux : -(2 * (n : ℝ) + 1) * c (Fin.last n) *
      xiShiftedHankelFirstOmittedCoupling y (n + 1) c ≠ 0) :
    ¬ (xiShiftedMomentHankelMatrix y (n + 2)).PosSemidef := by
  apply xiShiftedMomentHankelMatrix_succ_not_posSemidef_of_kernel_of_coupling_ne_zero
    y (n + 1) c hc
  intro hcoupling
  apply hflux
  rw [hcoupling]
  ring

end

end RHTower
