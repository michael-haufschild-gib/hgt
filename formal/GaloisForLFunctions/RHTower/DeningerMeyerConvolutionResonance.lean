import GaloisForLFunctions.RHTower.DeningerMeyerConvolutionTraceClass

/-! # Complete finite resonant blocks of an original source convolution

The resonant selector includes every Hasse slot above a resonant Xi point.
Trace-class diagonal summability proves finiteness unconditionally, and
block locality makes the selector commute with the full convolution.
-/

noncomputable section
open Complex Set Filter ContinuousLinearMap
open scoped Classical

namespace RHTower

def deningerHasseBlockProjection (S : Set XiDivisorSupport) :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert := by
  classical
  exact xiDivisorDiagonal (fun q => if q.1 ∈ S then 1 else 0)
    (C := 1) (by norm_num) (fun q => by split_ifs <;> norm_num)

@[simp] theorem deningerHasseBlockProjection_apply (S : Set XiDivisorSupport)
    (x : DeningerArithmeticJetHilbert) (q : DeningerArithmeticJetCoordinate) :
    deningerHasseBlockProjection S x q = if q.1 ∈ S then x q else 0 := by
  classical
  change (if q.1 ∈ S then (1 : ℂ) else 0)*x q = _
  split_ifs <;> simp

theorem deningerHasseBlockProjection_idempotent (S : Set XiDivisorSupport) :
    (deningerHasseBlockProjection S).comp (deningerHasseBlockProjection S) =
      deningerHasseBlockProjection S := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext q
  change deningerHasseBlockProjection S (deningerHasseBlockProjection S x) q =
    deningerHasseBlockProjection S x q
  by_cases hq : q.1 ∈ S <;>
    simp only [deningerHasseBlockProjection_apply, hq, ↓reduceIte]

theorem deningerMeyerHilbertConvolution_blockProjection (g : DeningerMeyerStrongLogTarget)
    (S : Set XiDivisorSupport) (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHilbertConvolution g (deningerHasseBlockProjection S x) q =
      if q.1 ∈ S then deningerMeyerHilbertConvolution g x q else 0 := by
  classical
  rw [deningerMeyerHilbertConvolution_jets]
  by_cases hq : q.1 ∈ S
  · simp only [deningerHasseBlockProjection_apply, deningerHasseLower, hq, ↓reduceIte]
    exact (deningerMeyerHilbertConvolution_jets g x q).symm
  · simp [deningerHasseBlockProjection_apply, deningerHasseLower, hq]

theorem deningerMeyerHilbertConvolution_comm_blockProjection (g : DeningerMeyerStrongLogTarget)
    (S : Set XiDivisorSupport) :
    (deningerMeyerHilbertConvolution g).comp (deningerHasseBlockProjection S) =
      (deningerHasseBlockProjection S).comp (deningerMeyerHilbertConvolution g) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext q
  exact (deningerMeyerHilbertConvolution_blockProjection g S x q).trans
    (deningerHasseBlockProjection_apply S _ q).symm

def deningerMeyerConvolutionResonance (g : DeningerMeyerStrongLogTarget) : Set XiDivisorSupport :=
  {rho | 1 + deningerMeyerStrongLogMellin g (rho : ℂ) = 0}

/-- Even without a bound on multiplicities, only finitely many complete slots resonate. -/
theorem deningerMeyerConvolutionResonance_copies_finite (g : DeningerMeyerStrongLogTarget) :
    {q : XiZeroCopy | q.1 ∈ deningerMeyerConvolutionResonance g}.Finite := by
  have h := (Metric.tendsto_nhds.mp
    (deningerMeyerHilbertConvolution_summable_diagonal g).tendsto_cofinite_zero) (1/2) (by norm_num)
  simp only [dist_zero_right] at h
  apply (Filter.eventually_cofinite.mp h).subset
  intro q hq
  have he : deningerMeyerStrongLogMellin g (q.1 : ℂ) = -1 := by
    have hz := hq
    change 1 + deningerMeyerStrongLogMellin g (q.1 : ℂ) = 0 at hz
    linear_combination hz
  simp only [Set.mem_setOf_eq, he, norm_neg, norm_one]
  norm_num

theorem deningerMeyerConvolutionResonance_finite (g : DeningerMeyerStrongLogTarget) :
    (deningerMeyerConvolutionResonance g).Finite := by
  apply ((deningerMeyerConvolutionResonance_copies_finite g).image Sigma.fst).subset
  intro rho hrho
  exact ⟨⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩, hrho, rfl⟩

def deningerMeyerConvolutionResonantProjection (g : DeningerMeyerStrongLogTarget) :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  deningerHasseBlockProjection (deningerMeyerConvolutionResonance g)

/-- Replace precisely the complete resonant blocks by the identity. -/
def deningerMeyerConvolutionFredholmRepair (g : DeningerMeyerStrongLogTarget) :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  1 + (deningerMeyerHilbertConvolution g).comp
    (1 - deningerMeyerConvolutionResonantProjection g)

theorem deningerMeyerConvolutionFredholmRepair_apply (g : DeningerMeyerStrongLogTarget)
    (x : DeningerArithmeticJetHilbert) (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerConvolutionFredholmRepair g x q =
      if q.1 ∈ deningerMeyerConvolutionResonance g then x q
      else x q + deningerMeyerHilbertConvolution g x q := by
  classical
  change x q + deningerMeyerHilbertConvolution g
    (x - deningerHasseBlockProjection (deningerMeyerConvolutionResonance g) x) q = _
  rw [map_sub]
  change x q + (deningerMeyerHilbertConvolution g x q -
    deningerMeyerHilbertConvolution g
      (deningerHasseBlockProjection (deningerMeyerConvolutionResonance g) x) q) = _
  rw [deningerMeyerHilbertConvolution_blockProjection]
  split_ifs <;> simp

end RHTower
