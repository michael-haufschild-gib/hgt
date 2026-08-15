import GaloisForLFunctions.RHTower.GaussCubicRelativeErrorBound
import GaloisForLFunctions.RHTower.GaussIteratedAmplitude

/-!
# Smooth cubic sandwich reduction

Both principal and model steps are positive sandwiches through the inverse-square multiplier.  The
smooth part of the cubic deviation therefore reduces to one ordinary shifted-block error, while
all nonsmooth propagation remains isolated in `gaussCubicPropagatedRelativeErrorVector`.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology

noncomputable section

theorem gaussTranslationBlock_add (δ ε : AddCircle (1 : ℝ))
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussTranslationBlock δ (gaussTranslationBlock ε u) = gaussTranslationBlock (δ + ε) u := by
  refine (fourierBasis (T := (1 : ℝ))).repr.injective ?_
  refine lp.ext (funext fun j => ?_)
  rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_gaussTranslationBlock,
    fourierCoeff_gaussTranslationBlock, fourierCoeff_gaussTranslationBlock,
    GaloisForLFunctions.fourier_add_arg]
  ring

theorem gaussTranslationBlock_zero
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussTranslationBlock 0 u = u := by
  refine (fourierBasis (T := (1 : ℝ))).repr.injective ?_
  refine lp.ext (funext fun j => ?_)
  rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_gaussTranslationBlock]
  simp [fourier_apply]

theorem gaussTranslationBlock_neg_comp (δ : AddCircle (1 : ℝ))
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussTranslationBlock δ (gaussTranslationBlock (-δ) u) = u := by
  rw [gaussTranslationBlock_add, add_neg_cancel, gaussTranslationBlock_zero]

theorem gaussTranslationBlock_inner (δ : AddCircle (1 : ℝ))
    (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (gaussTranslationBlock δ u) v : ℂ) =
      inner ℂ u (gaussTranslationBlock (-δ) v) := by
  calc
    (inner ℂ (gaussTranslationBlock δ u) v : ℂ) =
        inner ℂ (gaussTranslationBlock δ u)
          (gaussTranslationBlock δ (gaussTranslationBlock (-δ) v)) := by
      rw [gaussTranslationBlock_neg_comp]
    _ = inner ℂ u (gaussTranslationBlock (-δ) v) :=
      (gaussTranslationBlock δ).inner_map_map _ _

/-- Principal step as an inverse-square quadratic sandwich, for every vector. -/
theorem inner_gaussPrincipalStepBlock_eq_sandwich
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ)
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ f (gaussPrincipalStepBlock hm k p hp i f) : ℂ) =
      inner ℂ
        (gaussShiftedBlockOf hm k p i (gaussPrimeScaleBlock hp f))
        (gaussPrimeScaleInvSqBlock hp
          (gaussShiftedBlockOf hm k p i (gaussPrimeScaleBlock hp f))) := by
  rw [gaussPrincipalStepBlock_apply]
  rw [← gaussPrimeScaleBlock_inner hp]
  rw [← gaussShiftedBlockOf_inner hm k p i]

/-- Moving-amplitude model as the matching translated inverse-square quadratic sandwich. -/
theorem inner_gaussMovingAmplitudeBlock_eq_sandwich
    {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ))
    (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ f (gaussMovingAmplitudeBlock hp δ f) : ℂ) =
      inner ℂ (gaussRotationBlock δ (gaussPrimeScaleBlock hp f))
        (gaussPrimeScaleInvSqBlock hp
          (gaussRotationBlock δ (gaussPrimeScaleBlock hp f))) := by
  rw [← gaussPrimeScaleBlock_translate_invSq_translate hp δ f]
  rw [← gaussPrimeScaleBlock_inner hp]
  rw [← gaussTranslationBlock_inner δ]
  rw [← gaussRotationBlock_eq_translation]

/-- Ordinary shifted-block error on the smooth model vector in the cubic expansion. -/
def gaussCubicSmoothShiftErrorVector {m : ℕ} (hm : 1 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  gaussShiftedBlockOf hm k p i
      (gaussPrimeScaleBlock hp (gaussMovingAmplitudeOneVector (m := m) p hp i)) -
    gaussRotationBlock ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
      (gaussPrimeScaleBlock hp (gaussMovingAmplitudeOneVector (m := m) p hp i))

/-- The smooth cubic shifted-block error vanishes along every escaping frequency sequence. -/
theorem tendsto_norm_gaussCubicSmoothShiftErrorVector
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ => ‖gaussCubicSmoothShiftErrorVector hm k p hp (ι n)‖)
      atTop (nhds 0) := by
  have hdecay : ∀ (n : ℕ) (j : ℤ),
      ‖fourierCoeff ((gaussPrimeScaleBlock hp
          (gaussMovingAmplitudeOneVector (m := m) p hp (ι n)) :
            AddCircle (1 : ℝ) → ℂ)) j‖ ≤
        4 * (p : ℝ) ^ 2 / (1 + (j.natAbs : ℝ)) := by
    intro n j
    rw [gaussMovingAmplitudeOneVector]
    have hb := norm_fourierCoeff_gaussPrimeScaleBlock_amplitudePow hp
      (Int.fract_nonneg (gaussSamplePhase m p (ι n)))
      (Int.fract_lt_one (gaussSamplePhase m p (ι n))) 1 j
    rw [pow_one, coe_fract_eq] at hb
    norm_num at hb ⊢
    exact hb
  have h := tendsto_norm_gaussShiftedBlockOf_sub_rotation_family hm k p hι
    (fun n : ℕ => gaussPrimeScaleBlock hp
      (gaussMovingAmplitudeOneVector (m := m) p hp (ι n))) hdecay
  exact h

end

end RHTower
