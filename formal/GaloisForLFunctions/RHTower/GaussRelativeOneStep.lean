import GaloisForLFunctions.RHTower.GaussDoubleDefect
import GaloisForLFunctions.RHTower.GaussPrincipalStepBlock
import GaloisForLFunctions.RHTower.GaussSandwich
import GaloisForLFunctions.RHTower.GaussRelativeDiagonal

/-!
# The principal step is self-adjoint and relatively close to the moving amplitude

Two facts about the principal step `R = B S B⁻² S* B` at a fixed frequency.

It is self-adjoint: the outer and inner prime-scale blocks are multiplications by real symbols,
and the two normalized shifted blocks are mutually adjoint, because their Fourier symbols are
conjugate ratios of the sampled component.

And its action on the constant function converges to the moving amplitude *relatively*: the
`L²` deviation `‖R·1 - a_δ‖` itself tends to zero along every escaping frequency sequence, with
no step scalar in front.  The deviation splits into three vectors: the unconjugated defect at the
model intermediate, the double defect, and a contraction of the conjugate defect — the first and
third are single moving-translation estimates, the second is the double-defect estimate, and all
three require only `m ≥ 2` through the latter.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology

noncomputable section

/-! ## The two normalized shifted blocks are mutually adjoint -/

theorem gaussShiftedBlockDiag_inner {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (i : ℤ)
    (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (gaussShiftedBlockDiag hm k p i u) v : ℂ)
      = inner ℂ u (gaussShiftedBlockOf hm k p i v) := by
  rw [gaussShiftedBlockDiag, gaussShiftedBlockOf, inner_smul_left, inner_smul_right]
  have hmove : ∀ x y : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))),
      (inner ℂ (fourierMulBlock (-i) x) y : ℂ) = inner ℂ x (fourierMulBlock i y) := by
    intro x y
    have h := fourierMulBlock_inner i (fourierMulBlock (-i) x) y
    rw [fourierMulBlock_neg_apply] at h
    exact h.symm
  have hmove' : ∀ x y : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))),
      (inner ℂ x (fourierMulBlock (-i) y) : ℂ) = inner ℂ (fourierMulBlock i x) y := by
    intro x y
    rw [← inner_conj_symm, hmove, inner_conj_symm]
  rw [hmove, gaussDiagonalBlock_inner hm k p, ← hmove']
  rw [map_inv₀]

theorem gaussShiftedBlockOf_inner {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (i : ℤ)
    (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (gaussShiftedBlockOf hm k p i u) v : ℂ)
      = inner ℂ u (gaussShiftedBlockDiag hm k p i v) := by
  have h := gaussShiftedBlockDiag_inner hm k p i v u
  calc (inner ℂ (gaussShiftedBlockOf hm k p i u) v : ℂ)
      = starRingEnd ℂ (inner ℂ v (gaussShiftedBlockOf hm k p i u)) :=
        (inner_conj_symm _ _).symm
    _ = starRingEnd ℂ (inner ℂ (gaussShiftedBlockDiag hm k p i v) u) := by rw [h]
    _ = inner ℂ u (gaussShiftedBlockDiag hm k p i v) := inner_conj_symm _ _

/-! ## The principal step and the moving amplitude are self-adjoint -/

/-- **The principal step is self-adjoint.** -/
theorem gaussPrincipalStepBlock_inner {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i : ℤ)
    (f g : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (gaussPrincipalStepBlock hm k p hp i f) g : ℂ)
      = inner ℂ f (gaussPrincipalStepBlock hm k p hp i g) := by
  rw [gaussPrincipalStepBlock_apply, gaussPrincipalStepBlock_apply,
    gaussPrimeScaleBlock_inner hp, gaussShiftedBlockDiag_inner hm k p,
    gaussPrimeScaleInvSqBlock_inner hp, gaussShiftedBlockOf_inner hm k p,
    gaussPrimeScaleBlock_inner hp]

theorem gaussMovingAmplitudeCircle_conj (p : ℝ) (δ : AddCircle (1 : ℝ))
    (z : AddCircle (1 : ℝ)) :
    starRingEnd ℂ (gaussMovingAmplitudeCircle p δ z) = gaussMovingAmplitudeCircle p δ z := by
  rw [gaussMovingAmplitudeCircle, map_mul, map_mul, gaussPrimeScaleCircle_real,
    gaussPrimeScaleInvSqCircle_real]

/-- **The moving amplitude is self-adjoint.** -/
theorem gaussMovingAmplitudeBlock_inner {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ))
    (f g : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (gaussMovingAmplitudeBlock hp δ f) g : ℂ)
      = inner ℂ f (gaussMovingAmplitudeBlock hp δ g) :=
  MeasureTheory.lpBoundedMulCLM_inner_real _ _ _ (gaussMovingAmplitudeCircle_conj p δ) f g

/-! ## The relative one-step law -/

/-- **Relative one-step law.**  For `m ≥ 2` the action of the principal step on the constant
function converges in `L²` to the moving amplitude, along every escaping frequency sequence and
with no step scalar in front. -/
theorem tendsto_norm_gaussPrincipalStep_one_sub_amplitude {m : ℕ} (hm2 : 2 ≤ m) (k : Fin m)
    (p : Nat.Primes) (hp : (1 : ℝ) < (p : ℝ)) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ =>
      ‖gaussPrincipalStepBlock (le_trans one_le_two hm2) k p hp (ι n) (fourierLp 2 0) -
        gaussMovingAmplitudeBlock hp
          ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) (fourierLp 2 0)‖)
      atTop (nhds 0) := by
  have hm1 : 1 ≤ m := le_trans one_le_two hm2
  set b : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleBlock hp (fourierLp 2 0) with hbdef
  -- the three-vector split of the deviation
  have hsplit : ∀ n : ℕ,
      gaussPrincipalStepBlock hm1 k p hp (ι n) (fourierLp 2 0) -
        gaussMovingAmplitudeBlock hp
          ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) (fourierLp 2 0)
      = gaussPrimeScaleBlock hp
          ((gaussShiftedBlockDiag hm1 k p (ι n)
              (gaussPrimeScaleInvSqBlock hp
                (gaussRotationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) b)) -
            gaussRotationBlockInv ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
              (gaussPrimeScaleInvSqBlock hp
                (gaussRotationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) b))) +
          (gaussDoubleDefectVector hm1 k p hp (ι n) +
            gaussRotationBlockInv ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
              (gaussPrimeScaleInvSqBlock hp
                (gaussShiftedBlockOf hm1 k p (ι n) b -
                  gaussRotationBlock
                    ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) b)))) := by
    intro n
    set δ : AddCircle (1 : ℝ) := ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) with hδ
    have hR : gaussPrincipalStepBlock hm1 k p hp (ι n) (fourierLp 2 0)
        = gaussPrimeScaleBlock hp
            (gaussShiftedBlockDiag hm1 k p (ι n)
              (gaussPrimeScaleInvSqBlock hp
                (gaussShiftedBlockOf hm1 k p (ι n) b))) := by
      rw [gaussPrincipalStepBlock_apply, hbdef]
    have hM : gaussMovingAmplitudeBlock hp δ (fourierLp 2 0)
        = gaussPrimeScaleBlock hp
            (gaussRotationBlockInv δ
              (gaussPrimeScaleInvSqBlock hp (gaussRotationBlock δ b))) := by
      rw [← gaussPrimeScaleBlock_translate_invSq_translate hp δ (fourierLp 2 0),
        gaussRotationBlock_eq_translation, gaussRotationBlockInv_eq_translation, hbdef]
    rw [hR, hM, ← map_sub]
    congr 1
    rw [gaussDoubleDefectVector, ← hδ, ← hbdef]
    have hadd : gaussShiftedBlockDiag hm1 k p (ι n)
        (gaussPrimeScaleInvSqBlock hp (gaussShiftedBlockOf hm1 k p (ι n) b))
        = gaussShiftedBlockDiag hm1 k p (ι n)
            (gaussPrimeScaleInvSqBlock hp
              (gaussShiftedBlockOf hm1 k p (ι n) b - gaussRotationBlock δ b)) +
          gaussShiftedBlockDiag hm1 k p (ι n)
            (gaussPrimeScaleInvSqBlock hp (gaussRotationBlock δ b)) := by
      have h := gaussShiftedBlockDiag_sub hm1 k p (ι n)
        (gaussPrimeScaleInvSqBlock hp (gaussShiftedBlockOf hm1 k p (ι n) b))
        (gaussPrimeScaleInvSqBlock hp (gaussRotationBlock δ b))
      rw [← map_sub] at h
      rw [sub_eq_iff_eq_add] at h
      rw [h]
    rw [hadd]
    abel
  -- the three deviations vanish
  have hT1 : Tendsto (fun n : ℕ =>
      ‖gaussShiftedBlockDiag hm1 k p (ι n)
          (gaussPrimeScaleInvSqBlock hp
            (gaussRotationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) b)) -
        gaussRotationBlockInv ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
          (gaussPrimeScaleInvSqBlock hp
            (gaussRotationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) b))‖)
      atTop (nhds 0) := by
    have hdecay : ∀ (n : ℕ) (j : ℤ),
        ‖fourierCoeff ((gaussPrimeScaleInvSqBlock hp
            (gaussRotationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) b) :
              AddCircle (1 : ℝ) → ℂ)) j‖
          ≤ 4 * (p : ℝ) / (1 + (j.natAbs : ℝ)) := by
      intro n j
      have h1pow : (gaussMovingAmplitudeBlock hp
          ((Int.fract (gaussSamplePhase m p (ι n)) : ℝ) : AddCircle (1 : ℝ)) ^ 0)
          (fourierLp 2 0)
          = (fourierLp 2 0 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) := by
        rw [pow_zero]
        rfl
      have hb := norm_fourierCoeff_gaussIntermediate_amplitudePow hp
        (Int.fract_nonneg (gaussSamplePhase m p (ι n)))
        (Int.fract_lt_one (gaussSamplePhase m p (ι n))) 0 j
      rw [h1pow, zero_add, pow_one] at hb
      rw [gaussRotationBlock_eq_translation, ← coe_fract_eq, hbdef]
      exact hb
    have h := tendsto_norm_gaussShiftedBlockDiag_sub_rotationInv_family hm1 k p hι
      (fun n : ℕ => gaussPrimeScaleInvSqBlock hp
        (gaussRotationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) b))
      (A := 4 * (p : ℝ)) hdecay
    exact h
  have hT2 : Tendsto (fun n : ℕ =>
      ‖gaussDoubleDefectVector hm1 k p hp (ι n)‖) atTop (nhds 0) := by
    have h := tendsto_norm_gaussDoubleDefectVector_comp hm2 k p hp hι
    exact h
  have hT3 : Tendsto (fun n : ℕ =>
      ‖gaussRotationBlockInv ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
          (gaussPrimeScaleInvSqBlock hp
            (gaussShiftedBlockOf hm1 k p (ι n) b -
              gaussRotationBlock
                ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) b))‖)
      atTop (nhds 0) := by
    have hfold := tendsto_gaussFoldDefect hm1 k p hp hι
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hfold
    set δ : AddCircle (1 : ℝ) := ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) with hδ
    have hrot : ‖gaussRotationBlockInv δ
        (gaussPrimeScaleInvSqBlock hp
          (gaussShiftedBlockOf hm1 k p (ι n) b - gaussRotationBlock δ b))‖
        = ‖gaussPrimeScaleInvSqBlock hp
            (gaussShiftedBlockOf hm1 k p (ι n) b - gaussRotationBlock δ b)‖ := by
      rw [gaussRotationBlockInv_eq_translation]
      exact (gaussTranslationBlock (-δ)).norm_map _
    rw [hrot]
    have hcontr : ‖gaussPrimeScaleInvSqBlock hp
        (gaussShiftedBlockOf hm1 k p (ι n) b - gaussRotationBlock δ b)‖
        ≤ ‖gaussShiftedBlockOf hm1 k p (ι n) b - gaussRotationBlock δ b‖ := by
      refine ((gaussPrimeScaleInvSqBlock hp).le_opNorm _).trans ?_
      refine le_trans (mul_le_mul_of_nonneg_right
        (norm_gaussPrimeScaleInvSqBlock_le hp) (norm_nonneg _)) ?_
      rw [one_mul]
    refine hcontr.trans (le_of_eq ?_)
    rw [gaussFoldDefect, gaussRotationBlock_eq_translation, hbdef]
  -- assemble
  have hdom : Tendsto (fun n : ℕ =>
      Real.sqrt (p : ℝ) *
        (‖gaussShiftedBlockDiag hm1 k p (ι n)
            (gaussPrimeScaleInvSqBlock hp
              (gaussRotationBlock ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) b)) -
          gaussRotationBlockInv ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
            (gaussPrimeScaleInvSqBlock hp
              (gaussRotationBlock
                ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) b))‖ +
          (‖gaussDoubleDefectVector hm1 k p hp (ι n)‖ +
            ‖gaussRotationBlockInv ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ))
              (gaussPrimeScaleInvSqBlock hp
                (gaussShiftedBlockOf hm1 k p (ι n) b -
                  gaussRotationBlock
                    ((gaussSamplePhase m p (ι n) : ℝ) : AddCircle (1 : ℝ)) b))‖)))
      atTop (nhds 0) := by
    have hsum := hT1.add (hT2.add hT3)
    rw [add_zero, add_zero] at hsum
    have := hsum.const_mul (Real.sqrt (p : ℝ))
    simpa using this
  refine squeeze_zero_norm' ?_ hdom
  filter_upwards with n
  rw [hsplit n, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine le_trans ((gaussPrimeScaleBlock hp).le_opNorm _) ?_
  refine le_trans (mul_le_mul_of_nonneg_right (norm_gaussPrimeScaleBlock_le hp)
    (norm_nonneg _)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (norm_add_le _ _).trans ?_
  exact add_le_add le_rfl (norm_add_le _ _)

end

end RHTower
