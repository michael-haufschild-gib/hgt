import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheDetectorMomentErrorsAreSmall

/-!
# Three fixed profiles suffice for the detector main term

Every frozen-displacement main jet is quadratic in the mollifier weights.
Writing `S_n=(log n/log N)w_n` and `α=λ log N`, the correction and residual
weights are `−αS` and `w+αS`. Quadratic interpolation reduces the detector
main term to the three fixed weight families `w`, `S`, and `w+S`.
-/

open Complex Metric Set

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

theorem holomorphicGcdSum_scale (a b : ℂ) (N : ℕ) (w : ℕ → ℝ) (α : ℝ) :
    holomorphicGcdSum a b N (fun n => α * w n) =
      ((α ^ 2 : ℝ) : ℂ) * holomorphicGcdSum a b N w := by
  unfold holomorphicGcdSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-- Quadratic interpolation avoids any varying-profile convergence assumption. -/
theorem holomorphicGcdSum_affine (a b : ℂ) (N : ℕ) (w s : ℕ → ℝ) (α : ℝ) :
    holomorphicGcdSum a b N (fun n => w n + α * s n) =
      ((1 - α : ℝ) : ℂ) * holomorphicGcdSum a b N w +
        ((α ^ 2 - α : ℝ) : ℂ) * holomorphicGcdSum a b N s +
        (α : ℂ) * holomorphicGcdSum a b N (fun n => w n + s n) := by
  unfold holomorphicGcdSum
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_pow, Complex.ofReal_one]
  ring

theorem holomorphicTwistedMomentMain_scale (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ) (α : ℝ) (z : ℂ) :
    holomorphicTwistedMomentMain p q η N (fun n => α * w n) z =
      ((α ^ 2 : ℝ) : ℂ) * holomorphicTwistedMomentMain p q η N w z := by
  unfold holomorphicTwistedMomentMain
  rw [holomorphicGcdSum_scale, holomorphicGcdSum_scale]
  ring

theorem holomorphicTwistedMomentMain_affine (p q η : ℝ) (N : ℕ)
    (w s : ℕ → ℝ) (α : ℝ) (z : ℂ) :
    holomorphicTwistedMomentMain p q η N (fun n => w n + α * s n) z =
      ((1 - α : ℝ) : ℂ) * holomorphicTwistedMomentMain p q η N w z +
        ((α ^ 2 - α : ℝ) : ℂ) * holomorphicTwistedMomentMain p q η N s z +
        (α : ℂ) * holomorphicTwistedMomentMain p q η N (fun n => w n + s n) z := by
  unfold holomorphicTwistedMomentMain
  rw [holomorphicGcdSum_affine, holomorphicGcdSum_affine]
  ring

/-- Scaling weights scales every frozen main jet quadratically. -/
theorem realTwistedMomentMainJet_scale (p q η : ℝ) (N : ℕ) (w : ℕ → ℝ)
    (α : ℝ) (j : ℕ) (d : ℝ) :
    realTwistedMomentMainJet p q η N (fun n => α * w n) j d =
      α ^ 2 * realTwistedMomentMainJet p q η N w j d := by
  have he : holomorphicTwistedMomentMain p q η N (fun n => α * w n) =
      fun z => ((α ^ 2 : ℝ) : ℂ) * holomorphicTwistedMomentMain p q η N w z :=
    funext (holomorphicTwistedMomentMain_scale p q η N w α)
  unfold realTwistedMomentMainJet
  rw [he, iteratedDeriv_const_mul_field]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The same quadratic interpolation holds after every displacement derivative. -/
theorem realTwistedMomentMainJet_affine {p q η : ℝ} (hη : 0 < η) (hp : 4 ≤ p - η)
    (N : ℕ) (w s : ℕ → ℝ) (α : ℝ) {d : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20) (j : ℕ) :
    realTwistedMomentMainJet p q η N (fun n => w n + α * s n) j d =
      (1 - α) * realTwistedMomentMainJet p q η N w j d +
        (α ^ 2 - α) * realTwistedMomentMainJet p q η N s j d +
        α * realTwistedMomentMainJet p q η N (fun n => w n + s n) j d := by
  have hf (v : ℕ → ℝ) : ContDiffAt ℂ j (holomorphicTwistedMomentMain p q η N v) (d : ℂ) :=
    ((differentiableOn_holomorphicTwistedMomentMain hη hp N v hd hd20).analyticOnNhd
      isOpen_ball (d : ℂ) (mem_ball_self hd)).contDiffAt
  have h0 := (hf w).const_mul ((1 - α : ℝ) : ℂ)
  have h1 := (hf s).const_mul ((α ^ 2 - α : ℝ) : ℂ)
  have h2 := (hf (fun n => w n + s n)).const_mul (α : ℂ)
  have he : holomorphicTwistedMomentMain p q η N (fun n => w n + α * s n) =
      (fun z => ((1 - α : ℝ) : ℂ) * holomorphicTwistedMomentMain p q η N w z) +
        (fun z => ((α ^ 2 - α : ℝ) : ℂ) * holomorphicTwistedMomentMain p q η N s z) +
        (fun z => (α : ℂ) * holomorphicTwistedMomentMain p q η N (fun n => w n + s n) z) :=
    funext (holomorphicTwistedMomentMain_affine p q η N w s α)
  unfold realTwistedMomentMainJet
  rw [he, iteratedDeriv_add (h0.add h1) h2, iteratedDeriv_add h0 h1]
  simp only [iteratedDeriv_const_mul_field, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Weights corresponding to multiplication of a profile by `1−x`. -/
def detectorComplementWeights (N : ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Real.log n / Real.log N) * w n

/-- The literal detector main term involves only three fixed weight families. -/
theorem detectorThreeMomentMain_three_weights {p q η : ℝ} (hη : 0 < η) (hp : 4 ≤ p - η)
    {N : ℕ} (hN : 1 < N) (w : ℕ → ℝ) {d : ℝ} (hd : 0 < d) (hd20 : d ≤ 1 / 20) (lam : ℝ) :
    detectorThreeMomentMain p q η N w d lam =
      (1 - lam * Real.log N) * realTwistedMomentMainJet p q η N w 0 d +
        ((lam * Real.log N) ^ 2 - lam * Real.log N) *
          realTwistedMomentMainJet p q η N (detectorComplementWeights N w) 0 d +
        (lam * Real.log N) *
          realTwistedMomentMainJet p q η N (fun n => w n + detectorComplementWeights N w n) 0 d -
        lam / 2 *
          ((2 - lam * Real.log N) * realTwistedMomentMainJet p q η N w 1 d -
            (lam * Real.log N) * realTwistedMomentMainJet p q η N (detectorComplementWeights N w) 1 d +
            (lam * Real.log N) *
              realTwistedMomentMainJet p q η N (fun n => w n + detectorComplementWeights N w n) 1 d) +
        lam ^ 2 / 4 * realTwistedMomentMainJet p q η N w 2 d := by
  have hL : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hc : detectorCorrectionWeights lam w =
      fun n => (-(lam * Real.log N)) * detectorComplementWeights N w n := by
    funext n
    unfold detectorCorrectionWeights detectorComplementWeights
    field_simp [hL] <;> ring
  have hr : detectorResidualWeights lam w =
      fun n => w n + (lam * Real.log N) * detectorComplementWeights N w n := by
    funext n
    unfold detectorResidualWeights detectorComplementWeights
    field_simp [hL] <;> ring
  unfold detectorThreeMomentMain
  rw [hc, hr, realTwistedMomentMainJet_scale,
    realTwistedMomentMainJet_affine hη hp N w (detectorComplementWeights N w) _ hd hd20 0,
    realTwistedMomentMainJet_affine hη hp N w (detectorComplementWeights N w) _ hd hd20 1]
  ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
