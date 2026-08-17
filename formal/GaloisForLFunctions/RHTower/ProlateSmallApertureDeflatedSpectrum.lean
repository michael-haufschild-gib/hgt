import GaloisForLFunctions.RHTower.ProlateSmallApertureMomentField
import GaloisForLFunctions.HTGeometry.RectangularNuclearNormBound

/-!
# All-rung spectral gaps for moment-deflated small-aperture Fourier blocks

The preceding moment-field theorem gives operator-norm convergence of every
rescaled deflated Fourier synthesis to a nonzero rank-one operator.  This module
extracts the spectral content of that convergence.  Rectangular approximation
numbers are proved 1-Lipschitz and exactly homogeneous; consequently, at every
rung `k`, the first approximation number of the normalized block converges to a
strictly positive limit while the second converges to zero.  Their ratio tends
to zero, and both normalized and original deflated blocks have an eventual
strict top singular gap.

This is the first all-rung small-aperture result about the actual operator
spectrum rather than only its Taylor vectors.  The next frontier is the
hierarchical min--max step relating these deflated top singular branches to the
ordered singular branches of the undeflated even Slepian operator.
-/

open MeasureTheory Filter Topology Set Complex Metric

noncomputable section

namespace RHTower

section RectangularApproximationContinuity

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Every rectangular approximation number is 1-Lipschitz in operator norm. -/
theorem abs_rectApproxNumber_sub_le_norm_sub
    (T S : E →L[ℂ] F) (n : ℕ) :
    |rectApproxNumber T n - rectApproxNumber S n| ≤ ‖T - S‖ := by
  have hTS := rectApproxNumber_le_norm_sub_add T S n
  have hST := rectApproxNumber_le_norm_sub_add S T n
  rw [abs_le]
  constructor
  · rw [norm_sub_rev] at hST
    linarith
  · linarith

theorem lipschitzWith_rectApproxNumber (n : ℕ) :
    LipschitzWith 1 (fun T : E →L[ℂ] F => rectApproxNumber T n) := by
  apply LipschitzWith.of_dist_le_mul
  intro T S
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  exact abs_rectApproxNumber_sub_le_norm_sub T S n

theorem continuous_rectApproxNumber (n : ℕ) :
    Continuous (fun T : E →L[ℂ] F => rectApproxNumber T n) :=
  (lipschitzWith_rectApproxNumber (E := E) (F := F) n).continuous

theorem rectApproxNumber_eq_zero_of_hasRectRankLE
    {T : E →L[ℂ] F} {n : ℕ} (hT : HasRectRankLE T n) :
    rectApproxNumber T n = 0 := by
  apply le_antisymm
  · simpa using rectApproxNumber_le T n T hT
  · exact rectApproxNumber_nonneg T n

theorem HasRectRankLE.smul {T : E →L[ℂ] F} {n : ℕ}
    (hT : HasRectRankLE T n) (z : ℂ) :
    HasRectRankLE (z • T) n := by
  obtain ⟨V, hVfd, hVrank, hTV⟩ := hT
  exact ⟨V, hVfd, hVrank, fun x => V.smul_mem z (hTV x)⟩

theorem exists_hasRectRankLE_norm_sub_lt
    (T : E →L[ℂ] F) (n : ℕ) {ε : ℝ}
    (hε : rectApproxNumber T n < ε) :
    ∃ A : E →L[ℂ] F, HasRectRankLE A n ∧ ‖T - A‖ < ε := by
  obtain ⟨r, hrmem, hr⟩ :=
    (csInf_lt_iff (rectApproxNumber_set_bddBelow T n)
      (rectApproxNumber_set_nonempty T n)).mp hε
  obtain ⟨A, hA, rfl⟩ := hrmem
  exact ⟨A, hA, hr⟩

/-- Rectangular approximation numbers are exactly homogeneous. -/
theorem rectApproxNumber_smul (T : E →L[ℂ] F) (z : ℂ) (n : ℕ) :
    rectApproxNumber (z • T) n = ‖z‖ * rectApproxNumber T n := by
  have haux : ∀ (w : ℂ), w ≠ 0 → ∀ S : E →L[ℂ] F,
      rectApproxNumber (w • S) n ≤ ‖w‖ * rectApproxNumber S n := by
    intro w hw S
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
    obtain ⟨A, hA, hAlt⟩ := exists_hasRectRankLE_norm_sub_lt S n
      (lt_add_of_pos_right _ (by positivity : (0 : ℝ) < ε / ‖w‖))
    have hbound : rectApproxNumber (w • S) n ≤ ‖w • S - w • A‖ :=
      rectApproxNumber_le _ n _ (hA.smul w)
    rw [← smul_sub, norm_smul] at hbound
    calc
      rectApproxNumber (w • S) n ≤ ‖w‖ * ‖S - A‖ := hbound
      _ ≤ ‖w‖ * (rectApproxNumber S n + ε / ‖w‖) :=
        mul_le_mul_of_nonneg_left hAlt.le (norm_nonneg w)
      _ = ‖w‖ * rectApproxNumber S n + ε := by field_simp
  rcases eq_or_ne z 0 with rfl | hz
  · simp [rectApproxNumber_zero]
  · refine le_antisymm (haux z hz T) ?_
    have hinv := haux z⁻¹ (inv_ne_zero hz) (z • T)
    rw [smul_smul, inv_mul_cancel₀ hz, one_smul, norm_inv] at hinv
    have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    calc
      ‖z‖ * rectApproxNumber T n ≤
          ‖z‖ * (‖z‖⁻¹ * rectApproxNumber (z • T) n) :=
        mul_le_mul_of_nonneg_left hinv (norm_nonneg z)
      _ = rectApproxNumber (z • T) n := by field_simp

theorem rectApproxNumber_real_smul (T : E →L[ℂ] F) (r : ℝ) (n : ℕ) :
    rectApproxNumber (r • T) n = |r| * rectApproxNumber T n := by
  have hcast : r • T = (r : ℂ) • T := by
    ext x
    rfl
  rw [hcast, rectApproxNumber_smul, Complex.norm_real, Real.norm_eq_abs]

end RectangularApproximationContinuity

/-- The `k`th deflated Fourier synthesis, normalized by its first possible
small-aperture power. -/
noncomputable def normalizedApertureMomentSynthesis (k : ℕ) (c : ℝ) :
    UnitPhysicalScalarL2 →L[ℂ] UnitApertureL2 :=
  (c ^ k)⁻¹ • apertureMomentFourierSynthesis k c

theorem tendsto_normalizedApertureMomentSynthesis (k : ℕ) :
    Tendsto (normalizedApertureMomentSynthesis k)
      (𝓝[≠] (0 : ℝ)) (𝓝 (apertureMomentLeadingSynthesis k)) := by
  change Tendsto (fun c : ℝ =>
      (c ^ k)⁻¹ • apertureMomentFourierSynthesis k c)
    (𝓝[≠] (0 : ℝ)) (𝓝 (apertureMomentLeadingSynthesis k))
  exact tendsto_apertureMomentFourierSynthesis k

/-- Every fixed approximation number of the normalized deflated block converges
to the corresponding approximation number of its rank-one leading operator. -/
theorem tendsto_rectApproxNumber_normalizedApertureMomentSynthesis
    (k n : ℕ) :
    Tendsto (fun c : ℝ =>
      rectApproxNumber (normalizedApertureMomentSynthesis k c) n)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (rectApproxNumber (apertureMomentLeadingSynthesis k) n)) := by
  exact (continuous_rectApproxNumber
    (E := UnitPhysicalScalarL2) (F := UnitApertureL2) n).continuousAt.tendsto.comp
      (tendsto_normalizedApertureMomentSynthesis k)

/-- The leading singular value of every normalized deflated rung converges to
the strictly positive norm of its rank-one limit. -/
theorem tendsto_rectApproxNumber_zero_normalizedApertureMomentSynthesis
    (k : ℕ) :
    Tendsto (fun c : ℝ =>
      rectApproxNumber (normalizedApertureMomentSynthesis k c) 0)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ‖apertureMomentLeadingSynthesis k‖) := by
  simpa [rectApproxNumber_zero_eq_norm] using
    tendsto_rectApproxNumber_normalizedApertureMomentSynthesis k 0

theorem norm_apertureMomentLeadingSynthesis_pos (k : ℕ) :
    0 < ‖apertureMomentLeadingSynthesis k‖ :=
  norm_pos_iff.mpr (apertureMomentLeadingSynthesis_ne_zero k)

/-- The second singular value of every normalized deflated rung vanishes in
the small-aperture limit. -/
theorem tendsto_rectApproxNumber_one_normalizedApertureMomentSynthesis
    (k : ℕ) :
    Tendsto (fun c : ℝ =>
      rectApproxNumber (normalizedApertureMomentSynthesis k c) 1)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hzero : rectApproxNumber (apertureMomentLeadingSynthesis k) 1 = 0 :=
    rectApproxNumber_eq_zero_of_hasRectRankLE
      (hasRectRankLE_apertureMomentLeadingSynthesis k)
  simpa [hzero] using
    tendsto_rectApproxNumber_normalizedApertureMomentSynthesis k 1

/-- Spectral separation is asymptotically complete: the ratio between the
second and first singular values tends to zero at every rung. -/
theorem tendsto_deflated_singular_gap_ratio (k : ℕ) :
    Tendsto (fun c : ℝ =>
      rectApproxNumber (normalizedApertureMomentSynthesis k c) 1 /
        rectApproxNumber (normalizedApertureMomentSynthesis k c) 0)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have htop := tendsto_rectApproxNumber_zero_normalizedApertureMomentSynthesis k
  have htail := tendsto_rectApproxNumber_one_normalizedApertureMomentSynthesis k
  have hne : ‖apertureMomentLeadingSynthesis k‖ ≠ 0 :=
    ne_of_gt (norm_apertureMomentLeadingSynthesis_pos k)
  have hfun :
      (fun c : ℝ =>
        rectApproxNumber (normalizedApertureMomentSynthesis k c) 1 /
          rectApproxNumber (normalizedApertureMomentSynthesis k c) 0) =
      (fun c : ℝ => rectApproxNumber (normalizedApertureMomentSynthesis k c) 1) /
        (fun c : ℝ => rectApproxNumber (normalizedApertureMomentSynthesis k c) 0) := by
    rfl
  rw [hfun]
  simpa only [zero_div] using htail.div htop hne

/-- Every moment-deflated Fourier block has an eventual strict top singular
gap.  This is the spectral, rather than merely Taylor, all-rung output. -/
theorem eventually_rectApproxNumber_one_lt_zero_normalizedApertureMomentSynthesis
    (k : ℕ) :
    ∀ᶠ c : ℝ in 𝓝[≠] (0 : ℝ),
      rectApproxNumber (normalizedApertureMomentSynthesis k c) 1 <
        rectApproxNumber (normalizedApertureMomentSynthesis k c) 0 := by
  let L : ℝ := ‖apertureMomentLeadingSynthesis k‖
  have hL : 0 < L := norm_apertureMomentLeadingSynthesis_pos k
  have htop :=
    (tendsto_rectApproxNumber_zero_normalizedApertureMomentSynthesis k).eventually_const_lt
      (show L / 2 < L by linarith)
  have htail :=
    (tendsto_rectApproxNumber_one_normalizedApertureMomentSynthesis k).eventually_lt_const
      (show (0 : ℝ) < L / 2 by linarith)
  filter_upwards [htop, htail] with c hcTop hcTail
  exact hcTail.trans hcTop

/-- The normalization does not create the gap: every unnormalized deflated
Fourier block itself has a strict first singular gap at sufficiently small
nonzero aperture. -/
theorem eventually_rectApproxNumber_one_lt_zero_apertureMomentFourierSynthesis
    (k : ℕ) :
    ∀ᶠ c : ℝ in 𝓝[≠] (0 : ℝ),
      rectApproxNumber (apertureMomentFourierSynthesis k c) 1 <
        rectApproxNumber (apertureMomentFourierSynthesis k c) 0 := by
  have hgap :=
    eventually_rectApproxNumber_one_lt_zero_normalizedApertureMomentSynthesis k
  filter_upwards [hgap, self_mem_nhdsWithin] with c hcGap hc0
  have hc : c ≠ 0 := by simpa using hc0
  have hscale : 0 < |(c ^ k)⁻¹| :=
    abs_pos.mpr (inv_ne_zero (pow_ne_zero k hc))
  have hcast :
      (c ^ k)⁻¹ • apertureMomentFourierSynthesis k c =
        (((c ^ k)⁻¹ : ℝ) : ℂ) • apertureMomentFourierSynthesis k c := by
    ext x
    rfl
  change rectApproxNumber
      ((c ^ k)⁻¹ • apertureMomentFourierSynthesis k c) 1 <
    rectApproxNumber
      ((c ^ k)⁻¹ • apertureMomentFourierSynthesis k c) 0 at hcGap
  rw [hcast, rectApproxNumber_smul, rectApproxNumber_smul,
    Complex.norm_real, Real.norm_eq_abs] at hcGap
  nlinarith

end RHTower

