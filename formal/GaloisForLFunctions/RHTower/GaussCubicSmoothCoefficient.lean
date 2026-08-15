import GaloisForLFunctions.RHTower.GaussCubicTripleVectorConvergence

/-!
# Coefficient kernels of the two smooth cubic outer sources

The third source admits the exact telescoping identity
`B² T₋δ B⁻² w = M_{aδ} T₋δ w`.  Thus both smooth sources have one convolution index and two
sampled-ratio defects after the outer moving translation.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter

noncomputable section

theorem norm_fourierCoeff_gaussMovingAmplitudeCircle_le
    {p : ℝ} (hp : 1 < p) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (x : ℤ) :
    ‖fourierCoeff (gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ))) x‖ ≤
      4 * p / (1 + (x.natAbs : ℝ)) := by
  have hM : ∀ i : ℕ,
      ‖if i = 0 then ((Real.exp (s * Real.log p) : ℝ) : ℂ)
        else ((Real.exp ((s - 1) * Real.log p) : ℝ) : ℂ)‖ ≤ p :=
    fun i => norm_gaussAmplitudeCoeff_le hp hs1 i
  have hbound := norm_fourierCoeff_of_isExpPiecewise
    (isExpPiecewise_gaussMovingAmplitudeCircle (p := p) hs0 hs1)
    (by linarith : 0 ≤ p) hM x
  refine hbound.trans (le_of_eq ?_)
  rw [natAbs_cast_eq_abs]
  norm_num
  ring

/-- Harmonic convolution bound for multiplication by the moving amplitude. -/
theorem norm_fourierCoeff_gaussMovingAmplitudeBlock_le
    {p : ℝ} (hp : 1 < p) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (j : ℤ) :
    ‖fourierCoeff ((gaussMovingAmplitudeBlock hp
        ((s : ℝ) : AddCircle (1 : ℝ)) w : AddCircle (1 : ℝ) → ℂ)) j‖ ≤
      ∑' l : ℤ, 4 * p / (1 + ((l - j).natAbs : ℝ)) *
        ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖ := by
  have hsum := hasSum_fourierCoeff_lpBoundedMulCLM
    (measurable_gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ)))
    (by linarith : 0 ≤ p)
    (norm_gaussMovingAmplitudeCircle_le hp ((s : ℝ) : AddCircle (1 : ℝ)))
    (gaussMovingAmplitudeCircle_conj p ((s : ℝ) : AddCircle (1 : ℝ))) w j
  have hmaj : Summable (fun l : ℤ =>
      ‖starRingEnd ℂ
          (fourierCoeff (gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ)))
            (l - j)) * fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖) := by
    have hbase := summable_harmonicKernel_mul_fourierCoeff
      (κ := fun x => ‖fourierCoeff
        (gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ))) x‖)
      (A := 4 * p) (fun x => norm_nonneg _)
      (norm_fourierCoeff_gaussMovingAmplitudeCircle_le hp hs0 hs1) w j
    refine hbase.congr fun l => ?_
    rw [norm_mul, RCLike.norm_conj]
  have heq : fourierCoeff ((gaussMovingAmplitudeBlock hp
      ((s : ℝ) : AddCircle (1 : ℝ)) w : AddCircle (1 : ℝ) → ℂ)) j =
      ∑' l : ℤ, starRingEnd ℂ
        (fourierCoeff (gaussMovingAmplitudeCircle p ((s : ℝ) : AddCircle (1 : ℝ)))
          (l - j)) * fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l := hsum.tsum_eq.symm
  rw [heq]
  refine (norm_tsum_le_tsum_norm hmaj).trans ?_
  have hterm : Summable (fun l : ℤ => 4 * p / (1 + ((l - j).natAbs : ℝ)) *
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖) :=
    summable_harmonicKernel_mul_fourierCoeff
      (κ := fun x => 4 * p / (1 + (x.natAbs : ℝ))) (A := 4 * p)
      (fun x => by positivity) (fun x => le_rfl) w j
  refine hmaj.tsum_le_tsum (fun l => ?_) hterm
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_right
    (norm_fourierCoeff_gaussMovingAmplitudeCircle_le hp hs0 hs1 (l - j))
    (norm_nonneg _)

/-- Exact collapse of the apparently two-multiplier third source to moving-amplitude
multiplication followed by inverse rotation. -/
theorem gaussPrimeScaleSq_rotationInv_invSq_eq_movingAmplitude_rotationInv
    {p : ℝ} (hp : 1 < p) (δ : AddCircle (1 : ℝ))
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussPrimeScaleSqBlock hp
        (gaussRotationBlockInv δ (gaussPrimeScaleInvSqBlock hp w)) =
      gaussMovingAmplitudeBlock hp δ (gaussRotationBlockInv δ w) := by
  rw [gaussRotationBlockInv_eq_translation, gaussRotationBlockInv_eq_translation]
  refine Lp.ext ?_
  have hInv : (gaussPrimeScaleInvSqBlock hp w : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussPrimeScaleInvSqCircle p z * (w : AddCircle (1 : ℝ) → ℂ) z :=
    MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ w
  have hTransInv : (gaussTranslationBlock (-δ) (gaussPrimeScaleInvSqBlock hp w) :
      AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle] fun z =>
        gaussPrimeScaleInvSqCircle p (z + δ) * (w : AddCircle (1 : ℝ) → ℂ) (z + δ) := by
    refine (coeFn_gaussTranslationBlock (-δ) _).trans ?_
    filter_upwards [ae_eq_comp_sub (-δ) hInv] with z hz
    simpa only [sub_neg_eq_add] using hz
  have hTrans : (gaussTranslationBlock (-δ) w : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle] fun z => (w : AddCircle (1 : ℝ) → ℂ) (z + δ) := by
    refine (coeFn_gaussTranslationBlock (-δ) w).trans ?_
    filter_upwards with z
    simp only [sub_neg_eq_add]
  refine (MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ _).trans ?_
  refine Filter.EventuallyEq.trans ?_
    (MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ _).symm
  filter_upwards [hTransInv, hTrans] with z hzInv hzTrans
  rw [hzInv, hzTrans, gaussPrimeScaleSqCircle, gaussMovingAmplitudeCircle]
  ring

/-- First smooth source has exactly one sampled-ratio defect in each coefficient. -/
theorem norm_fourierCoeff_gaussCubicFirstSource_le
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i l : ℤ) :
    ‖fourierCoeff ((gaussCubicFirstSource hm k p hp i :
        AddCircle (1 : ℝ) → ℂ)) l‖ ≤
      4 * (p : ℝ) / (1 + (l.natAbs : ℝ)) *
        ‖gaussSampleRatioDefect k p l i‖ := by
  set δ : AddCircle (1 : ℝ) :=
    ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) with hδ
  set b : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleBlock hp (fourierLp 2 0) with hb
  set v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleInvSqBlock hp (gaussRotationBlock δ b) with hv
  set F : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussCubicFirstSource hm k p hp i with hF
  have hsub : fourierCoeff ((gaussCubicFirstSource hm k p hp i :
      AddCircle (1 : ℝ) → ℂ)) l =
      fourierCoeff ((gaussShiftedBlockDiag hm k p i v : AddCircle (1 : ℝ) → ℂ)) l -
        fourierCoeff ((gaussRotationBlockInv δ v : AddCircle (1 : ℝ) → ℂ)) l := by
    rw [← fourierBasis_repr, ← fourierBasis_repr, ← fourierBasis_repr,
      ← hF, hF, gaussCubicFirstSource, ← hδ, ← hb, ← hv, map_sub]
    rfl
  rw [hsub, hδ, norm_fourierCoeff_shiftedBlockDiag_sub_rotationInv hm k p]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hpow : (gaussMovingAmplitudeBlock hp
      ((Int.fract (gaussSamplePhase m p i) : ℝ) : AddCircle (1 : ℝ)) ^ 0)
      (fourierLp 2 0) =
        (fourierLp 2 0 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) := by
    rw [pow_zero]
    rfl
  have hbound := norm_fourierCoeff_gaussIntermediate_amplitudePow hp
    (Int.fract_nonneg (gaussSamplePhase m p i))
    (Int.fract_lt_one (gaussSamplePhase m p i)) 0 l
  rw [hpow, zero_add, pow_one] at hbound
  rw [hv, gaussRotationBlock_eq_translation]
  rw [hδ]
  rw [← coe_fract_eq (gaussSamplePhase m p i)]
  rw [hb]
  exact hbound

/-- Inner defect inside the third source has exactly one sampled-ratio defect. -/
theorem norm_fourierCoeff_gaussCubicThirdInnerDefect_le
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i l : ℤ) :
    ‖fourierCoeff ((((gaussShiftedBlockOf hm k p i
          (gaussPrimeScaleBlock hp (fourierLp 2 0)) -
        gaussRotationBlock ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ))
          (gaussPrimeScaleBlock hp (fourierLp 2 0))) :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
        AddCircle (1 : ℝ) → ℂ)) l‖ ≤
      4 * (p : ℝ) / (1 + (l.natAbs : ℝ)) *
        ‖gaussSampleRatioDefect k p l i‖ := by
  set δ : AddCircle (1 : ℝ) :=
    ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) with hδ
  set b : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussPrimeScaleBlock hp (fourierLp 2 0) with hb
  set w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussShiftedBlockOf hm k p i b - gaussRotationBlock δ b with hw
  change ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖ ≤ _
  have hsub : fourierCoeff (((gaussShiftedBlockOf hm k p i b -
      gaussRotationBlock δ b : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
      AddCircle (1 : ℝ) → ℂ)) l =
      fourierCoeff ((gaussShiftedBlockOf hm k p i b : AddCircle (1 : ℝ) → ℂ)) l -
        fourierCoeff ((gaussRotationBlock δ b : AddCircle (1 : ℝ) → ℂ)) l := by
    rw [← fourierBasis_repr, ← fourierBasis_repr, ← fourierBasis_repr, map_sub]
    rfl
  rw [hw, hsub, hδ, norm_fourierCoeff_shiftedBlockOf_sub_rotation hm k p]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hpow : (gaussMovingAmplitudeBlock hp ((0 : ℝ) : AddCircle (1 : ℝ)) ^ 0)
      (fourierLp 2 0) =
        (fourierLp 2 0 : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) := by
    rw [pow_zero]
    rfl
  have hbound := norm_fourierCoeff_gaussPrimeScaleBlock_amplitudePow hp
    (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 1) 0 l
  rw [hpow, zero_add, pow_one] at hbound
  exact hbound

/-- Universal harmonic pair kernel used by both smooth cubic sources. -/
def gaussCubicSmoothCoeffKernel (C : ℝ) (j l : ℤ) : ℝ :=
  C / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))

theorem gaussCubicSmoothCoeffKernel_nonneg {C : ℝ} (hC : 0 ≤ C) (j l : ℤ) :
    0 ≤ gaussCubicSmoothCoeffKernel C j l := by
  rw [gaussCubicSmoothCoeffKernel]
  positivity

theorem summable_gaussCubicSmoothCoeffKernel_ratio
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (i j : ℤ)
    {C : ℝ} (hC : 0 ≤ C) :
    Summable (fun l : ℤ => gaussCubicSmoothCoeffKernel C j l *
      ‖gaussSampleRatioDefect k p l i‖) := by
  set Rmax : ℝ :=
    1 + gaussSampleValueBound hm k p / ‖gaussSampleValue k p i‖ with hRmax
  have hRmax0 : 0 ≤ Rmax := by
    have h1 := gaussSampleValueBound_nonneg hm k p
    have h2 : 0 ≤ gaussSampleValueBound hm k p /
        ‖gaussSampleValue k p i‖ := by positivity
    rw [hRmax]
    linarith
  have hρ : ∀ l : ℤ, ‖gaussSampleRatioDefect k p l i‖ ≤ Rmax :=
    fun l => norm_gaussSampleRatioDefect_le_uniform hm k p i l
  have hmaj : Summable (fun l : ℤ =>
      (C * Rmax) *
        (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ))))) :=
    (summable_harmonicPairKernel j).mul_left _
  refine Summable.of_nonneg_of_le
    (fun l => mul_nonneg (gaussCubicSmoothCoeffKernel_nonneg hC j l) (norm_nonneg _))
    (fun l => ?_) hmaj
  rw [gaussCubicSmoothCoeffKernel]
  calc
    C / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ))) *
          ‖gaussSampleRatioDefect k p l i‖
        ≤ C / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ))) * Rmax := by
          exact mul_le_mul_of_nonneg_left (hρ l) (by positivity)
    _ = (C * Rmax) *
        (1 / ((1 + ((l - j).natAbs : ℝ)) * (1 + (l.natAbs : ℝ)))) := by ring

/-- After `B²`, the first smooth source is a literal one-index double-defect convolution. -/
theorem norm_fourierCoeff_gaussPrimeScaleSq_firstSource_le
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i j : ℤ) :
    ‖fourierCoeff ((gaussPrimeScaleSqBlock hp
        (gaussCubicFirstSource hm k p hp i) : AddCircle (1 : ℝ) → ℂ)) j‖ ≤
      ∑' l : ℤ, gaussCubicSmoothCoeffKernel (8 * (p : ℝ) ^ 3) j l *
        ‖gaussSampleRatioDefect k p l i‖ := by
  have hconv := norm_fourierCoeff_gaussPrimeScaleSqBlock_le hp
    (gaussCubicFirstSource hm k p hp i) j
  refine hconv.trans ?_
  have hleft : Summable (fun l : ℤ =>
      2 * (p : ℝ) ^ 2 / (1 + ((l - j).natAbs : ℝ)) *
        ‖fourierCoeff ((gaussCubicFirstSource hm k p hp i :
          AddCircle (1 : ℝ) → ℂ)) l‖) :=
    summable_harmonicKernel_mul_fourierCoeff
      (κ := fun x => 2 * (p : ℝ) ^ 2 / (1 + (x.natAbs : ℝ)))
      (A := 2 * (p : ℝ) ^ 2) (fun x => by positivity) (fun x => le_rfl)
      (gaussCubicFirstSource hm k p hp i) j
  have hright := summable_gaussCubicSmoothCoeffKernel_ratio hm k p i j
    (C := 8 * (p : ℝ) ^ 3) (by positivity)
  refine hleft.tsum_le_tsum (fun l => ?_) hright
  calc
    2 * (p : ℝ) ^ 2 / (1 + ((l - j).natAbs : ℝ)) *
        ‖fourierCoeff ((gaussCubicFirstSource hm k p hp i :
          AddCircle (1 : ℝ) → ℂ)) l‖
      ≤ 2 * (p : ℝ) ^ 2 / (1 + ((l - j).natAbs : ℝ)) *
          (4 * (p : ℝ) / (1 + (l.natAbs : ℝ)) *
            ‖gaussSampleRatioDefect k p l i‖) := by
        exact mul_le_mul_of_nonneg_left
          (norm_fourierCoeff_gaussCubicFirstSource_le hm k p hp i l) (by positivity)
    _ = gaussCubicSmoothCoeffKernel (8 * (p : ℝ) ^ 3) j l *
          ‖gaussSampleRatioDefect k p l i‖ := by
      rw [gaussCubicSmoothCoeffKernel]
      field_simp
      ring

/-- After `B²`, the third smooth source is also a literal one-index double-defect convolution. -/
theorem norm_fourierCoeff_gaussPrimeScaleSq_thirdSource_le
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (i j : ℤ) :
    ‖fourierCoeff ((gaussPrimeScaleSqBlock hp
        (gaussCubicThirdSource hm k p hp i) : AddCircle (1 : ℝ) → ℂ)) j‖ ≤
      ∑' l : ℤ, gaussCubicSmoothCoeffKernel (16 * (p : ℝ) ^ 2) j l *
        ‖gaussSampleRatioDefect k p l i‖ := by
  set δ : AddCircle (1 : ℝ) :=
    ((gaussSamplePhase m p i : ℝ) : AddCircle (1 : ℝ)) with hδ
  set w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussShiftedBlockOf hm k p i (gaussPrimeScaleBlock hp (fourierLp 2 0)) -
      gaussRotationBlock δ (gaussPrimeScaleBlock hp (fourierLp 2 0)) with hw
  have hsource : gaussPrimeScaleSqBlock hp (gaussCubicThirdSource hm k p hp i) =
      gaussMovingAmplitudeBlock hp δ (gaussRotationBlockInv δ w) := by
    rw [gaussCubicThirdSource, ← hδ, ← hw]
    exact gaussPrimeScaleSq_rotationInv_invSq_eq_movingAmplitude_rotationInv hp δ w
  rw [hsource]
  let s : ℝ := Int.fract (gaussSamplePhase m p i)
  have hs0 : 0 ≤ s := Int.fract_nonneg _
  have hs1 : s < 1 := Int.fract_lt_one _
  have hδs : ((s : ℝ) : AddCircle (1 : ℝ)) = δ := by
    change ((Int.fract (gaussSamplePhase m p i) : ℝ) : AddCircle (1 : ℝ)) = δ
    rw [coe_fract_eq, hδ]
  have hconv := norm_fourierCoeff_gaussMovingAmplitudeBlock_le hp hs0 hs1
    (gaussRotationBlockInv δ w) j
  rw [hδs] at hconv
  refine hconv.trans ?_
  have hleft : Summable (fun l : ℤ =>
      4 * (p : ℝ) / (1 + ((l - j).natAbs : ℝ)) *
        ‖fourierCoeff ((gaussRotationBlockInv δ w : AddCircle (1 : ℝ) → ℂ)) l‖) :=
    summable_harmonicKernel_mul_fourierCoeff
      (κ := fun x => 4 * (p : ℝ) / (1 + (x.natAbs : ℝ)))
      (A := 4 * (p : ℝ)) (fun x => by positivity) (fun x => le_rfl)
      (gaussRotationBlockInv δ w) j
  have hright := summable_gaussCubicSmoothCoeffKernel_ratio hm k p i j
    (C := 16 * (p : ℝ) ^ 2) (by positivity)
  refine hleft.tsum_le_tsum (fun l => ?_) hright
  have hrot : ‖fourierCoeff ((gaussRotationBlockInv δ w :
      AddCircle (1 : ℝ) → ℂ)) l‖ =
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖ := by
    rw [gaussRotationBlockInv_eq_translation,
      norm_fourierCoeff_gaussTranslationBlock]
  calc
    4 * (p : ℝ) / (1 + ((l - j).natAbs : ℝ)) *
        ‖fourierCoeff ((gaussRotationBlockInv δ w : AddCircle (1 : ℝ) → ℂ)) l‖
      = 4 * (p : ℝ) / (1 + ((l - j).natAbs : ℝ)) *
          ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖ := by rw [hrot]
    _ ≤ 4 * (p : ℝ) / (1 + ((l - j).natAbs : ℝ)) *
          (4 * (p : ℝ) / (1 + (l.natAbs : ℝ)) *
            ‖gaussSampleRatioDefect k p l i‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hw]
        exact norm_fourierCoeff_gaussCubicThirdInnerDefect_le hm k p hp i l
    _ = gaussCubicSmoothCoeffKernel (16 * (p : ℝ) ^ 2) j l *
          ‖gaussSampleRatioDefect k p l i‖ := by
      rw [gaussCubicSmoothCoeffKernel]
      field_simp
      ring

end

end RHTower
