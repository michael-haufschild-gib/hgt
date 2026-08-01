import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary
import GaloisForLFunctions.HTGeometry.PSDMatrixSpectralHankel

/-!
# Groskin's archimedean tail order without a numerical cutoff

Groskin's finite Guinand--Weil theorem identifies the omitted archimedean tail as an
integral of rank-two Cauchy Grams.  The published cutoff `7` uses an interval computation of
the digamma density at one point.  This file keeps the literal density and exact rank-two
kernel, but replaces that numerical step by the unconditional fact that the density tends to
`+∞`.  It therefore produces an analytic finite threshold and proves the Loewner-positive
tail increment without computation.

This is finite source infrastructure.  It proves neither positivity of the full Weil form nor
the Riemann hypothesis.
-/

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- The archimedean density in Groskin's Theorem 3.2. -/
def groskinArchimedeanDensity (T : ℝ) : ℝ :=
  (Complex.digamma (((1 / 4 : ℝ) : ℂ) + (((T / 2 : ℝ) : ℂ) * Complex.I))).re -
    Real.log Real.pi

/-- The literal archimedean density tends to `+∞`; no point value is computed. -/
theorem tendsto_groskinArchimedeanDensity_atTop :
    Tendsto groskinArchimedeanDensity atTop atTop := by
  have hhalf : Tendsto (fun T : ℝ => T / 2) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (f := fun T : ℝ => T) (l := atTop)
      (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
  have hdigamma :=
    (GaloisForLFunctions.re_digamma_vertical_tendsto_atTop
      (σ := (1 / 4 : ℝ)) (by norm_num)).comp hhalf
  have hsub := tendsto_atTop_add_const_right atTop (-Real.log Real.pi) hdigamma
  refine hsub.congr' (Eventually.of_forall fun T => ?_)
  simp only [groskinArchimedeanDensity, Function.comp_def, sub_eq_add_neg]

/-- Some finite analytic threshold makes the literal density strictly positive forever. -/
theorem exists_groskinArchimedeanDensity_pos_threshold :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, 0 < groskinArchimedeanDensity T := by
  rcases eventually_atTop.1
      (tendsto_groskinArchimedeanDensity_atTop.eventually_gt_atTop 0) with ⟨T₀, hT₀⟩
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

/-- A fixed noncomputable threshold selected from the analytic eventual-positivity theorem. -/
def groskinArchimedeanPositivityThreshold : ℝ :=
  Classical.choose exists_groskinArchimedeanDensity_pos_threshold

/-- The selected threshold has the required strict positivity property. -/
theorem groskinArchimedeanDensity_pos_of_threshold {T : ℝ}
    (hT : groskinArchimedeanPositivityThreshold ≤ T) :
    0 < groskinArchimedeanDensity T :=
  (Classical.choose_spec exists_groskinArchimedeanDensity_pos_threshold) T hT

/-- The first Cauchy feature `1 / (T / rho - x_i)`. -/
def groskinArchTailMinusFeature {ι : Type*}
    (ρ : ℝ) (x : ι → ℝ) (T : ℝ) (i : ι) : ℝ :=
  (T / ρ - x i)⁻¹

/-- The reflected Cauchy feature `1 / (T / rho + x_i)`. -/
def groskinArchTailPlusFeature {ι : Type*}
    (ρ : ℝ) (x : ι → ℝ) (T : ℝ) (i : ι) : ℝ :=
  (T / ρ + x i)⁻¹

/-- Scalar density multiplying the two Cauchy rank-one Grams. -/
def groskinArchTailWeight (L ρ T : ℝ) : ℝ :=
  groskinArchimedeanDensity T * Real.sin (L * T / 2) ^ 2 / (Real.pi ^ 2 * ρ)

/-- Exact rank-two Cauchy--Stieltjes matrix density from Groskin Theorem 3.2. -/
def groskinArchTailKernel {ι : Type*}
    (L ρ : ℝ) (x : ι → ℝ) (T : ℝ) : Matrix ι ι ℝ :=
  groskinArchTailWeight L ρ T •
    (Matrix.vecMulVec (groskinArchTailMinusFeature ρ x T)
        (groskinArchTailMinusFeature ρ x T) +
      Matrix.vecMulVec (groskinArchTailPlusFeature ρ x T)
        (groskinArchTailPlusFeature ρ x T))

/-- Restrict the exact density to one compact cutoff window. -/
def groskinArchTailWindowKernel {ι : Type*}
    (L ρ T₁ T₂ : ℝ) (x : ι → ℝ) (T : ℝ) : Matrix ι ι ℝ :=
  (Icc T₁ T₂).indicator (fun t => groskinArchTailKernel L ρ x t) T

/-- Entrywise integral of the exact tail density on `[T1,T2]`. -/
def groskinArchTailIncrement {ι : Type*}
    (L ρ T₁ T₂ : ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  HTGeometry.integralMatrixKernel volume (groskinArchTailWindowKernel L ρ T₁ T₂ x)

/-- Beyond the analytic threshold, the scalar Cauchy--Stieltjes density is nonnegative. -/
theorem groskinArchTailWeight_nonneg {L ρ T : ℝ} (hρ : 0 < ρ)
    (hT : groskinArchimedeanPositivityThreshold ≤ T) :
    0 ≤ groskinArchTailWeight L ρ T := by
  exact div_nonneg
    (mul_nonneg (groskinArchimedeanDensity_pos_of_threshold hT).le (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) hρ.le)

/-- The exact rank-two tail density is positive semidefinite pointwise. -/
theorem groskinArchTailKernel_posSemidef {ι : Type*} [Finite ι]
    {L ρ T : ℝ} (x : ι → ℝ) (hρ : 0 < ρ)
    (hT : groskinArchimedeanPositivityThreshold ≤ T) :
    (groskinArchTailKernel L ρ x T).PosSemidef := by
  have hminus :
      (Matrix.vecMulVec (groskinArchTailMinusFeature ρ x T)
        (groskinArchTailMinusFeature ρ x T)).PosSemidef := by
    simpa only [star_trivial] using
      Matrix.posSemidef_vecMulVec_self_star (groskinArchTailMinusFeature ρ x T)
  have hplus :
      (Matrix.vecMulVec (groskinArchTailPlusFeature ρ x T)
        (groskinArchTailPlusFeature ρ x T)).PosSemidef := by
    simpa only [star_trivial] using
      Matrix.posSemidef_vecMulVec_self_star (groskinArchTailPlusFeature ρ x T)
  exact (hminus.add hplus).smul (groskinArchTailWeight_nonneg hρ hT)

/-- The Cauchy denominators stay positive on a tail window lying beyond every scaled node. -/
theorem groskinArchTail_denominators_pos {ι : Type*}
    {ρ T₁ T₂ : ℝ} (x : ι → ℝ) (hρ : 0 < ρ)
    (hnode : ∀ i, ρ * |x i| < T₁) {T : ℝ} (hT : T ∈ Icc T₁ T₂) (i : ι) :
    0 < T / ρ - x i ∧ 0 < T / ρ + x i := by
  have hscaled : |x i| < T / ρ := by
    rw [lt_div_iff₀ hρ]
    exact lt_of_lt_of_le (by simpa [mul_comm] using hnode i) hT.1
  constructor <;> linarith [le_abs_self (x i), neg_abs_le (x i)]

/-- Every entry of the exact rank-two density is continuous on a pole-free cutoff window. -/
theorem continuousOn_groskinArchTailKernel_apply {ι : Type*}
    {L ρ T₁ T₂ : ℝ} (x : ι → ℝ) (hρ : 0 < ρ)
    (hnode : ∀ i, ρ * |x i| < T₁) (i j : ι) :
    ContinuousOn (fun T => groskinArchTailKernel L ρ x T i j) (Icc T₁ T₂) := by
  have hdensity : Continuous groskinArchimedeanDensity := by
    have harg : Continuous (fun T : ℝ =>
        (((1 / 4 : ℝ) : ℂ) + (((T / 2 : ℝ) : ℂ) * Complex.I))) := by fun_prop
    have hdigamma : Continuous (fun T : ℝ => Complex.digamma
        (((1 / 4 : ℝ) : ℂ) + (((T / 2 : ℝ) : ℂ) * Complex.I))) := by
      rw [continuous_iff_continuousAt]
      intro T
      exact (GaloisForLFunctions.continuousAt_digamma _ (fun m hzero => by
        have hre := congrArg Complex.re hzero
        have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        norm_num at hre
        linarith)).comp harg.continuousAt
    exact (Complex.continuous_re.comp hdigamma).sub continuous_const
  have hweight : Continuous (groskinArchTailWeight L ρ) := by
    unfold groskinArchTailWeight
    fun_prop
  have hminus (k : ι) :
      ContinuousOn (fun T => groskinArchTailMinusFeature ρ x T k) (Icc T₁ T₂) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro T hT
    exact (groskinArchTail_denominators_pos x hρ hnode hT k).1.ne'
  have hplus (k : ι) :
      ContinuousOn (fun T => groskinArchTailPlusFeature ρ x T k) (Icc T₁ T₂) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro T hT
    exact (groskinArchTail_denominators_pos x hρ hnode hT k).2.ne'
  change ContinuousOn (fun T => groskinArchTailWeight L ρ T *
    (groskinArchTailMinusFeature ρ x T i * groskinArchTailMinusFeature ρ x T j +
      groskinArchTailPlusFeature ρ x T i * groskinArchTailPlusFeature ρ x T j)) (Icc T₁ T₂)
  exact hweight.continuousOn.mul
    ((hminus i).mul (hminus j) |>.add ((hplus i).mul (hplus j)))

/-- Every windowed matrix entry is integrable on the full line. -/
theorem integrable_groskinArchTailWindowKernel_apply {ι : Type*}
    {L ρ T₁ T₂ : ℝ} (x : ι → ℝ) (hρ : 0 < ρ)
    (hnode : ∀ i, ρ * |x i| < T₁) (i j : ι) :
    Integrable (fun T => groskinArchTailWindowKernel L ρ T₁ T₂ x T i j) := by
  have hint : IntegrableOn (fun T => groskinArchTailKernel L ρ x T i j)
      (Icc T₁ T₂) volume :=
    (continuousOn_groskinArchTailKernel_apply x hρ hnode i j).integrableOn_Icc
  have hind := hint.integrable_indicator measurableSet_Icc
  have heq : (fun T => groskinArchTailWindowKernel L ρ T₁ T₂ x T i j) =
      (Icc T₁ T₂).indicator (fun T => groskinArchTailKernel L ρ x T i j) := by
    funext T
    by_cases hT : T ∈ Icc T₁ T₂ <;> simp [groskinArchTailWindowKernel, hT]
  rw [heq]
  exact hind

/-- **Groskin archimedean tail Loewner order, without computation.**

Past the analytically selected density threshold and every scaled node pole, the exact omitted
archimedean tail on any compact cutoff window is positive semidefinite. -/
theorem groskinArchTailIncrement_posSemidef {ι : Type*} [Fintype ι]
    {L ρ T₁ T₂ : ℝ} (x : ι → ℝ) (hρ : 0 < ρ)
    (hthreshold : groskinArchimedeanPositivityThreshold ≤ T₁)
    (hnode : ∀ i, ρ * |x i| < T₁) :
    (groskinArchTailIncrement L ρ T₁ T₂ x).PosSemidef := by
  apply HTGeometry.integralMatrixKernel_posSemidef
  · exact integrable_groskinArchTailWindowKernel_apply x hρ hnode
  · intro T
    by_cases hT : T ∈ Icc T₁ T₂
    · simp only [groskinArchTailWindowKernel, Set.indicator_of_mem hT]
      exact groskinArchTailKernel_posSemidef x hρ (hthreshold.trans hT.1)
    · simp [groskinArchTailWindowKernel, hT]
      exact Matrix.PosSemidef.zero

end RHTower
