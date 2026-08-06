import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary
import GaloisForLFunctions.HTGeometry.PSDMatrixSpectralHankel
import GaloisForLFunctions.HTGeometry.MatrixRankSubadditive

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

/-- **The pointwise Gram identity of Groskin Theorem 3.2.**  The quadratic form of the exact tail
density is the scalar density times the sum of the two squared Cauchy pairings — the identity that
exhibits the density as a rank-two Cauchy--Stieltjes Gram rather than merely a positive matrix. -/
theorem groskinArchTailKernel_quadraticForm {ι : Type*} [Fintype ι]
    (L ρ : ℝ) (x : ι → ℝ) (T : ℝ) (c : ι → ℝ) :
    (∑ i, ∑ j, c i * groskinArchTailKernel L ρ x T i j * c j)
      = groskinArchTailWeight L ρ T *
        ((∑ i, c i * groskinArchTailMinusFeature ρ x T i) ^ 2
          + (∑ i, c i * groskinArchTailPlusFeature ρ x T i) ^ 2) := by
  have hsq : ∀ f : ι → ℝ, (∑ i, c i * f i) ^ 2 = ∑ i, ∑ j, (c i * f i) * (c j * f j) := by
    intro f
    rw [sq, Finset.sum_mul_sum]
  rw [hsq, hsq, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [groskinArchTailKernel, Matrix.smul_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  ring

/-- **The exact tail density has rank at most two.**  It is the scalar density times the sum of the
two Cauchy outer products, so its column space is spanned by the two Cauchy feature vectors. -/
theorem groskinArchTailKernel_rank_le_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L ρ : ℝ) (x : ι → ℝ) (T : ℝ) : (groskinArchTailKernel L ρ x T).rank ≤ 2 := by
  refine le_trans (GaloisForLFunctions.HTGeometry.rank_smul_le _ _) ?_
  refine le_trans (GaloisForLFunctions.HTGeometry.rank_add_le_rank_add_rank _ _) ?_
  have hminus := Matrix.rank_vecMulVec_le (groskinArchTailMinusFeature ρ x T)
    (groskinArchTailMinusFeature ρ x T)
  have hplus := Matrix.rank_vecMulVec_le (groskinArchTailPlusFeature ρ x T)
    (groskinArchTailPlusFeature ρ x T)
  omega

/-- **The archimedean tail order.**  Shrinking the cutoff window lowers the tail increment in the
Loewner order: the difference of the two increments is the integral of the density over the
discarded part of the window, which is positive semidefinite there. -/
theorem groskinArchTailIncrement_mono {ι : Type*} [Fintype ι]
    {L ρ T₁ T₂ T₁' T₂' : ℝ} (x : ι → ℝ) (hρ : 0 < ρ)
    (hthreshold : groskinArchimedeanPositivityThreshold ≤ T₁)
    (hnode : ∀ i, ρ * |x i| < T₁) (hlow : T₁ ≤ T₁') (hhigh : T₂' ≤ T₂) :
    (groskinArchTailIncrement L ρ T₁ T₂ x - groskinArchTailIncrement L ρ T₁' T₂' x).PosSemidef := by
  have hnode' : ∀ i, ρ * |x i| < T₁' := fun i => lt_of_lt_of_le (hnode i) hlow
  have hint₁ := integrable_groskinArchTailWindowKernel_apply
    (L := L) (T₁ := T₁) (T₂ := T₂) x hρ hnode
  have hint₂ := integrable_groskinArchTailWindowKernel_apply
    (L := L) (T₁ := T₁') (T₂ := T₂') x hρ hnode'
  rw [groskinArchTailIncrement, groskinArchTailIncrement,
    ← HTGeometry.integralMatrixKernel_sub volume _ _ hint₁ hint₂]
  refine HTGeometry.integralMatrixKernel_posSemidef volume _ (fun i j => (hint₁ i j).sub (hint₂ i j))
    fun T => ?_
  by_cases hin : T ∈ Icc T₁' T₂'
  · have hbig : T ∈ Icc T₁ T₂ := ⟨le_trans hlow hin.1, le_trans hin.2 hhigh⟩
    simp only [groskinArchTailWindowKernel, Set.indicator_of_mem hin, Set.indicator_of_mem hbig,
      sub_self]
    exact Matrix.PosSemidef.zero
  · by_cases hbig : T ∈ Icc T₁ T₂
    · simp only [groskinArchTailWindowKernel, Set.indicator_of_mem hbig,
        Set.indicator_of_notMem hin, sub_zero]
      exact groskinArchTailKernel_posSemidef x hρ (hthreshold.trans hbig.1)
    · simp only [groskinArchTailWindowKernel, Set.indicator_of_notMem hin,
        Set.indicator_of_notMem hbig, sub_self]
      exact Matrix.PosSemidef.zero

/-- **The tail-order hypotheses are always satisfiable.**  For every positive scale and every finite
node family there is a nondegenerate cutoff window lying past both the analytic threshold and every
scaled node, so the Loewner-order theorems are never vacuous. -/
theorem exists_groskinArchTailWindow {ι : Type*} [Finite ι] (ρ : ℝ) (x : ι → ℝ) :
    ∃ T₁ T₂ : ℝ, T₁ < T₂ ∧ groskinArchimedeanPositivityThreshold ≤ T₁ ∧
      ∀ i, ρ * |x i| < T₁ := by
  obtain ⟨M, hM⟩ := Finite.exists_le fun i => ρ * |x i|
  refine ⟨max groskinArchimedeanPositivityThreshold M + 1,
    max groskinArchimedeanPositivityThreshold M + 2, by linarith, ?_, fun i => ?_⟩
  · have := le_max_left groskinArchimedeanPositivityThreshold M
    linarith
  · have h1 := hM i
    have h2 := le_max_right groskinArchimedeanPositivityThreshold M
    linarith

/-- **Nonvacuity of the archimedean tail order.**  Every positive scale and finite node family
admits a window on which the tail increment is positive semidefinite. -/
theorem exists_groskinArchTailIncrement_posSemidef {ι : Type*} [Fintype ι] (L : ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) (x : ι → ℝ) :
    ∃ T₁ T₂ : ℝ, T₁ < T₂ ∧ (groskinArchTailIncrement L ρ T₁ T₂ x).PosSemidef := by
  obtain ⟨T₁, T₂, hlt, hthreshold, hnode⟩ := exists_groskinArchTailWindow ρ x
  exact ⟨T₁, T₂, hlt, groskinArchTailIncrement_posSemidef x hρ hthreshold hnode⟩

/-- The action of a Cauchy outer product is a multiple of its feature vector. -/
theorem vecMulVec_mulVec_self {ι : Type*} [Fintype ι] (u y : ι → ℝ) :
    Matrix.mulVec (Matrix.vecMulVec u u) y = (dotProduct u y) • u := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Scalar multiplication commutes with the matrix action. -/
theorem smul_mulVec_eq {ι : Type*} [Fintype ι] (c : ℝ) (A : Matrix ι ι ℝ) (y : ι → ℝ) :
    Matrix.mulVec (c • A) y = c • Matrix.mulVec A y := by
  funext i
  simp only [Matrix.mulVec, Matrix.smul_apply, dotProduct, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The column space of the exact tail density is spanned by the two Cauchy features.**  This is
the structural content of "rank-two Cauchy--Stieltjes Gram": every column is a combination of the
two Cauchy feature vectors, with no positivity or threshold hypothesis. -/
theorem range_groskinArchTailKernel_le_span {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L ρ : ℝ) (x : ι → ℝ) (T : ℝ) :
    LinearMap.range (Matrix.mulVecLin (groskinArchTailKernel L ρ x T))
      ≤ Submodule.span ℝ {groskinArchTailMinusFeature ρ x T, groskinArchTailPlusFeature ρ x T} := by
  rintro _ ⟨y, rfl⟩
  have hval : Matrix.mulVecLin (groskinArchTailKernel L ρ x T) y
      = groskinArchTailWeight L ρ T •
        ((dotProduct (groskinArchTailMinusFeature ρ x T) y) •
            groskinArchTailMinusFeature ρ x T
          + (dotProduct (groskinArchTailPlusFeature ρ x T) y) •
            groskinArchTailPlusFeature ρ x T) := by
    simp only [Matrix.mulVecLin_apply, groskinArchTailKernel, smul_mulVec_eq,
      Matrix.add_mulVec, vecMulVec_mulVec_self]
  rw [hval]
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-! ### The exact rank of the tail density -/

/-- Clearing the two Cauchy denominators in a vanishing combination of the two features. -/
theorem cauchyPair_combination {u y s t : ℝ} (hm : u - y ≠ 0) (hp : u + y ≠ 0)
    (h : s * (u - y)⁻¹ + t * (u + y)⁻¹ = 0) : s * (u + y) + t * (u - y) = 0 := by
  have hzero : (s * (u - y)⁻¹ + t * (u + y)⁻¹) * ((u - y) * (u + y)) = 0 := by
    rw [h, zero_mul]
  have hexp : (s * (u - y)⁻¹ + t * (u + y)⁻¹) * ((u - y) * (u + y))
      = s * (u + y) + t * (u - y) := by
    field_simp
  rwa [hexp] at hzero

/-- **The two Cauchy features are independent as soon as two nodes differ.**  A vanishing
combination forces `(T/rho)(s+t) + x_i (s-t) = 0` at every node; two distinct nodes give `s = t`,
and a nonzero argument then gives `s = t = 0`. -/
theorem linearIndependent_groskinArchTailFeatures {ι : Type*} [Fintype ι]
    {ρ T : ℝ} (x : ι → ℝ) (hρ : 0 < ρ) (hnode : ∀ i, ρ * |x i| < T)
    {i₀ j₀ : ι} (hij : x i₀ ≠ x j₀) :
    LinearIndependent ℝ ![groskinArchTailMinusFeature ρ x T,
      groskinArchTailPlusFeature ρ x T] := by
  have hden : ∀ i, 0 < T / ρ - x i ∧ 0 < T / ρ + x i := by
    intro i
    have hscaled : |x i| < T / ρ := by
      rw [lt_div_iff₀ hρ]
      simpa [mul_comm] using hnode i
    constructor <;> linarith [le_abs_self (x i), neg_abs_le (x i)]
  have hu : T / ρ ≠ 0 := by
    have h := hden i₀
    have := abs_nonneg (x i₀)
    linarith [h.1, h.2, le_abs_self (x i₀), neg_abs_le (x i₀)]
  refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
  have key : ∀ i, s * (T / ρ + x i) + t * (T / ρ - x i) = 0 := by
    intro i
    have hm : T / ρ - x i ≠ 0 := ne_of_gt (hden i).1
    have hp : T / ρ + x i ≠ 0 := ne_of_gt (hden i).2
    have hi := congrFun hst i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
      groskinArchTailMinusFeature, groskinArchTailPlusFeature] at hi
    exact cauchyPair_combination hm hp hi
  have ki := key i₀
  have kj := key j₀
  have hdiff : (x i₀ - x j₀) * (s - t) = 0 := by linear_combination ki - kj
  have hst0 : s - t = 0 := by
    rcases mul_eq_zero.mp hdiff with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hij
    · exact h1
  have hsum : (T / ρ) * (s + t) = 0 := by linear_combination ki - x i₀ * hst0
  have hsum0 : s + t = 0 := by
    rcases mul_eq_zero.mp hsum with h1 | h1
    · exact absurd h1 hu
    · exact h1
  constructor <;> linarith

/-- The scalar Cauchy--Stieltjes density is nonzero away from the zeros of the modulating sine. -/
theorem groskinArchTailWeight_ne_zero {L ρ T : ℝ} (hρ : 0 < ρ)
    (hT : groskinArchimedeanPositivityThreshold ≤ T) (hsin : Real.sin (L * T / 2) ≠ 0) :
    groskinArchTailWeight L ρ T ≠ 0 := by
  have hs2 : 0 < Real.sin (L * T / 2) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hsin))
  have hpos : 0 < groskinArchimedeanDensity T * Real.sin (L * T / 2) ^ 2 :=
    mul_pos (groskinArchimedeanDensity_pos_of_threshold hT) hs2
  have hden : 0 < Real.pi ^ 2 * ρ := by positivity
  exact ne_of_gt (div_pos hpos hden)

/-- **The exact tail density has rank exactly two.**  Past the analytic threshold and away from the
zeros of the modulating sine, the scalar density is nonzero, and two distinct nodes make the two
Cauchy features independent, so the column space is exactly their span. -/
theorem groskinArchTailKernel_rank_eq_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L ρ T : ℝ} (x : ι → ℝ) (hρ : 0 < ρ) (hnode : ∀ i, ρ * |x i| < T)
    (hT : groskinArchimedeanPositivityThreshold ≤ T) (hsin : Real.sin (L * T / 2) ≠ 0)
    {i₀ j₀ : ι} (hij : x i₀ ≠ x j₀) :
    (groskinArchTailKernel L ρ x T).rank = 2 := by
  rw [groskinArchTailKernel,
    GaloisForLFunctions.HTGeometry.rank_smul_eq (groskinArchTailWeight_ne_zero hρ hT hsin)]
  exact GaloisForLFunctions.HTGeometry.rank_gramPair_eq_two
    (linearIndependent_groskinArchTailFeatures x hρ hnode hij)

/-- **The column space of the exact tail density is exactly the span of the two Cauchy features.** -/
theorem range_groskinArchTailKernel_eq_span {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L ρ T : ℝ} (x : ι → ℝ) (hρ : 0 < ρ) (hnode : ∀ i, ρ * |x i| < T)
    (hT : groskinArchimedeanPositivityThreshold ≤ T) (hsin : Real.sin (L * T / 2) ≠ 0)
    {i₀ j₀ : ι} (hij : x i₀ ≠ x j₀) :
    LinearMap.range (Matrix.mulVecLin (groskinArchTailKernel L ρ x T))
      = Submodule.span ℝ {groskinArchTailMinusFeature ρ x T, groskinArchTailPlusFeature ρ x T} := by
  refine le_antisymm (range_groskinArchTailKernel_le_span L ρ x T) ?_
  have hw := groskinArchTailWeight_ne_zero (L := L) hρ hT hsin
  have hspan := GaloisForLFunctions.HTGeometry.span_pair_le_range_gramPair
    (linearIndependent_groskinArchTailFeatures x hρ hnode hij)
  intro y hy
  obtain ⟨z, hz⟩ := hspan hy
  refine ⟨(groskinArchTailWeight L ρ T)⁻¹ • z, ?_⟩
  rw [Matrix.mulVecLin_apply, groskinArchTailKernel, smul_mulVec_eq, Matrix.mulVec_smul,
    smul_smul, mul_inv_cancel₀ hw, one_smul]
  rw [← Matrix.mulVecLin_apply, hz]

/-- A nonzero modulating frequency has arbitrarily large cutoffs off the zeros of its sine: the
sine and its quarter-period translate cannot vanish together. -/
theorem exists_sin_ne_zero_ge {L : ℝ} (hL : L ≠ 0) (T₀ : ℝ) :
    ∃ T : ℝ, T₀ ≤ T ∧ Real.sin (L * T / 2) ≠ 0 := by
  by_cases h : Real.sin (L * T₀ / 2) ≠ 0
  · exact ⟨T₀, le_refl _, h⟩
  push Not at h
  have habs : 0 < |L| := abs_pos.mpr hL
  have hcos : Real.cos (L * T₀ / 2) ≠ 0 := by
    intro hc
    have := Real.sin_sq_add_cos_sq (L * T₀ / 2)
    rw [h, hc] at this
    norm_num at this
  refine ⟨T₀ + Real.pi / |L|, le_add_of_nonneg_right (by positivity), ?_⟩
  rcases lt_or_gt_of_ne hL with hneg | hpos
  · have hL' : |L| = -L := abs_of_neg hneg
    have harg : L * (T₀ + Real.pi / |L|) / 2 = L * T₀ / 2 - Real.pi / 2 := by
      rw [hL']
      field_simp
      ring
    rw [harg, Real.sin_sub_pi_div_two]
    simpa using hcos
  · have hL' : |L| = L := abs_of_pos hpos
    have harg : L * (T₀ + Real.pi / |L|) / 2 = L * T₀ / 2 + Real.pi / 2 := by
      rw [hL']
      field_simp
    rw [harg, Real.sin_add_pi_div_two]
    exact hcos

/-- **Nonvacuity of the exact rank.**  For every nonzero modulating frequency, every positive scale
and every node family with two distinct nodes there is a cutoff at which the tail density has rank
exactly two. -/
theorem exists_groskinArchTailKernel_rank_eq_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L ρ : ℝ} (hL : L ≠ 0) (hρ : 0 < ρ) (x : ι → ℝ) {i₀ j₀ : ι} (hij : x i₀ ≠ x j₀) :
    ∃ T : ℝ, groskinArchimedeanPositivityThreshold ≤ T ∧ (∀ i, ρ * |x i| < T) ∧
      (groskinArchTailKernel L ρ x T).rank = 2 := by
  obtain ⟨T₁, -, hlt, hthreshold, hnode⟩ := exists_groskinArchTailWindow ρ x
  obtain ⟨T, hT₁, hsin⟩ := exists_sin_ne_zero_ge hL T₁
  refine ⟨T, hthreshold.trans hT₁, fun i => lt_of_lt_of_le (hnode i) hT₁, ?_⟩
  exact groskinArchTailKernel_rank_eq_two x hρ (fun i => lt_of_lt_of_le (hnode i) hT₁)
    (hthreshold.trans hT₁) hsin hij

/-! ### The Stieltjes representation of the increment -/

/-- **The tail increment is an explicit Cauchy--Stieltjes Gram.**  Its quadratic form is the
integral over the cutoff window of the pointwise Cauchy Gram: the scalar density times the sum of
the two squared Cauchy features.  This is the exact sense in which the omitted archimedean tail is
a Cauchy--Stieltjes Gram increment rather than an unstructured positive matrix. -/
theorem groskinArchTailIncrement_quadraticForm {ι : Type*} [Fintype ι]
    {L ρ T₁ T₂ : ℝ} (x : ι → ℝ) (hρ : 0 < ρ) (hnode : ∀ i, ρ * |x i| < T₁) (c : ι → ℝ) :
    dotProduct (star c) ((groskinArchTailIncrement L ρ T₁ T₂ x).mulVec c)
      = ∫ T in Set.Icc T₁ T₂, groskinArchTailWeight L ρ T *
          ((∑ i, c i * groskinArchTailMinusFeature ρ x T i) ^ 2
            + (∑ i, c i * groskinArchTailPlusFeature ρ x T i) ^ 2) := by
  have hquad : ∀ A : Matrix ι ι ℝ,
      dotProduct (star c) (A.mulVec c) = ∑ i, ∑ j, c i * A i j * c j := by
    intro A
    simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hint := integrable_groskinArchTailWindowKernel_apply
    (L := L) (T₁ := T₁) (T₂ := T₂) x hρ hnode
  rw [groskinArchTailIncrement,
    HTGeometry.integralMatrixKernel_quadratic_eq_integral volume _ hint c]
  have hpoint : ∀ T : ℝ,
      HTGeometry.integralMatrixKernelQuadratic (groskinArchTailWindowKernel L ρ T₁ T₂ x) c T
        = Set.indicator (Set.Icc T₁ T₂)
            (fun T => groskinArchTailWeight L ρ T *
              ((∑ i, c i * groskinArchTailMinusFeature ρ x T i) ^ 2
                + (∑ i, c i * groskinArchTailPlusFeature ρ x T i) ^ 2)) T := by
    intro T
    rw [HTGeometry.integralMatrixKernelQuadratic, hquad, groskinArchTailWindowKernel]
    by_cases hT : T ∈ Set.Icc T₁ T₂
    · rw [Set.indicator_of_mem hT, Set.indicator_of_mem hT]
      exact groskinArchTailKernel_quadraticForm L ρ x T c
    · rw [Set.indicator_of_notMem hT, Set.indicator_of_notMem hT]
      simp
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint),
    MeasureTheory.integral_indicator measurableSet_Icc]

/-- The scalar Cauchy Gram of a coefficient vector on the cutoff window. -/
def groskinArchTailScalarGram {ι : Type*} [Fintype ι]
    (L ρ : ℝ) (x : ι → ℝ) (c : ι → ℝ) (T : ℝ) : ℝ :=
  groskinArchTailWeight L ρ T *
    ((∑ i, c i * groskinArchTailMinusFeature ρ x T i) ^ 2
      + (∑ i, c i * groskinArchTailPlusFeature ρ x T i) ^ 2)

theorem groskinArchTailScalarGram_nonneg {ι : Type*} [Fintype ι]
    {L ρ T : ℝ} (x : ι → ℝ) (hρ : 0 < ρ)
    (hT : groskinArchimedeanPositivityThreshold ≤ T) (c : ι → ℝ) :
    0 ≤ groskinArchTailScalarGram L ρ x c T :=
  mul_nonneg (groskinArchTailWeight_nonneg hρ hT) (by positivity)

theorem integrableOn_groskinArchTailScalarGram {ι : Type*} [Fintype ι]
    {L ρ T₁ T₂ : ℝ} (x : ι → ℝ) (hρ : 0 < ρ) (hnode : ∀ i, ρ * |x i| < T₁) (c : ι → ℝ) :
    IntegrableOn (groskinArchTailScalarGram L ρ x c) (Set.Icc T₁ T₂) volume := by
  have hint := HTGeometry.integrable_integralMatrixKernelQuadratic volume
    (groskinArchTailWindowKernel L ρ T₁ T₂ x)
    (integrable_groskinArchTailWindowKernel_apply x hρ hnode) c
  refine (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mp ?_
  refine hint.congr (Filter.Eventually.of_forall fun T => ?_)
  rw [HTGeometry.integralMatrixKernelQuadratic, groskinArchTailWindowKernel]
  by_cases hT : T ∈ Set.Icc T₁ T₂
  · rw [Set.indicator_of_mem hT, Set.indicator_of_mem hT, groskinArchTailScalarGram]
    have hquad : dotProduct (star c) ((groskinArchTailKernel L ρ x T).mulVec c)
        = ∑ i, ∑ j, c i * groskinArchTailKernel L ρ x T i j * c j := by
      simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hquad]
    exact groskinArchTailKernel_quadraticForm L ρ x T c
  · rw [Set.indicator_of_notMem hT, Set.indicator_of_notMem hT]
    simp

/-- **The kernel of the tail increment's quadratic form.**  Because the increment's form is the
integral of a nonnegative Cauchy Gram, it vanishes at a coefficient vector exactly when that Gram
vanishes almost everywhere on the cutoff window. -/
theorem groskinArchTailIncrement_quadraticForm_eq_zero_iff {ι : Type*} [Fintype ι]
    {L ρ T₁ T₂ : ℝ} (x : ι → ℝ) (hρ : 0 < ρ) (hnode : ∀ i, ρ * |x i| < T₁)
    (hthreshold : groskinArchimedeanPositivityThreshold ≤ T₁) (c : ι → ℝ) :
    dotProduct (star c) ((groskinArchTailIncrement L ρ T₁ T₂ x).mulVec c) = 0
      ↔ groskinArchTailScalarGram L ρ x c =ᵐ[volume.restrict (Set.Icc T₁ T₂)] 0 := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc T₁ T₂)] groskinArchTailScalarGram L ρ x c := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
    refine Filter.Eventually.of_forall fun T hT => ?_
    exact groskinArchTailScalarGram_nonneg x hρ (hthreshold.trans hT.1) c
  have hform := groskinArchTailIncrement_quadraticForm (L := L) (T₂ := T₂) x hρ hnode c
  rw [show (∫ T in Set.Icc T₁ T₂, groskinArchTailWeight L ρ T *
        ((∑ i, c i * groskinArchTailMinusFeature ρ x T i) ^ 2
          + (∑ i, c i * groskinArchTailPlusFeature ρ x T i) ^ 2))
      = ∫ T in Set.Icc T₁ T₂, groskinArchTailScalarGram L ρ x c T from rfl] at hform
  rw [hform]
  exact MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg
    (integrableOn_groskinArchTailScalarGram x hρ hnode c)

/-- **The kernel of the increment annihilates both Cauchy features.**  Wherever the modulating sine
does not vanish, a coefficient vector in the kernel of the tail increment's form annihilates both
Cauchy feature vectors.  This is the exact input the strictness question needs; the card does not
assert strictness, and none is claimed here. -/
theorem groskinArchTailIncrement_quadraticForm_eq_zero_annihilates {ι : Type*} [Fintype ι]
    {L ρ T₁ T₂ : ℝ} (x : ι → ℝ) (hρ : 0 < ρ) (hnode : ∀ i, ρ * |x i| < T₁)
    (hthreshold : groskinArchimedeanPositivityThreshold ≤ T₁) {c : ι → ℝ}
    (h0 : dotProduct (star c) ((groskinArchTailIncrement L ρ T₁ T₂ x).mulVec c) = 0) :
    ∀ᵐ T ∂(volume.restrict (Set.Icc T₁ T₂)), Real.sin (L * T / 2) ≠ 0 →
      (∑ i, c i * groskinArchTailMinusFeature ρ x T i) = 0 ∧
        (∑ i, c i * groskinArchTailPlusFeature ρ x T i) = 0 := by
  have hae := (groskinArchTailIncrement_quadraticForm_eq_zero_iff x hρ hnode hthreshold c).mp h0
  have hae' := (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hae
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [hae'] with T hT hmem hsin
  have hw : groskinArchTailWeight L ρ T ≠ 0 :=
    groskinArchTailWeight_ne_zero hρ (hthreshold.trans hmem.1) hsin
  have hz : groskinArchTailScalarGram L ρ x c T = 0 := hT hmem
  rw [groskinArchTailScalarGram] at hz
  have hsum : (∑ i, c i * groskinArchTailMinusFeature ρ x T i) ^ 2
      + (∑ i, c i * groskinArchTailPlusFeature ρ x T i) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h hw
    · exact h
  constructor
  · have hA : (∑ i, c i * groskinArchTailMinusFeature ρ x T i) ^ 2 = 0 := by
      nlinarith [sq_nonneg (∑ i, c i * groskinArchTailMinusFeature ρ x T i),
        sq_nonneg (∑ i, c i * groskinArchTailPlusFeature ρ x T i)]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp hA
  · have hB : (∑ i, c i * groskinArchTailPlusFeature ρ x T i) ^ 2 = 0 := by
      nlinarith [sq_nonneg (∑ i, c i * groskinArchTailMinusFeature ρ x T i),
        sq_nonneg (∑ i, c i * groskinArchTailPlusFeature ρ x T i)]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp hB

/-! ### The card's statement in one object -/

/-- **The archimedean tail statement.**  For every positive scale and every finite node family there
is a cutoff window past an analytically produced threshold and past every scaled node, on which the
omitted archimedean tail increment is positive semidefinite, its quadratic form is the
Cauchy--Stieltjes integral of the pointwise Cauchy Gram, and the density generating it has its
column space inside the span of the two Cauchy feature vectors.  No numerical value of the digamma
density enters: the threshold is the analytic one. -/
theorem groskinArchimedeanTailStatement {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ℝ) {ρ : ℝ}
    (hρ : 0 < ρ) (x : ι → ℝ) :
    ∃ T₁ T₂ : ℝ, T₁ < T₂ ∧ groskinArchimedeanPositivityThreshold ≤ T₁ ∧ (∀ i, ρ * |x i| < T₁) ∧
      (groskinArchTailIncrement L ρ T₁ T₂ x).PosSemidef ∧
      (∀ c : ι → ℝ, dotProduct (star c) ((groskinArchTailIncrement L ρ T₁ T₂ x).mulVec c)
        = ∫ T in Set.Icc T₁ T₂, groskinArchTailScalarGram L ρ x c T) ∧
      (∀ T : ℝ, LinearMap.range (Matrix.mulVecLin (groskinArchTailKernel L ρ x T))
        ≤ Submodule.span ℝ
            {groskinArchTailMinusFeature ρ x T, groskinArchTailPlusFeature ρ x T}) := by
  obtain ⟨T₁, T₂, hlt, hthreshold, hnode⟩ := exists_groskinArchTailWindow ρ x
  refine ⟨T₁, T₂, hlt, hthreshold, hnode,
    groskinArchTailIncrement_posSemidef x hρ hthreshold hnode, fun c => ?_,
    fun T => range_groskinArchTailKernel_le_span L ρ x T⟩
  exact groskinArchTailIncrement_quadraticForm x hρ hnode c

end RHTower
