import GaloisForLFunctions.RHTower.WallPositionDerivative
import GaloisForLFunctions.RHTower.WallFrequencyFirstBoundary
import GaloisForLFunctions.RHTower.WallTailRayEstimates
import GaloisForLFunctions.HTGeometry.InverseFamilyThirdDerivative

/-!
# The second boundary term after multiplication by the frequency

The second boundary term has one power of `(1+|x|)^{-1}` from the resolvent derivative, so
multiplying by the frequency leaves it merely *bounded* — not square integrable.  The oscillation
is what saves it: `∂_L e^{-iLx} = -ix e^{-iLx}`, so integrating by parts in the **position** trades
the frequency for either one more resolvent power (the amplitude's own position derivative) or the
block profile's derivative.  Both keep the decay `(1+|x|)^{-1}`, which is square integrable on a
terminal ray.

The boundary terms of that integration by parts vanish because a differentiable profile supported in
a closed block vanishes at both endpoints — its complement is open, so the profile is eventually
zero on both sides.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {T : X →L[ℂ] X}

/-- The position integrand of the second boundary term. -/
def secondBoundaryIntegrand (T : X →L[ℂ] X) (g : ℝ → X) (σ x : ℝ) (L : ℝ) : X :=
  Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
    • (invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g L))

/-- Its position derivative. -/
def secondBoundaryIntegrandDeriv (T : X →L[ℂ] X) (g g' : ℝ → X) (σ x : ℝ) (L : ℝ) : X :=
  (-(Complex.I) * (x : ℂ)) • secondBoundaryIntegrand T g σ x L
    + Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
      • (wallSecondAmplitudePosDeriv T σ x L (g L)
        + invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g' L))

/-- The position derivative of the second boundary integrand. -/
theorem hasDerivAt_secondBoundaryIntegrand {σ x : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g g' : ℝ → X} (hg : ∀ L : ℝ, HasDerivAt g (g' L) L) {L : ℝ}
    (hgap : 0 < wallFloor T σ x + L) :
    HasDerivAt (secondBoundaryIntegrand T g σ x)
      (secondBoundaryIntegrandDeriv T g g' σ x L) L := by
  have hphase : HasDerivAt (fun M : ℝ => Complex.exp (-(Complex.I) * (M : ℂ) * (x : ℂ)))
      ((-(Complex.I) * (x : ℂ)) * Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))) L := by
    have hlin : HasDerivAt (fun M : ℝ => -(Complex.I) * (M : ℂ) * (x : ℂ))
        (-(Complex.I) * (x : ℂ)) L := by
      have h1 : HasDerivAt (fun M : ℝ => (M : ℂ)) 1 L := Complex.ofRealCLM.hasDerivAt
      have h2 := (h1.const_mul (-(Complex.I))).mul_const (x : ℂ)
      refine h2.congr_deriv ?_
      ring
    have := hlin.cexp
    refine this.congr_deriv ?_
    ring
  have hamp : HasDerivAt
      (fun M : ℝ => invFamilyProduct (wallGeneratorShift T σ M) (wallGeneratorD1 X σ) x)
      (wallSecondAmplitudePosDeriv T σ x L) L :=
    hasDerivAt_wallSecondAmplitude_position hσ0 hσ1 hgap
  have hampR : HasDerivAt
      (fun M : ℝ =>
        (invFamilyProduct (wallGeneratorShift T σ M) (wallGeneratorD1 X σ) x).restrictScalars ℝ)
      ((wallSecondAmplitudePosDeriv T σ x L).restrictScalars ℝ) L :=
    (ContinuousLinearMap.restrictScalarsL ℂ X X ℝ ℝ).hasFDerivAt.comp_hasDerivAt L hamp
  have happ : HasDerivAt
      (fun M : ℝ => invFamilyProduct (wallGeneratorShift T σ M) (wallGeneratorD1 X σ) x (g M))
      (wallSecondAmplitudePosDeriv T σ x L (g L)
        + invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g' L)) L :=
    hampR.clm_apply (hg L)
  have h := hphase.smul happ
  refine h.congr_deriv ?_
  rw [secondBoundaryIntegrandDeriv, secondBoundaryIntegrand, ← smul_smul]
  abel

/-! ## Continuity in the position -/

/-- The resolvent's position derivative is continuous where the floor is open. -/
theorem continuousOn_wallResolventPosDeriv {σ x : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {S : Set ℝ}
    (hgap : ∀ L ∈ S, 0 < wallFloor T σ x + L) :
    ContinuousOn (fun L : ℝ => wallResolventPosDeriv T σ x L) S :=
  continuousOn_invFamilyDeriv_of_unit
    (fun L _ => hasDerivAt_wallGeneratorShift_position T σ x L)
    (fun L hL => isUnit_wallGeneratorShift hσ0 hσ1 (hgap L hL)) continuousOn_const

/-- The block resolvent is continuous in the position. -/
theorem continuousOn_invFamily_pos {σ x : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {S : Set ℝ}
    (hgap : ∀ L ∈ S, 0 < wallFloor T σ x + L) :
    ContinuousOn (fun L : ℝ => invFamily (wallGeneratorShift T σ L) x) S :=
  continuousOn_invFamily_of_unit
    (fun L _ => hasDerivAt_wallGeneratorShift_position T σ x L)
    (fun L hL => isUnit_wallGeneratorShift hσ0 hσ1 (hgap L hL))

/-- The second amplitude's position derivative is continuous. -/
theorem continuousOn_wallSecondAmplitudePosDeriv {σ x : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {S : Set ℝ} (hgap : ∀ L ∈ S, 0 < wallFloor T σ x + L) :
    ContinuousOn (fun L : ℝ => wallSecondAmplitudePosDeriv T σ x L) S := by
  have hA := continuousOn_invFamily_pos hσ0 hσ1 hgap
  have hD := continuousOn_wallResolventPosDeriv hσ0 hσ1 hgap
  have h : ContinuousOn (fun L : ℝ =>
      -(wallResolventPosDeriv T σ x L * invFamily (wallGeneratorShift T σ L) x
          * wallGeneratorD1 X σ x * invFamily (wallGeneratorShift T σ L) x)
        - (invFamily (wallGeneratorShift T σ L) x * wallResolventPosDeriv T σ x L
          * wallGeneratorD1 X σ x * invFamily (wallGeneratorShift T σ L) x)
        - (invFamily (wallGeneratorShift T σ L) x * invFamily (wallGeneratorShift T σ L) x
          * wallGeneratorD1 X σ x * wallResolventPosDeriv T σ x L)) S :=
    ((((hD.mul hA).mul continuousOn_const).mul hA).neg.sub
      (((hA.mul hD).mul continuousOn_const).mul hA)).sub
      (((hA.mul hA).mul continuousOn_const).mul hD)
  exact h

/-- The second amplitude is continuous in the position. -/
theorem continuousOn_invFamilyProduct_pos {σ x : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {S : Set ℝ}
    (hgap : ∀ L ∈ S, 0 < wallFloor T σ x + L) :
    ContinuousOn (fun L : ℝ =>
      invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x) S := by
  have hA := continuousOn_invFamily_pos hσ0 hσ1 hgap
  have h : ContinuousOn (fun L : ℝ =>
      invFamily (wallGeneratorShift T σ L) x
        * -(invFamily (wallGeneratorShift T σ L) x * wallGeneratorD1 X σ x
          * invFamily (wallGeneratorShift T σ L) x)) S :=
    hA.mul (((hA.mul continuousOn_const).mul hA).neg)
  exact h

/-! ## The position integration by parts -/

omit [CompleteSpace X] in
/-- A differentiable profile vanishing off a closed block vanishes at both endpoints. -/
theorem block_endpoints_eq_zero {g g' : ℝ → X} {m : ℝ} (hg : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) : g m = 0 ∧ g (m + 1) = 0 := by
  constructor
  · have hne : (nhdsWithin m (Iio m)).NeBot := nhdsLT_neBot m
    have h1 : Filter.Tendsto g (nhdsWithin m (Iio m)) (nhds (g m)) :=
      ((hg m).continuousAt).continuousWithinAt.tendsto
    have h2 : Filter.Tendsto g (nhdsWithin m (Iio m)) (nhds 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hsupp y (fun hc => absurd hc.1 (not_le.mpr hy))).symm
    exact tendsto_nhds_unique h1 h2
  · have hne : (nhdsWithin (m + 1) (Ioi (m + 1))).NeBot := nhdsGT_neBot (m + 1)
    have h1 : Filter.Tendsto g (nhdsWithin (m + 1) (Ioi (m + 1))) (nhds (g (m + 1))) :=
      ((hg (m + 1)).continuousAt).continuousWithinAt.tendsto
    have h2 : Filter.Tendsto g (nhdsWithin (m + 1) (Ioi (m + 1))) (nhds 0) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hsupp y (fun hc => absurd hc.2 (not_le.mpr hy))).symm
    exact tendsto_nhds_unique h1 h2

/-- The position derivative is interval integrable on the block. -/
theorem intervalIntegrable_secondBoundaryIntegrandDeriv {σ x m : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g g' : ℝ → X} (hg : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hg'int : IntegrableOn g' (Icc m (m + 1)))
    (hgap : ∀ L ∈ Icc m (m + 1), 0 < wallFloor T σ x + L) :
    IntervalIntegrable (secondBoundaryIntegrandDeriv T g g' σ x) volume m (m + 1) := by
  have hle : m ≤ m + 1 := by linarith
  have hset : uIcc m (m + 1) = Icc m (m + 1) := uIcc_of_le hle
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun L => (hg L).continuousAt
  have hphase : Continuous fun L : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) := by
    fun_prop
  have hamp := continuousOn_wallSecondAmplitudePosDeriv (T := T) (x := x) hσ0 hσ1 hgap
  have hA := continuousOn_invFamilyProduct_pos (T := T) (x := x) hσ0 hσ1 hgap
  -- the three pieces
  have h1 : ContinuousOn (fun L : ℝ =>
      (-(Complex.I) * (x : ℂ)) • secondBoundaryIntegrand T g σ x L) (Icc m (m + 1)) := by
    have h : ContinuousOn (fun L : ℝ => (-(Complex.I) * (x : ℂ))
        • (Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
          • (invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g L))))
        (Icc m (m + 1)) :=
      ((hphase.continuousOn.smul (hA.clm_apply hgc.continuousOn)).const_smul _)
    exact h
  have h2 : ContinuousOn (fun L : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
      • (wallSecondAmplitudePosDeriv T σ x L (g L))) (Icc m (m + 1)) :=
    hphase.continuousOn.smul (hamp.clm_apply hgc.continuousOn)
  have h3 : IntegrableOn (fun L : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
      • (invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g' L)))
      (Icc m (m + 1)) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := m) (b := m + 1)).exists_bound_of_continuousOn hA
    have hmeas : AEStronglyMeasurable (fun L : ℝ =>
        Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
          • (invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g' L)))
        (volume.restrict (Icc m (m + 1))) := by
      refine (hphase.continuousOn.aestronglyMeasurable measurableSet_Icc).smul ?_
      exact ContinuousLinearMap.aestronglyMeasurable_comp₂ (ContinuousLinearMap.apply ℂ X)
        hg'int.aestronglyMeasurable (hA.aestronglyMeasurable measurableSet_Icc)
    refine Integrable.mono' (hg'int.norm.const_mul C) hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with L hL
    rw [norm_smul, norm_expPhase, one_mul]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hC L hL) (norm_nonneg _))
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
  have hsum : IntegrableOn (secondBoundaryIntegrandDeriv T g g' σ x) (Icc m (m + 1)) := by
    have hc1 : IntegrableOn (fun L : ℝ =>
        (-(Complex.I) * (x : ℂ)) • secondBoundaryIntegrand T g σ x L) (Icc m (m + 1)) :=
      h1.integrableOn_compact isCompact_Icc
    have hc2 : IntegrableOn (fun L : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
        • (wallSecondAmplitudePosDeriv T σ x L (g L))) (Icc m (m + 1)) :=
      h2.integrableOn_compact isCompact_Icc
    have hc3 := hc2.add h3
    have hfin := hc1.add hc3
    refine hfin.congr (Filter.Eventually.of_forall fun L => ?_)
    show (-(Complex.I) * (x : ℂ)) • secondBoundaryIntegrand T g σ x L
        + (Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
            • (wallSecondAmplitudePosDeriv T σ x L (g L))
          + Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
            • (invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g' L)))
      = secondBoundaryIntegrandDeriv T g g' σ x L
    rw [secondBoundaryIntegrandDeriv, smul_add]
  exact hsum

omit [CompleteSpace X] in
/-- The unit block as an interval integral. -/
theorem integral_interval_eq_block {f : ℝ → X} {m : ℝ} :
    (∫ L in m..(m + 1), f L) = ∫ L in Icc m (m + 1), f L := by
  rw [intervalIntegral.integral_of_le (by linarith : m ≤ m + 1)]
  exact setIntegral_congr_set Ioc_ae_eq_Icc

/-- **Multiplication by the frequency, on the second boundary term.**  Integrating by parts in the
position trades the frequency for either one more resolvent power or the block profile's own
derivative. -/
theorem freq_smul_secondBoundary_eq {σ x m : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g g' : ℝ → X} (hg : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    (hg'int : IntegrableOn g' (Icc m (m + 1)))
    (hgap : ∀ L ∈ Icc m (m + 1), 0 < wallFloor T σ x + L) :
    (x : ℂ) • secondBoundary T g m σ x
      = (-Complex.I) • ∫ L in Icc m (m + 1),
          Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
            • (wallSecondAmplitudePosDeriv T σ x L (g L)
              + invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g' L)) := by
  have hle : m ≤ m + 1 := by linarith
  have hset : uIcc m (m + 1) = Icc m (m + 1) := uIcc_of_le hle
  have hint := intervalIntegrable_secondBoundaryIntegrandDeriv (T := T) hσ0 hσ1 hg hg'int hgap
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := secondBoundaryIntegrand T g σ x)
    (f' := secondBoundaryIntegrandDeriv T g g' σ x)
    (fun L hL => hasDerivAt_secondBoundaryIntegrand hσ0 hσ1 hg
      (hgap L (by rwa [hset] at hL))) hint
  obtain ⟨hgm, hgm1⟩ := block_endpoints_eq_zero hg hsupp
  have hzero : (∫ L in m..(m + 1), secondBoundaryIntegrandDeriv T g g' σ x L) = 0 := by
    rw [hFTC]
    show Complex.exp (-(Complex.I) * ((m + 1 : ℝ) : ℂ) * (x : ℂ))
        • (invFamilyProduct (wallGeneratorShift T σ (m + 1)) (wallGeneratorD1 X σ) x (g (m + 1)))
      - Complex.exp (-(Complex.I) * ((m : ℝ) : ℂ) * (x : ℂ))
        • (invFamilyProduct (wallGeneratorShift T σ m) (wallGeneratorD1 X σ) x (g m)) = 0
    rw [hgm, hgm1, map_zero, map_zero, smul_zero, smul_zero, sub_zero]
  -- the two pieces are separately interval integrable
  have hI1 : IntervalIntegrable
      (fun L : ℝ => (-(Complex.I) * (x : ℂ)) • secondBoundaryIntegrand T g σ x L)
      volume m (m + 1) := by
    have hgc : Continuous g := continuous_iff_continuousAt.mpr fun L => (hg L).continuousAt
    have hphase : Continuous fun L : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) := by
      fun_prop
    have hA := continuousOn_invFamilyProduct_pos (T := T) (x := x) hσ0 hσ1 hgap
    have h : ContinuousOn (fun L : ℝ => (-(Complex.I) * (x : ℂ))
        • (Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
          • (invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g L))))
        (uIcc m (m + 1)) := by
      rw [hset]
      exact ((hphase.continuousOn.smul (hA.clm_apply hgc.continuousOn)).const_smul _)
    exact h.intervalIntegrable
  have hI2 : IntervalIntegrable
      (fun L : ℝ => Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
        • (wallSecondAmplitudePosDeriv T σ x L (g L)
          + invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g' L)))
      volume m (m + 1) := by
    have hd := hint
    have : IntervalIntegrable
        (fun L : ℝ => secondBoundaryIntegrandDeriv T g g' σ x L
          - (-(Complex.I) * (x : ℂ)) • secondBoundaryIntegrand T g σ x L) volume m (m + 1) :=
      hd.sub hI1
    refine this.congr (fun L _ => ?_)
    show secondBoundaryIntegrandDeriv T g g' σ x L
        - (-(Complex.I) * (x : ℂ)) • secondBoundaryIntegrand T g σ x L
      = Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
        • (wallSecondAmplitudePosDeriv T σ x L (g L)
          + invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g' L))
    rw [secondBoundaryIntegrandDeriv]
    abel
  have hsplit : (∫ L in m..(m + 1), secondBoundaryIntegrandDeriv T g g' σ x L)
      = (-(Complex.I) * (x : ℂ)) • (∫ L in m..(m + 1), secondBoundaryIntegrand T g σ x L)
        + ∫ L in m..(m + 1), Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
          • (wallSecondAmplitudePosDeriv T σ x L (g L)
            + invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g' L)) := by
    rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_add hI1 hI2]
    refine intervalIntegral.integral_congr fun L _ => ?_
    show secondBoundaryIntegrandDeriv T g g' σ x L
      = (-(Complex.I) * (x : ℂ)) • secondBoundaryIntegrand T g σ x L
        + Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
          • (wallSecondAmplitudePosDeriv T σ x L (g L)
            + invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g' L))
    rw [secondBoundaryIntegrandDeriv]
  have hS : (∫ L in m..(m + 1), secondBoundaryIntegrand T g σ x L) = secondBoundary T g m σ x := by
    rw [integral_interval_eq_block, secondBoundary]
    rfl
  rw [hzero, hS, integral_interval_eq_block] at hsplit
  have hkey : (-(Complex.I) * (x : ℂ)) • secondBoundary T g m σ x
      = -(∫ L in Icc m (m + 1), Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
        • (wallSecondAmplitudePosDeriv T σ x L (g L)
          + invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g' L))) :=
    eq_neg_of_add_eq_zero_left hsplit.symm
  have hII : (Complex.I : ℂ) * (-(Complex.I) * (x : ℂ)) = (x : ℂ) := by
    rw [← mul_assoc]
    simp [Complex.I_mul_I]
  have hmul := congrArg (fun v : X => (Complex.I : ℂ) • v) hkey
  simp only [smul_smul, hII] at hmul
  rw [hmul, smul_neg, ← neg_smul]

/-- **The second boundary term keeps its frequency decay after multiplication by the frequency.** -/
theorem norm_freq_smul_secondBoundary_le {σ x m μ₀ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    {g g' : ℝ → X} (hg : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    (hgint : IntegrableOn g (Icc m (m + 1))) (hg'int : IntegrableOn g' (Icc m (m + 1)))
    {A B : ℝ} (hA : (∫ L in Icc m (m + 1), ‖g L‖) ≤ A)
    (hB : (∫ L in Icc m (m + 1), ‖g' L‖) ≤ B)
    (hx : 1 ≤ |x|) (hfloor : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L) :
    ‖x • secondBoundary T g m σ x‖
      ≤ (3 * (μ₀⁻¹) ^ 4 * (3 + Real.pi) * A + (μ₀⁻¹) ^ 3 * (3 + Real.pi) * B)
        * (1 + |x|) ^ (-(1 : ℝ)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hgap : ∀ L ∈ Icc m (m + 1), 0 < wallFloor T σ x + L := fun L hL =>
    lt_of_lt_of_le hμ (hfloor L hL)
  have hcoe : x • secondBoundary T g m σ x = (x : ℂ) • secondBoundary T g m σ x :=
    (Complex.coe_smul x _).symm
  rw [hcoe, freq_smul_secondBoundary_eq hσ0 hσ1 hg hsupp hg'int hgap]
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  have hbound : ∀ L ∈ Icc m (m + 1),
      ‖Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ))
        • (wallSecondAmplitudePosDeriv T σ x L (g L)
          + invFamilyProduct (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) x (g' L))‖
      ≤ ((3 * (μ₀⁻¹) ^ 4 * (3 + Real.pi)) * (1 + |x|)⁻¹) * ‖g L‖
        + (((μ₀⁻¹) ^ 3 * (3 + Real.pi)) * (1 + |x|)⁻¹) * ‖g' L‖ := by
    intro L hL
    rw [norm_smul, norm_expPhase, one_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      exact mul_le_mul_of_nonneg_right
        (norm_wallSecondAmplitudePosDeriv_le hσ0 hσ1 hμ hx (hfloor L hL)) (norm_nonneg _)
    · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      exact mul_le_mul_of_nonneg_right
        (norm_invFamilyProduct_wallGeneratorShift_le' hσ0 hσ1 hμ hx (hfloor L hL)) (norm_nonneg _)
  have hmaj : IntegrableOn (fun L : ℝ =>
      ((3 * (μ₀⁻¹) ^ 4 * (3 + Real.pi)) * (1 + |x|)⁻¹) * ‖g L‖
        + (((μ₀⁻¹) ^ 3 * (3 + Real.pi)) * (1 + |x|)⁻¹) * ‖g' L‖) (Icc m (m + 1)) :=
    (hgint.norm.const_mul _).add (hg'int.norm.const_mul _)
  have hle := MeasureTheory.norm_integral_le_of_norm_le hmaj
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with L hL using hbound L hL)
  rw [integral_add (hgint.norm.const_mul _) (hg'int.norm.const_mul _),
    integral_const_mul, integral_const_mul] at hle
  rw [Real.rpow_neg_one]
  refine hle.trans ?_
  have hw : (0 : ℝ) < (1 + |x|)⁻¹ := by positivity
  have hc₁ : (0 : ℝ) ≤ 3 * (μ₀⁻¹) ^ 4 * (3 + Real.pi) := by positivity
  have hc₂ : (0 : ℝ) ≤ (μ₀⁻¹) ^ 3 * (3 + Real.pi) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hA (mul_nonneg hc₁ hw.le),
    mul_le_mul_of_nonneg_left hB (mul_nonneg hc₂ hw.le)]

end GaloisForLFunctions.RHTower
