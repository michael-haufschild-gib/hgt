import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayGlobalJointReflection

/-!
# Absolute integrability of one complete primitive theta ray

A fixed common-scale ray is a nonnegative subseries of the full ordered atom-pair density.  Its
finite-core current is therefore dominated in norm by the already-integrable full symmetric
correlation kernel.  Transporting this domination through the exact arithmetic-polar Jacobian
discharges the Fubini premise in the global joint reflection theorem.
-/

open Complex Real Polynomial MeasureTheory Set

namespace RHTower

noncomputable section

/-- The common-scale density carried by one positive arithmetic direction. -/
def thetaCuspPrimitiveRayDensityPair (a b : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑' g : ℕ,
    thetaCuspTailSecondDensityAtom (a * (g + 1)) p.1 *
      thetaCuspTailSecondDensityAtom (b * (g + 1)) p.2

/-- The corresponding Cartesian finite-core current integrand. -/
def thetaCuspPrimitiveRayCartesianCoreIntegrand
    (a b : ℕ) (d : ℕ) (z : ℂ) (p : ℝ × ℝ) : ℝ :=
  thetaCuspPrimitiveRayDensityPair a b p *
    xiCTaylorThetaTailCorePairCurrent d z p

private theorem continuous_thetaCuspTailSecondDensityAtom_all (n : ℕ) :
    Continuous (thetaCuspTailSecondDensityAtom n) := by
  unfold thetaCuspTailSecondDensityAtom
  exact continuous_const.mul (continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_thetaCuspPolynomialAtom
      (thetaCuspTailDerivativePolynomial 2) n x).continuousAt)

theorem measurable_thetaCuspPrimitiveRayDensityPair (a b : ℕ) :
    Measurable (thetaCuspPrimitiveRayDensityPair a b) := by
  unfold thetaCuspPrimitiveRayDensityPair
  apply Measurable.tsum
  intro g
  exact ((continuous_thetaCuspTailSecondDensityAtom_all (a * (g + 1))).comp
    continuous_fst).measurable.mul
      (((continuous_thetaCuspTailSecondDensityAtom_all (b * (g + 1))).comp
        continuous_snd).measurable)

theorem continuous_xiCTaylorThetaTailCorePairCurrent (d : ℕ) (z : ℂ) :
    Continuous (xiCTaylorThetaTailCorePairCurrent d z) := by
  unfold xiCTaylorThetaTailCorePairCurrent
  have hterm1 :=
    ((continuous_thetaCuspTailSecondCoreAtomDerivative d z).comp
      continuous_fst).mul
        (Complex.continuous_conj.comp
          ((continuous_thetaCuspTailSecondCoreAtom d z).comp continuous_snd))
  have hterm2 :=
    ((continuous_thetaCuspTailSecondCoreAtomDerivative d z).comp
      continuous_snd).mul
        (Complex.continuous_conj.comp
          ((continuous_thetaCuspTailSecondCoreAtom d z).comp continuous_fst))
  exact ((Complex.continuous_im.comp hterm1).add
    (Complex.continuous_im.comp hterm2)).div_const 2

theorem thetaCuspPrimitiveRayDensityPair_nonneg
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {p : ℝ × ℝ}
    (hp : p ∈ thetaCuspPositiveQuadrantSet) :
    0 ≤ thetaCuspPrimitiveRayDensityPair a b p := by
  unfold thetaCuspPrimitiveRayDensityPair
  apply tsum_nonneg
  intro g
  exact mul_nonneg
    (thetaCuspTailSecondDensityAtom_pos
      (Nat.mul_pos ha (Nat.succ_pos g)) hp.1.le).le
    (thetaCuspTailSecondDensityAtom_pos
      (Nat.mul_pos hb (Nat.succ_pos g)) hp.2.le).le

/-- A complete common-scale ray is pointwise bounded by the full canonical density product on the
positive quadrant. -/
theorem thetaCuspPrimitiveRayDensityPair_le_full
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {p : ℝ × ℝ}
    (hp : p ∈ thetaCuspPositiveQuadrantSet) :
    thetaCuspPrimitiveRayDensityPair a b p ≤
      thetaCuspTailSecondDensity p.1 * thetaCuspTailSecondDensity p.2 := by
  let F : ℕ × ℕ → ℝ := fun q =>
    thetaCuspTailSecondDensityAtom (q.1 + 1) p.1 *
      thetaCuspTailSecondDensityAtom (q.2 + 1) p.2
  let i : ℕ → ℕ × ℕ := fun g =>
    ((a * (g + 1)).pred, (b * (g + 1)).pred)
  have hFsum : Summable F :=
    summable_thetaCuspTailSecondDensityAtom_pair p.1 p.2
  have hF0 (q : ℕ × ℕ) : 0 ≤ F q := by
    exact mul_nonneg
      (thetaCuspTailSecondDensityAtom_pos (Nat.succ_pos q.1) hp.1.le).le
      (thetaCuspTailSecondDensityAtom_pos (Nat.succ_pos q.2) hp.2.le).le
  have hi : Function.Injective i := by
    intro g h hgh
    have hfirst := congrArg (fun q : ℕ × ℕ => q.1 + 1) hgh
    dsimp only [i] at hfirst
    have hpredg : (a * (g + 1)).pred + 1 = a * (g + 1) := by
      simpa only [Nat.add_one] using
        Nat.succ_pred_eq_of_pos (Nat.mul_pos ha (Nat.succ_pos g))
    have hpredh : (a * (h + 1)).pred + 1 = a * (h + 1) := by
      simpa only [Nat.add_one] using
        Nat.succ_pred_eq_of_pos (Nat.mul_pos ha (Nat.succ_pos h))
    rw [hpredg, hpredh] at hfirst
    exact Nat.succ.inj (Nat.mul_left_cancel ha hfirst)
  calc
    thetaCuspPrimitiveRayDensityPair a b p = ∑' g : ℕ, F (i g) := by
      unfold thetaCuspPrimitiveRayDensityPair
      apply tsum_congr
      intro g
      dsimp only [F, i]
      have hpreda : (a * (g + 1)).pred + 1 = a * (g + 1) := by
        simpa only [Nat.add_one] using
          Nat.succ_pred_eq_of_pos (Nat.mul_pos ha (Nat.succ_pos g))
      have hpredb : (b * (g + 1)).pred + 1 = b * (g + 1) := by
        simpa only [Nat.add_one] using
          Nat.succ_pred_eq_of_pos (Nat.mul_pos hb (Nat.succ_pos g))
      rw [hpreda, hpredb]
    _ ≤ ∑' q : ℕ × ℕ, F q :=
      tsum_comp_le_tsum_of_inj hFsum hF0 hi
    _ = thetaCuspTailSecondDensity p.1 * thetaCuspTailSecondDensity p.2 := by
      exact (thetaCuspTailSecondDensity_mul_eq_tsum_atomPair p.1 p.2).symm

/-- The Cartesian current on one complete primitive ray is absolutely integrable on the positive
source quadrant. -/
theorem integrableOn_thetaCuspPrimitiveRayCartesianCoreIntegrand
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (d : ℕ) (z : ℂ) :
    IntegrableOn (thetaCuspPrimitiveRayCartesianCoreIntegrand a b d z)
      thetaCuspPositiveQuadrantSet := by
  let mu : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))
  have hfull : Integrable
      (xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z) mu :=
    integrable_xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z
  have hmeas : AEStronglyMeasurable
      (thetaCuspPrimitiveRayCartesianCoreIntegrand a b d z) mu :=
    ((measurable_thetaCuspPrimitiveRayDensityPair a b).mul
      (continuous_xiCTaylorThetaTailCorePairCurrent d z).measurable).aestronglyMeasurable
  have hmem : ∀ᵐ p ∂mu, p ∈ thetaCuspPositiveQuadrantSet := by
    dsimp only [mu, thetaCuspPositiveQuadrantSet]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have hcore : Integrable
      (thetaCuspPrimitiveRayCartesianCoreIntegrand a b d z) mu := by
    apply Integrable.mono hfull hmeas
    filter_upwards [hmem] with p hp
    have hray0 := thetaCuspPrimitiveRayDensityPair_nonneg ha hb hp
    have hrayle := thetaCuspPrimitiveRayDensityPair_le_full ha hb hp
    have hfull0 :
        0 ≤ thetaCuspTailSecondDensity p.1 * thetaCuspTailSecondDensity p.2 :=
      mul_nonneg (thetaCuspTailSecondDensity_pos hp.1).le
        (thetaCuspTailSecondDensity_pos hp.2).le
    rw [xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_density_mul]
    unfold thetaCuspPrimitiveRayCartesianCoreIntegrand
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hray0,
      abs_of_nonneg hfull0]
    exact mul_le_mul_of_nonneg_right hrayle
      (abs_nonneg (xiCTaylorThetaTailCorePairCurrent d z p))
  change Integrable
    (thetaCuspPrimitiveRayCartesianCoreIntegrand a b d z)
      (volume.restrict thetaCuspPositiveQuadrantSet)
  rw [show volume.restrict thetaCuspPositiveQuadrantSet = mu by
    dsimp only [mu, thetaCuspPositiveQuadrantSet]
    rw [Measure.prod_restrict, Measure.volume_eq_prod]]
  exact hcore

/-- Absolute integrability transported through the exact arithmetic-polar Jacobian. -/
theorem integrableOn_thetaCuspPrimitiveRayPolarCoreIntegrand
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (d : ℕ) (z : ℂ) :
    IntegrableOn (thetaCuspPrimitiveRayPolarCoreIntegrand a b d z)
      (thetaCuspPrimitiveRayActiveSet a b) := by
  have htransport :=
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (μ := volume)
      (measurableSet_thetaCuspPrimitiveRayActiveSet a b)
      (fun q hq =>
        (hasFDerivAt_thetaCuspPrimitiveRayCartesianMap a b hq.1 hq.2.1).hasFDerivWithinAt)
      (thetaCuspPrimitiveRayCartesianMap_injectiveOn ha hb)
      (thetaCuspPrimitiveRayCartesianCoreIntegrand a b d z)
  rw [thetaCuspPrimitiveRayCartesianMap_image_activeSet ha hb] at htransport
  have hraw := htransport.mp
    (integrableOn_thetaCuspPrimitiveRayCartesianCoreIntegrand ha hb d z)
  apply hraw.congr
  filter_upwards [ae_restrict_mem (measurableSet_thetaCuspPrimitiveRayActiveSet a b)] with q hq
  have hweight :=
    tsum_thetaCuspTailSecondDensityAtom_arithmeticPolar_mul_jacobian_eq_seamWeight
      ha hb q.1 hq.1 hq.2.1
  unfold thetaCuspPrimitiveRayPolarCoreIntegrand
    thetaCuspPrimitiveRayCartesianCoreIntegrand
    thetaCuspPrimitiveRayDensityPair
    thetaCuspPrimitiveRayCartesianMap
  rw [det_thetaCuspPrimitiveRayCartesianFDeriv hq.1 hq.2.1,
    abs_thetaCuspPrimitiveRayArithmeticPolarSignedJacobian hq.1 hq.2.1]
  simp only [smul_eq_mul]
  rw [show thetaCuspPrimitiveRayArithmeticPolarJacobian q.2 *
        ((∑' g : ℕ,
          thetaCuspTailSecondDensityAtom (a * (g + 1))
              (thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2) *
            thetaCuspTailSecondDensityAtom (b * (g + 1))
              (thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2)) *
          xiCTaylorThetaTailCorePairCurrent d z
            (thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2,
              thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2)) =
      ((∑' g : ℕ,
          thetaCuspTailSecondDensityAtom (a * (g + 1))
              (thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2) *
            thetaCuspTailSecondDensityAtom (b * (g + 1))
              (thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2)) *
        thetaCuspPrimitiveRayArithmeticPolarJacobian q.2) *
          xiCTaylorThetaTailCorePairCurrent d z
            (thetaCuspPrimitiveRayArithmeticPolarX a q.1 q.2,
              thetaCuspPrimitiveRayArithmeticPolarY b q.1 q.2) by ring,
    hweight]
  rw [thetaCuspPrimitiveRayArithmeticPolarX_eq_corePolarX,
    thetaCuspPrimitiveRayArithmeticPolarY_eq_corePolarY]
  unfold thetaCuspPrimitiveRayCorePolarKernel
  ring

/-- **Unconditional global joint reflection on one complete primitive ray.**  Absolute
integrability is supplied by domination by the full canonical density-current kernel, so the
global seam-preserving identity has no remaining analytic premise. -/
theorem integral_thetaCuspPrimitiveRayDensityPair_mul_coreCurrent_eq_globalJoint_unconditional
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (d : ℕ) (z : ℂ) :
    (∫ p in thetaCuspPositiveQuadrantSet,
      (∑' g : ℕ,
        thetaCuspTailSecondDensityAtom (a * (g + 1)) p.1 *
          thetaCuspTailSecondDensityAtom (b * (g + 1)) p.2) *
        xiCTaylorThetaTailCorePairCurrent d z p) =
      ∫ r : ℝ in Ici (thetaCuspPrimitiveRayRadialLog a b 0 0),
        (8 * Real.exp
          (-(Real.log (a : ℝ) + Real.log (b : ℝ)) / 2)) *
        thetaCuspPrimitiveRayJointSeamIntegrand d z r
          (-Real.log (a : ℝ)) (-Real.log (b : ℝ)) := by
  apply integral_thetaCuspPrimitiveRayDensityPair_mul_coreCurrent_eq_globalJoint
    ha hb d z
  have hint :=
    (integrableOn_thetaCuspPrimitiveRayPolarCoreIntegrand ha hb d z).integrable_indicator
      (measurableSet_thetaCuspPrimitiveRayActiveSet a b)
  rw [Measure.volume_eq_prod] at hint
  exact hint

end

end RHTower
