import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayIntegrability

/-!
# Global reassembly of complete primitive theta rays

The positive square-index lattice is regrouped by coprime direction after absolute convergence
has been established.  This is the global arithmetic counterpart of the one-ray joint reflection.
-/

open Complex Real Polynomial MeasureTheory Set

namespace RHTower

noncomputable section

deriving instance Countable for ThetaCuspPrimitiveDirection

/-- The full common-scale density carried by one coprime positive direction. -/
def thetaCuspPrimitiveDirectionDensityPair
    (q : ThetaCuspPrimitiveDirection) (p : ℝ × ℝ) : ℝ :=
  ∑' g : ℕ+,
    thetaCuspTailSecondDensityAtom (q.1.1 * g) p.1 *
      thetaCuspTailSecondDensityAtom (q.1.2 * g) p.2

private theorem summable_thetaCuspTailSecondDensityAtom_pnat_reassembly (x : ℝ) :
    Summable (fun n : ℕ+ => thetaCuspTailSecondDensityAtom n x) := by
  have hnat : Summable
      (fun k : ℕ => thetaCuspTailSecondDensityAtom (k + 1) x) := by
    unfold thetaCuspTailSecondDensityAtom
    simpa only using (summable_thetaCuspTailDerivative 2 x).mul_left 4
  have h := (Equiv.pnatEquivNat.summable_iff).mpr hnat
  apply h.congr
  intro n
  simp only [Function.comp_apply, Equiv.pnatEquivNat_apply]
  rw [PNat.natPred_add_one]

private theorem summable_thetaCuspTailSecondDensityAtom_pair_pnat_reassembly
    (x y : ℝ) :
    Summable (fun q : ℕ+ × ℕ+ =>
      thetaCuspTailSecondDensityAtom q.1 x *
        thetaCuspTailSecondDensityAtom q.2 y) :=
  summable_mul_of_summable_norm
    (summable_thetaCuspTailSecondDensityAtom_pnat_reassembly x).norm
    (summable_thetaCuspTailSecondDensityAtom_pnat_reassembly y).norm

/-- The family of complete primitive-direction densities is absolutely summable pointwise. -/
theorem summable_thetaCuspPrimitiveDirectionDensityPair (p : ℝ × ℝ) :
    Summable (fun q : ThetaCuspPrimitiveDirection =>
      thetaCuspPrimitiveDirectionDensityPair q p) := by
  let f : ℕ+ × ℕ+ → ℝ := fun q =>
    thetaCuspTailSecondDensityAtom q.1 p.1 *
      thetaCuspTailSecondDensityAtom q.2 p.2
  have hpair : Summable f := by
    simpa only [f] using
      summable_thetaCuspTailSecondDensityAtom_pair_pnat_reassembly p.1 p.2
  have hray : Summable (fun q : ThetaCuspPrimitiveRayIndex =>
      f (thetaCuspPrimitiveRayIndexToPositivePair q)) :=
    (thetaCuspPrimitiveRayIndexEquivPositivePair.summable_iff).mpr hpair
  have hdir := hray.prod
  simpa only [thetaCuspPrimitiveDirectionDensityPair, f,
    thetaCuspPrimitiveRayIndexToPositivePair] using hdir

/-- Pointwise, the full canonical density product is the absolutely convergent sum of its
complete coprime-direction densities. -/
theorem thetaCuspTailSecondDensity_mul_eq_tsum_primitiveDirection
    (p : ℝ × ℝ) :
    thetaCuspTailSecondDensity p.1 * thetaCuspTailSecondDensity p.2 =
      ∑' q : ThetaCuspPrimitiveDirection,
        thetaCuspPrimitiveDirectionDensityPair q p := by
  let f : ℕ+ × ℕ+ → ℝ := fun q =>
    thetaCuspTailSecondDensityAtom q.1 p.1 *
      thetaCuspTailSecondDensityAtom q.2 p.2
  have hpair : Summable f := by
    simpa only [f] using
      summable_thetaCuspTailSecondDensityAtom_pair_pnat_reassembly p.1 p.2
  have hray : Summable (fun q : ThetaCuspPrimitiveRayIndex =>
      f (thetaCuspPrimitiveRayIndexToPositivePair q)) :=
    (thetaCuspPrimitiveRayIndexEquivPositivePair.summable_iff).mpr hpair
  calc
    thetaCuspTailSecondDensity p.1 * thetaCuspTailSecondDensity p.2 =
        ∑' q : ThetaCuspPrimitiveRayIndex,
          thetaCuspTailSecondDensityAtom
              (thetaCuspPrimitiveRayIndexToPositivePair q).1 p.1 *
            thetaCuspTailSecondDensityAtom
              (thetaCuspPrimitiveRayIndexToPositivePair q).2 p.2 :=
      thetaCuspTailSecondDensity_mul_eq_tsum_primitiveRay p.1 p.2
    _ = ∑' q : ThetaCuspPrimitiveDirection, ∑' g : ℕ+,
          thetaCuspTailSecondDensityAtom (q.1.1 * g) p.1 *
            thetaCuspTailSecondDensityAtom (q.1.2 * g) p.2 := by
      simpa only [f, thetaCuspPrimitiveRayIndexToPositivePair] using hray.tsum_prod
    _ = _ := rfl

/-- The positive-natural and ordinary-natural presentations of one common-scale ray agree. -/
theorem thetaCuspPrimitiveDirectionDensityPair_eq_rayDensityPair
    (q : ThetaCuspPrimitiveDirection) (p : ℝ × ℝ) :
    thetaCuspPrimitiveDirectionDensityPair q p =
      thetaCuspPrimitiveRayDensityPair (q.1.1 : ℕ) (q.1.2 : ℕ) p := by
  unfold thetaCuspPrimitiveDirectionDensityPair thetaCuspPrimitiveRayDensityPair
  let f : ℕ → ℝ := fun g =>
    thetaCuspTailSecondDensityAtom ((q.1.1 : ℕ) * (g + 1)) p.1 *
      thetaCuspTailSecondDensityAtom ((q.1.2 : ℕ) * (g + 1)) p.2
  have h := Equiv.pnatEquivNat.tsum_eq f
  simpa only [f, Function.comp_apply, Equiv.pnatEquivNat_apply,
    PNat.natPred_add_one] using h

/-- The current kernel carried by one complete coprime direction. -/
def thetaCuspPrimitiveDirectionCoreIntegrand
    (q : ThetaCuspPrimitiveDirection) (d : ℕ) (z : ℂ) (p : ℝ × ℝ) : ℝ :=
  thetaCuspPrimitiveDirectionDensityPair q p *
    xiCTaylorThetaTailCorePairCurrent d z p

theorem measurable_thetaCuspPrimitiveDirectionDensityPair
    (q : ThetaCuspPrimitiveDirection) :
    Measurable (thetaCuspPrimitiveDirectionDensityPair q) := by
  rw [show thetaCuspPrimitiveDirectionDensityPair q =
      thetaCuspPrimitiveRayDensityPair (q.1.1 : ℕ) (q.1.2 : ℕ) by
    funext p
    exact thetaCuspPrimitiveDirectionDensityPair_eq_rayDensityPair q p]
  exact measurable_thetaCuspPrimitiveRayDensityPair _ _

/-- The full symmetric core correlation integral is the sum of its complete coprime-direction
integrals.  Absolute convergence is inherited from the full canonical density, not assumed per
direction. -/
theorem integral_xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_tsum_primitiveDirection
    (d : ℕ) (z : ℂ) :
    (∫ p : ℝ × ℝ,
        xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p
          ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      ∑' q : ThetaCuspPrimitiveDirection,
        ∫ p : ℝ × ℝ,
          thetaCuspPrimitiveDirectionCoreIntegrand q d z p
            ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  let mu : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))
  let F : ThetaCuspPrimitiveDirection → (ℝ × ℝ) → ℝ := fun q p =>
    thetaCuspPrimitiveDirectionCoreIntegrand q d z p
  have hFmeas : ∀ q, AEStronglyMeasurable (F q) mu := by
    intro q
    exact (((measurable_thetaCuspPrimitiveDirectionDensityPair q).mul
      (continuous_xiCTaylorThetaTailCorePairCurrent d z).measurable).aestronglyMeasurable)
  have hfull : Integrable
      (xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z) mu :=
    integrable_xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z
  have hmem : ∀ᵐ p ∂mu, p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    dsimp [mu]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have hnormsum : ∀ᵐ p ∂mu,
      (∑' q : ThetaCuspPrimitiveDirection, ‖F q p‖₊) =
        ‖xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p‖₊ := by
    filter_upwards [hmem] with p hp
    let A : ThetaCuspPrimitiveDirection → ℝ := fun q =>
      thetaCuspPrimitiveDirectionDensityPair q p
    let K : ℝ := xiCTaylorThetaTailCorePairCurrent d z p
    have hA0 (q : ThetaCuspPrimitiveDirection) : 0 ≤ A q := by
      dsimp only [A]
      rw [thetaCuspPrimitiveDirectionDensityPair_eq_rayDensityPair]
      exact thetaCuspPrimitiveRayDensityPair_nonneg q.1.1.pos q.1.2.pos hp
    have hAsum : Summable A := by
      simpa only [A] using summable_thetaCuspPrimitiveDirectionDensityPair p
    have hAnn : Summable (fun q => (A q).toNNReal) := by
      apply NNReal.summable_coe.mp
      simpa only [Real.coe_toNNReal _ (hA0 _)] using hAsum
    have hFnorm (q : ThetaCuspPrimitiveDirection) :
        ‖F q p‖₊ = (A q).toNNReal * ‖K‖₊ := by
      apply NNReal.eq
      change |A q * K| = ↑((A q).toNNReal * ‖K‖₊)
      rw [abs_mul, abs_of_nonneg (hA0 q)]
      simp only [NNReal.coe_mul, Real.coe_toNNReal _ (hA0 q), coe_nnnorm,
        Real.norm_eq_abs]
    have hAtsum : (∑' q, A q) =
        thetaCuspTailSecondDensity p.1 * thetaCuspTailSecondDensity p.2 := by
      exact (thetaCuspTailSecondDensity_mul_eq_tsum_primitiveDirection p).symm
    have hfull0 :
        0 ≤ thetaCuspTailSecondDensity p.1 * thetaCuspTailSecondDensity p.2 :=
      mul_nonneg (thetaCuspTailSecondDensity_pos hp.1).le
        (thetaCuspTailSecondDensity_pos hp.2).le
    have hAnnTsum : (∑' q, (A q).toNNReal) =
        (thetaCuspTailSecondDensity p.1 *
          thetaCuspTailSecondDensity p.2).toNNReal := by
      apply NNReal.eq
      rw [NNReal.coe_tsum]
      · simp only [Real.coe_toNNReal _ (hA0 _), Real.coe_toNNReal _ hfull0]
        exact hAtsum
    calc
      (∑' q, ‖F q p‖₊) =
          ∑' q, (A q).toNNReal * ‖K‖₊ := by
            apply tsum_congr
            exact hFnorm
      _ = (∑' q, (A q).toNNReal) * ‖K‖₊ :=
        hAnn.tsum_mul_right ‖K‖₊
      _ = (thetaCuspTailSecondDensity p.1 *
          thetaCuspTailSecondDensity p.2).toNNReal * ‖K‖₊ := by
        rw [hAnnTsum]
      _ = ‖xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p‖₊ := by
        apply NNReal.eq
        rw [xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_density_mul]
        simp only [NNReal.coe_mul, Real.coe_toNNReal _ hfull0, coe_nnnorm,
          Real.norm_eq_abs, abs_mul, abs_of_nonneg hfull0]
        rfl
  have hnormsumE : ∀ᵐ p ∂mu,
      (∑' q : ThetaCuspPrimitiveDirection, ‖F q p‖ₑ) =
        ‖xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p‖ₑ := by
    filter_upwards [hnormsum, hmem] with p hpNorm hp
    let A : ThetaCuspPrimitiveDirection → ℝ := fun q =>
      thetaCuspPrimitiveDirectionDensityPair q p
    let K : ℝ := xiCTaylorThetaTailCorePairCurrent d z p
    have hA0 (q : ThetaCuspPrimitiveDirection) : 0 ≤ A q := by
      dsimp only [A]
      rw [thetaCuspPrimitiveDirectionDensityPair_eq_rayDensityPair]
      exact thetaCuspPrimitiveRayDensityPair_nonneg q.1.1.pos q.1.2.pos hp
    have hAsum : Summable A := by
      simpa only [A] using summable_thetaCuspPrimitiveDirectionDensityPair p
    have hAnn : Summable (fun q => (A q).toNNReal) := by
      apply NNReal.summable_coe.mp
      simpa only [Real.coe_toNNReal _ (hA0 _)] using hAsum
    have hFnorm (q : ThetaCuspPrimitiveDirection) :
        ‖F q p‖₊ = (A q).toNNReal * ‖K‖₊ := by
      apply NNReal.eq
      change |A q * K| = ↑((A q).toNNReal * ‖K‖₊)
      rw [abs_mul, abs_of_nonneg (hA0 q)]
      simp only [NNReal.coe_mul, Real.coe_toNNReal _ (hA0 q), coe_nnnorm,
        Real.norm_eq_abs]
    have hnorm : Summable (fun q => ‖F q p‖₊) := by
      exact (hAnn.mul_right ‖K‖₊).congr (fun q => hFnorm q |>.symm)
    calc
      (∑' q, ‖F q p‖ₑ) =
          ((∑' q, ‖F q p‖₊ : NNReal) : ENNReal) := by
            exact (ENNReal.coe_tsum hnorm).symm
      _ = (‖xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p‖₊ : ENNReal) := by
        rw [hpNorm]
      _ = ‖xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p‖ₑ := rfl
  have hfinite :
      (∑' q : ThetaCuspPrimitiveDirection, ∫⁻ p, ‖F q p‖ₑ ∂mu) ≠ ⊤ := by
    rw [← lintegral_tsum (fun q => (hFmeas q).enorm)]
    rw [lintegral_congr_ae hnormsumE]
    exact ne_of_lt hfull.hasFiniteIntegral
  have hswap := integral_tsum hFmeas hfinite
  change (∫ p : ℝ × ℝ,
      xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p ∂mu) = _
  rw [show xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z =
      fun p => ∑' q, F q p by
    funext p
    rw [xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_density_mul]
    unfold F thetaCuspPrimitiveDirectionCoreIntegrand
    rw [thetaCuspTailSecondDensity_mul_eq_tsum_primitiveDirection]
    exact (summable_thetaCuspPrimitiveDirectionDensityPair p).tsum_mul_right
      (xiCTaylorThetaTailCorePairCurrent d z p) |>.symm]
  exact hswap

/-- Exact full-current reassembly by complete coprime directions. -/
theorem xiCTaylorThetaTailCore_current_eq_tsum_primitiveDirectionIntegral
    (d : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        ∑' q : ThetaCuspPrimitiveDirection,
          ∫ p : ℝ × ℝ,
            thetaCuspPrimitiveDirectionCoreIntegrand q d z p
              ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  rw [xiCTaylorThetaTailCore_current_eq_symmetricCorrelationIntegral,
    integral_xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_tsum_primitiveDirection]

/-- Each complete direction integral is exactly its shell-born joint reflected radial packet. -/
theorem integral_thetaCuspPrimitiveDirectionCoreIntegrand_eq_globalJoint
    (q : ThetaCuspPrimitiveDirection) (d : ℕ) (z : ℂ) :
    (∫ p : ℝ × ℝ,
        thetaCuspPrimitiveDirectionCoreIntegrand q d z p
          ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      ∫ r : ℝ in Ici
          (thetaCuspPrimitiveRayRadialLog (q.1.1 : ℕ) (q.1.2 : ℕ) 0 0),
        (8 * Real.exp
          (-(Real.log (q.1.1 : ℝ) + Real.log (q.1.2 : ℝ)) / 2)) *
        thetaCuspPrimitiveRayJointSeamIntegrand d z r
          (-Real.log (q.1.1 : ℝ)) (-Real.log (q.1.2 : ℝ)) := by
  have hmeasure :
      volume.restrict thetaCuspPositiveQuadrantSet =
        (volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)) := by
    dsimp only [thetaCuspPositiveQuadrantSet]
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  rw [← hmeasure]
  simpa only [thetaCuspPrimitiveDirectionCoreIntegrand,
    thetaCuspPrimitiveDirectionDensityPair_eq_rayDensityPair] using
    integral_thetaCuspPrimitiveRayDensityPair_mul_coreCurrent_eq_globalJoint_unconditional
      q.1.1.pos q.1.2.pos d z

/-- **Exact global primitive-ray seam identity.**  The full finite theta-tail core current is the
sum over coprime directions of the joint reflected radial packet, with shell birth, parity,
favorable exponential square, swept endpoints, and finite angular derivative all retained. -/
theorem xiCTaylorThetaTailCore_current_eq_tsum_primitiveDirectionGlobalJoint
    (d : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        ∑' q : ThetaCuspPrimitiveDirection,
          ∫ r : ℝ in Ici
              (thetaCuspPrimitiveRayRadialLog (q.1.1 : ℕ) (q.1.2 : ℕ) 0 0),
            (8 * Real.exp
              (-(Real.log (q.1.1 : ℝ) + Real.log (q.1.2 : ℝ)) / 2)) *
            thetaCuspPrimitiveRayJointSeamIntegrand d z r
              (-Real.log (q.1.1 : ℝ)) (-Real.log (q.1.2 : ℝ)) := by
  rw [xiCTaylorThetaTailCore_current_eq_tsum_primitiveDirectionIntegral]
  congr 1
  apply tsum_congr
  intro q
  exact integral_thetaCuspPrimitiveDirectionCoreIntegrand_eq_globalJoint q d z

end


end RHTower
