import GaloisForLFunctions.RHTower.SuzukiTaCovarianceReflection
import GaloisForLFunctions.RHTower.SuzukiTaV2UpperHalfPlaneCofinalLimit

/-!
# Pole-free lower-chart convergence for Suzuki's actual v2 characteristic

The literal Suzuki v2 characteristic is meromorphic.  Therefore compact-open convergence on all
of `ℂ` is not a lawful target.  This module derives its reflected lower-half-plane projective
chart directly from the same finite-aperture Livšic carrier that controls the upper chart:

`Fₐ(-z) = (θₐ(z) - 1) / ((1 + c) θₐ(z) + c - 1)`.

Consequently one canonical cofinal subsequence converges in both actual charts: globally on the
upper half-plane, and locally uniformly on each lower pole-free domain.  The lower pole divisor
is retained explicitly; neither an inverse chart nor a compact-open continuation through that
divisor is substituted for the literal characteristic.  This establishes the correct meromorphic
convergence topology, but does not identify the limiting carrier with the Xi target.
-/

open Complex Metric Set Filter Topology

noncomputable section

namespace RHTower

/-- The literal projective transform of the reflected lower half-plane in the upper Livšic
coordinate. -/
noncomputable def suzukiV2ReflectedLowerMobiusTransform (c : ℝ) (w : ℂ) : ℂ :=
  (w - 1) / ((((1 + c : ℝ) : ℂ) * w) + ((c - 1 : ℝ) : ℂ))

/-- Homogeneous representative of the reflected lower Suzuki chart.  Unlike its affine quotient,
this pair remains defined at every limiting lower pole. -/
noncomputable def suzukiV2ReflectedLowerHomogeneousLift (c : ℝ) (w : ℂ) : ℂ × ℂ :=
  (w - 1, (((1 + c : ℝ) : ℂ) * w) + ((c - 1 : ℝ) : ℂ))

/-- The lower-chart homogeneous lift has no base point whenever its scale is positive. -/
theorem suzukiV2ReflectedLowerHomogeneousLift_ne_zero
    {c : ℝ} (hc : 0 < c) (w : ℂ) :
    suzukiV2ReflectedLowerHomogeneousLift c w ≠ 0 := by
  intro hzero
  have hnum : w - 1 = 0 := by
    simpa [suzukiV2ReflectedLowerHomogeneousLift] using congrArg Prod.fst hzero
  have hw : w = 1 := sub_eq_zero.mp hnum
  have hden : (((1 + c : ℝ) : ℂ) * w) + ((c - 1 : ℝ) : ℂ) = 0 := by
    simpa [suzukiV2ReflectedLowerHomogeneousLift] using congrArg Prod.snd hzero
  rw [hw] at hden
  have htwoc : ((2 * c : ℝ) : ℂ) = 0 := by
    calc
      ((2 * c : ℝ) : ℂ) = (((1 + c : ℝ) : ℂ) * (1 : ℂ)) +
          ((c - 1 : ℝ) : ℂ) := by push_cast; ring
      _ = 0 := hden
  have htwocReal : 2 * c = 0 := by exact_mod_cast htwoc
  nlinarith

/-- Exact determinant of the reflected lower homogeneous Möbius lift. -/
theorem suzukiV2ReflectedLowerHomogeneousLift_det (c : ℝ) (w v : ℂ) :
    (suzukiV2ReflectedLowerHomogeneousLift c w).1 *
        (suzukiV2ReflectedLowerHomogeneousLift c v).2 -
      (suzukiV2ReflectedLowerHomogeneousLift c w).2 *
        (suzukiV2ReflectedLowerHomogeneousLift c v).1 =
      (2 * (c : ℂ)) * (w - v) := by
  simp only [suzukiV2ReflectedLowerHomogeneousLift]
  push_cast
  ring

private lemma reflected_lower_mobius_algebra (A E c : ℂ) (hE : E ≠ 0) :
    -((-E) - (-A)) / (c * ((-E) + (-A)) - ((-E) - (-A))) =
      (A / E - 1) / ((1 + c) * (A / E) + (c - 1)) := by
  have hden : c * ((-E) + (-A)) - ((-E) - (-A)) =
      -(((1 + c) * A) + ((c - 1) * E)) := by
    ring
  rw [hden, div_neg]
  field_simp [hE]
  ring

/-- Exact lower-chart formula for the literal self-adjoint-angle Suzuki v2 characteristic. -/
theorem suzukiTaV2ProjectiveCharacteristic_neg_eq_reflectedLowerMobius
    (a : SuzukiPositiveAperture) {z : ℂ} (hz : 0 < z.im) :
    suzukiTaV2ProjectiveCharacteristic a (-z) =
      suzukiV2ReflectedLowerMobiusTransform xiHedenmalmDonoghueScale
        (suzukiTaV2Livsic a z) := by
  have hE : suzukiTaV2CharacteristicE a z ≠ 0 :=
    GaloisForLFunctions.RHTower.suzukiLivsic_denominator_ne_zero
      (differentiable_suzukiTaV2CharacteristicA a).continuous
      (differentiable_suzukiTaV2CharacteristicE a).continuous
      (suzukiTaV2CharacteristicA_I a) (suzukiTaV2_allAngleRealZeros a) hz
  have hpar := suzukiTaV2_parityPair a z
  obtain ⟨hA, hEpar⟩ := hpar
  rw [suzukiTaV2ProjectiveCharacteristic,
    suzukiTaCharacteristic_zeroAngle, suzukiTaCharacteristic_piAngle,
    hA, hEpar, suzukiV2ReflectedLowerMobiusTransform,
    suzukiTaV2Livsic, GaloisForLFunctions.RHTower.suzukiLivsicQuotient]
  push_cast
  apply reflected_lower_mobius_algebra
  exact hE

/-- The reflected lower limit chart is meromorphic on its entire upper-coordinate domain.  Its
explicit denominator is retained as the limiting lower-pole divisor. -/
theorem meromorphicOn_suzukiV2ReflectedLowerMobiusTransform
    {theta : ℂ → ℂ}
    (htheta : DifferentiableOn ℂ theta {z : ℂ | 0 < z.im}) :
    MeromorphicOn
      (fun z => suzukiV2ReflectedLowerMobiusTransform
        xiHedenmalmDonoghueScale (theta z)) {z : ℂ | 0 < z.im} := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have htheta' : AnalyticOnNhd ℂ theta U := htheta.analyticOnNhd hUopen
  have hnum : AnalyticOnNhd ℂ (fun z : ℂ => theta z - 1) U :=
    htheta'.sub analyticOnNhd_const
  have hden : AnalyticOnNhd ℂ
      (fun z : ℂ => (((1 + xiHedenmalmDonoghueScale : ℝ) : ℂ) * theta z) +
        ((xiHedenmalmDonoghueScale - 1 : ℝ) : ℂ)) U :=
    (analyticOnNhd_const.mul htheta').add analyticOnNhd_const
  change MeromorphicOn
    ((fun z : ℂ => theta z - 1) /
      (fun z : ℂ => (((1 + xiHedenmalmDonoghueScale : ℝ) : ℂ) * theta z) +
        ((xiHedenmalmDonoghueScale - 1 : ℝ) : ℂ))) U
  exact hnum.meromorphicOn.div hden.meromorphicOn

private theorem tendstoLocallyUniformlyOn_const (c : ℂ) {s : Set ℂ} :
    TendstoLocallyUniformlyOn (fun _k : ℕ => fun _z : ℂ => c)
      (fun _z : ℂ => c) atTop s := by
  intro u hu x _hx
  exact ⟨Set.univ, univ_mem,
    Eventually.of_forall fun _k _y _hy => refl_mem_uniformity hu⟩

/-- The literal reflected lower characteristic has a global homogeneous cofinal limit.  This is
the pole-inclusive projective convergence statement: at a zero of the affine denominator, the
nonzero pair is retained rather than claiming compact-open quotient convergence through a pole. -/
theorem suzukiTaV2ReflectedLowerHomogeneousLift_tendstoLocallyUniformlyOn
    {phi : ℕ → ℕ} {theta : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn
      (fun k => suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)))
      theta atTop {z : ℂ | 0 < z.im})
    (htheta : DifferentiableOn ℂ theta {z : ℂ | 0 < z.im}) :
    TendstoLocallyUniformlyOn
      (fun k z => suzukiV2ReflectedLowerHomogeneousLift xiHedenmalmDonoghueScale
        (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)) z))
      (fun z => suzukiV2ReflectedLowerHomogeneousLift xiHedenmalmDonoghueScale
        (theta z)) atTop {z : ℂ | 0 < z.im} := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  have hone := tendstoLocallyUniformlyOn_const (1 : ℂ) (s := U)
  have hcoefOne := tendstoLocallyUniformlyOn_const
    (((1 + xiHedenmalmDonoghueScale : ℝ) : ℂ)) (s := U)
  have hcoefShift := tendstoLocallyUniformlyOn_const
    (((xiHedenmalmDonoghueScale - 1 : ℝ) : ℂ)) (s := U)
  have hnum := hconv.sub hone
  have hden := (hcoefOne.mul₀ hconv continuousOn_const htheta.continuousOn).add hcoefShift
  have hlift := hnum.prodMk hden
  exact hlift.congr
    (G := fun k z => suzukiV2ReflectedLowerHomogeneousLift xiHedenmalmDonoghueScale
      (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)) z))
    fun _k _z _hz => by simp [suzukiV2ReflectedLowerHomogeneousLift]

/-- On every limiting lower pole-free domain, the literal reflected Suzuki characteristics
converge along the source's own canonical cofinal subsequence. -/
theorem suzukiTaV2ProjectiveCharacteristic_neg_tendstoLocallyUniformlyOn_of_poleFree
    {phi : ℕ → ℕ} {theta : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn
      (fun k => suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)))
      theta atTop {z : ℂ | 0 < z.im})
    (htheta : DifferentiableOn ℂ theta {z : ℂ | 0 < z.im})
    {V : Set ℂ} (hVU : V ⊆ {z : ℂ | 0 < z.im})
    (hpoleFree : ∀ z ∈ V,
      (((1 + xiHedenmalmDonoghueScale : ℝ) : ℂ) * theta z +
        ((xiHedenmalmDonoghueScale - 1 : ℝ) : ℂ)) ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun k z => suzukiTaV2ProjectiveCharacteristic
        (suzukiTaV2CanonicalAperture (phi k)) (-z))
      (fun z => suzukiV2ReflectedLowerMobiusTransform
        xiHedenmalmDonoghueScale (theta z)) atTop V := by
  have hconvV := hconv.mono hVU
  have hthetaV : ContinuousOn theta V := htheta.continuousOn.mono hVU
  have hone := tendstoLocallyUniformlyOn_const (1 : ℂ) (s := V)
  have hcoefOne := tendstoLocallyUniformlyOn_const
    (((1 + xiHedenmalmDonoghueScale : ℝ) : ℂ)) (s := V)
  have hcoefShift := tendstoLocallyUniformlyOn_const
    (((xiHedenmalmDonoghueScale - 1 : ℝ) : ℂ)) (s := V)
  have hnum := hconvV.sub hone
  have hden := (hcoefOne.mul₀ hconvV continuousOn_const hthetaV).add hcoefShift
  have hnumCont : ContinuousOn (fun z : ℂ => theta z - 1) V :=
    hthetaV.sub continuousOn_const
  have hdenCont : ContinuousOn
      (fun z : ℂ => (((1 + xiHedenmalmDonoghueScale : ℝ) : ℂ) * theta z) +
        ((xiHedenmalmDonoghueScale - 1 : ℝ) : ℂ)) V :=
    (continuousOn_const.mul hthetaV).add continuousOn_const
  have hquot := hnum.div₀ hden hnumCont hdenCont hpoleFree
  have hmob : TendstoLocallyUniformlyOn
      (fun k z => suzukiV2ReflectedLowerMobiusTransform xiHedenmalmDonoghueScale
        (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)) z))
      (fun z => suzukiV2ReflectedLowerMobiusTransform
        xiHedenmalmDonoghueScale (theta z)) atTop V := by
    have hseq := hquot.congr
      (G := fun k z => suzukiV2ReflectedLowerMobiusTransform xiHedenmalmDonoghueScale
        (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)) z))
      fun k z hz => by
        simp [suzukiV2ReflectedLowerMobiusTransform]
    refine hseq.congr_right fun z _hz => ?_
    simp [suzukiV2ReflectedLowerMobiusTransform]
  exact hmob.congr fun k z hz =>
    (suzukiTaV2ProjectiveCharacteristic_neg_eq_reflectedLowerMobius
      (suzukiTaV2CanonicalAperture (phi k)) (hVU hz)).symm

/-- One cofinal Livšic limit governs both literal projective charts: the upper chart globally and
the reflected lower chart on every domain avoiding its explicit limiting pole divisor. -/
theorem exists_suzukiTaV2CanonicalTwoChartCofinalLimits_on_poleFreeDomains :
    ∃ (phi : ℕ → ℕ) (theta : ℂ → ℂ), StrictMono phi ∧
      Tendsto (fun k => (suzukiTaV2CanonicalAperture (phi k)).1) atTop atTop ∧
      TendstoLocallyUniformlyOn
        (fun k => suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)))
        theta atTop {z : ℂ | 0 < z.im} ∧
      TendstoLocallyUniformlyOn
        (fun k => suzukiTaV2ProjectiveCharacteristic
          (suzukiTaV2CanonicalAperture (phi k)))
        (fun z => suzukiV2MobiusTransform xiHedenmalmDonoghueScale (theta z))
        atTop {z : ℂ | 0 < z.im} ∧
      DifferentiableOn ℂ theta {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → ‖theta z‖ ≤ 1) ∧
      theta I = 0 ∧
      ∀ (V : Set ℂ), V ⊆ {z : ℂ | 0 < z.im} →
        (∀ z ∈ V,
          (((1 + xiHedenmalmDonoghueScale : ℝ) : ℂ) * theta z +
            ((xiHedenmalmDonoghueScale - 1 : ℝ) : ℂ)) ≠ 0) →
        TendstoLocallyUniformlyOn
          (fun k z => suzukiTaV2ProjectiveCharacteristic
            (suzukiTaV2CanonicalAperture (phi k)) (-z))
          (fun z => suzukiV2ReflectedLowerMobiusTransform
            xiHedenmalmDonoghueScale (theta z)) atTop V := by
  obtain ⟨phi, theta, hphi, hcofinal, hconv, hupper, htheta, hbound, hanchor⟩ :=
    exists_suzukiTaV2CanonicalCompatibleCofinalLimits_on_upperHalfPlane
  exact ⟨phi, theta, hphi, hcofinal, hconv, hupper, htheta, hbound, hanchor,
    fun V hVU hpoleFree =>
      suzukiTaV2ProjectiveCharacteristic_neg_tendstoLocallyUniformlyOn_of_poleFree
        hconv htheta hVU hpoleFree⟩

/-- The same canonical cofinal carrier yields a pole-inclusive lower projective limit through
its nonvanishing homogeneous lift.  No identification of `theta` with the Xi target is used. -/
theorem exists_suzukiTaV2CanonicalReflectedLowerHomogeneousCofinalLimit :
    ∃ (phi : ℕ → ℕ) (theta : ℂ → ℂ), StrictMono phi ∧
      Tendsto (fun k => (suzukiTaV2CanonicalAperture (phi k)).1) atTop atTop ∧
      TendstoLocallyUniformlyOn
        (fun k => suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)))
        theta atTop {z : ℂ | 0 < z.im} ∧
      DifferentiableOn ℂ theta {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im →
        suzukiV2ReflectedLowerHomogeneousLift xiHedenmalmDonoghueScale (theta z) ≠ 0) ∧
      TendstoLocallyUniformlyOn
        (fun k z => suzukiV2ReflectedLowerHomogeneousLift xiHedenmalmDonoghueScale
          (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)) z))
        (fun z => suzukiV2ReflectedLowerHomogeneousLift xiHedenmalmDonoghueScale
          (theta z)) atTop {z : ℂ | 0 < z.im} := by
  obtain ⟨phi, theta, hphi, hcofinal, hconv, _hupper, htheta, _hbound, _hanchor⟩ :=
    exists_suzukiTaV2CanonicalCompatibleCofinalLimits_on_upperHalfPlane
  exact ⟨phi, theta, hphi, hcofinal, hconv, htheta,
    fun _z _hz => suzukiV2ReflectedLowerHomogeneousLift_ne_zero
      xiHedenmalmDonoghueScale_pos _,
    suzukiTaV2ReflectedLowerHomogeneousLift_tendstoLocallyUniformlyOn hconv htheta⟩

end RHTower

end
