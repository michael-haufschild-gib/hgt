import GaloisForLFunctions.RHTower.SuzukiTaV2LivsicUpperHalfPlaneCofinalLimit
import GaloisForLFunctions.RHTower.SuzukiTaV2ProjectiveCharacteristic

open Complex Metric Set Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

private theorem tendstoLocallyUniformlyOn_const (c : ℂ) {s : Set ℂ} :
    TendstoLocallyUniformlyOn (fun _k : ℕ => fun _z : ℂ => c)
      (fun _z : ℂ => c) atTop s := by
  intro u hu x _hx
  exact ⟨Set.univ, univ_mem,
    Eventually.of_forall fun _k _y _hy => refl_mem_uniformity hu⟩

/-- One cofinal subsequence simultaneously retains the literal Suzuki Livsic source and its v2
projective chart.  Thus projectivization creates no additional compactness or coefficient loss. -/
theorem exists_suzukiTaV2CanonicalCompatibleCofinalLimits_on_upperHalfPlane :
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
      theta I = 0 := by
  obtain ⟨phi, theta, hphi, hcofinal, hconv, htheta, hbound, hanchor, _hjets⟩ :=
    exists_suzukiTaV2CanonicalCofinalLivsicLimit_on_upperHalfPlane
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  have hone : TendstoLocallyUniformlyOn
      (fun _k : ℕ => fun _z : ℂ => (1 : ℂ)) (fun _z : ℂ => 1) atTop U :=
    tendstoLocallyUniformlyOn_const 1
  have hconst : TendstoLocallyUniformlyOn
      (fun _k : ℕ => fun _z : ℂ => (((1 + xiHedenmalmDonoghueScale : ℝ) : ℂ)))
      (fun _z : ℂ => (((1 + xiHedenmalmDonoghueScale : ℝ) : ℂ))) atTop U :=
    tendstoLocallyUniformlyOn_const _
  have hcoef : TendstoLocallyUniformlyOn
      (fun _k : ℕ => fun _z : ℂ => (((xiHedenmalmDonoghueScale - 1 : ℝ) : ℂ)))
      (fun _z : ℂ => (((xiHedenmalmDonoghueScale - 1 : ℝ) : ℂ))) atTop U :=
    tendstoLocallyUniformlyOn_const _
  have hnum := hone.sub hconv
  have hmul := hcoef.mul₀ hconv continuousOn_const htheta.continuousOn
  have hden := hconst.add hmul
  have hnumCont : ContinuousOn (fun z : ℂ => 1 - theta z) U :=
    continuousOn_const.sub htheta.continuousOn
  have hdenCont : ContinuousOn
      (fun z : ℂ => (((1 + xiHedenmalmDonoghueScale : ℝ) : ℂ)) +
        (((xiHedenmalmDonoghueScale - 1 : ℝ) : ℂ) * theta z)) U :=
    continuousOn_const.add (continuousOn_const.mul htheta.continuousOn)
  have hden0 : ∀ z ∈ U,
      (((1 + xiHedenmalmDonoghueScale : ℝ) : ℂ)) +
        (((xiHedenmalmDonoghueScale - 1 : ℝ) : ℂ) * theta z) ≠ 0 := by
    intro z hz
    exact suzukiV2MobiusDenominator_ne_zero
      xiHedenmalmDonoghueScale xiHedenmalmDonoghueScale_pos
      (theta z) (hbound z hz)
  have hmob : TendstoLocallyUniformlyOn
      (fun k z => suzukiV2MobiusTransform xiHedenmalmDonoghueScale
        (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)) z))
      (fun z => suzukiV2MobiusTransform xiHedenmalmDonoghueScale (theta z))
      atTop U := by
    have hquot := hnum.div₀ hden hnumCont hdenCont hden0
    have hseq := hquot.congr
      (G := fun k z => suzukiV2MobiusTransform xiHedenmalmDonoghueScale
        (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)) z))
      fun k z _hz => by
      simp [suzukiV2MobiusTransform]
    exact hseq.congr_right fun z _hz => by
      simp [suzukiV2MobiusTransform]
  have hprojective := hmob.congr fun k z hz =>
    (suzukiTaV2ProjectiveCharacteristic_eq_mobius
      (suzukiTaV2CanonicalAperture (phi k)) hz).symm
  exact ⟨phi, theta, hphi, hcofinal, hconv, hprojective,
    htheta, hbound, hanchor⟩

/-- Every sequence of literal Suzuki-v2 projective characteristics has one subsequence converging
locally uniformly on the entire pole-free upper-half-plane chart. -/
theorem exists_suzukiTaV2ProjectiveCharacteristic_montel_subseq_on_upperHalfPlane
    (a : ℕ → SuzukiPositiveAperture) :
    ∃ (phi : ℕ → ℕ) (g : ℂ → ℂ), StrictMono phi ∧
      TendstoLocallyUniformlyOn
        (fun k => suzukiTaV2ProjectiveCharacteristic (a (phi k))) g atTop
        {z : ℂ | 0 < z.im} ∧
      DifferentiableOn ℂ g {z : ℂ | 0 < z.im} ∧
      ∀ z : ℂ, 0 < z.im →
        ‖g z‖ ≤ 1 / min 1 xiHedenmalmDonoghueScale := by
  exact exists_subseq_tendstoLocallyUniformlyOn_upperHalfPlane
    (fun n => differentiableOn_suzukiTaV2ProjectiveCharacteristic_upperHalfPlane (a n))
    (fun n z hz => norm_suzukiTaV2ProjectiveCharacteristic_le (a n) hz)

/-- Canonical apertures have a cofinal subsequence whose literal Suzuki-v2 characteristics converge
locally uniformly on the whole pole-free upper half-plane.  The limit remains holomorphic and
inherits the aperture-uniform projective bound. -/
theorem exists_suzukiTaV2CanonicalCofinalProjectiveLimit_on_upperHalfPlane :
    ∃ (phi : ℕ → ℕ) (g : ℂ → ℂ), StrictMono phi ∧
      Tendsto (fun k => (suzukiTaV2CanonicalAperture (phi k)).1) atTop atTop ∧
      TendstoLocallyUniformlyOn
        (fun k => suzukiTaV2ProjectiveCharacteristic
          (suzukiTaV2CanonicalAperture (phi k))) g atTop
        {z : ℂ | 0 < z.im} ∧
      DifferentiableOn ℂ g {z : ℂ | 0 < z.im} ∧
      ∀ z : ℂ, 0 < z.im →
        ‖g z‖ ≤ 1 / min 1 xiHedenmalmDonoghueScale := by
  obtain ⟨phi, g, hphi, hconv, hg, hbd⟩ :=
    exists_suzukiTaV2ProjectiveCharacteristic_montel_subseq_on_upperHalfPlane
      suzukiTaV2CanonicalAperture
  exact ⟨phi, g, hphi,
    tendsto_suzukiTaV2CanonicalAperture_atTop.comp hphi.tendsto_atTop,
    hconv, hg, hbd⟩

end RHTower

end
