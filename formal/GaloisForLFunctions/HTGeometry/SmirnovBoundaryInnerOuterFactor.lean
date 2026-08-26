import GaloisForLFunctions.HTGeometry.OuterMultiplierUniqueness
import GaloisForLFunctions.HTGeometry.SmirnovToeplitzKernel

/-!
# Inner--outer factorization in the Smirnov boundary algebra

A nonzero Smirnov numerator splits into its bounded inner factor and a quotient of outer bounded
multipliers.  Equal boundary moduli for two such outer quotients imply equality up to one
unimodular constant, by cross multiplication and bounded outer uniqueness.
-/

open Complex MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Circle-boundary representative of a Smirnov quotient. -/
def DiskSmirnovBoundary.circleBoundary (F : DiskSmirnovBoundary) (z : Circle) : ℂ :=
  diskMultiplierBoundaryFun F.numerator z /
    diskMultiplierBoundaryFun F.denominator z

/-- Measurable representative of the circle-boundary Smirnov quotient. -/
def DiskSmirnovBoundary.circleBoundaryMeasurableRep
    (F : DiskSmirnovBoundary) (z : Circle) : ℂ :=
  diskMultiplierBoundaryMeasurableRep F.numerator z /
    diskMultiplierBoundaryMeasurableRep F.denominator z

theorem DiskSmirnovBoundary.measurable_circleBoundaryMeasurableRep
    (F : DiskSmirnovBoundary) :
    Measurable F.circleBoundaryMeasurableRep :=
  (measurable_diskMultiplierBoundaryMeasurableRep F.numerator).div
    (measurable_diskMultiplierBoundaryMeasurableRep F.denominator)

/-- The exact circle-boundary representative of every Smirnov quotient is strongly measurable
almost everywhere. -/
theorem DiskSmirnovBoundary.aestronglyMeasurable_circleBoundary
    (F : DiskSmirnovBoundary) :
    AEStronglyMeasurable F.circleBoundary circleLebesgue := by
  apply F.measurable_circleBoundaryMeasurableRep.aestronglyMeasurable.congr
  filter_upwards [diskMultiplierBoundaryMeasurableRep_ae F.numerator,
    diskMultiplierBoundaryMeasurableRep_ae F.denominator] with z hn hd
  change diskMultiplierBoundaryMeasurableRep F.numerator z /
      diskMultiplierBoundaryMeasurableRep F.denominator z =
    diskMultiplierBoundaryFun F.numerator z /
      diskMultiplierBoundaryFun F.denominator z
  rw [hn, hd]

/-- An a.e. equality of measurable circle functions can be recovered from its real Cayley
pullback.  The omitted Cayley point is null because the weighted real Cayley map pushes forward
exactly to normalized circle measure. -/
theorem circle_eventuallyEq_of_line_eventuallyEq
    {β : Type*} [MeasurableSpace β] [MeasurableEq β]
    {f g : Circle → β} (hf : Measurable f) (hg : Measurable g)
    (h : (fun x => f (circleCayley x)) =ᵐ[volume]
      fun x => g (circleCayley x)) :
    f =ᵐ[circleLebesgue] g := by
  have hweighted : (fun x => f (circleCayley x)) =ᵐ[
      (volume : Measure ℝ).withDensity (realDensity standardCauchyWeight)]
        fun x => g (circleCayley x) :=
    (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
      standardCauchyWeight_pos).mpr h
  rw [← circleCayley_weighted_measurePreserving.map_eq]
  exact (ae_map_iff continuous_circleCayley.measurable.aemeasurable
    (measurableSet_eq_fun hf hg)).2 hweighted

theorem DiskSmirnovBoundary.denominator_circle_ne_zero_ae
    (F : DiskSmirnovBoundary) :
    ∀ᵐ z ∂circleLebesgue, diskMultiplierBoundaryFun F.denominator z ≠ 0 :=
  diskMultiplierBoundary_ne_zero_ae F.denominator
    F.denominator_outer.exists_nonzero

/-- Bounded inner factor of a nonzero Smirnov numerator. -/
def DiskSmirnovBoundary.innerFactor
    (F : DiskSmirnovBoundary)
    (hF : ∃ z ∈ Metric.ball (0 : ℂ) 1, F.numerator.fn z ≠ 0) :
    DiskMultiplier :=
  diskMultiplierInnerFactor F.numerator hF

/-- Outer Smirnov factor: canonical outer numerator divided by the original outer denominator. -/
def DiskSmirnovBoundary.outerPart
    (F : DiskSmirnovBoundary)
    (hF : ∃ z ∈ Metric.ball (0 : ℂ) 1, F.numerator.fn z ≠ 0) :
    DiskSmirnovBoundary where
  numerator := diskMultiplierOuterFactor F.numerator hF
  denominator := F.denominator
  denominator_outer := F.denominator_outer

theorem DiskSmirnovBoundary.outerPart_numerator_outer
    (F : DiskSmirnovBoundary)
    (hF : ∃ z ∈ Metric.ball (0 : ℂ) 1, F.numerator.fn z ≠ 0) :
    IsOuterDiskMultiplier (F.outerPart hF).numerator :=
  isOuterDiskMultiplier_diskMultiplierOuterFactor F.numerator hF

/-- Exact real-line inner--outer factorization of a Smirnov boundary quotient. -/
theorem DiskSmirnovBoundary.boundary_innerFactor_mul_outerPart_ae
    (F : DiskSmirnovBoundary)
    (hF : ∃ z ∈ Metric.ball (0 : ℂ) 1, F.numerator.fn z ≠ 0) :
    F.boundary =ᵐ[volume] fun x =>
      diskMultiplierLineBoundary (F.innerFactor hF) x *
        (F.outerPart hF).boundary x := by
  filter_upwards [diskMultiplierLineBoundary_innerFactor_mul_outerFactor_ae
      F.numerator hF, F.denominator_ne_zero_ae] with x hfac hden
  change diskMultiplierLineBoundary F.numerator x /
      diskMultiplierLineBoundary F.denominator x =
    diskMultiplierLineBoundary (diskMultiplierInnerFactor F.numerator hF) x *
      (diskMultiplierLineBoundary (diskMultiplierOuterFactor F.numerator hF) x /
        diskMultiplierLineBoundary F.denominator x)
  rw [← hfac]
  field_simp

/-- Outer Smirnov quotients with equal a.e. circle-boundary moduli differ on the real boundary by
one unimodular constant. -/
theorem outerSmirnovBoundary_unique_up_to_unimodular
    (F G : DiskSmirnovBoundary)
    (hFn : IsOuterDiskMultiplier F.numerator)
    (hGn : IsOuterDiskMultiplier G.numerator)
    (hmod : ∀ᵐ z ∂circleLebesgue,
      ‖F.circleBoundary z‖ = ‖G.circleBoundary z‖) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ F.boundary =ᵐ[volume]
      fun x => c * G.boundary x := by
  let A := F.numerator.mul G.denominator
  let B := G.numerator.mul F.denominator
  have hAouter : IsOuterDiskMultiplier A := hFn.mul G.denominator_outer
  have hBouter : IsOuterDiskMultiplier B := hGn.mul F.denominator_outer
  have hcrossMod : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundaryFun A z‖ =
        ‖diskMultiplierBoundaryFun B z‖ := by
    filter_upwards [hmod, F.denominator_circle_ne_zero_ae,
      G.denominator_circle_ne_zero_ae,
      diskMultiplierBoundaryFun_mul_ae F.numerator G.denominator,
      diskMultiplierBoundaryFun_mul_ae G.numerator F.denominator]
        with z hz hFd hGd hA hB
    rw [hA, hB, norm_mul, norm_mul]
    rw [DiskSmirnovBoundary.circleBoundary, DiskSmirnovBoundary.circleBoundary,
      norm_div, norm_div] at hz
    exact (div_eq_div_iff (norm_ne_zero_iff.mpr hFd)
      (norm_ne_zero_iff.mpr hGd)).mp hz
  obtain ⟨c, hc, hcross⟩ :=
    outerDiskMultiplier_unique_up_to_unimodular A B hcrossMod hAouter hBouter
  refine ⟨c, hc, ?_⟩
  have hcrossLine : diskMultiplierLineBoundary A =ᵐ[volume]
      fun x => c * diskMultiplierLineBoundary B x := by
    have hcongr : diskMultiplierLineBoundary A =ᵐ[volume]
        diskMultiplierLineBoundary (B.scale c) := by
      apply diskMultiplierLineBoundary_congr_ae
      intro z hz
      rw [DiskMultiplier.scale_fn]
      exact hcross z hz
    exact hcongr.trans (diskMultiplierLineBoundary_scale_ae c B)
  filter_upwards [hcrossLine,
    diskMultiplierLineBoundary_mul_ae F.numerator G.denominator,
    diskMultiplierLineBoundary_mul_ae G.numerator F.denominator,
    F.denominator_ne_zero_ae, G.denominator_ne_zero_ae]
      with x hcrossx hAline hBline hFd hGd
  change diskMultiplierLineBoundary (F.numerator.mul G.denominator) x =
      c * diskMultiplierLineBoundary (G.numerator.mul F.denominator) x at hcrossx
  rw [hAline, hBline] at hcrossx
  rw [DiskSmirnovBoundary.boundary, DiskSmirnovBoundary.boundary]
  field_simp
  linear_combination hcrossx

/-- Real-line form of outer Smirnov uniqueness. -/
theorem outerSmirnovBoundary_unique_up_to_unimodular_of_line
    (F G : DiskSmirnovBoundary)
    (hFn : IsOuterDiskMultiplier F.numerator)
    (hGn : IsOuterDiskMultiplier G.numerator)
    (hmod : ∀ᵐ x ∂volume, ‖F.boundary x‖ = ‖G.boundary x‖) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ F.boundary =ᵐ[volume]
      fun x => c * G.boundary x := by
  have hrepLine :
      (fun x => ‖F.circleBoundaryMeasurableRep (circleCayley x)‖) =ᵐ[volume]
        fun x => ‖G.circleBoundaryMeasurableRep (circleCayley x)‖ := by
    exact hmod
  have hcircleRep : ∀ᵐ z ∂circleLebesgue,
      ‖F.circleBoundaryMeasurableRep z‖ =
        ‖G.circleBoundaryMeasurableRep z‖ := by
    apply circle_eventuallyEq_of_line_eventuallyEq
    · exact F.measurable_circleBoundaryMeasurableRep.norm
    · exact G.measurable_circleBoundaryMeasurableRep.norm
    · exact hrepLine
  have hcircle : ∀ᵐ z ∂circleLebesgue,
      ‖F.circleBoundary z‖ = ‖G.circleBoundary z‖ := by
    filter_upwards [hcircleRep,
      diskMultiplierBoundaryMeasurableRep_ae F.numerator,
      diskMultiplierBoundaryMeasurableRep_ae F.denominator,
      diskMultiplierBoundaryMeasurableRep_ae G.numerator,
      diskMultiplierBoundaryMeasurableRep_ae G.denominator]
        with z hz hFnRep hFdRep hGnRep hGdRep
    change ‖diskMultiplierBoundaryMeasurableRep F.numerator z /
        diskMultiplierBoundaryMeasurableRep F.denominator z‖ =
      ‖diskMultiplierBoundaryMeasurableRep G.numerator z /
        diskMultiplierBoundaryMeasurableRep G.denominator z‖ at hz
    change ‖diskMultiplierBoundaryFun F.numerator z /
        diskMultiplierBoundaryFun F.denominator z‖ =
      ‖diskMultiplierBoundaryFun G.numerator z /
        diskMultiplierBoundaryFun G.denominator z‖
    rw [hFnRep, hFdRep, hGnRep, hGdRep] at hz
    exact hz
  exact outerSmirnovBoundary_unique_up_to_unimodular F G hFn hGn hcircle

/-- The canonical bounded inner factor remains unimodular after real Cayley pullback. -/
theorem ae_norm_diskMultiplierLineBoundary_innerFactor_eq_one
    (phi : DiskMultiplier)
    (hphi : ∃ z ∈ Metric.ball (0 : ℂ) 1, phi.fn z ≠ 0) :
    ∀ᵐ x ∂volume,
      ‖diskMultiplierLineBoundary (diskMultiplierInnerFactor phi hphi) x‖ = 1 := by
  have hcircle : (fun z =>
      ‖diskMultiplierBoundaryFun (diskMultiplierInnerFactor phi hphi) z‖) =ᵐ[
        circleLebesgue] fun _ => 1 :=
    ae_norm_diskMultiplierInnerFactor_boundary_eq_one phi hphi
  have hweighted := hcircle.comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hvolume := (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp hweighted
  filter_upwards [hvolume,
    diskMultiplierLineBoundary_ae (diskMultiplierInnerFactor phi hphi)]
      with x hx hrep
  rw [hrep]
  exact hx

theorem DiskSmirnovBoundary.boundary_ne_zero_ae
    (F : DiskSmirnovBoundary)
    (hF : ∃ z ∈ Metric.ball (0 : ℂ) 1, F.numerator.fn z ≠ 0) :
    ∀ᵐ x ∂volume, F.boundary x ≠ 0 := by
  filter_upwards [diskMultiplierLineBoundary_ne_zero_ae F.numerator hF,
    F.denominator_ne_zero_ae] with x hnum hden
  exact div_ne_zero hnum hden

/-- A Toeplitz kernel's reflected Smirnov numerator is nonzero whenever its symbol is nonzero
almost everywhere. -/
theorem SmirnovToeplitzKernelElement.reflected_nonzero
    {U : ℝ → ℂ} (K : SmirnovToeplitzKernelElement U)
    (hU : ∀ᵐ x ∂volume, U x ≠ 0) :
    ∃ z ∈ Metric.ball (0 : ℂ) 1, K.reflected.numerator.fn z ≠ 0 := by
  have hforward := K.forward.boundary_ne_zero_ae K.forward_nonzero
  have hreflected : ∀ᵐ x ∂volume, K.reflected.boundary x ≠ 0 := by
    filter_upwards [K.boundary_relation, hU, hforward] with x hrel hUx hFx
    rw [hrel]
    exact mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).2 hUx)
      ((map_ne_zero (starRingEnd ℂ)).2 hFx)
  by_contra h
  push Not at h
  have hline : diskMultiplierLineBoundary K.reflected.numerator =ᵐ[volume]
      fun _ => 0 := by
    have hcongr : diskMultiplierLineBoundary K.reflected.numerator =ᵐ[volume]
        diskMultiplierLineBoundary (DiskMultiplier.const 0) := by
      apply diskMultiplierLineBoundary_congr_ae
      intro z hz
      rw [DiskMultiplier.const_fn]
      exact h z hz
    exact hcongr.trans (diskMultiplierLineBoundary_const_ae 0)
  have hzero : ∀ᵐ x ∂volume, K.reflected.boundary x = 0 := by
    filter_upwards [hline] with x hx
    rw [DiskSmirnovBoundary.boundary, hx, zero_div]
  obtain ⟨x, hne, hz⟩ := (hreflected.and hzero).exists
  exact hne hz

/-- Everywhere-unimodular patch of the phase reflection of a Smirnov outer quotient. -/
def DiskSmirnovBoundary.phaseReflectionSymbol
    (F : DiskSmirnovBoundary) (x : ℝ) : ℂ :=
  if F.boundary x = 0 then 1
  else (starRingEnd ℂ) (F.boundary x) / F.boundary x

theorem measurable_diskSmirnovBoundary_phaseReflectionSymbol
    (F : DiskSmirnovBoundary) : Measurable F.phaseReflectionSymbol := by
  apply Measurable.ite
  · exact F.measurable_boundary (measurableSet_singleton 0)
  · exact measurable_const
  · exact (Complex.continuous_conj.measurable.comp F.measurable_boundary).div
      F.measurable_boundary

theorem norm_diskSmirnovBoundary_phaseReflectionSymbol
    (F : DiskSmirnovBoundary) (x : ℝ) :
    ‖F.phaseReflectionSymbol x‖ = 1 := by
  rw [DiskSmirnovBoundary.phaseReflectionSymbol]
  split_ifs with hx
  · simp
  · simp [hx]

/-- Exact canonical boundary factorization supplied by a nonzero Smirnov Toeplitz-kernel element.
The symbol times the two bounded inner factors is, up to one unimodular scalar, the phase
reflection of a quotient of outer bounded multipliers. -/
theorem SmirnovToeplitzKernelElement.exists_innerOuter_boundary_factorization
    {U : ℝ → ℂ} (K : SmirnovToeplitzKernelElement U)
    (hU : ∀ᵐ x ∂volume, ‖U x‖ = 1) :
    ∃ (hR : ∃ z ∈ Metric.ball (0 : ℂ) 1,
        K.reflected.numerator.fn z ≠ 0) (c : ℂ),
      ‖c‖ = 1 ∧
      (fun x => U x *
          diskMultiplierLineBoundary (K.forward.innerFactor K.forward_nonzero) x *
          diskMultiplierLineBoundary (K.reflected.innerFactor hR) x) =ᵐ[volume]
        fun x => (starRingEnd ℂ) c *
          (K.reflected.outerPart hR).phaseReflectionSymbol x := by
  have hUne : ∀ᵐ x ∂volume, U x ≠ 0 := by
    filter_upwards [hU] with x hx
    exact norm_ne_zero_iff.mp (by rw [hx]; norm_num)
  let hR := K.reflected_nonzero hUne
  have hFfactor := K.forward.boundary_innerFactor_mul_outerPart_ae
    K.forward_nonzero
  have hRfactor := K.reflected.boundary_innerFactor_mul_outerPart_ae hR
  have hIfNorm := ae_norm_diskMultiplierLineBoundary_innerFactor_eq_one
    K.forward.numerator K.forward_nonzero
  have hIrNorm := ae_norm_diskMultiplierLineBoundary_innerFactor_eq_one
    K.reflected.numerator hR
  have houterMod : ∀ᵐ x ∂volume,
      ‖(K.forward.outerPart K.forward_nonzero).boundary x‖ =
        ‖(K.reflected.outerPart hR).boundary x‖ := by
    filter_upwards [hFfactor, hRfactor, K.boundary_relation,
      hIfNorm, hIrNorm, hU] with x hF hR' hrel hIf hIr hUx
    change ‖diskMultiplierLineBoundary
      (K.forward.innerFactor K.forward_nonzero) x‖ = 1 at hIf
    change ‖diskMultiplierLineBoundary
      (K.reflected.innerFactor hR) x‖ = 1 at hIr
    calc
      ‖(K.forward.outerPart K.forward_nonzero).boundary x‖ =
          ‖diskMultiplierLineBoundary
              (K.forward.innerFactor K.forward_nonzero) x *
            (K.forward.outerPart K.forward_nonzero).boundary x‖ := by
              rw [norm_mul, hIf, one_mul]
      _ = ‖K.forward.boundary x‖ := by rw [hF]
      _ = ‖K.reflected.boundary x‖ := by
        rw [hrel, norm_mul]
        simp [hUx]
      _ = ‖diskMultiplierLineBoundary (K.reflected.innerFactor hR) x *
            (K.reflected.outerPart hR).boundary x‖ := by rw [hR']
      _ = ‖(K.reflected.outerPart hR).boundary x‖ := by
        rw [norm_mul, hIr, one_mul]
  obtain ⟨c, hc, houter⟩ :=
    outerSmirnovBoundary_unique_up_to_unimodular_of_line
      (K.forward.outerPart K.forward_nonzero)
      (K.reflected.outerPart hR)
      (K.forward.outerPart_numerator_outer K.forward_nonzero)
      (K.reflected.outerPart_numerator_outer hR) houterMod
  refine ⟨hR, c, hc, ?_⟩
  have hHrNe := (K.reflected.outerPart hR).boundary_ne_zero_ae
    (K.reflected.outerPart_numerator_outer hR).exists_nonzero
  filter_upwards [hFfactor, hRfactor, K.boundary_relation, houter,
    hIfNorm, hIrNorm, hU, hHrNe] with x hF hR' hrel houterx
      hIf hIr hUx hHr
  rw [hR', hF, houterx] at hrel
  rw [DiskSmirnovBoundary.phaseReflectionSymbol, if_neg hHr]
  have hUunit : U x * (starRingEnd ℂ) (U x) = 1 := by
    rw [RCLike.mul_conj, hUx]
    norm_num
  let iF := diskMultiplierLineBoundary
    (K.forward.innerFactor K.forward_nonzero) x
  let iR := diskMultiplierLineBoundary (K.reflected.innerFactor hR) x
  let H := (K.reflected.outerPart hR).boundary x
  change ‖iF‖ = 1 at hIf
  have hiFunit : iF * (starRingEnd ℂ) iF = 1 := by
    rw [RCLike.mul_conj, hIf]
    norm_num
  change iR * H = (starRingEnd ℂ) (U x) *
      (starRingEnd ℂ) (iF * (c * H)) at hrel
  change U x * iF * iR = (starRingEnd ℂ) c *
      ((starRingEnd ℂ) H / H)
  rw [← mul_div_assoc]
  apply (eq_div_iff (show H ≠ 0 by exact hHr)).2
  calc
    (U x * iF * iR) * H = U x * iF * (iR * H) := by ring
    _ = U x * iF * ((starRingEnd ℂ) (U x) *
        (starRingEnd ℂ) (iF * (c * H))) := by rw [hrel]
    _ = (U x * (starRingEnd ℂ) (U x)) *
        (iF * (starRingEnd ℂ) iF) *
        (starRingEnd ℂ) c * (starRingEnd ℂ) H := by
          simp only [map_mul]
          ring
    _ = (starRingEnd ℂ) c * (starRingEnd ℂ) H := by
      rw [hUunit, hiFunit]
      ring

end

end GaloisForLFunctions.HTGeometry
