import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMModularEnergyDomain
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalAngularWeakResponse
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalSmoothResponse
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularAssembly
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularCovector
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularCircleGreen
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularCircleReconstruction
import GaloisForLFunctions.RHTower.Deninger.DeningerDivisorSchwarzMonodromy
import GaloisForLFunctions.RHTower.EisensteinLineRealness
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMAngularCutoffCalculus
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Schwarz structure of the completed modular energy graph

The PW-B source has a value-plus-two-hyperbolic-derivative modular energy domain.  This module
constructs its literal conjugate-linear real structure: conjugation preserves the smooth compact
core graph and, by continuity, its closed completion. It proves covariance of the literal
global forcing and unique finite-energy weak response; ordered CTP transport remains open.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate ENNReal

namespace RHTower.D4BMModularCore

noncomputable section

/-- Componentwise `L²` conjugation on the finite modular energy frame. -/
def energyConj (x : EnergySpace) : EnergySpace :=
  WithLp.toLp 2 (fun i => star (x.ofLp i))

@[simp] theorem energyConj_apply (x : EnergySpace) (i : Fin 3) :
    (energyConj x).ofLp i = star (x.ofLp i) := rfl

theorem spaceStar_add (f g : Space) :
    star (f + g) = star f + star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (star f) (star g), Lp.coeFn_star f,
    Lp.coeFn_star g, Lp.coeFn_star (f + g), Lp.coeFn_add f g] with z h1 h2 h3 h4 h5
  simp only [h1, h4, Pi.add_apply, Pi.star_apply, h2, h3, h5]
  exact star_add (f z) (g z)

theorem spaceStar_smul (c : ℂ) (f : Space) :
    star (c • f) = (starRingEnd ℂ) c • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_smul ((starRingEnd ℂ) c) (star f), Lp.coeFn_star f]
    with z h1 h2 h3 h4
  simp only [h1, h3, Pi.smul_apply, Pi.star_apply, h2, h4, smul_eq_mul]
  exact star_mul' c _

theorem spaceStar_norm (f : Space) : ‖star f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae (Lp.coeFn_star f) |>.trans ?_
  exact eLpNorm_star

theorem spaceStar_dist (f g : Space) : dist (star f) (star g) = dist f g := by
  have hsub : star f - star g = star (f - g) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (star f) (star g), Lp.coeFn_star f,
      Lp.coeFn_star g, Lp.coeFn_star (f - g), Lp.coeFn_sub f g]
      with z h1 h2 h3 h4 h5
    simp only [h1, h4, Pi.sub_apply, Pi.star_apply, h2, h3, h5]
    exact (star_sub _ _).symm
  rw [dist_eq_norm, dist_eq_norm, hsub, spaceStar_norm]

theorem spaceStar_star (f : Space) : star (star f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (star f), Lp.coeFn_star f] with z h1 h2
  simp only [h1, Pi.star_apply, h2]
  exact star_star _

theorem spaceStar_zero : star (0 : Space) = 0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (0 : Space), Lp.coeFn_zero ℂ 2 measure] with z h1 h2
  rw [h1, Pi.star_apply, h2]
  change (starRingEnd ℂ) 0 = 0
  exact map_zero _

theorem energyConj_add (x y : EnergySpace) :
    energyConj (x + y) = energyConj x + energyConj y := by
  apply PiLp.ext
  intro i
  change star (x.ofLp i + y.ofLp i) = star (x.ofLp i) + star (y.ofLp i)
  exact spaceStar_add _ _

theorem energyConj_smul (c : ℂ) (x : EnergySpace) :
    energyConj (c • x) = (starRingEnd ℂ) c • energyConj x := by
  apply PiLp.ext
  intro i
  change star (c • x.ofLp i) = (starRingEnd ℂ) c • star (x.ofLp i)
  exact spaceStar_smul _ _

theorem energyConj_zero : energyConj 0 = 0 := by
  apply PiLp.ext
  intro i
  change star (0 : Space) = 0
  exact spaceStar_zero

theorem energyConj_involutive (x : EnergySpace) : energyConj (energyConj x) = x := by
  apply PiLp.ext
  intro i
  change star (star (x.ofLp i)) = x.ofLp i
  exact spaceStar_star _

theorem energyConj_dist (x y : EnergySpace) :
    dist (energyConj x) (energyConj y) = dist x y := by
  rw [PiLp.dist_eq_sum (α := fun _ : Fin 3 => Space) (p := 2) (by norm_num),
    PiLp.dist_eq_sum (α := fun _ : Fin 3 => Space) (p := 2) (by norm_num)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change dist (star (x.ofLp i)) (star (y.ofLp i)) = dist (x.ofLp i) (y.ofLp i)
  exact spaceStar_dist _ _

theorem energyConj_continuous : Continuous (energyConj : EnergySpace → EnergySpace) := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => ?_)
  rw [energyConj_dist]
  simp

/-- Conjugation preserves smoothness, modular invariance, and compact quotient support. -/
def coreConj (f : CoreField) : CoreField where
  field z := Complex.conjCLE (f.field z)
  smooth := by
    intro z
    have hg : ContDiffAt ℝ ∞ (Complex.conjCLE.toContinuousLinearMap : ℂ → ℂ)
        ((f.field ∘ UpperHalfPlane.ofComplex) (z : ℂ)) :=
      Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt
    apply (hg.comp (z : ℂ) (f.smooth z)).congr_of_eventuallyEq
    filter_upwards with w
    simp [Function.comp_apply]
  invariant := by
    intro γ z
    rw [f.invariant]
  compact := by
    obtain ⟨K, hK, hf⟩ := f.compact
    refine ⟨K, hK, ?_⟩
    intro z hz hn
    change Complex.conjCLE (f.field z) = 0
    rw [hf z hz hn]
    exact map_zero _

theorem weightedDeriv_coreConj (v : ℂ) (f : CoreField) (z : UpperHalfPlane) :
    weightedDeriv v (coreConj f).field z =
      Complex.conjCLE (weightedDeriv v f.field z) := by
  unfold weightedDeriv
  have hf := ((f.smooth z).differentiableAt (by simp)).hasFDerivAt
  have hc := Complex.conjCLE.hasFDerivAt.comp (z : ℂ) hf
  change (z.im : ℂ) *
      (fderiv ℝ (⇑Complex.conjCLE ∘ f.field ∘ UpperHalfPlane.ofComplex) (z : ℂ)) v =
    Complex.conjCLE ((z.im : ℂ) *
      (fderiv ℝ (f.field ∘ UpperHalfPlane.ofComplex) (z : ℂ)) v)
  rw [hc.fderiv]
  rw [ContinuousLinearMap.comp_apply, Complex.conjCLE_apply, map_mul,
    Complex.conj_ofReal]
  change (z.im : ℂ) * Complex.conjCLE
      ((fderiv ℝ (f.field ∘ UpperHalfPlane.ofComplex) (z : ℂ)) v) = _
  rw [Complex.conjCLE_apply]

theorem fieldVector_coreConj (f : CoreField) :
    fieldVector (coreConj f) = star (fieldVector f) := by
  apply Lp.ext
  filter_upwards [
    (core_field_memLp (coreConj f).field (coreConj f).smooth
      (coreConj f).compact).coeFn_toLp,
    (core_field_memLp f.field f.smooth f.compact).coeFn_toLp,
    Lp.coeFn_star (fieldVector f)] with z hconj hfield hstar
  calc
    (fieldVector (coreConj f)) z = (coreConj f).field z := by
      simpa only [fieldVector] using hconj
    _ = Complex.conjCLE (f.field z) := rfl
    _ = star (f.field z) := Complex.conjCLE_apply _
    _ = star ((fieldVector f) z) := by
      congr 1
      simpa only [fieldVector] using hfield.symm
    _ = (star (fieldVector f)) z := hstar.symm

theorem derivativeVector_coreConj (f : CoreField) (v : ℂ) :
    derivativeVector (coreConj f) v = star (derivativeVector f v) := by
  apply Lp.ext
  filter_upwards [
    (weightedDeriv_memLp v (coreConj f).field (coreConj f).smooth
      (coreConj f).compact).coeFn_toLp,
    (weightedDeriv_memLp v f.field f.smooth f.compact).coeFn_toLp,
    Lp.coeFn_star (derivativeVector f v)] with z hconj hfield hstar
  calc
    (derivativeVector (coreConj f) v) z =
        weightedDeriv v (coreConj f).field z := by
      simpa only [derivativeVector] using hconj
    _ = Complex.conjCLE (weightedDeriv v f.field z) :=
      weightedDeriv_coreConj v f z
    _ = star (weightedDeriv v f.field z) := Complex.conjCLE_apply _
    _ = star ((derivativeVector f v) z) := by
      congr 1
      simpa only [derivativeVector] using hfield.symm
    _ = (star (derivativeVector f v)) z := hstar.symm

theorem frameGraph_coreConj (f : CoreField) :
    frameGraph (coreConj f) = energyConj (frameGraph f) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change fieldVector (coreConj f) = star (fieldVector f)
    exact fieldVector_coreConj f
  · change derivativeVector (coreConj f) 1 = star (derivativeVector f 1)
    exact derivativeVector_coreConj f 1
  · change derivativeVector (coreConj f) Complex.I =
      star (derivativeVector f Complex.I)
    exact derivativeVector_coreConj f Complex.I

/-- Componentwise conjugation preserves the completed modular value-plus-gradient graph. -/
theorem energyConj_mem_energyDomain (x : EnergySpace) (hx : x ∈ energyDomain) :
    energyConj x ∈ energyDomain := by
  let S : Submodule ℂ EnergySpace := Submodule.span ℂ (Set.range frameGraph)
  have hstable : ∀ ⦃y : EnergySpace⦄, y ∈ S → energyConj y ∈ S := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => energyConj y ∈ S) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨f, rfl⟩
      rw [← frameGraph_coreConj f]
      exact Submodule.subset_span ⟨coreConj f, rfl⟩
    · rw [energyConj_zero]
      exact S.zero_mem
    · intro y z _ _ hy hz
      rw [energyConj_add]
      exact S.add_mem hy hz
    · intro c y _ hy
      rw [energyConj_smul]
      exact S.smul_mem _ hy
  change energyConj x ∈ S.topologicalClosure
  have hmaps : Set.MapsTo energyConj (S : Set EnergySpace) (S : Set EnergySpace) := by
    intro y hy
    exact hstable hy
  exact hmaps.closure energyConj_continuous hx

/-- The Schwarz involution restricted to the completed modular energy domain. -/
def energyDomainConj (h : energyDomain) : energyDomain :=
  ⟨energyConj h, energyConj_mem_energyDomain h h.property⟩

@[simp] theorem embedding_energyDomainConj (h : energyDomain) :
    embedding (energyDomainConj h) = star (embedding h) := by
  change (energyConj (h : EnergySpace)).ofLp 0 = star ((h : EnergySpace).ofLp 0)
  exact energyConj_apply _ _

@[simp] theorem energyDomainConj_involutive (h : energyDomain) :
    energyDomainConj (energyDomainConj h) = h := by
  apply Subtype.ext
  exact energyConj_involutive h

/-- The physical branch parameter is transported by the divisor Schwarz involution. -/
theorem parameter_conj (q : XiZeroCopy) (minusBranch : Bool) :
    D4BMGlobalAngularResponse.parameter (xiZeroCopyConjEquiv q) minusBranch =
      (starRingEnd ℂ) (D4BMGlobalAngularResponse.parameter q minusBranch) := by
  have hq := deningerDivisorThetaEigen_conjEquiv q
  change ((xiZeroCopyConjEquiv q).1 : ℂ) = (starRingEnd ℂ) (q.1 : ℂ) at hq
  unfold D4BMGlobalAngularResponse.parameter D4BMQuadraticMixedSource.branchParameter
    D4BMQuadraticMixedSource.resolventParameter
  rw [hq]
  cases minusBranch <;> simp
  all_goals rw [map_ofNat]

/-- The literal Eisenstein center is transported by the divisor Schwarz involution. -/
theorem center_conj (q : XiZeroCopy) :
    D4BMGlobalAngularResponse.center (xiZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (D4BMGlobalAngularResponse.center q) := by
  have hq := deningerDivisorThetaEigen_conjEquiv q
  change ((xiZeroCopyConjEquiv q).1 : ℂ) = (starRingEnd ℂ) (q.1 : ℂ) at hq
  unfold D4BMGlobalAngularResponse.center
  rw [hq, map_sub]
  norm_num
  rw [map_ofNat]
  norm_num

/-- The literal fundamental time rate is Schwarz covariant without branch exchange. -/
theorem physicalRate_conj (q : XiZeroCopy) (branch : Bool) :
    (starRingEnd ℂ) (physicalRate q branch) =
      physicalRate (xiZeroCopyConjEquiv q) branch := by
  have hq := deningerDivisorThetaEigen_conjEquiv q
  change ((xiZeroCopyConjEquiv q).1 : ℂ) = (starRingEnd ℂ) (q.1 : ℂ) at hq
  unfold physicalRate
  rw [hq]
  cases branch
  · change (starRingEnd ℂ) (-((q.1 : ℂ)) - 1) = -((starRingEnd ℂ) (q.1 : ℂ)) - 1
    rw [map_sub, map_neg, map_one]
  · change (starRingEnd ℂ) ((q.1 : ℂ) - 2) = (starRingEnd ℂ) (q.1 : ℂ) - 2
    rw [map_sub, map_ofNat]

/-- Each literal completed-Eisenstein cusp coefficient is Schwarz covariant. -/
theorem cuspConstantCoefficient_conj (u : ℂ) (epsilon : Bool) :
    (starRingEnd ℂ) (d4BMCompletedEisensteinCuspConstantCoefficient u epsilon) =
      d4BMCompletedEisensteinCuspConstantCoefficient ((starRingEnd ℂ) u) epsilon := by
  cases epsilon <;>
    simp [d4BMCompletedEisensteinCuspConstantCoefficient, ← reflectedCompletedLambda_conj]
  all_goals rw [map_ofNat]

/-- Each explicit positive-height particular cusp power is Schwarz covariant. -/
theorem powerResponse_conj (lambda p A : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (starRingEnd ℂ) (D4BMQuadraticMixedSource.powerResponse lambda p A z) =
      D4BMQuadraticMixedSource.powerResponse ((starRingEnd ℂ) lambda)
        ((starRingEnd ℂ) p) ((starRingEnd ℂ) A) z := by
  unfold D4BMQuadraticMixedSource.powerResponse
  rw [map_mul, map_div₀, conj_cpow_of_pos hz, map_sub, map_mul, map_sub,
    map_one]

/-- The literal three-power cusp particular solution is Schwarz covariant. -/
theorem cuspPowerResponse_conj (lambda rho A D : ℂ) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (starRingEnd ℂ) (D4BMQuadraticMixedSource.cuspPowerResponse lambda rho A D z) =
      D4BMQuadraticMixedSource.cuspPowerResponse ((starRingEnd ℂ) lambda)
        ((starRingEnd ℂ) rho) ((starRingEnd ℂ) A) ((starRingEnd ℂ) D) z := by
  unfold D4BMQuadraticMixedSource.cuspPowerResponse
  rw [map_add, map_add, powerResponse_conj _ _ _ _ hz, powerResponse_conj _ _ _ _ hz,
    powerResponse_conj _ _ _ _ hz]
  simp only [map_mul, map_pow, map_sub, map_one, map_ofNat]

/-- The complete explicit cusp response is Schwarz covariant at every positive height. -/
theorem cuspResponse_conj (q : XiZeroCopy) (minusBranch : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (starRingEnd ℂ) (D4BMGlobalAngularResponse.cuspResponse q minusBranch z) =
      D4BMGlobalAngularResponse.cuspResponse (xiZeroCopyConjEquiv q) minusBranch z := by
  unfold D4BMGlobalAngularResponse.cuspResponse
  rw [map_mul, map_div₀, parameter_conj, cuspPowerResponse_conj _ _ _ _ _ hz,
    center_conj q]
  have hq := deningerDivisorThetaEigen_conjEquiv q
  change ((xiZeroCopyConjEquiv q).1 : ℂ) = (starRingEnd ℂ) (q.1 : ℂ) at hq
  rw [hq, cuspConstantCoefficient_conj, cuspConstantCoefficient_conj]
  rw [map_ofNat]

/-- The literal smooth height cutoff is real. -/
theorem cutoff_conj (z : Fin 2 → ℝ) :
    (starRingEnd ℂ) (D4BMGlobalAngularResponse.cutoff z) =
      D4BMGlobalAngularResponse.cutoff z := by
  simp [D4BMGlobalAngularResponse.cutoff]

/-- The complete explicit cutoff response is Schwarz covariant. -/
theorem cutoffResponse_conj (q : XiZeroCopy) (minusBranch : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (starRingEnd ℂ) (D4BMGlobalAngularResponse.cutoffResponse q minusBranch z) =
      D4BMGlobalAngularResponse.cutoffResponse (xiZeroCopyConjEquiv q) minusBranch z := by
  unfold D4BMGlobalAngularResponse.cutoffResponse
  rw [map_mul, cutoff_conj, cuspResponse_conj _ _ _ hz]

/-- The full literal Eisenstein scalar is Schwarz covariant at positive height. -/
theorem scalar_conj (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (starRingEnd ℂ) (D4BMGlobalAngularResponse.scalar (D4BMGlobalAngularResponse.center q) z) =
      D4BMGlobalAngularResponse.scalar
        (D4BMGlobalAngularResponse.center (xiZeroCopyConjEquiv q)) z := by
  unfold D4BMGlobalAngularResponse.scalar
  rw [cuspLeg_conj _ _ hz, center_conj q]

/-- The complete literal angular forcing is Schwarz covariant at every positive-height point. -/
theorem forcing_conj (q : XiZeroCopy) (minusBranch : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    (starRingEnd ℂ) (D4BMGlobalAngularResponse.forcing q minusBranch z) =
      D4BMGlobalAngularResponse.forcing (xiZeroCopyConjEquiv q) minusBranch z := by
  have hcut : D4BMGlobalAngularResponse.cutoffResponse (xiZeroCopyConjEquiv q) minusBranch =ᶠ[𝓝 z]
      fun w => conj (D4BMGlobalAngularResponse.cutoffResponse q minusBranch w) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    simpa using (cutoffResponse_conj q minusBranch w hw).symm
  unfold D4BMGlobalAngularResponse.forcing
  rw [map_sub, map_mul, map_div₀, parameter_conj, map_pow, scalar_conj _ _ hz,
    map_sub, map_mul, cutoffResponse_conj _ _ _ hz,
    D4BMAngularSeries.hyperbolicLaplacian_congr hcut,
    D4BMAngularSeries.hyperbolicLaplacian_conj]
  rw [map_ofNat]

/-- The admitted finite-energy forcing vector is Schwarz covariant. -/
theorem forcingVector_conj (q : XiZeroCopy) (minusBranch : Bool) :
    star (D4BMGlobalAngularResponse.forcingVector q minusBranch) =
      D4BMGlobalAngularResponse.forcingVector (xiZeroCopyConjEquiv q) minusBranch := by
  apply Lp.ext
  filter_upwards [D4BMGlobalAngularResponse.forcingVector_coe q minusBranch,
    D4BMGlobalAngularResponse.forcingVector_coe (xiZeroCopyConjEquiv q) minusBranch,
    Lp.coeFn_star (D4BMGlobalAngularResponse.forcingVector q minusBranch)] with z hq hqc hs
  rw [hs, Pi.star_apply, hq, hqc]
  exact forcing_conj q minusBranch (D4BMGlobalAngularResponse.coordinates z)
    (by simpa [D4BMGlobalAngularResponse.coordinates] using z.im_pos)

/-- Conjugation is antiunitary on the modular `L²` field space. -/
theorem spaceStar_inner (f g : Space) :
    inner ℂ (star f) (star g) = (starRingEnd ℂ) (inner ℂ f g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_star f, Lp.coeFn_star g] with z hf hg
  rw [hf, hg]
  simp only [Pi.star_apply, RCLike.star_def, RCLike.inner_apply', map_mul, Complex.conj_conj]

/-- Componentwise conjugation is antiunitary on the finite modular energy frame. -/
theorem energyConj_inner (x y : EnergySpace) :
    inner ℂ (energyConj x) (energyConj y) = (starRingEnd ℂ) (inner ℂ x y) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ (star (x.ofLp i)) (star (y.ofLp i)) =
    (starRingEnd ℂ) (inner ℂ (x.ofLp i) (y.ofLp i))
  exact spaceStar_inner _ _

/-- The restricted Schwarz involution is antiunitary for the completed energy-domain form. -/
theorem energyDomainConj_inner (x y : energyDomain) :
    inner ℂ (energyDomainConj x) (energyDomainConj y) =
      (starRingEnd ℂ) (inner ℂ x y) := by
  change inner ℂ (energyConj (x : EnergySpace)) (energyConj (y : EnergySpace)) = _
  exact energyConj_inner _ _

private theorem star_inner_energyDomainConj_left (v h : energyDomain) :
    (starRingEnd ℂ) (inner ℂ (energyDomainConj v) h) =
      inner ℂ v (energyDomainConj h) := by
  simpa using (energyDomainConj_inner (energyDomainConj v) h).symm

private theorem star_inner_embedding_energyDomainConj_left (v h : energyDomain) :
    (starRingEnd ℂ) (inner ℂ (embedding (energyDomainConj v)) (embedding h)) =
      inner ℂ (embedding v) (embedding (energyDomainConj h)) := by
  simpa only [embedding_energyDomainConj, energyDomainConj_involutive, star_star] using
    (spaceStar_inner (embedding (energyDomainConj v)) (embedding h)).symm

private theorem star_inner_embedding_energyDomainConj_forcing
    (q : XiZeroCopy) (minusBranch : Bool) (v : energyDomain) :
    (starRingEnd ℂ) (inner ℂ (embedding (energyDomainConj v))
      (D4BMGlobalAngularResponse.forcingVector q minusBranch)) =
      inner ℂ (embedding v)
        (D4BMGlobalAngularResponse.forcingVector (xiZeroCopyConjEquiv q) minusBranch) := by
  simpa only [embedding_energyDomainConj, star_star, forcingVector_conj] using
    (spaceStar_inner (embedding (energyDomainConj v))
      (D4BMGlobalAngularResponse.forcingVector q minusBranch)).symm

private theorem weakSolution_conj_transport (q : XiZeroCopy) (minusBranch : Bool)
    (h : energyDomain) (hh : WeakSolution q minusBranch h) :
    WeakSolution (xiZeroCopyConjEquiv q) minusBranch (energyDomainConj h) := by
  intro v
  have hs := congrArg (starRingEnd ℂ) (hh (energyDomainConj v))
  simpa only [map_sub, map_mul, map_neg, map_one, parameter_conj,
    star_inner_energyDomainConj_left, star_inner_embedding_energyDomainConj_left,
    star_inner_embedding_energyDomainConj_forcing] using hs

/-- The constructed full finite-energy response obeys literal divisor Schwarz covariance. -/
theorem weakResponse_conj (q : XiZeroCopy) (minusBranch : Bool) :
    energyDomainConj (weakResponse q minusBranch) =
      weakResponse (xiZeroCopyConjEquiv q) minusBranch := by
  apply full_forcing_weak_response_unique
  · exact weakSolution_conj_transport q minusBranch _ (weakResponse_spec q minusBranch)
  · exact weakResponse_spec _ _

/-- Zero extension from the open modular cell preserves the `L²` Schwarz relation. -/
private theorem cellExtension_star_ae (u : Space) :
    cellExtension (star u) =ᵐ[(volume : Measure UpperHalfPlane)]
      fun z => (starRingEnd ℂ) (cellExtension u z) := by
  have hstar := Lp.coeFn_star u
  have hfdo := ae_restrict_of_ae_restrict_of_subset fdo_subset_fd hstar
  have hvol := (ae_restrict_iff' isOpen_fdo.measurableSet).mp hfdo
  filter_upwards [hvol] with z hz
  by_cases hzfd : z ∈ fdo
  · simp only [cellExtension, Set.indicator_of_mem hzfd]
    exact hz hzfd
  · simp only [cellExtension, Set.indicator_of_notMem hzfd, map_zero]

/-- Modular periodization transports the Schwarz relation through the full countable orbit. -/
private theorem globalLift_star_ae (u : Space) :
    globalLift (star u) =ᵐ[(volume : Measure UpperHalfPlane)]
      fun z => (starRingEnd ℂ) (globalLift u z) := by
  have hcell := cellExtension_star_ae u
  have hall : ∀ᵐ z : UpperHalfPlane ∂(volume : Measure UpperHalfPlane),
      ∀ γ : PSL2Z, cellExtension (star u) (γ • z) =
        (starRingEnd ℂ) (cellExtension u (γ • z)) := by
    rw [MeasureTheory.ae_all_iff]
    intro γ
    exact (measurePreserving_smul γ volume).quasiMeasurePreserving.ae hcell
  filter_upwards [hall] with z hz
  unfold globalLift periodize
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro γ
  exact hz γ

private theorem chartSmooth_star {f : UpperHalfPlane → ℂ} (hf : ChartSmooth f) :
    ChartSmooth (fun z => (starRingEnd ℂ) (f z)) := by
  intro z
  have hg : ContDiffAt ℝ ∞ (Complex.conjCLE.toContinuousLinearMap : ℂ → ℂ)
      ((f ∘ ofComplex) (z : ℂ)) :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.contDiffAt
  change ContDiffAt ℝ ∞ ((fun w => (starRingEnd ℂ) (f w)) ∘ ofComplex) (z : ℂ)
  apply (hg.comp (z : ℂ) (hf z)).congr_of_eventuallyEq
  filter_upwards with w
  exact (Complex.conjCLE_apply _).symm

private theorem chartSmooth_eq_of_ae_eq {f g : UpperHalfPlane → ℂ}
    (hf : ChartSmooth f) (hg : ChartSmooth g)
    (he : f =ᵐ[(volume : Measure UpperHalfPlane)] g) : f = g := by
  have hm : ∀ᵐ z ∂Measure.map UpperHalfPlane.coe (volume : Measure UpperHalfPlane),
      f (ofComplex z) = g (ofComplex z) :=
    UpperHalfPlane.measurableEmbedding_coe.ae_map_iff.mpr (by
      filter_upwards [he] with z hz
      simpa only [ofComplex_apply] using hz)
  rw [map_volume_chart_eq] at hm
  have hd : Measurable (fun z : ℂ => (chartDensity z : ℝ≥0∞)) := by
    unfold chartDensity
    fun_prop
  have hh := (ae_withDensity_iff hd).mp hm
  have hae : (fun z : ℂ => f (ofComplex z)) =ᵐ[volume.restrict {z : ℂ | 0 < z.im}]
      (fun z : ℂ => g (ofComplex z)) := by
    filter_upwards [hh, ae_restrict_mem isOpen_upperHalfPlaneSet.measurableSet] with z hz hy
    exact hz (by simp [chartDensity, ne_of_gt hy])
  have hc (a : UpperHalfPlane → ℂ) (ha : ChartSmooth a) :
      ContinuousOn (fun z : ℂ => a (ofComplex z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hh := ha (ofComplex z)
    rw [ofComplex_apply_of_im_pos hz] at hh
    exact hh.continuousAt.continuousWithinAt
  have hp := Measure.eqOn_open_of_ae_eq hae isOpen_upperHalfPlaneSet (hc f hf) (hc g hg)
  funext z
  simpa only [ofComplex_apply] using hp z.im_pos

/-- The separately glued smooth response inherits the finite-energy Schwarz involution. -/
theorem globalResponse_conj (q : XiZeroCopy) (minusBranch : Bool) :
    globalResponse (xiZeroCopyConjEquiv q) minusBranch =
      fun z => (starRingEnd ℂ) (globalResponse q minusBranch z) := by
  apply chartSmooth_eq_of_ae_eq
  · exact globalResponse_smooth _ _
  · exact chartSmooth_star (globalResponse_smooth _ _)
  have hembedding : embedding (weakResponse (xiZeroCopyConjEquiv q) minusBranch) =
      star (embedding (weakResponse q minusBranch)) := by
    rw [← weakResponse_conj, embedding_energyDomainConj]
  have hleft := globalResponse_ae_lift (xiZeroCopyConjEquiv q) minusBranch
  rw [hembedding] at hleft
  have hstar := globalLift_star_ae (embedding (weakResponse q minusBranch))
  have hright := globalResponse_ae_lift q minusBranch
  filter_upwards [hleft, hstar, hright] with z hzleft hzstar hzright
  rw [hzleft, hzstar, hzright]

/-- The literal globally glued cusp cutoff is Schwarz covariant across every cell seam. -/
theorem globalCuspCutoff_conj (q : XiZeroCopy) (minusBranch : Bool) :
    globalCuspCutoff (xiZeroCopyConjEquiv q) minusBranch =
      fun z => (starRingEnd ℂ) (globalCuspCutoff q minusBranch z) := by
  funext z
  obtain ⟨A, hA⟩ := exists_smul_mem_fd z
  have hleft := globalCuspCutoff_invariant (xiZeroCopyConjEquiv q) minusBranch
    (QuotientGroup.mk A) z
  have hright := globalCuspCutoff_invariant q minusBranch (QuotientGroup.mk A) z
  simp only [PSL2Z_mk_smul] at hleft hright
  calc
    globalCuspCutoff (xiZeroCopyConjEquiv q) minusBranch z =
        globalCuspCutoff (xiZeroCopyConjEquiv q) minusBranch (A • z) := hleft.symm
    _ = D4BMGlobalAngularResponse.cutoffResponse (xiZeroCopyConjEquiv q) minusBranch
        (D4BMGlobalAngularResponse.coordinates (A • z)) :=
      globalCuspCutoff_eq_on_fd _ _ _ hA
    _ = (starRingEnd ℂ) (D4BMGlobalAngularResponse.cutoffResponse q minusBranch
        (D4BMGlobalAngularResponse.coordinates (A • z))) :=
      (cutoffResponse_conj q minusBranch _
        (by simpa [D4BMGlobalAngularResponse.coordinates] using (A • z).im_pos)).symm
    _ = (starRingEnd ℂ) (globalCuspCutoff q minusBranch (A • z)) :=
      (congrArg (starRingEnd ℂ) (globalCuspCutoff_eq_on_fd q minusBranch _ hA)).symm
    _ = (starRingEnd ℂ) (globalCuspCutoff q minusBranch z) := congrArg (starRingEnd ℂ) hright

/-- The complete literal modular angular field is Schwarz covariant pointwise. -/
theorem fullAngular_conj (q : XiZeroCopy) (minusBranch : Bool) :
    fullAngular (xiZeroCopyConjEquiv q) minusBranch =
      fun z => (starRingEnd ℂ) (fullAngular q minusBranch z) := by
  funext z
  unfold fullAngular
  rw [globalCuspCutoff_conj, globalResponse_conj, map_add]

/-- The original-coordinate full angular field is Schwarz covariant pointwise. -/
theorem fullAngularField_conj (q : XiZeroCopy) (minusBranch : Bool) :
    fullAngularField (xiZeroCopyConjEquiv q) minusBranch =
      fun z => (starRingEnd ℂ) (fullAngularField q minusBranch z) := by
  funext z
  unfold fullAngularField
  rw [fullAngular_conj]

private theorem circleAverage_conj (F : ℝ → ℂ) :
    (starRingEnd ℂ) (D4BMNativeCircle.average F) =
      D4BMNativeCircle.average (fun theta => (starRingEnd ℂ) (F theta)) := by
  have hcoeff : (starRingEnd ℂ) (1 / (2 * Real.pi : ℂ)) = 1 / (2 * Real.pi : ℂ) := by
    rw [map_div₀, map_one, map_mul, map_ofNat, Complex.conj_ofReal]
  unfold D4BMNativeCircle.average
  rw [map_mul, hcoeff, ← integral_conj]

/-- The literal full circular angular mean is Schwarz covariant. -/
theorem angularMean_conj (q : XiZeroCopy) (minusBranch : Bool) (d x k : ℝ) :
    (starRingEnd ℂ) (D4BMFullAngularCircle.angularMean q minusBranch d x k) =
      D4BMFullAngularCircle.angularMean (xiZeroCopyConjEquiv q) minusBranch d x k := by
  change (starRingEnd ℂ) (D4BMNativeCircle.average
      (fun theta => fullAngularField q minusBranch (D4BMNativeCircle.logCircle d theta x k))) =
    D4BMNativeCircle.average
      (fun theta => fullAngularField (xiZeroCopyConjEquiv q) minusBranch
        (D4BMNativeCircle.logCircle d theta x k))
  rw [circleAverage_conj]
  congr 1
  funext theta
  exact (congrFun (fullAngularField_conj q minusBranch) _).symm

/-- The literal direct-minus-image circular kernel is Schwarz covariant. -/
theorem angularDirichletKernel_conj (q : XiZeroCopy) (minusBranch : Bool)
    (h x y X k : ℝ) :
    (starRingEnd ℂ) (D4BMFullAngularReconstruction.angularDirichletKernel q minusBranch h x y X k) =
      D4BMFullAngularReconstruction.angularDirichletKernel
        (xiZeroCopyConjEquiv q) minusBranch h x y X k := by
  unfold D4BMFullAngularReconstruction.angularDirichletKernel
  by_cases hd : |x - y| ≤ h <;> by_cases hi : |x + y| ≤ h <;>
    simp only [hd, hi, ↓reduceIte, map_sub, map_div₀, map_ofNat, map_zero, angularMean_conj]

end

end RHTower.D4BMModularCore
