import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularEnergyDomain
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalAngularWeakResponse
import GaloisForLFunctions.RHTower.DeningerDivisorSchwarzMonodromy
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Schwarz structure of the completed modular energy graph

The PW-B source has a value-plus-two-hyperbolic-derivative modular energy domain.  This module
constructs its literal conjugate-linear real structure: conjugation preserves the smooth compact
core graph and, by continuity, its closed completion.  It does not assert the still-open
conjugation covariance of the global forcing or weak response.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate

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
  all_goals ring

end

end RHTower.D4BMModularCore
