import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspWeightCore
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspWeightSpatialMultipliers
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointRadialFamilyData

/-! Bounded cusp multiplication acts on the original completed joint differential domain. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointWave
open D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem core_value_ae (g : CoreField) :
    (fun p : ℝ × UpperHalfPlane => fieldVector g p.2) =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      fun p => g.field p.2 :=
  Measure.quasiMeasurePreserving_snd.ae_eq_comp (core_field_memLp g.field g.smooth g.compact).coeFn_toLp

private theorem core_deriv_ae (g : CoreField) (v : ℂ) :
    (fun p : ℝ × UpperHalfPlane => derivativeVector g v p.2) =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      fun p => weightedDeriv v g.field p.2 :=
  Measure.quasiMeasurePreserving_snd.ae_eq_comp (weightedDeriv_memLp v g.field g.smooth g.compact).coeFn_toLp

private theorem cell_ae : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure,
    p.2 ∈ ModularGroup.fd :=
  Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet)

private theorem value_product (N : ℝ) (hN : 0 < N) (f : RadialSpace) (g : CoreField) :
    cuspSpatialMultiply N hN (l2SeparatedProduct f (fieldVector g)) =
      l2SeparatedProduct f (fieldVector (cuspWeightedCore N hN g)) := by
  apply Lp.ext
  filter_upwards [cuspSpatialMultiply_coe N hN (l2SeparatedProduct f (fieldVector g)),
    l2SeparatedProduct_ae f (fieldVector g),
    l2SeparatedProduct_ae f (fieldVector (cuspWeightedCore N hN g)),
    core_value_ae g,core_value_ae (cuspWeightedCore N hN g)] with p hM ha hb hg hw
  simp only [l2SeparatedFun] at ha hb
  rw [hM,ha,hb,hg,hw]
  change modularCuspWeight N p.2*(f p.1*g.field p.2) = f p.1*(modularCuspWeight N p.2*g.field p.2)
  ring

private theorem horizontal_product (N : ℝ) (hN : 0 < N) (f : RadialSpace) (g : CoreField) :
    cuspSpatialMultiply N hN (l2SeparatedProduct f (derivativeVector g 1)) =
      l2SeparatedProduct f (derivativeVector (cuspWeightedCore N hN g) 1) := by
  apply Lp.ext
  filter_upwards [cuspSpatialMultiply_coe N hN (l2SeparatedProduct f (derivativeVector g 1)),
    l2SeparatedProduct_ae f (derivativeVector g 1),
    l2SeparatedProduct_ae f (derivativeVector (cuspWeightedCore N hN g) 1),
    core_deriv_ae g 1,core_deriv_ae (cuspWeightedCore N hN g) 1,cell_ae] with p hM ha hb hg hw hp
  simp only [l2SeparatedFun] at ha hb
  rw [hM,ha,hb,hg,hw,cuspWeightedCore_horizontal N hN g p.2 hp]
  dsimp [cuspWeightSymbol]
  ring

private theorem vertical_product (N : ℝ) (hN : 0 < N) (f : RadialCore) (g : CoreField) :
    cuspSpatialMultiply N hN (l2SeparatedProduct (radialWeightedValue f) (derivativeVector g Complex.I)) +
      cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (l2SeparatedProduct (radialValue f) (fieldVector g))) =
    l2SeparatedProduct (radialWeightedValue f) (derivativeVector (cuspWeightedCore N hN g) Complex.I) := by
  have hrv : (fun p : ℝ × UpperHalfPlane => radialValue f p.1) =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      fun p => f.field p.1 :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (f.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := radialMeasure) f.compact).coeFn_toLp
  have hrw : (fun p : ℝ × UpperHalfPlane => radialWeightedValue f p.1) =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      fun p => angularWeight p.1*f.field p.1 :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp (radialWeightedValue_ae f)
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      (cuspSpatialMultiply N hN (l2SeparatedProduct (radialWeightedValue f) (derivativeVector g Complex.I)))
      (cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (l2SeparatedProduct (radialValue f) (fieldVector g)))),
    cuspSpatialMultiply_coe N hN (l2SeparatedProduct (radialWeightedValue f) (derivativeVector g Complex.I)),
    cuspSpatialLogSlope_coe N hN (cuspSpatialMultiply N hN (l2SeparatedProduct (radialValue f) (fieldVector g))),
    cuspSpatialMultiply_coe N hN (l2SeparatedProduct (radialValue f) (fieldVector g)),
    l2SeparatedProduct_ae (radialWeightedValue f) (derivativeVector g Complex.I),
    l2SeparatedProduct_ae (radialValue f) (fieldVector g),
    l2SeparatedProduct_ae (radialWeightedValue f) (derivativeVector (cuspWeightedCore N hN g) Complex.I),
    core_value_ae g,core_deriv_ae g Complex.I,core_deriv_ae (cuspWeightedCore N hN g) Complex.I,
    hrv,hrw,cell_ae] with p hadd hM hR hMv ha hb ht hg hd hw hv hr hp
  simp only [l2SeparatedFun] at ha hb ht hr
  rw [hadd,Pi.add_apply,hM,hR,hMv,ha,hb,ht,hg,hd,hw,hv,hr,cuspWeightedCore_vertical]
  have hc := cuspLogSlopeSymbol_weight N hN p hp
  dsimp [cuspWeightSymbol] at hc ⊢
  linear_combination (f.field p.1*g.field p.2)*hc

/-- The original differential product rule as a bounded map on all four graph components. -/
def cuspGraphMap (N : ℝ) (hN : 0 < N) : JointEnergySpace →L[ℂ] JointEnergySpace :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 => SpatialSpace)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 4 => ![
      (cuspSpatialMultiply N hN).comp (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) 0),
      (cuspSpatialMultiply N hN).comp (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) 1),
      (cuspSpatialMultiply N hN).comp (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) 2),
      (cuspSpatialMultiply N hN).comp (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) 3)+
        ((cuspSpatialLogSlope N hN).comp (cuspSpatialMultiply N hN)).comp
          (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) 0)] i))

theorem cuspGraphMap_apply (N : ℝ) (hN : 0 < N) (u : JointEnergySpace) :
    cuspGraphMap N hN u = WithLp.toLp 2 ![
      cuspSpatialMultiply N hN (u 0),cuspSpatialMultiply N hN (u 1),
      cuspSpatialMultiply N hN (u 2),cuspSpatialMultiply N hN (u 3)+
        cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN (u 0))] := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

/-- The bounded graph map agrees with multiplication of the original smooth modular core. -/
theorem cuspGraphMap_core (N : ℝ) (hN : 0 < N) (f : RadialCore) (g : CoreField) :
    cuspGraphMap N hN (jointGraph f g) = jointGraph f (cuspWeightedCore N hN g) := by
  rw [cuspGraphMap_apply]
  apply PiLp.ext
  intro i
  fin_cases i
  · exact value_product N hN (radialValue f) g
  · exact value_product N hN (radialDerivative f) g
  · exact horizontal_product N hN (radialWeightedValue f) g
  · exact vertical_product N hN f g

/-- Multiplication preserves the actual completed domain, without a new domain premise. -/
theorem cuspGraphMap_mem (N : ℝ) (hN : 0 < N) (u : jointDomain) :
    cuspGraphMap N hN u ∈ jointDomain := by
  have hs : jointDomain ≤ jointDomain.comap (cuspGraphMap N hN).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨f,g⟩,rfl⟩
      change cuspGraphMap N hN (jointGraph f g) ∈ jointDomain
      rw [cuspGraphMap_core]
      exact jointGraph_mem _ _
    · exact (Submodule.isClosed_topologicalClosure _).preimage (cuspGraphMap N hN).continuous
  exact hs u.property

def jointCuspWeight (N : ℝ) (hN : 0 < N) : jointDomain →L[ℂ] jointDomain :=
  ((cuspGraphMap N hN).comp jointDomain.subtypeL).codRestrict jointDomain (cuspGraphMap_mem N hN)

theorem jointCuspWeight_components (N : ℝ) (hN : 0 < N) (u : jointDomain) :
    (jointCuspWeight N hN u : JointEnergySpace) = WithLp.toLp 2 ![
      cuspSpatialMultiply N hN ((u : JointEnergySpace) 0),
      cuspSpatialMultiply N hN ((u : JointEnergySpace) 1),
      cuspSpatialMultiply N hN ((u : JointEnergySpace) 2),
      cuspSpatialMultiply N hN ((u : JointEnergySpace) 3)+
        cuspSpatialLogSlope N hN (cuspSpatialMultiply N hN ((u : JointEnergySpace) 0))] :=
  cuspGraphMap_apply N hN u

theorem jointCuspWeight_mass (N : ℝ) (hN : 0 < N) (u : jointDomain) :
    jointEmbedding (jointCuspWeight N hN u) = cuspSpatialMultiply N hN (jointEmbedding u) := rfl

end
end RHTower.D4BMJointWave
