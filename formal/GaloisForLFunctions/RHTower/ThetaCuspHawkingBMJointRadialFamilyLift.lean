import GaloisForLFunctions.HTGeometry.BochnerL2ProductIsometry
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointAngularEnergyTests

/-! The exact continuous assembly of angular-energy-valued radial L² packets into the original joint graph. -/
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointWave
noncomputable section

private theorem bochnerL2Product_map {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (L : E →L[ℂ] F) (f : Lp ℂ 2 μ) (g : E) :
    L.compLp (bochnerL2Product f g) = bochnerL2Product f (L g) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (bochnerL2Product f g),bochnerL2Product_ae f g,
    bochnerL2Product_ae f (L g)] with t h0 h1 h2
  rw [h0,h1,h2,map_smul]

def angularEnergySlot (i : Fin 3) : D4BMModularCore.energyDomain →L[ℂ] D4BMModularCore.Space :=
  (PiLp.proj 2 (fun _ : Fin 3 => D4BMModularCore.Space) i).comp
    D4BMModularCore.energyDomain.subtypeL

def radialFamilySlot (i : Fin 3) :
    Lp D4BMModularCore.energyDomain 2 radialMeasure →L[ℂ] SpatialSpace :=
  bochnerL2ProductEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((angularEnergySlot i).compLpL 2 radialMeasure)

theorem radialFamilySlot_pure (i : Fin 3) (f : RadialSpace) (g : D4BMModularCore.energyDomain) :
    radialFamilySlot i (bochnerL2Product f g) =
      l2SeparatedProduct f ((g : D4BMModularCore.EnergySpace) i) := by
  change bochnerL2ProductEquiv ((angularEnergySlot i).compLp (bochnerL2Product f g)) = _
  rw [bochnerL2Product_map,bochnerL2ProductEquiv_pure]
  rfl

abbrev FamilyPacketSpace := PiLp 2 (fun _ : Fin 3 => Lp D4BMModularCore.energyDomain 2 radialMeasure)

/-- Values, radial derivatives, and weighted angular derivatives retain their original slots. -/
def familyPacketLift : FamilyPacketSpace →L[ℂ] JointEnergySpace :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 => SpatialSpace)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 4 => ![
      (radialFamilySlot 0).comp (PiLp.proj 2 _ 0),
      (radialFamilySlot 0).comp (PiLp.proj 2 _ 1),
      (radialFamilySlot 1).comp (PiLp.proj 2 _ 2),
      (radialFamilySlot 2).comp (PiLp.proj 2 _ 2)] i))

theorem familyPacketLift_apply (p : FamilyPacketSpace) :
    familyPacketLift p = WithLp.toLp 2 ![
      radialFamilySlot 0 (p 0),radialFamilySlot 0 (p 1),
      radialFamilySlot 1 (p 2),radialFamilySlot 2 (p 2)] := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

theorem familyPacketLift_pure (f : RadialCore) (g : D4BMModularCore.energyDomain) :
    familyPacketLift (WithLp.toLp 2 ![
      bochnerL2Product (radialValue f) g,bochnerL2Product (radialDerivative f) g,
      bochnerL2Product (radialWeightedValue f) g]) = radialAngularLift f g := by
  rw [familyPacketLift_apply,radialAngularLift_apply]
  apply PiLp.ext
  intro i
  fin_cases i <;> exact radialFamilySlot_pure _ _ _

end
end RHTower.D4BMJointWave
