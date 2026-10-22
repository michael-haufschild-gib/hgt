import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSpatialTests

/-! The completed differential graph of the literal radial and modular core fields. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointWave
noncomputable section

abbrev JointEnergySpace := PiLp 2 (fun _ : Fin 4 => SpatialSpace)

/-- Actual value, radial derivative, and both geometrically weighted angular derivatives. -/
def jointGraph (f : RadialCore) (g : D4BMModularCore.CoreField) : JointEnergySpace :=
  WithLp.toLp 2 ![
    l2SeparatedProduct (radialValue f) (D4BMModularCore.fieldVector g),
    l2SeparatedProduct (radialDerivative f) (D4BMModularCore.fieldVector g),
    l2SeparatedProduct (radialWeightedValue f) (D4BMModularCore.derivativeVector g 1),
    l2SeparatedProduct (radialWeightedValue f) (D4BMModularCore.derivativeVector g Complex.I)]

/-- Closure of the actual finite differential sums; no domain or derivative premise is supplied. -/
def jointDomain : Submodule ℂ JointEnergySpace :=
  (Submodule.span ℂ (Set.range (fun p : RadialCore × D4BMModularCore.CoreField =>
    jointGraph p.1 p.2))).topologicalClosure

instance : CompleteSpace jointDomain := by unfold jointDomain; infer_instance

def jointEmbedding : jointDomain →L[ℂ] SpatialSpace :=
  (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) 0).comp jointDomain.subtypeL

theorem jointGraph_mem (f : RadialCore) (g : D4BMModularCore.CoreField) :
    jointGraph f g ∈ jointDomain :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(f,g),rfl⟩)

theorem jointEmbedding_norm_le (u : jointDomain) : ‖jointEmbedding u‖ ≤ ‖u‖ :=
  PiLp.norm_apply_le (u : JointEnergySpace) 0

/-- The graph projection is dense in the full product-measure space. -/
theorem jointEmbedding_dense : Dense (jointEmbedding.range : Set SpatialSpace) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm
  · intro u hu
    change u = 0
    apply spatialValue_total u
    intro f g
    exact (Submodule.mem_orthogonal _ _).mp hu _
      ⟨⟨jointGraph f g,jointGraph_mem f g⟩,rfl⟩
  · exact bot_le

/-- The original radial integration-by-parts functional, continuous in the full graph norm. -/
def radialConstraint (f : RadialCore) (g : D4BMModularCore.CoreField) :
    JointEnergySpace →L[ℂ] ℂ :=
  (innerSL ℂ (l2SeparatedProduct (radialValue f) (D4BMModularCore.fieldVector g))).comp
    (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) 1) +
  (innerSL ℂ (l2SeparatedProduct (radialDerivative f) (D4BMModularCore.fieldVector g))).comp
    (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) 0)

/-- The original angular integration-by-parts functional with the actual radial weight. -/
def angularConstraint (f : RadialCore) (g : D4BMModularCore.InteriorTest) (i : Fin 2) :
    JointEnergySpace →L[ℂ] ℂ :=
  (innerSL ℂ (l2SeparatedProduct (radialValue f) (D4BMModularCore.massTest g))).comp
    (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) i.succ.succ) +
  (innerSL ℂ (l2SeparatedProduct (radialWeightedValue f)
    (D4BMModularCore.fluxTest g (D4BMModularCore.direction i)))).comp
    (PiLp.proj 2 (fun _ : Fin 4 => SpatialSpace) 0)

private theorem radialConstraint_graph (f h : RadialCore) (g k : D4BMModularCore.CoreField) :
    radialConstraint f g (jointGraph h k) = 0 := by
  change inner ℂ (l2SeparatedProduct (radialValue f) (D4BMModularCore.fieldVector g))
      (l2SeparatedProduct (radialDerivative h) (D4BMModularCore.fieldVector k)) +
    inner ℂ (l2SeparatedProduct (radialDerivative f) (D4BMModularCore.fieldVector g))
      (l2SeparatedProduct (radialValue h) (D4BMModularCore.fieldVector k)) = 0
  rw [l2SeparatedProduct_inner,l2SeparatedProduct_inner,← add_mul,radialDerivative_green,zero_mul]

private theorem angularConstraint_graph (f h : RadialCore) (g : D4BMModularCore.InteriorTest)
    (i : Fin 2) (k : D4BMModularCore.CoreField) :
    angularConstraint f g i (jointGraph h k) = 0 := by
  have hc : jointGraph h k i.succ.succ =
      l2SeparatedProduct (radialWeightedValue h)
        (D4BMModularCore.derivativeVector k (D4BMModularCore.direction i)) := by
    fin_cases i <;> rfl
  change inner ℂ (l2SeparatedProduct (radialValue f) (D4BMModularCore.massTest g))
      (jointGraph h k i.succ.succ) +
    inner ℂ (l2SeparatedProduct (radialWeightedValue f)
      (D4BMModularCore.fluxTest g (D4BMModularCore.direction i)))
      (l2SeparatedProduct (radialValue h) (D4BMModularCore.fieldVector k)) = 0
  rw [hc,l2SeparatedProduct_inner,l2SeparatedProduct_inner,radialWeightedValue_symmetric,
    ← mul_add,angularDerivative_green,mul_zero]

private theorem constraint_completed (L : JointEnergySpace →L[ℂ] ℂ)
    (hL : ∀ f g, L (jointGraph f g) = 0) (u : jointDomain) : L u = 0 := by
  have hs : jointDomain ≤ L.toLinearMap.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨f,g⟩,rfl⟩
      exact hL f g
    · exact L.isClosed_ker
  exact hs u.property

/-- The radial Green identity survives completion of the actual differential graph. -/
theorem radialConstraint_completed (f : RadialCore) (g : D4BMModularCore.CoreField)
    (u : jointDomain) : radialConstraint f g u = 0 :=
  constraint_completed _ (fun h k => radialConstraint_graph f h g k) u

/-- Both modular Green identities survive completion with the nonconstant radial weight. -/
theorem angularConstraint_completed (f : RadialCore) (g : D4BMModularCore.InteriorTest)
    (i : Fin 2) (u : jointDomain) : angularConstraint f g i u = 0 :=
  constraint_completed _ (fun h k => angularConstraint_graph f h g i k) u

end
end RHTower.D4BMJointWave
