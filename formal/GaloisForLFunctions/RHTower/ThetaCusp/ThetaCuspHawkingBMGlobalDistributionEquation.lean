import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalChartGreen

/-!
The actual full-forcing weak response satisfies the distribution equation against seam-crossing modular tests.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section

/-- Pairing an admitted planar chart test with a genuine modular core field
unfolds over the full upper half-plane, with conjugation retained exactly. -/
theorem PlanarChartTest.core_pairing_unfold (g : PlanarChartTest) (f : CoreField) :
    inner ℂ (embedding g.toChartTest.energyTest) (fieldVector f) =
      ∫ z : UpperHalfPlane, conj (g.field z)*f.field z := by
  rw [g.toChartTest.scalar_pairing]
  have he : (∫ z : UpperHalfPlane, conj (periodize g.toChartTest.field z)*(fieldVector f) z ∂measure) =
      ∫ z : UpperHalfPlane, conj (periodize g.toChartTest.field z)*f.field z ∂measure := by
    apply integral_congr_ae
    filter_upwards [(core_field_memLp f.field f.smooth f.compact).coeFn_toLp] with z hz
    change (fieldVector f) z = f.field z at hz
    rw [hz]
  rw [he]
  have hu : LocallyIntegrable f.field (volume : Measure UpperHalfPlane) :=
    (ChartSmooth.continuous f.smooth).locallyIntegrable
  simpa only [periodize,Complex.conj_tsum,PlanarChartTest.toChartTest,CompactChartTest.ofPlanar,
    PlanarChartTest.conjugate] using
    compact_test_modular_pairing_unfold g.conjugate.toChartTest f.field hu f.invariant

private theorem core_gradient_coe (f : CoreField) (i : Fin 2) :
    ((frameGraph f) i.succ : UpperHalfPlane → ℂ) =ᵐ[measure] weightedDeriv (direction i) f.field := by
  have he : frameGraph f i.succ = derivativeVector f (direction i) := by fin_cases i <;> rfl
  rw [he]
  exact (weightedDeriv_memLp _ f.field f.smooth f.compact).coeFn_toLp

/-- Both Hilbert gradient pairings are the literal full modular Dirichlet integral. -/
theorem CompactChartTest.core_gradient_pairing (g : CompactChartTest) (f : CoreField) :
    (∑ i : Fin 2, inner ℂ ((g.energyTest : EnergySpace) i.succ) ((frameGraph f) i.succ)) =
      ∫ z : UpperHalfPlane, frameEnergy (periodize g.field) f.field z ∂measure := by
  have hp (i : Fin 2) :
      inner ℂ ((g.energyTest : EnergySpace) i.succ) ((frameGraph f) i.succ) =
        ∫ z : UpperHalfPlane, conj (weightedDeriv (direction i) (periodize g.field) z)*
          weightedDeriv (direction i) f.field z ∂measure := by
    rw [g.gradient_pairing ⟨frameGraph f,frameGraph_mem f⟩ i]
    apply integral_congr_ae
    filter_upwards [core_gradient_coe f i] with z hz
    rw [hz]
  have hi (i : Fin 2) : Integrable (fun z : UpperHalfPlane =>
      conj (weightedDeriv (direction i) (periodize g.field) z)*weightedDeriv (direction i) f.field z)
      measure := by
    apply (L2.integrable_inner (𝕜 := ℂ) ((g.energyTest : EnergySpace) i.succ)
      ((frameGraph f) i.succ)).congr
    filter_upwards [g.energyTest_gradient i,core_gradient_coe f i] with z hg hf
    rw [hg,hf]
    simp [RCLike.inner_apply,mul_comm]
  simp_rw [hp]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  rfl

/-- The Laplacian test is an actual scalar vector in the original Hilbert space. -/
def PlanarChartTest.laplaceVector (g : PlanarChartTest) : Space :=
  embedding g.laplaceTest.toChartTest.energyTest

private theorem PlanarChartTest.core_green (g : PlanarChartTest) (f : CoreField) :
    (∑ i : Fin 2, inner ℂ ((g.toChartTest.energyTest : EnergySpace) i.succ) ((frameGraph f) i.succ)) =
      -inner ℂ g.laplaceVector (fieldVector f) := by
  rw [g.toChartTest.core_gradient_pairing,
    frameEnergy_periodize_integral g.toChartTest f.field f.smooth f.invariant,
    g.full_green f.field f.smooth]
  rw [PlanarChartTest.laplaceVector,g.laplaceTest.core_pairing_unfold]

/-- Continuous global Green constraint for tests that may cross modular seams. -/
def PlanarChartTest.greenConstraint (g : PlanarChartTest) : EnergySpace →L[ℂ] ℂ :=
  (∑ i : Fin 2, (innerSL ℂ ((g.toChartTest.energyTest : EnergySpace) i.succ)).comp
    (PiLp.proj 2 (fun _ : Fin 3 => Space) i.succ)) +
  (innerSL ℂ g.laplaceVector).comp (PiLp.proj 2 (fun _ : Fin 3 => Space) 0)

private theorem PlanarChartTest.greenConstraint_apply (g : PlanarChartTest) (x : EnergySpace) :
    g.greenConstraint x =
      (∑ i : Fin 2, inner ℂ ((g.toChartTest.energyTest : EnergySpace) i.succ) (x i.succ)) +
        inner ℂ g.laplaceVector (x 0) := by
  simp [PlanarChartTest.greenConstraint,PiLp.proj,innerSL_apply_apply]

/-- Global Green integration by parts survives the full original graph completion.
The response requires no smooth representative and no seam-trace premise. -/
theorem PlanarChartTest.completed_green (g : PlanarChartTest) (h : energyDomain) :
    (∑ i : Fin 2, inner ℂ ((g.toChartTest.energyTest : EnergySpace) i.succ) ((h : EnergySpace) i.succ)) =
      -inner ℂ g.laplaceVector (embedding h) := by
  have hsub : energyDomain ≤ g.greenConstraint.toLinearMap.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨f,rfl⟩
      change g.greenConstraint (frameGraph f) = 0
      rw [g.greenConstraint_apply,g.core_green]
      exact neg_add_cancel _
    · exact g.greenConstraint.isClosed_ker
  have he := hsub h.property
  change g.greenConstraint h = 0 at he
  rw [g.greenConstraint_apply] at he
  exact eq_neg_iff_add_eq_zero.mpr he

/-- The actual full-forcing Xi response satisfies the second-order modular
distribution equation against every compact positive-height planar chart test,
including tests crossing side identifications and elliptic stabilizer charts. -/
theorem full_response_global_distribution_equation (q : XiZeroCopy) (minusBranch : Bool)
    (g : PlanarChartTest) :
    inner ℂ g.laplaceVector (embedding (weakResponse q minusBranch)) -
      parameter q minusBranch*inner ℂ (embedding g.toChartTest.energyTest)
        (embedding (weakResponse q minusBranch)) =
      inner ℂ (embedding g.toChartTest.energyTest) (forcingVector q minusBranch) := by
  have he := (weakSolution_iff_gradient q minusBranch _).mp
    (weakResponse_spec q minusBranch) g.toChartTest.energyTest
  rw [g.completed_green] at he
  linear_combination -he

/-- Literal seam-crossing distributional identity for the constructed response.
All derivatives act on the actual compact test; the original forcing is retained. -/
theorem full_response_global_integral_equation (q : XiZeroCopy) (minusBranch : Bool)
    (g : PlanarChartTest) :
    (∫ z : UpperHalfPlane, conj (periodize g.laplaceTest.toChartTest.field z)*
      embedding (weakResponse q minusBranch) z ∂measure) -
    parameter q minusBranch*(∫ z : UpperHalfPlane, conj (periodize g.toChartTest.field z)*
      embedding (weakResponse q minusBranch) z ∂measure) =
    ∫ z : UpperHalfPlane, conj (periodize g.toChartTest.field z)*
      forcing q minusBranch (coordinates z) ∂measure := by
  have he := full_response_global_distribution_equation q minusBranch g
  rw [PlanarChartTest.laplaceVector,g.laplaceTest.toChartTest.scalar_pairing,
    g.toChartTest.scalar_pairing,g.toChartTest.scalar_pairing] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [forcingVector_coe q minusBranch] with z hz
  rw [hz]

end
end RHTower.D4BMModularCore
