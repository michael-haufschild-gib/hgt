import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PoissonBoundariesAreDenseInOriginMass
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerFiniteXiJetPacket

/-!
# Full finite-jet graph closure in origin Hilbert space

Every actual cohomological fibre is dense in the origin Hilbert coordinate.
Consequently a surjective cohomological reading has full product graph closure.
For finite Xi packets this includes every lower jet, regardless of criticality
or multiplicity, and prevents a single-valued closed graph on any nonempty packet.
-/

noncomputable section
open Complex MeasureTheory Set RHTower
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- A cohomological reading with dense image has dense joint graph with the half-density coordinate. -/
theorem meyerOrigin_joint_degree_dense_of_denseRange
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (E : DeningerMeyerStrongLogCohomology →ₗ[ℂ] Y) (hE : DenseRange E) :
    DenseRange (fun g : DeningerMeyerStrongLogTarget =>
      (deningerMeyerHalfDensityL2LM g, E (Submodule.Quotient.mk g))) := by
  intro p
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨v, ⟨u, rfl⟩, hu⟩ := Metric.mem_closure_iff.mp (hE p.2) ε hε
  obtain ⟨g, hg⟩ := (LinearMap.range deningerMeyerStrongLogSumLM).mkQ_surjective u
  have hgE : E (Submodule.Quotient.mk g) = E u := by
    change E ((LinearMap.range deningerMeyerStrongLogSumLM).mkQ g) = E u
    rw [hg]
  obtain ⟨v, ⟨f, rfl⟩, hf⟩ := Metric.mem_closure_iff.mp
    (meyerPoissonBoundary_halfDensity_dense (p.1 - deningerMeyerHalfDensityL2LM g)) ε hε
  let h := g + deningerMeyerStrongLogSumLM f
  have hclass : (Submodule.Quotient.mk h : DeningerMeyerStrongLogCohomology) =
      Submodule.Quotient.mk g := by
    change (LinearMap.range deningerMeyerStrongLogSumLM).mkQ
      (g + deningerMeyerStrongLogSumLM f) = _
    rw [map_add, show (LinearMap.range deningerMeyerStrongLogSumLM).mkQ
        (deningerMeyerStrongLogSumLM f) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨f, rfl⟩, add_zero]
    rfl
  refine ⟨(deningerMeyerHalfDensityL2LM h, E (Submodule.Quotient.mk h)), ⟨h, rfl⟩, ?_⟩
  rw [Prod.dist_eq, hclass, hgE]
  apply max_lt_iff.mpr
  refine ⟨?_, hu⟩
  change dist p.1 (deningerMeyerHalfDensityL2LM (g + deningerMeyerStrongLogSumLM f)) < ε
  rw [map_add, dist_eq_norm]
  simpa only [dist_eq_norm, sub_add_eq_sub_sub] using hf

/-- Every surjective cohomological reading has dense joint graph with the half-density coordinate. -/
theorem meyerOrigin_joint_degree_dense
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (E : DeningerMeyerStrongLogCohomology →ₗ[ℂ] Y) (hE : Function.Surjective E) :
    DenseRange (fun g : DeningerMeyerStrongLogTarget =>
      (deningerMeyerHalfDensityL2LM g, E (Submodule.Quotient.mk g))) := by
  apply meyerOrigin_joint_degree_dense_of_denseRange E
  intro y
  obtain ⟨u, rfl⟩ := hE y
  exact subset_closure ⟨u, rfl⟩

/-- The full algebraic source graph of a selected finite Xi-jet packet. -/
def meyerFiniteJetOriginGraph (S : Finset XiDivisorSupport) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ) × DeningerMeyerFiniteXiJetPacket S) :=
  LinearMap.range (deningerMeyerHalfDensityL2LM.prod
    ((deningerMeyerFiniteXiJetPacketLM S).comp
      (LinearMap.range deningerMeyerStrongLogSumLM).mkQ))

/-- Every selected full-jet packet has the whole product as its origin-Hilbert graph closure. -/
theorem meyerFiniteJetOriginGraph_closure_eq_top (S : Finset XiDivisorSupport) :
    (meyerFiniteJetOriginGraph S).topologicalClosure = ⊤ := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mp
  exact meyerOrigin_joint_degree_dense (deningerMeyerFiniteXiJetPacketLM S)
    (deningerMeyerFiniteXiJetPacketLM_surjective S)

/-- Every finite jet output lies over zero in the closed origin-Hilbert graph. -/
theorem meyerFiniteJetOriginGraph_full_vertical (S : Finset XiDivisorSupport)
    (y : DeningerMeyerFiniteXiJetPacket S) :
    ((0 : Lp ℂ 2 (volume : Measure ℝ)), y) ∈ (meyerFiniteJetOriginGraph S).topologicalClosure := by
  rw [meyerFiniteJetOriginGraph_closure_eq_top]
  exact Submodule.mem_top

/-- A closed relation retaining the actual finite-jet graph must be the whole product. -/
theorem meyerFiniteJetOriginGraph_closed_relation_eq_top (S : Finset XiDivisorSupport)
    (R : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ) × DeningerMeyerFiniteXiJetPacket S))
    (hR : IsClosed (R : Set (Lp ℂ 2 (volume : Measure ℝ) × DeningerMeyerFiniteXiJetPacket S)))
    (hg : meyerFiniteJetOriginGraph S ≤ R) : R = ⊤ := by
  have hc := Submodule.topologicalClosure_minimal _ hg hR
  rw [meyerFiniteJetOriginGraph_closure_eq_top] at hc
  exact top_unique hc

/-- The closed origin-Hilbert jet graph is single-valued precisely for the empty packet. -/
theorem meyerFiniteJetOriginGraph_singleValuedClosure_iff_empty (S : Finset XiDivisorSupport) :
    (∀ y : DeningerMeyerFiniteXiJetPacket S,
      ((0 : Lp ℂ 2 (volume : Measure ℝ)), y) ∈
        (meyerFiniteJetOriginGraph S).topologicalClosure → y = 0) ↔ S = ∅ := by
  classical
  constructor
  · intro hsingle
    by_contra hS
    obtain ⟨rho, hr⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    let q : DeningerMeyerFiniteXiJetSlot S :=
      ⟨⟨rho, hr⟩, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
    have hy := hsingle (Pi.single q 1) (meyerFiniteJetOriginGraph_full_vertical S (Pi.single q 1))
    have hbad : (1 : ℂ) = 0 := by simpa using congrFun hy q
    exact one_ne_zero hbad
  · rintro rfl y _
    funext q
    exact False.elim (Finset.notMem_empty q.1.1 q.1.2)

/-- No nonempty actual finite-jet graph has a single-valued closed extension in origin Hilbert space. -/
theorem meyerFiniteJetOriginGraph_no_closed_singleValued_extension
    (S : Finset XiDivisorSupport) (hS : S.Nonempty) :
    ¬ ∃ R : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ) × DeningerMeyerFiniteXiJetPacket S),
      IsClosed (R : Set (Lp ℂ 2 (volume : Measure ℝ) × DeningerMeyerFiniteXiJetPacket S)) ∧
        meyerFiniteJetOriginGraph S ≤ R ∧
        ∀ y, ((0 : Lp ℂ 2 (volume : Measure ℝ)), y) ∈ R → y = 0 := by
  rintro ⟨R, hR, hg, hsingle⟩
  have hc := Submodule.topologicalClosure_minimal _ hg hR
  have he := (meyerFiniteJetOriginGraph_singleValuedClosure_iff_empty S).mp
    (fun y hy => hsingle y (hc hy))
  exact hS.ne_empty he

/-- The full faithful operator reading also has dense joint graph in its actual normed range. -/
theorem meyerOrigin_joint_operator_dense :
    DenseRange (fun g : DeningerMeyerStrongLogTarget =>
      (deningerMeyerHalfDensityL2LM g,
        deningerMeyerConvolutionRepresentationLM.rangeRestrict (Submodule.Quotient.mk g))) :=
  meyerOrigin_joint_degree_dense
    (Y := LinearMap.range deningerMeyerConvolutionRepresentationLM)
    deningerMeyerConvolutionRepresentationLM.rangeRestrict
    deningerMeyerConvolutionRepresentationLM.surjective_rangeRestrict

/-- The actual convolution graph, with the operator norm on its genuine image. -/
def meyerOperatorOriginGraph :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ) ×
      LinearMap.range deningerMeyerConvolutionRepresentationLM) :=
  LinearMap.range (deningerMeyerHalfDensityL2LM.prod
    (deningerMeyerConvolutionRepresentationLM.rangeRestrict.comp
      (LinearMap.range deningerMeyerStrongLogSumLM).mkQ))

/-- Even the whole faithful operator graph has full product closure in the origin completion. -/
theorem meyerOperatorOriginGraph_closure_eq_top :
    meyerOperatorOriginGraph.topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp meyerOrigin_joint_operator_dense

/-- Every nonprincipal source supplies a nonzero vertical operator in the closed graph. -/
theorem meyerOperatorOriginGraph_nonzero_vertical
    (g : DeningerMeyerStrongLogTarget)
    (hg : g ∉ LinearMap.range deningerMeyerStrongLogSumLM) :
    ∃ y : LinearMap.range deningerMeyerConvolutionRepresentationLM,
      y ≠ 0 ∧ ((0 : Lp ℂ 2 (volume : Measure ℝ)), y) ∈
        meyerOperatorOriginGraph.topologicalClosure := by
  let y := deningerMeyerConvolutionRepresentationLM.rangeRestrict (Submodule.Quotient.mk g)
  refine ⟨y, ?_, ?_⟩
  · intro hy
    have hz : deningerMeyerHilbertConvolution g = 0 := congrArg Subtype.val hy
    exact hg ((deningerMeyerHilbertConvolution_eq_zero_iff g).mp hz)
  · rw [meyerOperatorOriginGraph_closure_eq_top]
    exact Submodule.mem_top

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
