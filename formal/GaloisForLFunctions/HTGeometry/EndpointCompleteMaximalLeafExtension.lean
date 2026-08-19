/-
# Endpoint completeness and maximal projective rank at one physical leaf parameter

Endpoint completeness is open on a simple eigenbranch chart.  Maximal projective spectral rank is
dense in the real Hermitian onsite-plus-edge slice.  The anchor-star perturbation supplies a real
point of that slice at which every ordered pair of chart eigenvectors is visible from the new
endpoint.  Hence one real physical parameter has both properties simultaneously.

Main result:
* `exists_maximallyProjective_endpointComplete_realLeafParameter` -- the common physical witness.
-/
import GaloisForLFunctions.HTGeometry.ChartEndpointGenericIntersection
import GaloisForLFunctions.HTGeometry.ParityCompleteLocalExtensionRelationEscape
import GaloisForLFunctions.HTGeometry.AllVertexGoodLeafExtensionOpen
import GaloisForLFunctions.HTGeometry.CompleteObserverSpectralSeed
import GaloisForLFunctions.HTGeometry.LayerSplitEndpointStep
import GaloisForLFunctions.HTGeometry.UnitaryChartProbeFamilyReduction

open Filter Set Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real split field whose complexification is `boolShift`. -/
def realBoolShift (z : ℝ) : Bool → ℝ :=
  fun b => if b then -(z / 2) else z / 2

theorem realBoolShift_complexification (z : ℝ) :
    (fun b => ((realBoolShift z b : ℝ) : ℂ)) = boolShift (z : ℂ) := by
  funext b
  cases b <;> simp [realBoolShift, boolShift]

/-- A Hermitian matrix with every off-diagonal entry nonzero has complete transition support. -/
theorem transitionSupportGraph_eq_top_of_offDiag_ne_zero
    {A : Type*} {M : Matrix A A ℂ}
    (hM : ∀ a b : A, a ≠ b → M a b ≠ 0) :
    transitionSupportGraph M = (⊤ : SimpleGraph A) := by
  ext a b
  constructor
  · intro hab
    simpa using hab.1
  · intro hab
    have hne : a ≠ b := by simpa using hab
    exact ⟨hne, mul_ne_zero (hM a b hne) (hM b a hne.symm)⟩

/-- A probe on the newly attached factor has exactly the endpoint pairing as its chart matrix
entry. -/
theorem LocalExtensionEigenbranchChart.probeMatrix_newEndpoint_eq_pairing
    {A : Type*} [Fintype A] [DecidableEq A]
    (energy : A → ℂ) (shift : Bool → ℂ) (M : Matrix A A ℂ)
    (C : LocalExtensionEigenbranchChart energy shift M)
    (p : (Bool → ℂ) × Matrix Bool Bool ℂ)
    (X : Matrix Bool Bool ℂ) (x y : A × Bool) :
    C.probeMatrix energy shift M
        (layerMatrixCoupling (1 : Matrix A A ℂ) X) p x y =
      endpointPairing
        (C.adjugateColumn energy shift M x p ∘ Prod.swap)
        (endpointProbeAction X
          (C.adjugateColumn energy shift M y p ∘ Prod.swap)) := by
  classical
  simp only [LocalExtensionEigenbranchChart.probeMatrix,
    LocalExtensionEigenbranchChart.sesquilinearProbe,
    endpointPairing, endpointProbeAction, Function.comp_apply,
    layerMatrixCoupling, Matrix.one_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul]
  simp only [Prod.swap_prod_mk]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp only [if_pos, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [mul_assoc]
    rw [starRingEnd_apply]
  · intro b _ hba
    have hab : a ≠ b := Ne.symm hba
    simp [hab]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

/-- **Common maximal-rank endpoint-complete physical leaf parameter.**  Start with a maximally
projective real spectrum on at least three states and a Hermitian endpoint channel seeing every
ordered pair.  One real onsite-plus-edge parameter of the attached qubit then has maximally
projective canonical spectrum and canonical chart eigenvectors that are again pairwise visible
from the new endpoint.  Both conclusions concern the same Hermitian Hamiltonian. -/
theorem exists_maximallyProjective_endpointComplete_realLeafParameter
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (hcard : 3 ≤ Fintype.card A)
    (energy : A → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (M : Matrix A A ℂ) (hMherm : M.IsHermitian)
    (hM : ∀ a b : A, a ≠ b → M a b ≠ 0) :
    ∃ z : ℝ,
      ∃ C : LocalExtensionEigenbranchChart
          (fun a => (energy a : ℂ)) (boolShift (z : ℂ)) M,
        ∃ q : Fin (localExtensionSliceParameterCount Bool) → ℝ,
          let p := realLocalExtensionParameter (localExtensionSliceParameter q)
          p ∈ C.U ∧
            MaximallyProjectiveEnergy
              (hermitianLocalExtensionSliceMatrix_isHermitian
                (α := A) (ρ := Bool) energy M hMherm q).eigenvalues ∧
            ∀ pair : (A × Bool) × (A × Bool), pair.1 ≠ pair.2 →
              layerReducedTransition
                (C.adjugateColumn (fun a => (energy a : ℂ))
                  (boolShift (z : ℂ)) M pair.1 p)
                (C.adjugateColumn (fun a => (energy a : ℂ))
                  (boolShift (z : ℂ)) M pair.2 p) ≠ 0 := by
  classical
  obtain ⟨z, hz⟩ := exists_real_admissible_split_shift energy
  have henergyC : Function.Injective (fun a => (energy a : ℂ)) := by
    intro a b hab
    exact hmax.injective (Complex.ofReal_injective hab)
  have hsplit : Function.Injective
      (layeredEnergy (fun a => (energy a : ℂ)) (boolShift (z : ℂ))) := by
    rw [layeredEnergy_boolShift]
    exact injective_layerSplitEnergy henergyC hz
  obtain ⟨C⟩ := exists_localExtensionEigenbranchChart
    (fun a => (energy a : ℂ)) (boolShift (z : ℂ)) M hsplit

  have hcoe : Tendsto (fun t : ℝ => ((t : ℝ) : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hzero : Tendsto (fun t : ℝ => ((t : ℝ) : ℂ))
        (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ))
    exact hzero.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ((boolShift (z : ℂ), ((t : ℝ) : ℂ) • anchorStarLayerEdge false) :
        (Bool → ℂ) × Matrix Bool Bool ℂ) ∈ C.U :=
    hcoe.eventually
      (C.eventually_anchorStar_mem
        (fun a => (energy a : ℂ)) (boolShift (z : ℂ)) M false)
  obtain ⟨t, hcomplete, htU⟩ :=
    ((eventually_forall_chartAdjugate_endpoint_ne_zero
      (E := fun a => (energy a : ℂ)) (z := (z : ℂ)) hsplit
      (fun a b hab => hM b a hab.symm) C).and hmem).exists

  let p₀R : (Bool → ℝ) × Matrix Bool Bool ℝ :=
    (realBoolShift z, t • realAnchorStarLayerEdge false)
  let q₀ : Fin (localExtensionSliceParameterCount Bool) → ℝ :=
    localExtensionSliceCoordinates p₀R
  let physicalParameter :
      (Fin (localExtensionSliceParameterCount Bool) → ℝ) →
        (Bool → ℂ) × Matrix Bool Bool ℂ :=
    realLocalExtensionParameter ∘ localExtensionSliceParameter
  have hq₀decode : localExtensionSliceParameter q₀ = p₀R := by
    exact localExtensionSliceParameter_coordinates p₀R
  have hp₀ : physicalParameter q₀ =
      (boolShift (z : ℂ), (t : ℂ) • anchorStarLayerEdge false) := by
    simp only [physicalParameter, Function.comp_apply, hq₀decode, p₀R]
    rw [realLocalExtensionParameter_realAnchorStarLayerEdge]
    simp only [realBoolShift_complexification]

  have hsupport : transitionSupportGraph M = (⊤ : SimpleGraph A) :=
    transitionSupportGraph_eq_top_of_offDiag_ne_zero hM
  have hconnected : (transitionSupportGraph M).Preconnected := by
    rw [hsupport]
    exact SimpleGraph.preconnected_top
  have hnonbipartite : ¬ (transitionSupportGraph M).IsBipartite := by
    rw [hsupport]
    exact completeGraph_not_isBipartite_of_three_le_card hcard
  obtain ⟨_rankWitness, _hrankWitnessMax, hdense, _hresidual, _hnull⟩ :=
    hermitianLocalExtensionSliceMaximalSet_dense_residual_fullMeasure_of_goodSupport
      energy hmax (realBoolShift z) M hMherm
      (by simpa only [realBoolShift_complexification] using hsplit)
      (by norm_num : 2 ≤ Fintype.card Bool) hconnected hnonbipartite

  have hphysicalContinuousAt : ContinuousAt physicalParameter q₀ := by
    have hcomp :=
      (realLocalExtensionParameter_continuous (ρ := Bool)).comp
        (localExtensionSliceParameter_continuous (ρ := Bool))
    simpa only [physicalParameter] using hcomp.continuousAt
  let psi : (A × Bool) →
      (Fin (localExtensionSliceParameterCount Bool) → ℝ) →
        (A × Bool → ℂ) :=
    fun i r => C.adjugateColumn (fun a => (energy a : ℂ))
      (boolShift (z : ℂ)) M i (physicalParameter r)
  have hpsiContinuous : ∀ i y, ContinuousAt (fun r => psi i r y) q₀ := by
    intro i y
    have hanalytic := C.adjugateColumn_analyticAt
      (fun a => (energy a : ℂ)) (boolShift (z : ℂ)) M i
      (physicalParameter q₀) (by simpa [hp₀] using htU) y
    exact hanalytic.continuousAt.comp hphysicalContinuousAt
  have hcomplete₀ : ∀ pair : (A × Bool) × (A × Bool), pair.1 ≠ pair.2 →
      layerReducedTransition (psi pair.1 q₀) (psi pair.2 q₀) ≠ 0 := by
    intro pair hpair
    simpa [psi, hp₀] using hcomplete pair hpair
  have hendpointEvent : ∀ᶠ r in 𝓝 q₀,
      ∀ pair : (A × Bool) × (A × Bool), pair.1 ≠ pair.2 →
        layerReducedTransition (psi pair.1 r) (psi pair.2 r) ≠ 0 :=
    eventually_forall_layerReducedTransition_ne_zero
      psi hpsiContinuous hcomplete₀
  have hchartEvent : ∀ᶠ r in 𝓝 q₀, physicalParameter r ∈ C.U := by
    have htend : Tendsto physicalParameter (𝓝 q₀)
        (𝓝 (physicalParameter q₀)) := hphysicalContinuousAt
    exact htend.eventually
      (C.isOpen_U.mem_nhds (by simpa [hp₀] using htU))
  obtain ⟨V, hVsub, hVopen, hq₀V⟩ :=
    mem_nhds_iff.mp (hchartEvent.and hendpointEvent)
  obtain ⟨q, hqMax, hqV⟩ :=
    hdense.exists_mem_open hVopen ⟨q₀, hq₀V⟩
  have hq := hVsub hqV
  refine ⟨z, C, q, hq.1, hqMax, ?_⟩
  intro pair hpair
  exact hq.2 pair hpair

/-- **Exact orthonormal endpoint channel at the common witness.**  The common parameter above
admits a Hermitian one-qubit endpoint probe whose matrix in the relabelled canonical orthonormal
eigenbasis has no vanishing off-diagonal entry. -/
theorem exists_maximallyProjective_unitaryEndpointComplete_realLeafParameter
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (hcard : 3 ≤ Fintype.card A)
    (energy : A → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (M : Matrix A A ℂ) (hMherm : M.IsHermitian)
    (hM : ∀ a b : A, a ≠ b → M a b ≠ 0) :
    ∃ z : ℝ,
      ∃ C : LocalExtensionEigenbranchChart
          (fun a => (energy a : ℂ)) (boolShift (z : ℂ)) M,
        ∃ q : Fin (localExtensionSliceParameterCount Bool) → ℝ,
          let p := realLocalExtensionParameter (localExtensionSliceParameter q)
          ∃ hH : (localExtensionMatrix (fun a => (energy a : ℂ))
              p.1 M p.2).IsHermitian,
            ∃ e : (A × Bool) ≃ (A × Bool),
              ∃ X : Matrix Bool Bool ℂ,
                p ∈ C.U ∧
                MaximallyProjectiveEnergy hH.eigenvalues ∧
                (∀ i, C.realBranchEnergy (fun a => (energy a : ℂ))
                  (boolShift (z : ℂ)) M p i = hH.eigenvalues (e i)) ∧
                X.IsHermitian ∧
                ∀ x y : A × Bool, x ≠ y →
                  C.unitaryProbeMatrix hH e
                    (layerMatrixCoupling (1 : Matrix A A ℂ) X) x y ≠ 0 := by
  classical
  obtain ⟨z, C, q, hp, hmaxNext, hcomplete⟩ :=
    exists_maximallyProjective_endpointComplete_realLeafParameter
      hcard energy hmax M hMherm hM
  let p := realLocalExtensionParameter (localExtensionSliceParameter q)
  let hH : (localExtensionMatrix (fun a => (energy a : ℂ)) p.1 M p.2).IsHermitian :=
    localExtensionMatrix_realParameter_isHermitian
      energy M hMherm (localExtensionSliceParameter q)
  obtain ⟨e, he⟩ := C.exists_eigenvalueEquiv
    (fun a => (energy a : ℂ)) (boolShift (z : ℂ)) M p hp hH
  obtain ⟨X, hXherm, hX⟩ :=
    exists_hermitian_covering_endpoint_probe
      (fun i => C.adjugateColumn (fun a => (energy a : ℂ))
        (boolShift (z : ℂ)) M i p ∘ Prod.swap)
      (fun i j hij => by
        rw [← layerReducedTransition_eq_reducedTransition]
        exact hcomplete (i, j) hij)
  refine ⟨z, C, q, hH, e, X, hp, ?_, he, hXherm, ?_⟩
  · exact hmaxNext
  · intro x y hxy
    apply C.probeMatrix_entry_ne_zero_imp_unitary
      (fun a => (energy a : ℂ)) (boolShift (z : ℂ)) M p hp hH e he
    rw [C.probeMatrix_newEndpoint_eq_pairing]
    exact hX x y hxy

end

end GaloisForLFunctions.HTGeometry
