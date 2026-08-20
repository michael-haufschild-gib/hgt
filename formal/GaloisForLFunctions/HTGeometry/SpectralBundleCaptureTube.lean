/-
# The capture tube of a spectral phase bundle

The capture event of a phase orbit is a set on the phase torus that depends on the Hamiltonian
through its eigenbasis.  Read as a subset of the *bundle* -- parameter times torus -- it is the
superlevel set of the phase pairing of the gauge-invariant cross-weights, so it is closed over any
compact set of parameters on which those weights are continuous.  Its fibres are exactly the
relative-phase capture events of the parent incidence law, so the fibrewise replica-moment bound
applies verbatim.

Main results:
* `bundlePairing` — the phase pairing `∑_j conj(e^{2πi y_j}) w_j` of a weight vector.
* `finiteComplexInner_torusAmpOrbit` — **the orbit pairing is the pairing of the cross-weights**.
* `projectiveBundleTube` — the capture tube in the relative-phase bundle.
* `preimage_projectiveBundleTube` — **its fibres are the parent card's capture events**.
* `isCompact_projectiveBundleTube_inter`, `isClosed_projectiveBundleTube_inter` —
  **the tube is closed over every compact set of continuity**.
-/
import GaloisForLFunctions.HTGeometry.LagrangeSpectralProjector
import GaloisForLFunctions.HTGeometry.SpectralOrbitCaptureDensity

open MeasureTheory Complex UnitAddTorus Set Filter Topology ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {C : Type*} [Fintype C]

/-! ## The phase pairing of a gauge-invariant weight vector -/

/-- The phase pairing `∑_j conj(e^{2πi y_j}) w_j`. -/
def bundlePairing (w : I → ℂ) (y : UnitAddTorus I) : ℂ :=
  ∑ j, conj (UnitAddTorus.mFourier (Pi.single j 1) y) * w j

/-- **The orbit pairing is the phase pairing of the cross-weights.**  Each eigenvector phase enters
`c j` and `v j` with opposite signs, so it cancels in the product `conj (c j) * v j`. -/
theorem finiteComplexInner_torusAmpOrbit (c v : I → ℂ) (y : UnitAddTorus I) :
    finiteComplexInner (torusAmpOrbit c y) v
      = bundlePairing (fun j => conj (c j) * v j) y := by
  simp only [finiteComplexInner, torusAmpOrbit, bundlePairing, map_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem continuous_bundlePairing_torus (w : I → ℂ) :
    Continuous (fun y : UnitAddTorus I => bundlePairing w y) := by
  refine continuous_finsetSum _ fun j _ => ?_
  exact (Complex.continuous_conj.comp
    (UnitAddTorus.mFourier (Pi.single j 1)).continuous).mul continuous_const

/-! ## The capture tube of a bundle of weight vectors -/

variable {X : Type*} [TopologicalSpace X]

/-- The capture tube in the relative-phase bundle over a parameter space. -/
def projectiveBundleTube (i₀ : I) (w : X → C → I → ℂ) (a : ℝ) :
    Set (X × UnitAddTorus {i : I // i ≠ i₀}) :=
  {q | ∃ κ : C, a ≤ ‖bundlePairing (w q.1 κ) (torusSection i₀ q.2)‖ ^ 2}

/-- **The fibres of the tube are the parent card's relative-phase capture events.** -/
theorem preimage_projectiveBundleTube (i₀ : I) (a : ℝ) (c : X → I → ℂ) (z : X → C → I → ℂ)
    (x : X) :
    Prod.mk x ⁻¹'
        projectiveBundleTube i₀ (fun x' κ j => conj (c x' j) * z x' κ j) a
      = projectiveAmpCaptureTarget i₀ (c x) a (z x) := by
  ext y
  simp only [Set.mem_preimage, projectiveBundleTube, Set.mem_setOf_eq,
    projectiveAmpCaptureTarget, projectiveSpectralOrbit, finitePureStateFidelity]
  constructor
  · rintro ⟨κ, hκ⟩
    exact ⟨κ, by rwa [finiteComplexInner_torusAmpOrbit]⟩
  · rintro ⟨κ, hκ⟩
    exact ⟨κ, by rwa [finiteComplexInner_torusAmpOrbit] at hκ⟩

theorem continuousOn_bundlePairing_prod {K : Set X} {i₀ : I} {v : X → I → ℂ}
    (hv : ∀ j, ContinuousOn (fun x => v x j) K) :
    ContinuousOn
      (fun q : X × UnitAddTorus {i : I // i ≠ i₀} =>
        bundlePairing (v q.1) (torusSection i₀ q.2)) (K ×ˢ (Set.univ : Set _)) := by
  refine continuousOn_finsetSum _ fun j _ => ?_
  refine ContinuousOn.mul ?_ ?_
  · exact ((Complex.continuous_conj.comp
      ((UnitAddTorus.mFourier (Pi.single j 1)).continuous.comp
        (continuous_torusSection i₀))).comp continuous_snd).continuousOn
  · exact (hv j).comp continuousOn_fst fun q hq => hq.1

/-- A compact parameter set of continuity carries a compact tube slice. -/
theorem isCompact_inter_preimage_of_continuousOn {Y : Type*} [TopologicalSpace Y]
    {s : Set X} (hs : IsCompact s) {f : X → Y} (hf : ContinuousOn f s) {F : Set Y}
    (hF : IsClosed F) : IsCompact (s ∩ f ⁻¹' F) := by
  have hcomp : IsCompact (Set.univ : Set ↥s) := isCompact_iff_isCompact_univ.mp hs
  have hcl : IsClosed ((s.restrict f) ⁻¹' F) :=
    hF.preimage (continuousOn_iff_continuous_restrict.mp hf)
  have hc2 : IsCompact ((s.restrict f) ⁻¹' F) :=
    hcomp.of_isClosed_subset hcl (Set.subset_univ _)
  have himg := hc2.image continuous_subtype_val
  have hset : Subtype.val '' ((s.restrict f) ⁻¹' F) = s ∩ f ⁻¹' F := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hmem, rfl⟩
      exact ⟨hy, hmem⟩
    · rintro ⟨hx, hmem⟩
      exact ⟨⟨x, hx⟩, hmem, rfl⟩
  rwa [hset] at himg

/-- **The capture tube is compact over every compact parameter set of continuity.** -/
theorem isCompact_projectiveBundleTube_inter {K : Set X} (hK : IsCompact K)
    {i₀ : I} {w : X → C → I → ℂ} (hw : ∀ κ j, ContinuousOn (fun x => w x κ j) K) (a : ℝ) :
    IsCompact (projectiveBundleTube i₀ w a ∩ (K ×ˢ (Set.univ : Set _))) := by
  classical
  have hprod : IsCompact (K ×ˢ (Set.univ : Set (UnitAddTorus {i : I // i ≠ i₀}))) :=
    hK.prod isCompact_univ
  have hunion : projectiveBundleTube i₀ w a ∩ (K ×ˢ (Set.univ : Set _))
      = ⋃ κ : C, ((K ×ˢ (Set.univ : Set (UnitAddTorus {i : I // i ≠ i₀}))) ∩
          (fun q : X × UnitAddTorus {i : I // i ≠ i₀} =>
            ‖bundlePairing (w q.1 κ) (torusSection i₀ q.2)‖ ^ 2) ⁻¹' (Set.Ici a)) := by
    ext q
    simp only [projectiveBundleTube, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_preimage, Set.mem_Ici]
    constructor
    · rintro ⟨⟨κ, hκ⟩, hq⟩
      exact ⟨κ, hq, hκ⟩
    · rintro ⟨κ, hq, hκ⟩
      exact ⟨⟨κ, hκ⟩, hq⟩
  rw [hunion]
  refine isCompact_iUnion fun κ => ?_
  refine isCompact_inter_preimage_of_continuousOn hprod ?_ isClosed_Ici
  exact ((continuousOn_bundlePairing_prod (i₀ := i₀) (v := fun x => w x κ)
    fun j => hw κ j).norm).pow 2

/-- **The capture tube is closed over every compact parameter set of continuity.** -/
theorem isClosed_projectiveBundleTube_inter {K : Set X} (hK : IsCompact K)
    {i₀ : I} {w : X → C → I → ℂ} (hw : ∀ κ j, ContinuousOn (fun x => w x κ j) K) (a : ℝ)
    [T2Space X] :
    IsClosed (projectiveBundleTube i₀ w a ∩ (K ×ˢ (Set.univ : Set _))) :=
  (isCompact_projectiveBundleTube_inter hK hw a).isClosed

end GaloisForLFunctions.HTGeometry

end
