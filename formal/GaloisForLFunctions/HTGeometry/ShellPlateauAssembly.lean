/-
# The fixed-shell plateau bookkeeping

Putting the four inputs together: the easy-circuit tube of a finite target dictionary is the
projective bundle tube of the gauge-invariant cross-weights, so it is closed over every compact
slab of the simple-spectrum locus, its fibres are the relative-phase capture events whose Haar mass
the replica moment bounds, and the angular-phase map carries physical time onto it.  The compact
exhaustion then gives the card's `(20)`.

Main results:
* `sortedEigenBasis` — the orthonormal eigenbasis in the canonical (sorted) labelling.
* `easyTube` — the easy-circuit tube in the angular-phase bundle.
* `anglePhaseMap_preimage_easyTube` — **its physical-time fibres are the capture events**.
* `limsup_sphereLaw_capture_le` — **the `(20)` bookkeeping on a fixed shell**.
-/
import GaloisForLFunctions.HTGeometry.AngularPhaseCompactExhaustion
import GaloisForLFunctions.HTGeometry.EvolvedStateBundlePairing
import GaloisForLFunctions.HTGeometry.ProjectiveCaptureHaarBound
import GaloisForLFunctions.HTGeometry.ShellFamilySimpleSpectrum
import GaloisForLFunctions.HTGeometry.GaussianEnsembleCircuitDensity
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum

open Filter Topology MeasureTheory Metric Matrix ComplexConjugate

attribute [local instance] instMeasureSpaceUnitAddCircle

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option linter.unusedSectionVars false

/-- The two measure-space instances on the unit circle carry the same volume. -/
theorem unitAddCircle_volume_eq :
    (@volume UnitAddCircle instMeasureSpaceUnitAddCircle)
      = (@volume UnitAddCircle (AddCircle.measureSpace 1)) := by
  show AddCircle.haarAddCircle = _
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

/-- Hence so do the two induced instances on the phase torus. -/
theorem torusVolume_eq (I : Type*) [Fintype I] [DecidableEq I] :
    (@volume (UnitAddTorus I)
        (@MeasureSpace.pi I _ (fun _ => UnitAddCircle) (fun _ => instMeasureSpaceUnitAddCircle)))
      = (@volume (UnitAddTorus I)
        (@MeasureSpace.pi I _ (fun _ => UnitAddCircle) (fun _ => AddCircle.measureSpace 1))) := by
  show Measure.pi (fun _ => (@volume UnitAddCircle instMeasureSpaceUnitAddCircle))
    = Measure.pi (fun _ => (@volume UnitAddCircle (AddCircle.measureSpace 1)))
  congr 1
  funext i
  exact unitAddCircle_volume_eq

variable {N D : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
variable {C : Type*} [Fintype C] [Nonempty C]

/-- The orthonormal eigenbasis of the shell Hamiltonian in the canonical (sorted) labelling. -/
def sortedEigenBasis (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) : Fin D → Fin D → ℂ :=
  fun j => hermitianEigenBasis (spectralEnsembleMatrix P θ)
    (isHermitian_spectralEnsembleMatrix hP θ)
    (Tuple.sort (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues j)

theorem isOrthoEigenBasis_sortedEigenBasis (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) :
    IsOrthoEigenBasis (spectralEnsembleMatrix P θ) (sortedEigenBasis hP θ)
      (spectralTuple hP θ) :=
  (isOrthoEigenBasis_hermitian _ (isHermitian_spectralEnsembleMatrix hP θ)).reindex
    (Tuple.sort (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues)

theorem injective_spectralTuple (hP : ∀ a, (P a).IsHermitian) {θ : Fin N → ℝ}
    (hinj : Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues) :
    Function.Injective (spectralTuple hP θ) :=
  hinj.comp (Tuple.sort _).injective

/-- The easy-circuit tube of a finite target dictionary, in the angular-phase bundle. -/
def easyTube (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D) (Ω : Fin D → ℂ)
    (Z : C → (Fin D → ℂ)) (a : ℝ) : Set (coeffSphere N × UnitAddTorus (phaseIndex i₀)) :=
  projectiveBundleTube i₀
    (fun x κ => spectralCrossWeight (spectralTuple hP (sphereCoeff x))
      (spectralEnsembleMatrix P (sphereCoeff x)) (Z κ) Ω) a

/-- **The tube is closed over every compact slab of the simple-spectrum locus.** -/
theorem isClosed_easyTube_inter (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D) (Ω : Fin D → ℂ)
    (Z : C → (Fin D → ℂ)) (a : ℝ) {K : Set (coeffSphere N)} (hK : IsCompact K)
    (hKsimple : ∀ x ∈ K,
      Function.Injective (isHermitian_spectralEnsembleMatrix hP (sphereCoeff x)).eigenvalues) :
    IsClosed (easyTube hP i₀ Ω Z a ∩
      (K ×ˢ (Set.univ : Set (UnitAddTorus (phaseIndex i₀))))) := by
  refine isClosed_projectiveBundleTube_inter hK ?_ a
  intro κ j x hx
  refine ContinuousAt.continuousWithinAt ?_
  exact continuousAt_spectralCrossWeight
    ((continuous_spectralTuple hP).comp continuous_sphereCoeff)
    ((continuous_spectralEnsembleMatrix P).comp continuous_sphereCoeff) (Z κ) Ω j
    (injective_spectralTuple hP (hKsimple x hx))

/-- The eigencoordinates of the reference state, conjugated. -/
def tubeInputCoeff (hP : ∀ a, (P a).IsHermitian) (Ω : Fin D → ℂ) (x : coeffSphere N) :
    Fin D → ℂ :=
  fun j => conj (finiteComplexInner (sortedEigenBasis hP (sphereCoeff x) j) Ω)

/-- The eigencoordinates of the dictionary, conjugated. -/
def tubeTargetCoeff (hP : ∀ a, (P a).IsHermitian) (Z : C → (Fin D → ℂ))
    (x : coeffSphere N) : C → Fin D → ℂ :=
  fun κ j => conj (finiteComplexInner (sortedEigenBasis hP (sphereCoeff x) j) (Z κ))

theorem easyTube_weight_eq (hP : ∀ a, (P a).IsHermitian) {x : coeffSphere N}
    (hinj : Function.Injective (isHermitian_spectralEnsembleMatrix hP (sphereCoeff x)).eigenvalues)
    (Ω : Fin D → ℂ) (Z : C → (Fin D → ℂ)) (κ : C) (j : Fin D) :
    spectralCrossWeight (spectralTuple hP (sphereCoeff x))
        (spectralEnsembleMatrix P (sphereCoeff x)) (Z κ) Ω j
      = conj (tubeInputCoeff hP Ω x j) * tubeTargetCoeff hP Z x κ j := by
  rw [spectralCrossWeight_eq (isOrthoEigenBasis_sortedEigenBasis hP (sphereCoeff x))
    (injective_spectralTuple hP hinj) (Z κ) Ω, tubeInputCoeff, tubeTargetCoeff]
  simp only [RingHomInvPair.comp_apply_eq]
  ring

/-- The fibre of a bundle tube depends only on the weight over that point. -/
theorem preimage_projectiveBundleTube_congr (i₀ : Fin D) (a : ℝ) (x : coeffSphere N)
    (w w' : coeffSphere N → C → Fin D → ℂ) (h : w x = w' x) :
    Prod.mk x ⁻¹' projectiveBundleTube i₀ w a
      = Prod.mk x ⁻¹' projectiveBundleTube i₀ w' a := by
  ext y
  simp only [Set.mem_preimage, projectiveBundleTube, Set.mem_setOf_eq, h]

/-- **The fibre of the tube is the relative-phase capture event of the cross-weights.** -/
theorem preimage_easyTube (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D) (Ω : Fin D → ℂ)
    (Z : C → (Fin D → ℂ)) (a : ℝ) {x : coeffSphere N}
    (hx : Function.Injective
      (isHermitian_spectralEnsembleMatrix hP (sphereCoeff x)).eigenvalues) :
    Prod.mk x ⁻¹' easyTube hP i₀ Ω Z a
      = projectiveAmpCaptureTarget i₀ (tubeInputCoeff hP Ω x) a (tubeTargetCoeff hP Z x) := by
  rw [easyTube, preimage_projectiveBundleTube_congr i₀ a x _
    (fun x' κ j => conj (tubeInputCoeff hP Ω x' j) * tubeTargetCoeff hP Z x' κ j)
    (by funext κ; funext j; exact easyTube_weight_eq hP hx Ω Z κ j)]
  exact preimage_projectiveBundleTube i₀ a (tubeInputCoeff hP Ω) (tubeTargetCoeff hP Z) x

/-- **At a simple-spectrum direction the angular-phase preimage of the tube is the physical capture
event.** -/
theorem mem_anglePhaseMap_preimage_easyTube_iff (hP : ∀ a, (P a).IsHermitian) (i₀ : Fin D)
    (Ω : Fin D → ℂ) (Z : C → (Fin D → ℂ)) (a : ℝ) (t : ℝ) {x : coeffSphere N}
    (hsimplex : Function.Injective
      (isHermitian_spectralEnsembleMatrix hP (sphereCoeff x)).eigenvalues) :
    x ∈ anglePhaseMap hP i₀ t ⁻¹' easyTube hP i₀ Ω Z a
      ↔ ∃ κ : C, a ≤ finitePureStateFidelity
          (unitaryEvolution (spectralEnsembleMatrix P (sphereCoeff x))
            (2 * Real.pi * t) *ᵥ Ω) (Z κ) := by
  have hpt : (anglePhaseMap hP i₀ t x).2
      = evolvedPhasePoint (spectralTuple hP (sphereCoeff x)) i₀ (2 * Real.pi * t) := by
    funext j
    show ((t * projectivePhase hP i₀ (sphereCoeff x) j : ℝ) : UnitAddCircle) = _
    have hpi : (2 * Real.pi) ≠ 0 := by
      have := Real.pi_ne_zero
      intro h
      apply this
      linarith [h]
    show ((t * projectivePhase hP i₀ (sphereCoeff x) j : ℝ) : UnitAddCircle)
      = ((((2 * Real.pi * t) / (2 * Real.pi)) *
          (spectralTuple hP (sphereCoeff x) j.1 - spectralTuple hP (sphereCoeff x) i₀) : ℝ) :
        UnitAddCircle)
    congr 1
    rw [projectivePhase]
    field_simp
  constructor
  · rintro ⟨κ, hκ⟩
    refine ⟨κ, ?_⟩
    rw [finitePureStateFidelity_unitaryEvolution_eq
      (isOrthoEigenBasis_sortedEigenBasis hP (sphereCoeff x))
      (injective_spectralTuple hP hsimplex) Ω (Z κ) i₀ (2 * Real.pi * t)]
    rw [← hpt]
    exact hκ
  · rintro ⟨κ, hκ⟩
    refine ⟨κ, ?_⟩
    rw [finitePureStateFidelity_unitaryEvolution_eq
      (isOrthoEigenBasis_sortedEigenBasis hP (sphereCoeff x))
      (injective_spectralTuple hP hsimplex) Ω (Z κ) i₀ (2 * Real.pi * t)] at hκ
    rw [hpt]
    exact hκ

/-! ## The plateau bookkeeping -/

theorem finiteComplexInner_conj_self {α : Type*} [Fintype α] (u : α → ℂ)
    (h : finiteComplexInner u u = 1) :
    finiteComplexInner (fun j => conj (u j)) (fun j => conj (u j)) = 1 := by
  have : finiteComplexInner (fun j => conj (u j)) (fun j => conj (u j))
      = conj (finiteComplexInner u u) := by
    rw [finiteComplexInner, finiteComplexInner, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, RingHomInvPair.comp_apply_eq, mul_comm]
  rw [this, h, map_one]

/-- **The `(20)` bookkeeping on a fixed shell.**  For a family with one simple-spectrum member, an
input state and a finite target dictionary below the replica order, the long-time shell density of
the directions whose evolution reaches the dictionary is at most `2^{-r/2}` plus the mass of the
directions with a large input collision. -/
theorem limsup_sphereLaw_capture_le (hN : 0 < N)
    (hP : ∀ a, (P a).IsHermitian) (hdisc : spectralDiscriminantPoly P ≠ 0)
    (hRL : ∀ b : Fin D → ℝ, (∑ i, b i = 0) → b ≠ 0 →
      ∀ g : coeffSphere N → ℂ, Measurable g → ∀ Cb : ℝ, 0 ≤ Cb → (∀ x, ‖g x‖ ≤ Cb) →
        Tendsto (fun u : ℝ => ∫ x, g x *
            Complex.exp (-((u * sortedSpectralAction hP b (sphereCoeff x) : ℝ) : ℂ) * Complex.I)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)) (cocompact ℝ) (nhds 0))
    (i₀ : Fin D) (Ω : Fin D → ℂ) (hΩ : finiteComplexInner Ω Ω = 1)
    (Z : C → (Fin D → ℂ)) (hZ : ∀ κ, finiteComplexInner (Z κ) (Z κ) = 1)
    {a : ℝ} (ha : 0 < a) {r : ℕ} (hr : 1 ≤ r) {c₀ : ℝ}
    (hscale : 16 * c₀ / a ^ 2 ≤ 1 / (2 * r))
    {M : ℝ} (hM : 1 < M) {s : ℕ} (hcard : (Fintype.card C : ℝ) ≤ M ^ (s + 1))
    (hs : ((s : ℝ) + 1) * Real.log M ≤ ((r : ℝ) / 2) * Real.log 2)
    {G : Set (coeffSphere N)} (hG : MeasurableSet G)
    (hGsimple : ∀ x ∈ G, Function.Injective
      (isHermitian_spectralEnsembleMatrix hP (sphereCoeff x)).eigenvalues)
    (hGcoll : ∀ x ∈ G, spectralCollision (sortedEigenBasis hP (sphereCoeff x)) Ω ≤ c₀)
    {δ : ENNReal} (hGc : (sphereLaw N) Gᶜ ≤ δ) :
    (atTop.limsup fun t : ℝ => (sphereLaw N)
        {x : coeffSphere N | ∃ κ : C, a ≤ finitePureStateFidelity
          (unitaryEvolution (spectralEnsembleMatrix P (sphereCoeff x))
            (2 * Real.pi * t) *ᵥ Ω) (Z κ)})
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) + δ := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : Set (coeffSphere N), S = {x : coeffSphere N |
      Function.Injective (isHermitian_spectralEnsembleMatrix hP (sphereCoeff x)).eigenvalues} :=
    ⟨_, rfl⟩
  have hbadmeas : MeasurableSet {θ : Fin N → ℝ |
      ¬ Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues} := by
    have hset : {θ : Fin N → ℝ |
        ¬ Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues}
        = {θ : Fin N → ℝ | MvPolynomial.eval θ (spectralDiscriminantPoly P) = 0} := by
      ext θ
      simp only [Set.mem_setOf_eq]
      rw [injective_eigenvalues_iff_eval_spectralDiscriminantPoly_ne_zero hP θ]
      exact not_not
    rw [hset]
    exact (MvPolynomial.continuous_eval _).measurable (measurableSet_singleton (0 : ℝ))
  have hScompl : Sᶜ = sphereCoeff ⁻¹' {θ : Fin N → ℝ |
      ¬ Function.Injective (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues} := by
    rw [hSdef]
    rfl
  have hSmeas : MeasurableSet S := by
    refine MeasurableSet.of_compl ?_
    rw [hScompl]
    exact hbadmeas.preimage continuous_sphereCoeff.measurable
  have hSnull : (sphereLaw N) Sᶜ = 0 := by
    rw [hScompl]
    exact sphereLaw_eq_zero_of_toSphere_eq_zero (toSphere_degenerate_eq_zero hP hdisc)
  have hclosed : ∀ K : Set (coeffSphere N), IsCompact K → K ⊆ S →
      IsClosed (easyTube hP i₀ Ω Z a ∩
        (K ×ˢ (Set.univ : Set (UnitAddTorus (phaseIndex i₀))))) := by
    intro K hK hKS
    refine isClosed_easyTube_inter hP i₀ Ω Z a hK ?_
    intro x hx
    have := hKS hx
    rw [hSdef] at this
    exact this
  have hgood : ∀ x ∈ G, (volume : Measure (UnitAddTorus (phaseIndex i₀)))
      (Prod.mk x ⁻¹' easyTube hP i₀ Ω Z a)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) / 2))) := by
    intro x hx
    rw [preimage_easyTube hP i₀ Ω Z a (hGsimple x hx)]
    have heb := isOrthoEigenBasis_sortedEigenBasis hP (sphereCoeff x)
    have hnorm : ∀ j, ‖tubeInputCoeff hP Ω x j‖
        = ‖eigenCoords (sortedEigenBasis hP (sphereCoeff x)) Ω j‖ := by
      intro j
      rw [tubeInputCoeff, Complex.norm_conj]
      rfl
    have hcsum : ∑ j, ‖tubeInputCoeff hP Ω x j‖ ^ 2 ≤ 1 := by
      rw [Finset.sum_congr rfl (fun j _ => by rw [hnorm j])]
      exact le_of_eq (sum_normSq_eigenCoords heb Ω hΩ)
    have hznormfun : ∀ (κ : C) j, ‖tubeTargetCoeff hP Z x κ j‖
        = ‖eigenCoords (sortedEigenBasis hP (sphereCoeff x)) (Z κ) j‖ := by
      intro κ j
      rw [tubeTargetCoeff, Complex.norm_conj]
      rfl
    have hz : ∀ κ, finiteComplexInner (tubeTargetCoeff hP Z x κ)
        (tubeTargetCoeff hP Z x κ) = 1 := by
      intro κ
      refine finiteComplexInner_conj_self _ ?_
      exact (finiteComplexInner_eigenCoords heb (Z κ) (Z κ)).trans (hZ κ)
    have hznorm : ∀ κ, ∑ j, ‖tubeTargetCoeff hP Z x κ j‖ ^ 2 ≤ 1 := by
      intro κ
      rw [Finset.sum_congr rfl (fun j _ => by rw [hznormfun κ j])]
      exact le_of_eq (sum_normSq_eigenCoords heb (Z κ) (hZ κ))
    have hcoll : occupationCollision (fun j => ‖tubeInputCoeff hP Ω x j‖ ^ 2) ≤ c₀ := by
      rw [occupationCollision, Finset.sum_congr rfl (fun j _ => by rw [hnorm j])]
      rw [← occupationCollision]
      rw [occupationCollision_eigenCoords]
      exact hGcoll x hx
    rw [torusVolume_eq (phaseIndex i₀)]
    exact measure_projectiveAmpCaptureTarget_le_two_rpow i₀ _ hcsum ha _ hz hznorm hr hcoll
      hscale hM hcard hs
  have hmain := limsup_measure_preimage_anglePhase_le_of_good_of_exhaustion hN hP i₀ hRL
    hSmeas hSnull hclosed hG hgood hGc
  refine le_trans (limsup_le_limsup (Filter.Eventually.of_forall fun t => ?_)) hmain
  have hsub : {x : coeffSphere N | ∃ κ : C, a ≤ finitePureStateFidelity
      (unitaryEvolution (spectralEnsembleMatrix P (sphereCoeff x))
        (2 * Real.pi * t) *ᵥ Ω) (Z κ)}
      ⊆ (anglePhaseMap hP i₀ t ⁻¹' easyTube hP i₀ Ω Z a) ∪ Sᶜ := by
    intro x hx
    by_cases hxS : x ∈ S
    · refine Or.inl ?_
      refine (mem_anglePhaseMap_preimage_easyTube_iff hP i₀ Ω Z a t ?_).mpr hx
      rw [hSdef] at hxS
      exact hxS
    · exact Or.inr hxS
  calc (sphereLaw N) {x : coeffSphere N | ∃ κ : C, a ≤ finitePureStateFidelity
        (unitaryEvolution (spectralEnsembleMatrix P (sphereCoeff x))
          (2 * Real.pi * t) *ᵥ Ω) (Z κ)}
      ≤ (sphereLaw N) ((anglePhaseMap hP i₀ t ⁻¹' easyTube hP i₀ Ω Z a) ∪ Sᶜ) :=
        measure_mono hsub
    _ ≤ (sphereLaw N) (anglePhaseMap hP i₀ t ⁻¹' easyTube hP i₀ Ω Z a)
        + (sphereLaw N) Sᶜ := measure_union_le _ _
    _ = (sphereLaw N) (anglePhaseMap hP i₀ t ⁻¹' easyTube hP i₀ Ω Z a) := by
        rw [hSnull, add_zero]

/-! ## The gauge-invariant collision functional -/

/-- The simple-spectrum locus of the shell. -/
def simpleLocus (hP : ∀ a, (P a).IsHermitian) : Set (coeffSphere N) :=
  {x | Function.Injective (isHermitian_spectralEnsembleMatrix hP (sphereCoeff x)).eigenvalues}

theorem isOpen_simpleLocus (hP : ∀ a, (P a).IsHermitian) : IsOpen (simpleLocus hP) := by
  have hclosed := isClosed_repeatedSpectrum
    (F := fun x : coeffSphere N => spectralEnsembleMatrix P (sphereCoeff x))
    ((continuous_spectralEnsembleMatrix P).comp continuous_sphereCoeff)
    (fun x => isHermitian_spectralEnsembleMatrix hP (sphereCoeff x))
  rw [← isClosed_compl_iff]
  exact hclosed

/-- The input collision read through the gauge-invariant cross-weights. -/
def crossCollision (hP : ∀ a, (P a).IsHermitian) (Ω : Fin D → ℂ) (x : coeffSphere N) : ℝ :=
  ∑ j, ‖spectralCrossWeight (spectralTuple hP (sphereCoeff x))
    (spectralEnsembleMatrix P (sphereCoeff x)) Ω Ω j‖ ^ 2

theorem crossCollision_eq (hP : ∀ a, (P a).IsHermitian) (Ω : Fin D → ℂ) {x : coeffSphere N}
    (hx : x ∈ simpleLocus hP) :
    crossCollision hP Ω x = spectralCollision (sortedEigenBasis hP (sphereCoeff x)) Ω := by
  rw [crossCollision, spectralCollision]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [spectralCrossWeight_eq (isOrthoEigenBasis_sortedEigenBasis hP (sphereCoeff x))
    (injective_spectralTuple hP hx) Ω Ω j, finitePureStateFidelity]
  rw [norm_mul, Complex.norm_conj]
  ring

theorem continuousOn_crossCollision (hP : ∀ a, (P a).IsHermitian) (Ω : Fin D → ℂ) :
    ContinuousOn (crossCollision hP Ω) (simpleLocus hP) := by
  refine continuousOn_finsetSum _ fun j _ => ?_
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  exact (((continuousAt_spectralCrossWeight
    ((continuous_spectralTuple hP).comp continuous_sphereCoeff)
    ((continuous_spectralEnsembleMatrix P).comp continuous_sphereCoeff) Ω Ω j
    (injective_spectralTuple hP hx)).norm).pow 2)

/-- The good set of directions: simple spectrum and small input collision. -/
def goodSet (hP : ∀ a, (P a).IsHermitian) (Ω : Fin D → ℂ) (c : ℝ) : Set (coeffSphere N) :=
  simpleLocus hP ∩ crossCollision hP Ω ⁻¹' (Set.Iic c)

theorem measurableSet_goodSet (hP : ∀ a, (P a).IsHermitian) (Ω : Fin D → ℂ) (c : ℝ) :
    MeasurableSet (goodSet hP Ω c) := by
  have hopen : IsOpen (simpleLocus hP ∩ crossCollision hP Ω ⁻¹' (Set.Ioi c)) :=
    (continuousOn_crossCollision hP Ω).isOpen_inter_preimage (isOpen_simpleLocus hP) isOpen_Ioi
  have hEq : goodSet hP Ω c
      = simpleLocus hP \ (simpleLocus hP ∩ crossCollision hP Ω ⁻¹' (Set.Ioi c)) := by
    ext x
    simp only [goodSet, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_sdiff,
      Set.mem_Ioi, not_and, not_lt]
    constructor
    · rintro ⟨hs, hle⟩
      exact ⟨hs, fun _ => hle⟩
    · rintro ⟨hs, h⟩
      exact ⟨hs, h hs⟩
  rw [hEq]
  exact (isOpen_simpleLocus hP).measurableSet.diff hopen.measurableSet

end

end GaloisForLFunctions.HTGeometry
