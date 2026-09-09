import GaloisForLFunctions.HTGeometry.GomesFockThresholdCardinality
import GaloisForLFunctions.HTGeometry.GomesFockThresholdChannel
import GaloisForLFunctions.HTGeometry.GomesFockThresholdObservability

/-! Exact compression of the spectral threshold experiment. Optional distinct
cut boundaries index precisely its realizable cells, replacing the 2^n labelled
carrier by distinct-cut-count+1 outcomes. All actual spectral observations are
preserved: only empty cells are removed. This realizes the reconstruction-based
compression exposed by the corpus application of Gomes, arXiv:2607.24901v1.
A realizable cell can still carry zero spectral mass; none are discarded on that basis. -/

open scoped Matrix Classical ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- The realizable cell indexed by an optional maximal failed threshold. -/
def gomesFockThresholdCompressedCell {n : ℕ} (cuts : Fin n → ℝ)
    (r : Option ↑(gomesFockThresholdCutSet cuts)) : Set ℝ :=
  gomesFockThresholdCell cuts (gomesFockThresholdBoundaryRecord cuts r)

/-- Every compressed cell is Borel. -/
theorem gomesFockThresholdCompressedCell_measurable {n : ℕ} (cuts : Fin n → ℝ)
    (r : Option ↑(gomesFockThresholdCutSet cuts)) :
    MeasurableSet (gomesFockThresholdCompressedCell cuts r) :=
  gomesFockThresholdCell_measurable cuts _

/-- The compressed carrier has no geometrically impossible records. -/
theorem gomesFockThresholdCompressedCell_nonempty {n : ℕ} (cuts : Fin n → ℝ)
    (r : Option ↑(gomesFockThresholdCutSet cuts)) :
    (gomesFockThresholdCompressedCell cuts r).Nonempty :=
  gomesFockThresholdBoundaryRecord_realizable cuts r

/-- Distinct compressed records remain disjoint. -/
theorem gomesFockThresholdCompressedCell_pairwise {n : ℕ} (cuts : Fin n → ℝ) :
    Pairwise (fun r s => Disjoint (gomesFockThresholdCompressedCell cuts r)
      (gomesFockThresholdCompressedCell cuts s)) := by
  intro r s hrs
  apply gomesFockThresholdCell_pairwise cuts
  intro h
  exact hrs (gomesFockThresholdBoundaryRecord_injective cuts h)

/-- Compression retains the complete energy-axis partition. -/
theorem gomesFockThresholdCompressedCell_iUnion {n : ℕ} (cuts : Fin n → ℝ) :
    (⋃ r, gomesFockThresholdCompressedCell cuts r) = Set.univ := by
  ext t
  simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
  have hcell : (gomesFockThresholdCell cuts (gomesFockThresholdOutcome cuts t)).Nonempty :=
    ⟨t,gomesFockThresholdOutcome_mem cuts t⟩
  obtain ⟨r,hr⟩ := (gomesFockThresholdCell_boundary_classification cuts _).mp hcell
  refine ⟨r,?_⟩
  change t ∈ gomesFockThresholdCell cuts (gomesFockThresholdBoundaryRecord cuts r)
  rw [hr]
  exact gomesFockThresholdOutcome_mem cuts t

/-- The unchanged spectral effect of a retained record. -/
def gomesFockThresholdCompressedEffect {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (r : Option ↑(gomesFockThresholdCutSet cuts)) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  gomesFockSpectralPOVM B (gomesFockThresholdCompressedCell cuts r)

/-- A retained effect is exactly its original Boolean-labelled effect. -/
theorem gomesFockThresholdCompressedEffect_eq_original {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (r : Option ↑(gomesFockThresholdCutSet cuts)) :
    gomesFockThresholdCompressedEffect B cuts r =
      gomesFockThresholdEffect B cuts (gomesFockThresholdBoundaryRecord cuts r) := rfl

/-- Every retained effect is positive. -/
theorem gomesFockThresholdCompressedEffect_posSemidef {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (r : Option ↑(gomesFockThresholdCutSet cuts)) :
    (gomesFockThresholdCompressedEffect B cuts r).PosSemidef :=
  gomesFockSpectralPOVM_posSemidef B _

/-- Removing all impossible labels leaves exact operator normalization. -/
theorem gomesFockThresholdCompressedEffect_sum {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) :
    ∑ r, gomesFockThresholdCompressedEffect B cuts r = 1 := by
  have h := VectorMeasure.hasSum_of_disjoint_iUnion (v := gomesFockSpectralPOVM B)
    (gomesFockThresholdCompressedCell_measurable cuts) (gomesFockThresholdCompressedCell_pairwise cuts)
  simpa only [tsum_fintype,gomesFockThresholdCompressedCell_iUnion,gomesFockSpectralPOVM_univ,
    gomesFockThresholdCompressedEffect] using h.tsum_eq

/-- The compressed experiment in the existing finite POVM interface. -/
def gomesFockThresholdCompressedPOVM {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) :
    FiniteMatrixPOVM (d+1) (Fintype.card (Option ↑(gomesFockThresholdCutSet cuts))) where
  effect j := gomesFockThresholdCompressedEffect B cuts
    ((Fintype.equivFin (Option ↑(gomesFockThresholdCutSet cuts))).symm j)
  effect_posSemidef j := gomesFockThresholdCompressedEffect_posSemidef B cuts _
  completeness := by
    rw [(Fintype.equivFin (Option ↑(gomesFockThresholdCutSet cuts))).symm.sum_comp]
    exact gomesFockThresholdCompressedEffect_sum B cuts

/-- Exact size of the compressed outcome carrier. -/
theorem gomesFockThresholdCompressedPOVM_outcome_count {n : ℕ} (cuts : Fin n → ℝ) :
    Fintype.card (Option ↑(gomesFockThresholdCutSet cuts)) =
      (gomesFockThresholdCutSet cuts).card+1 := by simp

/-- Fin reindexing preserves each compressed effect. -/
theorem gomesFockThresholdCompressedPOVM_effect_record {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (r : Option ↑(gomesFockThresholdCutSet cuts)) :
    (gomesFockThresholdCompressedPOVM B cuts).effect
      (Fintype.equivFin (Option ↑(gomesFockThresholdCutSet cuts)) r) =
      gomesFockThresholdCompressedEffect B cuts r := by
  simp [gomesFockThresholdCompressedPOVM]

/-- The compressed experiment retains all original scalar mass. -/
theorem gomesFockThresholdCompressedMass_sum {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) (x : Fin (d+1) → ℂ) :
    ∑ r, gomesFockWindowMass B (gomesFockThresholdCompressedCell cuts r) x =
      freeFockVectorMoment (gomesCompletedFockGenerators B) x 0 := by
  have h := VectorMeasure.hasSum_of_disjoint_iUnion
    (v := (gomesFockSpectralMeasure B x).toSignedMeasure)
    (gomesFockThresholdCompressedCell_measurable cuts) (gomesFockThresholdCompressedCell_pairwise cuts)
  simpa only [tsum_fintype,gomesFockThresholdCompressedCell_iUnion,Measure.toSignedMeasure_apply,
    gomesFockThresholdCompressedCell_measurable,MeasurableSet.univ,if_true,measureReal_def,
    gomesFockWindowMass,gomesFockSpectralMeasure_totalMass] using h.tsum_eq

/-- Compression preserves observational equality even between different source dimensions and generator counts. -/
theorem gomesFockThresholdCompressed_observations_iff {d e k l n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (C : Fin l → Matrix (Fin (e+1)) (Fin (e+1)) ℂ) (cuts : Fin n → ℝ)
    (x : Fin (d+1) → ℂ) (y : Fin (e+1) → ℂ) :
    (∀ r, gomesFockWindowMass B (gomesFockThresholdCompressedCell cuts r) x =
      gomesFockWindowMass C (gomesFockThresholdCompressedCell cuts r) y) ↔
    (∀ bits, gomesFockWindowMass B (gomesFockThresholdCell cuts bits) x =
      gomesFockWindowMass C (gomesFockThresholdCell cuts bits) y) := by
  constructor
  · intro h bits
    by_cases hn : (gomesFockThresholdCell cuts bits).Nonempty
    · obtain ⟨r,hr⟩ := (gomesFockThresholdCell_boundary_classification cuts bits).mp hn
      simpa only [gomesFockThresholdCompressedCell,hr] using h r
    · have he : gomesFockThresholdCell cuts bits = ∅ := by
        ext t
        constructor
        · intro ht
          exact False.elim (hn ⟨t,ht⟩)
        · intro ht
          cases ht
      simp [he,gomesFockWindowMass]
  · intro h r
    exact h (gomesFockThresholdBoundaryRecord cuts r)

/-- The compressed bank has no common blind state except zero. -/
theorem gomesFockThresholdCompressedMass_all_zero_iff {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) (x : Fin (d+1) → ℂ) :
    (∀ r, gomesFockWindowMass B (gomesFockThresholdCompressedCell cuts r) x = 0) ↔ x = 0 := by
  constructor
  · intro h
    apply (gomesFockVector_mass_zero_iff (gomesCompletedFockGenerators B) x).mp
    rw [← gomesFockThresholdCompressedMass_sum B cuts x]
    simp only [h,Finset.sum_const_zero]
  · intro hx
    subst x
    have h0 := (gomesFockSpectralMeasure_zero_iff B 0).mpr rfl
    intro r
    simp [gomesFockWindowMass,h0]

/-- Three coherent reference intensities on each retained cell. -/
def gomesFockThresholdCompressedCoherentMenu {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (x : Fin (d+1) → ℂ) (c : ℂ) : Option ↑(gomesFockThresholdCutSet cuts) → ℝ × ℝ × ℝ :=
  fun r => gomesFockWindowIntensityMenu B (gomesFockThresholdCompressedCell cuts r) x c

/-- Compression retains complete scalar reconstruction by coherent reference measurements. -/
theorem gomesFockThresholdCompressedCoherentMenu_reconstruction {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (x : Fin (d+1) → ℂ) (c e : ℂ) :
    gomesFockThresholdCompressedCoherentMenu B cuts x c =
      gomesFockThresholdCompressedCoherentMenu B cuts x e ↔ c=e ∨ x=0 := by
  constructor
  · intro h
    by_cases hce : c=e
    · exact Or.inl hce
    · right
      apply (gomesFockThresholdCompressedMass_all_zero_iff B cuts x).mp
      intro r
      exact ((gomesFockWindowIntensityMenu_reconstruction B
        (gomesFockThresholdCompressedCell cuts r) x c e).mp (congrFun h r)).resolve_left hce
  · rintro (hce | hx)
    · rw [hce]
    · funext r
      apply (gomesFockWindowIntensityMenu_reconstruction B
        (gomesFockThresholdCompressedCell cuts r) x c e).mpr
      exact Or.inr ((gomesFockThresholdCompressedMass_all_zero_iff B cuts x).mpr hx r)

/-- The compressed physical measurement inherits the exact quantum-to-classical fidelity bound. -/
theorem gomesFockThresholdCompressedPOVM_fidelity_dataProcessing {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (Y Z : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    finiteBuresRootFidelity (Yᴴ*Y) (Zᴴ*Z) ≤
      finiteHellingerAffinity
        (fun j => ((Yᴴ*Y*(gomesFockThresholdCompressedPOVM B cuts).effect j).trace).re)
        (fun j => ((Zᴴ*Z*(gomesFockThresholdCompressedPOVM B cuts).effect j).trace).re) :=
  (gomesFockThresholdCompressedPOVM B cuts).finiteBuresRootFidelity_le_finiteHellingerAffinity
    (Matrix.posSemidef_conjTranspose_mul_self Y) (Matrix.posSemidef_conjTranspose_mul_self Z)

end GaloisForLFunctions.HTGeometry
