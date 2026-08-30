import GaloisForLFunctions.HTGeometry.HellingerAffinityFactorization

/-!
# Common Markov recovery is information-neutral

A parameter-independent Markov kernel extends two observer laws to split packet laws on the
product space.  Marginalization is a left inverse of the extension, the likelihood ratio is the
original one read on the retained coordinate, and both the relative entropy and the Hellinger
affinity are unchanged.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

variable {X Hh : Type*} [MeasurableSpace X] [MeasurableSpace Hh]

/-- `(RCN.20)`  The split packet law of an observer law under a common Markov recovery kernel. -/
def splitPacketLaw (μ : Measure X) (κ : Kernel X Hh) : Measure (X × Hh) := μ ⊗ₘ κ

instance isFiniteMeasure_splitPacketLaw (μ : Measure X) [IsFiniteMeasure μ] (κ : Kernel X Hh)
    [IsFiniteKernel κ] : IsFiniteMeasure (splitPacketLaw μ κ) := by
  rw [splitPacketLaw]; infer_instance

instance sFinite_splitPacketLaw (μ : Measure X) [SFinite μ] (κ : Kernel X Hh)
    [IsSFiniteKernel κ] : SFinite (splitPacketLaw μ κ) := by
  rw [splitPacketLaw]; infer_instance

/-- Marginalization is a left inverse of packet extension. -/
theorem splitPacketLaw_fst (μ : Measure X) [SFinite μ] (κ : Kernel X Hh) [IsMarkovKernel κ] :
    (splitPacketLaw μ κ).fst = μ :=
  Measure.fst_compProd μ κ

/-- `(RCN.23)`  Packet extension is an isometry of score spaces: integrating a function of the
retained coordinate against the split packet law is integrating it against the original law. -/
theorem lintegral_splitPacketLaw_comp_fst (μ : Measure X) [SFinite μ] (κ : Kernel X Hh)
    [IsMarkovKernel κ] {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p.1 ∂(splitPacketLaw μ κ) = ∫⁻ x, f x ∂μ := by
  have h : ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂((splitPacketLaw μ κ).fst) := by rw [splitPacketLaw_fst]
  rw [h, Measure.fst, lintegral_map hf measurable_fst]

/-- `(RCN.23)`  Packet extension is an `L^p` isometry of score spaces. -/
theorem eLpNorm_splitPacketLaw_comp_fst (μ : Measure X) [SFinite μ] (κ : Kernel X Hh)
    [IsMarkovKernel κ] {G : Type*} [NormedAddCommGroup G] {g : X → G}
    (hg : AEStronglyMeasurable g μ) (p : ℝ≥0∞) :
    eLpNorm (fun q : X × Hh => g q.1) p (splitPacketLaw μ κ) = eLpNorm g p μ := by
  have hmap : (splitPacketLaw μ κ).map Prod.fst = μ := splitPacketLaw_fst μ κ
  have hg' : AEStronglyMeasurable g ((splitPacketLaw μ κ).map Prod.fst) := by rw [hmap]; exact hg
  have h := eLpNorm_map_measure (μ := splitPacketLaw μ κ) (f := Prod.fst) (g := g) (p := p)
    hg' measurable_fst.aemeasurable
  rw [hmap] at h
  exact h.symm

/-- `(RCN.22)`  The likelihood ratio of two split packet laws is the original likelihood ratio,
read on the retained coordinate. -/
theorem splitPacketLaw_withDensity (ν : Measure X) [SFinite ν] (κ : Kernel X Hh)
    [IsSFiniteKernel κ] {f : X → ℝ≥0∞} (hf : Measurable f) :
    splitPacketLaw (ν.withDensity f) κ
      = (splitPacketLaw ν κ).withDensity (fun p => f p.1) :=
  (compProd_withDensity_fst ν κ hf).symm

/-- `(RCN.21)`  A common Markov recovery preserves relative entropy exactly. -/
theorem klDiv_splitPacketLaw (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X Hh) [IsMarkovKernel κ] :
    klDiv (splitPacketLaw μ κ) (splitPacketLaw ν κ) = klDiv μ ν :=
  klDiv_compProd_left μ ν κ

/-- `(RCN.21)`, Hellinger form.  A common Markov recovery preserves the Hellinger affinity
exactly. -/
theorem bhattacharyya_splitPacketLaw (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X Hh) [IsMarkovKernel κ] :
    bhattacharyya (splitPacketLaw μ κ) (splitPacketLaw ν κ) = bhattacharyya μ ν := by
  set lam : Measure X := μ + ν with hlam
  have hμl : μ ≪ lam := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hνl : ν ≪ lam := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  set f : X → ℝ≥0∞ := μ.rnDeriv lam with hf
  set g : X → ℝ≥0∞ := ν.rnDeriv lam with hg
  have hfm : Measurable f := Measure.measurable_rnDeriv _ _
  have hgm : Measurable g := Measure.measurable_rnDeriv _ _
  have hμd : μ = lam.withDensity f := (Measure.withDensity_rnDeriv_eq μ lam hμl).symm
  have hνd : ν = lam.withDensity g := (Measure.withDensity_rnDeriv_eq ν lam hνl).symm
  haveI : IsFiniteMeasure (lam.withDensity f) := hμd ▸ ‹IsFiniteMeasure μ›
  haveI : IsFiniteMeasure (lam.withDensity g) := hνd ▸ ‹IsFiniteMeasure ν›
  have hsplitμ : splitPacketLaw μ κ = (splitPacketLaw lam κ).withDensity (fun p => f p.1) := by
    rw [hμd]; exact splitPacketLaw_withDensity lam κ hfm
  have hsplitν : splitPacketLaw ν κ = (splitPacketLaw lam κ).withDensity (fun p => g p.1) := by
    rw [hνd]; exact splitPacketLaw_withDensity lam κ hgm
  haveI : IsFiniteMeasure ((splitPacketLaw lam κ).withDensity (fun p => f p.1)) :=
    hsplitμ ▸ (by rw [splitPacketLaw]; infer_instance)
  haveI : IsFiniteMeasure ((splitPacketLaw lam κ).withDensity (fun p => g p.1)) :=
    hsplitν ▸ (by rw [splitPacketLaw]; infer_instance)
  rw [hsplitμ, hsplitν, bhattacharyya_withDensity _ (by fun_prop) (by fun_prop),
    lintegral_splitPacketLaw_comp_fst lam κ (f := fun x => (f x * g x) ^ (1 / 2 : ℝ))
      (by fun_prop), bhattacharyya_eq_lintegral μ ν lam hμl hνl]

/-- `(RCN.24)`  Common conditional formation preserves divergence, affinity and the retained
observer law. -/
theorem commonRecovery_certificate (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (κ : Kernel X Hh) [IsMarkovKernel κ] :
    (splitPacketLaw μ κ).fst = μ
      ∧ klDiv (splitPacketLaw μ κ) (splitPacketLaw ν κ) = klDiv μ ν
      ∧ bhattacharyya (splitPacketLaw μ κ) (splitPacketLaw ν κ) = bhattacharyya μ ν :=
  ⟨splitPacketLaw_fst μ κ, klDiv_splitPacketLaw μ ν κ, bhattacharyya_splitPacketLaw μ ν κ⟩

end

end GaloisForLFunctions.HTGeometry
