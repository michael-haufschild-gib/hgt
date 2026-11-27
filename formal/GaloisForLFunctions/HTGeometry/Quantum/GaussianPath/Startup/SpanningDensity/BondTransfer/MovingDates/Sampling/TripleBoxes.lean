import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.Relative.RelativeTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.BoxPrice

/-! # Finite lower-tail bound for disjoint calibrated triples -/

open Finset Set MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit.Counts RepeatedGates.PhysicalBlocks FixedHorizon
noncomputable section

/-- A moving four-row calibration box may have very small probability.
The lower-tail exponent is proportional to the expected number of matches
in the actual Gaussian prefix. -/
theorem few_triple_boxes (q δ : ℝ) (m : ℕ) :
    let p := boxProbability q δ
    pathPauliDisorderLaw.real {ω | ((goodBoxes q δ ω m).card:ℝ)≤p*m/4}≤2*exp (-(p*m)/4) := by
  classical
  intro p
  let ν := Measure.infinitePi (fun _ : TripleBoxIndex => gaussianReal 0 1)
  letI : IsProbabilityMeasure ν := by dsimp only [ν]; infer_instance
  let B : Set (TripleBoxIndex→ℝ) := Set.univ.pi fun i => Icc (boxField q i-δ) (boxField q i+δ)
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  let X (ω : PathPauliDisorder) (i : Fin m) (j : TripleBoxIndex) := ω (blockCoordinate (i.val,j))
  let μ := Measure.pi fun _ : Fin m => ν
  have hX : MeasurePreserving X pathPauliDisorderLaw μ := by
    have hi : Function.Injective (fun z : Fin m×TripleBoxIndex => blockCoordinate (z.1.val,z.2)) := by
      intro x y he
      obtain ⟨h₁,h₂⟩ := Prod.mk.inj (blockCoordinate_injective he)
      exact Prod.ext (Fin.ext h₁) h₂
    simpa only [μ,ν,X,pathPauliDisorderLaw,Measure.infinitePi_eq_pi] using disjoint_window_law (gaussianReal 0 1) _ hi
  have hcard (ω : PathPauliDisorder) : sampleCount B (X ω)=(goodBoxes q δ ω m).card := by
    have hb (i : Fin m) : X ω i∈B ↔ goodBox q δ ω i.val := by
      simp only [B,Set.mem_univ_pi,goodBox,X]
    apply card_bij (fun i _ => i.val)
    · intro i hi
      exact mem_filter.mpr ⟨mem_range.mpr i.isLt,(hb i).mp (mem_filter.mp hi).2⟩
    · intro i _ j _ hij
      exact Fin.ext hij
    · intro j hj
      obtain ⟨hl,hg⟩ := mem_filter.mp hj
      let i : Fin m := ⟨j,mem_range.mp hl⟩
      exact ⟨i,mem_filter.mpr ⟨mem_univ _,(hb i).mpr hg⟩,rfl⟩
  let E := {x : Fin m→(TripleBoxIndex→ℝ) | (sampleCount B x:ℝ)≤p*m/4 ∨ 4*(p*m)≤(sampleCount B x:ℝ)}
  have hsub : {ω | ((goodBoxes q δ ω m).card:ℝ)≤p*m/4}⊆X ⁻¹' E := by
    intro ω h
    exact Or.inl (by rwa [hcard])
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  apply ((measureReal_mono (μ:=pathPauliDisorderLaw) hsub).trans
    (ENNReal.toReal_mono (measure_ne_top μ E) (hX.measure_preimage_le E))).trans
  have hp : ν.real B=p := rfl
  change μ.real E≤_
  simpa only [μ,E,Fintype.card_fin,hp] using relative_sample_tail (I:=Fin m) ν B hB

#print axioms few_triple_boxes
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
