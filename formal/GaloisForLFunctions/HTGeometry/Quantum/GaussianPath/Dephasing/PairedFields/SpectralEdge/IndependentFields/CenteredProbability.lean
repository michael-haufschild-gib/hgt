import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.RelativeCircuit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.SharedDraw

/-! # Probability of a centered circuit fit from independent perturbations -/

open Matrix MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
noncomputable section
private abbrev Config (N : ℕ) := Fin N → Bool
private def pack {n : ℕ} (x : Coeff n × Coeff n) : FieldPair n := fun i => (x.1 i,x.2 i)

private theorem pack_law (n : ℕ) :
    MeasurePreserving pack ((fieldLaw n).prod (fieldLaw n)) (pairLaw n) :=
  (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (PathLabel n)
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)).symm

private theorem preimage_real_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure ν] {f : X → Y}
    (hf : MeasurePreserving f μ ν) (S : Set Y) : μ.real (f ⁻¹' S) ≤ ν.real S := by
  have h := Measure.le_map_apply (μ:=μ) hf.measurable.aemeasurable S
  rw [hf.map_eq] at h
  exact ENNReal.toReal_mono (measure_ne_top _ _) h

/-- If a measurable set of Gaussian field pairs admits affine circuit fits,
its probability squared is at most the outer probability of a single centered
fit at twice the budget and tolerance. -/
theorem centered_capture {n s : ℕ} (R : Finset (Config (n+2))) (a b T ε : ℝ)
    {G : Set (FieldPair n)} (hm : MeasurableSet G) (hgood : G ⊆ edgeFit n s R a b T ε) :
    (pairLaw n).real G ≤ Real.sqrt ((pairLaw n).real
      (centeredFit n (s+s) R (Real.sqrt 2*(T*b)) (2*ε))) := by
  let μ := fieldLaw n
  let A := pack ⁻¹' G
  have hA : MeasurableSet A := hm.preimage (pack_law n).measurable
  let c := 1/Real.sqrt 2
  have hs₂ : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hc : c^2+(-c)^2=1 := by
    dsimp only [c]
    rw [neg_sq,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    norm_num
  let diff (y : Coeff n × Coeff n) := rotated c (-c) (pack y)
  have hdiff : MeasurePreserving diff (μ.prod μ) μ := (rotated_law n hc).comp (pack_law n)
  let Z (z : Coeff n × Coeff n × Coeff n) := pack (z.1,diff z.2)
  have hZ : MeasurePreserving Z (μ.prod (μ.prod μ)) (pairLaw n) :=
    (pack_law n).comp ((MeasurePreserving.id μ).prod hdiff)
  let S := centeredFit n (s+s) R (Real.sqrt 2*(T*b)) (2*ε)
  let J : Set (Coeff n × Coeff n × Coeff n) := {z | (z.1,z.2.1)∈A ∧ (z.1,z.2.2)∈A}
  have hJS : J ⊆ Z ⁻¹' S := by
    rintro ⟨h,g,k⟩ ⟨hg,hk⟩
    change pack (h,diff (g,k)) ∈ centeredFit n (s+s) R _ _
    rw [two_mul]
    apply centered_of_two_fits R a b T ε h g k _ _ _ (hgood hg) (hgood hk)
    intro i
    change Real.sqrt 2*(T*b)*(c*g i+ -c*k i)=T*b*(g i-k i)
    dsimp only [c]
    field_simp [hs₂.ne']
    ring
  have hj : ((μ.prod μ).real A)^2 ≤ (μ.prod (μ.prod μ)).real J := by
    rw [show (μ.prod (μ.prod μ)).real J=_ from shared_draw_success μ μ hA]
    exact le_add_of_nonneg_right (variance_nonneg ..)
  have hs := (hj.trans (measureReal_mono hJS)).trans (preimage_real_le hZ S)
  rw [←show (μ.prod μ).real A=(pairLaw n).real G from
    congrArg ENNReal.toReal ((pack_law n).measure_preimage hm.nullMeasurableSet)]
  exact (sq_le_sq₀ measureReal_nonneg (Real.sqrt_nonneg _)).mp (hs.trans_eq
    (Real.sq_sqrt (measureReal_nonneg (μ:=pairLaw n) (s:=S))).symm)

#print axioms centered_capture
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
