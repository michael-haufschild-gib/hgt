import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldBlocks
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.Packets

/-! # Probability that a path interval contains no weak bond -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- Nine pair couplings on the bond starting at site j. -/
def bondRow (ω : PathPauliDisorder) (j : ℕ) (q : Fin 3 × Fin 3) := ω (j,.inr q)

def weakRow (γ : ℝ) (ω : PathPauliDisorder) (j : ℕ) := ∀ q, |bondRow ω j q| ≤ γ

/-- Every bond with individually small coefficients is a weak interaction
in projective operator norm. -/
theorem edge_norm_of_weak {n : ℕ} (ω : PathPauliDisorder) (e : Fin (n+1))
    {γ : ℝ} (h : weakRow γ ω e.val) : ‖edgePart (pathPauliDisorderShell ω n) e‖ ≤ 9*γ := by
  apply (norm_sum_le _ _).trans
  calc _ ≤ ∑ _q : Fin 3 × Fin 3, γ := Finset.sum_le_sum fun q _ => by
         rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one]
         exact h q
       _ = _ := by simp [nsmul_eq_mul]

private def rowLaw : Measure ((Fin 3 × Fin 3) → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1
private instance : IsProbabilityMeasure rowLaw := by unfold rowLaw; infer_instance

private theorem distinct_rows {ι : Type*} (f : ι → ℕ) (hf : Function.Injective f) :
    MeasurePreserving (fun ω i => bondRow ω (f i)) pathPauliDisorderLaw (Measure.infinitePi fun _ : ι => rowLaw) := by
  let F (p : ι × (Fin 3 × Fin 3)) : ℕ × PathPauliDirections := (f p.1,.inr p.2)
  have hF : Function.Injective F := by
    intro x y h
    obtain ⟨hj,hq⟩ := Prod.mk.inj h
    exact Prod.ext (hf hj) (Sum.inr.inj hq)
  let ν : Measure ((ι × (Fin 3 × Fin 3)) → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1
  have hR : MeasurePreserving (fun ω p => ω (F p)) pathPauliDisorderLaw ν :=
    ⟨measurable_pi_lambda _ (fun _ => measurable_pi_apply _),Measure.map_infinitePi_infinitePi_of_inj hF⟩
  have hC : MeasurePreserving (MeasurableEquiv.curry ι (Fin 3 × Fin 3) ℝ) ν
      (Measure.infinitePi fun _ : ι => rowLaw) :=
    ⟨(MeasurableEquiv.curry ..).measurable,Measure.infinitePi_map_curry (fun _ _ => gaussianReal 0 1)⟩
  exact hC.comp hR

/-- For every positive strength threshold, each tested bond contributes
one identical factor strictly below one to the probability of missing
all weak bonds. The selected indices can be anywhere in the chain. -/
theorem gaussian_weak_strip_mass {γ : ℝ} (hγ : 0 < γ) :
    ∃ q ∈ Ico (0:ℝ) 1, 1-q=((gaussianReal 0 1).real (Icc (-γ) γ))^9 ∧
      ∀ (L : ℕ) (f : Fin L → ℕ), Function.Injective f →
      pathPauliDisorderLaw.real {ω | ∀ i, ¬weakRow γ ω (f i)}=q^L := by
  let B : Set ((Fin 3 × Fin 3) → ℝ) := univ.pi fun _ => Icc (-γ) γ
  have hB : MeasurableSet B := MeasurableSet.pi (Set.to_countable _) fun _ _ => measurableSet_Icc
  have hpos : 0 < rowLaw B := by
    simp only [rowLaw,B,Measure.infinitePi_eq_pi,Measure.pi_pi]
    rw [pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => (gaussianReal_Icc_pos (neg_lt_self hγ)).ne'
  have hq : rowLaw.real Bᶜ < 1 := by
    have hp := ENNReal.toReal_pos hpos.ne' (measure_ne_top rowLaw B)
    rw [measureReal_def,measure_compl hB (measure_ne_top _ _),measure_univ,
      ENNReal.toReal_sub_of_le (prob_le_one) ENNReal.one_ne_top,ENNReal.toReal_one]
    linarith only [hp]
  refine ⟨rowLaw.real Bᶜ,⟨measureReal_nonneg,hq⟩,?_,?_⟩
  · rw [measureReal_def,measure_compl hB (measure_ne_top _ _),measure_univ,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,ENNReal.toReal_one,sub_sub_cancel]
    simp only [measureReal_def,rowLaw,B,Measure.infinitePi_eq_pi,Measure.pi_pi,
      Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,ENNReal.toReal_pow]
  intro L f hf
  let A : Set (Fin L → (Fin 3 × Fin 3) → ℝ) := univ.pi fun _ => Bᶜ
  have hA : MeasurableSet A := MeasurableSet.pi (Set.to_countable _) fun _ _ => hB.compl
  have hmem (x : (Fin 3 × Fin 3) → ℝ) : x∈B ↔ ∀ j, |x j|≤γ := by
    simp only [B,Set.mem_univ_pi,Set.mem_Icc,abs_le]
  have he : {ω | ∀ i, ¬weakRow γ ω (f i)}=(fun ω i => bondRow ω (f i)) ⁻¹' A := by
    ext ω
    simp only [A,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_univ_pi,Set.mem_compl_iff,hmem,weakRow]
  rw [he,measureReal_def,(distinct_rows f hf).measure_preimage hA.nullMeasurableSet,
    Measure.infinitePi_eq_pi,Measure.pi_pi,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ENNReal.toReal_pow,measureReal_def]

/-- Each extra tested bond multiplies the missed-guard probability by
the same number strictly less than one. -/
theorem gaussian_weak_strip {γ : ℝ} (hγ : 0 < γ) :
    ∃ q ∈ Ico (0:ℝ) 1, ∀ (L : ℕ) (f : Fin L → ℕ), Function.Injective f →
      pathPauliDisorderLaw.real {ω | ∀ i, ¬weakRow γ ω (f i)}=q^L := by
  obtain ⟨q,hq,_,h⟩ := gaussian_weak_strip_mass hγ
  exact ⟨q,hq,h⟩

#print axioms gaussian_weak_strip
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
