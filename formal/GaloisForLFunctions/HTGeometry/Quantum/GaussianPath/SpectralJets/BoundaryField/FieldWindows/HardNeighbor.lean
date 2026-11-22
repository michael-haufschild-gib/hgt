import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldWindows.InverseTime
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.CrossingDates
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.ShortWord
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion
import GaloisForLFunctions.HTGeometry.ObserverProfileStability

/-! # Scalar and near-Hilbert hard endpoints at one date in one field interval -/
open MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
noncomputable section
private abbrev Reg (k : ℕ) := Matrix (Fin (k+3)→Bool) (Fin (k+3)→Bool) ℂ

/-- At time t the last Pauli field has Lipschitz constant |t| in the
distance to every physical gate budget. -/
theorem field_distance_le (ω : PathPauliDisorder) (k P : ℕ) (b z t : ℝ) :
    let H (v : ℝ) : selfAdjoint (Reg k) := ⟨boundaryHamiltonian ω k v,(boundaryHermitian ω k v).isSelfAdjoint⟩
    orbitCircuitDistance (H b) P t ≤ orbitCircuitDistance (H z) P t+ |t| * |b-z| := by
  intro H
  have hsub : (H b).val-(H z).val=((b-z:ℝ):ℂ) • SpinExtension.lastPauli (k+2) 2 := by
    dsimp only [H,boundaryHamiltonian]
    rw [add_sub_add_left_eq_sub,Complex.ofReal_sub,sub_smul]
  have h := norm_unitaryEvolution_sub_le _ _ (H b).2 (H z).2 t
  rw [hsub,norm_smul,SpinExtension.lastPauli_word,norm_finitePauliMatrix,mul_one,Complex.norm_real,Real.norm_eq_abs] at h
  apply (Metric.infDist_le_infDist_add_dist (y:=unitaryEvolution (H z).val t)).trans
  exact add_le_add le_rfl (by simpa only [dist_eq_norm] using h)

private theorem return_transfer {k P : ℕ} (H : selfAdjoint (Reg k)) (T σ : ℝ) {e r : ℝ}
    (h : HasProjectiveCircuitApproximation (k+3) e 0 (unitaryEvolution H.val (T-σ)))
    (hfit : HasProjectiveCircuitApproximation (k+3) r P (unitaryEvolution H.val T)) :
    orbitCircuitDistance H P σ ≤ e+r := by
  have hp := LocalPatches.approx_product (unitaryEvolution_mem_unitary H.2 T) (h.neg_time H) hfit
  have he := unitaryEvolution_sub_mul H σ T
  rw [show σ-T= -(T-σ) by ring] at he
  rw [he,zero_add] at hp
  exact (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp hp

/-- A scalar return at T−σ transfers a robust crossing at σ to a
hard endpoint at T, after changing the field by at most 2M/T. -/
theorem hard_neighbors_of_crossing (ω : PathPauliDisorder) (k P : ℕ) (b σ M : ℝ)
    (hσ : 0 < σ) (hM : 1 ≤ M)
    (he : orbitCircuitDistance ⟨boundaryHamiltonian ω k b,(boundaryHermitian ω k b).isSelfAdjoint⟩ P σ=9/80)
    (hnear : ∀ T : ℝ, M^2≤T → ∃ z∈Icc b (b+M/T), HasProjectiveCircuitApproximation (k+3) (1/400:ℝ) 0
        (unitaryEvolution (boundaryHamiltonian ω k z) T)) :
    let H (z : ℝ) : selfAdjoint (Reg k) := ⟨boundaryHamiltonian ω k z,(boundaryHermitian ω k z).isSelfAdjoint⟩
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
        (∃ z∈Icc b (b+C/T), orbitCircuitDistance (H z) 0 T ≤ 1/20) ∧
        ∃ z∈Icc b (b+C/T), 21/200 < orbitCircuitDistance (H z) P T := by
  intro H
  have hm := zero_lt_one.trans_le hM
  refine ⟨2*M,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (σ+M^2),eventually_ge_atTop (2*σ),
    eventually_ge_atTop (σ+400*σ*M)] with T h1 h2 h3
  have ht : 0 < T := (by linarith only [hσ] : 0 < 2*σ).trans_le h2
  have hτ : 0 < T-σ := by linarith only [hσ,h2]
  obtain ⟨z,hz,hfit⟩ := hnear T (by linarith only [h1,hσ])
  have hW : M/T ≤ 2*M/T := div_le_div_of_nonneg_right (by linarith only [hm]) ht.le
  have hdist := (hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mp hfit
  refine ⟨⟨z,⟨hz.1,hz.2.trans (add_le_add_right hW b)⟩,hdist.trans (by norm_num)⟩,?_⟩
  obtain ⟨u,hu,hret⟩ := hnear (T-σ) (by linarith only [h1])
  have hwidth : M/(T-σ) ≤ 2*M/T := (div_le_div_iff₀ hτ ht).mpr (by
    linarith only [mul_le_mul_of_nonneg_left h2 hm.le])
  refine ⟨u,⟨hu.1,hu.2.trans (add_le_add_right hwidth b)⟩,?_⟩
  by_contra! hbad
  have hpert := field_distance_le ω k P b u σ
  rw [abs_of_pos hσ,abs_of_nonpos (sub_nonpos.mpr hu.1)] at hpert
  have hgap := return_transfer (H u) T σ hret
    ((hasProjectiveCircuitApproximation_iff_infDist _ P _).mpr hbad)
  have hrad : u-b ≤ M/(T-σ) := by linarith only [hu.2]
  have hr : σ*(u-b) ≤ 1/400 := calc
    _ ≤ σ*(M/(T-σ)) := mul_le_mul_of_nonneg_left hrad hσ.le
    _ ≤ _ := by rw [←mul_div_assoc]; apply (div_le_iff₀ hτ).mpr; linarith only [h3]
  change orbitCircuitDistance (H b) P σ=9/80 at he
  change orbitCircuitDistance (H b) P σ ≤ orbitCircuitDistance (H u) P σ+σ* -(b-u) at hpert
  linarith only [hpert,he,hgap,hr]

/-- At every sufficiently late date, within C/T on the same side of
one terminal coupling there is both a scalar setting at error 1/20
and a setting beyond the near-Hilbert budget even at error 21/200. -/
theorem gaussian_inverse_time_hard_neighbor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ∃ B : Set ℝ, B.Countable ∧ ∀ b∉B,
      let H (z : ℝ) : selfAdjoint (Reg k) := ⟨boundaryHamiltonian ω k z,(boundaryHermitian ω k z).isSelfAdjoint⟩
      let P := nearHilbertContinuousCircuitBudget (k+3)
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
        (∃ z∈Icc b (b+C/T), orbitCircuitDistance (H z) 0 T ≤ 1/20) ∧
        ∃ z∈Icc b (b+C/T), 21/200 < orbitCircuitDistance (H z) P T := by
  filter_upwards [gaussian_inverse_time_scalar_field,gaussian_boundary_crossing_return_dates] with ω hf hh
  filter_upwards [hh] with k hk
  obtain ⟨B,hB,h⟩ := hf k
  obtain ⟨A,hA,hhard⟩ := hk ∅ countable_empty
  refine ⟨B∪A,hB.union hA,?_⟩
  intro b hb H P
  have hsmall : (1/400:ℝ)∈Ioo (0:ℝ) (Real.sqrt 2) := ⟨by norm_num,by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]⟩
  obtain ⟨M,hM,hnear⟩ := h b (fun h => hb (Or.inl h)) (1/400) hsmall
  obtain ⟨σ,hσ,he,_,_⟩ := hhard b (fun h => hb (Or.inr h))
  exact hard_neighbors_of_crossing ω k P b σ M hσ hM he hnear

#print axioms gaussian_inverse_time_hard_neighbor
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
