import GaloisForLFunctions.HTGeometry.GaussianSmallBallLowerBound

/-! # Gaussian mass of a probe displaced by a longitudinal field -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.LongitudinalSpins
noncomputable section

/-- If one of every pair of field values separated by at most one succeeds,
the standard Gaussian success probability has a uniform positive floor. -/
theorem gaussian_paired_mass (A : Set ℝ) (hA : MeasurableSet A) {d : ℝ} (hd : d ∈ Icc 0 1)
    (h : ∀ x ∈ Icc (-1:ℝ) 0, x ∈ A ∨ x+d ∈ A) :
    gaussianDensityFloor/2 ≤ (gaussianReal 0 1).real A := by
  let B := A ∩ Icc (-1:ℝ) 1
  have hm : MeasurableSet B := hA.inter measurableSet_Icc
  have hf : volume B ≠ ⊤ := measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hs : Icc (-1:ℝ) 0 ⊆ B ∪ (fun x => x+d) ⁻¹' B := by
    intro x hx
    rcases h x hx with hy | hy
    · exact Or.inl ⟨hy,hx.1,hx.2.trans (by norm_num)⟩
    · exact Or.inr ⟨hy,by linarith only [hx.1,hd.1],by linarith only [hx.2,hd.2]⟩
  have hlen : (1:ℝ≥0∞) ≤ volume B+volume B := calc
    1 = volume (Icc (-1:ℝ) 0) := by rw [Real.volume_Icc]; norm_num
    _ ≤ _ := measure_mono hs
    _ ≤ volume B + volume ((fun x => x+d) ⁻¹' B) := measure_union_le _ _
    _ = _ := by rw [(measurePreserving_add_right volume d).measure_preimage hm.nullMeasurableSet]
  have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf,hf⟩) hlen
  rw [ENNReal.toReal_one,ENNReal.toReal_add hf hf] at hh
  have hg : ENNReal.ofReal gaussianDensityFloor*volume B ≤ gaussianReal 0 1 B := by
    rw [gaussianReal_of_var_ne_zero _ one_ne_zero,withDensity_apply _ hm,←setLIntegral_const]
    exact setLIntegral_mono' hm fun x hx => ENNReal.ofReal_le_ofReal
      (gaussianPDFReal_ge_floor (abs_le.mpr hx.2))
  have he := ENNReal.toReal_mono (measure_ne_top (gaussianReal 0 1) A)
    (hg.trans (measure_mono inter_subset_left))
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal gaussianDensityFloor_pos.le] at he
  exact (show gaussianDensityFloor/2 ≤ gaussianDensityFloor*(volume B).toReal by
    nlinarith only [mul_le_mul_of_nonneg_left hh gaussianDensityFloor_pos.le]).trans he

/-- A continuous probe which changes sign under the field shift has
order-one error from any fixed unit probe on a positive Gaussian fraction. -/
theorem gaussian_probe_moves {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : Continuous f) (X : E) (hX : ‖X‖=1) {d : ℝ} (hd : d ∈ Icc 0 1)
    (hs : ∀ x, f (x+d)= -f x) :
    gaussianDensityFloor/2 ≤ (gaussianReal 0 1).real {x | 1≤‖X-f x‖} := by
  apply gaussian_paired_mass _ (isClosed_le continuous_const (continuous_const.sub hf).norm).measurableSet hd
  intro x _
  by_cases hx : 1≤‖X-f x‖
  · exact Or.inl hx
  right
  change 1≤‖X-f (x+d)‖
  by_contra h
  have hb := norm_add_le (X-f x) (X-f (x+d))
  rw [hs,sub_neg_eq_add,show X-f x+(X+f x)=(2:ℝ) • X by rw [two_smul]; abel,
    norm_smul,hX] at hb
  rw [hs,sub_neg_eq_add] at h
  norm_num at hb
  linarith only [hb,lt_of_not_ge hx,lt_of_not_ge h]

#print axioms gaussian_probe_moves
end
end GaloisForLFunctions.HTGeometry.LongitudinalSpins
