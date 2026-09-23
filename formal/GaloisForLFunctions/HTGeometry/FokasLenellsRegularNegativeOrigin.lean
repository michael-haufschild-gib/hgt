import GaloisForLFunctions.HTGeometry.FokasLenellsContourGaugeScattering

/-!
# Actual normalized reflection weights on the negative squared-spectral ray

The proved contour gauge exposes the swapped transmission factors.
The lower weight still has a finite origin limit for arbitrary Schwartz
data; the upper weight retains exactly the compatibility residue.
-/

open Complex Matrix MeasureTheory Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Exact negative-ray weighted formulas, with the transmission exchange kept explicit. -/
theorem regularSecondInverseReflection_negative_exp_factor (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    regularSecondInverseReflection q false (-((Real.exp κ)^(2 : ℕ))) =
      2*I*(Real.exp κ : ℂ)^(2 : ℕ)*originWeightedReflection (twistedPotential q) ((Real.exp κ)^(2 : ℕ)) /
        regularScatteringMatrix q (-((Real.exp κ)^(2 : ℕ))) 0 0 ∧
    regularSecondInverseReflection q true (-((Real.exp κ)^(2 : ℕ))) =
      I*originWeightedReflection (twistedPotential q) ((Real.exp κ)^(2 : ℕ)) /
        (2*regularScatteringMatrix q (-((Real.exp κ)^(2 : ℕ))) 1 1) := by
  have hS := regularScatteringMatrix_negative_exp q κ
  have hd0 : regularScatteringMatrix q (-((Real.exp κ)^(2 : ℕ))) 0 0 = reverseTransmission (twistedPotential q) κ := by
    rw [hS]
    rfl
  have hd1 : regularScatteringMatrix q (-((Real.exp κ)^(2 : ℕ))) 1 1 = transmission (twistedPotential q) κ := by
    rw [hS]
    rfl
  have he : (Real.exp κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero κ)
  constructor
  · simp only [regularSecondInverseReflection, Bool.false_eq_true, ↓reduceIte,
      regularReflectionCoefficient, originWeightedReflection_exp, hd0]
    rw [hS]
    change (2*I*(Real.exp κ : ℂ)*reflectionAmplitude (twistedPotential q) κ /
      reverseTransmission (twistedPotential q) κ) / (↑(-((Real.exp κ)^(2 : ℕ))) : ℂ)^(2 : ℕ) = _
    simp only [Complex.ofReal_neg, Complex.ofReal_pow, neg_sq]
    by_cases ht : reverseTransmission (twistedPotential q) κ = 0
    · simp [ht]
    · field_simp
  · simp only [regularSecondInverseReflection, ↓reduceIte,
      regularReverseReflectionCoefficient, originWeightedReflection_exp, hd1]
    rw [hS]
    change ((I*reflectionAmplitude (twistedPotential q) κ/(2*(Real.exp κ : ℂ))) /
      transmission (twistedPotential q) κ) / (↑(-((Real.exp κ)^(2 : ℕ))) : ℂ)^(2 : ℕ) = _
    simp only [Complex.ofReal_neg, Complex.ofReal_pow, neg_sq]
    by_cases ht : transmission (twistedPotential q) κ = 0
    · simp [ht]
    · field_simp

private theorem regular_second_inverse_negative_factor (q : SchwartzMap ℝ ℂ) (z : ℝ) (hz : 0 < z) :
    regularSecondInverseReflection q false (-z) =
      2*I*(z : ℂ)*originWeightedReflection (twistedPotential q) z / regularScatteringMatrix q (-z) 0 0 ∧
    regularSecondInverseReflection q true (-z) =
      I*originWeightedReflection (twistedPotential q) z / (2*regularScatteringMatrix q (-z) 1 1) := by
  have hh := regularSecondInverseReflection_negative_exp_factor q (Real.log (Real.sqrt z))
  rw [Real.exp_log (Real.sqrt_pos.mpr hz), Real.sq_sqrt hz.le] at hh
  have hs : (Real.sqrt z : ℂ)^(2 : ℕ) = (z : ℂ) := by exact_mod_cast Real.sq_sqrt hz.le
  rwa [hs] at hh

private theorem negative_transmission_tendsto (q : SchwartzMap ℝ ℂ) (i : Fin 2) :
    Tendsto (fun z : ℝ => regularScatteringMatrix q (-z) i i) (𝓝[>] 0) (𝓝 1) := by
  have hn : Tendsto (fun z : ℝ => -z) (𝓝[>] 0) (𝓝 0) := by
    have hi : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [neg_zero] using hi.neg
  exact (regularTransmission_diagonal_tendsto_zero q i).comp hn

/-- The lower weight has the same finite limit from the negative side for every Schwartz profile. -/
theorem regularSecondInverseReflection_lower_negative_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun z : ℝ => regularSecondInverseReflection q false (-z))
      (𝓝[>] 0) (𝓝 (-4*compatibilityMoment q)) := by
  have hh := ((originWeightedReflection_mul_coordinate_tendsto (twistedPotential q)).const_mul (2*I)).div
    (negative_transmission_tendsto q 0) one_ne_zero
  change Tendsto (fun z : ℝ => (2*I*((z : ℂ)*originWeightedReflection (twistedPotential q) z)) /
    regularScatteringMatrix q (-z) 0 0) (𝓝[>] 0) (𝓝 ((2*I*(2*compatibilityMoment (twistedPotential q)))/1)) at hh
  have hc : (2*I*(2*compatibilityMoment (twistedPotential q)))/1 = -4*compatibilityMoment q := by
    rw [compatibilityMoment_twistedPotential]
    ring_nf
    simp
  rw [hc] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [(regular_second_inverse_negative_factor q z hz).1]
  ring

/-- Written in positive distance to the origin, the negative-ray upper residue is minus the same compatibility moment. -/
theorem regularSecondInverseReflection_upper_negative_residue_tendsto (q : SchwartzMap ℝ ℂ) :
    Tendsto (fun z : ℝ => (z : ℂ)*regularSecondInverseReflection q true (-z))
      (𝓝[>] 0) (𝓝 (-compatibilityMoment q)) := by
  have hh := ((originWeightedReflection_mul_coordinate_tendsto (twistedPotential q)).const_mul I).div
    ((negative_transmission_tendsto q 1).const_mul (2 : ℂ)) (by norm_num)
  change Tendsto (fun z : ℝ => (I*((z : ℂ)*originWeightedReflection (twistedPotential q) z)) /
    (2*regularScatteringMatrix q (-z) 1 1)) (𝓝[>] 0) (𝓝 ((I*(2*compatibilityMoment (twistedPotential q)))/(2*1))) at hh
  have hc : (I*(2*compatibilityMoment (twistedPotential q)))/(2*1) = -compatibilityMoment q := by
    rw [compatibilityMoment_twistedPotential]
    ring_nf
    simp
  rw [hc] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [(regular_second_inverse_negative_factor q z hz).2]
  ring

/-- The negative-ray upper channel has a finite limit exactly on the same compatibility locus. -/
theorem regularSecondInverseReflection_upper_negative_finite_limit_iff (q : SchwartzMap ℝ ℂ) :
    (∃ c : ℂ, Tendsto (fun z : ℝ => regularSecondInverseReflection q true (-z)) (𝓝[>] 0) (𝓝 c)) ↔
      compatibilityMoment q = 0 := by
  constructor
  · rintro ⟨c,hc⟩
    have hz : Tendsto (fun z : ℝ => (z : ℂ)) (𝓝[>] 0) (𝓝 0) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have hh := hz.mul hc
    simp only [zero_mul] at hh
    have he := tendsto_nhds_unique (regularSecondInverseReflection_upper_negative_residue_tendsto q) hh
    exact neg_eq_zero.mp he
  · intro hm
    obtain ⟨c,hc⟩ := (originWeightedReflection_finite_limit_iff (twistedPotential q)).2
      ((compatibilityMoment_twistedPotential_zero_iff q).2 hm)
    refine ⟨I*c/2, ?_⟩
    have hh := (hc.const_mul I).div ((negative_transmission_tendsto q 1).const_mul (2 : ℂ)) (by norm_num)
    change Tendsto (fun z : ℝ => I*originWeightedReflection (twistedPotential q) z /
      (2*regularScatteringMatrix q (-z) 1 1)) (𝓝[>] 0) (𝓝 (I*c/(2*1))) at hh
    simp only [mul_one] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (regular_second_inverse_negative_factor q z hz).2.symm

end
end GaloisForLFunctions.HTGeometry.FokasLenells
