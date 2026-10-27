import GaloisForLFunctions.ArithmeticPositiveDuality.EverySquareIntegrableWaveHasAVisibleSuccessor
import GaloisForLFunctions.HTGeometry.AbsolutelyContinuousMeasuresAreAutocorrelations
import GaloisForLFunctions.ArithmeticPositiveDuality.AFiniteArchimedeanSpectrumBlindsTheSuccessor

/-!
# Every density has a visible affine extension

A finite real measure with nonzero Lebesgue absolutely continuous part is
realized as the exact positive-dilation measure of a positive-definite state
on `Aff(ℚ)` with nonconstant successor. The density is realized by an inverse
L² Fourier transform and its real affine vector state. A translation-invariant
character integral carries the singular remainder without changing visibility.
-/

open Complex MeasureTheory Filter Set
open scoped ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Unitary archimedean characters are integrable against every finite measure. -/
lemma integrable_archChar_left (ν : Measure ℝ) [IsFiniteMeasure ν] (u : ℚ) :
    Integrable (fun γ => archChar γ u) ν := by
  have hc : Continuous (fun γ : ℝ => archChar γ u) := by unfold archChar; fun_prop
  exact (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun γ => (norm_archChar γ u).le)

/-- The translation-invariant affine state carrying a prescribed dilation measure. -/
def blindArchState (ν : Measure ℝ) (g : AffineGroupQ) : ℂ :=
  ∫ γ, archChar γ |affSlope g| ∂ν

/-- Integrating the character Gram identity gives positivity of the blind state. -/
lemma isPosDefOnGroup_blindArchState (ν : Measure ℝ) [IsFiniteMeasure ν] :
    IsPosDefOnGroup (blindArchState ν) := by
  intro N x c
  let V : ℝ → ℂ := fun γ => ∑ j, c j * archChar γ |affSlope (x j)|
  have hpt (γ : ℝ) :
      (∑ a, ∑ b, star (c a) * archChar γ |affSlope ((x a)⁻¹ * x b)| * c b) =
        (Complex.normSq (V γ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [V, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [archChar_abs_slope_inv_mul, map_mul, Complex.star_def]
    ring
  refine ⟨∫ γ, Complex.normSq (V γ) ∂ν,
    integral_nonneg fun γ => Complex.normSq_nonneg _, ?_⟩
  calc (∑ a, ∑ b, star (c a) * blindArchState ν ((x a)⁻¹ * x b) * c b)
      = ∫ γ, ∑ a, ∑ b, star (c a) * archChar γ |affSlope ((x a)⁻¹ * x b)| * c b ∂ν := by
        rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
          ((integrable_archChar_left ν _).const_mul _).mul_const _]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finsetSum _ fun b _ =>
          ((integrable_archChar_left ν _).const_mul _).mul_const _]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [blindArchState, integral_mul_const, integral_const_mul]
    _ = ∫ γ, (Complex.normSq (V γ) : ℂ) ∂ν :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = ((∫ γ, Complex.normSq (V γ) ∂ν : ℝ) : ℂ) := integral_ofReal

/-- The blind state retains the prescribed positive-dilation coefficients. -/
lemma blindArchState_dilation (ν : Measure ℝ) (u : ℚˣ) (hu : 0 < (u : ℚ)) :
    blindArchState ν (dilation u) = ∫ γ, archChar γ u ∂ν := by
  rw [blindArchState, affSlope_dilation, abs_of_pos hu]

/-- Every translation has the same coefficient in the blind state. -/
lemma blindArchState_translation (ν : Measure ℝ) (b : ℚ) :
    blindArchState ν (translation b) = (ν.real univ : ℂ) := by
  simp only [blindArchState, affSlope_translation, abs_one, archChar_one,
    integral_const, Complex.real_smul, mul_one]

/-- Logarithmic dilation characters use the usual characteristic-function convention. -/
lemma integral_archChar_eq_charFun (ν : Measure ℝ) (u : ℚ) :
    (∫ γ, archChar γ u ∂ν) = charFun ν (Real.log u) := by
  rw [charFun_apply_real]
  apply integral_congr_ae
  exact Eventually.of_forall fun γ => by
    simp only [archChar, mul_comm, mul_assoc]

/-- Every nonzero finite absolutely continuous dilation measure has a nonblind affine extension. -/
theorem exists_nonblind_affine_extension_of_absolutelyContinuous
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≪ volume) (hmass : 0 < ν.real univ) :
    ∃ φ : AffineGroupQ → ℂ, IsPosDefOnGroup φ ∧
      (∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∫ γ, archChar γ u ∂ν) ∧
      ¬ ∃ α : ℂ, ∀ b : ℚ, b ≠ 0 → φ (translation b) = α := by
  obtain ⟨H, hcorr, hnorm⟩ :=
    GaloisForLFunctions.HTGeometry.exists_L2_autocorrelation_eq_charFun ν hν
  obtain ⟨φ, hφ, hdil, hvis⟩ := successor_sees_L2_autocorrelation (Lp.memLp H)
    (by rw [hnorm]; exact hmass)
  refine ⟨φ, hφ, ?_, hvis⟩
  intro u hu
  rw [hdil u hu, hcorr, integral_archChar_eq_charFun]

/-- A nonzero absolutely continuous part suffices, with the full prescribed dilation measure. -/
theorem exists_nonblind_affine_extension_of_positive_ac_mass
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hmass : 0 < (volume.withDensity (ν.rnDeriv volume)).real univ) :
    ∃ φ : AffineGroupQ → ℂ, IsPosDefOnGroup φ ∧
      (∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∫ γ, archChar γ u ∂ν) ∧
      ¬ ∃ α : ℂ, ∀ b : ℚ, b ≠ 0 → φ (translation b) = α := by
  let νa := volume.withDensity (ν.rnDeriv volume)
  let νs := ν.singularPart volume
  have hsum : νa + νs = ν := Measure.rnDeriv_add_singularPart ν volume
  obtain ⟨φ, hφ, hdil, hvis⟩ := exists_nonblind_affine_extension_of_absolutelyContinuous
    νa (withDensity_absolutelyContinuous _ _) hmass
  refine ⟨fun g => φ g + blindArchState νs g,
    hφ.add (isPosDefOnGroup_blindArchState νs), ?_, ?_⟩
  · intro u hu
    change φ (dilation u) + blindArchState νs (dilation u) = _
    rw [hdil u hu, blindArchState_dilation νs u hu, ← hsum,
      integral_add_measure (integrable_archChar_left νa _) (integrable_archChar_left νs _)]
  · rintro ⟨α, hα⟩
    apply hvis
    refine ⟨α - (νs.real univ : ℂ), fun b hb => ?_⟩
    have h := hα b hb
    change φ (translation b) + blindArchState νs (translation b) = α at h
    rw [blindArchState_translation] at h
    exact eq_sub_iff_add_eq.mpr h

/-- Every finite measure with a nonzero Lebesgue absolutely continuous part admits a visible
positive-definite extension to the rational affine group. -/
theorem exists_nonblind_affine_extension_of_ac_part_ne_zero
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : volume.withDensity (ν.rnDeriv volume) ≠ 0) :
    ∃ φ : AffineGroupQ → ℂ, IsPosDefOnGroup φ ∧
      (∀ u : ℚˣ, 0 < (u : ℚ) → φ (dilation u) = ∫ γ, archChar γ u ∂ν) ∧
      ¬ ∃ α : ℂ, ∀ b : ℚ, b ≠ 0 → φ (translation b) = α := by
  apply exists_nonblind_affine_extension_of_positive_ac_mass ν
  exact ENNReal.toReal_pos (fun hz => hν (Measure.measure_univ_eq_zero.mp hz))
    (measure_ne_top _ _)

#print axioms isPosDefOnGroup_blindArchState
#print axioms exists_nonblind_affine_extension_of_positive_ac_mass
#print axioms exists_nonblind_affine_extension_of_ac_part_ne_zero

end GaloisForLFunctions.ArithmeticPositiveDuality
