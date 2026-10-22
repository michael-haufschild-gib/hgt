import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenFourEffectiveSchur
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEffectiveCompensatedTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenCompensationRationalFamily

/-! # Explicit outer positivity for the complete corrected even rank-four source

The canonical coefficient and every coefficient in its proved rational band are
covered for physical centers at least six fifths, independently of aperture.
The remaining compact interior sign is not asserted here.
-/
namespace RHTower
noncomputable section

/-- The complete correction loses at most two over thirty to the fourth in twelfth-entry units. -/
theorem thetaCuspCenterCompensationSource_six_normalized_lower {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    -(2 : ℝ)/30^(4 : ℕ) ≤ thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)) := by
  have h := thetaCuspCenterCompensationSource_normalized_lower hq
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have heq : thetaCuspCenterCompensationSource x /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)) =
      (thetaCuspCenterCompensationSource x /
        (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(5 : ℕ))) /
          thetaCuspSingleAtomReflectionScale 1 x := by
    rw [div_div]
    congr 1
    ring
  rw [heq]
  apply (le_div_iff₀ hqp).mpr
  nlinarith only [h, hq]

/-- A uniform positive margin survives the full correction throughout its rational coefficient band. -/
theorem thetaCuspNativeEvenFourCompensated_effective_normalized_lower {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000000)
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    90000000 < (thetaCuspNativeEvenFourSchur x+C*thetaCuspCenterCompensationSource x) /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)) := by
  have hs := thetaCuspNativeEvenFourSchur_effective_normalized_lower hq
  have hg := thetaCuspCenterCompensationSource_six_normalized_lower hq
  have hm := mul_le_mul_of_nonneg_left hg hC0
  rw [add_div, mul_div_assoc]
  nlinarith only [hs, hm, hC1]

/-- Literal source positivity on the whole scale-thirty ray, with no omitted tail contribution. -/
theorem thetaCuspNativeEvenFourCompensated_posDef_of_thirty_le {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000000)
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  have hx : 0 < x := regimeOne_pos_of_six_le (by linarith)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hd : 0 < thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ) := by positivity
  have hm := thetaCuspNativeEvenFourCompensated_effective_normalized_lower hC0 hC1 hq
  have hp : 0 < (thetaCuspNativeEvenFourSchur x+C*thetaCuspCenterCompensationSource x) /
      (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^(6 : ℕ)) := by linarith
  rw [thetaCuspNativeEvenFourCompensated_posDef_iff hx.le]
  exact (div_pos_iff_of_pos_right hd).mp hp

/-- Six fifths is an explicit physical outer endpoint for the entire bounded coefficient family. -/
theorem thetaCuspNativeEvenFourCompensated_posDef_on_explicit_tail {C x : ℝ}
    (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000000) (hx : 6/5 ≤ x) :
    (thetaCuspNativeEvenFourCompensated C x).PosDef :=
  thetaCuspNativeEvenFourCompensated_posDef_of_thirty_le hC0 hC1
    (thirty_le_firstAtomScale_of_six_fifths_le hx)

/-- The actual source-selected coefficient satisfies the explicit complete-source tail sign. -/
theorem thetaCuspNativeEvenFourCanonical_posDef_on_explicit_tail :
    ∀ x : ℝ, 6/5 ≤ x →
      (thetaCuspNativeEvenFourCompensated thetaCuspNativeEvenCompensationCoefficient x).PosDef := by
  intro x hx
  exact thetaCuspNativeEvenFourCompensated_posDef_on_explicit_tail
    thetaCuspNativeEvenCompensationCoefficient_pos.le
    thetaCuspNativeEvenCompensationCoefficient_bounds.2.le hx

/-- The literal weighted matrix is positive past twelve fifths for every positive aperture. -/
theorem thetaCuspCenterCorrectedEvenFour_posDef_on_explicit_tail {a C r : ℝ}
    (ha : 0 < a) (hC0 : 0 ≤ C) (hC1 : C ≤ 3000000000000) (hr : 12/5 ≤ r) :
    (thetaCuspCenterCorrectedEvenFour a C r).PosDef := by
  apply thetaCuspCenterCorrectedEvenFour_posDef_of_source ha hC0 (by linarith)
  exact thetaCuspNativeEvenFourCompensated_posDef_on_explicit_tail hC0 hC1 (by linarith)

/-- Closed canonical weighted tail positivity, uniformly over every positive aperture. -/
theorem thetaCuspCenterCorrectedEvenFourCanonical_posDef_on_explicit_tail :
    ∀ a r : ℝ, 0 < a → 12/5 ≤ r →
      (thetaCuspCenterCorrectedEvenFour a thetaCuspNativeEvenCompensationCoefficient r).PosDef := by
  intro a r ha hr
  exact thetaCuspCenterCorrectedEvenFour_posDef_on_explicit_tail ha
    thetaCuspNativeEvenCompensationCoefficient_pos.le
    thetaCuspNativeEvenCompensationCoefficient_bounds.2.le hr

/-- Every possible failure in the rational family lies below the fixed outer endpoint six fifths. -/
theorem exists_thetaCuspEvenCompensation_rationalFamily_explicit_outer_gap :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 6/5 ∧ ∀ C x : ℝ,
      1000000000000 ≤ C → C ≤ 3000000000000 → 0 ≤ x → (x < δ ∨ 6/5 ≤ x) →
        (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  obtain ⟨δ, hδ, hnear⟩ := exists_thetaCuspEvenCompensation_rationalFamily_posDef_near_zero
  refine ⟨min δ (6/5), lt_min hδ (by norm_num), min_le_right _ _, fun C x hCL hCU hx h => ?_⟩
  rcases h with h | h
  · exact hnear C x hCL hCU hx ((lt_min_iff.mp h).1)
  · exact thetaCuspNativeEvenFourCompensated_posDef_on_explicit_tail (by linarith) hCU h

end
end RHTower
