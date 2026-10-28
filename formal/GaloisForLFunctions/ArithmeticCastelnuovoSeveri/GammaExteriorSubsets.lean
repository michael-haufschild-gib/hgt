import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaPairRemainder

/-!
# Gamma averaging loss on arbitrary exterior subsets

Removing the two boundary points does not change a Lebesgue integral. Hence
any exterior carrier inherits the uniform first-moment bound for the full row.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals

private theorem exterior_subset_ae {a b : ℝ} {F : Set ℝ} (hF : F ⊆ (Ioo a b)ᶜ) :
    F ≤ᵐ[volume] (Iio a ∪ Ioi b : Set ℝ) := by
  have hne : ∀ᵐ y ∂volume, y ≠ a ∧ y ≠ b := by
    have ha : ∀ᵐ y ∂volume, y ≠ a := by rw [ae_iff]; simp
    have hb : ∀ᵐ y ∂volume, y ≠ b := by rw [ae_iff]; simp
    exact ha.and hb
  filter_upwards [hne] with y hy
  intro hyF
  have hout := hF hyF
  by_cases hya : y < a
  · exact Or.inl hya
  · right
    have hay : a < y := lt_of_le_of_ne (le_of_not_gt hya) (Ne.symm hy.1)
    have hby : b ≤ y := le_of_not_gt (fun hyb => hout ⟨hay, hyb⟩)
    exact lt_of_le_of_ne hby (Ne.symm hy.2)

/-- Every exterior subset inherits the full interval averaging-loss bound. -/
theorem gamma_interval_exterior_subset_defect_le {a b : ℝ} (hab : a < b)
    (hw : b - a ≤ 1) {F : Set ℝ} (hF : F ⊆ (Ioo a b)ᶜ) :
    (∫⁻ x in Ioo a b, ∫⁻ y in F, gammaIntervalRowDefect a b x y) ≤
      ENNReal.ofReal (Real.exp (1 / 2) * (b - a)) := by
  refine (lintegral_mono fun x => lintegral_mono'
    (Measure.restrict_mono' (exterior_subset_ae hF) le_rfl) le_rfl).trans
      (gamma_interval_row_defect_le hab hw)

/-- The actual kernel on any exterior subset is finite, with its explicit width-tail bound. -/
theorem gamma_interval_exterior_subset_kernel_le {a b : ℝ} (hab : a < b)
    (hw : b - a ≤ 1) {F : Set ℝ} (hF : F ⊆ (Ioo a b)ᶜ) :
    (∫⁻ x in Ioo a b, ∫⁻ y in F, ENNReal.ofReal (archLevyDensity |y - x|)) ≤
      ENNReal.ofReal ((b - a) * (2 * gammaTailMass (b - a) + Real.exp (1 / 2))) := by
  exact (lintegral_mono fun x => lintegral_mono'
    (Measure.restrict_mono' (exterior_subset_ae hF) le_rfl) le_rfl).trans
      (gamma_interval_exterior_kernel_le hab hw)

/-- The weighted far charge is bounded by the actual finite exterior kernel. -/
theorem gamma_interval_far_charge_le {a b : ℝ} (hab : a < b)
    (hw : b - a ≤ 1) {F : Set ℝ} (hF : F ⊆ (Ioo a b)ᶜ) (q : ℝ) :
    (∫⁻ y in F, ENNReal.ofReal ((b - a) * q ^ 2) * gammaFarCharge a b y) ≤
      ENNReal.ofReal (q ^ 2 * ((b - a) *
        (2 * gammaTailMass (b - a) + Real.exp (1 / 2)))) := by
  have hfar : ENNReal.ofReal (b - a) * (∫⁻ y in F, gammaFarCharge a b y) ≤
      ∫⁻ x in Ioo a b, ∫⁻ y in F, ENNReal.ofReal (archLevyDensity |y - x|) := by
    rw [gamma_interval_set_kernel_eq_defect_add_far]
    exact le_add_self
  calc
    _ = ENNReal.ofReal (q ^ 2) *
        (ENNReal.ofReal (b - a) * ∫⁻ y in F, gammaFarCharge a b y) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ENNReal.ofReal_mul (sub_pos.mpr hab).le]
      ring
    _ ≤ ENNReal.ofReal (q ^ 2) * ENNReal.ofReal
        ((b - a) * (2 * gammaTailMass (b - a) + Real.exp (1 / 2))) :=
      mul_le_mul_right (hfar.trans (gamma_interval_exterior_subset_kernel_le hab hw hF)) _
    _ = _ := (ENNReal.ofReal_mul (sq_nonneg q)).symm

/-- Each touching interaction costs one full row loss and one finite far-charge rectangle. -/
theorem gammaIntervalPairDefect_le_boundary {a b c d : ℝ} (hab : a < b)
    (hw : b - a ≤ 1) (hsep : b ≤ c ∨ d ≤ a) :
    gammaIntervalPairDefect a b c d ≤
      ENNReal.ofReal (Real.exp (1 / 2) * (b - a)) +
        ENNReal.ofReal ((b - a) * (d - c) * archLevyDensity (b - a)) := by
  have hsub : Ioo c d ⊆ (Ioo a b)ᶜ := by
    intro y hy hyI
    rcases hsep with hr | hl
    · exact (not_lt_of_ge (hr.trans hy.1.le)) hyI.2
    · exact (not_lt_of_ge (hy.2.le.trans hl)) hyI.1
  exact (tsub_le_self.trans (gammaIntervalKernel_le_defect_add_width hab hsep)).trans
    (add_le_add (gamma_interval_exterior_subset_defect_le hab hw hsub) le_rfl)

#print axioms gamma_interval_exterior_subset_defect_le
#print axioms gamma_interval_exterior_subset_kernel_le
#print axioms gamma_interval_far_charge_le
#print axioms gammaIntervalPairDefect_le_boundary

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeanZeroIntervals
