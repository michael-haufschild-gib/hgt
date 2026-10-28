import GaloisForLFunctions.ArithmeticIndexDescent.ArithmeticSectionsHaveOnlyPresentationRadicals

/-!
# The unused width fraction remains as arithmetic reserve

The full-width section theorem may spend its entire weighted reserve on the two
pole moments. Keeping the pole cost as `w N (exp w + 1)` shows what remains at
smaller widths. Using a fraction `a` of the allowed width retains `(1-a)/8` of
the actual weighted profile mass in the original complete Weil form.
-/

open MeasureTheory RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-- The pole cost before rounding it to the full section reserve. -/
def sectionPoleCost (N : ℕ) (w : ℝ) : ℝ := w * N * (Real.exp w + 1)

/-- Weighted pole Cauchy–Schwarz retains the actual width-dependent cost. -/
theorem neg_sectionPoleCost_mul_reserve_le_poleProduct
    {G : ℕ → ℝ → ℝ} {N : ℕ} {w : ℝ}
    (hg : ∀ n, Continuous (G n)) (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0)
    (hN : 1 ≤ N) (hw : 0 ≤ w) :
    -(sectionPoleCost N w * sectionReserve N G) ≤
      2 * poleA (arithmeticSection N G) * poleB (arithmeticSection N G) := by
  let A := poleA (arithmeticSection N G)
  let B := poleB (arithmeticSection N G)
  let L := 1 + Real.log N
  let D := sectionReserve N G
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < L := by
    dsimp only [L]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Real.log_natCast_nonneg N)
  have hA := mul_le_mul_of_nonneg_left (poleA_arithmeticSection_sq_le hg hs hN hw)
    (show 0 ≤ L / N by positivity)
  have hB := mul_le_mul_of_nonneg_left (poleB_arithmeticSection_sq_le (N := N) hg hs hw)
    (show 0 ≤ (N : ℝ) / L by positivity)
  have heA : L / N * ((w * Real.exp w * ((N : ℝ) ^ 2 / L)) * D) =
      w * N * Real.exp w * D := by field_simp
  have heB : (N : ℝ) / L * ((w * L) * D) = w * N * D := by field_simp
  change L / N * A ^ 2 ≤ L / N * ((w * Real.exp w * ((N : ℝ) ^ 2 / L)) * D) at hA
  change (N : ℝ) / L * B ^ 2 ≤ (N : ℝ) / L * ((w * L) * D) at hB
  rw [heA] at hA
  rw [heB] at hB
  have hYoung : 0 ≤ L / N * A ^ 2 + 2 * A * B + (N : ℝ) / L * B ^ 2 := by
    have he : (L * A + N * B) ^ 2 / (L * N) =
        L / N * A ^ 2 + 2 * A * B + (N : ℝ) / L * B ^ 2 := by field_simp; ring
    rw [← he]
    positivity
  change -(w * N * (Real.exp w + 1) * D) ≤ 2 * A * B
  nlinarith only [hYoung, hA, hB]

/-- The original full source form retains its weighted reserve minus the exact pole charge. -/
theorem weilPair_arithmeticSection_ge_unused_reserve
    {G : ℕ → ℝ → ℝ} {N : ℕ} {w : ℝ}
    (hg : ∀ n, ContDiff ℝ 2 (G n)) (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0)
    (hN : 1 ≤ N) (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N) :
    (∫ u, arithmeticSection N G u ^ 2) +
        (1 / 8 - sectionPoleCost N w) * sectionReserve N G ≤
      weilPair (arithmeticSection N G) (arithmeticSection N G) := by
  have hM := markovEnergy_arithmeticSection_ge_reserve hg hs hN hw0 hw
  have hP := neg_sectionPoleCost_mul_reserve_le_poleProduct
    (fun n => (hg n).continuous) hs hN hw0.le
  have hW := weilPair_eq_markovEnergy_add_poleProduct
    (show arithmeticSection N G ∈ realTests from
      ⟨contDiff_arithmeticSection hg N, hasCompactSupport_arithmeticSection hs N⟩)
  change weilPair (arithmeticSection N G) (arithmeticSection N G) =
    markovEnergy (fun u => (arithmeticSection N G u : ℂ)) +
      2 * poleA (arithmeticSection N G) * poleB (arithmeticSection N G) at hW
  linarith only [hM, hP, hW]

/-- A width fraction pays at most the same fraction of the full pole reserve. -/
theorem sectionPoleCost_le_width_fraction {N : ℕ} (hN : 1 ≤ N)
    {w a : ℝ} (hw0 : 0 < w) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hw : w ≤ (a * fullSectionRatio) * atomSpacing N) :
    sectionPoleCost N w ≤ a / 8 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have haF : a * fullSectionRatio ≤ fullSectionRatio := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 fullSectionRatio_pos.le
  have hwN : w * N ≤ a * fullSectionRatio := by
    have h := hw.trans (mul_le_mul_of_nonneg_left (atomSpacing_le_inv hN)
      (mul_nonneg ha0 fullSectionRatio_pos.le))
    have he : (a * fullSectionRatio) * (1 / (N : ℝ)) = a * fullSectionRatio / N := by ring
    rw [he, le_div_iff₀ hN0] at h
    exact h
  have hw1 : w ≤ 1 := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hwwN : w ≤ w * N := by nlinarith only [hw0, hN1]
    linarith only [hwwN, hwN, haF, fullSectionRatio_le_half_spacing, spacingRatio_lt_half]
  have hF : fullSectionRatio * (Real.exp 1 + 1) ≤ 1 / 8 := by
    calc
      _ ≤ (1 / (8 * (Real.exp 1 + 1))) * (Real.exp 1 + 1) :=
        mul_le_mul_of_nonneg_right fullSectionRatio_le_pole (by positivity)
      _ = _ := by field_simp
  calc
    sectionPoleCost N w ≤ (a * fullSectionRatio) * (Real.exp 1 + 1) :=
      mul_le_mul hwN (add_le_add (Real.exp_le_exp.mpr hw1) (le_refl (1 : ℝ)))
        (by positivity) (mul_nonneg ha0 fullSectionRatio_pos.le)
    _ = a * (fullSectionRatio * (Real.exp 1 + 1)) := by ring
    _ ≤ a * (1 / 8) := mul_le_mul_of_nonneg_left hF ha0
    _ = a / 8 := by ring

/-- Reducing the allowed width retains a quantified reserve after both pole moments are paid. -/
theorem weilPair_arithmeticSection_ge_width_reserve
    {G : ℕ → ℝ → ℝ} {N : ℕ} {w a : ℝ}
    (hg : ∀ n, ContDiff ℝ 2 (G n)) (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0)
    (hN : 1 ≤ N) (hw0 : 0 < w) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hw : w ≤ (a * fullSectionRatio) * atomSpacing N) :
    (∫ u, arithmeticSection N G u ^ 2) + ((1 - a) / 8) * sectionReserve N G ≤
      weilPair (arithmeticSection N G) (arithmeticSection N G) := by
  have haF : a * fullSectionRatio ≤ fullSectionRatio := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 fullSectionRatio_pos.le
  have hfull := hw.trans (mul_le_mul_of_nonneg_right haF (atomSpacing_pos hN).le)
  have hW := weilPair_arithmeticSection_ge_unused_reserve hg hs hN hw0 hfull
  have hcost := mul_le_mul_of_nonneg_right
    (sectionPoleCost_le_width_fraction hN hw0 ha0 ha1 hw) (sectionReserve_nonneg N G)
  linarith only [hW, hcost]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.weilPair_arithmeticSection_ge_unused_reserve
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.weilPair_arithmeticSection_ge_width_reserve
