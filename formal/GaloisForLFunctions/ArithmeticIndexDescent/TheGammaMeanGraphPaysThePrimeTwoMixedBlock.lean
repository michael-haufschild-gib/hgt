import GaloisForLFunctions.ArithmeticIndexDescent.ThePrimeTwoMixedBlockReadsCoarseDifferences
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellMeanGraph

/-!
# Gamma graph payment for the actual prime-two mixed source

The adjacent coarse differences read by prime two are edges of the retained
Gamma mean graph. Their conductance is uniformly comparable to the balanced
detail mass. One use of that graph pays the complete signed prime-two mixed
block, retaining the remaining logarithmic detail charge.
-/

noncomputable section

open MeasureTheory Finset Set
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

private def coarseGammaEdge (q : ℕ → ℝ) (a b : ℕ) : ℝ :=
  logCellWidth a * logCellWidth b * (q a - q b) ^ 2 *
    archLevyDensity (max
      (Real.log ((2 * b + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ))
      (Real.log ((2 * a + 2 : ℕ) : ℝ) - Real.log ((2 * b : ℕ) : ℝ)))

private theorem coarseGammaEdge_nonneg (q : ℕ → ℝ) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) : 0 ≤ coarseGammaEdge q a b := by
  have hpa : 0 < Real.log ((2 * a + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ) := by
    rw [haarPairWidth ha]
    exact logCellWidth_pos ha
  have hpb : 0 < Real.log ((2 * b + 2 : ℕ) : ℝ) - Real.log ((2 * b : ℕ) : ℝ) := by
    rw [haarPairWidth hb]
    exact logCellWidth_pos hb
  have hdist : 0 < max
      (Real.log ((2 * b + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ))
      (Real.log ((2 * a + 2 : ℕ) : ℝ) - Real.log ((2 * b : ℕ) : ℝ)) := by
    by_contra h
    have hl := (le_max_left
      (Real.log ((2 * b + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ))
      (Real.log ((2 * a + 2 : ℕ) : ℝ) - Real.log ((2 * b : ℕ) : ℝ))).trans (le_of_not_gt h)
    have hr := (le_max_right
      (Real.log ((2 * b + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ))
      (Real.log ((2 * a + 2 : ℕ) : ℝ) - Real.log ((2 * b : ℕ) : ℝ))).trans (le_of_not_gt h)
    linarith only [hpa, hpb, hl, hr]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (logCellWidth_pos ha).le (logCellWidth_pos hb).le) (sq_nonneg _))
    (archLevyDensity_pos hdist).le

private theorem adjacent_coarse_distance {a : ℕ} (ha : 1 ≤ a) :
    max
      (Real.log ((2 * (2 * a + 1) + 2 : ℕ) : ℝ) - Real.log ((2 * (2 * a) : ℕ) : ℝ))
      (Real.log ((2 * (2 * a) + 2 : ℕ) : ℝ) - Real.log ((2 * (2 * a + 1) : ℕ) : ℝ)) =
      logCellWidth a := by
  have hmid : (2 * (2 * a) + 2 : ℕ) = 2 * (2 * a + 1) := by omega
  have hspan : Real.log ((2 * (2 * a + 1) + 2 : ℕ) : ℝ) -
      Real.log ((2 * (2 * a) : ℕ) : ℝ) = logCellWidth a := by
    rw [← adjacent_logCellWidths ha,
      ← haarPairWidth (by omega : 1 ≤ 2 * a),
      ← haarPairWidth (by omega : 1 ≤ 2 * a + 1), hmid]
    ring
  rw [hspan, hmid, sub_self, max_eq_left (logCellWidth_pos ha).le]

private theorem coarseGammaEdge_adjacent (q : ℕ → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    coarseGammaEdge q (2 * a) (2 * a + 1) =
      haarMass a * (logCellWidth a * archLevyDensity (logCellWidth a)) *
        (q (2 * a) - q (2 * a + 1)) ^ 2 := by
  have hm : haarMass a * logCellWidth a =
      logCellWidth (2 * a) * logCellWidth (2 * a + 1) := by
    rw [← adjacent_logCellWidths ha, haarMass,
      div_mul_cancel₀ _ (add_pos (logCellWidth_pos (by omega : 1 ≤ 2 * a))
        (logCellWidth_pos (by omega : 1 ≤ 2 * a + 1))).ne']
  rw [coarseGammaEdge, adjacent_coarse_distance ha, ← hm]
  ring

private theorem width_mul_gamma_ge {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    Real.exp (-(1 / 2 : ℝ)) / 2 ≤ h * archLevyDensity h := by
  have hd : 0 < 1 - Real.exp (-2 * h) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [hh]))
  have hden : 1 - Real.exp (-2 * h) ≤ 2 * h := by
    have he := Real.add_one_le_exp (-2 * h)
    linarith only [he]
  have hnum : Real.exp (-(1 / 2 : ℝ)) ≤ Real.exp (-h / 2) :=
    Real.exp_le_exp.mpr (by linarith only [hh1])
  rw [archLevyDensity, ← mul_div_assoc]
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ (Real.exp (-(1 / 2 : ℝ)) / 2) * (2 * h) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    _ = h * Real.exp (-(1 / 2 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnum hh.le

private theorem coarseGammaEdge_adjacent_ge (q : ℕ → ℝ) {a : ℕ} (ha : 1 ≤ a) :
    (Real.exp (-(1 / 2 : ℝ)) / 2) *
      (haarMass a * (q (2 * a) - q (2 * a + 1)) ^ 2) ≤
        coarseGammaEdge q (2 * a) (2 * a + 1) := by
  have hw1 : logCellWidth a ≤ 1 :=
    (logCellWidth_le_inv ha).trans
      ((div_le_one (by exact_mod_cast (show 0 < a by omega))).mpr (by exact_mod_cast ha))
  have h := mul_le_mul_of_nonneg_left (width_mul_gamma_ge (logCellWidth_pos ha) hw1)
    (mul_nonneg (haarMass_pos ha).le (sq_nonneg (q (2 * a) - q (2 * a + 1))))
  rw [coarseGammaEdge_adjacent q ha]
  convert h using 1 <;> ring

/-- The existing mean graph pays the same adjacent variation read by prime two. -/
theorem primeTwoCoarseVariation_le_meanGraph (q : ℕ → ℝ) {Y X : ℕ}
    (hYX : 2 * Y + 1 ≤ X) :
    (Real.exp (-(1 / 2 : ℝ)) / 4) * primeTwoCoarseVariation q Y ≤
      (1 / 2) * completePairMeanGraph q X := by
  classical
  have hrows : (Finset.Icc 1 Y).image (fun a => 2 * a) ⊆ Finset.Icc 1 X := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    have ha1 := (Finset.mem_Icc.mp ha).1
    have haY := (Finset.mem_Icc.mp ha).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hrowNN (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
      0 ≤ ∑ b ∈ Finset.Icc 1 X, coarseGammaEdge q a b := by
    apply Finset.sum_nonneg
    intro b hb
    exact coarseGammaEdge_nonneg q (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1
  have hselected := Finset.sum_le_sum_of_subset_of_nonneg hrows
    (fun a ha _ => hrowNN a ha)
  rw [Finset.sum_image (by intro a _ b _ hab; omega)] at hselected
  have hcols : (∑ a ∈ Finset.Icc 1 Y, coarseGammaEdge q (2 * a) (2 * a + 1)) ≤
      ∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 X, coarseGammaEdge q (2 * a) b := by
    apply Finset.sum_le_sum
    intro a ha
    have ha1 := (Finset.mem_Icc.mp ha).1
    have haY := (Finset.mem_Icc.mp ha).2
    exact Finset.single_le_sum
      (fun b hb => coarseGammaEdge_nonneg q (by omega) (Finset.mem_Icc.mp hb).1)
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hlocal : (Real.exp (-(1 / 2 : ℝ)) / 2) * primeTwoCoarseVariation q Y ≤
      ∑ a ∈ Finset.Icc 1 Y, coarseGammaEdge q (2 * a) (2 * a + 1) := by
    rw [primeTwoCoarseVariation, Finset.mul_sum]
    exact Finset.sum_le_sum fun a ha => coarseGammaEdge_adjacent_ge q (Finset.mem_Icc.mp ha).1
  have hgraph : (Real.exp (-(1 / 2 : ℝ)) / 2) * primeTwoCoarseVariation q Y ≤
      completePairMeanGraph q X := hlocal.trans (hcols.trans hselected)
  have hhalf := mul_le_mul_of_nonneg_left hgraph (by norm_num : (0 : ℝ) ≤ 1 / 2)
  convert hhalf using 1 <;> ring

/-- A horizon-independent detail charge for the literal prime-two coefficient. -/
def primeTwoDetailCharge : ℝ :=
  1 + 4 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) ^ 2 / Real.exp (-(1 / 2 : ℝ))

theorem primeTwoDetailCharge_pos : 0 < primeTwoDetailCharge := by
  unfold primeTwoDetailCharge
  positivity

private theorem primeTwoCoarseVariation_nonneg (q : ℕ → ℝ) (Y : ℕ) :
    0 ≤ primeTwoCoarseVariation q Y := by
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (haarMass_pos (Finset.mem_Icc.mp ha).1).le (sq_nonneg _)

/-- The signed mixed block consumes one mean-graph payment and a fixed detail charge. -/
theorem abs_primeTwoMixedSource_le_meanGraph (d q : ℕ → ℝ) {Y X : ℕ}
    (hYX : 2 * Y + 1 ≤ X) :
    |primeTwoMixedSource d q Y X| ≤ primeTwoDetailCharge * primeTwoDetailMass d Y +
      (1 / 2) * completePairMeanGraph q X := by
  have hcoef : (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) ^ 2 / primeTwoDetailCharge ≤
      Real.exp (-(1 / 2 : ℝ)) / 4 := by
    apply (div_le_iff₀ primeTwoDetailCharge_pos).mpr
    have he : (Real.exp (-(1 / 2 : ℝ)) / 4) * primeTwoDetailCharge =
        Real.exp (-(1 / 2 : ℝ)) / 4 + (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) ^ 2 := by
      unfold primeTwoDetailCharge
      field_simp [Real.exp_ne_zero (-(1 / 2 : ℝ))]
      ring
    rw [he]
    exact le_add_of_nonneg_left (by positivity)
  apply (abs_primeTwoMixedSource_le_variation d q hYX primeTwoDetailCharge_pos).trans
  exact add_le_add_left
    ((mul_le_mul_of_nonneg_right hcoef (primeTwoCoarseVariation_nonneg q Y)).trans
      (primeTwoCoarseVariation_le_meanGraph q hYX)) _

/-- Paying the complete prime-two mixed block retains the remaining detail charge. -/
theorem completePair_gamma_after_primeTwoMixed (d q : ℕ → ℝ) (Y : ℕ) :
    (∑ a ∈ Finset.Icc 1 (2 * Y + 1), Real.log (a : ℝ) * haarMass a * d a ^ 2) -
        primeTwoDetailCharge * primeTwoDetailMass d Y ≤
      levyEnergy (completePairProfile q d (2 * Y + 1)) -
        |primeTwoMixedSource d q (2 * Y + 1) (2 * Y + 1)| := by
  have hgamma := completePairProfile_levyEnergy_ge_detail_graph_exterior q d (2 * Y + 1)
  have hpay := abs_primeTwoMixedSource_le_meanGraph d q (le_refl (2 * Y + 1))
  rw [primeTwoMixedSource_odd_horizon] 
  have hext := ENNReal.toReal_nonneg (a := completePairExteriorCharge q (2 * Y + 1))
  linarith only [hgamma, hpay, hext]

/-- One fixed lower detail index pays prime two with every coarse average still arbitrary. -/
theorem exists_high_detail_gamma_pays_primeTwo :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (Y : ℕ),
      |primeTwoMixedSource (fun a => if A ≤ a then d a else 0) q (2 * Y + 1) (2 * Y + 1)| ≤
        levyEnergy (completePairProfile q (fun a => if A ≤ a then d a else 0) (2 * Y + 1)) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp primeTwoDetailCharge)
  have hA1 : 1 ≤ A := by
    have hpos : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hpos.ne')
  have hlog {a : ℕ} (hAa : A ≤ a) : primeTwoDetailCharge ≤ Real.log (a : ℝ) := by
    have hbound : Real.exp primeTwoDetailCharge < (a : ℝ) :=
      hA.trans_le (by exact_mod_cast hAa)
    have h := Real.log_lt_log (Real.exp_pos _) hbound
    rw [Real.log_exp] at h
    exact h.le
  refine ⟨A, hA1, ?_⟩
  intro d q Y
  let c : ℕ → ℝ := fun a => if A ≤ a then d a else 0
  have hcoef (a : ℕ) (ha : 1 ≤ a) :
      primeTwoDetailCharge * (haarMass a * c a ^ 2) ≤ Real.log (a : ℝ) * haarMass a * c a ^ 2 := by
    by_cases hAa : A ≤ a
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hlog hAa)
        (mul_nonneg (haarMass_pos ha).le (sq_nonneg (c a)))
    · simp only [c, if_neg hAa, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, le_refl]
  have htotal : primeTwoDetailCharge * primeTwoDetailMass c (2 * Y + 1) ≤
      ∑ a ∈ Finset.Icc 1 (2 * Y + 1), Real.log (a : ℝ) * haarMass a * c a ^ 2 := by
    rw [primeTwoDetailMass, Finset.mul_sum]
    exact Finset.sum_le_sum fun a ha => hcoef a (Finset.mem_Icc.mp ha).1
  have hsub : primeTwoDetailMass c Y ≤ primeTwoDetailMass c (2 * Y + 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro a ha
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1, by have := (Finset.mem_Icc.mp ha).2; omega⟩
    · intro a ha _
      exact mul_nonneg (haarMass_pos (Finset.mem_Icc.mp ha).1).le (sq_nonneg _)
  have hbudget := (mul_le_mul_of_nonneg_left hsub primeTwoDetailCharge_pos.le).trans htotal
  have hpay := completePair_gamma_after_primeTwoMixed c q Y
  change |primeTwoMixedSource c q (2 * Y + 1) (2 * Y + 1)| ≤
    levyEnergy (completePairProfile q c (2 * Y + 1))
  linarith only [hbudget, hpay]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.primeTwoCoarseVariation_le_meanGraph
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_primeTwoMixedSource_le_meanGraph
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.completePair_gamma_after_primeTwoMixed
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_high_detail_gamma_pays_primeTwo
