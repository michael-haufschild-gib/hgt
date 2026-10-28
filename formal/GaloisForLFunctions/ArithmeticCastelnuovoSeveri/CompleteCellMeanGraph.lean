import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaMeanVarianceCapacity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellVariancePayment

/-!
# Simultaneous Gamma payment for cell details and pair averages

Every complete cell coefficient is retained. The original Gamma energy pays
the logarithmic detail mass together with a positive graph on pair averages.
The graph uses the original Gamma density at each farthest pair distance.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry HTGeometry IntervalVariance

/-- A finite graph on the actual weighted pair averages, with far-end Gamma conductances. -/
def completePairMeanGraph (q : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
    logCellWidth a * logCellWidth b * (q a - q b) ^ 2 *
      archLevyDensity (max
        (Real.log ((2 * b + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ))
        (Real.log ((2 * a + 2 : ℕ) : ℝ) - Real.log ((2 * b : ℕ) : ℝ)))

/-- Boundary payment for the pair averages against the zero exterior source. -/
def completePairExteriorCharge (q : ℕ → ℝ) (X : ℕ) : ℝ≥0∞ :=
  ∑ a : Finset.Icc 1 X, ∫⁻ y in
    (⋃ b : Finset.Icc 1 X, Ioo (Real.log ((2 * (b : ℕ) : ℕ) : ℝ))
      (Real.log ((2 * (b : ℕ) + 2 : ℕ) : ℝ)))ᶜ,
    ENNReal.ofReal (logCellWidth (a : ℕ) * q a ^ 2) *
      MeanZeroIntervals.gammaFarCharge (Real.log ((2 * (a : ℕ) : ℕ) : ℝ))
        (Real.log ((2 * (a : ℕ) + 2 : ℕ) : ℝ)) y

private theorem completePairProfile_zero_ae_exterior (q d : ℕ → ℝ) (X : ℕ) :
    ∀ᵐ x ∂volume.restrict
      (⋃ a : Finset.Icc 1 X, Ioo (Real.log ((2 * (a : ℕ) : ℕ) : ℝ))
        (Real.log ((2 * (a : ℕ) + 2 : ℕ) : ℝ)))ᶜ,
      completePairProfile q d X x = 0 := by
  have hne : ∀ᵐ x ∂volume, ∀ a : ℕ, x ≠ Real.log ((2 * a : ℕ) : ℝ) := by
    apply ae_all_iff.mpr
    intro a
    rw [ae_iff]
    simp
  have hFm : MeasurableSet
      (⋃ a : Finset.Icc 1 X, Ioo (Real.log ((2 * (a : ℕ) : ℕ) : ℝ))
        (Real.log ((2 * (a : ℕ) + 2 : ℕ) : ℝ)))ᶜ :=
    (MeasurableSet.iUnion (fun _ => measurableSet_Ioo)).compl
  filter_upwards [ae_restrict_mem hFm,
    ae_restrict_of_ae hne] with x hx hnx
  have hout (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
      x ∉ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)) := by
    intro hi
    apply hx
    refine mem_iUnion.mpr ⟨⟨a, ha⟩, ?_⟩
    exact ⟨lt_of_le_of_ne hi.1 (Ne.symm (hnx a)), hi.2⟩
  have hc (a : ℕ) (ha : a ∈ Finset.Icc 1 X) : coarseProfile a x = 0 := by
    have ha1 := (Finset.mem_Icc.mp ha).1
    have hlo : Real.log ((2 * a : ℕ) : ℝ) ≤ Real.log ((2 * a + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a ≤ 2 * a + 1 by omega))
    have hhi : Real.log ((2 * a + 1 : ℕ) : ℝ) ≤ Real.log ((2 * a + 2 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a + 1 ≤ 2 * a + 2 by omega))
    have hl : x ∉ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 1 : ℕ) : ℝ)) :=
      fun h => hout a ha ⟨h.1, h.2.trans_le hhi⟩
    have hr : x ∉ Ico (Real.log ((2 * a + 1 : ℕ) : ℝ))
        (Real.log ((2 * a + 1 + 1 : ℕ) : ℝ)) := by
      intro h
      exact hout a ha ⟨hlo.trans h.1, by simpa only [Nat.add_assoc] using h.2⟩
    simp only [coarseProfile, rawCell, indicator_of_notMem hl, indicator_of_notMem hr, add_zero]
  have ha : averageSectionProfile q X x = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [hc a ha, mul_zero]
  have hd : haarSectionProfile d X x = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [haarProfile_zero_outside_pair (Finset.mem_Icc.mp ha).1 (hout a ha), mul_zero]
  rw [completePairProfile, ha, hd, add_zero]

private theorem gammaExteriorMeanCharge_completePairProfile (q d : ℕ → ℝ) (X : ℕ)
    (a : Finset.Icc 1 X) :
    gammaExteriorMeanCharge (Real.log ((2 * (a : ℕ) : ℕ) : ℝ))
      (Real.log ((2 * (a : ℕ) + 2 : ℕ) : ℝ))
      (⋃ b : Finset.Icc 1 X, Ioo (Real.log ((2 * (b : ℕ) : ℕ) : ℝ))
        (Real.log ((2 * (b : ℕ) + 2 : ℕ) : ℝ)))ᶜ (completePairProfile q d X) =
      ∫⁻ y in (⋃ b : Finset.Icc 1 X, Ioo (Real.log ((2 * (b : ℕ) : ℕ) : ℝ))
        (Real.log ((2 * (b : ℕ) + 2 : ℕ) : ℝ)))ᶜ,
        ENNReal.ofReal (logCellWidth (a : ℕ) * q a ^ 2) *
          MeanZeroIntervals.gammaFarCharge (Real.log ((2 * (a : ℕ) : ℕ) : ℝ))
            (Real.log ((2 * (a : ℕ) + 2 : ℕ) : ℝ)) y := by
  unfold gammaExteriorMeanCharge
  rw [intervalMean_completePairProfile q d (Finset.mem_Icc.mp a.property).1
    (Finset.mem_Icc.mp a.property).2, haarPairWidth (Finset.mem_Icc.mp a.property).1]
  apply lintegral_congr_ae
  filter_upwards [completePairProfile_zero_ae_exterior q d X] with y hy
  rw [hy, sub_zero]

private theorem gammaMeanPairEnergy_completePairProfile (q d : ℕ → ℝ) {X a b : ℕ}
    (ha : 1 ≤ a) (haX : a ≤ X) (hb : 1 ≤ b) (hbX : b ≤ X) :
    gammaMeanPairEnergy
      (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
      (Real.log ((2 * b : ℕ) : ℝ)) (Real.log ((2 * b + 2 : ℕ) : ℝ))
      (completePairProfile q d X) =
    logCellWidth a * logCellWidth b * (q a - q b) ^ 2 *
      archLevyDensity (max
        (Real.log ((2 * b + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ))
        (Real.log ((2 * a + 2 : ℕ) : ℝ) - Real.log ((2 * b : ℕ) : ℝ))) := by
  rw [gammaMeanPairEnergy, haarPairWidth ha, haarPairWidth hb,
    intervalMean_completePairProfile q d ha haX,
    intervalMean_completePairProfile q d hb hbX]

/-- Both pair-average graph and boundary payment coexist with every logarithmic detail charge. -/
theorem completePairProfile_levyEnergy_ge_detail_graph_exterior (q d : ℕ → ℝ) (X : ℕ) :
    (∑ a ∈ Finset.Icc 1 X, Real.log (a : ℝ) * haarMass a * d a ^ 2) +
        (1 / 2) * completePairMeanGraph q X + (completePairExteriorCharge q X).toReal ≤
      levyEnergy (completePairProfile q d X) := by
  let S := Finset.Icc 1 X
  let L : S → ℝ := fun i => Real.log ((2 * (i : ℕ) : ℕ) : ℝ)
  let U : S → ℝ := fun i => Real.log ((2 * (i : ℕ) + 2 : ℕ) : ℝ)
  have hpos (i : S) : 1 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
  have hwidth (i : S) : U i - L i = logCellWidth (i : ℕ) := haarPairWidth (hpos i)
  have hw0 (i : S) : 0 < U i - L i := by rw [hwidth]; exact logCellWidth_pos (hpos i)
  have hwidth1 (i : S) : U i - L i ≤ 1 := by
    rw [hwidth]
    exact (logCellWidth_le_inv (hpos i)).trans
      ((div_le_one (by exact_mod_cast (show 0 < (i : ℕ) by have := hpos i; omega))).mpr
        (by exact_mod_cast hpos i))
  have hsep (i j : S) (hij : i ≠ j) : U i ≤ L j ∨ U j ≤ L i := by
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      apply Real.log_le_log (by have := hpos i; positivity)
      exact_mod_cast (show 2 * (i : ℕ) + 2 ≤ 2 * (j : ℕ) by omega)
    · right
      apply Real.log_le_log (by have := hpos j; positivity)
      exact_mod_cast (show 2 * (j : ℕ) + 2 ≤ 2 * (i : ℕ) by omega)
  have hgraph : (∑ i : S, ∑ j : S,
      gammaMeanPairEnergy (L i) (U i) (L j) (U j) (completePairProfile q d X)) =
      completePairMeanGraph q X := by
    unfold completePairMeanGraph
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro i _hi
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro j _hj
    exact gammaMeanPairEnergy_completePairProfile q d
      (hpos i) (Finset.mem_Icc.mp i.property).2 (hpos j) (Finset.mem_Icc.mp j.property).2
  have hext : (∑ i : S, gammaExteriorMeanCharge (L i) (U i)
      (⋃ j : S, Ioo (L j) (U j))ᶜ (completePairProfile q d X)) =
      completePairExteriorCharge q X := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact gammaExteriorMeanCharge_completePairProfile q d X i
  have h := levyEnergy_ge_log_variance_add_mean_graph_add_exterior L U
    (fun i => sub_pos.mp (hw0 i)) hwidth1 hsep
    (completePairProfile_bv q d X) (completePairProfile_compact q d X)
  rw [hgraph, hext] at h
  apply le_trans ?_ h
  refine add_le_add (add_le_add ?_ le_rfl) le_rfl
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_le_sum
  intro i _hi
  rw [intervalVariance_completePairProfile q d (hpos i) (Finset.mem_Icc.mp i.property).2]
  have hlog : Real.log ((i : ℕ) : ℝ) ≤ Real.log (1 / (U i - L i)) := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < (i : ℕ) by have := hpos i; omega))
    apply (le_div_iff₀ (hw0 i)).mpr
    rw [hwidth]
    have hle := mul_le_mul_of_nonneg_left (logCellWidth_le_inv (hpos i))
      (Nat.cast_nonneg (i : ℕ))
    have hi0 : ((i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show (i : ℕ) ≠ 0 by have := hpos i; omega)
    simpa only [mul_one_div_cancel hi0] using hle
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hlog
    (mul_nonneg (haarMass_pos (hpos i)).le (sq_nonneg _))

/-- Both original cell coefficients survive in simultaneous detail, mean, and boundary payment. -/
theorem cellPairSum_levyEnergy_ge_detail_graph_exterior (u v : ℕ → ℝ) (X : ℕ) :
    (∑ a ∈ Finset.Icc 1 X, Real.log (a : ℝ) * haarMass a * (u a - v a) ^ 2) +
        (1 / 2) * completePairMeanGraph
          (fun a => haarRightCoeff a * u a + haarLeftCoeff a * v a) X +
        (completePairExteriorCharge
          (fun a => haarRightCoeff a * u a + haarLeftCoeff a * v a) X).toReal ≤
      levyEnergy (fun x => ∑ a ∈ Finset.Icc 1 X,
        (u a * rawCell (2 * a) x + v a * rawCell (2 * a + 1) x)) := by
  have h := completePairProfile_levyEnergy_ge_detail_graph_exterior
    (fun a => haarRightCoeff a * u a + haarLeftCoeff a * v a) (fun a => u a - v a) X
  have he := funext (completePairProfile_eq_cells u v X)
  rw [he] at h
  exact h

#print axioms completePairProfile_levyEnergy_ge_detail_graph_exterior
#print axioms cellPairSum_levyEnergy_ge_detail_graph_exterior

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
