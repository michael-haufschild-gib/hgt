import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellGammaUniformRows

/-!
# Recovery of the original coarse Gamma energy

One universal square-mass error replaces the retained mean graph and exterior
charge by the actual Gamma energy of the coarse source. Combining this upper
estimate with simultaneous variance payment keeps the logarithmic detail
reserve and the full coarse Gamma term in the same original source energy.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry

/-- A constant complete pair has exactly its logarithmic interval width as mass. -/
theorem integral_coarseProfile {a : ℕ} (ha : 1 ≤ a) :
    ∫ x, coarseProfile a x = logCellWidth a := by
  have hlo : Real.log ((2 * a : ℕ) : ℝ) ≤ Real.log ((2 * a + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 2 * a ≤ 2 * a + 2 by omega))
  have he := funext (coarseProfile_eq_indicator ha)
  rw [he, integral_indicator_const 1 measurableSet_Ico, Real.volume_real_Ico_of_le hlo]
  simp only [smul_eq_mul, mul_one]
  exact haarPairWidth ha

/-- The coarse coefficient mass is exactly the square mass of its actual real source. -/
theorem integral_averageSectionProfile_sq (q : ℕ → ℝ) (X : ℕ) :
    ∫ x, averageSectionProfile q X x ^ 2 =
      ∑ a ∈ Finset.Icc 1 X, logCellWidth a * q a ^ 2 := by
  -- Off the null endpoint set, each active cell reads exactly its own coefficient.
  have hne : ∀ᵐ x ∂volume, ∀ a : ℕ, x ≠ Real.log ((2 * a : ℕ) : ℝ) := by
    apply ae_all_iff.mpr
    intro a
    rw [ae_iff]
    simp
  have hsq : (fun x => averageSectionProfile q X x ^ 2) =ᵐ[volume]
      (fun x => ∑ a ∈ Finset.Icc 1 X, q a ^ 2 * coarseProfile a x) := by
    filter_upwards [hne] with x hnx
    have hmul (a : ℕ) (ha : a ∈ Finset.Icc 1 X) :
        averageSectionProfile q X x * coarseProfile a x = q a * coarseProfile a x := by
      have ha1 := (Finset.mem_Icc.mp ha).1
      by_cases hx : x ∈ Ico (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
      · have hxo : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ)) :=
          ⟨lt_of_le_of_ne hx.1 (Ne.symm (hnx a)), hx.2⟩
        rw [averageSectionProfile_eq_on_pair q ha1 (Finset.mem_Icc.mp ha).2 hxo]
      · simp only [coarseProfile_eq_indicator ha1, indicator_of_notMem hx, mul_zero]
    calc
      _ = averageSectionProfile q X x *
          (∑ a ∈ Finset.Icc 1 X, q a * coarseProfile a x) := by
        simp only [pow_two, averageSectionProfile]
      _ = ∑ a ∈ Finset.Icc 1 X, q a * (averageSectionProfile q X x * coarseProfile a x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hmul a ha]
        ring
  have hI (a : ℕ) : Integrable (coarseProfile a) :=
    (integrable_rawCell (2 * a)).add (integrable_rawCell (2 * a + 1))
  calc
    _ = ∫ x, ∑ a ∈ Finset.Icc 1 X, q a ^ 2 * coarseProfile a x := integral_congr_ae hsq
    _ = ∑ a ∈ Finset.Icc 1 X, q a ^ 2 * ∫ x, coarseProfile a x := by
      rw [integral_finsetSum _ fun a _ => (hI a).const_mul (q a ^ 2)]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [integral_const_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_coarseProfile (Finset.mem_Icc.mp ha).1, mul_comm]

/-- Every retained mean-graph edge is nonnegative. -/
theorem completePairMeanGraph_nonneg (q : ℕ → ℝ) (X : ℕ) :
    0 ≤ completePairMeanGraph q X := by
  unfold completePairMeanGraph
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro b hb
  have ha1 := (Finset.mem_Icc.mp ha).1
  have hb1 := (Finset.mem_Icc.mp hb).1
  have hwa := logCellWidth_pos ha1
  have hwb := logCellWidth_pos hb1
  have hda : 0 < Real.log ((2 * a + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ) := by
    rwa [haarPairWidth ha1]
  have hdb : 0 < Real.log ((2 * b + 2 : ℕ) : ℝ) - Real.log ((2 * b : ℕ) : ℝ) := by
    rwa [haarPairWidth hb1]
  have hd : 0 < max
      (Real.log ((2 * b + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ))
      (Real.log ((2 * a + 2 : ℕ) : ℝ) - Real.log ((2 * b : ℕ) : ℝ)) := by
    have h1 := le_max_left
      (Real.log ((2 * b + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ))
      (Real.log ((2 * a + 2 : ℕ) : ℝ) - Real.log ((2 * b : ℕ) : ℝ))
    have h2 := le_max_right
      (Real.log ((2 * b + 2 : ℕ) : ℝ) - Real.log ((2 * a : ℕ) : ℝ))
      (Real.log ((2 * a + 2 : ℕ) : ℝ) - Real.log ((2 * b : ℕ) : ℝ))
    linarith only [hda, hdb, h1, h2]
  exact mul_nonneg (mul_nonneg (mul_nonneg hwa.le hwb.le) (sq_nonneg _))
    (archLevyDensity_pos hd).le

/-- The actual coarse Gamma energy is recovered with one universal square-mass error. -/
theorem averageSectionProfile_gamma_recovery (q : ℕ → ℝ) (X : ℕ) :
    levyEnergy (averageSectionProfile q X) ≤
      (1 / 2) * completePairMeanGraph q X + (completePairExteriorCharge q X).toReal +
        (2 * completePairGammaRowConstant) *
          ∑ a ∈ Finset.Icc 1 X, logCellWidth a * q a ^ 2 := by
  let M : ℝ := ∑ a ∈ Finset.Icc 1 X, logCellWidth a * q a ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun a ha =>
    mul_nonneg (logCellWidth_pos (Finset.mem_Icc.mp ha).1).le (sq_nonneg _)
  have hR := completePairGammaRowConstant_nonneg
  have hRM : 0 ≤ completePairGammaRowConstant * M := mul_nonneg hR hM
  have hG := completePairMeanGraph_nonneg q X
  have hrows : (∑ i : Finset.Icc 1 X, ENNReal.ofReal (q i ^ 2) * completePairGammaErrorRow X i) ≤
      ENNReal.ofReal (completePairGammaRowConstant * M) := by
    calc
      _ ≤ ∑ i : Finset.Icc 1 X,
          ENNReal.ofReal (completePairGammaRowConstant * logCellWidth (i : ℕ) * q i ^ 2) := by
        apply Finset.sum_le_sum
        intro i _hi
        refine (mul_le_mul_right (completePairGammaErrorRow_le X i) (ENNReal.ofReal (q i ^ 2))).trans_eq ?_
        rw [← ENNReal.ofReal_mul (sq_nonneg (q i))]
        congr 1
        ring
      _ = ENNReal.ofReal (∑ i : Finset.Icc 1 X,
          completePairGammaRowConstant * logCellWidth (i : ℕ) * q i ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun (i : Finset.Icc 1 X) _ =>
          mul_nonneg (mul_nonneg hR (logCellWidth_pos (Finset.mem_Icc.mp i.property).1).le)
            (sq_nonneg (q i))]
      _ = _ := by
        congr 1
        rw [Finset.sum_coe_sort (Finset.Icc 1 X)
          (fun a : ℕ => completePairGammaRowConstant * logCellWidth a * q a ^ 2)]
        dsimp only [M]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
  have hbound := (averageSectionProfile_gamma_le_graph_exterior_rows q X).trans
    (add_le_add le_rfl (mul_le_mul_right hrows 4))
  -- Finiteness of the actual exterior charge justifies conversion to real energy.
  have hrealcharge : ENNReal.ofReal
      (completePairMeanGraph q X + 2 * (completePairExteriorCharge q X).toReal +
        4 * (completePairGammaRowConstant * M)) =
      ENNReal.ofReal (completePairMeanGraph q X) + 2 * completePairExteriorCharge q X +
        4 * ENNReal.ofReal (completePairGammaRowConstant * M) := by
    rw [ENNReal.ofReal_add
        (add_nonneg hG (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ENNReal.toReal_nonneg))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hRM),
      ENNReal.ofReal_add hG (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.ofReal_toReal (completePairExteriorCharge_ne_top q X)]
    norm_num only [ENNReal.ofReal_ofNat]
  have hleft : ENNReal.ofReal (2 * levyEnergy (averageSectionProfile q X)) =
      2 * ENNReal.ofReal (levyEnergy (averageSectionProfile q X)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num only [ENNReal.ofReal_ofNat]
  rw [← hrealcharge, ← hleft] at hbound
  have hrhs : 0 ≤ completePairMeanGraph q X + 2 * (completePairExteriorCharge q X).toReal +
      4 * (completePairGammaRowConstant * M) := by positivity
  have h := (ENNReal.ofReal_le_ofReal_iff hrhs).mp hbound
  change _ ≤ (1 / 2) * completePairMeanGraph q X + (completePairExteriorCharge q X).toReal +
    (2 * completePairGammaRowConstant) * M
  linarith only [h]

/-- The recovery error is a universal multiple of the actual coarse square mass. -/
theorem averageSectionProfile_gamma_recovery_integral (q : ℕ → ℝ) (X : ℕ) :
    levyEnergy (averageSectionProfile q X) ≤
      (1 / 2) * completePairMeanGraph q X + (completePairExteriorCharge q X).toReal +
        (2 * completePairGammaRowConstant) * ∫ x, averageSectionProfile q X x ^ 2 := by
  rw [integral_averageSectionProfile_sq]
  exact averageSectionProfile_gamma_recovery q X

/-- Full coarse Gamma and logarithmic detail payment coexist in the original complete source. -/
theorem completePairProfile_gamma_ge_coarse_add_detail (q d : ℕ → ℝ) (X : ℕ) :
    levyEnergy (averageSectionProfile q X) +
        (∑ a ∈ Finset.Icc 1 X, Real.log (a : ℝ) * haarMass a * d a ^ 2) ≤
      levyEnergy (completePairProfile q d X) +
        (2 * completePairGammaRowConstant) *
          ∑ a ∈ Finset.Icc 1 X, logCellWidth a * q a ^ 2 := by
  have hcoarse := averageSectionProfile_gamma_recovery q X
  have hfull := completePairProfile_levyEnergy_ge_detail_graph_exterior q d X
  linarith only [hcoarse, hfull]

/-- The simultaneous coarse and detail estimate uses the literal source square mass. -/
theorem completePairProfile_gamma_ge_coarse_add_detail_integral (q d : ℕ → ℝ) (X : ℕ) :
    levyEnergy (averageSectionProfile q X) +
        (∑ a ∈ Finset.Icc 1 X, Real.log (a : ℝ) * haarMass a * d a ^ 2) ≤
      levyEnergy (completePairProfile q d X) +
        (2 * completePairGammaRowConstant) * ∫ x, averageSectionProfile q X x ^ 2 := by
  rw [integral_averageSectionProfile_sq]
  exact completePairProfile_gamma_ge_coarse_add_detail q d X

/-- One nonnegative constant works for every signed source and every finite horizon. -/
theorem exists_completePair_gamma_coarse_detail_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      levyEnergy (averageSectionProfile q X) +
          (∑ a ∈ Finset.Icc 1 X, Real.log (a : ℝ) * haarMass a * d a ^ 2) ≤
        levyEnergy (completePairProfile q d X) +
          C * ∫ x, averageSectionProfile q X x ^ 2 := by
  refine ⟨2 * completePairGammaRowConstant,
    mul_nonneg (by norm_num) completePairGammaRowConstant_nonneg, ?_⟩
  exact completePairProfile_gamma_ge_coarse_add_detail_integral

/-- Coarse recovery and detail payment retain both independent original cell coefficients. -/
theorem cellPairSum_gamma_ge_coarse_add_detail (u v : ℕ → ℝ) (X : ℕ) :
    levyEnergy (averageSectionProfile
        (fun a => haarRightCoeff a * u a + haarLeftCoeff a * v a) X) +
        (∑ a ∈ Finset.Icc 1 X, Real.log (a : ℝ) * haarMass a * (u a - v a) ^ 2) ≤
      levyEnergy (fun x => ∑ a ∈ Finset.Icc 1 X,
        (u a * rawCell (2 * a) x + v a * rawCell (2 * a + 1) x)) +
        (2 * completePairGammaRowConstant) * ∑ a ∈ Finset.Icc 1 X,
          logCellWidth a * (haarRightCoeff a * u a + haarLeftCoeff a * v a) ^ 2 := by
  have h := completePairProfile_gamma_ge_coarse_add_detail
    (fun a => haarRightCoeff a * u a + haarLeftCoeff a * v a) (fun a => u a - v a) X
  rw [funext (completePairProfile_eq_cells u v X)] at h
  exact h

#print axioms integral_coarseProfile
#print axioms integral_averageSectionProfile_sq
#print axioms completePairMeanGraph_nonneg
#print axioms averageSectionProfile_gamma_recovery
#print axioms averageSectionProfile_gamma_recovery_integral
#print axioms completePairProfile_gamma_ge_coarse_add_detail
#print axioms completePairProfile_gamma_ge_coarse_add_detail_integral
#print axioms exists_completePair_gamma_coarse_detail_bound
#print axioms cellPairSum_gamma_ge_coarse_add_detail

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
