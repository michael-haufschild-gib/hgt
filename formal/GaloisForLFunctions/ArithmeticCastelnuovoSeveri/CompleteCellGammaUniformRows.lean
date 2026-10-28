import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellGammaAccounting
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCellGammaUniformRows

/-!
# Uniform Gamma errors for the actual complete pairs

The pair intervals are a common translate of the logarithmic partition.
Their actual endpoint errors and exterior averaging loss have one fixed
mass bound. The retained exterior charge is finite before real conversion.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry MeanZeroIntervals

/-- One fixed constant controls every complete-pair Gamma error row. -/
def completePairGammaRowConstant : ℝ :=
  13 * Real.exp (1 / 2) + 2 * gammaTailMass (Real.log (3 / 2 : ℝ))

theorem completePairGammaRowConstant_nonneg : 0 ≤ completePairGammaRowConstant := by
  have ht := gammaTailMass_nonneg (show 0 < Real.log (3 / 2 : ℝ) from Real.log_pos (by norm_num))
  unfold completePairGammaRowConstant
  positivity

private theorem pair_left_translate {b : ℕ} (hb : 1 ≤ b) :
    Real.log ((2 * b : ℕ) : ℝ) = Real.log 2 + Real.log (b : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity)]

private theorem pair_right_translate (b : ℕ) :
    Real.log ((2 * b + 2 : ℕ) : ℝ) = Real.log 2 + Real.log ((b + 1 : ℕ) : ℝ) := by
  rw [show 2 * b + 2 = 2 * (b + 1) by omega, Nat.cast_mul, Nat.cast_ofNat,
    Real.log_mul (by norm_num) (by positivity)]

/-- Every actual complete-pair row is uniformly bounded by its own logarithmic width. -/
theorem completePairGammaErrorRow_le (X : ℕ) (i : Finset.Icc 1 X) :
    completePairGammaErrorRow X i ≤
      ENNReal.ofReal (completePairGammaRowConstant * logCellWidth (i : ℕ)) := by
  classical
  let S := Finset.Icc 1 X
  let a : ℕ := i
  let P : ℕ → ℝ≥0∞ := fun b => gammaIntervalPairDefect
    (Real.log 2 + Real.log (a : ℝ)) (Real.log 2 + Real.log ((a + 1 : ℕ) : ℝ))
    (Real.log 2 + Real.log (b : ℝ)) (Real.log 2 + Real.log ((b + 1 : ℕ) : ℝ))
  let L : S → ℝ := fun j => Real.log ((2 * (j : ℕ) : ℕ) : ℝ)
  let U : S → ℝ := fun j => Real.log ((2 * (j : ℕ) + 2 : ℕ) : ℝ)
  let I : S → Set ℝ := fun j => Ioo (L j) (U j)
  let F := (⋃ j, I j)ᶜ
  have hpos (j : S) : 1 ≤ (j : ℕ) := (Finset.mem_Icc.mp j.property).1
  have ha : 1 ≤ a := hpos i
  have hpair (j : S) : gammaFinitePairDefect L U i j =
      if (j : ℕ) = a then 0 else P j := by
    by_cases hij : i = j
    · subst j
      simp [gammaFinitePairDefect_self, a]
    · have hji : (j : ℕ) ≠ a := fun h => hij (Subtype.ext h.symm)
      rw [gammaFinitePairDefect, if_neg hij, if_neg hji]
      dsimp only [L, U, P, a]
      rw [pair_left_translate (hpos i), pair_right_translate (i : ℕ),
        pair_left_translate (hpos j), pair_right_translate (j : ℕ)]
  -- Remove the zero diagonal before applying the translated logarithmic row bound.
  have hsum : (∑ j : S, gammaFinitePairDefect L U i j) = ∑ b ∈ S.erase a, P b := by
    rw [Finset.sum_congr rfl fun j _ => hpair j,
      Finset.sum_coe_sort S (fun b : ℕ => if b = a then (0 : ℝ≥0∞) else P b)]
    rw [← Finset.filter_ne' S a, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _hb
    by_cases hb : b = a <;> simp [hb]
  have hpairs : (∑ j : S, gammaFinitePairDefect L U i j) ≤
      ENNReal.ofReal ((12 * Real.exp (1 / 2) +
        2 * gammaTailMass (Real.log (3 / 2 : ℝ))) * logCellWidth a) := by
    rw [hsum]
    exact gamma_logCell_pairRow_le ha (Real.log 2) S fun b hb => (Finset.mem_Icc.mp hb).1
  have hwidth : U i - L i = logCellWidth a := haarPairWidth ha
  have hab : L i < U i := by
    apply sub_pos.mp
    rw [hwidth]
    exact logCellWidth_pos ha
  have hw : U i - L i ≤ 1 := by
    rw [hwidth]
    exact (logCellWidth_le_inv ha).trans
      ((div_le_one (by positivity : (0 : ℝ) < a)).mpr (by exact_mod_cast ha))
  have hF : F ⊆ (I i)ᶜ := fun _ hy hi => hy (mem_iUnion.mpr ⟨i, hi⟩)
  have hext := gamma_interval_exterior_subset_defect_le hab hw hF
  rw [hwidth] at hext
  change (∑ j : S, gammaFinitePairDefect L U i j) +
    (∫⁻ x in I i, ∫⁻ y in F, gammaIntervalRowDefect (L i) (U i) x y) ≤ _
  refine (add_le_add hpairs hext).trans_eq ?_
  have ht := gammaTailMass_nonneg (show 0 < Real.log (3 / 2 : ℝ) from Real.log_pos (by norm_num))
  have hw0 := (logCellWidth_pos ha).le
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  dsimp only [completePairGammaRowConstant]
  ring

/-- The retained exterior charge is finite for every actual finite coarse source. -/
theorem completePairExteriorCharge_ne_top (q : ℕ → ℝ) (X : ℕ) :
    completePairExteriorCharge q X ≠ ⊤ := by
  unfold completePairExteriorCharge
  apply ENNReal.sum_ne_top.mpr
  intro i _hi
  have ha := (Finset.mem_Icc.mp i.property).1
  let a := Real.log ((2 * (i : ℕ) : ℕ) : ℝ)
  let b := Real.log ((2 * (i : ℕ) + 2 : ℕ) : ℝ)
  let F := (⋃ j : Finset.Icc 1 X, Ioo (Real.log ((2 * (j : ℕ) : ℕ) : ℝ))
    (Real.log ((2 * (j : ℕ) + 2 : ℕ) : ℝ)))ᶜ
  have hwidth : b - a = logCellWidth (i : ℕ) := haarPairWidth ha
  have hab : a < b := by
    apply sub_pos.mp
    rw [hwidth]
    exact logCellWidth_pos ha
  have hw : b - a ≤ 1 := by
    rw [hwidth]
    exact (logCellWidth_le_inv ha).trans
      ((div_le_one (by positivity : (0 : ℝ) < (i : ℕ))).mpr (by exact_mod_cast ha))
  have hF : F ⊆ (Ioo a b)ᶜ := fun _ hy hi => hy (mem_iUnion.mpr ⟨i, hi⟩)
  have h := gamma_interval_far_charge_le hab hw hF (q i)
  rw [hwidth] at h
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

#print axioms completePairGammaRowConstant_nonneg
#print axioms completePairGammaErrorRow_le
#print axioms completePairExteriorCharge_ne_top

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
