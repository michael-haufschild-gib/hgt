import GaloisForLFunctions.ArithmeticIndexDescent.TheCenteredSquareSourceHasAGammaMassBound
import GaloisForLFunctions.ArithmeticIndexDescent.CompleteCellAveragesAreBoundedInGammaEnergy
import GaloisForLFunctions.ArithmeticIndexDescent.GammaBoundedCompleteProfilesHaveCompactDetails

/-!
# Uniformly small tails of the actual mixed square-prime source

Pair averages are orthogonal to balanced details in ordinary square mass.
Their mean and constant-multiplier corrections therefore vanish exactly.
The centred mixed-source estimate and reciprocal-width tail payment make
the literal mixed even-prime source arbitrarily small in the Gamma energy
of the original complete profile, uniformly over all horizons.
-/

noncomputable section
open MeasureTheory Set Filter
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells HTGeometry

/-- The literal even-prime source remaining after its two diagonal blocks are removed. -/
def squarePrimeMixedSource (q d : ℕ → ℝ) (X : ℕ) : ℝ :=
  squarePrimeSource (completePairProfile q d X) - squarePrimeSource (averageSectionProfile q X) -
    squarePrimeSource (haarSectionProfile d X)

private theorem integral_average_mul_haarProfile (q : ℕ → ℝ) {a X : ℕ}
    (ha : 1 ≤ a) (haX : a ≤ X) :
    (∫ x, averageSectionProfile q X x * haarProfile a x) = 0 := by
  have he : (∫ x, averageSectionProfile q X x * haarProfile a x) =
      ∫ x, q a * haarProfile a x := by
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne volume (Real.log ((2 * a : ℕ) : ℝ))] with x hx
    by_cases hm : x ∈ Ioo (Real.log ((2 * a : ℕ) : ℝ)) (Real.log ((2 * a + 2 : ℕ) : ℝ))
    · rw [averageSectionProfile_eq_on_pair q ha haX hm]
    · have hz : haarProfile a x = 0 := by
        apply haarProfile_zero_outside_pair ha
        intro hi
        apply hm
        refine ⟨?_, hi.2⟩
        rcases lt_or_eq_of_le hi.1 with hl | heq
        · exact hl
        · exact False.elim (hx heq.symm)
      rw [hz, mul_zero, mul_zero]
  rw [he, integral_const_mul, integral_haarProfile ha, mul_zero]

/-- Actual pair averages and balanced details are orthogonal before any smoothing. -/
theorem integral_average_mul_haarSection (q d : ℕ → ℝ) (X : ℕ) :
    (∫ x, averageSectionProfile q X x * haarSectionProfile d X x) = 0 := by
  have hg := memLp_compact_bv (averageSectionProfile_bv q X) (averageSectionProfile_compact q X)
  have hh (a : ℕ) := memLp_compact_bv (haarProfile_bv a) (haarProfile_compact a)
  have hprod (a : ℕ) : Integrable (fun x => averageSectionProfile q X x * (d a * haarProfile a x)) :=
    hg.integrable_mul ((hh a).const_mul (d a))
  simp only [haarSectionProfile, Finset.mul_sum]
  rw [integral_finsetSum (Finset.Icc 1 X) (fun a _ => hprod a)]
  apply Finset.sum_eq_zero
  intro a ha
  have he : (fun x => averageSectionProfile q X x * (d a * haarProfile a x)) =
      fun x => d a * (averageSectionProfile q X x * haarProfile a x) := by
    funext x
    ring
  rw [he, integral_const_mul, integral_average_mul_haarProfile q
    (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2, mul_zero]

private theorem integral_averageSectionProfile_exists (q : ℕ → ℝ) (X : ℕ) :
    Integrable (averageSectionProfile q X) := by
  simpa only [mul_one] using integrable_compact_bv_mul
    (averageSectionProfile_bv q X) (averageSectionProfile_compact q X)
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))

private theorem completePairProfile_mean_eq_average (q d : ℕ → ℝ) (X : ℕ) :
    (∫ x, completePairProfile q d X x) = ∫ x, averageSectionProfile q X x := by
  change (∫ x, averageSectionProfile q X x + haarSectionProfile d X x) = _
  rw [integral_add (integral_averageSectionProfile_exists q X)
    (integrable_haarSectionProfile d X), integral_haarSectionProfile, add_zero]

/-- The complete profile has the exact orthogonal sum of its average and detail square masses. -/
theorem integral_completePairProfile_sq (q d : ℕ → ℝ) (X : ℕ) :
    (∫ x, completePairProfile q d X x ^ 2) =
      (∫ x, averageSectionProfile q X x ^ 2) + ∫ x, haarSectionProfile d X x ^ 2 := by
  have hg := memLp_compact_bv (averageSectionProfile_bv q X) (averageSectionProfile_compact q X)
  have hh := memLp_haarSectionProfile d X
  have hgh : Integrable (fun x => averageSectionProfile q X x * haarSectionProfile d X x) :=
    hg.integrable_mul hh
  have hleft : Integrable (fun x => averageSectionProfile q X x ^ 2 +
      2 * (averageSectionProfile q X x * haarSectionProfile d X x)) :=
    hg.integrable_sq.add (hgh.const_mul 2)
  have he : (fun x => completePairProfile q d X x ^ 2) = fun x =>
      (averageSectionProfile q X x ^ 2 +
        2 * (averageSectionProfile q X x * haarSectionProfile d X x)) +
          haarSectionProfile d X x ^ 2 := by
    funext x
    unfold completePairProfile
    ring
  rw [he, integral_add hleft hh.integrable_sq,
    integral_add hg.integrable_sq (hgh.const_mul 2), integral_const_mul,
    integral_average_mul_haarSection, mul_zero, add_zero]

/-- Both corrections cancel exactly on original average-detail profiles. -/
theorem squarePrimeMixedSource_eq_centered (q d : ℕ → ℝ) (X : ℕ) :
    squarePrimeMixedSource q d X =
      centeredSquarePrimeSource (completePairProfile q d X) -
        centeredSquarePrimeSource (averageSectionProfile q X) -
          centeredSquarePrimeSource (haarSectionProfile d X) := by
  simp only [squarePrimeMixedSource, centeredSquarePrimeSource,
    completePairProfile_mean_eq_average, integral_completePairProfile_sq,
    integral_haarSectionProfile, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
  ring

/-- No coarse ordinary mass is charged in the mixed square estimate. -/
theorem exists_squarePrimeMixed_gamma_mass_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      |squarePrimeMixedSource q d X| ≤
        ε * (levyEnergy (averageSectionProfile q X) + levyEnergy (haarSectionProfile d X)) +
          C * ∫ x, haarSectionProfile d X x ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_centeredSquareSource_gamma_mass_bv hε
  refine ⟨C, hC, ?_⟩
  intro q d X
  rw [squarePrimeMixedSource_eq_centered]
  exact hb _ _ (averageSectionProfile_bv q X) (averageSectionProfile_compact q X)
    (haarSectionProfile_bv d X) (haarSectionProfile_compact d X)

private theorem gamma_coarse_add_detail_tail_le (q d : ℕ → ℝ) (A X : ℕ) :
    levyEnergy (averageSectionProfile q X) +
        levyEnergy (haarSectionProfile (fun a => if A ≤ a then d a else 0) X) ≤
      (2 + 16 * haarGammaUpperConstant) * levyEnergy (completePairProfile q d X) := by
  have hweighted : (∑ a ∈ Finset.Icc 1 X,
      cellGammaWeight a * haarMass a * (if A ≤ a then d a else 0) ^ 2) ≤
      ∑ a ∈ Finset.Icc 1 X, cellGammaWeight a * haarMass a * d a ^ 2 := by
    apply Finset.sum_le_sum
    intro a ha
    by_cases hAa : A ≤ a
    · rw [if_pos hAa]
    · rw [if_neg hAa, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
      exact mul_nonneg (mul_nonneg (cellGammaWeight_pos (Finset.mem_Icc.mp ha).1).le
        (haarMass_pos (Finset.mem_Icc.mp ha).1).le) (sq_nonneg _)
  have htail := (haarSectionProfile_gamma_le_weighted_mass
    (fun a => if A ≤ a then d a else 0) X).trans
      (mul_le_mul_of_nonneg_left
        (hweighted.trans (completePairProfile_gamma_ge_weighted_detail q d X))
        (mul_nonneg (by norm_num) haarGammaUpperConstant_pos.le))
  have hproj := completePairProfile_gamma_pays_coarse_and_detail q d X
  have hh := levyEnergy_nonneg_bv (haarSectionProfile_bv d X) (haarSectionProfile_compact d X)
  linarith only [htail, hproj, hh]

/-- One cutoff makes the actual mixed even-prime tail arbitrarily small in the original Gamma energy. -/
theorem exists_uniform_small_squarePrimeMixed_tail {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      |squarePrimeMixedSource q (fun a => if A ≤ a then d a else 0) X| ≤
        ε * levyEnergy (completePairProfile q d X) := by
  have hP : 0 < 2 + 16 * haarGammaUpperConstant := by
    have h := haarGammaUpperConstant_pos
    positivity
  have hη : 0 < ε / (2 * (2 + 16 * haarGammaUpperConstant)) := by positivity
  obtain ⟨C, hC, hmix⟩ := exists_squarePrimeMixed_gamma_mass_bound hη
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp (2 * C / ε))
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hcap : C ≤ (ε / 2) * cellGammaWeight A := by
    have hl := Real.log_lt_log (Real.exp_pos _) hA
    rw [Real.log_exp] at hl
    have hp := (div_le_iff₀ hε).mp (hl.le.trans (log_le_cellGammaWeight hA1))
    linarith only [hp]
  refine ⟨A, hA1, ?_⟩
  intro q d X
  have hmass : cellGammaWeight A *
      (∫ x, haarSectionProfile (fun a => if A ≤ a then d a else 0) X x ^ 2) ≤
        levyEnergy (completePairProfile q d X) := by
    rw [integral_haarSectionProfile_sq]
    exact cellGammaWeight_mul_haar_tail_mass_le_gamma q d hA1 X
  have hmass0 : 0 ≤ ∫ x, haarSectionProfile (fun a => if A ≤ a then d a else 0) X x ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hmasspay : C * (∫ x, haarSectionProfile (fun a => if A ≤ a then d a else 0) X x ^ 2) ≤
      (ε / 2) * levyEnergy (completePairProfile q d X) := by
    calc _ ≤ ((ε / 2) * cellGammaWeight A) *
          (∫ x, haarSectionProfile (fun a => if A ≤ a then d a else 0) X x ^ 2) :=
            mul_le_mul_of_nonneg_right hcap hmass0
      _ = (ε / 2) * (cellGammaWeight A *
          ∫ x, haarSectionProfile (fun a => if A ≤ a then d a else 0) X x ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  have hgammapay := mul_le_mul_of_nonneg_left (gamma_coarse_add_detail_tail_le q d A X) hη.le
  have he : ε / (2 * (2 + 16 * haarGammaUpperConstant)) *
      ((2 + 16 * haarGammaUpperConstant) * levyEnergy (completePairProfile q d X)) =
        (ε / 2) * levyEnergy (completePairProfile q d X) := by
    field_simp [hP.ne']
  rw [he] at hgammapay
  have hm := hmix q (fun a => if A ≤ a then d a else 0) X
  linarith only [hm, hgammapay, hmasspay]

end GaloisForLFunctions.ArithmeticIndexDescent
