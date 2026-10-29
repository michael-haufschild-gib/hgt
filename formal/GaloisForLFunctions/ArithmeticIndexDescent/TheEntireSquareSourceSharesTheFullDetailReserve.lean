import GaloisForLFunctions.ArithmeticIndexDescent.TheFullPolarNonfirstSourceHasUniformFiniteIndex

/-!
# Entire square source with the full detail and polar payment

The retained coarse Gamma share pays the coarse even-prime source without
spending the complete-profile energy again. Together with the already paid
mixed and detail blocks, this includes the entire even-prime source exactly
once. Positive coarse and detail reserves remain. The full original pole
and the square-source mean term leave two scalar costs, so one fixed detail
head and those two original moments bound negative dimension uniformly.
-/

noncomputable section
open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells HTGeometry

/-- Add the missing coarse square source to the joint detail, mixed, and full-polar source. -/
def fullSquarePolarSourceForm (q d : ℕ → ℝ) (X : ℕ) : ℝ :=
  fullPolarNonfirstSourceForm q d X - squarePrimeSource (averageSectionProfile q X)

/-- The entire even-prime source occurs exactly once in the original complete profile. -/
theorem fullSquarePolarSourceForm_eq_source_parts (q d : ℕ → ℝ) (X : ℕ) :
    fullSquarePolarSourceForm q d X =
      levyEnergy (completePairProfile q d X) +
        2 * gammaHardyPhaseRate 0 * (∫ x, haarSectionProfile d X x ^ 2) -
        (haarPrimeEnergy d X - squarePrimeSource (haarSectionProfile d X)) -
        squarePrimeSource (completePairProfile q d X) - oddHigherPrimePowerMixedSource d q X +
        (2 * coshHalfMoment (completePairProfile q d X) ^ 2 -
          2 * sinhHalfMoment (completePairProfile q d X) ^ 2) := by
  unfold fullSquarePolarSourceForm fullPolarNonfirstSourceForm squarePrimeMixedSource
  ring

/-- Balanced details do not alter the ordinary mean of the original profile. -/
theorem integral_completePairProfile_eq_average (q d : ℕ → ℝ) (X : ℕ) :
    (∫ x, completePairProfile q d X x) = ∫ x, averageSectionProfile q X x := by
  have hg : Integrable (averageSectionProfile q X) := by
    simpa only [mul_one] using integrable_compact_bv_mul
      (averageSectionProfile_bv q X) (averageSectionProfile_compact q X)
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  change (∫ x, averageSectionProfile q X x + haarSectionProfile d X x) = _
  rw [integral_add hg (integrable_haarSectionProfile d X), integral_haarSectionProfile, add_zero]

/-- Paying the coarse square source leaves positive coarse and detail reserves jointly. -/
theorem exists_fullSquarePolar_coarse_detail_reserve :
    ∃ c : ℝ, 0 < c ∧ ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a : ℕ, a < A → d a = 0) →
      c * levyEnergy (averageSectionProfile q X) +
          (Real.eulerMascheroniConstant / 2) * (∫ x, averageSectionProfile q X x ^ 2) +
          (fullDetailPrimeGap / 8) * haarLogarithmicMass d X +
          (∫ x, haarSectionProfile d X x ^ 2) +
          2 * coshHalfMoment (completePairProfile q d X) ^ 2 ≤
        fullSquarePolarSourceForm q d X +
          2 * sinhHalfMoment (completePairProfile q d X) ^ 2 +
          (1 / 2 : ℝ) * (∫ x, completePairProfile q d X x) ^ 2 := by
  obtain ⟨δ, hδ, hsquare⟩ := exists_squarePrime_retained_gamma_bv
  obtain ⟨A, hA, hbase⟩ := exists_fullPolarNonfirst_coarse_reserve (δ / 2) (by positivity)
  refine ⟨δ / 2, by positivity, A, hA, ?_⟩
  intro q d X hd
  have hb := hbase q d X hd
  have hs := hsquare (averageSectionProfile q X)
    (averageSectionProfile_bv q X) (averageSectionProfile_compact q X)
  rw [fullSquarePolarSourceForm, integral_completePairProfile_eq_average]
  linarith only [hb, hs]

/-- The same payment holds on the literal detail tail of every original coefficient family. -/
theorem exists_fullSquarePolar_uniform_tail :
    ∃ c : ℝ, 0 < c ∧ ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      let t := haarTailCoeffs A d
      c * levyEnergy (averageSectionProfile q X) +
          (Real.eulerMascheroniConstant / 2) * (∫ x, averageSectionProfile q X x ^ 2) +
          (fullDetailPrimeGap / 8) * haarLogarithmicMass t X +
          (∫ x, haarSectionProfile t X x ^ 2) +
          2 * coshHalfMoment (completePairProfile q t X) ^ 2 ≤
        fullSquarePolarSourceForm q t X +
          2 * sinhHalfMoment (completePairProfile q t X) ^ 2 +
          (1 / 2 : ℝ) * (∫ x, completePairProfile q t X x) ^ 2 := by
  obtain ⟨c, hc, A, hA, hpay⟩ := exists_fullSquarePolar_coarse_detail_reserve
  refine ⟨c, hc, A, hA, ?_⟩
  intro q d X
  apply hpay q (haarTailCoeffs A d) X
  intro a ha
  exact if_neg (by omega : ¬A ≤ a)

/-- The ordinary mean is the actual linear readout on every finite complete-profile family. -/
private theorem integral_completePairProfile_linearCombination {n : ℕ}
    (q d : Fin n → ℕ → ℝ) (X : ℕ) (x : Fin n → ℝ) :
    (∫ y, completePairProfile (fun a => ∑ i, x i * q i a)
      (fun a => ∑ i, x i * d i a) X y) =
        ∑ i, x i * ∫ y, completePairProfile (q i) (d i) X y := by
  have he (y : ℝ) : completePairProfile (fun a => ∑ i, x i * q i a)
      (fun a => ∑ i, x i * d i a) X y = ∑ i, x i * completePairProfile (q i) (d i) X y := by
    simp only [completePairProfile, averageSectionProfile, haarSectionProfile,
      Finset.sum_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_assoc]
    congr 1 <;> exact Finset.sum_comm
  have hi (i : Fin n) : Integrable (completePairProfile (q i) (d i) X) := by
    simpa only [mul_one] using integrable_compact_bv_mul
      (completePairProfile_bv (q i) (d i) X) (completePairProfile_compact (q i) (d i) X)
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  simp only [he]
  rw [integral_finsetSum Finset.univ (fun i _ => (hi i).const_mul (x i))]
  simp only [integral_const_mul]

/-- The joint source on arbitrary finite families of original complete profiles. -/
def fullSquarePolarProfileForm {n : ℕ} (q d : Fin n → ℕ → ℝ) (X : ℕ)
    (x : Fin n → ℝ) : ℝ :=
  fullSquarePolarSourceForm (fun a => ∑ i, x i * q i a) (fun a => ∑ i, x i * d i a) X

private def fullSquarePolarReadout {n : ℕ} (q d : Fin n → ℕ → ℝ) (X A : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin (A + 2) → ℝ) where
  toFun x a := if (a : ℕ) < A then ∑ i, x i * d i a else
    if (a : ℕ) = A then ∑ i, x i * sinhHalfMoment (completePairProfile (q i) (d i) X) else
      ∑ i, x i * ∫ y, completePairProfile (q i) (d i) X y
  map_add' x y := by
    funext a
    simp only [Pi.add_apply]
    split_ifs <;> simp only [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp only [mul_assoc, Finset.mul_sum]
    all_goals rfl

/-- One fixed detail head and the two original scalar moments bound negative dimension. -/
theorem exists_uniform_fullSquarePolar_negative_dimension :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (n : ℕ) (q d : Fin n → ℕ → ℝ) (X : ℕ)
      (W : Submodule ℝ (Fin n → ℝ)),
      (∀ x ∈ W, x ≠ 0 → fullSquarePolarProfileForm q d X x < 0) →
        Module.finrank ℝ W ≤ A + 2 := by
  obtain ⟨c, hc, A, hA, hpay⟩ := exists_fullSquarePolar_coarse_detail_reserve
  refine ⟨A, hA, ?_⟩
  intro n q d X W hW
  let T := fullSquarePolarReadout q d X A
  have hnonneg (x : Fin n → ℝ) (hx : T x = 0) : 0 ≤ fullSquarePolarProfileForm q d X x := by
    have hz (a : ℕ) (ha : a < A) : (∑ i, x i * d i a) = 0 := by
      have h : (if a < A then ∑ i, x i * d i a else
          if a = A then ∑ i, x i * sinhHalfMoment (completePairProfile (q i) (d i) X) else
            ∑ i, x i * ∫ y, completePairProfile (q i) (d i) X y) = 0 :=
        congrFun hx (⟨a, by omega⟩ : Fin (A + 2))
      simpa only [if_pos ha] using h
    have hs : sinhHalfMoment (completePairProfile (fun a => ∑ i, x i * q i a)
        (fun a => ∑ i, x i * d i a) X) = 0 := by
      have h : (if A < A then ∑ i, x i * d i A else
          if A = A then ∑ i, x i * sinhHalfMoment (completePairProfile (q i) (d i) X) else
            ∑ i, x i * ∫ y, completePairProfile (q i) (d i) X y) = 0 :=
        congrFun hx (⟨A, by omega⟩ : Fin (A + 2))
      rw [sinhHalfMoment_completePairProfile_linearCombination]
      rw [if_neg (by omega : ¬A < A), if_pos (rfl : A = A)] at h
      exact h
    have hm : (∫ y, completePairProfile (fun a => ∑ i, x i * q i a)
        (fun a => ∑ i, x i * d i a) X y) = 0 := by
      have h : (if A + 1 < A then ∑ i, x i * d i (A + 1) else
          if A + 1 = A then ∑ i, x i * sinhHalfMoment (completePairProfile (q i) (d i) X) else
            ∑ i, x i * ∫ y, completePairProfile (q i) (d i) X y) = 0 :=
        congrFun hx (⟨A + 1, by omega⟩ : Fin (A + 2))
      rw [integral_completePairProfile_linearCombination]
      simpa only [if_neg (by omega : ¬A + 1 < A), if_neg (by omega : A + 1 ≠ A)] using h
    have hp := hpay (fun a => ∑ i, x i * q i a) (fun a => ∑ i, x i * d i a) X hz
    simp only [hs, hm, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at hp
    have hG := levyEnergy_nonneg_bv (averageSectionProfile_bv (fun a => ∑ i, x i * q i a) X)
      (averageSectionProfile_compact (fun a => ∑ i, x i * q i a) X)
    have hD := haarLogarithmicMass_nonneg (fun a => ∑ i, x i * d i a) X
    have hMg : 0 ≤ ∫ y, averageSectionProfile (fun a => ∑ i, x i * q i a) X y ^ 2 :=
      integral_nonneg fun y => sq_nonneg _
    have hMh : 0 ≤ ∫ y, haarSectionProfile (fun a => ∑ i, x i * d i a) X y ^ 2 :=
      integral_nonneg fun y => sq_nonneg _
    have hκ := fullDetailPrimeGap_pos
    have hγ : 0 < Real.eulerMascheroniConstant :=
      (by norm_num : (0 : ℝ) < 1 / 2).trans Real.one_half_lt_eulerMascheroniConstant
    have hl : 0 ≤ c * levyEnergy (averageSectionProfile (fun a => ∑ i, x i * q i a) X) +
        (Real.eulerMascheroniConstant / 2) *
          (∫ y, averageSectionProfile (fun a => ∑ i, x i * q i a) X y ^ 2) +
        (fullDetailPrimeGap / 8) * haarLogarithmicMass (fun a => ∑ i, x i * d i a) X +
        (∫ y, haarSectionProfile (fun a => ∑ i, x i * d i a) X y ^ 2) +
        2 * coshHalfMoment (completePairProfile (fun a => ∑ i, x i * q i a)
          (fun a => ∑ i, x i * d i a) X) ^ 2 := by positivity
    exact hl.trans hp
  have hker : LinearMap.ker (T.domRestrict W) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hx
    by_contra hx0
    have hv : (x : Fin n → ℝ) ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
    exact (not_lt_of_ge (hnonneg x hx)) (hW x x.property hv)
  have hinj : Function.Injective (T.domRestrict W) := LinearMap.ker_eq_bot.mp hker
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hd

end GaloisForLFunctions.ArithmeticIndexDescent
