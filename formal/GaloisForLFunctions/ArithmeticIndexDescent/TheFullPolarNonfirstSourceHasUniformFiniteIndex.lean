import GaloisForLFunctions.ArithmeticIndexDescent.EveryMixedExponentAboveOneLeavesACoarseReserve

/-!
# Full polar payment alongside every mixed exponent above one

The two exponential moments bound the detail pole in absolute value by
ordinary detail mass. A fixed part of the logarithmic detail reserve pays
its removal. Restoring the actual complete-profile pole leaves its positive
cosh square and only one adverse sinh square. One finite detail head and
that original sinh moment therefore bound negative dimension uniformly.
-/

noncomputable section
open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells HTGeometry

/-- The positive part of the detail pole also costs at most twice its exact square mass. -/
theorem haarSectionProfile_pole_le_mass (d : ℕ → ℝ) (X : ℕ) :
    2 * coshHalfMoment (haarSectionProfile d X) ^ 2 -
        2 * sinhHalfMoment (haarSectionProfile d X) ^ 2 ≤
      2 * ∫ x, haarSectionProfile d X x ^ 2 := by
  have hp : Integrable (fun x => Real.exp (x / 2) * haarSectionProfile d X x) := by
    simpa only [mul_comm] using integrable_compact_bv_mul (haarSectionProfile_bv d X)
      (haarSectionProfile_compact d X) (show Continuous (fun x : ℝ => Real.exp (x / 2)) by fun_prop)
  have hm : Integrable (fun x => Real.exp (-(x / 2)) * haarSectionProfile d X x) := by
    simpa only [mul_comm] using integrable_compact_bv_mul (haarSectionProfile_bv d X)
      (haarSectionProfile_compact d X) (show Continuous (fun x : ℝ => Real.exp (-(x / 2))) by fun_prop)
  have hps : (∫ x, Real.exp (x / 2) * haarSectionProfile d X x) ^ 2 ≤
      ∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2 := by
    simpa only [mul_comm] using haarSectionProfile_exp_pos_sq_le d X
  have hms : (∫ x, Real.exp (-(x / 2)) * haarSectionProfile d X x) ^ 2 ≤
      ∑ a ∈ Finset.Icc 1 X, haarMass a * d a ^ 2 := by
    simpa only [neg_div, mul_comm] using haarSectionProfile_exp_neg_sq_le d X
  rw [(halfMoments_eq_exp hp hm).1, (halfMoments_eq_exp hp hm).2, integral_haarSectionProfile_sq]
  nlinarith only [hps, hms,
    sq_nonneg ((∫ x, Real.exp (x / 2) * haarSectionProfile d X x) -
      ∫ x, Real.exp (-(x / 2)) * haarSectionProfile d X x)]

/-- The same source includes the full actual pole, including its coarse and mixed terms. -/
def fullPolarNonfirstSourceForm (q d : ℕ → ℝ) (X : ℕ) : ℝ :=
  levyEnergy (completePairProfile q d X) +
    2 * gammaHardyPhaseRate 0 * (∫ x, haarSectionProfile d X x ^ 2) -
      haarPrimeEnergy d X - squarePrimeMixedSource q d X - oddHigherPrimePowerMixedSource d q X +
      (2 * coshHalfMoment (completePairProfile q d X) ^ 2 -
        2 * sinhHalfMoment (completePairProfile q d X) ^ 2)

/-- Replacing the detail pole by the complete pole is an exact identity on the original profiles. -/
theorem fullPolarNonfirstSourceForm_eq (q d : ℕ → ℝ) (X : ℕ) :
    fullPolarNonfirstSourceForm q d X = fullDetailNonfirstMixedSourceForm q d X -
      (2 * coshHalfMoment (haarSectionProfile d X) ^ 2 -
        2 * sinhHalfMoment (haarSectionProfile d X) ^ 2) +
      (2 * coshHalfMoment (completePairProfile q d X) ^ 2 -
        2 * sinhHalfMoment (completePairProfile q d X) ^ 2) := by
  rw [fullDetailNonfirstMixedSourceForm, fullDetailCoupledSourceForm_eq_source_parts]
  unfold fullPolarNonfirstSourceForm
  ring

private theorem mass_le_weighted_of_high_detail {A : ℕ} (hA : 1 ≤ A)
    (d : ℕ → ℝ) (X : ℕ) (hd : ∀ a : ℕ, a < A → d a = 0) :
    cellGammaWeight A * (∫ x, haarSectionProfile d X x ^ 2) ≤ haarLogarithmicMass d X := by
  rw [integral_haarSectionProfile_sq, haarLogarithmicMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hAa : A ≤ a
  · have hm := mul_nonneg (haarMass_pos (Finset.mem_Icc.mp ha).1).le (sq_nonneg (d a))
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (cellGammaWeight_mono hA hAa) hm
  · rw [hd a (by omega)]
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]

/-- The actual full pole leaves one adverse scalar square after the shared source payment. -/
theorem exists_fullPolarNonfirst_coarse_reserve (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a : ℕ, a < A → d a = 0) →
      (1 - ε) * levyEnergy (averageSectionProfile q X) +
          (fullDetailPrimeGap / 8) * haarLogarithmicMass d X +
          (∫ x, haarSectionProfile d X x ^ 2) +
          2 * coshHalfMoment (completePairProfile q d X) ^ 2 ≤
        fullPolarNonfirstSourceForm q d X +
          2 * sinhHalfMoment (completePairProfile q d X) ^ 2 := by
  obtain ⟨A₀, hA₀, hbase⟩ := exists_fullDetailNonfirstMixed_coarse_reserve ε hε
  obtain ⟨A₁, hA₁⟩ := exists_nat_gt (Real.exp (16 / fullDetailPrimeGap))
  have hA₁1 : 1 ≤ A₁ := by
    have hp : (0 : ℝ) < A₁ := (Real.exp_pos _).trans hA₁
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hcap : 2 ≤ (fullDetailPrimeGap / 8) * cellGammaWeight A₁ := by
    have hl := Real.log_lt_log (Real.exp_pos _) hA₁
    rw [Real.log_exp] at hl
    have hp := (div_le_iff₀ fullDetailPrimeGap_pos).mp
      (hl.le.trans (log_le_cellGammaWeight hA₁1))
    linarith only [hp]
  refine ⟨max A₀ A₁, hA₀.trans (le_max_left _ _), ?_⟩
  intro q d X hd
  have hd₀ (a : ℕ) (ha : a < A₀) : d a = 0 := hd a (ha.trans_le (le_max_left _ _))
  have hd₁ (a : ℕ) (ha : a < A₁) : d a = 0 := hd a (ha.trans_le (le_max_right _ _))
  have hM : 0 ≤ ∫ x, haarSectionProfile d X x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hm := mul_le_mul_of_nonneg_left (mass_le_weighted_of_high_detail hA₁1 d X hd₁)
    (div_nonneg fullDetailPrimeGap_pos.le (by norm_num : (0 : ℝ) ≤ 8))
  have hc := mul_le_mul_of_nonneg_right hcap hM
  have hmass : 2 * (∫ x, haarSectionProfile d X x ^ 2) ≤
      (fullDetailPrimeGap / 8) * haarLogarithmicMass d X := by
    nlinarith only [hm, hc]
  have hb := hbase q d X hd₀
  have hp := haarSectionProfile_pole_le_mass d X
  rw [fullPolarNonfirstSourceForm_eq]
  linarith only [hb, hp, hmass]

/-- The same estimate holds on the literal tail of every coefficient family. -/
theorem exists_fullPolarNonfirst_uniform_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      let t := haarTailCoeffs A d
      (1 - ε) * levyEnergy (averageSectionProfile q X) +
          (fullDetailPrimeGap / 8) * haarLogarithmicMass t X +
          (∫ x, haarSectionProfile t X x ^ 2) +
          2 * coshHalfMoment (completePairProfile q t X) ^ 2 ≤
        fullPolarNonfirstSourceForm q t X +
          2 * sinhHalfMoment (completePairProfile q t X) ^ 2 := by
  obtain ⟨A, hA, hpay⟩ := exists_fullPolarNonfirst_coarse_reserve ε hε
  refine ⟨A, hA, ?_⟩
  intro q d X
  apply hpay q (haarTailCoeffs A d) X
  intro a ha
  exact if_neg (by omega : ¬A ≤ a)

/-- The adverse moment is exactly linear on every original finite family of profiles. -/
theorem sinhHalfMoment_completePairProfile_linearCombination {n : ℕ}
    (q d : Fin n → ℕ → ℝ) (X : ℕ) (x : Fin n → ℝ) :
    sinhHalfMoment (completePairProfile (fun a => ∑ i, x i * q i a)
      (fun a => ∑ i, x i * d i a) X) =
        ∑ i, x i * sinhHalfMoment (completePairProfile (q i) (d i) X) := by
  have he (y : ℝ) : completePairProfile (fun a => ∑ i, x i * q i a)
      (fun a => ∑ i, x i * d i a) X y = ∑ i, x i * completePairProfile (q i) (d i) X y := by
    simp only [completePairProfile, averageSectionProfile, haarSectionProfile,
      Finset.sum_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_assoc]
    congr 1 <;> exact Finset.sum_comm
  have hi (i : Fin n) : Integrable (fun y => completePairProfile (q i) (d i) X y *
      Real.sinh (y / 2)) := integrable_compact_bv_mul (completePairProfile_bv (q i) (d i) X)
        (completePairProfile_compact (q i) (d i) X) (by fun_prop)
  simp only [sinhHalfMoment, he, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum Finset.univ (fun i _ => (hi i).const_mul (x i))]
  simp only [integral_const_mul]

/-- The source with the full original pole on a finite complete-profile family. -/
def fullPolarNonfirstProfileForm {n : ℕ} (q d : Fin n → ℕ → ℝ) (X : ℕ)
    (x : Fin n → ℝ) : ℝ :=
  fullPolarNonfirstSourceForm (fun a => ∑ i, x i * q i a) (fun a => ∑ i, x i * d i a) X

private def fullPolarDetailReadout {n : ℕ} (q d : Fin n → ℕ → ℝ) (X A : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin (A + 1) → ℝ) where
  toFun x a := if (a : ℕ) < A then ∑ i, x i * d i a else
    ∑ i, x i * sinhHalfMoment (completePairProfile (q i) (d i) X)
  map_add' x y := by
    funext a
    simp only [Pi.add_apply]
    split_ifs <;> simp only [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp only [mul_assoc, Finset.mul_sum]
    all_goals rfl

/-- Full polar self and cross terms cost only the single actual sinh readout beyond the detail head. -/
theorem exists_uniform_fullPolarNonfirst_negative_dimension :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (n : ℕ) (q d : Fin n → ℕ → ℝ) (X : ℕ)
      (W : Submodule ℝ (Fin n → ℝ)),
      (∀ x ∈ W, x ≠ 0 → fullPolarNonfirstProfileForm q d X x < 0) →
        Module.finrank ℝ W ≤ A + 1 := by
  obtain ⟨A, hA, hpay⟩ := exists_fullPolarNonfirst_coarse_reserve (1 / 2) (by norm_num)
  refine ⟨A, hA, ?_⟩
  intro n q d X W hW
  let T := fullPolarDetailReadout q d X A
  have hnonneg (x : Fin n → ℝ) (hx : T x = 0) : 0 ≤ fullPolarNonfirstProfileForm q d X x := by
    have hz (a : ℕ) (ha : a < A) : (∑ i, x i * d i a) = 0 := by
      have h : (if a < A then ∑ i, x i * d i a else
          ∑ i, x i * sinhHalfMoment (completePairProfile (q i) (d i) X)) = 0 :=
        congrFun hx (⟨a, by omega⟩ : Fin (A + 1))
      simpa only [if_pos ha] using h
    have hs : sinhHalfMoment (completePairProfile (fun a => ∑ i, x i * q i a)
        (fun a => ∑ i, x i * d i a) X) = 0 := by
      have h : (if A < A then ∑ i, x i * d i A else
          ∑ i, x i * sinhHalfMoment (completePairProfile (q i) (d i) X)) = 0 :=
        congrFun hx (⟨A, by omega⟩ : Fin (A + 1))
      rw [sinhHalfMoment_completePairProfile_linearCombination]
      simpa only [if_neg (by omega : ¬A < A)] using h
    have hp := hpay (fun a => ∑ i, x i * q i a) (fun a => ∑ i, x i * d i a) X hz
    rw [hs, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at hp
    have hG := levyEnergy_nonneg_bv (averageSectionProfile_bv (fun a => ∑ i, x i * q i a) X)
      (averageSectionProfile_compact (fun a => ∑ i, x i * q i a) X)
    have hD := haarLogarithmicMass_nonneg (fun a => ∑ i, x i * d i a) X
    have hM : 0 ≤ ∫ y, haarSectionProfile (fun a => ∑ i, x i * d i a) X y ^ 2 :=
      integral_nonneg fun y => sq_nonneg _
    have hκ := fullDetailPrimeGap_pos
    have hl : 0 ≤ (1 - (1 / 2 : ℝ)) *
        levyEnergy (averageSectionProfile (fun a => ∑ i, x i * q i a) X) +
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
