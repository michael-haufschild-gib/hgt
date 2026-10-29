import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaCouplingUsesOnlyDetailMass
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellEffectivity
import GaloisForLFunctions.ArithmeticIndexDescent.CompleteCellAveragesAreBoundedInGammaEnergy

/-!
# Full detail payment with retained coarse Gamma energy

The entire Haar Weil diagonal includes every prime power, its archimedean
mass and its actual pole product. Its logarithmic surplus pays the Gamma
coupling to arbitrary pair averages, with any prescribed coarse Gamma loss.
The same reserve also pays all mixed prime powers of exponent at least three.
One detail cutoff works for every signed source and every support horizon.
-/

noncomputable section
open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- The positive gap between the Gamma and full-prime logarithmic coefficients. -/
def fullDetailPrimeGap : ℝ := 1 - 1 / Real.sqrt 2

theorem fullDetailPrimeGap_pos : 0 < fullDetailPrimeGap :=
  sub_pos.mpr haarPrime_log_coefficient_lt_one

/-- Exact reciprocal-width square mass of the actual balanced details. -/
def haarLogarithmicMass (d : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X, cellGammaWeight a * haarMass a * d a ^ 2

theorem haarLogarithmicMass_nonneg (d : ℕ → ℝ) (X : ℕ) :
    0 ≤ haarLogarithmicMass d X := by
  apply Finset.sum_nonneg
  intro a ha
  have ha1 := (Finset.mem_Icc.mp ha).1
  exact mul_nonneg (mul_nonneg (cellGammaWeight_pos ha1).le (haarMass_pos ha1).le)
    (sq_nonneg _)

/-- Exact capacity and the arithmetic logarithm differ by a bounded mass cost. -/
theorem cellGammaWeight_le_log_add_one {a : ℕ} (ha : 1 ≤ a) :
    cellGammaWeight a ≤ Real.log (a : ℝ) + 1 := by
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have hw := logCellWidth_pos ha
  have hi : 1 / logCellWidth a ≤ (a : ℝ) + 1 := by
    apply (div_le_iff₀ hw).mpr
    have h := (div_le_iff₀ (by positivity : 0 < (a : ℝ) + 1)).mp
      (inv_add_one_le_logCellWidth ha)
    simpa only [mul_comm] using h
  have hlog := Real.log_le_log (div_pos zero_lt_one hw) hi
  have htwo : (a : ℝ) + 1 ≤ 2 * (a : ℝ) := by exact_mod_cast (show a + 1 ≤ 2 * a by omega)
  have hl := Real.log_le_log (by positivity : 0 < (a : ℝ) + 1) htwo
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0.ne'] at hl
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  change cellGammaWeight a ≤ _ at hlog
  linarith only [hlog, hl, hl2]

/-- The full original Haar Weil form retains its logarithmic surplus up to square mass. -/
theorem haarSectionProfile_roughWeil_ge_logarithmic_mass (d : ℕ → ℝ) (X : ℕ) :
    fullDetailPrimeGap * haarLogarithmicMass d X -
        (20 - 2 * gammaHardyPhaseRate 0 + fullDetailPrimeGap) *
          (∫ x, haarSectionProfile d X x ^ 2) ≤
      roughWeil (haarSectionProfile d X) := by
  apply le_trans ?_ (haarSectionProfile_roughWeil_ge d X)
  rw [haarLogarithmicMass, integral_haarSectionProfile_sq,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro a ha
  have ha1 := (Finset.mem_Icc.mp ha).1
  have hc := mul_le_mul_of_nonneg_left (cellGammaWeight_le_log_add_one ha1)
    fullDetailPrimeGap_pos.le
  have hp : fullDetailPrimeGap * cellGammaWeight a -
      (20 - 2 * gammaHardyPhaseRate 0 + fullDetailPrimeGap) ≤
      (1 - 1 / Real.sqrt 2) * Real.log (a : ℝ) + 2 * gammaHardyPhaseRate 0 - 20 := by
    change fullDetailPrimeGap * cellGammaWeight a - _ ≤
      fullDetailPrimeGap * Real.log (a : ℝ) + _ - _
    linarith only [hc]
  convert mul_le_mul_of_nonneg_right hp
    (mul_nonneg (haarMass_pos ha1).le (sq_nonneg (d a))) using 1 <;> ring

/-- Mean-zero Gamma coupling costs arbitrarily little coarse energy and fixed detail mass. -/
theorem abs_completeGammaMixed_le_coarse_add_mass (ε : ℝ) (hε : 0 < ε)
    (q d : ℕ → ℝ) (X : ℕ) :
    |completeGammaMixed q d X| ≤ ε * levyEnergy (averageSectionProfile q X) +
      (32 * Real.exp (1 / 2) / ε) * (∫ x, haarSectionProfile d X x ^ 2) := by
  let G := levyEnergy (averageSectionProfile q X)
  let M := ∫ x, haarSectionProfile d X x ^ 2
  let C := 32 * Real.exp (1 / 2) / ε
  have hG : 0 ≤ G := levyEnergy_nonneg_bv
    (averageSectionProfile_bv q X) (averageSectionProfile_compact q X)
  have hM : 0 ≤ M := integral_nonneg fun x => sq_nonneg (haarSectionProfile d X x)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hp : completeGammaMixed q d X ^ 2 ≤ 4 * (ε * G) * (C * M) := by
    apply (completeGammaMixed_sq_le q d X).trans_eq
    change 128 * Real.exp (1 / 2) * G * M = 4 * (ε * G) * (C * M)
    dsimp only [C]
    field_simp [hε.ne']
    ring
  have hs : |completeGammaMixed q d X| ^ 2 ≤ (ε * G + C * M) ^ 2 := by
    rw [sq_abs]
    nlinarith only [hp, sq_nonneg (ε * G - C * M)]
  exact (sq_le_sq₀ (abs_nonneg _) (add_nonneg (mul_nonneg hε.le hG)
    (mul_nonneg hC hM))).mp hs

/-- Coarse Gamma, mixed Gamma, and the full original Haar Weil diagonal in one source. -/
def fullDetailCoupledSourceForm (q d : ℕ → ℝ) (X : ℕ) : ℝ :=
  levyEnergy (completePairProfile q d X) - levyEnergy (haarSectionProfile d X) +
    roughWeil (haarSectionProfile d X)

/-- The coupled source keeps the entire prime series and the original polar moments. -/
theorem fullDetailCoupledSourceForm_eq_source_parts (q d : ℕ → ℝ) (X : ℕ) :
    fullDetailCoupledSourceForm q d X = levyEnergy (completePairProfile q d X) +
      2 * gammaHardyPhaseRate 0 * (∫ x, haarSectionProfile d X x ^ 2) -
      haarPrimeEnergy d X +
      (2 * coshHalfMoment (haarSectionProfile d X) ^ 2 -
        2 * sinhHalfMoment (haarSectionProfile d X) ^ 2) := by
  rw [haarPrimeEnergy_eq_primeSum]
  unfold fullDetailCoupledSourceForm roughWeil
  ring

/-- The unweighted detail cost left after retaining a prescribed coarse Gamma share. -/
def fullDetailMassCost (ε : ℝ) : ℝ :=
  32 * Real.exp (1 / 2) / ε + 20 - 2 * gammaHardyPhaseRate 0 + fullDetailPrimeGap

/-- All detail self-interactions and Gamma mixing admit one joint mass-error estimate. -/
theorem fullDetailCoupledSourceForm_ge (ε : ℝ) (hε : 0 < ε)
    (q d : ℕ → ℝ) (X : ℕ) :
    (1 - ε) * levyEnergy (averageSectionProfile q X) +
        fullDetailPrimeGap * haarLogarithmicMass d X -
        fullDetailMassCost ε * (∫ x, haarSectionProfile d X x ^ 2) ≤
      fullDetailCoupledSourceForm q d X := by
  have hmix := abs_completeGammaMixed_le_coarse_add_mass ε hε q d X
  have hneg := (abs_le.mp hmix).1
  have hdiag := haarSectionProfile_roughWeil_ge_logarithmic_mass d X
  have he : fullDetailCoupledSourceForm q d X = levyEnergy (averageSectionProfile q X) +
      completeGammaMixed q d X + roughWeil (haarSectionProfile d X) := by
    unfold fullDetailCoupledSourceForm completeGammaMixed
    ring
  rw [he]
  unfold fullDetailMassCost
  nlinarith only [hneg, hdiag]

/-- One fixed detail head leaves almost all coarse Gamma and a logarithmic detail reserve. -/
theorem exists_fullDetailCoupled_coarse_reserve (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a : ℕ, a < A → d a = 0) →
      (1 - ε) * levyEnergy (averageSectionProfile q X) +
          (fullDetailPrimeGap / 2) * haarLogarithmicMass d X +
          (∫ x, haarSectionProfile d X x ^ 2) ≤ fullDetailCoupledSourceForm q d X := by
  let T := 2 * (fullDetailMassCost ε + 1) / fullDetailPrimeGap
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp T)
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos T).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hlog : T ≤ Real.log (A : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos T) hA.le
    rwa [Real.log_exp] at h
  have hcap : fullDetailMassCost ε + 1 ≤
      (fullDetailPrimeGap / 2) * Real.log (A : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlog
      (div_nonneg fullDetailPrimeGap_pos.le (by norm_num : (0 : ℝ) ≤ 2))
    have he : (fullDetailPrimeGap / 2) * T = fullDetailMassCost ε + 1 := by
      dsimp only [T]
      field_simp [fullDetailPrimeGap_pos.ne']
    rwa [he] at h
  refine ⟨A, hA1, ?_⟩
  intro q d X hd
  have hm : (fullDetailMassCost ε + 1) * (∫ x, haarSectionProfile d X x ^ 2) ≤
      (fullDetailPrimeGap / 2) * haarLogarithmicMass d X := by
    rw [integral_haarSectionProfile_sq, haarLogarithmicMass, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    have ha1 := (Finset.mem_Icc.mp ha).1
    by_cases hAa : A ≤ a
    · have hlogAa : Real.log (A : ℝ) ≤ Real.log (a : ℝ) :=
        Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hAa)
      have hcoef := hcap.trans (mul_le_mul_of_nonneg_left
        (hlogAa.trans (log_le_cellGammaWeight ha1))
        (div_nonneg fullDetailPrimeGap_pos.le (by norm_num : (0 : ℝ) ≤ 2)))
      convert mul_le_mul_of_nonneg_right hcoef
        (mul_nonneg (haarMass_pos ha1).le (sq_nonneg (d a))) using 1
      ring
    · rw [hd a (by omega)]
      simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
  have h := fullDetailCoupledSourceForm_ge ε hε q d X
  nlinarith only [h, hm]

/-- The same source reserve also pays every mixed prime power of exponent at least three. -/
theorem exists_fullDetailHigherMixed_coarse_reserve (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a : ℕ, a < A → d a = 0) →
      (1 - ε) * levyEnergy (averageSectionProfile q X) +
          (fullDetailPrimeGap / 4) * haarLogarithmicMass d X +
          (∫ x, haarSectionProfile d X x ^ 2) ≤
        fullDetailCoupledSourceForm q d X - higherPrimePowerMixedSource d q X := by
  obtain ⟨A₀, hA₀, hbase⟩ := exists_fullDetailCoupled_coarse_reserve (ε / 2) (by positivity)
  let δ := min (ε / 4) (fullDetailPrimeGap / (32 * haarGammaUpperConstant))
  have hδ : 0 < δ := lt_min (by positivity)
    (div_pos fullDetailPrimeGap_pos (mul_pos (by norm_num) haarGammaUpperConstant_pos))
  obtain ⟨A₁, hA₁, htail⟩ := exists_higherPrimePower_gamma_small_tail hδ
  refine ⟨max A₀ A₁, hA₀.trans (le_max_left _ _), ?_⟩
  intro q d X hd
  have hd₀ (a : ℕ) (ha : a < A₀) : d a = 0 := hd a (ha.trans_le (le_max_left _ _))
  have hd₁ (a : ℕ) (ha : a < A₁) : d a = 0 := hd a (ha.trans_le (le_max_right _ _))
  have he : (fun a => if A₁ ≤ a then d a else 0) = d := by
    funext a
    by_cases ha : A₁ ≤ a
    · exact if_pos ha
    · rw [if_neg ha, hd₁ a (by omega)]
  have hmixed := htail d q X
  rw [he] at hmixed
  have hupper := (completePairProfile_gamma_equivalent_coarse_weighted_detail q d X).2
  change levyEnergy (completePairProfile q d X) ≤
    2 * levyEnergy (averageSectionProfile q X) +
      (8 * haarGammaUpperConstant) * haarLogarithmicMass d X at hupper
  have hG := levyEnergy_nonneg_bv (averageSectionProfile_bv q X) (averageSectionProfile_compact q X)
  have hD := haarLogarithmicMass_nonneg d X
  have hδ₁ : δ ≤ ε / 4 := min_le_left _ _
  have hδ₂ : δ * (32 * haarGammaUpperConstant) ≤ fullDetailPrimeGap :=
    (le_div_iff₀ (mul_pos (by norm_num) haarGammaUpperConstant_pos)).mp (min_le_right _ _)
  have hpayG := mul_le_mul_of_nonneg_right
    (show 2 * δ ≤ ε / 2 by linarith only [hδ₁]) hG
  have hpayD := mul_le_mul_of_nonneg_right
    (show δ * (8 * haarGammaUpperConstant) ≤ fullDetailPrimeGap / 4 by
      nlinarith only [hδ₂]) hD
  have hp : |higherPrimePowerMixedSource d q X| ≤
      (ε / 2) * levyEnergy (averageSectionProfile q X) +
        (fullDetailPrimeGap / 4) * haarLogarithmicMass d X := by
    apply (hmixed.trans (mul_le_mul_of_nonneg_left hupper hδ.le)).trans
    nlinarith only [hpayG, hpayD]
  have hb := hbase q d X hd₀
  have hs := le_abs_self (higherPrimePowerMixedSource d q X)
  nlinarith only [hb, hp, hs]

/-- An unconditional tail formulation, uniform over all signed coefficients and horizons. -/
theorem exists_fullDetailHigherMixed_uniform_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      let t := haarTailCoeffs A d
      (1 - ε) * levyEnergy (averageSectionProfile q X) +
          (fullDetailPrimeGap / 4) * haarLogarithmicMass t X +
          (∫ x, haarSectionProfile t X x ^ 2) ≤
        fullDetailCoupledSourceForm q t X - higherPrimePowerMixedSource t q X := by
  obtain ⟨A, hA, hpay⟩ := exists_fullDetailHigherMixed_coarse_reserve ε hε
  refine ⟨A, hA, ?_⟩
  intro q d X
  apply hpay q (haarTailCoeffs A d) X
  intro a ha
  exact if_neg (by omega : ¬A ≤ a)

/-- The paid source on an arbitrary finite family of actual complete profiles. -/
def fullDetailHigherMixedProfileForm {n : ℕ} (q d : Fin n → ℕ → ℝ) (X : ℕ)
    (x : Fin n → ℝ) : ℝ :=
  fullDetailCoupledSourceForm (fun a => ∑ i, x i * q i a) (fun a => ∑ i, x i * d i a) X -
    higherPrimePowerMixedSource (fun a => ∑ i, x i * d i a) (fun a => ∑ i, x i * q i a) X

private def fullDetailHeadReadout {n : ℕ} (d : Fin n → ℕ → ℝ) (A : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin A → ℝ) where
  toFun x a := ∑ i, x i * d i a
  map_add' x y := by
    funext a
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
    rfl

/-- One fixed head bounds negative dimension after paying the full detail diagonal and higher mixing. -/
theorem exists_uniform_fullDetailHigherMixed_negative_dimension :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (n : ℕ) (q d : Fin n → ℕ → ℝ) (X : ℕ)
      (W : Submodule ℝ (Fin n → ℝ)),
      (∀ x ∈ W, x ≠ 0 → fullDetailHigherMixedProfileForm q d X x < 0) →
        Module.finrank ℝ W ≤ A := by
  obtain ⟨A, hA, hpay⟩ :=
    exists_fullDetailHigherMixed_coarse_reserve (1 / 2) (by norm_num)
  refine ⟨A, hA, ?_⟩
  intro n q d X W hW
  let T := fullDetailHeadReadout d A
  have hnonneg (x : Fin n → ℝ) (hx : T x = 0) :
      0 ≤ fullDetailHigherMixedProfileForm q d X x := by
    have hz (a : ℕ) (ha : a < A) : (∑ i, x i * d i a) = 0 :=
      congrFun hx (⟨a, ha⟩ : Fin A)
    have hp := hpay (fun a => ∑ i, x i * q i a) (fun a => ∑ i, x i * d i a) X hz
    have hG := levyEnergy_nonneg_bv (averageSectionProfile_bv (fun a => ∑ i, x i * q i a) X)
      (averageSectionProfile_compact (fun a => ∑ i, x i * q i a) X)
    have hD := haarLogarithmicMass_nonneg (fun a => ∑ i, x i * d i a) X
    have hM : 0 ≤ ∫ y, haarSectionProfile (fun a => ∑ i, x i * d i a) X y ^ 2 :=
      integral_nonneg fun y => sq_nonneg _
    have hκ := fullDetailPrimeGap_pos
    have hl : 0 ≤ (1 - (1 / 2 : ℝ)) *
        levyEnergy (averageSectionProfile (fun a => ∑ i, x i * q i a) X) +
          (fullDetailPrimeGap / 4) * haarLogarithmicMass (fun a => ∑ i, x i * d i a) X +
          (∫ y, haarSectionProfile (fun a => ∑ i, x i * d i a) X y ^ 2) := by positivity
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
