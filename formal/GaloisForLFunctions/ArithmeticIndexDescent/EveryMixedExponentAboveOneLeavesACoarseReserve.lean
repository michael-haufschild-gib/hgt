import GaloisForLFunctions.ArithmeticIndexDescent.TheMixedSquareSourceHasUniformSmallTails
import GaloisForLFunctions.ArithmeticIndexDescent.TheFullDetailSourceRetainsCoarseGamma

/-!
# Joint payment of every mixed prime exponent above one

The full Haar Weil diagonal and Gamma coupling already leave a coarse Gamma
reserve. The disjoint even-power and odd higher-power mixed sources each
cost an arbitrarily small part of the original Gamma energy after one detail
head. Paying both from the same reserve retains coarse Gamma, logarithmic
detail mass, and ordinary detail mass simultaneously.
-/

noncomputable section
open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells HTGeometry

/-- Full detail self-interaction, Gamma coupling, and every mixed prime exponent at least two. -/
def fullDetailNonfirstMixedSourceForm (q d : ℕ → ℝ) (X : ℕ) : ℝ :=
  fullDetailCoupledSourceForm q d X - squarePrimeMixedSource q d X -
    oddHigherPrimePowerMixedSource d q X

/-- One detail head pays the two disjoint mixed sources while retaining almost all coarse Gamma. -/
theorem exists_fullDetailNonfirstMixed_coarse_reserve (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a : ℕ, a < A → d a = 0) →
      (1 - ε) * levyEnergy (averageSectionProfile q X) +
          (fullDetailPrimeGap / 4) * haarLogarithmicMass d X +
          (∫ x, haarSectionProfile d X x ^ 2) ≤
        fullDetailNonfirstMixedSourceForm q d X := by
  obtain ⟨A₀, hA₀, hbase⟩ := exists_fullDetailCoupled_coarse_reserve (ε / 2) (by positivity)
  let δ := min (ε / 8) (fullDetailPrimeGap / (64 * haarGammaUpperConstant))
  have hδ : 0 < δ := lt_min (by positivity)
    (div_pos fullDetailPrimeGap_pos (mul_pos (by norm_num) haarGammaUpperConstant_pos))
  obtain ⟨A₂, _, hsquare⟩ := exists_uniform_small_squarePrimeMixed_tail hδ
  obtain ⟨Ao, _, hodd⟩ := exists_oddHigherPrimePower_gamma_small_tail hδ
  refine ⟨max A₀ (max A₂ Ao), hA₀.trans (le_max_left _ _), ?_⟩
  intro q d X hd
  have hd₀ (a : ℕ) (ha : a < A₀) : d a = 0 := hd a (ha.trans_le (le_max_left _ _))
  have hA₂ : A₂ ≤ max A₀ (max A₂ Ao) := (le_max_left _ _).trans (le_max_right _ _)
  have hAo : Ao ≤ max A₀ (max A₂ Ao) := (le_max_right _ _).trans (le_max_right _ _)
  have he₂ : (fun a => if A₂ ≤ a then d a else 0) = d := by
    funext a
    by_cases ha : A₂ ≤ a
    · exact if_pos ha
    · rw [if_neg ha, hd a ((show a < A₂ by omega).trans_le hA₂)]
  have heo : (fun a => if Ao ≤ a then d a else 0) = d := by
    funext a
    by_cases ha : Ao ≤ a
    · exact if_pos ha
    · rw [if_neg ha, hd a ((show a < Ao by omega).trans_le hAo)]
  have hs := hsquare q d X
  have ho := hodd d q X
  rw [he₂] at hs
  rw [heo] at ho
  have hupper := (completePairProfile_gamma_equivalent_coarse_weighted_detail q d X).2
  change levyEnergy (completePairProfile q d X) ≤
    2 * levyEnergy (averageSectionProfile q X) +
      (8 * haarGammaUpperConstant) * haarLogarithmicMass d X at hupper
  have hG := levyEnergy_nonneg_bv (averageSectionProfile_bv q X) (averageSectionProfile_compact q X)
  have hD := haarLogarithmicMass_nonneg d X
  have hδ₁ : δ ≤ ε / 8 := min_le_left _ _
  have hδ₂ : δ * (64 * haarGammaUpperConstant) ≤ fullDetailPrimeGap :=
    (le_div_iff₀ (mul_pos (by norm_num) haarGammaUpperConstant_pos)).mp (min_le_right _ _)
  have hpayG := mul_le_mul_of_nonneg_right
    (show 4 * δ ≤ ε / 2 by linarith only [hδ₁]) hG
  have hpayD := mul_le_mul_of_nonneg_right
    (show δ * (16 * haarGammaUpperConstant) ≤ fullDetailPrimeGap / 4 by
      nlinarith only [hδ₂]) hD
  have henergy := mul_le_mul_of_nonneg_left hupper (show 0 ≤ 2 * δ by positivity)
  have hpaid : |squarePrimeMixedSource q d X| + |oddHigherPrimePowerMixedSource d q X| ≤
      (ε / 2) * levyEnergy (averageSectionProfile q X) +
        (fullDetailPrimeGap / 4) * haarLogarithmicMass d X := by
    nlinarith only [hs, ho, henergy, hpayG, hpayD]
  have hb := hbase q d X hd₀
  have hss := le_abs_self (squarePrimeMixedSource q d X)
  have hoo := le_abs_self (oddHigherPrimePowerMixedSource d q X)
  unfold fullDetailNonfirstMixedSourceForm
  nlinarith only [hb, hpaid, hss, hoo]

/-- The joint reserve holds on the actual high-detail profile for every signed source and horizon. -/
theorem exists_fullDetailNonfirstMixed_uniform_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      let t := haarTailCoeffs A d
      (1 - ε) * levyEnergy (averageSectionProfile q X) +
          (fullDetailPrimeGap / 4) * haarLogarithmicMass t X +
          (∫ x, haarSectionProfile t X x ^ 2) ≤
        fullDetailNonfirstMixedSourceForm q t X := by
  obtain ⟨A, hA, hpay⟩ := exists_fullDetailNonfirstMixed_coarse_reserve ε hε
  refine ⟨A, hA, ?_⟩
  intro q d X
  apply hpay q (haarTailCoeffs A d) X
  intro a ha
  exact if_neg (by omega : ¬A ≤ a)

/-- The jointly paid source on any finite family of original complete profiles. -/
def fullDetailNonfirstMixedProfileForm {n : ℕ} (q d : Fin n → ℕ → ℝ) (X : ℕ)
    (x : Fin n → ℝ) : ℝ :=
  fullDetailNonfirstMixedSourceForm (fun a => ∑ i, x i * q i a)
    (fun a => ∑ i, x i * d i a) X

private def nonfirstDetailHeadReadout {n : ℕ} (d : Fin n → ℕ → ℝ) (A : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin A → ℝ) where
  toFun x a := ∑ i, x i * d i a
  map_add' x y := by
    funext a
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
    rfl

/-- The full detail and non-first mixed payment has uniformly bounded negative dimension. -/
theorem exists_uniform_fullDetailNonfirstMixed_negative_dimension :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (n : ℕ) (q d : Fin n → ℕ → ℝ) (X : ℕ)
      (W : Submodule ℝ (Fin n → ℝ)),
      (∀ x ∈ W, x ≠ 0 → fullDetailNonfirstMixedProfileForm q d X x < 0) →
        Module.finrank ℝ W ≤ A := by
  obtain ⟨A, hA, hpay⟩ :=
    exists_fullDetailNonfirstMixed_coarse_reserve (1 / 2) (by norm_num)
  refine ⟨A, hA, ?_⟩
  intro n q d X W hW
  let T := nonfirstDetailHeadReadout d A
  have hnonneg (x : Fin n → ℝ) (hx : T x = 0) :
      0 ≤ fullDetailNonfirstMixedProfileForm q d X x := by
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
