import GaloisForLFunctions.ArithmeticIndexDescent.TheSquarePrimeEstimateHoldsOnCompleteProfiles
import GaloisForLFunctions.ArithmeticIndexDescent.OddHigherPrimePowerMixedTailsAreGammaSmall
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw

/-!
# Joint payment of the mixed and diagonal odd higher-power details

An integer translate of a pair average is orthogonal to every target
detail. The complete prime source minus its coarse source is therefore
one translated-detail pairing. Summing its Gamma bound over odd prime
powers of exponent at least three pays both detail blocks together.

The full even-power source retains enough Gamma energy for this payment.
One fixed detail head and the ordinary mean then bound the negative
dimension, uniformly in the complete-cell horizon. The coarse odd source
and the first-prime source remain explicit unpaid contributions.
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-- Literal critical coefficients, restricted to odd exponents at least three. -/
def oddHigherPrimePowerWeight (pk : Nat.Primes × ℕ) : ℝ :=
  if Odd (pk.2 + 3) then
    2 * ArithmeticFunction.vonMangoldt (higherPrimePowerIndex pk) /
      Real.sqrt (higherPrimePowerIndex pk) else 0

theorem oddHigherPrimePowerWeight_nonneg (pk : Nat.Primes × ℕ) :
    0 ≤ oddHigherPrimePowerWeight pk := by
  unfold oddHigherPrimePowerWeight
  split_ifs
  · exact div_nonneg (mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg)
      (Real.sqrt_nonneg _)
  · exact le_refl 0

theorem summable_oddHigherPrimePowerWeight : Summable oddHigherPrimePowerWeight := by
  apply Summable.of_nonneg_of_le oddHigherPrimePowerWeight_nonneg
    (fun pk => ?_) summable_higherPrimePowerGammaWeight
  rw [higherPrimePowerGammaWeight_eq]
  have hw : 0 ≤ 2 * ArithmeticFunction.vonMangoldt (higherPrimePowerIndex pk) /
      Real.sqrt (higherPrimePowerIndex pk) :=
    div_nonneg (mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg)
      (Real.sqrt_nonneg _)
  unfold oddHigherPrimePowerWeight
  split_ifs <;> linarith only [hw]

/-- The finite total critical weight of the odd higher-power source. -/
def oddHigherPrimePowerDetailCost : ℝ := ∑' pk, oddHigherPrimePowerWeight pk

/-- The original oriented odd higher-power pairing on the physical half-line space. -/
def oddHigherPrimePowerPairing (u v : L²₊) : ℝ :=
  ∑' pk, oddHigherPrimePowerWeight pk *
    (inner ℂ (halfLineRightShift (Real.log (higherPrimePowerIndex pk)) u) v).re

theorem summable_oddHigherPrimePowerPairing (u v : L²₊) :
    Summable (fun pk => oddHigherPrimePowerWeight pk *
      (inner ℂ (halfLineRightShift (Real.log (higherPrimePowerIndex pk)) u) v).re) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun pk => ?_) (summable_oddHigherPrimePowerWeight.mul_right (‖u‖ * ‖v‖))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (oddHigherPrimePowerWeight_nonneg pk)]
  apply mul_le_mul_of_nonneg_left _ (oddHigherPrimePowerWeight_nonneg pk)
  exact (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_halfLineRightShift_le _ u) (norm_nonneg v)))

/-- The literal odd higher-power quadratic source, with every diagonal and mixed entry. -/
def oddHigherPrimePowerSource (v : L²₊) : ℝ := oddHigherPrimePowerPairing v v

/-- The Hilbert-space source has exactly the original complete-profile correlations. -/
theorem oddHigherPrimePowerSource_eq_complete_integrals (q d : ℕ → ℝ) (X : ℕ) :
    oddHigherPrimePowerSource (coarseSection q X + haarSection d X) =
      ∑' pk, oddHigherPrimePowerWeight pk *
        ∫ u, completePairProfile q d X u *
          completePairProfile q d X (u + Real.log (higherPrimePowerIndex pk)) := by
  unfold oddHigherPrimePowerSource oddHigherPrimePowerPairing
  apply tsum_congr
  intro pk
  rw [inner_shift_completePairProfile]

/-- The subtracted coarse source is the actual pair-average autocorrelation. -/
theorem oddHigherPrimePowerSource_eq_coarse_integrals (q : ℕ → ℝ) (X : ℕ) :
    oddHigherPrimePowerSource (coarseSection q X) =
      ∑' pk, oddHigherPrimePowerWeight pk *
        ∫ u, averageSectionProfile q X u *
          averageSectionProfile q X (u + Real.log (higherPrimePowerIndex pk)) := by
  unfold oddHigherPrimePowerSource oddHigherPrimePowerPairing
  apply tsum_congr
  intro pk
  rw [inner_shift_coarse_profile]

/-- Triangular integer incidence combines the mixed and detail diagonal into one pairing. -/
theorem oddHigherPrimePowerSource_sub_coarse (q d : ℕ → ℝ) (X : ℕ) :
    oddHigherPrimePowerSource (coarseSection q X + haarSection d X) -
      oddHigherPrimePowerSource (coarseSection q X) =
        oddHigherPrimePowerPairing (haarSection d X) (coarseSection q X + haarSection d X) := by
  unfold oddHigherPrimePowerSource oddHigherPrimePowerPairing
  rw [← (summable_oddHigherPrimePowerPairing _ _).tsum_sub
    (summable_oddHigherPrimePowerPairing _ _)]
  apply tsum_congr
  intro pk
  have hz := inner_shift_coarseSection_haarSection q d X X (two_le_higherPrimePowerIndex pk)
  rw [map_add, inner_add_left, inner_add_right, inner_add_right]
  simp only [Complex.add_re, hz]
  ring

/-- This source difference includes the formerly separate pure-detail contribution. -/
theorem oddHigherPrimePowerSource_sub_coarse_eq_mixed_add_detail (q d : ℕ → ℝ) (X : ℕ) :
    oddHigherPrimePowerSource (coarseSection q X + haarSection d X) -
      oddHigherPrimePowerSource (coarseSection q X) =
        oddHigherPrimePowerMixedSource d q X + oddHigherPrimePowerSource (haarSection d X) := by
  rw [oddHigherPrimePowerSource_sub_coarse]
  unfold oddHigherPrimePowerSource oddHigherPrimePowerPairing oddHigherPrimePowerMixedSource
  rw [← (summable_oddHigherPrimePowerMixed d q X).tsum_add
    (summable_oddHigherPrimePowerPairing _ _)]
  apply tsum_congr
  intro pk
  have hz := inner_shift_coarseSection_haarSection q d X X (two_le_higherPrimePowerIndex pk)
  simp only [oddHigherPrimePowerMixedTerm, oddHigherPrimePowerWeight, integerMixedSource,
    inner_add_right, Complex.add_re, hz, add_zero]
  split_ifs <;> ring

/-- The full source pays the joint high-detail pairing at all horizons and all integer lags. -/
theorem abs_oddHigherPrimePower_detail_tail_le_gamma (q d : ℕ → ℝ) {A : ℕ}
    (hA : 1 ≤ A) (X : ℕ) :
    |oddHigherPrimePowerPairing (haarSection (fun a => if A ≤ a then d a else 0) X)
      (coarseSection q X + haarSection d X)| ≤
        oddHigherPrimePowerDetailCost *
          (levyEnergy (completePairProfile q d X) / cellGammaWeight A) := by
  have hp (pk : Nat.Primes × ℕ) :
      |oddHigherPrimePowerWeight pk *
        (inner ℂ (halfLineRightShift (Real.log (higherPrimePowerIndex pk))
          (haarSection (fun a => if A ≤ a then d a else 0) X))
            (coarseSection q X + haarSection d X)).re| ≤
        oddHigherPrimePowerWeight pk *
          (levyEnergy (completePairProfile q d X) / cellGammaWeight A) := by
    rw [abs_mul, abs_of_nonneg (oddHigherPrimePowerWeight_nonneg pk),
      inner_shift_haar_completePair_profiles]
    apply mul_le_mul_of_nonneg_left _ (oddHigherPrimePowerWeight_nonneg pk)
    simpa only [sub_neg_eq_add] using
      abs_translated_detail_le_gamma_div_weight q d hA (le_refl X)
        (-Real.log (higherPrimePowerIndex pk))
  have h := RHTower.abs_tsum_le_tsum_of_abs_le
    (summable_oddHigherPrimePowerWeight.mul_right
      (levyEnergy (completePairProfile q d X) / cellGammaWeight A)) hp
  rw [tsum_mul_right] at h
  exact h

/-- A fixed detail head makes both odd higher-power detail blocks jointly Gamma-small. -/
theorem exists_oddHigherPrimePower_joint_gamma_small_tail {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      |oddHigherPrimePowerPairing (haarSection (fun a => if A ≤ a then d a else 0) X)
        (coarseSection q X + haarSection d X)| ≤ δ * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp (oddHigherPrimePowerDetailCost / δ))
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hlog : oddHigherPrimePowerDetailCost / δ < Real.log (A : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) hA
    rwa [Real.log_exp] at h
  have hcoef : oddHigherPrimePowerDetailCost / cellGammaWeight A ≤ δ := by
    apply (div_le_iff₀ (cellGammaWeight_pos hA1)).mpr
    calc
      _ ≤ δ * Real.log (A : ℝ) := by
        simpa only [mul_comm] using (div_le_iff₀ hδ).mp hlog.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (log_le_cellGammaWeight hA1) hδ.le
  refine ⟨A, hA1, ?_⟩
  intro q d X
  calc
    _ ≤ _ := abs_oddHigherPrimePower_detail_tail_le_gamma q d hA1 X
    _ = (oddHigherPrimePowerDetailCost / cellGammaWeight A) *
        levyEnergy (completePairProfile q d X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef
      (levyEnergy_nonneg_bv (completePairProfile_bv q d X) (completePairProfile_compact q d X))

/-- Full even powers and all detail-dependent odd higher powers, with the coarse source retained. -/
def squareOddHigherRefinementSourceForm (q d : ℕ → ℝ) (X : ℕ) : ℝ :=
  levyEnergy (completePairProfile q d X) - squarePrimeSource (completePairProfile q d X) -
    (oddHigherPrimePowerSource (coarseSection q X + haarSection d X) -
      oddHigherPrimePowerSource (coarseSection q X))

/-- One Gamma reserve pays the full even source and the joint odd higher-power detail block. -/
theorem exists_squareOddHigherRefinement_finite_head_coercivity :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a : ℕ, a < A → d a = 0) →
      (Real.eulerMascheroniConstant / 2) * (∫ x : ℝ, completePairProfile q d X x ^ 2) ≤
        squareOddHigherRefinementSourceForm q d X +
          (1 / 2 : ℝ) * (∫ x : ℝ, completePairProfile q d X x) ^ 2 := by
  obtain ⟨δ, hδ, hsquare⟩ := exists_squarePrime_retained_gamma_complete
  obtain ⟨A, hA, hodd⟩ := exists_oddHigherPrimePower_joint_gamma_small_tail hδ
  refine ⟨A, hA, ?_⟩
  intro q d X hd
  have htail : (fun a => if A ≤ a then d a else 0) = d := by
    funext a
    by_cases ha : A ≤ a
    · exact if_pos ha
    · rw [if_neg ha, hd a (by omega)]
  have ho := hodd q d X
  rw [htail] at ho
  have hp := hsquare q d X
  have hsign := le_abs_self
    (oddHigherPrimePowerPairing (haarSection d X) (coarseSection q X + haarSection d X))
  unfold squareOddHigherRefinementSourceForm
  rw [oddHigherPrimePowerSource_sub_coarse]
  linarith only [ho, hp, hsign]

/-- The literal refinement form evaluated on a finite family of complete-cell profiles. -/
def squareOddHigherRefinementProfileForm {n : ℕ} (q d : Fin n → ℕ → ℝ) (X : ℕ)
    (x : Fin n → ℝ) : ℝ :=
  squareOddHigherRefinementSourceForm (fun a => ∑ i, x i * q i a)
    (fun a => ∑ i, x i * d i a) X

private theorem integral_completePairProfile_sum {n : ℕ} (q d : Fin n → ℕ → ℝ)
    (X : ℕ) (x : Fin n → ℝ) :
    (∫ y : ℝ, completePairProfile (fun a => ∑ i, x i * q i a)
      (fun a => ∑ i, x i * d i a) X y) =
        ∑ i, x i * ∫ y : ℝ, completePairProfile (q i) (d i) X y := by
  have hi (i : Fin n) : Integrable (completePairProfile (q i) (d i) X) := by
    simpa only [mul_one] using integrable_compact_bv_mul (completePairProfile_bv (q i) (d i) X)
      (completePairProfile_compact (q i) (d i) X)
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  have he (y : ℝ) :
      completePairProfile (fun a => ∑ i, x i * q i a) (fun a => ∑ i, x i * d i a) X y =
        ∑ i, x i * completePairProfile (q i) (d i) X y := by
    simp only [completePairProfile, averageSectionProfile, haarSectionProfile,
      Finset.sum_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_assoc]
    congr 1 <;> exact Finset.sum_comm
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => (hi i).const_mul (x i))]
  simp only [integral_const_mul]

private def oddHigherDetailMeanReadout {n : ℕ} (q d : Fin n → ℕ → ℝ) (A X : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] ((Fin A → ℝ) × ℝ) where
  toFun x := (fun a => ∑ i, x i * d i a,
    ∑ i, x i * ∫ y : ℝ, completePairProfile (q i) (d i) X y)
  map_add' x y := by
    apply Prod.ext
    · change (fun a : Fin A => ∑ i, (x i + y i) * d i a) =
        (fun a : Fin A => (∑ i, x i * d i a) + ∑ i, y i * d i a)
      funext a
      simp only [add_mul, Finset.sum_add_distrib]
    · change (∑ i, (x i + y i) * ∫ z : ℝ, completePairProfile (q i) (d i) X z) =
        (∑ i, x i * ∫ z : ℝ, completePairProfile (q i) (d i) X z) +
          ∑ i, y i * ∫ z : ℝ, completePairProfile (q i) (d i) X z
      simp only [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    apply Prod.ext
    · change (fun a : Fin A => ∑ i, (c * x i) * d i a) =
        (fun a : Fin A => c * ∑ i, x i * d i a)
      funext a
      simp only [mul_assoc, Finset.mul_sum]
    · change (∑ i, (c * x i) * ∫ z : ℝ, completePairProfile (q i) (d i) X z) =
        c * ∑ i, x i * ∫ z : ℝ, completePairProfile (q i) (d i) X z
      simp only [mul_assoc, Finset.mul_sum]

/-- The enlarged original source has uniformly bounded negative dimension on every complete horizon. -/
theorem exists_uniform_squareOddHigherRefinement_negative_dimension :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (n : ℕ) (q d : Fin n → ℕ → ℝ) (X : ℕ)
      (W : Submodule ℝ (Fin n → ℝ)),
      (∀ x ∈ W, x ≠ 0 → squareOddHigherRefinementProfileForm q d X x < 0) →
        Module.finrank ℝ W ≤ A + 1 := by
  obtain ⟨A, hA, hpay⟩ := exists_squareOddHigherRefinement_finite_head_coercivity
  refine ⟨A, hA, ?_⟩
  intro n q d X W hW
  let T := oddHigherDetailMeanReadout q d A X
  have hnonneg (x : Fin n → ℝ) (hx : T x = 0) :
      0 ≤ squareOddHigherRefinementProfileForm q d X x := by
    have hz (a : ℕ) (ha : a < A) : (∑ i, x i * d i a) = 0 := by
      exact congrFun (congrArg Prod.fst hx) (⟨a, ha⟩ : Fin A)
    have hm : (∫ y : ℝ, completePairProfile (fun a => ∑ i, x i * q i a)
        (fun a => ∑ i, x i * d i a) X y) = 0 := by
      rw [integral_completePairProfile_sum]
      exact congrArg Prod.snd hx
    have hp := hpay (fun a => ∑ i, x i * q i a) (fun a => ∑ i, x i * d i a) X hz
    rw [hm, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at hp
    have hγ : 0 ≤ Real.eulerMascheroniConstant / 2 := by
      have h := Real.one_half_lt_eulerMascheroniConstant
      linarith only [h]
    exact (mul_nonneg hγ (integral_nonneg fun y => sq_nonneg _)).trans hp
  have hker : LinearMap.ker (T.domRestrict W) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hx
    by_contra hx0
    have hv : (x : Fin n → ℝ) ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
    exact (not_lt_of_ge (hnonneg x hx)) (hW x x.property hv)
  have hinj : Function.Injective (T.domRestrict W) := LinearMap.ker_eq_bot.mp hker
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin, Module.finrank_self] using hd

end GaloisForLFunctions.ArithmeticIndexDescent
