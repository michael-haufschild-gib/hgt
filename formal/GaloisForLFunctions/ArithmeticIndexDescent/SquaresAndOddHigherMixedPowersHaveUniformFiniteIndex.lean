import GaloisForLFunctions.ArithmeticIndexDescent.TheSquarePrimeEstimateHoldsOnCompleteProfiles
import GaloisForLFunctions.ArithmeticIndexDescent.OddHigherPrimePowerMixedTailsAreGammaSmall
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw

/-!
# One finite detail head and one mean bound the square-plus-odd index

The square-prime estimate retains a uniform Gamma share. That share pays
all odd higher-power mixed detail tails. On the kernel of a fixed finite
detail head and the ordinary mean, a positive L² floor remains. Restricting
these readouts to any strictly negative subspace makes them injective.

The form here consists exactly of the Gamma jump energy, the full even
prime-power source, and the mixed odd powers of exponent at least three.
-/

noncomputable section
open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- The literal even source and the disjoint odd higher mixed source, paid by the original Gamma energy. -/
def squareOddHigherGammaSourceForm (q d : ℕ → ℝ) (X : ℕ) : ℝ :=
  levyEnergy (completePairProfile q d X) - squarePrimeSource (completePairProfile q d X) -
    oddHigherPrimePowerMixedSource d q X

/-- A fixed detail head leaves only the single ordinary-mean defect and a positive mass floor. -/
theorem exists_squareOddHigher_finite_head_coercivity :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a : ℕ, a < A → d a = 0) →
      (Real.eulerMascheroniConstant / 2) * (∫ x : ℝ, completePairProfile q d X x ^ 2) ≤
        squareOddHigherGammaSourceForm q d X +
          (1 / 2 : ℝ) * (∫ x : ℝ, completePairProfile q d X x) ^ 2 := by
  obtain ⟨δ, hδ, hsquare⟩ := exists_squarePrime_retained_gamma_complete
  obtain ⟨A, hA, hodd⟩ := exists_oddHigherPrimePower_gamma_small_tail hδ
  refine ⟨A, hA, ?_⟩
  intro q d X hd
  have htail : (fun a => if A ≤ a then d a else 0) = d := by
    funext a
    by_cases ha : A ≤ a
    · exact if_pos ha
    · rw [if_neg ha, hd a (by omega)]
  have ho := hodd d q X
  rw [htail] at ho
  have hp := hsquare q d X
  have hsign := le_abs_self (oddHigherPrimePowerMixedSource d q X)
  unfold squareOddHigherGammaSourceForm
  linarith only [ho, hp, hsign]

/-- Complete profiles depend linearly on their original pair coefficients. -/
theorem completePairProfile_linearCombination {n : ℕ} (q d : Fin n → ℕ → ℝ)
    (X : ℕ) (x : Fin n → ℝ) (y : ℝ) :
    completePairProfile (fun a => ∑ i, x i * q i a) (fun a => ∑ i, x i * d i a) X y =
      ∑ i, x i * completePairProfile (q i) (d i) X y := by
  simp only [completePairProfile, averageSectionProfile, haarSectionProfile,
    Finset.sum_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_assoc]
  congr 1 <;> exact Finset.sum_comm

/-- The ordinary mean readout is the mean of the actual combined profile. -/
theorem integral_completePairProfile_linearCombination {n : ℕ} (q d : Fin n → ℕ → ℝ)
    (X : ℕ) (x : Fin n → ℝ) :
    (∫ y : ℝ, completePairProfile (fun a => ∑ i, x i * q i a)
      (fun a => ∑ i, x i * d i a) X y) =
        ∑ i, x i * ∫ y : ℝ, completePairProfile (q i) (d i) X y := by
  have hi (i : Fin n) : Integrable (completePairProfile (q i) (d i) X) := by
    simpa only [mul_one] using integrable_compact_bv_mul (completePairProfile_bv (q i) (d i) X)
      (completePairProfile_compact (q i) (d i) X)
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  simp_rw [completePairProfile_linearCombination]
  rw [integral_finsetSum _ (fun i _ => (hi i).const_mul (x i))]
  simp only [integral_const_mul]

/-- The specified source form on an arbitrary finite family of complete profiles. -/
def squareOddHigherGammaProfileForm {n : ℕ} (q d : Fin n → ℕ → ℝ) (X : ℕ)
    (x : Fin n → ℝ) : ℝ :=
  squareOddHigherGammaSourceForm (fun a => ∑ i, x i * q i a) (fun a => ∑ i, x i * d i a) X

private def squareOddDetailMeanReadout {n : ℕ} (q d : Fin n → ℕ → ℝ) (A X : ℕ) :
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

/-- The full even source together with odd higher mixed powers has negative dimension at most A+1, uniformly in horizon and family. -/
theorem exists_uniform_squareOddHigherGamma_negative_dimension :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (n : ℕ) (q d : Fin n → ℕ → ℝ) (X : ℕ)
      (W : Submodule ℝ (Fin n → ℝ)),
      (∀ x ∈ W, x ≠ 0 → squareOddHigherGammaProfileForm q d X x < 0) →
        Module.finrank ℝ W ≤ A + 1 := by
  obtain ⟨A, hA, hpay⟩ := exists_squareOddHigher_finite_head_coercivity
  refine ⟨A, hA, ?_⟩
  intro n q d X W hW
  let T := squareOddDetailMeanReadout q d A X
  have hnonneg (x : Fin n → ℝ) (hx : T x = 0) :
      0 ≤ squareOddHigherGammaProfileForm q d X x := by
    have hz (a : ℕ) (ha : a < A) : (∑ i, x i * d i a) = 0 := by
      have h := congrFun (congrArg Prod.fst hx) (⟨a, ha⟩ : Fin A)
      exact h
    have hm : (∫ y : ℝ, completePairProfile (fun a => ∑ i, x i * q i a)
        (fun a => ∑ i, x i * d i a) X y) = 0 := by
      rw [integral_completePairProfile_linearCombination]
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

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_squareOddHigher_finite_head_coercivity
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.integral_completePairProfile_linearCombination
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_uniform_squareOddHigherGamma_negative_dimension
