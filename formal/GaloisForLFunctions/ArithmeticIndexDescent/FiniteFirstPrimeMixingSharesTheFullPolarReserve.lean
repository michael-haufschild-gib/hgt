import GaloisForLFunctions.ArithmeticIndexDescent.TheFullNonfirstSourceRetainsAlmostAllGamma
import GaloisForLFunctions.ArithmeticIndexDescent.EveryIntegerPrimeLagHasGammaSmallMixedTails

/-!
# Joint payment of finitely many first-prime mixed sources

A fixed finite first-prime sum is small on high details in the original
complete-profile Gamma norm. It shares the proved nonfirst payment while
retaining both original polar moments and every coarse coefficient.
-/

noncomputable section
open MeasureTheory Finset
open RHTower
namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- Only first powers occur in this finite mixed source. -/
def finiteFirstPrimeMixedSource (P : Finset Nat.Primes) (d q : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ p ∈ P, integerMixedSource (p : ℕ) d q X X

/-- Sum of the individual first-prime mixed-tail constants. -/
def finiteFirstPrimeMixedCost (P : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ P, 2 * (2 * ArithmeticFunction.vonMangoldt (p : ℕ) / Real.sqrt (p : ℝ))

theorem finiteFirstPrimeMixed_tail_bound (P : Finset Nat.Primes) (d q : ℕ → ℝ)
    {A : ℕ} (hA : 1 ≤ A) (X : ℕ) :
    |finiteFirstPrimeMixedSource P (fun a => if A ≤ a then d a else 0) q X| ≤
      finiteFirstPrimeMixedCost P *
        (levyEnergy (completePairProfile q d X) / cellGammaWeight A) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p ∈ P, (2 * (2 * ArithmeticFunction.vonMangoldt (p : ℕ) /
        Real.sqrt (p : ℝ))) *
        (levyEnergy (completePairProfile q d X) / cellGammaWeight A) :=
      sum_le_sum fun p _ => abs_integerMixed_tail_le_gamma_div_weight d q hA p.property.two_le X
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- A finite first-prime family has one common detail head at every cell horizon. -/
theorem exists_finiteFirstPrimeMixed_gamma_small_tail (P : Finset Nat.Primes)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (X : ℕ),
      |finiteFirstPrimeMixedSource P (fun a => if A ≤ a then d a else 0) q X| ≤
        δ * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp (finiteFirstPrimeMixedCost P / δ))
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hl := Real.log_lt_log (Real.exp_pos _) hA
  rw [Real.log_exp] at hl
  have hcoef : finiteFirstPrimeMixedCost P / cellGammaWeight A ≤ δ := by
    apply (div_le_iff₀ (cellGammaWeight_pos hA1)).mpr
    have h := (div_le_iff₀ hδ).mp (hl.le.trans (log_le_cellGammaWeight hA1))
    simpa only [mul_comm] using h
  refine ⟨A, hA1, fun d q X => ?_⟩
  have hE := levyEnergy_nonneg_bv (completePairProfile_bv q d X)
    (completePairProfile_compact q d X)
  calc
    _ ≤ _ := finiteFirstPrimeMixed_tail_bound P d q hA1 X
    _ = (finiteFirstPrimeMixedCost P / cellGammaWeight A) *
        levyEnergy (completePairProfile q d X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE

/-- The exact full-polar nonfirst source augmented by the finite first-prime mixed sum. -/
def finiteFirstPrimeFullPolarSource (P : Finset Nat.Primes) (q d : ℕ → ℝ) (X : ℕ) : ℝ :=
  fullPolarNonfirstSourceForm q d X - finiteFirstPrimeMixedSource P d q X

/-- The joint source keeps almost all original Gamma energy and its exact full pole. -/
theorem exists_finiteFirstPrime_fullPolar_gamma_approximation
    (P : Finset Nat.Primes) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a, a < A → d a = 0) →
      |finiteFirstPrimeFullPolarSource P q d X -
        (levyEnergy (completePairProfile q d X) +
          (2 * coshHalfMoment (completePairProfile q d X) ^ 2 -
            2 * sinhHalfMoment (completePairProfile q d X) ^ 2))| ≤
        ε * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A₀, hA₀, h₀⟩ := exists_fullPolarNonfirst_gamma_approximation (ε / 2)
    (by positivity)
  obtain ⟨A₁, _, h₁⟩ := exists_finiteFirstPrimeMixed_gamma_small_tail P
    (by positivity : 0 < ε / 2)
  refine ⟨max A₀ A₁, hA₀.trans (le_max_left _ _), fun q d X hd => ?_⟩
  have he₀ := h₀ q d X (fun a ha => hd a (ha.trans_le (le_max_left _ _)))
  have he₁ := h₁ d q X
  have htail : (fun a => if A₁ ≤ a then d a else 0) = d := by
    funext a
    split_ifs with ha
    · rfl
    · exact (hd a ((lt_of_not_ge ha).trans_le (le_max_right _ _))).symm
  rw [htail] at he₁
  have he : finiteFirstPrimeFullPolarSource P q d X -
      (levyEnergy (completePairProfile q d X) +
        (2 * coshHalfMoment (completePairProfile q d X) ^ 2 -
          2 * sinhHalfMoment (completePairProfile q d X) ^ 2)) =
      (fullPolarNonfirstSourceForm q d X -
        (levyEnergy (completePairProfile q d X) +
          (2 * coshHalfMoment (completePairProfile q d X) ^ 2 -
            2 * sinhHalfMoment (completePairProfile q d X) ^ 2))) -
        finiteFirstPrimeMixedSource P d q X := by
    unfold finiteFirstPrimeFullPolarSource
    ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add he₀ he₁).trans_eq (by ring))

/-- A single finite detail head pays first-prime mixing and the entire nonfirst source jointly. -/
theorem exists_finiteFirstPrime_fullPolar_completeGamma_reserve
    (P : Finset Nat.Primes) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a, a < A → d a = 0) →
      (1 - ε) * levyEnergy (completePairProfile q d X) +
          2 * coshHalfMoment (completePairProfile q d X) ^ 2 ≤
        finiteFirstPrimeFullPolarSource P q d X +
          2 * sinhHalfMoment (completePairProfile q d X) ^ 2 := by
  obtain ⟨A, hA, h⟩ := exists_finiteFirstPrime_fullPolar_gamma_approximation P hε
  refine ⟨A, hA, fun q d X hd => ?_⟩
  have he := (abs_le.mp (h q d X hd)).1
  linarith only [he]

/-- The joint source on each original finite complete-profile family. -/
def finiteFirstPrimeFullPolarProfileForm {n : ℕ} (P : Finset Nat.Primes)
    (q d : Fin n → ℕ → ℝ) (X : ℕ) (x : Fin n → ℝ) : ℝ :=
  finiteFirstPrimeFullPolarSource P (fun a => ∑ i, x i * q i a)
    (fun a => ∑ i, x i * d i a) X

private def firstPrimePolarReadout {n : ℕ} (q d : Fin n → ℕ → ℝ) (X A : ℕ) :
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

/-- The joint finite first-prime, nonfirst and full polar source has uniform finite index. -/
theorem exists_uniform_finiteFirstPrime_fullPolar_negative_dimension (P : Finset Nat.Primes) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (n : ℕ) (q d : Fin n → ℕ → ℝ) (X : ℕ)
      (W : Submodule ℝ (Fin n → ℝ)),
      (∀ x ∈ W, x ≠ 0 → finiteFirstPrimeFullPolarProfileForm P q d X x < 0) →
        Module.finrank ℝ W ≤ A + 1 := by
  obtain ⟨A, hA, hpay⟩ := exists_finiteFirstPrime_fullPolar_completeGamma_reserve P
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨A, hA, ?_⟩
  intro n q d X W hW
  let T := firstPrimePolarReadout q d X A
  have hnonneg (x : Fin n → ℝ) (hx : T x = 0) :
      0 ≤ finiteFirstPrimeFullPolarProfileForm P q d X x := by
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
    have hG := levyEnergy_nonneg_bv
      (completePairProfile_bv (fun a => ∑ i, x i * q i a) (fun a => ∑ i, x i * d i a) X)
      (completePairProfile_compact (fun a => ∑ i, x i * q i a)
        (fun a => ∑ i, x i * d i a) X)
    apply le_trans _ hp
    positivity
  have hker : LinearMap.ker (T.domRestrict W) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hx
    by_contra hx0
    have hv : (x : Fin n → ℝ) ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
    exact (not_lt_of_ge (hnonneg x hx)) (hW x x.property hv)
  have hd := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hd

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_finiteFirstPrimeMixed_gamma_small_tail
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_finiteFirstPrime_fullPolar_completeGamma_reserve
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_uniform_finiteFirstPrime_fullPolar_negative_dimension
