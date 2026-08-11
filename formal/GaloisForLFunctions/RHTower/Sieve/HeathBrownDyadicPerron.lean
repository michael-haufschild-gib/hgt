import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicBoxes

/-!
# Signed dyadic Heath--Brown boxes and weighted prefixes

The core dyadic boxes are lifted to the complete signed binomial terms.  A weighted prefix is
packaged as an additive functional, so the exact finite Heath--Brown identity becomes a finite sum
over boxes without manual sum rearrangements.  Boxes whose lower product edge exceeds the prefix
vanish identically; every surviving box has only constant-factor support inflation.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex

/-- Any arithmetic function vanishes below `1`, because its zero coefficient is zero. -/
theorem arithmeticFunction_vanishesBelow_one (F : ArithmeticFunction ℝ) :
    VanishesBelow F 1 := by
  intro n hn
  have hn0 : n = 0 := by omega
  subst n
  simp

/-- Complete signed version of one dyadic core box. -/
def heathBrownDyadicTermBox
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ) (q : ℕ) :
    ArithmeticFunction ℝ :=
  (-1 : ArithmeticFunction ℝ) ^ (m + k + 1) *
    (k.choose m : ArithmeticFunction ℝ) *
    heathBrownDyadicCoreBox L X (k - m) a b q

/-- Exact coefficient-level box expansion of a complete signed term. -/
theorem heathBrownFiniteTerm_eq_sum_dyadicBoxes (L X k m : ℕ) :
    heathBrownFiniteTerm L X k m =
      ∑ q ∈ Finset.range (Nat.log 2 X + 1),
        ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
          ∑ a ∈ dyadicChoiceSet (k - m) L,
            heathBrownDyadicTermBox L X k m a b q := by
  let S : ArithmeticFunction ℝ :=
    (-1 : ArithmeticFunction ℝ) ^ (m + k + 1) *
      (k.choose m : ArithmeticFunction ℝ)
  calc
    heathBrownFiniteTerm L X k m =
        S * heathBrownFiniteCore L X (k - m) := by
      rfl
    _ = S * (∑ q ∈ Finset.range (Nat.log 2 X + 1),
        ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
          ∑ a ∈ dyadicChoiceSet (k - m) L,
            heathBrownDyadicCoreBox L X (k - m) a b q) :=
      congrArg (fun F : ArithmeticFunction ℝ => S * F)
        (heathBrownFiniteCore_eq_sum_dyadicBoxes L X (k - m))
    _ = ∑ q ∈ Finset.range (Nat.log 2 X + 1),
        ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
          ∑ a ∈ dyadicChoiceSet (k - m) L,
            heathBrownDyadicTermBox L X k m a b q := by
      simp only [Finset.mul_sum, S, heathBrownDyadicTermBox]

theorem vanishesBelow_heathBrownDyadicTermBox
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ) (q : ℕ) :
    VanishesBelow (heathBrownDyadicTermBox L X k m a b q)
      (heathBrownDyadicCoreLower (k - m) a b q) := by
  have hsign := (arithmeticFunction_vanishesBelow_one
    (-1 : ArithmeticFunction ℝ)).pow (m + k + 1)
  have hchoose := arithmeticFunction_vanishesBelow_one
    (k.choose m : ArithmeticFunction ℝ)
  have hcore := vanishesBelow_heathBrownDyadicCoreBox_lower
    L X (k - m) a b q
  simpa [heathBrownDyadicTermBox] using
    vanishesBelow_mul (vanishesBelow_mul hsign hchoose) hcore

theorem upperSupported_heathBrownDyadicTermBox
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ) (q : ℕ) :
    UpperSupported (heathBrownDyadicTermBox L X k m a b q)
      (heathBrownDyadicCoreUpper (k - m) a b q) := by
  have hsign := upperSupported_negOne.pow (m + k + 1)
  have hchoose := upperSupported_natCast (k.choose m)
  have hcore := upperSupported_heathBrownDyadicCoreBox_upper
    L X (k - m) a b q
  simpa [heathBrownDyadicTermBox] using (hsign.mul hchoose).mul hcore

/-- Every dyadic block has a finite L-series at every complex argument. -/
theorem LSeriesSummable_complexCoeff_arithmeticDyadicBlock
    (F : ArithmeticFunction ℝ) (q : ℕ) (s : ℂ) :
    LSeriesSummable (complexCoeff (arithmeticDyadicBlock F q)) s := by
  apply LSeriesSummable_of_support (s := Finset.Icc 1 (2 ^ (q + 1)))
  intro n hn
  apply upperSupported_arithmeticDyadicBlock F q n
  intro hzero
  apply hn
  rw [complexCoeff_apply, hzero, Complex.ofReal_zero]

/-- Finite products of summable arithmetic functions remain summable. -/
theorem LSeriesSummable_complexCoeff_finsetProd
    {ι : Type*} (u : Finset ι) (F : ι → ArithmeticFunction ℝ) (s : ℂ)
    (hF : ∀ i ∈ u, LSeriesSummable (complexCoeff (F i)) s) :
    LSeriesSummable (complexCoeff (∏ i ∈ u, F i)) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using LSeriesSummable_complexCoeff_one s
  | @insert a u ha ih =>
      rw [Finset.prod_insert ha]
      exact LSeriesSummable_complexCoeff_mul
        (hF a (Finset.mem_insert_self a u))
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

/-- L-series of a finite convolution product is the product of the individual L-series. -/
theorem LSeries_complexCoeff_finsetProd
    {ι : Type*} (u : Finset ι) (F : ι → ArithmeticFunction ℝ) (s : ℂ)
    (hF : ∀ i ∈ u, LSeriesSummable (complexCoeff (F i)) s) :
    LSeries (complexCoeff (∏ i ∈ u, F i)) s =
      ∏ i ∈ u, LSeries (complexCoeff (F i)) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using LSeries_complexCoeff_one s
  | @insert a u ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        LSeries_complexCoeff_mul (hF a (Finset.mem_insert_self a u))
          (LSeriesSummable_complexCoeff_finsetProd u F s
            (fun i hi => hF i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))]

theorem LSeriesSummable_complexCoeff_dyadicBlockProduct
    (F : ArithmeticFunction ℝ) (r : ℕ) (a : Fin r → ℕ) (s : ℂ) :
    LSeriesSummable (complexCoeff (dyadicBlockProduct F r a)) s := by
  rw [dyadicBlockProduct]
  apply LSeriesSummable_complexCoeff_finsetProd
  intro i hi
  exact LSeriesSummable_complexCoeff_arithmeticDyadicBlock F (a i) s

theorem LSeries_complexCoeff_dyadicBlockProduct
    (F : ArithmeticFunction ℝ) (r : ℕ) (a : Fin r → ℕ) (s : ℂ) :
    LSeries (complexCoeff (dyadicBlockProduct F r a)) s =
      ∏ i, LSeries (complexCoeff (arithmeticDyadicBlock F (a i))) s := by
  rw [dyadicBlockProduct]
  apply LSeries_complexCoeff_finsetProd
  intro i hi
  exact LSeriesSummable_complexCoeff_arithmeticDyadicBlock F (a i) s

theorem LSeriesSummable_complexCoeff_heathBrownDyadicCoreBox
    (L X j : ℕ) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ) (s : ℂ) :
    LSeriesSummable (complexCoeff (heathBrownDyadicCoreBox L X j a b q)) s := by
  rw [heathBrownDyadicCoreBox]
  exact LSeriesSummable_complexCoeff_mul
    (LSeriesSummable_complexCoeff_mul
      (LSeriesSummable_complexCoeff_dyadicBlockProduct
        (truncatedMoebius L) j a s)
      (LSeriesSummable_complexCoeff_dyadicBlockProduct
        (coeffTrunc (zeta : ArithmeticFunction ℝ) X) (j - 1) b s))
    (LSeriesSummable_complexCoeff_arithmeticDyadicBlock
      (coeffTrunc ArithmeticFunction.log X) q s)

/-- Exact product factorization of one dyadic core box. -/
theorem LSeries_heathBrownDyadicCoreBox
    (L X j : ℕ) (a : Fin j → ℕ) (b : Fin (j - 1) → ℕ) (q : ℕ) (s : ℂ) :
    LSeries (complexCoeff (heathBrownDyadicCoreBox L X j a b q)) s =
      (∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock (truncatedMoebius L) (a i))) s) *
      (∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (coeffTrunc (zeta : ArithmeticFunction ℝ) X) (b i))) s) *
      LSeries (complexCoeff (arithmeticDyadicBlock
        (coeffTrunc ArithmeticFunction.log X) q)) s := by
  have hA := LSeriesSummable_complexCoeff_dyadicBlockProduct
    (truncatedMoebius L) j a s
  have hB := LSeriesSummable_complexCoeff_dyadicBlockProduct
    (coeffTrunc (zeta : ArithmeticFunction ℝ) X) (j - 1) b s
  have hq := LSeriesSummable_complexCoeff_arithmeticDyadicBlock
    (coeffTrunc ArithmeticFunction.log X) q s
  rw [heathBrownDyadicCoreBox,
    LSeries_complexCoeff_mul (LSeriesSummable_complexCoeff_mul hA hB) hq,
    LSeries_complexCoeff_mul hA hB,
    LSeries_complexCoeff_dyadicBlockProduct,
    LSeries_complexCoeff_dyadicBlockProduct]

/-- Weighted coefficient prefix as an additive functional. -/
def weightedArithmeticPrefix (X : ℕ) (w : ℂ) : ArithmeticFunction ℝ →+ ℂ where
  toFun F := ∑ n ∈ Finset.Icc 1 X, complexCoeff F n * (n : ℂ) ^ (-w)
  map_zero' := by simp [complexCoeff]
  map_add' F G := by
    simp only [complexCoeff_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[simp] theorem weightedArithmeticPrefix_apply
    (X : ℕ) (w : ℂ) (F : ArithmeticFunction ℝ) :
    weightedArithmeticPrefix X w F =
      ∑ n ∈ Finset.Icc 1 X, complexCoeff F n * (n : ℂ) ^ (-w) := rfl

/-- A dyadic box whose lower product edge exceeds the prefix contributes exactly zero. -/
theorem weightedArithmeticPrefix_heathBrownDyadicTermBox_eq_zero
    (L X k m : ℕ) (a : Fin (k - m) → ℕ) (b : Fin (k - m - 1) → ℕ) (q : ℕ)
    (w : ℂ) (hX : X < heathBrownDyadicCoreLower (k - m) a b q) :
    weightedArithmeticPrefix X w (heathBrownDyadicTermBox L X k m a b q) = 0 := by
  rw [weightedArithmeticPrefix_apply]
  apply Finset.sum_eq_zero
  intro n hn
  have hnX := (Finset.mem_Icc.mp hn).2
  have hnlow : n < heathBrownDyadicCoreLower (k - m) a b q := hnX.trans_lt hX
  rw [vanishesBelow_heathBrownDyadicTermBox L X k m a b q n hnlow,
    complexCoeff_apply, Complex.ofReal_zero, zero_mul]

/-- **Exact weighted von Mangoldt prefix as a finite sum of dyadic `2j`-factor boxes.** -/
theorem sum_Icc_vonMangoldt_eq_sum_heathBrownDyadicTermBoxes
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) (w : ℂ) :
    (∑ n ∈ Finset.Icc 1 X, (vonMangoldt n : ℂ) * (n : ℂ) ^ (-w)) =
      ∑ m ∈ Finset.range k,
        ∑ q ∈ Finset.range (Nat.log 2 X + 1),
          ∑ b ∈ dyadicChoiceSet (k - m - 1) X,
            ∑ a ∈ dyadicChoiceSet (k - m) L,
              weightedArithmeticPrefix X w
                (heathBrownDyadicTermBox L X k m a b q) := by
  rw [sum_Icc_vonMangoldt_eq_sum_heathBrownFiniteTerm L X k hXL w]
  refine Finset.sum_congr rfl fun m hm => ?_
  change weightedArithmeticPrefix X w (heathBrownFiniteTerm L X k m) = _
  rw [heathBrownFiniteTerm_eq_sum_dyadicBoxes]
  simp only [map_sum]

end RHTower.Sieve
