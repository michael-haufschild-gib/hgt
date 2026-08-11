import GaloisForLFunctions.RHTower.Sieve.MaynardRaisedDyadic
import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicCoefficientBound
import GaloisForLFunctions.RHTower.Sieve.LorentzianLSeriesLine
import GaloisForLFunctions.RHTower.Sieve.LogPolyDirPoly

/-!
# Literal grouped Heath--Brown factors

Maynard groups a bounded family of individual dyadic factors before raising one group.  This file
constructs that group at coefficient level for an arbitrary finite index type.  Its lower edge is
the product of the individual lower edges, its upper edge is exactly `2^w` times the lower edge,
where `w` is the number of factors, and the anchored coefficient vector therefore satisfies the
fixed-width support hypothesis of `MaynardRaisedDyadic`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Product of a finite family of literal arithmetic dyadic factors. -/
def groupedDyadicProduct {ι : Type*} [Fintype ι]
    (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ) : ArithmeticFunction ℝ :=
  ∏ i, arithmeticDyadicBlock (F i) (q i)

/-- Multiplicative lower edge of a grouped factor. -/
def groupedDyadicLower {ι : Type*} [Fintype ι] (q : ι → ℕ) : ℕ :=
  ∏ i, 2 ^ q i

/-- Multiplicative upper edge of a grouped factor. -/
def groupedDyadicUpper {ι : Type*} [Fintype ι] (q : ι → ℕ) : ℕ :=
  ∏ i, 2 ^ (q i + 1)

theorem vanishesBelow_groupedDyadicProduct {ι : Type*} [Fintype ι]
    (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ) :
    VanishesBelow (groupedDyadicProduct F q) (groupedDyadicLower q) := by
  classical
  have hprod : ∀ u : Finset ι,
      VanishesBelow (∏ i ∈ u, arithmeticDyadicBlock (F i) (q i))
        (∏ i ∈ u, 2 ^ q i) := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
        simpa using (show VanishesBelow (1 : ArithmeticFunction ℝ) 1 by
          intro n hn
          have hn0 : n = 0 := by omega
          subst n
          simp)
    | @insert a u ha ih =>
        simp only [Finset.prod_insert ha]
        exact vanishesBelow_mul (vanishesBelow_arithmeticDyadicBlock (F a) (q a)) ih
  simpa [groupedDyadicProduct, groupedDyadicLower] using hprod Finset.univ

theorem upperSupported_groupedDyadicProduct {ι : Type*} [Fintype ι]
    (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ) :
    UpperSupported (groupedDyadicProduct F q) (groupedDyadicUpper q) := by
  classical
  have hprod : ∀ u : Finset ι,
      UpperSupported (∏ i ∈ u, arithmeticDyadicBlock (F i) (q i))
        (∏ i ∈ u, 2 ^ (q i + 1)) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simpa using upperSupported_one
    | @insert a u ha ih =>
        simp only [Finset.prod_insert ha]
        exact (upperSupported_arithmeticDyadicBlock (F a) (q a)).mul ih
  simpa [groupedDyadicProduct, groupedDyadicUpper] using hprod Finset.univ

/-- **Exact width law.** -/
theorem groupedDyadicUpper_eq_lower_mul_twoPow {ι : Type*} [Fintype ι]
    (q : ι → ℕ) :
    groupedDyadicUpper q = groupedDyadicLower q * 2 ^ Fintype.card ι := by
  classical
  simp only [groupedDyadicUpper, groupedDyadicLower, pow_add, pow_one]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- Coefficient vector of a grouped factor, anchored at positive integers. -/
def groupedDyadicCoeffVector {ι : Type*} [Fintype ι]
    (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ) :
    Fin (groupedDyadicUpper q) → ℂ := fun j =>
  complexCoeff (groupedDyadicProduct F q) ((j : ℕ) + 1)

/-- **The literal grouped vector has fixed multiplicative width `2^w`.** -/
theorem groupedDyadicCoeffVector_support_fixedWidth {ι : Type*} [Fintype ι]
    (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ)
    (j : Fin (groupedDyadicUpper q))
    (hj : groupedDyadicCoeffVector F q j ≠ 0) :
    groupedDyadicLower q ≤ (j : ℕ) + 1 ∧
      (j : ℕ) + 1 ≤ groupedDyadicLower q * 2 ^ Fintype.card ι := by
  have hreal : groupedDyadicProduct F q ((j : ℕ) + 1) ≠ 0 := by
    intro hzero
    exact hj (by simp [groupedDyadicCoeffVector, complexCoeff_apply, hzero])
  have hlower : groupedDyadicLower q ≤ (j : ℕ) + 1 := by
    by_contra hnot
    have hlt : (j : ℕ) + 1 < groupedDyadicLower q := Nat.lt_of_not_ge hnot
    exact hreal (vanishesBelow_groupedDyadicProduct F q _ hlt)
  have hupper : (j : ℕ) + 1 ≤ groupedDyadicUpper q :=
    (Finset.mem_Icc.mp (upperSupported_groupedDyadicProduct F q _ hreal)).2
  have hupper' : (j : ℕ) + 1 ≤ groupedDyadicLower q * 2 ^ Fintype.card ι :=
    hupper.trans_eq (groupedDyadicUpper_eq_lower_mul_twoPow q)
  exact ⟨hlower, hupper'⟩

/-- **Pointwise coefficient bound for a grouped factor.**  If every selected dyadic factor is
bounded by `L`, a `w`-factor group costs at most `(d(n)L)^w`. -/
theorem norm_groupedDyadicProduct_le_divisors_mul_pow
    {ι : Type*} [Fintype ι] (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ)
    {L : ℝ} (hL : 0 ≤ L)
    (hfactor : ∀ i n, ‖arithmeticDyadicBlock (F i) (q i) n‖ ≤ L)
    (n : ℕ) :
    ‖groupedDyadicProduct F q n‖
      ≤ ((n.divisors.card : ℝ) * L) ^ Fintype.card ι := by
  classical
  have hprod : ∀ u : Finset ι,
      ‖(∏ i ∈ u, arithmeticDyadicBlock (F i) (q i)) n‖
        ≤ ((n.divisors.card : ℝ) * L) ^ u.card := by
    intro u
    induction u using Finset.induction_on generalizing n with
    | empty =>
        by_cases hn : n = 1 <;> simp [hn]
    | @insert a u ha ih =>
        rw [Finset.prod_insert ha, ArithmeticFunction.mul_apply]
        calc
          ‖∑ x ∈ n.divisorsAntidiagonal,
              arithmeticDyadicBlock (F a) (q a) x.1 *
                (∏ i ∈ u, arithmeticDyadicBlock (F i) (q i)) x.2‖
              ≤ ∑ x ∈ n.divisorsAntidiagonal,
                  ‖arithmeticDyadicBlock (F a) (q a) x.1 *
                    (∏ i ∈ u, arithmeticDyadicBlock (F i) (q i)) x.2‖ :=
                norm_sum_le _ _
          _ ≤ ∑ _x ∈ n.divisorsAntidiagonal,
                L * (((n.divisors.card : ℝ) * L) ^ u.card) := by
            apply Finset.sum_le_sum
            intro x hx
            have hn0 : n ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hx).2
            have hxn : x.2 ∣ n :=
              Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)
            have hcard : (x.2.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
              exact_mod_cast card_divisors_mono_of_dvd hxn hn0
            have hbase : (x.2.divisors.card : ℝ) * L
                ≤ (n.divisors.card : ℝ) * L :=
              mul_le_mul_of_nonneg_right hcard hL
            rw [norm_mul]
            exact mul_le_mul (hfactor a x.1)
              ((ih x.2).trans (pow_le_pow_left₀ (by positivity) hbase u.card))
              (norm_nonneg _) hL
          _ = ((n.divisors.card : ℝ) * L) ^ (insert a u).card := by
            rw [Finset.sum_const, nsmul_eq_mul,
              card_divisorsAntidiagonal_eq_card_divisors,
              Finset.card_insert_of_notMem ha, pow_succ]
            ring
  simpa [groupedDyadicProduct] using hprod Finset.univ

/-- **Base-group energy with an arbitrarily small divisor loss.** -/
theorem exists_sum_normSq_groupedDyadicCoeffVector_le
    {ι : Type*} [Fintype ι] (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ)
    {L : ℝ} (hL : 0 ≤ L)
    (hfactor : ∀ i n, ‖arithmeticDyadicBlock (F i) (q i) n‖ ≤ L)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∑ j : Fin (groupedDyadicUpper q), ‖groupedDyadicCoeffVector F q j‖ ^ 2
        ≤ (groupedDyadicUpper q : ℝ) *
          ((C * (groupedDyadicUpper q : ℝ) ^ eta * L) ^ Fintype.card ι) ^ 2 := by
  obtain ⟨C, hC, hdiv⟩ := RHTower.card_divisors_le_const_mul_rpow heta
  refine ⟨C, hC, ?_⟩
  let M := groupedDyadicUpper q
  have hM1 : 1 ≤ M := by
    dsimp [M]
    rw [groupedDyadicUpper_eq_lower_mul_twoPow]
    have hlo : 1 ≤ groupedDyadicLower q := by
      classical
      rw [groupedDyadicLower]
      have hpos : 0 < ∏ i, 2 ^ q i := Finset.prod_pos fun i _ => by positivity
      omega
    have htwo : 1 ≤ 2 ^ Fintype.card ι := Nat.one_le_two_pow
    nlinarith
  have hterm : ∀ j : Fin M,
      ‖groupedDyadicCoeffVector F q j‖ ^ 2
        ≤ ((C * (M : ℝ) ^ eta * L) ^ Fintype.card ι) ^ 2 := by
    intro j
    have hnpos : 0 < (j : ℕ) + 1 := by omega
    have hd := hdiv ((j : ℕ) + 1) hnpos
    have hjcast : ((((j : ℕ) + 1 : ℕ) : ℝ)) ≤ (M : ℝ) := by
      exact_mod_cast j.isLt
    have hmono : ((((j : ℕ) + 1 : ℕ) : ℝ) ^ eta) ≤ (M : ℝ) ^ eta :=
      Real.rpow_le_rpow (by positivity) hjcast heta.le
    have hdM : (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ))
        ≤ C * (M : ℝ) ^ eta :=
      hd.trans (mul_le_mul_of_nonneg_left hmono hC.le)
    have hbase : (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ)) * L
        ≤ (C * (M : ℝ) ^ eta) * L :=
      mul_le_mul_of_nonneg_right hdM hL
    have hnorm := norm_groupedDyadicProduct_le_divisors_mul_pow F q hL hfactor
      ((j : ℕ) + 1)
    have hnorm' : ‖groupedDyadicCoeffVector F q j‖
        ≤ (((((j : ℕ) + 1).divisors.card : ℕ) : ℝ) * L) ^ Fintype.card ι := by
      simpa [groupedDyadicCoeffVector, complexCoeff_apply] using hnorm
    have hvec : ‖groupedDyadicCoeffVector F q j‖
        ≤ (C * (M : ℝ) ^ eta * L) ^ Fintype.card ι := by
      refine hnorm'.trans ?_
      simpa [mul_assoc] using pow_le_pow_left₀ (by positivity) hbase (Fintype.card ι)
    exact pow_le_pow_left₀ (norm_nonneg _) hvec 2
  calc
    ∑ j : Fin (groupedDyadicUpper q), ‖groupedDyadicCoeffVector F q j‖ ^ 2
        ≤ ∑ _j : Fin M,
            ((C * (M : ℝ) ^ eta * L) ^ Fintype.card ι) ^ 2 :=
          Finset.sum_le_sum fun j _ => hterm j
    _ = (M : ℝ) * ((C * (M : ℝ) ^ eta * L) ^ Fintype.card ι) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (groupedDyadicUpper q : ℝ) *
          ((C * (groupedDyadicUpper q : ℝ) ^ eta * L) ^ Fintype.card ι) ^ 2 := rfl

/-- The grouped lower edge is positive. -/
theorem one_le_groupedDyadicLower {ι : Type*} [Fintype ι] (q : ι → ℕ) :
    1 ≤ groupedDyadicLower q := by
  classical
  rw [groupedDyadicLower]
  have hpos : 0 < ∏ i, 2 ^ q i := Finset.prod_pos fun i _ => by positivity
  omega

/-- The grouped upper edge is positive. -/
theorem one_le_groupedDyadicUpper {ι : Type*} [Fintype ι] (q : ι → ℕ) :
    1 ≤ groupedDyadicUpper q := by
  rw [groupedDyadicUpper_eq_lower_mul_twoPow]
  have hlo := one_le_groupedDyadicLower q
  have htwo : 1 ≤ 2 ^ Fintype.card ι := Nat.one_le_two_pow
  nlinarith

/-- The three kinds of factors occurring in a Heath--Brown dyadic product. -/
inductive HeathBrownFactorKind where
  | moebius
  | zeta
  | log
  deriving DecidableEq

/-- Underlying arithmetic function of one Heath--Brown factor kind. -/
def heathBrownFactorBase (L X : ℕ) : HeathBrownFactorKind → ArithmeticFunction ℝ
  | .moebius => truncatedMoebius L
  | .zeta => coeffTrunc (zeta : ArithmeticFunction ℝ) X
  | .log => coeffTrunc ArithmeticFunction.log X

/-- An individual selected factor is bounded by `1+log M`, where `M` is the upper edge of the
whole group. -/
theorem norm_heathBrownGroupedFactorBlock_le
    {ι : Type*} [Fintype ι] (L X : ℕ)
    (kind : ι → HeathBrownFactorKind) (q : ι → ℕ) (i : ι) (n : ℕ) :
    ‖arithmeticDyadicBlock (heathBrownFactorBase L X (kind i)) (q i) n‖
      ≤ 1 + Real.log (groupedDyadicUpper q : ℝ) := by
  have hM1 : 1 ≤ groupedDyadicUpper q := one_le_groupedDyadicUpper q
  have hlogM : 0 ≤ Real.log (groupedDyadicUpper q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hM1)
  cases hkind : kind i with
  | moebius =>
      have hunit := norm_arithmeticDyadicBlock_le_one
        (fun n => norm_truncatedMoebius_le_one L n) (q i) n
      exact hunit.trans (by linarith)
  | zeta =>
      have hunit := norm_arithmeticDyadicBlock_le_one
        (fun n => norm_coeffTrunc_zeta_le_one X n) (q i) n
      exact hunit.trans (by linarith)
  | log =>
      change ‖arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) (q i) n‖
        ≤ 1 + Real.log (groupedDyadicUpper q : ℝ)
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [arithmeticDyadicBlock]
        linarith
      · by_cases hzero : arithmeticDyadicBlock
            (coeffTrunc ArithmeticFunction.log X) (q i) n = 0
        · rw [hzero, norm_zero]
          linarith
        · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
          have hlog := norm_arithmeticDyadicLogBlock_le_log X (q i) hn1
          have hnblock := upperSupported_arithmeticDyadicBlock
            (coeffTrunc ArithmeticFunction.log X) (q i) n hzero
          have hsingle : 2 ^ (q i + 1) ≤ groupedDyadicUpper q := by
            rw [groupedDyadicUpper]
            exact Finset.single_le_prod'
              (s := (Finset.univ : Finset ι))
              (f := fun k => 2 ^ (q k + 1))
              (fun k _ => Nat.one_le_two_pow) (Finset.mem_univ i)
          have hnM : n ≤ groupedDyadicUpper q :=
            (Finset.mem_Icc.mp hnblock).2.trans hsingle
          have hlogmono : Real.log (n : ℝ) ≤ Real.log (groupedDyadicUpper q : ℝ) :=
            Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnM)
          exact hlog.trans (by linarith)

/-- Base-group energy for literal Heath--Brown factor kinds. -/
theorem exists_sum_normSq_heathBrownGroupedCoeffVector_le
    {ι : Type*} [Fintype ι] (L X : ℕ)
    (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∑ j : Fin (groupedDyadicUpper q),
          ‖groupedDyadicCoeffVector (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2
        ≤ (groupedDyadicUpper q : ℝ) *
          ((C * (groupedDyadicUpper q : ℝ) ^ eta *
            (1 + Real.log (groupedDyadicUpper q : ℝ))) ^ Fintype.card ι) ^ 2 := by
  apply exists_sum_normSq_groupedDyadicCoeffVector_le
  · have hM1 := one_le_groupedDyadicUpper q
    have hlog : 0 ≤ Real.log (groupedDyadicUpper q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hM1)
    linarith
  · exact norm_heathBrownGroupedFactorBlock_le L X kind q
  · exact heta

/-- **Complete coefficient-energy package after raising a literal grouped factor.** -/
theorem exists_sum_normSq_convPow_heathBrownGrouped_le
    {ι : Type*} [Fintype ι] (L X ell : ℕ) (hell : 0 < ell)
    (kind : ι → HeathBrownFactorKind) (q : ι → ℕ)
    {eta xi : ℝ} (heta : 0 < eta) (hxi : 0 < xi) :
    ∃ Cbase Craise : ℝ, 0 < Cbase ∧ 0 < Craise ∧
      ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
        ‖convPow (groupedDyadicUpper q) ell
          (groupedDyadicCoeffVector (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ 2
      ≤ Craise * (((groupedDyadicUpper q) ^ ell : ℕ) : ℝ) ^ xi *
        (((groupedDyadicUpper q : ℝ) *
          ((Cbase * (groupedDyadicUpper q : ℝ) ^ eta *
            (1 + Real.log (groupedDyadicUpper q : ℝ))) ^ Fintype.card ι) ^ 2) ^ ell) := by
  obtain ⟨Cbase, hCbase, hbase⟩ :=
    exists_sum_normSq_heathBrownGroupedCoeffVector_le L X kind q heta
  obtain ⟨Craise, hCraise, hraise⟩ :=
    exists_sum_normSq_convPow_le_rpow ell hell hxi
  refine ⟨Cbase, Craise, hCbase, hCraise, ?_⟩
  have hraw := hraise (groupedDyadicUpper q) (one_le_groupedDyadicUpper q)
    (groupedDyadicCoeffVector (fun i => heathBrownFactorBase L X (kind i)) q)
  have hsum0 : 0 ≤ ∑ j : Fin (groupedDyadicUpper q),
      ‖groupedDyadicCoeffVector (fun i => heathBrownFactorBase L X (kind i)) q j‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hpow := pow_le_pow_left₀ hsum0 hbase ell
  exact hraw.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

/-- L-series of a literal group is the product of its individual dyadic-factor L-series. -/
theorem LSeries_groupedDyadicProduct {ι : Type*} [Fintype ι]
    (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ) (s : ℂ) :
    LSeries (complexCoeff (groupedDyadicProduct F q)) s =
      ∏ i, LSeries (complexCoeff (arithmeticDyadicBlock (F i) (q i))) s := by
  classical
  rw [groupedDyadicProduct]
  exact LSeries_complexCoeff_finsetProd Finset.univ
    (fun i => arithmeticDyadicBlock (F i) (q i)) s
    (fun i _ => LSeriesSummable_complexCoeff_arithmeticDyadicBlock (F i) (q i) s)

/-- **Vertical-line group identity.**  The coefficient vector used by Huxley is exactly the
literal product of the grouped arithmetic factors at `sigma+it`. -/
theorem dirPoly_groupedDyadicCoeffVector_eq_product {ι : Type*} [Fintype ι]
    (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ) (sigma t : ℝ) :
    dirPoly (groupedDyadicUpper q)
        (sigmaWeightedCoeff (groupedDyadicUpper q) (groupedDyadicCoeffVector F q) sigma) (-t) =
      ∏ i, LSeries (complexCoeff (arithmeticDyadicBlock (F i) (q i)))
        ((sigma : ℂ) + (t : ℝ) * Complex.I) := by
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 (groupedDyadicUpper q) := by simp
  have hsupp : ∀ n : ℕ, complexCoeff (groupedDyadicProduct F q) n ≠ 0 →
      n ∈ Finset.Icc 1 (groupedDyadicUpper q) := by
    intro n hn
    apply upperSupported_groupedDyadicProduct F q n
    intro hzero
    exact hn (by simp [complexCoeff_apply, hzero])
  let c : ℕ → ℂ := fun n => complexCoeff (groupedDyadicProduct F q) n *
    ((((n : ℝ) ^ (-sigma) : ℝ)) : ℂ)
  have hline := LSeries_eq_logPoly_of_support hs0 hsupp sigma t
  rw [LSeries_groupedDyadicProduct] at hline
  rw [logPoly_eq_dirPoly] at hline
  have hfreq : 2 * Real.pi * (-t / (2 * Real.pi)) = -t := by
    field_simp [Real.pi_ne_zero]
  rw [hfreq] at hline
  have hcoeff : (fun n : Fin (groupedDyadicUpper q) =>
      complexCoeff (groupedDyadicProduct F q) ((n : ℕ) + 1) *
        ((((((n : ℕ) + 1 : ℕ) : ℝ) ^ (-sigma) : ℝ)) : ℂ)) =
      sigmaWeightedCoeff (groupedDyadicUpper q) (groupedDyadicCoeffVector F q) sigma := by
    rfl
  rw [hcoeff] at hline
  exact hline.symm

/-- **Exact power law for a literal grouped factor.**  The abstract raised value is the `ℓ`-th
power of the group's ordinary weighted Dirichlet polynomial. -/
theorem raised_groupedDyadicValue_eq_pow {ι : Type*} [Fintype ι]
    (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ) (ℓ : ℕ) (sigma t : ℝ) :
    raisedDirichletValue (groupedDyadicUpper q) ℓ (groupedDyadicCoeffVector F q) sigma t =
      (dirPoly (groupedDyadicUpper q)
        (sigmaWeightedCoeff (groupedDyadicUpper q) (groupedDyadicCoeffVector F q) sigma)
        (-t)) ^ ℓ :=
  raisedDirichletValue_eq_pow _ _ _ _ _

/-- **Literal grouped-product powering law.** -/
theorem raised_groupedDyadicValue_eq_product_pow {ι : Type*} [Fintype ι]
    (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ) (ℓ : ℕ) (sigma t : ℝ) :
    raisedDirichletValue (groupedDyadicUpper q) ℓ (groupedDyadicCoeffVector F q) sigma t =
      (∏ i, LSeries (complexCoeff (arithmeticDyadicBlock (F i) (q i)))
        ((sigma : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ := by
  rw [raised_groupedDyadicValue_eq_pow,
    dirPoly_groupedDyadicCoeffVector_eq_product]

end RHTower.Sieve
