import GaloisForLFunctions.RHTower.MobiusDivisorContinuousHeadMoment
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Finite-clock positivity of the literal processed divisor source

For every finite prime core and every upper clock boundary, the inverse-cube
primitive of the actual signed head retains at least one forty-eighth of the
unprocessed primitive. It is strictly positive exactly after the first source
birth. The constant is independent of both the core and the cutoff.

The finite Euler products bound the total odd-parity divisor weight by 47/48.
Nonnegative monotone truncated unit primitives then retain the unit contribution
against every negative divisor contribution. Dilation preserves the original
upper boundary; no infinite-clock limit is substituted for the finite integral.

This is an inverse-cube moment statement, not a bound for the critical Suzuki
clock action or for multiplication by a sign-changing second head.
-/

noncomputable section
open Finset Filter Topology MeasureTheory Set
namespace RHTower

private def weight (n : ℕ) : ℝ := Real.sqrt n / (n : ℝ)^2

private lemma weight_nonneg (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity

private lemma weight_rpow (n : ℕ) : weight n = (n : ℝ)^(-3/2 : ℝ) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · norm_num [weight]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [weight, Real.sqrt_eq_rpow, ← Real.rpow_natCast (n : ℝ) 2,
    ← Real.rpow_sub hnR]
  norm_num

private lemma weight_summable : Summable weight := by
  change Summable (fun n => weight n)
  simp_rw [weight_rpow]
  exact Real.summable_nat_rpow.mpr (by norm_num)

private lemma weight_succ_le (n : ℕ) (hn : 0 < n) :
    weight (n+1) ≤ 2 / Real.sqrt n - 2 / Real.sqrt (n+1 : ℕ) := by
  have hu : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hv : 0 < Real.sqrt (n+1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
  have hsqs := Real.sq_sqrt (Nat.cast_nonneg (n+1))
  have huv : Real.sqrt (n : ℝ) ≤ Real.sqrt (n+1 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)
  have hrec : weight (n+1) = 1 / Real.sqrt (n+1 : ℕ)^3 := by
    unfold weight
    field_simp
    nlinarith only [congrArg (fun x : ℝ => x^2) hsqs]
  have hdiff : 2 / Real.sqrt n - 2 / Real.sqrt (n+1 : ℕ) =
      2 / (Real.sqrt n * Real.sqrt (n+1 : ℕ) *
        (Real.sqrt n + Real.sqrt (n+1 : ℕ))) := by
    field_simp
    have hcast : ((n+1 : ℕ) : ℝ) = (n : ℝ)+1 := by push_cast; ring
    nlinarith only [hsq, hsqs, hcast]
  rw [hrec, hdiff]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hmul := mul_le_mul_of_nonneg_left huv hu.le
  have hmul' := mul_le_mul_of_nonneg_left huv hv.le
  nlinarith [mul_nonneg hv.le (sub_nonneg.mpr hmul),
    mul_nonneg hv.le (sub_nonneg.mpr hmul')]

private lemma weight_le_of_sq (n : ℕ) (b : ℝ) (hb : 0 < b) (hn : 0 < n)
    (hsq : (1 / ((n : ℝ) * b))^2 ≤ (n : ℝ)) : weight n ≤ b := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hlow : 1 / ((n : ℝ) * b) ≤ Real.sqrt n := by
    nlinarith [Real.sq_sqrt hnR.le, Real.sqrt_nonneg (n : ℝ)]
  have hh := (div_le_iff₀ (mul_pos hnR hb)).mp hlow
  unfold weight
  apply (div_le_iff₀ (pow_pos hnR 2)).mpr
  have hm := mul_le_mul_of_nonneg_left hh hs.le
  nlinarith [Real.sq_sqrt hnR.le]

private lemma weight_prefix : (∑ n ∈ range 10, weight n) ≤ 2 := by
  have h2 := weight_le_of_sq 2 (5/14) (by norm_num) (by norm_num) (by norm_num)
  have h3 := weight_le_of_sq 3 (1/5) (by norm_num) (by norm_num) (by norm_num)
  have h5 := weight_le_of_sq 5 (1/10) (by norm_num) (by norm_num) (by norm_num)
  have h6 := weight_le_of_sq 6 (5/72) (by norm_num) (by norm_num) (by norm_num)
  have h7 := weight_le_of_sq 7 (2/35) (by norm_num) (by norm_num) (by norm_num)
  have h8 := weight_le_of_sq 8 (5/112) (by norm_num) (by norm_num) (by norm_num)
  have h0 : weight 0 = 0 := by norm_num [weight]
  have h1 : weight 1 = 1 := by norm_num [weight]
  have h4 : weight 4 = 1/8 := by norm_num [weight, Real.sqrt_eq_iff_mul_self_eq]
  have h9 : weight 9 = 1/27 := by norm_num [weight, Real.sqrt_eq_iff_mul_self_eq]
  norm_num only [Finset.sum_range_succ, sum_range_zero, h0, h1, h4, h9]
  linarith

private lemma weight_sum_bound : (∑' n, weight n) ≤ 8/3 := by
  have hlarge : ∀ N, 9 ≤ N →
      (∑ n ∈ range (N+1), weight n) ≤ 8/3 - 2/Real.sqrt N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      have h9 : Real.sqrt (9 : ℝ) = 3 := by norm_num
      norm_num only [Nat.cast_ofNat, h9] at *
      linarith [weight_prefix]
    | succ N hN ih =>
      rw [Finset.sum_range_succ]
      have h := weight_succ_le N (by omega)
      linarith
  apply weight_summable.tsum_le_of_sum_range_le
  intro N
  by_cases hN : N ≤ 10
  · have hsub : range N ⊆ range 10 := range_mono hN
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => weight_nonneg n)).trans
      (weight_prefix.trans (by norm_num))
  · have h := hlarge (N-1) (by omega)
    rw [show N-1+1=N by omega] at h
    exact h.trans (sub_le_self _ (by positivity))

private def weightHom : ℕ →* ℝ where
  toFun := weight
  map_one' := by norm_num [weight]
  map_mul' m n := by
    simp only [weight, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m), mul_pow]
    ring

private lemma prime_weight {p : ℕ} (hp : p.Prime) : weight p ≤ 1/2 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs := Real.sq_sqrt (Nat.cast_nonneg p)
  have hs0 := Real.sqrt_nonneg (p : ℝ)
  unfold weight
  rw [div_le_iff₀ (pow_pos (by linarith : (0 : ℝ)<p) 2)]
  nlinarith [sq_nonneg ((p : ℝ)-1)]

private lemma minus_prod_lower (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (3/8 : ℝ) ≤ ∏ p ∈ P, (1-weight p) := by
  have hs : Summable weightHom := weight_summable
  have he := EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers hs P
  have hf : P.filter Nat.Prime = P := filter_eq_self.mpr hP
  rw [hf] at he
  change (∏ p ∈ P, (1-weight p)⁻¹) = _ at he
  have hb := (Summable.tsum_subtype_le weight (Nat.factoredNumbers P)
    weight_nonneg weight_summable).trans weight_sum_bound
  change (∑' n : Nat.factoredNumbers P, weightHom n) ≤ (8/3 : ℝ) at hb
  rw [← he, prod_inv_distrib] at hb
  have hpos : 0 < ∏ p ∈ P, (1-weight p) :=
    prod_pos (fun p hp => by have := prime_weight (hP p hp); linarith)
  have hm := mul_le_mul_of_nonneg_right hb hpos.le
  rw [inv_mul_cancel₀ hpos.ne'] at hm
  linarith

private lemma plus_prod_upper_two (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (h2 : 2 ∈ P) : (∏ p ∈ P, (1+weight p)) ≤ (7/3 : ℝ) := by
  have hprod : (∏ p ∈ P, (1+weight p)) * (∏ p ∈ P, (1-weight p)) =
      ∏ p ∈ P, (1-weight p^2) := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro p _
    ring
  have htail : (∏ p ∈ P.erase 2, (1-weight p^2)) ≤ 1 := by
    apply prod_le_one
    · intro p hp
      have hw := prime_weight (hP p (mem_erase.mp hp).2)
      have hw0 := weight_nonneg p
      nlinarith
    · intro p _
      nlinarith [sq_nonneg (weight p)]
  have htwo : 1-weight 2^2 = (7/8 : ℝ) := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    norm_num [weight, div_pow] at *
  have hmass : (∏ p ∈ P, (1-weight p^2)) ≤ (7/8 : ℝ) := by
    rw [← insert_erase h2, prod_insert (notMem_erase 2 P), htwo]
    nlinarith
  have hlow := minus_prod_lower P hP
  have hplus : 0 ≤ ∏ p ∈ P, (1+weight p) :=
    prod_nonneg (fun p _ => by have := weight_nonneg p; linarith)
  nlinarith [mul_le_mul_of_nonneg_left hlow hplus]

private lemma odd_mass_gap (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, (1+weight p)) - (∏ p ∈ P, (1-weight p)) ≤ (47/24 : ℝ) := by
  have hQ : ∀ p ∈ insert 2 P, p.Prime := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · norm_num
    · exact hP p hp
  have hu := plus_prod_upper_two (insert 2 P) hQ (mem_insert_self 2 P)
  have hl := minus_prod_lower (insert 2 P) hQ
  by_cases h2 : 2 ∈ P
  · simpa [Finset.insert_eq_of_mem h2] using (show
      (∏ p ∈ insert 2 P, (1+weight p)) - (∏ p ∈ insert 2 P, (1-weight p)) ≤
        (47/24 : ℝ) by linarith)
  · rw [prod_insert h2] at hu hl
    have ha : 0 ≤ ∏ p ∈ P, (1+weight p) :=
      prod_nonneg (fun p _ => by have := weight_nonneg p; linarith)
    have hb : 0 ≤ ∏ p ∈ P, (1-weight p) :=
      prod_nonneg (fun p hp => by have := prime_weight (hP p hp); linarith)
    nlinarith [mul_nonneg (weight_nonneg 2) (add_nonneg ha hb)]

private def weightAF : ArithmeticFunction ℝ := ⟨weight, by norm_num [weight]⟩

private lemma weightAF_mult : weightAF.IsMultiplicative := by
  constructor
  · norm_num [weightAF, weight]
  · intro m n _
    exact weightHom.map_mul m n

private lemma sum_weights (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ d ∈ (∏ p ∈ P, p).divisors, weight d) = ∏ p ∈ P, (1+weight p) := by
  have h := weightAF_mult.prodPrimeFactors_one_add_of_squarefree
    (GibbsGas.squarefree_prod_primes hP)
  rw [Nat.primeFactors_prod hP] at h
  exact h.symm

private lemma sum_signed_weights (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ d ∈ (∏ p ∈ P, p).divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)*weight d) =
        ∏ p ∈ P, (1-weight p) := by
  have h := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    weightAF weightAF_mult (GibbsGas.squarefree_prod_primes hP)
  rw [Nat.primeFactors_prod hP] at h
  exact h.symm

private lemma signed_profile_lower (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (J : ℕ → ℝ) (hJ0 : 0 ≤ J 1)
    (hJ : ∀ d ∈ (∏ p ∈ P, p).divisors, 0 ≤ J d ∧ J d ≤ J 1) :
    J 1 / 48 ≤ ∑ d ∈ (∏ p ∈ P, p).divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)*weight d*J d := by
  let D := ∏ p ∈ P, p
  have hD : 0 < D := prod_pos (fun p hp => (hP p hp).pos)
  have h1 : 1 ∈ D.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, hD.ne'⟩
  have hpoint (d : ℕ) (hd : d ∈ D.divisors) :
      (if d=1 then J 1 else 0) -
        ((1-((ArithmeticFunction.moebius d : ℤ) : ℝ))/2)*weight d*J 1 ≤
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)*weight d*J d := by
    by_cases hd1 : d=1
    · subst d
      simp [weight]
    have hsf : Squarefree d := Squarefree.squarefree_of_dvd
      (Nat.mem_divisors.mp hd).1 (GibbsGas.squarefree_prod_primes hP)
    have hmu := ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp
      (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsf)
    rw [if_neg hd1]
    rcases hmu with hmu | hmu
    · simp only [hmu, Int.cast_one, sub_self, zero_div, zero_mul, one_mul]
      exact mul_nonneg (weight_nonneg d) (hJ d hd).1
    · simp only [hmu, Int.cast_neg, Int.cast_one]
      have h := mul_le_mul_of_nonneg_left (hJ d hd).2 (weight_nonneg d)
      linarith
  have hs := sum_le_sum hpoint
  have he : (∑ d ∈ D.divisors,
      ((if d=1 then J 1 else 0) -
        ((1-((ArithmeticFunction.moebius d : ℤ) : ℝ))/2)*weight d*J 1)) =
      J 1 - ((∏ p ∈ P, (1+weight p))-(∏ p ∈ P, (1-weight p)))/2*J 1 := by
    rw [sum_sub_distrib]
    have hsingle : (∑ d ∈ D.divisors, if d=1 then J 1 else 0) = J 1 := by
      simp [h1]
    rw [hsingle]
    congr 1
    calc
      _ = ((∑ d ∈ D.divisors, weight d) -
          ∑ d ∈ D.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)*weight d)/2*J 1 := by
        rw [← sum_sub_distrib, sum_div, sum_mul]
        apply sum_congr rfl
        intro d _
        ring
      _ = _ := by rw [sum_weights P hP, sum_signed_weights P hP]
  rw [he] at hs
  have hg := mul_le_mul_of_nonneg_right (odd_mass_gap P hP) hJ0
  linarith

private def unitPrimitive (X : ℝ) : ℝ :=
  ∫ x in Ioc (0 : ℝ) X, divisorContinuousUnitHead x / x^3

private lemma unit_integrable (X : ℝ) :
    IntegrableOn (fun x => divisorContinuousUnitHead x / x^3) (Ioc 0 X) :=
  integrable_divisorContinuousUnitHead_moment.mono_set Ioc_subset_Ioi_self

private lemma unit_nonneg (X : ℝ) : 0 ≤ unitPrimitive X := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact div_nonneg (divisorContinuousUnitHead_nonneg x) (pow_nonneg hx.1.le _)

private lemma unit_mono {X Y : ℝ} (hXY : X ≤ Y) : unitPrimitive X ≤ unitPrimitive Y := by
  apply setIntegral_mono_set (unit_integrable Y)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact div_nonneg (divisorContinuousUnitHead_nonneg x) (pow_nonneg hx.1.le _)
  · exact Filter.Eventually.of_forall (fun x hx => ⟨hx.1, hx.2.trans hXY⟩)

private lemma dilation_integrand (d x : ℝ) (hd : d ≠ 0) :
    divisorContinuousUnitHead (x/d)/x^3 =
      (d^3)⁻¹ * (divisorContinuousUnitHead (d⁻¹*x)/(d⁻¹*x)^3) := by
  rw [div_eq_mul_inv x d, mul_comm x d⁻¹]
  by_cases hx : x=0
  · simp [hx]
  · field_simp

private lemma dilation_integrable {d : ℝ} (hd : 0 < d) (X : ℝ) :
    IntegrableOn (fun x => divisorContinuousUnitHead (x/d)/x^3) (Ioc 0 X) := by
  have hc := (integrableOn_Ioi_comp_mul_left_iff
    (fun x => divisorContinuousUnitHead x/x^3) 0 (inv_pos.mpr hd)).mpr
    (by simpa using integrable_divisorContinuousUnitHead_moment)
  have hi : IntegrableOn (fun x => divisorContinuousUnitHead (x/d)/x^3) (Ioi 0) := by
    apply (hc.const_mul (d^3)⁻¹).congr
    filter_upwards with x
    exact (dilation_integrand d x hd.ne').symm
  exact hi.mono_set Ioc_subset_Ioi_self

private lemma dilation_primitive {d X : ℝ} (hd : 0 < d) (hX : 0 ≤ X) :
    (∫ x in Ioc (0 : ℝ) X, divisorContinuousUnitHead (x/d)/x^3) =
      (d^2)⁻¹ * unitPrimitive (X/d) := by
  rw [← intervalIntegral.integral_of_le hX]
  simp_rw [dilation_integrand d _ hd.ne']
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => divisorContinuousUnitHead x/x^3) (inv_ne_zero hd.ne'), mul_zero,
    inv_inv, smul_eq_mul]
  rw [intervalIntegral.integral_of_le (mul_nonneg (inv_nonneg.mpr hd.le) hX)]
  rw [show d⁻¹*X = X/d by ring]
  unfold unitPrimitive
  field_simp

private lemma actual_primitive_eq (P : Finset ℕ) (X : ℝ) (hX : 0 ≤ X) :
    (∫ x in Ioc (0 : ℝ) X, mobiusDivisorContinuousHead P x/x^3) =
      ∑ d ∈ (∏ p ∈ P, p).divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*weight d*unitPrimitive (X/d) := by
  simp only [mobiusDivisorContinuousHead, sum_div, mul_div_assoc]
  rw [integral_finsetSum _ (fun d hd =>
    (dilation_integrable (by exact_mod_cast Nat.pos_of_mem_divisors hd) X).const_mul _)]
  apply sum_congr rfl
  intro d hd
  rw [integral_const_mul, dilation_primitive (by exact_mod_cast Nat.pos_of_mem_divisors hd) hX]
  unfold weight
  ring

private theorem actual_primitive_lower (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (X : ℝ) :
    unitPrimitive X / 48 ≤
      ∫ x in Ioc (0 : ℝ) X, mobiusDivisorContinuousHead P x/x^3 := by
  by_cases hX : 0 ≤ X
  · rw [actual_primitive_eq P X hX]
    have h := signed_profile_lower P hP (fun d => unitPrimitive (X/d))
      (by simpa using unit_nonneg X) (by
        intro d hd
        refine ⟨unit_nonneg _, unit_mono ?_⟩
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd
        simpa using div_le_self hX hd1)
    simpa using h
  · have he : Ioc (0 : ℝ) X = ∅ := Ioc_eq_empty_of_le (le_of_not_ge hX)
    simp [unitPrimitive, he]

private lemma unit_pos {X : ℝ} (hX : 1 < X) : 0 < unitPrimitive X := by
  apply (integral_pos_iff_support_of_nonneg_ae _ (unit_integrable X)).mpr
  · let b := min 2 X
    have hb : 1 < b := lt_min (by norm_num) hX
    have hsub : Ioo (1 : ℝ) b ⊆ Function.support
        (fun x => divisorContinuousUnitHead x/x^3) := by
      intro x hx
      exact ne_of_gt (div_pos (divisorContinuousUnitHead_pos_first
        ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩) (pow_pos (by linarith [hx.1]) 3))
    apply lt_of_lt_of_le _ (measure_mono hsub)
    rw [Measure.restrict_apply measurableSet_Ioo]
    have he : Ioo (1 : ℝ) b ∩ Ioc 0 X = Ioo (1 : ℝ) b :=
      inter_eq_left.mpr (fun x hx => ⟨by linarith [hx.1],
        hx.2.le.trans (min_le_right _ _)⟩)
    rw [he, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hb)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact div_nonneg (divisorContinuousUnitHead_nonneg x) (pow_nonneg hx.1.le _)

private theorem actual_primitive_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {X : ℝ} (hX : 1 < X) :
    0 < ∫ x in Ioc (0 : ℝ) X, mobiusDivisorContinuousHead P x/x^3 :=
  (div_pos (unit_pos hX) (by norm_num)).trans_le (actual_primitive_lower P hP X)


/-- The actual signed finite-clock primitive has a core-independent positive
margin and a sharp source-birth threshold, for all finite sets of actual primes.
No source-sign, cancellation, convergence-rate, or RH premise is assumed. -/
theorem mobiusDivisorContinuousHead_finite_clock_cancellation :
    ∀ (P : Finset Nat.Primes) (X : ℝ),
      (∫ x in Ioc (0 : ℝ) X, divisorContinuousUnitHead x / x^3) / 48 ≤
        (∫ x in Ioc (0 : ℝ) X,
          mobiusDivisorContinuousHead (P.image (fun p : Nat.Primes => (p : ℕ))) x / x^3) ∧
      (0 < (∫ x in Ioc (0 : ℝ) X,
          mobiusDivisorContinuousHead (P.image (fun p : Nat.Primes => (p : ℕ))) x / x^3) ↔
        1 < X) := by
  intro P X
  let Q : Finset ℕ := P.image (fun p : Nat.Primes => (p : ℕ))
  have hQ : ∀ p ∈ Q, p.Prime := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := mem_image.mp hp
    exact q.property
  refine ⟨actual_primitive_lower Q hQ X, ?_⟩
  constructor
  · intro hpos
    by_contra hX
    have hz : (∫ x in Ioc (0 : ℝ) X, mobiusDivisorContinuousHead Q x/x^3) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      simp only [mobiusDivisorContinuousHead_eq_zero Q (hx.2.trans (le_of_not_gt hX)), zero_div, Pi.zero_apply]
    change 0 < (∫ x in Ioc (0 : ℝ) X, mobiusDivisorContinuousHead Q x/x^3) at hpos
    linarith
  · exact actual_primitive_pos Q hQ

end RHTower
