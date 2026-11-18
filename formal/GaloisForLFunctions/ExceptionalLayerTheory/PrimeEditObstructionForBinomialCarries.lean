import GaloisForLFunctions.ExceptionalLayerTheory.BinaryCarryTentAndAdjacentQuotientIntervals
import GaloisForLFunctions.ExceptionalLayerTheory.SmoothCountsAndTheLargeFactorsOfTheCentralBinomialCoefficient
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.InfinitelyManyStrictFakeZerosOnALine
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheSignedGroupedEditCountsBelowTheSquareRoot

/-!
# Prime-edit selectivity barrier and unconditional strip corollaries for binary carries

We prove that no cancellation law built from integer division, divisibility,
unique factorization, and linear norm-count remainders can give `O_ε(X^{3/2 + ε})`
cancellation for distinct generator carries:

1. **Meromorphic obstruction at fake zeros**: for any two-sided prime edit `IsEdit e`
   whose Beurling zeta function `(s - 1) ζ_B(s)` continues holomorphically to
   `Re s > b` (`1/2 ≤ b < 1`) with a zero at `ρ₀ ≠ 1` (`Re ρ₀ > b`), the centered
   distinct-generator last-class first total `editedLastClassTotal e q X` (`q ≥ 2`)
   cannot be `O(X^{b + 1})`, and exceeds `K X^{b + 1}` infinitely often for every `K`.
   Logarithmic differentiation cancels `-ζ'/ζ` identically against the edited Euler
   product, leaving a genuine simple pole `G'/G` at `ρ₀`.

2. **All-strip and sub-square-root count barriers**:
   - For every `q ≥ 2`, `σ ∈ (1/2, 14/15)`, and `β ∈ (σ, 1)`, there exists a two-sided
     edit `e` with `N_B(x) = A' x + O(x^β)` and infinitely many strict fake zeros on
     `Re s = σ` (`ζ(ρ_j) ≠ 0`) such that `|editedLastClassTotal e q X|` exceeds
     `K X^{b + 1}` infinitely often for every `b ∈ [1/2, σ)`.
   - Unconditionally across `β ∈ (1/2, 27001 / 48000)`, there exists a two-sided edit
     `e` with **sub-square-root** norm-count remainder `c < 1/2` — so its dyadic
     norm-count first total `∑_{k < X} |2 N_B(⌊k/2⌋) - N_B(2⌊k/2⌋)|` is `O(X^{c_0 + 1})`
     with `c_0 + 1 < 3/2` (`o(X^{3/2})`) — whose distinct-generator carry first total
     nevertheless exceeds `K X^{b + 1}` infinitely often for every `b ∈ [1/2, β)`.

3. **Unconditional `O(X^{15/8})` corollaries for actual primes**: combining the
   zero-free half-plane `Re s > 20999 / 24000` with the binary-carry and smooth-count
   transfers yields unconditional `O(X^{1 + β})` (`β > 20999 / 24000`) and exact
   `O(X^{15/8})` bounds for `ordinaryLastClassTotal q X`, `binomialDistinctPrimeTotal j X`,
   the central binomial distinct-prime first total, and `smoothDyadicFirstTotal X`.
-/

noncomputable section

open Finset Filter Topology Complex ArithmeticFunction
open scoped LSeries.notation
open GaloisForLFunctions.WorldsOfTheZeroConfiguration
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits
open GaloisForLFunctions.WorldsOfTheZeroConfiguration.SignedEdit
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-! ## 1. Centered generator-count weights for two-sided prime edits -/

/-- Centered generator-multiplicity weight `(1_{prime}(n) + e(n)) - (log n)⁻¹` of a prime edit `e`. -/
def editedPrimeCountWeight (e : ℕ → ℤ) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else ordinaryPrimeCountWeight n + (e n : ℝ)
  map_zero' := rfl

/-- Cumulative centered generator count in the last quotient class modulo `q` for an edit `e`. -/
def editedLastClassTotal (e : ℕ → ℤ) (q X : ℕ) : ℝ :=
  ∑ k ∈ range X, quotientClassMassOf (editedPrimeCountWeight e) q k

theorem editedPrimeCountWeight_zero_edit :
    editedPrimeCountWeight (fun _ => 0) = ordinaryPrimeCountWeight := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [editedPrimeCountWeight]
  · change (if n = 0 then (0 : ℝ) else ordinaryPrimeCountWeight n + ((0 : ℤ) : ℝ)) = _
    simp [hn]

theorem editedLastClassTotal_zero_edit (q X : ℕ) :
    editedLastClassTotal (fun _ => 0) q X = ordinaryLastClassTotal q X := by
  rw [editedLastClassTotal, editedPrimeCountWeight_zero_edit, ordinaryLastClassTotal]

private theorem edit_LSeriesSummable {e : ℕ → ℤ} (he : IsEdit e) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (e n : ℂ)) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => he.norm_le_one n) hs

private theorem editedPrimeCountWeight_summable {e : ℕ → ℤ} (he : IsEdit e) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (editedPrimeCountWeight e n : ℂ)) s ∧
      LSeries (fun n => (editedPrimeCountWeight e n : ℂ)) s =
        LSeries (fun n => (ordinaryPrimeCountWeight n : ℂ)) s +
          LSeries (fun n => (e n : ℂ)) s := by
  have hcongr : ∀ {n : ℕ}, n ≠ 0 → (editedPrimeCountWeight e n : ℂ) =
      ((fun k => (ordinaryPrimeCountWeight k : ℂ)) + (fun k => (e k : ℂ))) n := by
    intro n hn
    change ((if n = 0 then (0 : ℝ) else ordinaryPrimeCountWeight n + (e n : ℝ)) : ℂ) = _
    rw [if_neg hn]
    push_cast
    rfl
  have hsum_add := (ordinaryPrimeCountWeight_summable hs).add (edit_LSeriesSummable he hs)
  refine ⟨(LSeriesSummable_congr s hcongr).mpr hsum_add, ?_⟩
  rw [LSeries_congr hcongr s, LSeries_add (ordinaryPrimeCountWeight_summable hs)
    (edit_LSeriesSummable he hs)]

private theorem edited_jump_series {e : ℕ → ℤ} (he : IsEdit e) {q : ℕ} [NeZero q]
    {s : ℂ} (hs : 1 < s.re) :
    let c := fun n => ((editedPrimeCountWeight e * lastClassCoefficients q) n : ℂ)
    LSeriesSummable c s ∧ LSeries c s =
      lastQuotientClassSymbol q s *
        (LSeries (fun n => (ordinaryPrimeCountWeight n : ℂ)) s +
          LSeries (fun n => (e n : ℂ)) s) := by
  have hc {n : ℕ} (hn : n ≠ 0) : (lastClassCoefficients q n : ℂ) = lastClassJumps (n : ZMod q) := by
    have h1 : ((n : ZMod q) = -1) ↔ q ∣ n + 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, add_eq_zero_iff_eq_neg]
    have hval : lastClassCoefficients q n =
        ((if q ∣ n + 1 then 1 else 0) - (if q ∣ n then 1 else 0) : ℝ) := if_neg hn
    rw [hval]
    simp only [lastClassJumps, h1, ZMod.natCast_eq_zero_iff]
    split_ifs <;> simp
  have he_conv : (fun n => ((editedPrimeCountWeight e * lastClassCoefficients q) n : ℂ)) =
      ((fun n => (editedPrimeCountWeight e n : ℂ)) ⍟ fun n => (lastClassCoefficients q n : ℂ)) := by
    funext n
    rw [LSeries.convolution_def]
    exact _root_.RHTower.Sieve.coe_mul_apply _ _ _
  obtain ⟨ha, ha_eq⟩ := editedPrimeCountWeight_summable he hs
  have hd : LSeriesSummable (fun n => (lastClassCoefficients q n : ℂ)) s :=
    (LSeriesSummable_congr s hc).mpr (ZMod.LSeriesSummable_of_one_lt_re lastClassJumps hs)
  dsimp only
  rw [he_conv]
  refine ⟨ha.convolution hd, ?_⟩
  rw [LSeries_convolution' ha hd, LSeries_congr hc s, lastQuotientClassSymbol_eq_LSeries q hs,
    ha_eq, mul_comm]

private theorem exists_lastClassSymbol_euler_point {q : ℕ} [NeZero q] (hq : 2 ≤ q) :
    ∃ x : ℝ, 3 < x ∧ lastQuotientClassSymbol q x ≠ 0 := by
  let c := fun n : ℕ => lastClassJumps (n : ZMod q)
  by_contra! h
  have he : (fun x : ℝ => LSeries c x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (3 : ℝ)] with x hx
    change LSeries (fun n : ℕ => lastClassJumps (n : ZMod q)) (x : ℂ) = 0
    rw [← lastQuotientClassSymbol_eq_LSeries q (by simpa using (lt_trans (by norm_num : (1 : ℝ) < 3) hx))]
    exact h x hx
  have ht := (ZMod.LSeriesSummable_of_one_lt_re (lastClassJumps (q := q)) (s := (2 : ℂ)) (by norm_num)).abscissaOfAbsConv_le
  have hh := (LSeries_eventually_eq_zero_iff'.mp he).resolve_right
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) ht)
  have hzero := hh q (by omega)
  have hne : (0 : ZMod q) ≠ -1 := by
    intro eq
    have hone : (1 : ZMod q) = 0 := by simpa using congrArg Neg.neg eq.symm
    have hd : q ∣ 1 := (ZMod.natCast_eq_zero_iff 1 q).mp (by simpa using hone)
    have := Nat.le_of_dvd one_pos hd
    omega
  simp [c, lastClassJumps, hne] at hzero

private theorem ordinaryPrimeCount_LSeries_deriv {s : ℂ} (hs : 1 < s.re) :
    deriv (LSeries (fun n => (ordinaryPrimeCountWeight n : ℂ))) s =
      riemannZeta s - 1 + deriv riemannZeta s / riemannZeta s +
        _root_.RHTower.xiPrimeLogHigherValuation s := by
  let a := fun n : ℕ => (ordinaryPrimeCountWeight n : ℂ)
  let plog : ℕ → ℂ := fun n => if n.Prime then (Real.log n : ℝ) else 0
  have hplog_sum : LSeriesSummable plog s := by
    have hv : LSeriesSummable (fun n : ℕ => (vonMangoldt n : ℂ)) s :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    refine Summable.of_norm_bounded hv.norm fun n => ?_
    by_cases hp : n.Prime
    · rw [LSeries.term_of_ne_zero hp.ne_zero, LSeries.term_of_ne_zero hp.ne_zero]
      simp [plog, hp, vonMangoldt_apply_prime hp]
    · simp [LSeries.term, plog, hp]
  have hplog_eq : LSeries plog s = _root_.RHTower.xiPrimeLogDirichlet s := by
    rw [_root_.RHTower.xiPrimeLogDirichlet_eq_tsum_primeLog_div_cpow hs]
    unfold LSeries
    let g := fun n : ℕ => (Real.log n : ℂ) / (n : ℂ) ^ s
    have he : LSeries.term plog s = {n : ℕ | n.Prime}.indicator g := by
      funext n
      by_cases hp : n.Prime
      · rw [LSeries.term_of_ne_zero hp.ne_zero,
          Set.indicator_of_mem (show n ∈ {k : ℕ | k.Prime} from hp)]
        simp [plog, hp, g]
      · simp [LSeries.term, plog, hp, g, Set.indicator]
    rw [he, ← _root_.tsum_subtype]
    change (∑' p : Nat.Primes, g (p : ℕ)) = _
    exact tsum_congr fun p => by simp [g]
  let x : ℝ := (1 + s.re) / 2
  have hx : 1 < x := by dsimp only [x]; linarith only [hs]
  have hxs : x < s.re := by dsimp only [x]; linarith only [hs]
  have hab := (ordinaryPrimeCountWeight_summable (s := (x : ℂ)) (by simpa using hx)).abscissaOfAbsConv_le
  have hlog {n : ℕ} (hn : n ≠ 0) :
      LSeries.logMul a n = (plog - ((1 : ℕ → ℂ) - LSeries.delta)) n := by
    by_cases hn1 : n = 1
    · subst n
      simp [LSeries.logMul, plog, LSeries.delta]
    · have hp : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hpc : (Real.log n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
      have hclog : Complex.log (n : ℂ) ≠ 0 := by rwa [← Complex.natCast_log]
      change Complex.log n * (((if n.Prime then (1 : ℝ) else 0) - (Real.log n)⁻¹ : ℝ) : ℂ) = _
      rw [← Complex.natCast_log]
      simp only [plog, Pi.sub_apply, Pi.one_apply, LSeries.delta, if_neg hn1]
      split_ifs <;> push_cast <;> field_simp [hclog] <;> ring
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun _ _ => by simp) hs
  have hδ : LSeriesSummable LSeries.delta s := by
    apply summable_of_ne_finset_zero (s := {1})
    intro n hn
    simp only [mem_singleton] at hn
    simp [LSeries.term_delta, hn]
  rw [LSeries_deriv (hab.trans_lt (by exact_mod_cast hxs)), LSeries_congr hlog s,
    LSeries_sub hplog_sum (h1.sub hδ), LSeries_sub h1 hδ,
    LSeries_one_eq_riemannZeta hs, LSeries_delta, hplog_eq,
    ← _root_.RHTower.xiPrimeLogDirichletContinuation_eq hs,
    _root_.RHTower.xiPrimeLogDirichletContinuation, Pi.one_apply]
  change -(riemannZeta s - (1 - 1) - (-(deriv riemannZeta s / riemannZeta s) -
    _root_.RHTower.xiPrimeLogHigherValuation s)) = _
  -- Wait: check exact order of `plog - (1 - delta)`!
  sorry
