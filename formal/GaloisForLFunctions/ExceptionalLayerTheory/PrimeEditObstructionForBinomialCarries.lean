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
    _root_.RHTower.xiPrimeLogDirichletContinuation,
    _root_.RHTower.infinitePrimeFlux, logDeriv_apply, Pi.one_apply]
  ring

/-! ## 2. Meromorphic obstruction at zeros of an edited Beurling zeta function -/

/-- Any `O(X^{b + 1})` bound (`1/2 ≤ b < 1`) on `editedLastClassTotal e q` (`q ≥ 2`) excludes
every zero `ρ₀ ≠ 1` (`Re ρ₀ > b`) of the continued Beurling zeta function `G = (s - 1) ζ_B`. -/
theorem editedLastClassTotal_bound_excludes_fake_zero {e : ℕ → ℤ} (he : IsEdit e)
    {q : ℕ} (hq : 2 ≤ q) {b C : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1)
    (hbound : ∀ X : ℕ, 1 ≤ X → |editedLastClassTotal e q X| ≤ C * (X : ℝ) ^ (b + 1))
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {s : ℂ | b < s.re})
    (hG_eq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    {ρ₀ : ℂ} (hρ : b < ρ₀.re) (hρ1 : ρ₀ ≠ 1) : G ρ₀ ≠ 0 := by
  letI : NeZero q := ⟨by omega⟩
  have hC : 0 ≤ |C| := abs_nonneg C
  have hb0 : 0 ≤ b := by linarith only [hb]
  let c : ℕ → ℝ := fun n => (editedPrimeCountWeight e * lastClassCoefficients q) n
  have hprofile (N : ℕ) (hN : 1 ≤ N) :
      |triangularPrimeProfile c (N : ℝ)⁻¹| ≤ |C| * (N : ℝ) ^ b := by
    have hp : 0 < (N : ℝ) := by exact_mod_cast hN
    have heq : (N : ℝ) * triangularPrimeProfile c (N : ℝ)⁻¹ = editedLastClassTotal e q N := by
      rw [triangularPrimeProfile_sample, editedLastClassTotal]
      exact sum_congr rfl fun k _ => (quotientClassMassOf_eq_prefix _ hq k).symm
    have hh := (hbound N hN).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    rw [← heq, abs_mul, abs_of_pos hp, Real.rpow_add_one hp.ne'] at hh
    exact le_of_mul_le_mul_left (hh.trans_eq (by ring)) hp
  let U := {s : ℂ | b < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_half : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  let H := triangularDirichletContinuation c
  let D := lastQuotientClassSymbol q
  let M := H / D
  have hH : DifferentiableOn ℂ H U :=
    fun _ hs => (differentiableAt_triangularDirichletContinuation c hC hb0 hprofile hs).differentiableWithinAt
  have hD : Differentiable ℂ D := differentiable_lastQuotientClassSymbol q
  have hM : MeromorphicOn M U :=
    fun z hz => ((hH.analyticOnNhd hU z hz).meromorphicAt).div ((hD.analyticAt z).meromorphicAt)
  -- Identify `H` on `Re s > 3`
  let f : ℕ → ℂ := fun n => (c n : ℂ)
  have hf2 : LSeriesSummable f 2 := (edited_jump_series he (q := q) (s := 2) (by norm_num)).1
  let Bnd := ∑' n, ‖LSeries.term f 2 n‖
  have hcoef (n : ℕ) : |c (n + 1)| ≤ Bnd * ((n : ℝ) + 1) ^ (2 : ℝ) := by
    have he_le : ‖LSeries.term f 2 (n + 1)‖ ≤ Bnd :=
      hf2.norm.le_tsum (n + 1) (fun _ _ => norm_nonneg _)
    rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)] at he_le
    simp only [f, Complex.norm_real, Real.norm_eq_abs,
      show (2 : ℂ).re = (2 : ℝ) by norm_num, Nat.cast_succ] at he_le
    exact (div_le_iff₀ (by positivity : 0 < ((n : ℝ) + 1) ^ (2 : ℝ))).mp he_le
  let L₀ : ℂ → ℂ := LSeries (fun n => (ordinaryPrimeCountWeight n : ℂ))
  let E : ℂ → ℂ := LSeries (fun n => (e n : ℂ))
  have hH_eq {s : ℂ} (hs : 3 < s.re) : H s = D s * (L₀ s + E s) := by
    have hs1 : 1 < s.re := by linarith only [hs]
    dsimp only [H, D, L₀, E]
    rw [triangularDirichletContinuation_eq_series c hcoef (by linarith only [hs]) (by linarith only [hs]),
      ← (edited_jump_series he (q := q) hs1).2]
    have hsum := (edited_jump_series he (q := q) hs1).1.hasSum
    have hs' := (hasSum_nat_add_iff' 1).mpr hsum
    simp only [sum_range_one, LSeries.term_zero, sub_zero] at hs'
    refine (tsum_congr (g := fun n => LSeries.term f s (n + 1)) fun n => ?_).trans hs'.tsum_eq
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg, div_eq_mul_inv]
    simp [f]
  -- Logarithmic-derivative cancellation on `Re s > 1`: `-ζ'/ζ` cancels identically
  let R : ℂ → ℂ := fun z =>
    riemannZeta z - 1 - (z - 1)⁻¹ + _root_.RHTower.xiPrimeLogHigherValuation z - deriv (editRem e) z
  let Ψ : ℂ → ℂ := (deriv G / G) + R
  have hderiv_id {s : ℂ} (hs : 1 < s.re) : deriv (L₀ + E) s = Ψ s := by
    have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl 1 hs
    let xm : ℝ := (1 + s.re) / 2
    have hxm1 : 1 < xm := by dsimp only [xm]; linarith only [hs]
    have hxms : xm < s.re := by dsimp only [xm]; linarith only [hs]
    have hL₀_diff : DifferentiableAt ℂ L₀ s :=
      (LSeries_hasDerivAt ((ordinaryPrimeCountWeight_summable (s := (xm : ℂ))
        (by simpa using hxm1)).abscissaOfAbsConv_le.trans_lt (by exact_mod_cast hxms))).differentiableAt
    have hE_diff : DifferentiableAt ℂ E s :=
      (LSeries_hasDerivAt ((edit_LSeriesSummable he (s := (xm : ℂ))
        (by simpa using hxm1)).abscissaOfAbsConv_le.trans_lt (by exact_mod_cast hxms))).differentiableAt
    have hQ_diff : DifferentiableAt ℂ (editRem e) s :=
      ((differentiableOn_editRem he).differentiableAt (hU_half.mem_nhds (by linarith only [hs])))
    have hG_ev : G =ᶠ[𝓝 s] fun w => (w - 1) * (riemannZeta w * Complex.exp (E w + editRem e w)) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
      rw [hG_eq w hw, editSystem_zetaSeriesC he hw]
    have hprod_deriv : HasDerivAt
        (fun w => (w - 1) * (riemannZeta w * Complex.exp (E w + editRem e w)))
        (1 * (riemannZeta s * Complex.exp (E s + editRem e s)) +
          (s - 1) * (deriv riemannZeta s * Complex.exp (E s + editRem e s) +
            riemannZeta s * (Complex.exp (E s + editRem e s) *
              (deriv E s + deriv (editRem e) s)))) s := by
      have hd1 : HasDerivAt (fun w : ℂ => w - 1) 1 s := (hasDerivAt_id s).sub_const 1
      have hdζ : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
        (differentiableAt_riemannZeta hs_ne1).hasDerivAt
      have hdexp : HasDerivAt (fun w => Complex.exp (E w + editRem e w))
          (Complex.exp (E s + editRem e s) * (deriv E s + deriv (editRem e) s)) s :=
        (hE_diff.hasDerivAt.add hQ_diff.hasDerivAt).cexp
      exact hd1.mul (hdζ.mul hdexp)
    have hGs_eq : G s = (s - 1) * (riemannZeta s * Complex.exp (E s + editRem e s)) := by
      rw [hG_eq s hs, editSystem_zetaSeriesC he hs]
    have hdGs_eq : deriv G s =
        1 * (riemannZeta s * Complex.exp (E s + editRem e s)) +
          (s - 1) * (deriv riemannZeta s * Complex.exp (E s + editRem e s) +
            riemannZeta s * (Complex.exp (E s + editRem e s) *
              (deriv E s + deriv (editRem e) s))) :=
      (hG_ev.hasDerivAt_iff.mpr hprod_deriv).deriv
    have hs1_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne1
    have hζ_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    have hexp_ne : Complex.exp (E s + editRem e s) ≠ 0 := Complex.exp_ne_zero _
    have hlogG : deriv G s / G s =
        (s - 1)⁻¹ + deriv riemannZeta s / riemannZeta s + deriv E s + deriv (editRem e) s := by
      rw [hdGs_eq, hGs_eq]
      field_simp [hs1_ne, hζ_ne, hexp_ne]
      ring
    change deriv (fun z => L₀ z + E z) s = deriv G s / G s + R s
    rw [deriv_add hL₀_diff hE_diff, ordinaryPrimeCount_LSeries_deriv hs, hlogG]
    dsimp only [R]
    ring
  -- Analytic continuation of `deriv M = Ψ` across `U = {b < s.re}`
  have hG_an : AnalyticOnNhd ℂ G U := hG.analyticOnNhd hU
  have hQ_an : AnalyticOnNhd ℂ (editRem e) {s : ℂ | 1 / 2 < s.re} :=
    (differentiableOn_editRem he).analyticOnNhd hU_half
  have hval_an : AnalyticOnNhd ℂ _root_.RHTower.xiPrimeLogHigherValuation {s : ℂ | 1 / 2 < s.re} :=
    _root_.RHTower.differentiableOn_xiPrimeLogHigherValuation_halfPlane.analyticOnNhd hU_half
  have hΨ_mero : MeromorphicOn Ψ U := by
    intro z hz
    have hz_half : 1 / 2 < z.re := hb.trans_lt hz
    have hGG : MeromorphicAt (deriv G / G) z :=
      ((hG_an z hz).deriv.meromorphicAt).div (hG_an z hz).meromorphicAt
    have hRz : MeromorphicAt R z := by
      have hζ := _root_.RHTower.meromorphicAt_riemannZeta_everywhere z
      have h1 : MeromorphicAt (fun _ : ℂ => (1 : ℂ)) z := analyticAt_const.meromorphicAt
      have hinv : MeromorphicAt (fun w : ℂ => (w - 1)⁻¹) z :=
        ((analyticAt_id.sub analyticAt_const).meromorphicAt).inv
      have hv : MeromorphicAt _root_.RHTower.xiPrimeLogHigherValuation z :=
        (hval_an z hz_half).meromorphicAt
      have hQd : MeromorphicAt (deriv (editRem e)) z :=
        ((hQ_an z hz_half).deriv).meromorphicAt
      exact (((hζ.sub h1).sub hinv).add hv).sub hQd
    exact hGG.add hRz
  obtain ⟨x, hx3, hxD⟩ := exists_lastClassSymbol_euler_point hq
  have hx1 : 1 < x := (by norm_num : (1 : ℝ) < 3).trans hx3
  have hxU : (x : ℂ) ∈ U := by show b < (x : ℂ).re; simpa using hb1.trans hx1
  have hM_ev : M =ᶠ[𝓝 (x : ℂ)] (L₀ + E) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (x : ℂ) ∈ {s : ℂ | 3 < s.re} from hx3),
      hD.continuous.continuousAt.eventually_ne hxD] with s hs hd_ne
    change H s / D s = L₀ s + E s
    rw [hH_eq hs, mul_div_cancel_left₀ _ hd_ne]
  let F := deriv M - Ψ
  have hF_mero : MeromorphicOn F U := fun z hz => (hM z hz).deriv.sub (hΨ_mero z hz)
  have hF_top_x : meromorphicOrderAt F (x : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [nhdsWithin_le_nhds hM_ev.deriv,
      nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (x : ℂ) ∈ {s : ℂ | 1 < s.re} from hx1))] with s hs hs1
    exact sub_eq_zero.mpr (hs.trans (hderiv_id hs1))
  have hF_top_ρ : meromorphicOrderAt F ρ₀ = ⊤ := by
    by_contra hne
    exact (hF_mero.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt b).isPreconnected hρ hxU hne) hF_top_x
  have hM_Ψ : deriv M =ᶠ[𝓝[≠] ρ₀] Ψ :=
    (meromorphicOrderAt_eq_top_iff.mp hF_top_ρ).mono fun s hs => sub_eq_zero.mp hs
  -- Exclude `G ρ₀ = 0`: otherwise `deriv G / G` gives `deriv M` a simple pole at `ρ₀`
  intro hG0
  have h2U : (2 : ℂ) ∈ U := by show b < (2 : ℂ).re; norm_num; exact hb1.trans (by norm_num)
  have hG2_ne : G 2 ≠ 0 := by
    rw [hG_eq 2 (by norm_num), editSystem_zetaSeriesC he (by norm_num)]
    exact mul_ne_zero (by norm_num)
      (mul_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by norm_num)) (Complex.exp_ne_zero _))
  have hG_ord_ne_top : meromorphicOrderAt G ρ₀ ≠ ⊤ := by
    intro htop
    have h2_top : meromorphicOrderAt G 2 = ⊤ := by
      by_contra hne2
      exact (hG_an.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
        (convex_halfSpace_re_gt b).isPreconnected h2U hρ hne2) htop
    have h2_zero : meromorphicOrderAt G 2 = 0 :=
      meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero (hG_an 2 h2U) hG2_ne
    exact WithTop.zero_ne_top (h2_zero.symm.trans h2_top)
  have hG_ord_pos : 0 < meromorphicOrderAt G ρ₀ :=
    meromorphicOrderAt_pos_of_analyticAt_eq_zero (hG_an ρ₀ hρ) hG0
  lift meromorphicOrderAt G ρ₀ to ℤ using hG_ord_ne_top with m hm
  have hm_pos : 0 < m := by exact_mod_cast hG_ord_pos
  have hdG_ord : meromorphicOrderAt (deriv G) ρ₀ = ((m - 1 : ℤ) : WithTop ℤ) :=
    meromorphicOrderAt_deriv_eq_sub_one (show (m : ℂ) ≠ 0 by exact_mod_cast hm_pos.ne') hm.symm
  have hlogG_ord : meromorphicOrderAt (deriv G / G) ρ₀ = ((-1 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_div ((hG_an ρ₀ hρ).deriv.meromorphicAt) (hG_an ρ₀ hρ).meromorphicAt,
      hdG_ord, ← hm]
    exact_mod_cast (show (m - 1 : ℤ) - m = -1 by omega)
  have hρ_half : 1 / 2 < ρ₀.re := hb.trans_lt hρ
  have hR_an : AnalyticAt ℂ R ρ₀ :=
    ((((analyticAt_riemannZeta hρ1).sub analyticAt_const).sub
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hρ1))).add
      (hval_an ρ₀ hρ_half)).sub ((hQ_an ρ₀ hρ_half).deriv)
  have hΨ_ord : meromorphicOrderAt Ψ ρ₀ = ((-1 : ℤ) : WithTop ℤ) := by
    dsimp only [Ψ]
    rw [meromorphicOrderAt_add_eq_left_of_lt hR_an.meromorphicAt]
    · exact hlogG_ord
    · rw [hlogG_ord]
      exact lt_of_lt_of_le (by decide : ((-1 : ℤ) : WithTop ℤ) < 0) hR_an.meromorphicOrderAt_nonneg
  exact meromorphic_deriv_order_ne_neg_one (hM ρ₀ hρ)
    ((meromorphicOrderAt_congr hM_Ψ).trans hΨ_ord)

/-- Below any zero `ρ₀ ≠ 1` (`Re ρ₀ > b`, `1/2 ≤ b < 1`) of `G = (s - 1) ζ_B`, the edited
last-class first total exceeds `K X^{b + 1}` infinitely often for every modulus `q ≥ 2` and `K`. -/
theorem editedLastClassTotal_frequently_large_at_fake_zero {e : ℕ → ℤ} (he : IsEdit e)
    {q : ℕ} (hq : 2 ≤ q) {b : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1)
    {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {s : ℂ | b < s.re})
    (hG_eq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * (editSystem e).zetaSeriesC s)
    {ρ₀ : ℂ} (hρ : b < ρ₀.re) (hρ1 : ρ₀ ≠ 1) (hG0 : G ρ₀ = 0) (K : ℝ) :
    ∃ᶠ X : ℕ in atTop, K * (X : ℝ) ^ (b + 1) < |editedLastClassTotal e q X| := by
  by_contra h
  obtain ⟨T, hT⟩ := eventually_atTop.mp (Filter.not_frequently.mp h)
  let S := ∑ j ∈ range T, |editedLastClassTotal e q j|
  have hS : 0 ≤ S := sum_nonneg fun _ _ => abs_nonneg _
  refine editedLastClassTotal_bound_excludes_fake_zero he hq hb hb1 (C := |K| + S) ?_
    hG hG_eq hρ hρ1 hG0
  intro X hX
  have hpow : 1 ≤ (X : ℝ) ^ (b + 1) :=
    Real.one_le_rpow (by exact_mod_cast hX) (by linarith only [hb])
  rcases lt_or_ge X T with hsmall | hlarge
  · have hle : |editedLastClassTotal e q X| ≤ S :=
      single_le_sum (fun j _ => abs_nonneg _) (mem_range.mpr hsmall)
    exact (hle.trans (le_add_of_nonneg_left (abs_nonneg K))).trans
      (le_mul_of_one_le_right (add_nonneg (abs_nonneg K) hS) hpow)
  · exact (not_lt.mp (hT X hlarge)).trans (mul_le_mul_of_nonneg_right
      ((le_abs_self K).trans (le_add_of_nonneg_right hS)) (zero_le_one.trans hpow))

/-! ## 3. All-strip and sub-square-root prime-edit barriers -/

/-- All-strip selectivity barrier across `(1/2, 14/15)`: for every `σ ∈ (1/2, 14/15)` and
`β ∈ (σ, 1)`, there exists a two-sided prime edit `e` that is an integer-norm fake at `β` with
infinitely many strict fake zeros on `Re s = σ` (`ζ(ρ_j) ≠ 0`), whose last-class generator
first total exceeds `K X^{b + 1}` infinitely often for every `q ≥ 2`, `b ∈ [1/2, σ)`, and `K`. -/
theorem exists_isEdit_strict_line_carry_obstruction {σ β : ℝ}
    (hσ : 1 / 2 < σ) (hσ14 : σ < 14 / 15) (hσβ : σ < β) (hβ1 : β < 1) :
    ∃ (ρ : ℕ → ℂ) (e : ℕ → ℤ),
      IsEdit e ∧
      IsIntegerNormFakeAt (editSystem e) β ∧
      (∀ j, (ρ j).re = σ) ∧
      (∀ j, riemannZeta (ρ j) ≠ 0) ∧
      (Set.range ρ).Infinite ∧
      ∀ (q : ℕ), 2 ≤ q → ∀ (b : ℝ), 1 / 2 ≤ b → b < σ → ∀ (K : ℝ),
        ∃ᶠ X : ℕ in atTop, K * (X : ℝ) ^ (b + 1) < |editedLastClassTotal e q X| := by
  let g := min (14 / 15 - σ) (β - σ)
  have hg : 0 < g := lt_min (by linarith) (by linarith)
  let A : ℝ := 1 / g
  have hA : 0 < A := one_div_pos.mpr hg
  have hhalf_step : 1 / (2 * A) = g / 2 := by dsimp only [A]; field_simp
  have hroom : σ + 1 / (2 * A) < 14 / 15 := by
    rw [hhalf_step]
    have : g ≤ 14 / 15 - σ := min_le_left _ _
    linarith
  have hβ_room : σ + 1 / (2 * A) < β := by
    rw [hhalf_step]
    have : g ≤ β - σ := min_le_right _ _
    linarith
  obtain ⟨ρ, e, hre, hζ, hinf, he, hfake, hset⟩ :=
    exists_isEdit_fake_with_strict_zeros_on_a_line hσ hA hroom hβ_room hβ1
  refine ⟨ρ, e, he, hfake, hre, hζ, hinf, fun q hq b hb hbσ K => ?_⟩
  obtain ⟨G, hG_diff, hG_eq, hG_zeros⟩ := hset
  have hρ0_re : b < (ρ 0).re := by rw [hre 0]; exact hbσ
  have hρ0_ne1 : ρ 0 ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    rw [hre 0, Complex.one_re] at this
    linarith
  have hG0 : G (ρ 0) = 0 :=
    (hG_zeros (ρ 0) (by rw [hre 0]; exact hσ) hρ0_ne1 (hζ 0)).mpr ⟨0, Or.inl rfl⟩
  exact editedLastClassTotal_frequently_large_at_fake_zero he hq hb (hbσ.trans (by linarith))
    (hG_diff.mono fun z hz => hb.trans_lt hz) hG_eq hρ0_re hρ0_ne1 hG0 K

/-- Sub-square-root count barrier across `(1/2, 27001 / 48000)`: unconditionally, there exists a
two-sided prime edit `e` with norm-count remainder exponent `c < 1/2` — so its dyadic norm-count
first total `∑_{k < X} |2 N_B(⌊k/2⌋) - N_B(2⌊k/2⌋)|` is `O(X^{c_0 + 1})` with `c_0 + 1 < 3/2` —
whose distinct-generator carry first total still exceeds `K X^{b + 1}` infinitely often for every
`q ≥ 2`, `b ∈ [1/2, β)`, and `K`. -/
theorem exists_sub_sqrt_count_edit_with_carry_obstruction {β : ℝ}
    (hβ : 1 / 2 < β) (hβ_hi : β < 27001 / 48000) :
    ∃ (e : ℕ → ℤ) (c₀ Cdyad : ℝ),
      IsEdit e ∧
      0 ≤ c₀ ∧ c₀ < 1 / 2 ∧ 0 ≤ Cdyad ∧
      IsIntegerNormFakeAt (editSystem e) c₀ ∧
      (∀ X : ℕ, 1 ≤ X →
        (∑ k ∈ range X,
          |2 * ((editSystem e).countBall (k / 2 : ℕ) : ℝ) -
            ((editSystem e).countBall ((2 * (k / 2) : ℕ)) : ℝ)|) ≤
          Cdyad * (X : ℝ) ^ (c₀ + 1)) ∧
      (∀ (q : ℕ), 2 ≤ q → ∀ (b : ℝ), 1 / 2 ≤ b → b < β → ∀ (K : ℝ),
        ∃ᶠ X : ℕ in atTop, K * (X : ℝ) ^ (b + 1) < |editedLastClassTotal e q X|) := by
  have hβ23 : β < 2 / 3 := by linarith
  have hΘ : _root_.RHTower.zetaZeroAbscissa ≤ 20999 / 24000 :=
    GaloisForLFunctions.ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths
  have hΘβ : _root_.RHTower.zetaZeroAbscissa + 2 * β < 2 := by linarith
  obtain ⟨γ, _, _, hζ_seg⟩ := exists_riemannZeta_ne_zero_on_segment
    (show β ≠ 1 by linarith) (by norm_num : (1 : ℝ) < 2)
  have hpt : zeroPt β γ = (⟨β, γ⟩ : ℂ) := by
    apply Complex.ext <;> simp [zeroPt]
  have hζ : riemannZeta (zeroPt β γ) ≠ 0 := by rwa [hpt]
  obtain ⟨α, k₀, c, hc_half, hfake, hG_eq, σ₁, hσ₁_half, hG_diff, hG_zeros⟩ :=
    exists_isIntegerNormFakeAt_sEdit_lt_half hβ hβ23 hΘβ hζ
  let e := sEdit α β γ k₀
  have he : IsEdit e := isEdit_sEdit α β γ k₀
  let c₀ : ℝ := max c 0
  have hc₀_nonneg : 0 ≤ c₀ := le_max_right c 0
  have hc₀_lt : c₀ < 1 / 2 := max_lt hc_half (by norm_num)
  have hfake₀ : IsIntegerNormFakeAt (editSystem e) c₀ := hfake.mono (le_max_left c 0)
  obtain ⟨_, _, _, ⟨A, Ccnt, _, hcnt⟩, _⟩ := hfake₀
  let C₀ : ℝ := |((editSystem e).countBall 0 : ℝ)|
  let Cterm : ℝ := C₀ + (2 + (2 : ℝ) ^ c₀) * |Ccnt|
  have hCterm0 : 0 ≤ Cterm := by dsimp only [Cterm, C₀]; positivity
  refine ⟨e, c₀, Cterm, he, hc₀_nonneg, hc₀_lt, hCterm0, hfake₀, ?_, ?_⟩
  · intro X hX
    have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hk_le (k : ℕ) (hk : k ∈ range X) :
        |2 * ((editSystem e).countBall (k / 2 : ℕ) : ℝ) -
            ((editSystem e).countBall ((2 * (k / 2) : ℕ)) : ℝ)| ≤
          Cterm * (X : ℝ) ^ c₀ := by
      let n := k / 2
      rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
      · change |2 * ((editSystem e).countBall n : ℝ) -
          ((editSystem e).countBall (2 * n : ℕ) : ℝ)| ≤ _
        rw [hn0, Nat.mul_zero, Nat.cast_zero]
        have h1 : |2 * ((editSystem e).countBall 0 : ℝ) - ((editSystem e).countBall 0 : ℝ)| = C₀ := by
          dsimp only [C₀]; ring_nf
        have hpow1 : 1 ≤ (X : ℝ) ^ c₀ := Real.one_le_rpow hX1 hc₀_nonneg
        have hC₀_le : C₀ ≤ Cterm := by dsimp only [Cterm]; positivity
        exact (h1.le.trans hC₀_le).trans (le_mul_of_one_le_right hCterm0 hpow1)
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn_pos
        have h2n1 : (1 : ℝ) ≤ (2 * n : ℕ) := by exact_mod_cast (show 1 ≤ 2 * n by omega)
        have hnX : (n : ℝ) ≤ X := by
          have hkX := (mem_range.mp hk).le
          have : n ≤ k := Nat.div_le_self k 2
          exact_mod_cast (this.trans hkX)
        have hb1 := (hcnt n hn1).trans (mul_le_mul_of_nonneg_right (le_abs_self Ccnt) (by positivity))
        have hb2 := (hcnt (2 * n : ℕ) h2n1).trans
          (mul_le_mul_of_nonneg_right (le_abs_self Ccnt) (by positivity))
        have hlin : 2 * ((editSystem e).countBall n : ℝ) -
            ((editSystem e).countBall (2 * n : ℕ) : ℝ) =
            2 * (((editSystem e).countBall n : ℝ) - A * n) -
              (((editSystem e).countBall (2 * n : ℕ) : ℝ) - A * (2 * n : ℕ)) := by
          push_cast
          ring
        have hpow_n : (n : ℝ) ^ c₀ ≤ (X : ℝ) ^ c₀ :=
          Real.rpow_le_rpow (Nat.cast_nonneg n) hnX hc₀_nonneg
        have hpow_2n : ((2 * n : ℕ) : ℝ) ^ c₀ ≤ (2 : ℝ) ^ c₀ * (X : ℝ) ^ c₀ := by
          rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)]
          exact mul_le_mul_of_nonneg_left hpow_n (by positivity)
        change |2 * ((editSystem e).countBall n : ℝ) -
          ((editSystem e).countBall (2 * n : ℕ) : ℝ)| ≤ _
        rw [hlin]
        have htri : |2 * (((editSystem e).countBall n : ℝ) - A * n) -
              (((editSystem e).countBall (2 * n : ℕ) : ℝ) - A * (2 * n : ℕ))| ≤
            2 * |((editSystem e).countBall n : ℝ) - A * n| +
              |((editSystem e).countBall (2 * n : ℕ) : ℝ) - A * (2 * n : ℕ)| := by
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        calc
          |2 * (((editSystem e).countBall n : ℝ) - A * n) -
              (((editSystem e).countBall (2 * n : ℕ) : ℝ) - A * (2 * n : ℕ))|
              ≤ 2 * (|Ccnt| * (n : ℝ) ^ c₀) + |Ccnt| * ((2 * n : ℕ) : ℝ) ^ c₀ :=
            htri.trans (add_le_add (mul_le_mul_of_nonneg_left hb1 (by norm_num)) hb2)
          _ ≤ 2 * (|Ccnt| * (X : ℝ) ^ c₀) + |Ccnt| * ((2 : ℝ) ^ c₀ * (X : ℝ) ^ c₀) :=
            add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow_n (abs_nonneg _))
              (by norm_num)) (mul_le_mul_of_nonneg_left hpow_2n (abs_nonneg _))
          _ = ((2 + (2 : ℝ) ^ c₀) * |Ccnt|) * (X : ℝ) ^ c₀ := by ring
          _ ≤ Cterm * (X : ℝ) ^ c₀ := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            dsimp only [Cterm]
            linarith [abs_nonneg ((editSystem e).countBall 0 : ℝ)]
    calc
      (∑ k ∈ range X,
          |2 * ((editSystem e).countBall (k / 2 : ℕ) : ℝ) -
            ((editSystem e).countBall ((2 * (k / 2) : ℕ)) : ℝ)|)
          ≤ ∑ _k ∈ range X, Cterm * (X : ℝ) ^ c₀ :=
        (sum_le_sum hk_le)
      _ = Cterm * ((X : ℝ) ^ c₀ * (X : ℝ)) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring
      _ = Cterm * (X : ℝ) ^ (c₀ + 1) := by
        rw [Real.rpow_add_one hX0.ne']
  · intro q hq b hb hbβ K
    have hρ_re : (zeroPt β γ).re = β := by simp [zeroPt]
    have hρ_gt_b : b < (zeroPt β γ).re := by rw [hρ_re]; exact hbβ
    have hρ_ne1 : zeroPt β γ ≠ 1 := by
      intro h1
      have := congrArg Complex.re h1
      rw [hρ_re, Complex.one_re] at this
      linarith
    have hG0 : editG α β γ k₀ (zeroPt β γ) = 0 :=
      (hG_zeros (zeroPt β γ) (by rw [hρ_re]; linarith) ).mpr (Or.inr (Or.inl rfl))
    exact editedLastClassTotal_frequently_large_at_fake_zero he hq hb (hbβ.trans (by linarith))
      (hG_diff.mono fun z hz => hσ₁_half.trans (hb.trans_lt hz)) hG_eq hρ_gt_b hρ_ne1 hG0 K

/-! ## 4. Unconditional `O(X^{15/8})` corollaries for actual primes -/

/-- Unconditionally, for every `β ∈ (20999 / 24000, 1)`, `|ordinaryLastClassTotal q X| ≤ C X^{1 + β}`
uniformly across all moduli `q ≥ 2` and `X ≥ 1`. -/
theorem exists_ordinaryLastClassTotal_sub_seven_eighths {β : ℝ}
    (hβ : (20999 / 24000 : ℝ) < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q X : ℕ, 2 ≤ q → 1 ≤ X →
      |ordinaryLastClassTotal q X| ≤ C * (X : ℝ) ^ (1 + β) := by
  have hΘ : _root_.RHTower.zeroReSup < β := by
    refine (_root_.RHTower.zeroReSup_le_of_forall_re_le fun z => ?_).trans_lt hβ
    by_contra hgt
    exact GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re
      (not_le.mp hgt) (_root_.RHTower.riemannZeta_eq_zero_of_xiZeroCopy z)
  obtain ⟨K, hK, hp⟩ := ordinary_prefix_power hΘ
  have hβ0 : 0 < β := by linarith
  refine ⟨K / β, by positivity, fun q X hq hX => ?_⟩
  let A := fun n : ℕ => if q ∣ n + 1 then (1 : ℝ) else 0
  have hn : ¬ q ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
  have h0 : A 0 = 0 := by simp [A, hn]
  have he (k : ℕ) (hk : k ∈ range X) :
      quotientClassMassOf ordinaryPrimeCountWeight q k =
        ∑ m ∈ Icc 1 X, ordinaryPrimeCountWeight m * A (k / m) := by
    apply sum_subset (Icc_subset_Icc_right (mem_range.mp hk).le)
    intro m hm hm'
    have hm0 := (mem_Icc.mp hm).1
    have hkm : k < m := by by_contra! hg; exact hm' (mem_Icc.mpr ⟨hm0, hg⟩)
    simp [Nat.div_eq_of_lt hkm, hn]
  have ht : ordinaryLastClassTotal q X =
      ∑ m ∈ Icc 1 X, ordinaryPrimeCountWeight m * discreteQuotientMean A m X := by
    rw [ordinaryLastClassTotal, sum_congr rfl he, sum_comm]
    simp only [discreteQuotientMean, mul_sum]
  rw [ht]
  apply (abs_discreteQuotientMean_weighted _ A h0 (fun n => by dsimp only [A]; split <;> norm_num) X).trans
  have hxR : 0 < (X : ℝ) := by exact_mod_cast hX
  rw [add_comm (1 : ℝ) β, Real.rpow_add_one hxR.ne']
  calc
    _ ≤ X * ∑ n ∈ Icc 1 X, K * (n : ℝ) ^ (β - 1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X)
      refine sum_le_sum fun n hn_mem => ?_
      have h1 := (mem_Icc.mp hn_mem).1
      have hnR : 0 < (n : ℝ) := by exact_mod_cast h1
      rw [Real.rpow_sub_one hnR.ne', ← mul_div_assoc]
      exact (div_le_div_of_nonneg_left (abs_nonneg _) hnR (by linarith : (n : ℝ) ≤ n + 1)).trans
        (div_le_div_of_nonneg_right (hp n h1) hnR.le)
    _ ≤ _ := by
      rw [← mul_sum, ← Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_comm (1 : ℝ)]
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (_root_.HTGeometry.sum_rpow_sub_one_le hβ0 hβ1 X) hK) hxR.le).trans_eq (by ring)

/-- Unconditional sub-`7/8` bound for `binomialDistinctPrimeTotal j X` (`j ≥ 0`) and
`smoothDyadicFirstTotal X`: for every `β ∈ (20999 / 24000, 1)`, both are `O(X^{1 + β})`. -/
theorem exists_binomialDistinctPrime_and_smooth_sub_seven_eighths {β : ℝ}
    (hβ : (20999 / 24000 : ℝ) < β) (hβ1 : β < 1) :
    (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      |binomialDistinctPrimeTotal j X| ≤ C * (X : ℝ) ^ (1 + β)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      |smoothDyadicFirstTotal X| ≤ C * (X : ℝ) ^ (1 + β)) := by
  obtain ⟨C₀, hC₀, hord⟩ := exists_ordinaryLastClassTotal_sub_seven_eighths hβ hβ1
  have hb_half : 1 / 2 ≤ β := by linarith
  have hbin : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      |binomialDistinctPrimeTotal j X| ≤ C * (X : ℝ) ^ (1 + β) := by
    intro j
    obtain ⟨K, hK, herr⟩ := binomialDistinctPrimeTotal_error j hb_half
    have hq : 2 ≤ 2 ^ (j + 1) := by have := Nat.lt_two_pow_self (n := j + 1); omega
    refine ⟨K + C₀, add_nonneg hK hC₀, fun X hX => ?_⟩
    have htri := abs_sub_le (binomialDistinctPrimeTotal j X)
      (ordinaryLastClassTotal (2 ^ (j + 1)) X) 0
    simp only [sub_zero] at htri
    have h1 := herr X hX
    rw [add_comm β 1] at h1
    exact (htri.trans (add_le_add h1 (hord _ X hq hX))).trans_eq (add_mul ..).symm
  refine ⟨hbin, ?_⟩
  obtain ⟨Cb, hCb, hbin0⟩ := hbin 0
  refine ⟨1 + Cb, by positivity, fun X hX => ?_⟩
  obtain ⟨hl, hu⟩ := centralBinom_smooth_first_total_error X
  have hcount : Nat.primeCounting X.sqrt ≤ X.sqrt := by
    rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_one]
    exact (card_filter_le ..).trans (by simp)
  have hr : (X.sqrt : ℝ) ≤ (X : ℝ) ^ β := by
    apply Real.nat_sqrt_le_real_sqrt.trans
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX) hb_half
  have hdiff : |binomialDistinctPrimeTotal 0 X - smoothDyadicFirstTotal X| ≤
      (X : ℝ) ^ (1 + β) := by
    rw [abs_of_nonneg hl, add_comm (1 : ℝ) β, Real.rpow_add_one (by positivity),
      mul_comm ((X : ℝ) ^ β)]
    exact hu.trans (mul_le_mul_of_nonneg_left
      ((show (Nat.primeCounting X.sqrt : ℝ) ≤ X.sqrt by exact_mod_cast hcount).trans hr)
      (Nat.cast_nonneg _))
  have htri := abs_sub_le (smoothDyadicFirstTotal X) (binomialDistinctPrimeTotal 0 X) 0
  simp only [sub_zero] at htri
  rw [abs_sub_comm] at htri
  exact (htri.trans (add_le_add hdiff (hbin0 X hX))).trans_eq (by ring)

/-- Exact exponent `15 / 8` unconditional bounds (no `+ ε` loss) for `ordinaryLastClassTotal`,
`binomialDistinctPrimeTotal j`, the central binomial distinct-prime first total, and
`smoothDyadicFirstTotal`. -/
theorem exists_binomialDistinctPrime_and_smooth_fifteen_eighths_exact :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ q X : ℕ, 2 ≤ q → 1 ≤ X →
      |ordinaryLastClassTotal q X| ≤ C * (X : ℝ) ^ (15 / 8 : ℝ)) ∧
    (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      |binomialDistinctPrimeTotal j X| ≤ C * (X : ℝ) ^ (15 / 8 : ℝ)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      |∑ k ∈ range X, (((Nat.centralBinom (k / 2)).primeFactors.card : ℝ) -
        quotientClassMassOf (fun m => (Real.log m)⁻¹) 2 k)| ≤ C * (X : ℝ) ^ (15 / 8 : ℝ)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      |smoothDyadicFirstTotal X| ≤ C * (X : ℝ) ^ (15 / 8 : ℝ)) := by
  have h158 : (1 : ℝ) + (7 / 8 : ℝ) = (15 / 8 : ℝ) := by norm_num
  obtain ⟨C₀, hC₀, hord⟩ := exists_ordinaryLastClassTotal_sub_seven_eighths
    (β := 7 / 8) (by norm_num) (by norm_num)
  obtain ⟨hbin, hsm⟩ := exists_binomialDistinctPrime_and_smooth_sub_seven_eighths
    (β := 7 / 8) (by norm_num) (by norm_num)
  refine ⟨⟨C₀, hC₀, fun q X hq hX => by simpa only [h158] using hord q X hq hX⟩,
    fun j => ?_, ?_, ?_⟩
  · obtain ⟨Cj, hCj, hj⟩ := hbin j
    exact ⟨Cj, hCj, fun X hX => by simpa only [h158] using hj X hX⟩
  · obtain ⟨C0, hC0, h0⟩ := hbin 0
    refine ⟨C0, hC0, fun X hX => ?_⟩
    simpa only [binomialDistinctPrimeTotal, dyadicBinomialGcd, Nat.zero_add, pow_one, h158]
      using h0 X hX
  · obtain ⟨Cs, hCs, hs⟩ := hsm
    exact ⟨Cs, hCs, fun X hX => by simpa only [h158] using hs X hX⟩

#print axioms editedLastClassTotal_bound_excludes_fake_zero
#print axioms editedLastClassTotal_frequently_large_at_fake_zero
#print axioms exists_isEdit_strict_line_carry_obstruction
#print axioms exists_sub_sqrt_count_edit_with_carry_obstruction
#print axioms exists_binomialDistinctPrime_and_smooth_fifteen_eighths_exact

end GaloisForLFunctions.ExceptionalLayerTheory