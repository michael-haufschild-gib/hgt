import GaloisForLFunctions.RHTower.XiHeatCassiniWoldZetaPoleCarrier
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# Critical-boundary continuation of the higher-valuation prime-log tail

The valuation-`>= 2` tail is not absolutely convergent on `Re s = 1/2`, but only its
valuation-two row reaches that wall.  Splitting that row and reassembling it through the full
von Mangoldt current gives

`H(s) = A(2s) - H(2s) + H_{>=3}(s)`

on `Re s > 1/2`, where `A = -zeta'/zeta`.  The right side is holomorphic through every nonreal
point of the critical line.  Thus the prime-square wall is a single real polar obstruction; it
cannot hide a nontrivial critical-line zeta pole.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Prime-log tail restricted to valuation at least three. -/
def xiPrimeLogHigherValuationThreePlus (s : ℂ) : ℂ :=
  ∑' pk : Nat.Primes × ℕ,
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      s ((pk.1 : ℕ) ^ (pk.2 + 3))

/-- Positive absolute-convergence weight for the valuation-`>= 3` tail. -/
def xiPrimeLogHigherValuationThreePlusWeight
    (sigma : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  Real.log (pk.1 : ℝ) *
    ((pk.1 : ℝ)⁻¹) ^ (((pk.2 + 3 : ℕ) : ℝ) * sigma)

theorem summable_xiPrimeLogHigherValuationThreePlusWeight
    {sigma : ℝ} (hsigma : 1 / 3 < sigma) :
    Summable (xiPrimeLogHigherValuationThreePlusWeight sigma) := by
  have h := summable_primeLog_mul_inv_rpow_mul_add sigma (3 * sigma)
    (by linarith) (by linarith)
  apply h.congr
  rintro ⟨p, k⟩
  rw [xiPrimeLogHigherValuationThreePlusWeight]
  congr 2
  push_cast
  ring

theorem norm_vonMangoldtLSeriesTerm_primePower_eq_threePlusWeight
    (s : ℂ) (pk : Nat.Primes × ℕ) :
    ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      s ((pk.1 : ℕ) ^ (pk.2 + 3))‖ =
      xiPrimeLogHigherValuationThreePlusWeight s.re pk := by
  have hpPow : 0 < (pk.1 : ℕ) ^ (pk.2 + 3) := pow_pos pk.1.prop.pos _
  have hpR : (1 : ℝ) < (pk.1 : ℝ) := by exact_mod_cast pk.1.prop.one_lt
  rw [LSeries.norm_term_eq, if_neg hpPow.ne',
    ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime pk.1.prop]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos hpR)]
  rw [xiPrimeLogHigherValuationThreePlusWeight, Nat.cast_pow,
    div_eq_mul_inv,
    ← Real.rpow_neg (by positivity : 0 ≤ ((pk.1 : ℝ) ^ (pk.2 + 3)))]
  congr 1
  rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (pk.1 : ℝ))]
  rw [Real.inv_rpow (by positivity : 0 ≤ (pk.1 : ℝ)),
    ← Real.rpow_neg (by positivity : 0 ≤ (pk.1 : ℝ))]
  congr 1
  ring

theorem summable_xiPrimeLogHigherValuationThreePlus_term
    {s : ℂ} (hs : 1 / 3 < s.re) :
    Summable (fun pk : Nat.Primes × ℕ =>
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        s ((pk.1 : ℕ) ^ (pk.2 + 3))) := by
  apply summable_norm_iff.mp
  exact (summable_xiPrimeLogHigherValuationThreePlusWeight hs).congr
    (fun pk => (norm_vonMangoldtLSeriesTerm_primePower_eq_threePlusWeight s pk).symm)

/-- Only valuation two lies between the half and third walls. -/
theorem xiPrimeLogHigherValuation_eq_two_add_threePlus
    {s : ℂ} (hs : 1 / 2 < s.re) :
    xiPrimeLogHigherValuation s =
      xiPrimeLogDirichlet (2 * s) + xiPrimeLogHigherValuationThreePlus s := by
  let f : Nat.Primes × ℕ → ℂ := fun pk =>
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      s ((pk.1 : ℕ) ^ (pk.2 + 2))
  have hfull : Summable f := by
    simpa only [f] using summable_xiPrimeLogHigherValuation_term_of_half_lt_re hs
  have htail : Summable (fun pk : Nat.Primes × ℕ =>
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        s ((pk.1 : ℕ) ^ (pk.2 + 3))) :=
    summable_xiPrimeLogHigherValuationThreePlus_term (by linarith)
  have hhead : Summable (fun p : Nat.Primes =>
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        s ((p : ℕ) ^ 2)) := by
    have hcomp := hfull.comp_injective
      (i := fun p : Nat.Primes => (p, 0)) (fun _ _ h => congrArg Prod.fst h)
    simpa only [Function.comp_apply, f, zero_add] using! hcomp
  have htailOuter : Summable (fun p : Nat.Primes =>
      ∑' k : ℕ,
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          s ((p : ℕ) ^ (k + 3))) := htail.prod
  have hinner (p : Nat.Primes) :
      (∑' k : ℕ,
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          s ((p : ℕ) ^ (k + 2))) =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          s ((p : ℕ) ^ 2) +
        ∑' k : ℕ,
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            s ((p : ℕ) ^ (k + 3)) := by
    have hp : Summable (fun k : ℕ => f (p, k)) := by
      exact hfull.comp_injective
        (i := fun k : ℕ => (p, k)) (fun _ _ h => congrArg Prod.snd h)
    simpa only [f, zero_add, add_assoc] using hp.tsum_eq_zero_add
  change (∑' pk : Nat.Primes × ℕ, f pk) =
    xiPrimeLogDirichlet (2 * s) +
      ∑' pk : Nat.Primes × ℕ,
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          s ((pk.1 : ℕ) ^ (pk.2 + 3))
  calc
    (∑' pk : Nat.Primes × ℕ, f pk) =
        ∑' p : Nat.Primes, ∑' k : ℕ,
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            s ((p : ℕ) ^ (k + 2)) := by
      simpa only [f] using hfull.tsum_prod
    _ = ∑' p : Nat.Primes,
        (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            s ((p : ℕ) ^ 2) +
          ∑' k : ℕ,
            LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              s ((p : ℕ) ^ (k + 3))) := tsum_congr hinner
    _ = (∑' p : Nat.Primes,
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            s ((p : ℕ) ^ 2)) +
        ∑' p : Nat.Primes, ∑' k : ℕ,
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            s ((p : ℕ) ^ (k + 3)) := hhead.tsum_add htailOuter
    _ = xiPrimeLogDirichlet (2 * s) +
        ∑' pk : Nat.Primes × ℕ,
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            s ((pk.1 : ℕ) ^ (pk.2 + 3)) := by
      congr 1
      · unfold xiPrimeLogDirichlet
        apply tsum_congr
        intro p
        congr 2
        ring
      · rw [← htail.tsum_prod]

/-- Boundary model obtained by reassembling the valuation-two row through `-zeta'/zeta`. -/
def xiPrimeLogHigherValuationCriticalContinuation (s : ℂ) : ℂ :=
  infinitePrimeFlux (2 * s) - xiPrimeLogHigherValuation (2 * s) +
    xiPrimeLogHigherValuationThreePlus s

/-- The critical-boundary model agrees with the original tail on its absolute half-plane. -/
theorem xiPrimeLogHigherValuationCriticalContinuation_eq
    {s : ℂ} (hs : 1 / 2 < s.re) :
    xiPrimeLogHigherValuationCriticalContinuation s =
      xiPrimeLogHigherValuation s := by
  have htwo : 1 < (2 * s).re := by simp; linarith
  have hflux := infinitePrimeFlux_eq_primeLog_add_higherValuation htwo
  have hsplit := xiPrimeLogHigherValuation_eq_two_add_threePlus hs
  rw [xiPrimeLogHigherValuationCriticalContinuation, hflux]
  linear_combination hsplit.symm

/-- The valuation-`>=3` tail is holomorphic on `Re s > 1/3`. -/
theorem differentiableAt_xiPrimeLogHigherValuationThreePlus
    {s : ℂ} (hs : 1 / 3 < s.re) :
    DifferentiableAt ℂ xiPrimeLogHigherValuationThreePlus s := by
  let c : ℝ := (s.re + 1 / 3) / 2
  let U : Set ℂ := {z : ℂ | c < z.re}
  have hc : 1 / 3 < c := by dsimp only [c]; linarith
  have hcs : c < s.re := by dsimp only [c]; linarith
  have hU : IsOpen U :=
    isOpen_lt (continuous_const : Continuous fun _ : ℂ => c) Complex.continuous_re
  have hsU : s ∈ U := by simpa only [U, Set.mem_setOf_eq] using hcs
  have hmajor := summable_xiPrimeLogHigherValuationThreePlusWeight hc
  have hterm : ∀ pk : Nat.Primes × ℕ,
      DifferentiableOn ℂ (fun z : ℂ =>
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          z ((pk.1 : ℕ) ^ (pk.2 + 3))) U := by
    intro pk
    have hn0 : (pk.1 : ℕ) ^ (pk.2 + 3) ≠ 0 :=
      (pow_pos pk.1.prop.pos _).ne'
    have heq : (fun z : ℂ =>
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          z ((pk.1 : ℕ) ^ (pk.2 + 3))) =
        fun z : ℂ =>
          (ArithmeticFunction.vonMangoldt ((pk.1 : ℕ) ^ (pk.2 + 3)) : ℂ) /
            ((((pk.1 : ℕ) ^ (pk.2 + 3) : ℕ) : ℂ) ^ z) := by
      funext z
      rw [LSeries.term_of_ne_zero hn0]
    rw [heq]
    intro z _
    have hn0C : ((((pk.1 : ℕ) ^ (pk.2 + 3) : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast hn0
    have hpow : DifferentiableAt ℂ
        (fun w : ℂ => ((((pk.1 : ℕ) ^ (pk.2 + 3) : ℕ) : ℂ) ^ w)) z :=
      differentiableAt_id.const_cpow (Or.inl hn0C)
    have hden : ((((pk.1 : ℕ) ^ (pk.2 + 3) : ℕ) : ℂ) ^ z) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hn0C)
    exact ((differentiableAt_const
      (c := (ArithmeticFunction.vonMangoldt ((pk.1 : ℕ) ^ (pk.2 + 3)) : ℂ))).div
        hpow hden).differentiableWithinAt
  have hbound : ∀ (pk : Nat.Primes × ℕ) (z : ℂ), z ∈ U →
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          z ((pk.1 : ℕ) ^ (pk.2 + 3))‖ ≤
        xiPrimeLogHigherValuationThreePlusWeight c pk := by
    intro pk z hz
    have hcz : c ≤ z.re := by simpa only [U, Set.mem_setOf_eq] using hz.le
    calc
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          z ((pk.1 : ℕ) ^ (pk.2 + 3))‖ ≤
          ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (c : ℂ) ((pk.1 : ℕ) ^ (pk.2 + 3))‖ :=
        LSeries.norm_term_le_of_re_le_re _ (by simpa using hcz) _
      _ = xiPrimeLogHigherValuationThreePlusWeight c pk :=
        norm_vonMangoldtLSeriesTerm_primePower_eq_threePlusWeight (c : ℂ) pk
  have hdiff := Complex.differentiableOn_tsum_of_summable_norm
    hmajor hterm hU hbound
  change DifferentiableAt ℂ
    (fun z : ℂ => ∑' pk : Nat.Primes × ℕ,
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        z ((pk.1 : ℕ) ^ (pk.2 + 3))) s
  exact hdiff.differentiableAt (hU.mem_nhds hsU)

/-- Away from the real pole `s=1/2` and doubled zeta zeros, the boundary model is holomorphic. -/
theorem differentiableAt_xiPrimeLogHigherValuationCriticalContinuation
    {s : ℂ} (hthird : 1 / 3 < s.re)
    (htwoOne : 2 * s ≠ 1) (htwoZero : riemannZeta (2 * s) ≠ 0) :
    DifferentiableAt ℂ xiPrimeLogHigherValuationCriticalContinuation s := by
  have hflux : DifferentiableAt ℂ (fun z : ℂ => infinitePrimeFlux (2 * z)) s := by
    have hinner : DifferentiableAt ℂ (fun z : ℂ => 2 * z) s := by fun_prop
    have hcomp :=
      (differentiableAt_neg_logDeriv_riemannZeta htwoOne htwoZero).comp s hinner
    simpa only [infinitePrimeFlux, logDeriv_apply, Function.comp_apply, neg_div] using! hcomp
  have hhigh : DifferentiableAt ℂ (fun z : ℂ => xiPrimeLogHigherValuation (2 * z)) s := by
    have hre : 1 / 2 < (2 * s).re := by simp; linarith
    exact (differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re hre).comp s (by fun_prop)
  exact (hflux.sub hhigh).add
    (differentiableAt_xiPrimeLogHigherValuationThreePlus hthird)

/-- A nontrivial critical-line zero cannot coincide with the sole real prime-square wall. -/
theorem xiPrimeLogHigherValuationCriticalContinuation_differentiableAt_zeta_zero
    {rho : ℂ} (hhalf : rho.re = 1 / 2) (hzeta : riemannZeta rho = 0) :
    DifferentiableAt ℂ xiPrimeLogHigherValuationCriticalContinuation rho := by
  have him : rho.im ≠ 0 := by
    intro him0
    have hrho : rho = (rho.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him0
    rw [hrho, hhalf] at hzeta
    exact riemannZeta_ne_zero_of_ofReal_mem_Ioo (by norm_num) (by norm_num) hzeta
  have htwoOne : 2 * rho ≠ 1 := by
    intro h
    have himEq := congrArg Complex.im h
    have : 2 * rho.im = 0 := by simpa using himEq
    exact him (by linarith)
  have htwoZero : riemannZeta (2 * rho) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simp [hhalf]
  exact differentiableAt_xiPrimeLogHigherValuationCriticalContinuation
    (by rw [hhalf]; norm_num) htwoOne htwoZero

end

end RHTower
