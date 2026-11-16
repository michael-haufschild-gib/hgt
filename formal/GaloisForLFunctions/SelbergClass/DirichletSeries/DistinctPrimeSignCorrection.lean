import GaloisForLFunctions.BezoutValuationIncidence.SingularSeries.TwinPrimeConstant
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The odd-prime correction to the distinct-prime sign series

The local factor `(1 - 2p⁻ˢ)/(1 - p⁻ˢ)²` differs from one by
`-(p⁻ˢ/(1 - p⁻ˢ))²`. These quadratic deficits give locally uniform
convergence on `Re s > 1/2`, including points where a local factor vanishes.
At one, the product is the twin-prime constant.
-/

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.SelbergClass

/-- Entire prime-decay function, written without a branch-dependent logarithm. -/
def distinctPrimeDecay (p : Nat.Primes) (s : ℂ) : ℂ :=
  Complex.exp (-(s * (Real.log (p : ℕ) : ℂ)))

/-- The quadratic Euler correction, with the prime two removed. -/
def oddPrimeCorrectionFactor (p : Nat.Primes) (s : ℂ) : ℂ :=
  if (p : ℕ) = 2 then 1 else
    1 - (distinctPrimeDecay p s / (1 - distinctPrimeDecay p s)) ^ 2

/-- The convergent odd-prime correction product. -/
def oddPrimeCorrection (s : ℂ) : ℂ := ∏' p : Nat.Primes, oddPrimeCorrectionFactor p s

private theorem norm_distinctPrimeDecay (p : Nat.Primes) (s : ℂ) :
    ‖distinctPrimeDecay p s‖ = Real.exp (-(s.re * Real.log (p : ℕ))) := by
  simp only [distinctPrimeDecay, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private theorem norm_distinctPrimeDecay_le (p : Nat.Primes) {σ : ℝ} {s : ℂ}
    (hs : σ ≤ s.re) :
    ‖distinctPrimeDecay p s‖ ≤ Real.exp (-(σ * Real.log (p : ℕ))) := by
  rw [norm_distinctPrimeDecay]
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (mul_le_mul_of_nonneg_right hs
    (Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)))

private theorem norm_distinctPrimeDecay_uniform (p : Nat.Primes) {σ : ℝ}
    (hσ : 0 ≤ σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖distinctPrimeDecay p s‖ ≤ Real.exp (-(σ * Real.log 2)) := by
  refine (norm_distinctPrimeDecay_le p hs).trans (Real.exp_le_exp.mpr ?_)
  have hp : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.two_le
  exact neg_le_neg (mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hp) hσ)

private theorem norm_distinctPrimeDecay_lt_one (p : Nat.Primes) {s : ℂ}
    (hs : 0 < s.re) : ‖distinctPrimeDecay p s‖ < 1 := by
  rw [norm_distinctPrimeDecay, Real.exp_lt_one_iff]
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
  linarith only [mul_pos hs (Real.log_pos hp)]

private theorem one_sub_distinctPrimeDecay_ne_zero (p : Nat.Primes) {s : ℂ}
    (hs : 0 < s.re) : 1 - distinctPrimeDecay p s ≠ 0 := by
  intro h
  have hn := norm_distinctPrimeDecay_lt_one p hs
  rw [← sub_eq_zero.mp h, norm_one] at hn
  exact lt_irrefl _ hn

private theorem differentiableOn_oddPrimeCorrectionFactor (p : Nat.Primes) :
    DifferentiableOn ℂ (oddPrimeCorrectionFactor p) {s : ℂ | 0 < s.re} := by
  intro s hs
  by_cases hp : (p : ℕ) = 2
  · simp only [oddPrimeCorrectionFactor, if_pos hp]
    exact differentiableWithinAt_const _
  · have hx : DifferentiableAt ℂ (distinctPrimeDecay p) s := by
      unfold distinctPrimeDecay
      fun_prop
    have hd : DifferentiableAt ℂ (fun z => 1 - distinctPrimeDecay p z) s :=
      differentiableAt_const.sub hx
    have h := differentiableAt_const.sub
      ((hx.div hd (one_sub_distinctPrimeDecay_ne_zero p hs)).pow 2)
    simpa only [oddPrimeCorrectionFactor, if_neg hp] using h.differentiableWithinAt

/-- A summable quadratic majorant, uniform on any strictly positive half-plane. -/
private theorem norm_oddPrimeCorrectionFactor_sub_one_le (p : Nat.Primes) {σ : ℝ}
    (hσ : 0 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖oddPrimeCorrectionFactor p s - 1‖ ≤
      (p : ℝ) ^ (-(2 * σ)) / (1 - Real.exp (-(σ * Real.log 2))) ^ 2 := by
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  have hq : Real.exp (-(σ * Real.log 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith only [mul_pos hσ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hb : 0 < 1 - Real.exp (-(σ * Real.log 2)) := sub_pos.mpr hq
  by_cases hp2 : (p : ℕ) = 2
  · rw [oddPrimeCorrectionFactor, if_pos hp2, sub_self, norm_zero]
    positivity
  · have hden : 1 - Real.exp (-(σ * Real.log 2)) ≤ ‖1 - distinctPrimeDecay p s‖ := by
      have ht := norm_sub_norm_le (1 : ℂ) (distinctPrimeDecay p s)
      rw [norm_one] at ht
      linarith only [ht, norm_distinctPrimeDecay_uniform p hσ.le hs]
    have hsquare : ‖distinctPrimeDecay p s‖ ^ 2 ≤ (p : ℝ) ^ (-(2 * σ)) := by
      calc
        _ ≤ (Real.exp (-(σ * Real.log (p : ℕ)))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_distinctPrimeDecay_le p hs) 2
        _ = _ := by
          rw [Real.rpow_def_of_pos hp0, ← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
    rw [oddPrimeCorrectionFactor, if_neg hp2,
      show (1 - (distinctPrimeDecay p s / (1 - distinctPrimeDecay p s)) ^ 2) - 1 =
        -(distinctPrimeDecay p s / (1 - distinctPrimeDecay p s)) ^ 2 by ring,
      norm_neg, norm_pow, norm_div, div_pow]
    exact (div_le_div_of_nonneg_right hsquare (sq_nonneg _)).trans
      (div_le_div_of_nonneg_left (Real.rpow_nonneg hp0.le _) (pow_pos hb 2)
        (pow_le_pow_left₀ hb.le hden 2))

/-- Every half-plane strictly inside `Re s > 1/2` has a normally convergent product. -/
theorem multipliableLocallyUniformlyOn_oddPrimeCorrection {σ : ℝ} (hσ : 1 / 2 < σ) :
    MultipliableLocallyUniformlyOn oddPrimeCorrectionFactor {s : ℂ | σ < s.re} := by
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hsum : Summable fun p : Nat.Primes =>
      (p : ℝ) ^ (-(2 * σ)) / (1 - Real.exp (-(σ * Real.log 2))) ^ 2 :=
    (Nat.Primes.summable_rpow.mpr (by linarith only [hσ])).div_const _
  have h := hsum.multipliableLocallyUniformlyOn_one_add
    (isOpen_lt continuous_const Complex.continuous_re)
    (f := fun p s => oddPrimeCorrectionFactor p s - 1)
    (Eventually.of_forall fun p s hs => norm_oddPrimeCorrectionFactor_sub_one_le p hσ0 hs.le)
    (fun p => ((differentiableOn_oddPrimeCorrectionFactor p).continuousOn.mono
      (fun s hs => hσ0.trans hs)).sub continuousOn_const)
  have he : (fun (p : Nat.Primes) (s : ℂ) => 1 + (oddPrimeCorrectionFactor p s - 1)) =
      oddPrimeCorrectionFactor := by funext p s; ring
  rwa [he] at h

/-- Absolute summability of the local deficits controls all possible product zeros. -/
theorem summable_norm_oddPrimeCorrectionFactor_sub_one {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun p : Nat.Primes => ‖oddPrimeCorrectionFactor p s - 1‖ := by
  have hsum : Summable fun p : Nat.Primes =>
      (p : ℝ) ^ (-(2 * s.re)) / (1 - Real.exp (-(s.re * Real.log 2))) ^ 2 :=
    (Nat.Primes.summable_rpow.mpr (by linarith only [hs])).div_const _
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p =>
    norm_oddPrimeCorrectionFactor_sub_one_le p (by linarith only [hs]) le_rfl) hsum

/-- No additional zeros arise from the infinite product. -/
theorem oddPrimeCorrection_eq_zero_iff {s : ℂ} (hs : 1 / 2 < s.re) :
    oddPrimeCorrection s = 0 ↔ ∃ p : Nat.Primes, oddPrimeCorrectionFactor p s = 0 := by
  constructor
  · intro h
    by_contra hne
    have hlocal : ∀ p, oddPrimeCorrectionFactor p s ≠ 0 := fun p hp => hne ⟨p, hp⟩
    have hprod := tprod_one_add_ne_zero_of_summable
      (f := fun p => oddPrimeCorrectionFactor p s - 1)
      (fun p => by rw [add_sub_cancel]; exact hlocal p)
      (summable_norm_oddPrimeCorrectionFactor_sub_one hs)
    simp only [add_sub_cancel] at hprod
    exact hprod h
  · exact tprod_of_exists_eq_zero

/-- Holomorphy survives local-factor zeros; no logarithmic branch is imposed on the product. -/
theorem analyticOnNhd_oddPrimeCorrection :
    AnalyticOnNhd ℂ oddPrimeCorrection {s : ℂ | 1 / 2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  let σ : ℝ := (1 / 2 + s.re) / 2
  have hσ : 1 / 2 < σ := by dsimp only [σ]; linarith only [hs]
  have hsσ : σ < s.re := by dsimp only [σ]; linarith only [hs]
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ oddPrimeCorrection {s : ℂ | σ < s.re} :=
    (multipliableLocallyUniformlyOn_oddPrimeCorrection hσ).hasProdLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun _ => by
        simpa only [Finset.prod_fn] using
          DifferentiableOn.finsetProd (fun p _ =>
            (differentiableOn_oddPrimeCorrectionFactor p).mono
              (fun z hz => (show 0 < σ by linarith only [hσ]).trans hz))) hU
  exact (hd.differentiableAt (hU.mem_nhds hsσ)).differentiableWithinAt

/-- At one, prime decay is the reciprocal prime. -/
theorem distinctPrimeDecay_one (p : Nat.Primes) :
    distinctPrimeDecay p 1 = (p : ℂ)⁻¹ := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  rw [distinctPrimeDecay, one_mul, Complex.exp_neg, ← Complex.ofReal_exp,
    Real.exp_log hp]
  rfl

/-- The analytic local correction specializes to the prime-pair factor. -/
theorem oddPrimeCorrectionFactor_one (p : Nat.Primes) :
    oddPrimeCorrectionFactor p 1 =
      (BezoutValuationIncidence.twinPrimeFactor p : ℂ) := by
  unfold oddPrimeCorrectionFactor BezoutValuationIncidence.twinPrimeFactor
  split_ifs with hp
  · simp only [Complex.ofReal_one]
  · rw [distinctPrimeDecay_one]
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
    have hp1 : (p : ℂ) - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast p.prop.ne_one)
    push_cast
    field_simp
    <;> ring

/-- The holomorphic correction takes the positive twin-prime value at one. -/
theorem oddPrimeCorrection_one :
    oddPrimeCorrection 1 = (BezoutValuationIncidence.twinPrimeConstant : ℂ) := by
  have h : HasProd BezoutValuationIncidence.twinPrimeFactor
      BezoutValuationIncidence.twinPrimeConstant := by
    rw [BezoutValuationIncidence.twinPrimeConstant_eq_singularSeries]
    exact BezoutValuationIncidence.hasProd_twinPrimeFactor
  exact ((h.map Complex.ofRealHom Complex.continuous_ofReal).congr_fun
    oddPrimeCorrectionFactor_one).tprod_eq

#print axioms multipliableLocallyUniformlyOn_oddPrimeCorrection
#print axioms analyticOnNhd_oddPrimeCorrection
#print axioms oddPrimeCorrection_eq_zero_iff
#print axioms oddPrimeCorrection_one
end GaloisForLFunctions.SelbergClass
