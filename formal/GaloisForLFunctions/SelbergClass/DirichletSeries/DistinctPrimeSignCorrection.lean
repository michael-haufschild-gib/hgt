import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The odd-prime correction to the distinct-prime sign series

The local factor `(1 - 2p⁻ˢ)/(1 - p⁻ˢ)²` differs from one by
`-(p⁻ˢ/(1 - p⁻ˢ))²`. These quadratic deficits give locally uniform
convergence on `Re s > 1/2`, including points where a local factor vanishes.
-/

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.SelbergClass

/-- Entire prime-decay function, written without a branch-dependent logarithm. -/
def distinctPrimeDecay (p : Nat.Primes) (s : ℂ) : ℂ :=
  Complex.exp (-(s * (Real.log (p : ℕ) : ℂ)))

/-- Positive prime bases identify exponential decay with the usual complex power. -/
theorem distinctPrimeDecay_eq_cpow (p : Nat.Primes) (s : ℂ) :
    distinctPrimeDecay p s = (p : ℂ) ^ (-s) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℕ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (Nat.cast_nonneg (p : ℕ))).symm
  rw [distinctPrimeDecay, Complex.cpow_def_of_ne_zero hp, hlog]
  congr 1
  ring

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

/-- Positive real part keeps every geometric denominator away from zero. -/
theorem one_sub_distinctPrimeDecay_ne_zero (p : Nat.Primes) {s : ℂ}
    (hs : 0 < s.re) : 1 - distinctPrimeDecay p s ≠ 0 := by
  intro h
  have hn := norm_distinctPrimeDecay_lt_one p hs
  rw [← sub_eq_zero.mp h, norm_one] at hn
  exact lt_irrefl _ hn

/-- The quadratic deficit equals the rational Euler correction. -/
theorem oddPrimeCorrectionFactor_eq (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    oddPrimeCorrectionFactor p s =
      if (p : ℕ) = 2 then 1 else
        (1 - 2 * distinctPrimeDecay p s) / (1 - distinctPrimeDecay p s) ^ 2 := by
  unfold oddPrimeCorrectionFactor
  split_ifs
  · rfl
  · have hd := one_sub_distinctPrimeDecay_ne_zero p hs
    field_simp
    ring

/-- A local zero occurs precisely when an odd-prime decay equals one half. -/
theorem oddPrimeCorrectionFactor_eq_zero_iff (p : Nat.Primes) {s : ℂ}
    (hs : 0 < s.re) :
    oddPrimeCorrectionFactor p s = 0 ↔
      (p : ℕ) ≠ 2 ∧ distinctPrimeDecay p s = 1 / 2 := by
  rw [oddPrimeCorrectionFactor_eq p hs]
  split_ifs with hp
  · simp only [hp, ne_eq, not_true_eq_false, false_and, one_ne_zero]
  · rw [div_eq_zero_iff, or_iff_left (pow_ne_zero 2
      (one_sub_distinctPrimeDecay_ne_zero p hs))]
    constructor
    · intro h
      refine ⟨hp, ?_⟩
      linear_combination -h / 2
    · rintro ⟨_, h⟩
      rw [h]
      norm_num

private theorem differentiableOn_oddPrimeCorrectionFactor (p : Nat.Primes) :
    DifferentiableOn ℂ (oddPrimeCorrectionFactor p) {s : ℂ | 0 < s.re} := by
  by_cases hp : (p : ℕ) = 2
  · have he : oddPrimeCorrectionFactor p = fun _ => 1 := by
      funext s
      exact if_pos hp
    rw [he]
    intro s _
    exact (differentiableAt_const (1 : ℂ)).differentiableWithinAt
  · intro s hs
    have he : oddPrimeCorrectionFactor p = fun z =>
        1 - (distinctPrimeDecay p z / (1 - distinctPrimeDecay p z)) ^ 2 := by
      funext z
      exact if_neg hp
    rw [he]
    have hx : DifferentiableAt ℂ (distinctPrimeDecay p) s := by
      unfold distinctPrimeDecay
      fun_prop
    have hd : DifferentiableAt ℂ (fun z => 1 - distinctPrimeDecay p z) s :=
      (differentiableAt_const (1 : ℂ)).sub hx
    have h : DifferentiableAt ℂ (fun z =>
        1 - (distinctPrimeDecay p z / (1 - distinctPrimeDecay p z)) ^ 2) s :=
      (differentiableAt_const (1 : ℂ)).sub
      ((hx.div hd (one_sub_distinctPrimeDecay_ne_zero p hs)).pow 2)
    exact h.differentiableWithinAt

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

/-- The local factors converge to the defined product at every point of its half-plane. -/
theorem hasProd_oddPrimeCorrection {s : ℂ} (hs : 1 / 2 < s.re) :
    HasProd (fun p => oddPrimeCorrectionFactor p s) (oddPrimeCorrection s) := by
  have hσ : 1 / 2 < (1 / 2 + s.re) / 2 := by linarith only [hs]
  have hsσ : (1 / 2 + s.re) / 2 < s.re := by linarith only [hs]
  exact (multipliableLocallyUniformlyOn_oddPrimeCorrection hσ).hasProdLocallyUniformlyOn.hasProd hsσ

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
  change 1 / 2 < s.re at hs
  let σ : ℝ := (1 / 2 + s.re) / 2
  have hσ : 1 / 2 < σ := by dsimp only [σ]; linarith only [hs]
  have hsσ : σ < s.re := by dsimp only [σ]; linarith only [hs]
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hU : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ oddPrimeCorrection {s : ℂ | σ < s.re} :=
    (multipliableLocallyUniformlyOn_oddPrimeCorrection hσ).hasProdLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun S => by
        classical
        induction S using Finset.induction_on with
        | empty =>
            simp only [Finset.prod_empty]
            intro z _
            exact (differentiableAt_const (1 : ℂ)).differentiableWithinAt
        | @insert p S hp ih =>
            simp only [Finset.prod_insert hp]
            exact ((differentiableOn_oddPrimeCorrectionFactor p).mono
              (fun z hz => hσ0.trans hz)).mul ih) hU
  exact (hd.differentiableAt (hU.mem_nhds hsσ)).differentiableWithinAt

/-- At one, prime decay is the reciprocal prime. -/
theorem distinctPrimeDecay_one (p : Nat.Primes) :
    distinctPrimeDecay p 1 = (p : ℂ)⁻¹ := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  rw [distinctPrimeDecay, one_mul, Complex.exp_neg, ← Complex.ofReal_exp,
    Real.exp_log hp]
  rfl

private theorem norm_distinctPrimeDecay_lt_half (p : Nat.Primes) (hp : 4 ≤ (p : ℕ))
    {s : ℂ} (hs : 1 / 2 < s.re) : ‖distinctPrimeDecay p s‖ < 1 / 2 := by
  have hlogp : 0 < Real.log (p : ℕ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hlog4 : Real.log 4 ≤ Real.log (p : ℕ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp)
  have hlog : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using Real.log_pow 2 2
  have he : -(s.re * Real.log (p : ℕ)) < -Real.log 2 := by
    have hmul := mul_lt_mul_of_pos_right hs hlogp
    linarith only [hlog4, hlog, hmul]
  rw [norm_distinctPrimeDecay]
  calc
    _ < Real.exp (-Real.log 2) := Real.exp_lt_exp.mpr he
    _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

/-- In the convergence half-plane, prime three accounts for every correction zero. -/
theorem oddPrimeCorrection_eq_zero_iff_three {s : ℂ} (hs : 1 / 2 < s.re) :
    oddPrimeCorrection s = 0 ↔
      distinctPrimeDecay ⟨3, Nat.prime_three⟩ s = 1 / 2 := by
  have hs0 : 0 < s.re := by linarith only [hs]
  rw [oddPrimeCorrection_eq_zero_iff hs]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨hp2, hdecay⟩ := (oddPrimeCorrectionFactor_eq_zero_iff p hs0).mp hp
    have hp3 : (p : ℕ) = 3 := by
      by_contra hne
      have hp4 : 4 ≤ (p : ℕ) := by have h := p.prop.two_le; omega
      have hn := norm_distinctPrimeDecay_lt_half p hp4 hs
      rw [hdecay] at hn
      norm_num at hn
    have he : p = (⟨3, Nat.prime_three⟩ : Nat.Primes) := Subtype.ext hp3
    simpa only [he] using hdecay
  · intro h
    exact ⟨⟨3, Nat.prime_three⟩,
      (oddPrimeCorrectionFactor_eq_zero_iff _ hs0).mpr ⟨by norm_num, h⟩⟩

/-- The real prime-three zero lies strictly between one half and one. -/
theorem log_two_div_log_three_mem :
    Real.log 2 / Real.log 3 ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h23 := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)
  have h34 := Real.log_lt_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) < 4)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using Real.log_pow 2 2
  constructor
  · apply (lt_div_iff₀ h3).mpr
    linarith only [h34, h4]
  · exact (div_lt_one h3).mpr h23

/-- The odd-prime correction has an explicit zero inside its holomorphic half-plane. -/
theorem oddPrimeCorrection_log_two_div_log_three :
    oddPrimeCorrection (Real.log 2 / Real.log 3 : ℝ) = 0 := by
  have h3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne'
  apply (oddPrimeCorrection_eq_zero_iff_three
    (by exact log_two_div_log_three_mem.1)).mpr
  unfold distinctPrimeDecay
  change Complex.exp (-((↑(Real.log 2 / Real.log 3) : ℂ) * ↑(Real.log 3))) = 1 / 2
  rw [← Complex.ofReal_mul, div_mul_cancel₀ _ h3, Complex.exp_neg,
    ← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

#print axioms multipliableLocallyUniformlyOn_oddPrimeCorrection
#print axioms analyticOnNhd_oddPrimeCorrection
#print axioms oddPrimeCorrection_eq_zero_iff
#print axioms oddPrimeCorrection_eq_zero_iff_three
#print axioms oddPrimeCorrection_log_two_div_log_three
end GaloisForLFunctions.SelbergClass
