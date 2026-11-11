import GaloisForLFunctions.SelectiveArithmetic.InTheMeanOverTheHeightsTheContactsCancel
import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.RHTower.WeilConePrimePolynomialMoments
import GaloisForLFunctions.RHTower.VonMangoldtNonPrimeSqrtSum
import GaloisForLFunctions.RHTower.Sieve.ZetaThreeFourOne

/-!
# The contact polynomial has few large heights

The mean square on `[T,2T]` bounds the measure of heights at which the contact
polynomial exceeds a fixed fraction of `log T`. Mertens' first theorem bounds
the contact energy by `log N (log N + log 4 + 4)`. At aperture `a ≥ 1` this gives
`(13+2 log 4) T a²/(c log T)²`, when the off-diagonal term fits in the height interval.
This is a statement about the contact polynomial; full window positivity has a
separate quantifier over packet frequencies.
-/

open Filter Topology MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

/-- Mertens' first theorem saves one logarithm in the contact energy. -/
theorem contactEnergy_le_mertens {N : ℕ} (hN : 1 ≤ N) :
    contactEnergy N ≤ Real.log N * (Real.log N + Real.log 4 + 4) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hm := (abs_le.mp (_root_.RHTower.Mertens.mertens_first N hN)).2
  have hsum : ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) / n ≤
      Real.log N + Real.log 4 + 4 := by
    have hsub : ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) / n ≤
        ∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) / n :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn => Finset.mem_Icc.mpr
          ⟨by have := (Finset.mem_Icc.mp hn).1; omega, (Finset.mem_Icc.mp hn).2⟩)
        (fun n _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
    linarith only [hm, hsub]
  calc
    contactEnergy N ≤ ∑ n ∈ Finset.Icc 2 N, Real.log N * ((Λ n : ℝ) / n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by
        exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : 0 < n)
      have hΛ : (Λ n : ℝ) ≤ Real.log N := ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log hn0 (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2))
      rw [div_pow, Real.sq_sqrt hn0.le, sq, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hΛ
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hn0.le)
    _ = Real.log N * ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) / n :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hlogN

private theorem measureReal_contactPoly_le_of_integral {N : ℕ} {T V B : ℝ}
    (hT : 0 ≤ T) (hV : 0 < V)
    (hB : (∫ t in T..2 * T, contactPoly N t ^ 2) ≤ B) :
    (volume.restrict (Ioc T (2 * T))).real {t | V ≤ |contactPoly N t|} ≤ B / V ^ 2 := by
  have hint : Integrable (fun t => contactPoly N t ^ 2)
      (volume.restrict (Ioc T (2 * T))) :=
    (((continuous_contactPoly N).pow 2).integrableOn_Icc
      (a := T) (b := 2 * T)).mono_set Ioc_subset_Icc_self
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := volume.restrict (Ioc T (2 * T)))
    (Filter.Eventually.of_forall fun t => sq_nonneg (contactPoly N t)) hint (V ^ 2)
  have hset : {t | V ≤ |contactPoly N t|} = {t | V ^ 2 ≤ contactPoly N t ^ 2} := by
    ext t
    simp only [mem_setOf_eq]
    constructor
    · intro h
      simpa only [sq_abs] using pow_le_pow_left₀ hV.le h 2
    · intro h
      by_contra hn
      have hlt := pow_lt_pow_left₀ (lt_of_not_ge hn) (abs_nonneg (contactPoly N t))
        (by norm_num : 2 ≠ 0)
      rw [sq_abs] at hlt
      exact (not_lt.mpr h) hlt
  rw [hset, le_div_iff₀ (sq_pos_of_pos hV), mul_comm]
  rw [intervalIntegral.integral_of_le (by linarith only [hT])] at hB
  exact hm.trans hB

/-- An explicit large-value estimate with quadratic logarithmic variance. -/
theorem measureReal_large_contactPoly_mertens_le {N : ℕ} (hN : 1 ≤ N)
    {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V) :
    (volume.restrict (Ioc T (2 * T))).real {t | V ≤ |contactPoly N t|} ≤
      (T * (Real.log N * (Real.log N + Real.log 4 + 4)) +
        4 * N * contactMass N ^ 2) / V ^ 2 := by
  apply measureReal_contactPoly_le_of_integral hT hV
  have hm := integral_contactPoly_shift_sq_le hN hT 0
  simp only [add_zero] at hm
  exact hm.trans (add_le_add
    (mul_le_mul_of_nonneg_left (contactEnergy_le_mertens hN) hT) le_rfl)

/-- Markov's inequality turns the contact mean square into a large-height bound. -/
theorem measureReal_large_contactPoly_le {a T V : ℝ} (ha : 0 ≤ a) (hV : 0 < V)
    (hT : 4 * Real.exp (4 * a) * (2 + 2 * a) ^ 4 ≤ T) :
    (volume.restrict (Ioc T (2 * T))).real
      {t | V ≤ |contactPoly ⌊Real.exp (2 * a)⌋₊ t|} ≤
      T * (2 * a * (2 + 2 * a) ^ 2 + 1) / V ^ 2 := by
  exact measureReal_contactPoly_le_of_integral
    ((by positivity : 0 ≤ 4 * Real.exp (4 * a) * (2 + 2 * a) ^ 4).trans hT)
    hV (integral_contactPoly_window_sq_le ha hT)

/-- Mertens improves the exceptional-height bound from cubic to quadratic in aperture. -/
theorem measureReal_contactPoly_log_heights_quadratic_le {a T c : ℝ}
    (ha : 1 ≤ a) (hT1 : 1 < T) (hc : 0 < c)
    (hT : 4 * Real.exp (4 * a) * (2 + 2 * a) ^ 4 ≤ T) :
    (volume.restrict (Ioc T (2 * T))).real
      {t | c * Real.log T ≤ |contactPoly ⌊Real.exp (2 * a)⌋₊ t|} ≤
      (13 + 2 * Real.log 4) * T * a ^ 2 / (c * Real.log T) ^ 2 := by
  let N := ⌊Real.exp (2 * a)⌋₊
  let C := Real.log 4 + 4
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hT0 : 0 ≤ T := (zero_lt_one.trans hT1).le
  have hC : 0 ≤ C := by
    dsimp [C]
    have hl := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith only [hl]
  have hN : 1 ≤ N := (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    (by simpa using Real.one_le_exp_iff.mpr (by linarith only [ha0] : 0 ≤ 2 * a))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : Real.log N ≤ 2 * a := by
    have h := Real.log_le_log hN0 (Nat.floor_le (Real.exp_pos (2 * a)).le)
    rwa [Real.log_exp] at h
  have henergy : contactEnergy N ≤ 2 * a * (2 * a + C) := by
    refine (contactEnergy_le_mertens hN).trans ?_
    have hlog0 := Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N)
    have hh := mul_le_mul hlogN (add_le_add hlogN (le_refl C))
      (add_nonneg hlog0 hC) (by positivity : 0 ≤ 2 * a)
    simpa only [C, add_assoc] using hh
  have hpoly : 2 * a * (2 * a + C) + 1 ≤ (13 + 2 * Real.log 4) * a ^ 2 := by
    have ha2 : a ≤ a ^ 2 := by nlinarith only [mul_nonneg ha0 (sub_nonneg.mpr ha)]
    have ha21 : 1 ≤ a ^ 2 := ha.trans ha2
    have hm := mul_le_mul_of_nonneg_left ha2 hC
    dsimp [C] at hm ⊢
    nlinarith only [hm, ha21]
  apply measureReal_contactPoly_le_of_integral hT0 (mul_pos hc (Real.log_pos hT1))
  have hm := integral_contactPoly_shift_sq_le hN hT0 0
  simp only [add_zero] at hm
  have hoff := (four_mul_window_mass_sq_le ha0).trans hT
  have he := mul_le_mul_of_nonneg_left henergy hT0
  have hp := mul_le_mul_of_nonneg_left hpoly hT0
  change (∫ t in T..2 * T, contactPoly N t ^ 2) ≤ _
  change 4 * (N : ℝ) * contactMass N ^ 2 ≤ T at hoff
  nlinarith only [hm, hoff, he, hp]

/-- The exceptional contact heights have measure at most `33 T a³/(c log T)²`. -/
theorem measureReal_contactPoly_log_heights_le {a T c : ℝ}
    (ha : 1 ≤ a) (hT1 : 1 < T) (hc : 0 < c)
    (hT : 4 * Real.exp (4 * a) * (2 + 2 * a) ^ 4 ≤ T) :
    (volume.restrict (Ioc T (2 * T))).real
      {t | c * Real.log T ≤ |contactPoly ⌊Real.exp (2 * a)⌋₊ t|} ≤
      33 * T * a ^ 3 / (c * Real.log T) ^ 2 := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hpoly : 2 * a * (2 + 2 * a) ^ 2 + 1 ≤ 33 * a ^ 3 := by
    have hs : (2 + 2 * a) ^ 2 ≤ (4 * a) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [ha]) 2
    have hcube : 1 ≤ a ^ 3 := one_le_pow₀ ha
    have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * a)
    nlinarith only [hm, hcube]
  refine (measureReal_large_contactPoly_le ha0 (mul_pos hc (Real.log_pos hT1)) hT).trans ?_
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hpoly (zero_lt_one.trans hT1).le
  nlinarith only [hm]

/-- The prime coefficients of the contact polynomial, truncated at `N`. -/
def primeContactCoeff (N : ℕ) : ArithmeticFunction ℂ where
  toFun n := if n.Prime ∧ n ≤ N then ((Λ n : ℝ) : ℂ) else 0
  map_zero' := by simp

@[simp] theorem primeContactCoeff_apply (N n : ℕ) :
    primeContactCoeff N n = if n.Prime ∧ n ≤ N then ((Λ n : ℝ) : ℂ) else 0 := rfl

/-- Proper prime powers change the contact polynomial by at most `O(log N)`. -/
theorem abs_contactPoly_sub_prime_re_le {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    |contactPoly N t -
      (_root_.RHTower.edPoly (primeContactCoeff N) (Finset.Icc 1 N)
        (_root_.RHTower.displacedLinePt 0 t)).re| ≤
      2 * Real.log N + 4 * Real.log 4 + 16 := by
  classical
  let s := _root_.RHTower.displacedLinePt 0 t
  have hsre : s.re = 1 / 2 := by norm_num [s, _root_.RHTower.displacedLinePt]
  have hsim : s.im = t := by norm_num [s, _root_.RHTower.displacedLinePt]
  have hsub : Finset.Icc 2 N ⊆ Finset.Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hn).1; omega,
      (Finset.mem_Icc.mp hn).2⟩
  have hsum : _root_.RHTower.edPoly (primeContactCoeff N) (Finset.Icc 1 N) s =
      ∑ n ∈ Finset.Icc 2 N, primeContactCoeff N n * ((n : ℝ) : ℂ) ^ (-s) := by
    unfold _root_.RHTower.edPoly
    symm
    apply Finset.sum_subset hsub
    intro n hn hn'
    have hn1 : n = 1 := by
      have := Finset.mem_Icc.mp hn
      have : ¬ (2 ≤ n ∧ n ≤ N) := by simpa only [Finset.mem_Icc] using hn'
      omega
    subst n
    simp [primeContactCoeff]
  have hre : (_root_.RHTower.edPoly (primeContactCoeff N) (Finset.Icc 1 N) s).re =
      ∑ n ∈ Finset.Icc 2 N,
        if n.Prime then (Λ n : ℝ) / Real.sqrt n * Real.cos (t * Real.log n) else 0 := by
    rw [hsum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnN := (Finset.mem_Icc.mp hn).2
    by_cases hp : n.Prime
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hp.pos
      have hexp : Real.exp (-Real.log n * (1 / 2)) = 1 / Real.sqrt n := by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0, neg_mul, Real.exp_neg]
        simp only [one_div]
      simp only [primeContactCoeff_apply, hp, hnN, and_self, if_true,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.ofReal_natCast]
      rw [_root_.RHTower.Sieve.re_prime_cpow_neg hp.pos, hsre, hsim, hexp,
        mul_comm (Real.log n) t]
      ring
    · simp [primeContactCoeff, hp]
  have hdiff : |contactPoly N t -
      (_root_.RHTower.edPoly (primeContactCoeff N) (Finset.Icc 1 N) s).re| ≤
      ∑ n ∈ Finset.Icc 2 N, if n.Prime then 0 else (Λ n : ℝ) / Real.sqrt n := by
    rw [contactPoly, hre, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    by_cases hp : n.Prime
    · simp [hp]
    · simp only [hp, if_false, sub_zero, abs_mul,
        abs_of_nonneg (contactCoeff_nonneg n)]
      exact mul_le_of_le_one_right (contactCoeff_nonneg n) (Real.abs_cos_le_one _)
  have htail : (∑ n ∈ Finset.Icc 2 N, if n.Prime then 0 else (Λ n : ℝ) / Real.sqrt n) ≤
      ∑ n ∈ Finset.Ioc 0 N with ¬n.Prime, (Λ n : ℝ) / Real.sqrt n := by
    rw [Finset.sum_filter]
    simp only [ite_not]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      have := Finset.mem_Icc.mp hn
      exact Finset.mem_Ioc.mpr ⟨by omega, this.2⟩
    · intro n _ _
      split_ifs <;> first | exact le_rfl | exact contactCoeff_nonneg n
  exact hdiff.trans (htail.trans (_root_.RHTower.sum_nonprime_vonMangoldt_div_sqrt_le hN))

/-- The prime part has at most the contact energy, hence quadratic logarithmic variance. -/
theorem primeContactEnergy_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, ‖primeContactCoeff N n‖ ^ 2 / (n : ℝ)) ≤
      Real.log N * (Real.log N + Real.log 4 + 4) := by
  have hsum : (∑ n ∈ Finset.Icc 1 N, ((Λ n : ℝ) / Real.sqrt n) ^ 2) =
      contactEnergy N := by
    symm
    unfold contactEnergy
    apply Finset.sum_subset
    · intro n hn
      have := Finset.mem_Icc.mp hn
      exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
    · intro n hn hn'
      have hn1 : n = 1 := by
        have := Finset.mem_Icc.mp hn
        have : ¬ (2 ≤ n ∧ n ≤ N) := by simpa only [Finset.mem_Icc] using hn'
        omega
      subst n
      simp
  calc
    (∑ n ∈ Finset.Icc 1 N, ‖primeContactCoeff N n‖ ^ 2 / (n : ℝ)) ≤
        ∑ n ∈ Finset.Icc 1 N, ((Λ n : ℝ) / Real.sqrt n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hp : n.Prime
      · have hnN := (Finset.mem_Icc.mp hn).2
        simp only [primeContactCoeff_apply, hp, hnN, and_self, if_true,
          Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
          Real.sq_sqrt (Nat.cast_nonneg n)]
        exact le_rfl
      · simp only [primeContactCoeff_apply, hp, false_and, if_false, norm_zero,
          sq, zero_mul, zero_div]
        exact mul_self_nonneg _
    _ = contactEnergy N := hsum
    _ ≤ _ := contactEnergy_le_mertens hN

/-- High moments of the prime part control large contact values after the explicit
proper-prime-power error. The moment order may grow with the height. -/
theorem measureReal_contactPoly_high_moment_le {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (hlen : 8 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log (N ^ k : ℕ)) ≤ T) :
    (volume.restrict (Ioc T (2 * T))).real
      {t | V + (2 * Real.log N + 4 * Real.log 4 + 16) ≤ |contactPoly N t|} ≤
      2 * Real.exp 1 * Real.sqrt k * T *
        (k * (Real.log N * (Real.log N + Real.log 4 + 4)) /
          (Real.exp 1 * V ^ 2)) ^ k := by
  have hprime : ∀ n, primeContactCoeff N n ≠ 0 → n.Prime := by
    intro n hn
    by_contra hp
    exact hn (by simp [primeContactCoeff, hp])
  have hsupport : ∀ n, primeContactCoeff N n ≠ 0 → n ≤ N := by
    intro n hn
    by_contra hgt
    exact hn (by simp [primeContactCoeff, hgt])
  have hsub : {t | V + (2 * Real.log N + 4 * Real.log 4 + 16) ≤ |contactPoly N t|} ⊆
      {t | V ≤ ‖_root_.RHTower.edPoly (primeContactCoeff N) (Finset.Icc 1 N)
        (_root_.RHTower.displacedLinePt 0 t)‖} := by
    intro t ht
    have he := abs_contactPoly_sub_prime_re_le hN t
    have hre := Complex.abs_re_le_norm
      (_root_.RHTower.edPoly (primeContactCoeff N) (Finset.Icc 1 N)
        (_root_.RHTower.displacedLinePt 0 t))
    have htri := abs_add_le
      (contactPoly N t - (_root_.RHTower.edPoly (primeContactCoeff N) (Finset.Icc 1 N)
        (_root_.RHTower.displacedLinePt 0 t)).re)
      (_root_.RHTower.edPoly (primeContactCoeff N) (Finset.Icc 1 N)
        (_root_.RHTower.displacedLinePt 0 t)).re
    rw [sub_add_cancel] at htri
    change V + _ ≤ _ at ht
    change V ≤ _
    linarith only [ht, he, hre, htri]
  refine (measureReal_mono hsub).trans ?_
  have hm := _root_.RHTower.WeilConeMoments.measureReal_large_primePoly_le
    hprime hsupport 0 hk (show T ≤ 2 * T by linarith only [hT]) hV
    (by simpa only [two_mul, add_sub_cancel_left] using hlen)
  have hm' : (volume.restrict (Ioc T (2 * T))).real
      {t | V ≤ ‖_root_.RHTower.edPoly (primeContactCoeff N) (Finset.Icc 1 N)
        (_root_.RHTower.displacedLinePt 0 t)‖} ≤
      2 * Real.exp 1 * Real.sqrt k * T *
        (k * (∑ n ∈ Finset.Icc 1 N, ‖primeContactCoeff N n‖ ^ 2 / (n : ℝ)) /
          (Real.exp 1 * V ^ 2)) ^ k := by
    simpa only [mul_zero, zero_sub, Real.rpow_neg_one, ← div_eq_mul_inv,
      two_mul, add_sub_cancel_left] using hm
  refine hm'.trans ?_
  gcongr
  exact primeContactEnergy_le hN

end GaloisForLFunctions.SelectiveArithmetic
