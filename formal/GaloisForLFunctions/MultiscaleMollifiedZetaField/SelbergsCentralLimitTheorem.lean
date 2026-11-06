import GaloisForLFunctions.MultiscaleMollifiedZetaField.ThePrimeFieldIsGaussian
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheOffLineLogarithmIsThePrimeField
import GaloisForLFunctions.RHTower.ChebyshevSquareWeight
import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# Selberg's central limit theorem

The law of `log|ζ(½ + it)|/√(½ log log T)` on `t ∈ (T, 2T]` tends to the standard Gaussian
(`tendsto_log_norm_zeta_law_gaussian`).

**Decomposition.** With `L = log T`, `κ = (log L)^{1/4}`, `R = κ/L`, `x = T^{1/30000}`,
`Y = ⌊e^{L/log L}⌋` and `F = Σ_{p ≤ Y} p^{−1/2} cos(t log p)`,

`log|ζ(½ + it)| − F = (shift to ½ + R) + (zero sum) + (polynomial difference)`:

* the shift has mean `O(κ)`, `exists_volume_log_norm_zeta_shift_ge_le`;
* the zero sum is bounded outside measure `≪ T e^{−κ/60000}`,
  `exists_volume_log_norm_zeta_sub_logPoly_gt_le`;
* the polynomial difference `Re P_x(½ + R + it) − F` has mean square `O(log log L)` by the mean value
  theorem and Mertens (`sum_polyDiffCoeff_sq_le`): the primes `p ≤ Y` move by `R log p`, the primes
  `Y < p ≤ x²` carry the reciprocal mass `log(log x/log Y) ≍ log log L`.

All three are `o(√(log L))` in probability, and `F` is Gaussian by the Steinhaus transfer. The
primes above `T^{o(1)}` never have to be independent: they are small in mean square.
-/

noncomputable section

open Complex Set MeasureTheory Filter ArithmeticFunction ProbabilityTheory Topology
open RHTower RHTower.SteinhausModel

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-! ### The classical weight -/

/-- The weight `p^{−1/2}` of the prime sum on the critical line. -/
def halfWeight (m : ℕ) : ℝ := (m : ℝ) ^ (-(1 / 2) : ℝ)

theorem halfWeight_nonneg (m : ℕ) : 0 ≤ halfWeight m :=
  Real.rpow_nonneg (Nat.cast_nonneg m) _

theorem halfWeight_le_one (m : ℕ) : halfWeight m ≤ 1 := by
  unfold halfWeight
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
    norm_num
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm) (by norm_num)

theorem halfWeight_sq (m : ℕ) : halfWeight m ^ 2 = 1 / (m : ℝ) := by
  unfold halfWeight
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
    norm_num
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
    norm_num
    rw [Real.rpow_neg_one]

/-- The primes up to `Y`. -/
def primesUpTo (Y : ℕ) : Finset ℕ := (Finset.Icc 1 Y).filter Nat.Prime

theorem prime_of_mem_primesUpTo {Y p : ℕ} (hp : p ∈ primesUpTo Y) : p.Prime :=
  (Finset.mem_filter.mp hp).2

theorem le_of_mem_primesUpTo {Y p : ℕ} (hp : p ∈ primesUpTo Y) : p ≤ Y :=
  (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2

theorem sum_primesUpTo_inv (Y : ℕ) :
    ∑ p ∈ primesUpTo Y, 1 / (p : ℝ) = Sieve.mertensS Y := by
  unfold Sieve.mertensS primesUpTo
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.primesLE_eq_filter_range, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨by omega, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨⟨h3.one_lt.le, by omega⟩, h3⟩

/-- **The prime sum on the critical line is Gaussian.** If `Y → ∞` and `Y^K = o(T)` for every `K`,
the law of `Σ_{p ≤ Y} p^{−1/2} cos(t log p)/√(½ Σ_{p ≤ Y} 1/p)` on `(T, 2T]` tends to the standard
Gaussian. -/
theorem tendsto_primeSum_law_gaussian {T : ℕ → ℝ} {Y : ℕ → ℕ} (hT : ∀ n, 0 < T n)
    (hY1 : ∀ n, 1 ≤ Y n) (hW : Tendsto (fun n => Sieve.mertensS (Y n)) atTop atTop)
    (hsmall : ∀ K : ℕ, Tendsto (fun n => (Y n : ℝ) ^ K / T n) atTop (𝓝 0)) :
    Tendsto (fun n => windowLaw (hT n)
        (fun t => primeField halfWeight (primesUpTo (Y n)) t /
          Real.sqrt ((∑ p ∈ primesUpTo (Y n), halfWeight p ^ 2) / 2))
        ((continuous_primeField halfWeight (primesUpTo (Y n))).measurable.div_const _))
      atTop (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  have hWeq : ∀ n, ∑ p ∈ primesUpTo (Y n), halfWeight p ^ 2 = Sieve.mertensS (Y n) := fun n => by
    rw [← sum_primesUpTo_inv]
    exact Finset.sum_congr rfl fun p _ => halfWeight_sq p
  refine tendsto_primeFieldLaw_gaussian (w := fun _ => halfWeight) (P := fun n => primesUpTo (Y n))
    hT (fun _ m => halfWeight_nonneg m) (fun _ m => halfWeight_le_one m)
    (fun n p hp => prime_of_mem_primesUpTo hp) hY1 (fun n p hp => le_of_mem_primesUpTo hp) ?_ ?_
  · simpa only [hWeq] using hW
  · intro K
    have hbound : ∀ n, ((∑ p ∈ primesUpTo (Y n), halfWeight p) * Y n) ^ K / T n ≤
        (Y n : ℝ) ^ (2 * K) / T n := by
      intro n
      refine div_le_div_of_nonneg_right ?_ (hT n).le
      have hsum : ∑ p ∈ primesUpTo (Y n), halfWeight p ≤ Y n := by
        calc ∑ p ∈ primesUpTo (Y n), halfWeight p
            ≤ ∑ _p ∈ primesUpTo (Y n), (1 : ℝ) :=
              Finset.sum_le_sum fun p _ => halfWeight_le_one p
          _ = ((primesUpTo (Y n)).card : ℝ) := by simp
          _ ≤ ((Finset.Icc 1 (Y n)).card : ℝ) := by
              exact_mod_cast Finset.card_filter_le _ _
          _ = Y n := by simp
      rw [pow_mul]
      refine pow_le_pow_left₀ (mul_nonneg (Finset.sum_nonneg fun p _ => halfWeight_nonneg p)
        (Nat.cast_nonneg _)) ?_ K
      rw [sq]
      exact mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg _)
    refine squeeze_zero (fun n => div_nonneg (pow_nonneg (mul_nonneg
      (Finset.sum_nonneg fun p _ => halfWeight_nonneg p) (Nat.cast_nonneg _)) K) (hT n).le)
      hbound (hsmall (2 * K))

/-! ### Comparison of laws -/

/-- `‖e^{ia} − e^{ib}‖ ≤ |a − b|`. -/
theorem norm_cexp_sub_cexp_le (a b : ℝ) :
    ‖cexp ((a : ℂ) * I) - cexp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have h := norm_cexp_sub_sum_le 1 (a - b)
  simp only [expRemainder, Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one, Nat.factorial_one] at h
  have hmul : cexp ((a : ℂ) * I) - cexp ((b : ℂ) * I) =
      cexp ((b : ℂ) * I) * (cexp (((a - b : ℝ) : ℂ) * I) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [hmul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact h

/-- **Slutsky's lemma on a window of heights.** Two fields close in probability have the same limit
law. -/
theorem tendsto_windowLaw_of_close {T : ℕ → ℝ} (hT : ∀ n, 0 < T n) {f g : ℕ → ℝ → ℝ}
    (hf : ∀ n, Measurable (f n)) (hg : ∀ n, Measurable (g n)) {μ : ProbabilityMeasure ℝ}
    (h : Tendsto (fun n => windowLaw (hT n) (f n) (hf n)) atTop (𝓝 μ))
    (hclose : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (windowMeasure (T n)).real {t | ε ≤ |f n t - g n t|}) atTop (𝓝 0)) :
    Tendsto (fun n => windowLaw (hT n) (g n) (hg n)) atTop (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun] at h ⊢
  intro u
  have hu := h u
  rw [Metric.tendsto_atTop] at hu ⊢
  intro δ hδ
  obtain ⟨n₁, hn₁⟩ := hu (δ / 3) (by positivity)
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = δ / (3 * (|u| + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]
    positivity
  have hcl := (hclose ε hε0).eventually (gt_mem_nhds (show (0 : ℝ) < δ / 6 by positivity))
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp hcl
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  have h1 := hn₁ n (le_of_max_le_left hn)
  have h2 := hn₂ n (le_of_max_le_right hn)
  haveI := isProbabilityMeasure_windowMeasure (hT n)
  -- the two characteristic functions as integrals against the window
  have hcf : ∀ (F : ℝ → ℝ) (hF : Measurable F),
      charFun ((windowLaw (hT n) F hF : ProbabilityMeasure ℝ) : Measure ℝ) u =
        ∫ t, cexp (((u * F t : ℝ) : ℂ) * I) ∂(windowMeasure (T n)) := by
    intro F hF
    simp only [windowLaw, ProbabilityMeasure.coe_mk]
    rw [charFun_apply_real, integral_map hF.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    congr 1
    push_cast
    ring
  have hint : ∀ (F : ℝ → ℝ), Measurable F →
      Integrable (fun t => cexp (((u * F t : ℝ) : ℂ) * I)) (windowMeasure (T n)) := by
    intro F hF
    refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun t => ?_)
    · have : Measurable fun t => cexp (((u * F t : ℝ) : ℂ) * I) := by fun_prop
      exact this.aestronglyMeasurable
    · rw [Complex.norm_exp_ofReal_mul_I]
  obtain ⟨S, hS⟩ : ∃ S : Set ℝ, S = {t | ε ≤ |f n t - g n t|} := ⟨_, rfl⟩
  have hSm : MeasurableSet S := by
    rw [hS]
    exact measurableSet_le measurable_const (((hf n).sub (hg n)).abs)
  have hind : Integrable (S.indicator fun _ => (2 : ℝ)) (windowMeasure (T n)) :=
    (integrable_const (2 : ℝ)).indicator hSm
  have hdiff : ‖charFun ((windowLaw (hT n) (g n) (hg n) : ProbabilityMeasure ℝ) : Measure ℝ) u -
      charFun ((windowLaw (hT n) (f n) (hf n) : ProbabilityMeasure ℝ) : Measure ℝ) u‖ ≤
      |u| * ε + 2 * (windowMeasure (T n)).real S := by
    rw [hcf, hcf, ← integral_sub (hint _ (hg n)) (hint _ (hf n))]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hbd : ∀ t, ‖cexp (((u * g n t : ℝ) : ℂ) * I) - cexp (((u * f n t : ℝ) : ℂ) * I)‖ ≤
        |u| * ε + S.indicator (fun _ => (2 : ℝ)) t := by
      intro t
      by_cases htS : t ∈ S
      · rw [Set.indicator_of_mem htS]
        have h3 := norm_sub_le (cexp (((u * g n t : ℝ) : ℂ) * I)) (cexp (((u * f n t : ℝ) : ℂ) * I))
        rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I] at h3
        have : 0 ≤ |u| * ε := by positivity
        linarith
      · rw [Set.indicator_of_notMem htS, add_zero]
        refine (norm_cexp_sub_cexp_le _ _).trans ?_
        have hlt : |f n t - g n t| < ε := by
          rw [hS] at htS
          exact not_le.mp htS
        rw [← mul_sub, abs_mul, abs_sub_comm]
        exact mul_le_mul_of_nonneg_left hlt.le (abs_nonneg u)
    have hI : Integrable (fun t => |u| * ε + S.indicator (fun _ => (2 : ℝ)) t)
        (windowMeasure (T n)) := (integrable_const _).add hind
    refine (integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
      hI (Eventually.of_forall hbd)).trans (le_of_eq ?_)
    rw [integral_add (integrable_const _) hind, integral_const, integral_indicator hSm,
      setIntegral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [dist_eq_norm] at h1 ⊢
  have h3 : |u| * ε ≤ δ / 3 := by
    rw [hε]
    have hu0 : 0 ≤ |u| := abs_nonneg u
    have : |u| * (δ / (3 * (|u| + 1))) = (δ / 3) * (|u| / (|u| + 1)) := by
      field_simp
    rw [this]
    refine mul_le_of_le_one_right (by positivity) ?_
    rw [div_le_one (by positivity)]
    linarith
  have h4 : (windowMeasure (T n)).real S < δ / 6 := hS ▸ h2
  have h5 := norm_sub_le_norm_sub_add_norm_sub
    (charFun ((windowLaw (hT n) (g n) (hg n) : ProbabilityMeasure ℝ) : Measure ℝ) u)
    (charFun ((windowLaw (hT n) (f n) (hf n) : ProbabilityMeasure ℝ) : Measure ℝ) u)
    (charFun (μ : Measure ℝ) u)
  linarith

/-- A subset of the window controls the window measure. -/
theorem windowMeasure_real_le {T : ℝ} (hT : 0 < T) {S V : Set ℝ}
    (hSV : ∀ t ∈ Ioc T (T + T), t ∈ S → t ∈ V) {a : ℝ} (ha : 0 ≤ a)
    (hV : volume V ≤ ENNReal.ofReal a) :
    (windowMeasure T).real S ≤ T⁻¹ * a := by
  have h1 : windowMeasure T S ≤ ENNReal.ofReal T⁻¹ * ENNReal.ofReal a := by
    simp only [windowMeasure, Measure.smul_apply, smul_eq_mul]
    refine mul_le_mul_right ?_ _
    rw [Measure.restrict_apply' measurableSet_Ioc]
    refine (measure_mono fun t ht => hSV t ht.2 ht.1).trans hV
  rw [← ENNReal.ofReal_mul (by positivity)] at h1
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rwa [ENNReal.toReal_ofReal (by positivity)] at h2

/-! ### The polynomial difference -/

/-- `W_x(n) = 1` for `n ≤ x`. -/
theorem selbergWeight_eq_one {x : ℝ} (hx : 1 < x) {n : ℕ} (hn1 : 1 ≤ n) (hn : (n : ℝ) ≤ x) :
    selbergWeight x n = 1 := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  unfold selbergWeight
  have h1 : 0 ≤ Real.log (x / n) := Real.log_nonneg (by rwa [le_div_iff₀ hn0, one_mul])
  have h2 : 0 ≤ Real.log (x ^ 2 / n) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hn0, one_mul]
    nlinarith
  rw [max_eq_left h1, max_eq_left h2, Real.log_div (by positivity) hn0.ne',
    Real.log_div hx0.ne' hn0.ne', Real.log_pow]
  push_cast
  field_simp
  ring

/-- The coefficient of `Re P_x(½ + R + it) − Σ_{p ≤ Y} p^{−1/2} cos(t log p)` on the line. -/
def polyDiffCoeff (x R : ℝ) (Y n : ℕ) : ℂ :=
  ((logPolyCoeff x n * (n : ℝ) ^ (-R) - if n.Prime ∧ n ≤ Y then 1 else 0 : ℝ) : ℂ)

/-- A prime power carries at least `log 2`. -/
theorem log_two_le_vonMangoldt {n : ℕ} (h : (vonMangoldt n : ℝ) ≠ 0) :
    Real.log 2 ≤ vonMangoldt n := by
  have hpp : IsPrimePow n := vonMangoldt_ne_zero_iff.mp h
  rw [vonMangoldt_apply, if_pos hpp]
  have h2 : 2 ≤ n.minFac := (Nat.minFac_prime hpp.ne_one).two_le
  exact Real.log_le_log (by norm_num) (by exact_mod_cast h2)

/-- The coefficient of the critical polynomial is bounded by the von Mangoldt weight. -/
theorem logPolyCoeff_sq_le {x : ℝ} (hx : 1 < x) (n : ℕ) :
    logPolyCoeff x n ^ 2 ≤ vonMangoldt n / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases h : (vonMangoldt n : ℝ) = 0
  · unfold logPolyCoeff
    rw [h]
    simp
  · have h1 : 1 ≤ (vonMangoldt n : ℝ) / Real.log 2 :=
      (one_le_div hl2).mpr (log_two_le_vonMangoldt h)
    have h2 := abs_logPolyCoeff_le hx n
    have h3 : logPolyCoeff x n ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) h2
    linarith

/-- A nonprime index only carries its von Mangoldt weight. -/
theorem polyDiffCoeff_nonprime_term_le {x R : ℝ} (hx : 1 < x) (hR : 0 ≤ R) (Y : ℕ) {n : ℕ}
    (hn1 : 1 ≤ n) (hp : ¬ n.Prime) :
    ‖polyDiffCoeff x R Y n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) ≤
      (1 / Real.log 2) * (vonMangoldt n * (n : ℝ) ^ (-(1 / 2 + 1 / 2) : ℝ)) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (n : ℝ) ^ (-R) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
  have hpow0 : 0 ≤ (n : ℝ) ^ (-R) := Real.rpow_nonneg hn0.le _
  unfold polyDiffCoeff
  have hif : ¬ (n.Prime ∧ n ≤ Y) := fun h => hp h.1
  rw [if_neg hif, sub_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  have h1 := logPolyCoeff_sq_le hx n
  have h2 : ((n : ℝ) ^ (-R)) ^ 2 ≤ 1 := pow_le_one₀ hpow0 hpow
  have h3 : logPolyCoeff x n ^ 2 * ((n : ℝ) ^ (-R)) ^ 2 ≤ vonMangoldt n / Real.log 2 := by
    calc logPolyCoeff x n ^ 2 * ((n : ℝ) ^ (-R)) ^ 2 ≤ logPolyCoeff x n ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact h1
  have e1 : (2 * (0 : ℝ) - 1) = -(1 / 2 + 1 / 2) := by norm_num
  rw [e1]
  have hp0 : 0 ≤ (n : ℝ) ^ (-(1 / 2 + 1 / 2) : ℝ) := Real.rpow_nonneg hn0.le _
  calc _ ≤ vonMangoldt n / Real.log 2 * (n : ℝ) ^ (-(1 / 2 + 1 / 2) : ℝ) :=
        mul_le_mul_of_nonneg_right h3 hp0
    _ = _ := by ring

/-- A prime `p ≤ Y` moves by `R log p`. -/
theorem polyDiffCoeff_small_prime_term_le {x R : ℝ} (hx : 1 < x) (hR : 0 ≤ R) {Y n : ℕ}
    (hYx : (Y : ℝ) ≤ x) (hp : n.Prime) (hnY : n ≤ Y) :
    ‖polyDiffCoeff x R Y n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) ≤
      R ^ 2 * (vonMangoldt n ^ 2 / (n : ℝ)) := by
  have hn1 : 1 ≤ n := hp.one_lt.le
  have hn : (1 : ℝ) < n := by exact_mod_cast hp.one_lt
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos hn
  have hW : selbergWeight x n = 1 :=
    selbergWeight_eq_one hx hn1 (le_trans (by exact_mod_cast hnY) hYx)
  have hc : logPolyCoeff x n = 1 := by
    unfold logPolyCoeff
    rw [hW, vonMangoldt_apply_prime hp]
    field_simp
  unfold polyDiffCoeff
  rw [if_pos ⟨hp, hnY⟩, hc, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hexp : (n : ℝ) ^ (-R) = Real.exp (-(R * Real.log n)) := by
    rw [Real.rpow_def_of_pos hn0]
    congr 1
    ring
  have hy : 0 ≤ R * Real.log n := by positivity
  have h1 : 1 - Real.exp (-(R * Real.log n)) ≤ R * Real.log n := by
    linarith [Real.add_one_le_exp (-(R * Real.log n))]
  have h2 : Real.exp (-(R * Real.log n)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsq : ((n : ℝ) ^ (-R) - 1) ^ 2 ≤ (R * Real.log n) ^ 2 := by
    rw [hexp, show (Real.exp (-(R * Real.log n)) - 1) ^ 2 =
      (1 - Real.exp (-(R * Real.log n))) ^ 2 by ring]
    exact pow_le_pow_left₀ (by linarith) h1 2
  have e1 : (n : ℝ) ^ (2 * (0 : ℝ) - 1) = (n : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one]
    norm_num
  rw [e1, vonMangoldt_apply_prime hp, div_eq_mul_inv]
  calc ((n : ℝ) ^ (-R) - 1) ^ 2 * (n : ℝ)⁻¹ ≤ (R * Real.log n) ^ 2 * (n : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr hn0.le)
    _ = _ := by ring

/-- A prime `p > Y` only carries its reciprocal mass. -/
theorem polyDiffCoeff_large_prime_term_le {x R : ℝ} (hx : 1 < x) (hR : 0 ≤ R) {Y n : ℕ}
    (hp : n.Prime) (hnY : ¬ n ≤ Y) :
    ‖polyDiffCoeff x R Y n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) ≤ 1 / (n : ℝ) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hp.one_lt.le
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow : (n : ℝ) ^ (-R) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
  have hpow0 : 0 ≤ (n : ℝ) ^ (-R) := Real.rpow_nonneg hn0.le _
  unfold polyDiffCoeff
  have hif : ¬ (n.Prime ∧ n ≤ Y) := fun h => hnY h.2
  rw [if_neg hif, sub_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have e1 : (n : ℝ) ^ (2 * (0 : ℝ) - 1) = 1 / (n : ℝ) := by
    rw [one_div, ← Real.rpow_neg_one]
    norm_num
  rw [e1]
  have h1 := abs_logPolyCoeff_le hx n
  have h2 : (logPolyCoeff x n * (n : ℝ) ^ (-R)) ^ 2 ≤ 1 := by
    rw [← sq_abs, abs_mul, abs_of_nonneg hpow0]
    refine pow_le_one₀ (by positivity) (mul_le_one₀ h1 hpow0 hpow)
  exact mul_le_of_le_one_left (by positivity) h2

/-- **The coefficient energy of the polynomial difference.** The primes up to `Y` contribute
`R² log Y (log Y + C)`, the primes between `Y` and `N` their reciprocal mass, and the proper prime
powers a constant. -/
theorem sum_polyDiffCoeff_sq_le {x R CΛ : ℝ} {Y N : ℕ} (hx : 1 < x) (hR : 0 ≤ R)
    (hYx : (Y : ℝ) ≤ x) (hYN : Y ≤ N)
    (hC : ∑ k ∈ Finset.Icc 1 Y, (vonMangoldt k) ^ (2 : ℕ) / (k : ℝ) ≤
      Real.log (Y : ℝ) * (Real.log (Y : ℝ) + CΛ)) :
    ∑ n ∈ Finset.Icc 1 N, ‖polyDiffCoeff x R Y n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) ≤
      72 / Real.log 2 + R ^ 2 * (Real.log (Y : ℝ) * (Real.log (Y : ℝ) + CΛ)) +
        (Sieve.mertensS N - Sieve.mertensS Y) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) Nat.Prime]
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 N).filter Nat.Prime)
    (fun n => n ≤ Y)]
  have hA : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Prime),
      ‖polyDiffCoeff x R Y n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) ≤ 72 / Real.log 2 := by
    have h := sum_nonprime_vonMangoldt_rpow_le (δ := 1 / 2) (by norm_num) (by norm_num) N
    calc _ ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Prime),
          (1 / Real.log 2) * (vonMangoldt n * (n : ℝ) ^ (-(1 / 2 + 1 / 2) : ℝ)) :=
          Finset.sum_le_sum fun n hn => polyDiffCoeff_nonprime_term_le hx hR Y
            (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1 (Finset.mem_filter.mp hn).2
      _ = (1 / Real.log 2) * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ n.Prime),
          (vonMangoldt n * (n : ℝ) ^ (-(1 / 2 + 1 / 2) : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ (1 / Real.log 2) * (36 / (1 / 2)) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 72 / Real.log 2 := by ring
  have hB : ∑ n ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun n => n ≤ Y),
      ‖polyDiffCoeff x R Y n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) ≤
      R ^ 2 * (Real.log (Y : ℝ) * (Real.log (Y : ℝ) + CΛ)) := by
    calc _ ≤ ∑ n ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun n => n ≤ Y),
          R ^ 2 * (vonMangoldt n ^ 2 / (n : ℝ)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hn
          exact polyDiffCoeff_small_prime_term_le hx hR hYx
            (Finset.mem_filter.mp h1).2 h2
      _ = R ^ 2 * ∑ n ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun n => n ≤ Y),
          (vonMangoldt n ^ 2 / (n : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (le_trans ?_ hC) (sq_nonneg R)
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => by positivity
          intro n hn
          obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hn
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp h1).1).1, h2⟩
  have hD : ∑ n ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun n => ¬ n ≤ Y),
      ‖polyDiffCoeff x R Y n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) ≤
      Sieve.mertensS N - Sieve.mertensS Y := by
    have hsub : primesUpTo Y ⊆ primesUpTo N := by
      intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
      obtain ⟨h3, h4⟩ := Finset.mem_Icc.mp h1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3, h4.trans hYN⟩, h2⟩
    have hdiff : Sieve.mertensS N - Sieve.mertensS Y =
        ∑ p ∈ primesUpTo N \ primesUpTo Y, 1 / (p : ℝ) := by
      rw [← sum_primesUpTo_inv, ← sum_primesUpTo_inv, ← Finset.sum_sdiff hsub]
      ring
    rw [hdiff]
    calc _ ≤ ∑ n ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun n => ¬ n ≤ Y),
          1 / (n : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hn
          exact polyDiffCoeff_large_prime_term_le hx hR (Finset.mem_filter.mp h1).2 h2
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => by positivity
          intro n hn
          obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hn
          obtain ⟨h3, h4⟩ := Finset.mem_filter.mp h1
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨h3, h4⟩, fun hY => ?_⟩
          exact h2 (Finset.mem_Icc.mp (Finset.mem_filter.mp hY).1).2
  refine le_trans (le_of_eq ?_) (le_trans (add_le_add (add_le_add hB hD) hA) (le_of_eq (by ring)))
  congr!

/-- The Dirichlet polynomial `Σ_n b_n n^{−1/2−it}` whose real part is the polynomial difference. -/
def polyDiff (x R : ℝ) (Y : ℕ) (t : ℝ) : ℂ :=
  edPoly (polyDiffCoeff x R Y) (Finset.Icc 1 (selbergPolyLength x)) (displacedLinePt 0 t)

theorem continuous_polyDiff (x R : ℝ) (Y : ℕ) : Continuous (polyDiff x R Y) := by
  unfold polyDiff
  refine (differentiable_edPoly _ fun n hn => (Finset.mem_Icc.mp hn).1).continuous.comp ?_
  unfold displacedLinePt
  fun_prop

/-- The real part of a prime term of the critical polynomial. -/
theorem re_cpow_critical {p : ℕ} (hp : 1 ≤ p) (t : ℝ) :
    (((p : ℝ) : ℂ) ^ (-displacedLinePt 0 t)).re = halfWeight p * Real.cos (t * Real.log p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hne : ((p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp0.ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hp0.le]
  have e : ((Real.log p : ℝ) : ℂ) * (-displacedLinePt 0 t) =
      ((-(1 / 2) * Real.log p : ℝ) : ℂ) + ((-(t * Real.log p) : ℝ) : ℂ) * I := by
    unfold displacedLinePt
    push_cast
    ring
  rw [e, Complex.exp_add, ← Complex.ofReal_exp, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  unfold halfWeight
  rw [Real.rpow_def_of_pos hp0]
  congr 2
  ring

/-- Off the line, the same term carries the extra damping `n^{−R}`. -/
theorem cpow_shift_eq {n : ℕ} (hn : 1 ≤ n) (R t : ℝ) :
    ((n : ℝ) : ℂ) ^ (-(((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)) =
      (((n : ℝ) ^ (-R) : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (-displacedLinePt 0 t) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn0.ne'
  rw [Complex.ofReal_cpow hn0.le, ← Complex.cpow_add _ _ hne]
  congr 1
  unfold displacedLinePt
  push_cast
  ring

/-- **The polynomial difference.** For `Y ≤ N_x`, the real part of `polyDiff` is
`Re P_x(½ + R + it) − Σ_{p ≤ Y} p^{−1/2} cos(t log p)`. -/
theorem re_polyDiff_eq {x R : ℝ} {Y : ℕ} (hY : Y ≤ selbergPolyLength x) (t : ℝ) :
    (polyDiff x R Y t).re = (logPoly x (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)).re -
      primeField halfWeight (primesUpTo Y) t := by
  classical
  unfold polyDiff logPoly edPoly polyDiffCoeff primeField
  rw [Complex.re_sum, Complex.re_sum]
  have hprime : ∑ p ∈ primesUpTo Y, halfWeight p * Real.cos (t * Real.log p) =
      ∑ n ∈ Finset.Icc 1 (selbergPolyLength x),
        (if n.Prime ∧ n ≤ Y then 1 else 0) * (((n : ℝ) : ℂ) ^ (-displacedLinePt 0 t)).re := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    have hset : (Finset.Icc 1 (selbergPolyLength x)).filter (fun n => n.Prime ∧ n ≤ Y) =
        primesUpTo Y := by
      ext n
      simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3, h4⟩
        exact ⟨⟨h1, h4⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, h2.trans hY⟩, h3, h2⟩
    rw [hset]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [re_cpow_critical (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1]
  rw [hprime, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 := (Finset.mem_Icc.mp hn).1
  rw [cpow_shift_eq hn1, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]
  ring

/-- **The mean square of the polynomial difference.** -/
theorem integral_normSq_polyDiff_le {x R : ℝ} {Y : ℕ} {T : ℝ} :
    ∫ t in T..(2 * T), ‖polyDiff x R Y t‖ ^ 2 ≤
      (T + 8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x))) *
        ∑ n ∈ Finset.Icc 1 (selbergPolyLength x),
          ‖polyDiffCoeff x R Y n‖ ^ 2 * (n : ℝ) ^ (2 * (0 : ℝ) - 1) := by
  have h := integral_normSq_edPoly_displaced_le 0 (polyDiffCoeff x R Y) (selbergPolyLength x) T
    (2 * T)
  rw [show 2 * T - T = T by ring] at h
  exact h

/-! ### The parameters -/

/-- The double logarithm `log log T`. -/
def dlog (T : ℝ) : ℝ := Real.log (Real.log T)

theorem tendsto_dlog : Tendsto dlog atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

/-- The depth `κ = (log log T)^{1/4}` of the off-line point. -/
def shiftDepth (T : ℝ) : ℝ := Real.sqrt (Real.sqrt (dlog T))

/-- The off-line displacement `R = κ/log T`. -/
def shiftR (T : ℝ) : ℝ := shiftDepth T / Real.log T

/-- The length `Y = ⌊e^{log T/log log T}⌋ + 1` of the Gaussian prime sum. -/
def primeLength (T : ℝ) : ℕ := ⌊Real.exp (Real.log T / dlog T)⌋₊ + 1

/-- The length `x = T^{1/30000}` of the explicit formula. -/
def formulaLength (T : ℝ) : ℝ := Real.exp (Real.log T / 30000)

/-- The prime sum at height `T`. -/
def criticalPrimeSum (T t : ℝ) : ℝ := primeField halfWeight (primesUpTo (primeLength T)) t

/-- The normalization `√(½ log log T)`. -/
def criticalScale (T : ℝ) : ℝ := Real.sqrt (dlog T / 2)

theorem tendsto_shiftDepth : Tendsto shiftDepth atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_dlog)

theorem tendsto_criticalScale : Tendsto criticalScale atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (tendsto_dlog.atTop_div_const two_pos)

theorem sqrt_le_self_of_one_le {a : ℝ} (ha : 1 ≤ a) : Real.sqrt a ≤ a :=
  Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩

/-- `κ ≤ log log T` once `log log T ≥ 1`. -/
theorem shiftDepth_le_dlog {T : ℝ} (hT : 1 ≤ dlog T) : shiftDepth T ≤ dlog T := by
  unfold shiftDepth
  have h1 : Real.sqrt (dlog T) ≤ dlog T := sqrt_le_self_of_one_le hT
  have h2 : 1 ≤ Real.sqrt (dlog T) := Real.one_le_sqrt.mpr hT
  exact (sqrt_le_self_of_one_le h2).trans h1

/-- `κ/σ → 0`. -/
theorem tendsto_shiftDepth_div_scale :
    Tendsto (fun T => shiftDepth T / criticalScale T) atTop (𝓝 0) := by
  have hkey : Tendsto (fun u : ℝ => Real.sqrt 2 * (Real.sqrt (Real.sqrt u))⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      Real.tendsto_sqrt_atTop)).const_mul (Real.sqrt 2)
    simpa using h
  refine (hkey.comp tendsto_dlog).congr' ?_
  filter_upwards [tendsto_dlog.eventually_gt_atTop 0] with T hT
  simp only [Function.comp_apply]
  unfold shiftDepth criticalScale
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Real.sqrt (Real.sqrt (dlog T)) := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [ha]
    exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hT)
  have hd : dlog T = a ^ 4 := by
    rw [ha, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt hT.le]
  rw [← ha]
  have hsq : Real.sqrt (dlog T / 2) = a ^ 2 / Real.sqrt 2 := by
    rw [hd, Real.sqrt_div (by positivity), show a ^ 4 = (a ^ 2) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [hsq]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

/-- `V/σ² → 0` for `V = C + log log log T`. -/
theorem tendsto_energy_div_scale_sq (C : ℝ) :
    Tendsto (fun T => (C + Real.log (dlog T)) / criticalScale T ^ 2) atTop (𝓝 0) := by
  have hkey : Tendsto (fun u : ℝ => 2 * ((C + Real.log u) / u)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => C / u) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h4 := ((h1.add h2).const_mul 2)
    rw [add_zero, mul_zero] at h4
    refine h4.congr' ?_
    filter_upwards with u
    ring
  refine (hkey.comp tendsto_dlog).congr' ?_
  filter_upwards [tendsto_dlog.eventually_gt_atTop 0] with T hT
  simp only [Function.comp_apply]
  unfold criticalScale
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- `log log T` is arbitrarily small against `log T`. -/
theorem eventually_mul_dlog_le (K : ℝ) (hK : 0 < K) : ∀ᶠ T in atTop, K * dlog T ≤ Real.log T := by
  have h := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / K by positivity)
  filter_upwards [Real.tendsto_log_atTop.eventually h,
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT hL
  simp only [id, Real.norm_eq_abs] at hT
  rw [abs_of_pos hL] at hT
  have h2 := (le_abs_self _).trans hT
  have h3 := mul_le_mul_of_nonneg_left h2 hK.le
  have e : K * (1 / K * Real.log T) = Real.log T := by field_simp
  rw [e] at h3
  exact h3

/-! ### The prime length and the formula length -/

/-- The sizes of `Y`: `e^{L/u} ≤ Y ≤ 2 e^{L/u}`, `L/u ≤ log Y ≤ 2L/u`. -/
theorem primeLength_bounds {T : ℝ} (hu : 0 < dlog T)
    (hLu : 4 * dlog T ≤ Real.log T) :
    Real.exp (Real.log T / dlog T) ≤ primeLength T ∧
      (primeLength T : ℝ) ≤ 2 * Real.exp (Real.log T / dlog T) ∧
      Real.log T / dlog T ≤ Real.log (primeLength T) ∧
      Real.log (primeLength T) ≤ 2 * (Real.log T / dlog T) := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.log T / dlog T := ⟨_, rfl⟩
  rw [← hy]
  have hy4 : 4 ≤ y := by
    rw [hy, le_div_iff₀ hu]
    exact hLu
  have hexp1 : 1 ≤ Real.exp y := Real.one_le_exp (by linarith)
  have h0 : 0 ≤ Real.exp y := (Real.exp_pos y).le
  have hlow : Real.exp y ≤ primeLength T := by
    unfold primeLength
    rw [← hy]
    push_cast
    exact (Nat.lt_floor_add_one _).le
  have hup : (primeLength T : ℝ) ≤ 2 * Real.exp y := by
    unfold primeLength
    rw [← hy]
    push_cast
    have := Nat.floor_le h0
    linarith
  have hpos : (0 : ℝ) < primeLength T := lt_of_lt_of_le (Real.exp_pos y) hlow
  refine ⟨hlow, hup, ?_, ?_⟩
  · have := Real.log_le_log (Real.exp_pos y) hlow
    rwa [Real.log_exp] at this
  · have h1 := Real.log_le_log hpos hup
    rw [Real.log_mul (by norm_num) (Real.exp_pos y).ne', Real.log_exp] at h1
    have h2 := Real.log_two_lt_d9
    linarith

/-- `x = T^{1/30000}` dominates `Y`. -/
theorem primeLength_le_formulaLength {T : ℝ} (hL : 0 < Real.log T) (hu : 60000 ≤ dlog T)
    (hLu : 4 * dlog T ≤ Real.log T) : (primeLength T : ℝ) ≤ formulaLength T := by
  have hu0 : 0 < dlog T := by linarith
  obtain ⟨-, h1, -, -⟩ := primeLength_bounds hu0 hLu
  refine h1.trans ?_
  unfold formulaLength
  have hL6 : 240000 ≤ Real.log T := by linarith
  have h2 : Real.log T / dlog T ≤ Real.log T / 60000 :=
    div_le_div_of_nonneg_left hL.le (by norm_num) hu
  have h3 : (2 : ℝ) ≤ Real.exp (Real.log T / 60000) := by
    have := Real.add_one_le_exp (Real.log T / 60000)
    have : (4 : ℝ) ≤ Real.log T / 60000 := by
      rw [le_div_iff₀ (by norm_num)]
      linarith
    linarith
  calc 2 * Real.exp (Real.log T / dlog T)
      ≤ Real.exp (Real.log T / 60000) * Real.exp (Real.log T / 60000) :=
        mul_le_mul h3 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring

theorem one_lt_formulaLength {T : ℝ} (hL : 0 < Real.log T) : 1 < formulaLength T :=
  Real.one_lt_exp_iff.mpr (by positivity)

/-- The length `N_x` is at most `2 T^{1/15000}`, and at least `x`. -/
theorem selbergPolyLength_bounds {T : ℝ} (hL : 0 < Real.log T) :
    formulaLength T ≤ selbergPolyLength (formulaLength T) ∧
      (selbergPolyLength (formulaLength T) : ℝ) ≤ 2 * Real.exp (Real.log T / 15000) := by
  have hx := one_lt_formulaLength hL
  have hsq : formulaLength T ^ 2 = Real.exp (Real.log T / 15000) := by
    unfold formulaLength
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h1 : formulaLength T ^ 2 ≤ selbergPolyLength (formulaLength T) := Nat.le_ceil _
  have h2 : (selbergPolyLength (formulaLength T) : ℝ) < formulaLength T ^ 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h3 : (1 : ℝ) ≤ formulaLength T ^ 2 := by nlinarith
  refine ⟨by nlinarith, ?_⟩
  rw [← hsq]
  linarith

/-- The mean-value error is absorbed by the window. -/
theorem meanValue_error_le {T : ℝ} (hT : 0 < T) (hL : 8 ≤ Real.log T) :
    (T + 8 * selbergPolyLength (formulaLength T) * (1 + Real.log (selbergPolyLength (formulaLength T))))
      ≤ 2 * T := by
  have hL0 : 0 < Real.log T := by linarith
  obtain ⟨h1, h2⟩ := selbergPolyLength_bounds hL0
  have hx := one_lt_formulaLength hL0
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (selbergPolyLength (formulaLength T) : ℝ) := ⟨_, rfl⟩
  rw [← hN] at h1 h2 ⊢
  have hN1 : 1 < N := by linarith
  have hlog : 1 + Real.log N ≤ N := by
    have := Real.log_le_sub_one_of_pos (show 0 < N by linarith)
    linarith
  have hexp : 8 * (2 * Real.exp (Real.log T / 15000)) ^ 2 ≤ T := by
    have hT' : Real.exp (Real.log T) = T := Real.exp_log hT
    have e : (2 * Real.exp (Real.log T / 15000)) ^ 2 =
        4 * Real.exp (Real.log T / 7500) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
      ring_nf
    rw [e]
    have h32 : (32 : ℝ) ≤ Real.exp (7499 / 7500 * Real.log T) := by
      have h3 := Real.add_one_le_exp (7499 / 7500 * Real.log T)
      have h4 : Real.exp 1 ≥ 2 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have h5 : (5 : ℝ) ≤ 7499 / 7500 * Real.log T := by linarith
      have h6 : Real.exp 5 ≤ Real.exp (7499 / 7500 * Real.log T) := Real.exp_le_exp.mpr h5
      have h7 : (32 : ℝ) ≤ Real.exp 5 := by
        have h8 : Real.exp 5 = Real.exp 1 ^ (5 : ℕ) := by
          rw [← Real.exp_nat_mul]
          norm_num
        rw [h8]
        calc (32 : ℝ) = 2 ^ (5 : ℕ) := by norm_num
          _ ≤ _ := pow_le_pow_left₀ (by norm_num) h4 5
      linarith
    have hsplit : T = Real.exp (Real.log T / 7500) * Real.exp (7499 / 7500 * Real.log T) := by
      rw [← Real.exp_add]
      nth_rewrite 1 [← hT']
      congr 1
      ring
    calc 8 * (4 * Real.exp (Real.log T / 7500))
        = Real.exp (Real.log T / 7500) * 32 := by ring
      _ ≤ Real.exp (Real.log T / 7500) * Real.exp (7499 / 7500 * Real.log T) :=
          mul_le_mul_of_nonneg_left h32 (Real.exp_pos _).le
      _ = T := hsplit.symm
  have hNsq : 8 * N * (1 + Real.log N) ≤ 8 * (2 * Real.exp (Real.log T / 15000)) ^ 2 := by
    have h3 : N * (1 + Real.log N) ≤ N * N :=
      mul_le_mul_of_nonneg_left hlog (by linarith)
    have h4 : N * N ≤ (2 * Real.exp (Real.log T / 15000)) ^ 2 := by
      rw [sq]
      exact mul_le_mul h2 h2 (by linarith) (by positivity)
    nlinarith
  linarith

/-! ### The energy of the polynomial difference -/

/-- The small-prime part of the energy is bounded. -/
theorem small_prime_energy_le {R y lY CΛ : ℝ} (hR : 0 ≤ R) (hy : 0 < y) (hRy : R * y ≤ 1)
    (hRC : R * |CΛ| ≤ 1) (h0 : 0 ≤ lY) (hl : lY ≤ 2 * y) :
    R ^ 2 * (lY * (lY + CΛ)) ≤ 6 := by
  have h1 : lY + CΛ ≤ 2 * y + |CΛ| := by
    have := le_abs_self CΛ
    linarith
  have h2 : lY * (lY + CΛ) ≤ 2 * y * (2 * y + |CΛ|) := by
    calc lY * (lY + CΛ) ≤ lY * (2 * y + |CΛ|) := mul_le_mul_of_nonneg_left h1 h0
      _ ≤ 2 * y * (2 * y + |CΛ|) :=
          mul_le_mul_of_nonneg_right hl (by positivity)
  have h3 : R ^ 2 * (2 * y * (2 * y + |CΛ|)) = 4 * (R * y) ^ 2 + 2 * (R * y) * (R * |CΛ|) := by
    ring
  have h4 : (R * y) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hRy
  have h5 : (R * y) * (R * |CΛ|) ≤ 1 := mul_le_one₀ hRy (by positivity) hRC
  calc R ^ 2 * (lY * (lY + CΛ)) ≤ R ^ 2 * (2 * y * (2 * y + |CΛ|)) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg R)
    _ ≤ 6 := by
        rw [h3]
        nlinarith

/-- `log log N − log log Y ≤ log log log T`. -/
theorem logLog_sub_le {T : ℝ} (hL : 8 ≤ Real.log T) (hu : 60000 ≤ dlog T)
    (hLu : 4 * dlog T ≤ Real.log T) :
    Real.log (Real.log (selbergPolyLength (formulaLength T))) -
        Real.log (Real.log (primeLength T)) ≤ Real.log (dlog T) := by
  have hL0 : 0 < Real.log T := by linarith
  have hu0 : 0 < dlog T := by linarith
  obtain ⟨-, -, hY3, -⟩ := primeLength_bounds hu0 hLu
  obtain ⟨h1, h2⟩ := selbergPolyLength_bounds hL0
  have hx := one_lt_formulaLength hL0
  have hN1 : (1 : ℝ) < selbergPolyLength (formulaLength T) := by linarith
  have hlogN : Real.log (selbergPolyLength (formulaLength T)) ≤ Real.log T := by
    have h3 := Real.log_le_log (by linarith) h2
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h3
    have := Real.log_two_lt_d9
    linarith
  have hlogN0 : 0 < Real.log (selbergPolyLength (formulaLength T)) := Real.log_pos hN1
  have hA : Real.log (Real.log (selbergPolyLength (formulaLength T))) ≤ dlog T :=
    Real.log_le_log hlogN0 hlogN
  have hy0 : 0 < Real.log T / dlog T := by positivity
  have hB : dlog T - Real.log (dlog T) ≤ Real.log (Real.log (primeLength T)) := by
    have h3 := Real.log_le_log hy0 hY3
    rw [Real.log_div hL0.ne' hu0.ne'] at h3
    exact h3
  linarith

/-- **The energy of the polynomial difference is `O(log log log T)`.** -/
theorem exists_energy_polyDiff_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∑ n ∈ Finset.Icc 1 (selbergPolyLength (formulaLength T)),
        ‖polyDiffCoeff (formulaLength T) (shiftR T) (primeLength T) n‖ ^ 2 *
          (n : ℝ) ^ (2 * (0 : ℝ) - 1) ≤ C + Real.log (dlog T) := by
  obtain ⟨CΛ, hCΛ⟩ := exists_sum_vonMangoldt_sq_div_le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨72 / Real.log 2 + 6 + (|Sieve.mertensSecondUpperConst| + |Sieve.mertensSecondLowerConst|) + 1,
    by positivity, ?_⟩
  filter_upwards [tendsto_dlog.eventually_ge_atTop 60000, eventually_mul_dlog_le 4 (by norm_num),
    eventually_mul_dlog_le (|CΛ| + 1) (by positivity)] with T hu hLu hLC
  have hu0 : 0 < dlog T := by linarith
  have hL6 : 240000 ≤ Real.log T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  obtain ⟨hY0, hY2, hY3, hY4⟩ := primeLength_bounds hu0 hLu
  have hx := one_lt_formulaLength hL0
  have hYx := primeLength_le_formulaLength hL0 hu hLu
  obtain ⟨hN1, hN2⟩ := selbergPolyLength_bounds hL0
  have hYN : primeLength T ≤ selbergPolyLength (formulaLength T) := by
    exact_mod_cast hYx.trans hN1
  have hk0 : 0 ≤ shiftDepth T := Real.sqrt_nonneg _
  have hk : shiftDepth T ≤ dlog T := shiftDepth_le_dlog (by linarith)
  have hR : 0 ≤ shiftR T := by
    unfold shiftR
    positivity
  have hY1 : 1 ≤ primeLength T := Nat.succ_le_succ (Nat.zero_le _)
  have hV := sum_polyDiffCoeff_sq_le (R := shiftR T) hx hR hYx hYN (hCΛ _ hY1)
  refine hV.trans ?_
  have hy0 : 0 < Real.log T / dlog T := by positivity
  have hRy : shiftR T * (Real.log T / dlog T) ≤ 1 := by
    unfold shiftR
    have e : shiftDepth T / Real.log T * (Real.log T / dlog T) = shiftDepth T / dlog T := by
      field_simp
    rw [e, div_le_one hu0]
    exact hk
  have hRC : shiftR T * |CΛ| ≤ 1 := by
    unfold shiftR
    rw [div_mul_eq_mul_div, div_le_one hL0]
    have h1 : shiftDepth T * |CΛ| ≤ dlog T * |CΛ| :=
      mul_le_mul_of_nonneg_right hk (abs_nonneg _)
    nlinarith
  have hsmall := small_prime_energy_le (CΛ := CΛ) hR hy0 hRy hRC
    (hy0.le.trans hY3) hY4
  -- Mertens
  have hNnat : 2 ≤ selbergPolyLength (formulaLength T) := by
    have h1 : (1 : ℝ) < selbergPolyLength (formulaLength T) := by linarith
    exact_mod_cast h1
  have hYnat : 2 ≤ primeLength T := by
    have h1 : (1 : ℝ) < primeLength T := by
      have := Real.one_lt_exp_iff.mpr hy0
      linarith
    exact_mod_cast h1
  have hM1 := Sieve.mertensS_le hNnat
  have hM2 := Sieve.le_mertensS hYnat
  have hll := logLog_sub_le (by linarith) hu hLu
  have hU := le_abs_self Sieve.mertensSecondUpperConst
  have hLo := le_abs_self Sieve.mertensSecondLowerConst
  unfold Sieve.logLog at hM1 hM2
  linarith

/-- The heights where the polynomial difference is large. -/
theorem volume_re_polyDiff_ge_le {T V c : ℝ} (hT : 0 < T) (hL : 8 ≤ Real.log T) (hc : 0 < c)
    (hV0 : 0 ≤ ∑ n ∈ Finset.Icc 1 (selbergPolyLength (formulaLength T)),
        ‖polyDiffCoeff (formulaLength T) (shiftR T) (primeLength T) n‖ ^ 2 *
          (n : ℝ) ^ (2 * (0 : ℝ) - 1))
    (hV : ∑ n ∈ Finset.Icc 1 (selbergPolyLength (formulaLength T)),
        ‖polyDiffCoeff (formulaLength T) (shiftR T) (primeLength T) n‖ ^ 2 *
          (n : ℝ) ^ (2 * (0 : ℝ) - 1) ≤ V) :
    volume {t | t ∈ Icc T (2 * T) ∧
        c ≤ |(polyDiff (formulaLength T) (shiftR T) (primeLength T) t).re|} ≤
      ENNReal.ofReal (2 * T * V / c ^ 2) := by
  have hcont : Continuous fun t => ‖polyDiff (formulaLength T) (shiftR T) (primeLength T) t‖ ^ 2 :=
    (continuous_polyDiff _ _ _).norm.pow 2
  have hint := (integral_normSq_polyDiff_le (x := formulaLength T) (R := shiftR T)
    (Y := primeLength T) (T := T)).trans
    (mul_le_mul (meanValue_error_le hT hL) hV hV0 (by positivity))
  have h := volume_Icc_setOf_le_le_of_integral (show T ≤ 2 * T by linarith)
    (show 0 < c ^ 2 by positivity) (fun t => sq_nonneg _) hcont hint
  refine (measure_mono ?_).trans h
  rintro t ⟨ht, hle⟩
  refine ⟨ht, ?_⟩
  have h1 := Complex.abs_re_le_norm (polyDiff (formulaLength T) (shiftR T) (primeLength T) t)
  exact pow_le_pow_left₀ hc.le (hle.trans h1) 2

/-! ### Closeness of `log|ζ|` to the prime sum -/

/-- The two-step triangle inequality for three errors. -/
theorem three_error_split {a b d c : ℝ} (h : 3 * c ≤ |a + b + d|) : c ≤ |a| ∨ c ≤ |b| ∨ c ≤ |d| := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have h4 := abs_add_three a b d
  linarith

/-- The arithmetic of the three exceptional measures. -/
theorem close_terms_le {T CA CB CV κ σ ε E ℓ s₁ s₂ c C : ℝ} (hT : 0 < T) (hCA : 0 < CA)
    (hCB : 0 < CB) (hCV : 0 < CV) (hκ : 0 ≤ κ) (hσ : 0 < σ) (hε : 0 < ε) (hE : 0 ≤ E)
    (hℓ : 0 ≤ ℓ) (hs₂ : 0 ≤ s₂) (hs : T * s₂ = s₁) (hc : c = ε * σ / 3)
    (hC : C = 3 * CA + CB + 18 + CV) :
    CA * κ * T / c + (CB * T * E + CB * s₁ + 2 * T * (CV + ℓ) / c ^ 2) ≤
      T * (C / ε * (κ / σ) + C * E + C * s₂ + C / ε ^ 2 * ((C + ℓ) / σ ^ 2)) := by
  have hc0 : c ≠ 0 := by
    rw [hc]
    positivity
  have h1 : CA * κ * T / c = T * (3 * CA / ε * (κ / σ)) := by
    rw [hc]
    field_simp
  have h2 : 2 * T * (CV + ℓ) / c ^ 2 = T * (18 / ε ^ 2 * ((CV + ℓ) / σ ^ 2)) := by
    rw [hc]
    field_simp
    ring
  have hCpos : 0 < C := by
    rw [hC]
    positivity
  have h3 : 3 * CA / ε * (κ / σ) ≤ C / ε * (κ / σ) := by
    refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ hε.le) (by positivity)
    rw [hC]
    linarith
  have h4 : CB * E ≤ C * E := by
    refine mul_le_mul_of_nonneg_right ?_ hE
    rw [hC]
    linarith
  have h5 : CB * s₂ ≤ C * s₂ := by
    refine mul_le_mul_of_nonneg_right ?_ hs₂
    rw [hC]
    linarith
  have h6 : 18 / ε ^ 2 * ((CV + ℓ) / σ ^ 2) ≤ C / ε ^ 2 * ((C + ℓ) / σ ^ 2) := by
    refine mul_le_mul (div_le_div_of_nonneg_right ?_ (by positivity))
      (div_le_div_of_nonneg_right ?_ (by positivity)) (by positivity) (by positivity)
    · rw [hC]
      linarith
    · rw [hC]
      linarith
  have e : CB * T * E + CB * s₁ = T * (CB * E + CB * s₂) := by
    rw [← hs]
    ring
  rw [h1, h2]
  have hmain := mul_le_mul_of_nonneg_left
    (show 3 * CA / ε * (κ / σ) + (CB * E + CB * s₂) + 18 / ε ^ 2 * ((CV + ℓ) / σ ^ 2) ≤
      C / ε * (κ / σ) + C * E + C * s₂ + C / ε ^ 2 * ((C + ℓ) / σ ^ 2) by linarith) hT.le
  rw [← e] at *
  nlinarith

/-- **`log|ζ(½ + it)|` is the prime sum up to `o(√(log log T))`.** -/
theorem exists_volume_log_norm_zeta_sub_primeSum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop,
      volume {t | t ∈ Icc T (2 * T) ∧ ε * criticalScale T ≤
          |Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ - criticalPrimeSum T t|} ≤
        ENNReal.ofReal (T * (C / ε * (shiftDepth T / criticalScale T) +
          C * Real.exp (-(shiftDepth T / 60000)) + C * T ^ (-(1 / 2) : ℝ) +
          C / ε ^ 2 * ((C + Real.log (dlog T)) / criticalScale T ^ 2))) := by
  obtain ⟨CA, hCA, hA⟩ := exists_volume_log_norm_zeta_shift_ge_le
  obtain ⟨C₀, CB, hC₀, hCB, hB⟩ := exists_volume_log_norm_zeta_sub_logPoly_gt_le
  obtain ⟨CV, hCV, hV⟩ := exists_energy_polyDiff_le
  refine ⟨3 * CA + CB + 18 + CV, by positivity, fun ε hε => ?_⟩
  have hσev := tendsto_criticalScale.eventually_gt_atTop (3 * C₀ / ε)
  filter_upwards [hA, hB, hV, hσev, eventually_gt_atTop 1,
    tendsto_dlog.eventually_ge_atTop 60000, eventually_mul_dlog_le 16 (by norm_num),
    tendsto_shiftDepth.eventually_ge_atTop 9600] with T hAT hBT hVT hσT hT1 hu hLu hκ
  have hT0 : 0 < T := by linarith
  have hu0 : 0 < dlog T := by linarith
  have hL6 : 960000 ≤ Real.log T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = criticalScale T := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by
    rw [hσdef]
    exact Real.sqrt_pos.mpr (by positivity)
  rw [← hσdef] at hσT ⊢
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = shiftDepth T := ⟨_, rfl⟩
  rw [← hκdef] at hκ ⊢
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ε * σ / 3 := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [hcdef]
    positivity
  have hC₀c : C₀ < c := by
    rw [hcdef, lt_div_iff₀ (by norm_num)]
    rw [div_lt_iff₀ hε] at hσT
    linarith
  have hk : κ ≤ dlog T := hκdef ▸ shiftDepth_le_dlog (by linarith)
  have hR0 : 0 < shiftR T := by
    unfold shiftR
    rw [← hκdef]
    have : 0 < κ := by linarith
    positivity
  have hRL : shiftR T * Real.log T = κ := by
    unfold shiftR
    rw [← hκdef]
    field_simp
  have hR16 : shiftR T ≤ 1 / 16 := by
    unfold shiftR
    rw [← hκdef, div_le_iff₀ hL0]
    linarith
  -- the three exceptional sets
  have hAset := hAT (shiftR T) hR0 (by linarith) c hc0
  have hBset := hBT (shiftR T) hR0 hR16 (by rw [hRL]; exact hκ)
  rw [hRL] at hBset
  have hV0 : 0 ≤ ∑ n ∈ Finset.Icc 1 (selbergPolyLength (formulaLength T)),
      ‖polyDiffCoeff (formulaLength T) (shiftR T) (primeLength T) n‖ ^ 2 *
        (n : ℝ) ^ (2 * (0 : ℝ) - 1) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hDset := volume_re_polyDiff_ge_le hT0 (by linarith) hc0 hV0 hVT
  have hYN : primeLength T ≤ selbergPolyLength (formulaLength T) := by
    have h1 := primeLength_le_formulaLength hL0 hu (by linarith)
    have h2 := (selbergPolyLength_bounds hL0).1
    exact_mod_cast h1.trans h2
  have hsub : {t | t ∈ Icc T (2 * T) ∧ ε * σ ≤
      |Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ - criticalPrimeSum T t|} ⊆
      {t | t ∈ Icc T (2 * T) ∧ c ≤
        |Real.log ‖riemannZeta (((1 / 2 + shiftR T : ℝ) : ℂ) + (t : ℂ) * I)‖ -
          Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖|} ∪
      ({t | t ∈ Icc T (2 * T) ∧ C₀ <
        |Real.log ‖riemannZeta (((1 / 2 + shiftR T : ℝ) : ℂ) + (t : ℂ) * I)‖ -
          (logPoly (Real.exp (Real.log T / 30000)) (((1 / 2 + shiftR T : ℝ) : ℂ) + (t : ℂ) * I)).re|} ∪
      {t | t ∈ Icc T (2 * T) ∧
        c ≤ |(polyDiff (formulaLength T) (shiftR T) (primeLength T) t).re|}) := by
    rintro t ⟨ht, hle⟩
    have hsplit : Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ - criticalPrimeSum T t =
        -(Real.log ‖riemannZeta (((1 / 2 + shiftR T : ℝ) : ℂ) + (t : ℂ) * I)‖ -
          Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) +
        (Real.log ‖riemannZeta (((1 / 2 + shiftR T : ℝ) : ℂ) + (t : ℂ) * I)‖ -
          (logPoly (formulaLength T) (((1 / 2 + shiftR T : ℝ) : ℂ) + (t : ℂ) * I)).re) +
        (polyDiff (formulaLength T) (shiftR T) (primeLength T) t).re := by
      rw [re_polyDiff_eq hYN]
      unfold criticalPrimeSum
      ring
    rw [hsplit] at hle
    have h3c : 3 * c = ε * σ := by
      rw [hcdef]
      ring
    rw [← h3c] at hle
    rcases three_error_split hle with h | h | h
    · rw [abs_neg] at h
      exact Or.inl ⟨ht, h⟩
    · exact Or.inr (Or.inl ⟨ht, hC₀c.trans_le h⟩)
    · exact Or.inr (Or.inr ⟨ht, h⟩)
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add hAset ((measure_union_le _ _).trans (add_le_add hBset hDset))).trans ?_
  have hlogdlog : 0 ≤ Real.log (dlog T) := Real.log_nonneg (by linarith)
  have hsq0 : 0 ≤ T ^ ((1 : ℝ) / 2) := by positivity
  have hE0 : 0 ≤ Real.exp (-(κ / 60000)) := (Real.exp_pos _).le
  have hκ0 : 0 ≤ κ := by linarith
  have hR1 : CA * shiftR T * T * Real.log T / c = CA * κ * T / c := by
    rw [← hRL]
    ring
  have hs : T * T ^ (-(1 / 2) : ℝ) = T ^ ((1 : ℝ) / 2) := by
    nth_rewrite 1 [← Real.rpow_one T]
    rw [← Real.rpow_add hT0]
    norm_num
  have hP1 : 0 ≤ CA * shiftR T * T * Real.log T / c := by positivity
  have hP2 : 0 ≤ CB * T * Real.exp (-(κ / 60000)) + CB * T ^ ((1 : ℝ) / 2) := by positivity
  have hP3 : 0 ≤ 2 * T * (CV + Real.log (dlog T)) / c ^ 2 := by positivity
  rw [← ENNReal.ofReal_add hP2 hP3, ← ENNReal.ofReal_add hP1 (add_nonneg hP2 hP3), hR1]
  refine ENNReal.ofReal_le_ofReal ?_
  have hkey := close_terms_le (T := T) (CA := CA) (CB := CB) (CV := CV) (κ := κ) (σ := σ) (ε := ε)
    (E := Real.exp (-(κ / 60000))) (ℓ := Real.log (dlog T)) (s₁ := T ^ ((1 : ℝ) / 2))
    (s₂ := T ^ (-(1 / 2) : ℝ)) (c := c) (C := 3 * CA + CB + 18 + CV) hT0 hCA hCB hCV hκ0 hσ0 hε hE0
    hlogdlog (by positivity) hs hcdef rfl
  exact hkey

/-! ### The prime sum: size of the variance and second moment -/

/-- The mass of the prime sum. -/
def primeMass (T : ℝ) : ℝ := Sieve.mertensS (primeLength T)

theorem sum_halfWeight_sq (Y : ℕ) :
    ∑ p ∈ primesUpTo Y, halfWeight p ^ 2 = Sieve.mertensS Y := by
  rw [← sum_primesUpTo_inv]
  exact Finset.sum_congr rfl fun p _ => halfWeight_sq p

theorem sum_halfWeight_le (Y : ℕ) : ∑ p ∈ primesUpTo Y, halfWeight p ≤ Y := by
  calc ∑ p ∈ primesUpTo Y, halfWeight p
      ≤ ∑ _p ∈ primesUpTo Y, (1 : ℝ) := Finset.sum_le_sum fun p _ => halfWeight_le_one p
    _ = ((primesUpTo Y).card : ℝ) := by simp
    _ ≤ ((Finset.Icc 1 Y).card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _
    _ = Y := by simp

/-- `u − log u − C ≤ W ≤ u + C`, `u = log log T`. -/
theorem exists_primeMass_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      dlog T - Real.log (dlog T) - C ≤ primeMass T ∧ primeMass T ≤ dlog T + C := by
  refine ⟨|Sieve.mertensSecondUpperConst| + |Sieve.mertensSecondLowerConst| + 1, by positivity, ?_⟩
  filter_upwards [tendsto_dlog.eventually_ge_atTop 2, eventually_mul_dlog_le 4 (by norm_num)]
    with T hu hLu
  have hu0 : 0 < dlog T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  obtain ⟨hY0, -, hY3, hY4⟩ := primeLength_bounds hu0 hLu
  have hy0 : 0 < Real.log T / dlog T := by positivity
  have hY1 : (1 : ℝ) < primeLength T := by
    have := Real.one_lt_exp_iff.mpr hy0
    linarith
  have hYnat : 2 ≤ primeLength T := by exact_mod_cast hY1
  have hM1 := Sieve.mertensS_le hYnat
  have hM2 := Sieve.le_mertensS hYnat
  unfold Sieve.logLog at hM1 hM2
  have hlog0 : 0 < Real.log (primeLength T) := Real.log_pos hY1
  have hup : Real.log (Real.log (primeLength T)) ≤ dlog T := by
    refine Real.log_le_log hlog0 (hY4.trans ?_)
    rw [← mul_div_assoc, div_le_iff₀ hu0]
    nlinarith
  have hlow : dlog T - Real.log (dlog T) ≤ Real.log (Real.log (primeLength T)) := by
    have h := Real.log_le_log hy0 hY3
    rwa [Real.log_div hL0.ne' hu0.ne'] at h
  have hU := le_abs_self Sieve.mertensSecondUpperConst
  have hLo := le_abs_self Sieve.mertensSecondLowerConst
  have hU0 := abs_nonneg Sieve.mertensSecondUpperConst
  have hLo0 := abs_nonneg Sieve.mertensSecondLowerConst
  unfold primeMass
  constructor <;> linarith

/-- `W/log log T → 1`. -/
theorem tendsto_primeMass_div_dlog : Tendsto (fun T => primeMass T / dlog T) atTop (𝓝 1) := by
  obtain ⟨C, hC, hb⟩ := exists_primeMass_bounds
  have h1 : Tendsto (fun u : ℝ => C / u) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hup : Tendsto (fun T => 1 + C / dlog T) atTop (𝓝 1) := by
    have := (h1.comp tendsto_dlog).const_add 1
    simpa using this
  have hlow : Tendsto (fun T => 1 - Real.log (dlog T) / dlog T - C / dlog T) atTop (𝓝 1) := by
    have := ((h2.comp tendsto_dlog).const_sub 1).sub (h1.comp tendsto_dlog)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [hb, tendsto_dlog.eventually_gt_atTop 0] with T hT hu
    rw [le_div_iff₀ hu]
    have e : (1 - Real.log (dlog T) / dlog T - C / dlog T) * dlog T =
        dlog T - Real.log (dlog T) - C := by
      field_simp
    rw [e]
    exact hT.1
  · filter_upwards [hb, tendsto_dlog.eventually_gt_atTop 0] with T hT hu
    rw [div_le_iff₀ hu]
    have e : (1 + C / dlog T) * dlog T = dlog T + C := by
      field_simp
    rw [e]
    exact hT.2

/-- `W → ∞`. -/
theorem tendsto_primeMass_atTop : Tendsto primeMass atTop atTop := by
  have h := tendsto_primeMass_div_dlog.pos_mul_atTop one_pos tendsto_dlog
  refine h.congr' ?_
  filter_upwards [tendsto_dlog.eventually_gt_atTop 0] with T hu
  field_simp

/-- The mismatch of the two normalizations is negligible: `W (1/√(W/2) − 1/σ)² → 0`. -/
theorem tendsto_primeMass_mul_theta_sq :
    Tendsto (fun T => primeMass T *
      (1 / Real.sqrt (primeMass T / 2) - 1 / criticalScale T) ^ 2) atTop (𝓝 0) := by
  have hr : Tendsto (fun T => 2 * (1 - Real.sqrt (primeMass T / dlog T)) ^ 2) atTop (𝓝 0) := by
    have h1 := Real.continuous_sqrt.tendsto (1 : ℝ) |>.comp tendsto_primeMass_div_dlog
    rw [Real.sqrt_one] at h1
    have h2 := ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).pow 2
    have h3 := h2.const_mul 2
    simpa using h3
  refine hr.congr' ?_
  filter_upwards [tendsto_primeMass_atTop.eventually_gt_atTop 0,
    tendsto_dlog.eventually_gt_atTop 0] with T hW hu
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Real.sqrt (primeMass T / 2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = criticalScale T := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [ha]
    exact Real.sqrt_pos.mpr (by positivity)
  have hb0 : 0 < b := by
    rw [hb]
    exact Real.sqrt_pos.mpr (by positivity)
  have ha2 : primeMass T = 2 * a ^ 2 := by
    rw [ha, Real.sq_sqrt (by positivity)]
    ring
  have hb2 : dlog T = 2 * b ^ 2 := by
    rw [hb]
    unfold criticalScale
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hs : Real.sqrt (primeMass T / dlog T) = a / b := by
    rw [ha2, hb2, show 2 * a ^ 2 / (2 * b ^ 2) = (a / b) ^ 2 by field_simp,
      Real.sqrt_sq (by positivity)]
  rw [hs, ← ha, ← hb, ha2]
  field_simp

/-- The length of the prime sum is `T^{o(1)}`. -/
theorem tendsto_primeLength_pow_div (K : ℕ) :
    Tendsto (fun T => (primeLength T : ℝ) ^ K / T) atTop (𝓝 0) := by
  have hdec : Tendsto (fun T : ℝ => T ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  refine squeeze_zero' ?_ ?_ hdec
  · filter_upwards [eventually_gt_atTop 0] with T hT
    positivity
  · filter_upwards [eventually_gt_atTop 1, tendsto_dlog.eventually_ge_atTop (4 * K + 1),
      eventually_mul_dlog_le 4 (by norm_num),
      Real.tendsto_log_atTop.eventually_ge_atTop (4 * (K * Real.log 2) + 1)] with T hT hu hLu hLK
    have hT0 : 0 < T := by linarith
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hu0 : 0 < dlog T := by linarith
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hL0 : 0 < Real.log T := by
      have : 0 ≤ 4 * (K * Real.log 2) := by positivity
      linarith
    obtain ⟨-, hY2, -, -⟩ := primeLength_bounds hu0 hLu
    have hstep : (primeLength T : ℝ) ^ K ≤ T ^ ((1 : ℝ) / 2) := by
      have h1 : (primeLength T : ℝ) ^ K ≤ (2 * Real.exp (Real.log T / dlog T)) ^ K :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hY2 K
      refine h1.trans ?_
      have e2 : (2 * Real.exp (Real.log T / dlog T)) ^ K =
          Real.exp (K * (Real.log 2 + Real.log T / dlog T)) := by
        rw [Real.exp_nat_mul, Real.exp_add, Real.exp_log (by norm_num)]
      rw [e2, Real.rpow_def_of_pos hT0]
      refine Real.exp_le_exp.mpr ?_
      have h2 : (K : ℝ) * (Real.log T / dlog T) ≤ Real.log T / 4 := by
        rw [← mul_div_assoc, div_le_iff₀ hu0]
        nlinarith
      rw [mul_add]
      linarith
    rw [div_le_iff₀ hT0]
    have e : T ^ (-(1 / 2) : ℝ) * T = T ^ ((1 : ℝ) / 2) := by
      nth_rewrite 2 [← Real.rpow_one T]
      rw [← Real.rpow_add hT0]
      norm_num
    rw [e]
    exact hstep

/-- **The second moment of the prime sum** is at most `6W + 2Y⁴/T` on `(T, 2T]`. -/
theorem integral_primeField_sq_le {T : ℝ} {Y : ℕ} (hT : 0 < T) (hY1 : 1 ≤ Y)
    (hW : 0 < Sieve.mertensS Y) :
    ∫ t in T..(T + T), primeField halfWeight (primesUpTo Y) t ^ 2 ≤
      T * (6 * Sieve.mertensS Y + 2 * (Y : ℝ) ^ 4 / T) := by
  have hP0 : ∀ p ∈ primesUpTo Y, p ≠ 0 := fun p hp => (prime_of_mem_primesUpTo hp).ne_zero
  have htrans := abs_mean_primeField_pow_sub_model_le halfWeight_nonneg hP0 hY1
    (fun p hp => le_of_mem_primesUpTo hp) hT 2
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Real.sqrt (2 / Sieve.mertensS Y) := ⟨_, rfl⟩
  have hl0 : 0 < l := by
    rw [hl]
    exact Real.sqrt_pos.mpr (by positivity)
  have hl2 : l ^ 2 = 2 / Sieve.mertensS Y := by
    rw [hl, Real.sq_sqrt (by positivity)]
  have hM := integral_modelField_even_pow_le (w := halfWeight) (P := primesUpTo Y)
    halfWeight_nonneg (fun p hp => prime_of_mem_primesUpTo hp) 1 hl0
  rw [sum_halfWeight_sq, mul_one, hl2] at hM
  have e1 : 2 / Sieve.mertensS Y * Sieve.mertensS Y / 2 = 1 := by
    field_simp
  rw [e1] at hM
  have hexp : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hmodel : ∫ ω, modelField halfWeight (primesUpTo Y) ω ^ 2 ∂steinhausMeasure ≤
      6 * Sieve.mertensS Y := by
    refine hM.trans ?_
    have e2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [e2]
    have e3 : (2 : ℝ) * (2 / Sieve.mertensS Y)⁻¹ * (2 * Real.exp 1) =
        2 * Real.exp 1 * Sieve.mertensS Y := by
      field_simp
    rw [e3]
    nlinarith
  have hA : (∑ p ∈ primesUpTo Y, halfWeight p) * Y ≤ (Y : ℝ) ^ 2 := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right (sum_halfWeight_le Y) (Nat.cast_nonneg _)
  have hA0 : 0 ≤ (∑ p ∈ primesUpTo Y, halfWeight p) * Y :=
    mul_nonneg (Finset.sum_nonneg fun p _ => halfWeight_nonneg p) (Nat.cast_nonneg _)
  have hA2 : ((∑ p ∈ primesUpTo Y, halfWeight p) * Y) ^ 2 ≤ (Y : ℝ) ^ 4 := by
    calc ((∑ p ∈ primesUpTo Y, halfWeight p) * Y) ^ 2 ≤ ((Y : ℝ) ^ 2) ^ 2 :=
          pow_le_pow_left₀ hA0 hA 2
      _ = (Y : ℝ) ^ 4 := by ring
  have hupper := (abs_le.mp htrans).2
  have hdiv : 2 * ((∑ p ∈ primesUpTo Y, halfWeight p) * Y) ^ 2 / T ≤ 2 * (Y : ℝ) ^ 4 / T :=
    div_le_div_of_nonneg_right (by linarith) hT.le
  have hmean : T⁻¹ * ∫ t in T..(T + T), primeField halfWeight (primesUpTo Y) t ^ 2 ≤
      6 * Sieve.mertensS Y + 2 * (Y : ℝ) ^ 4 / T := by linarith
  have h := mul_le_mul_of_nonneg_left hmean hT.le
  rwa [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul] at h

/-! ### The theorem -/

/-- The prime sum and `log|ζ|`, each with its normalization, are close in probability. -/
theorem tendsto_windowMeasure_close {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T => (windowMeasure T).real {t | ε ≤
        |primeField halfWeight (primesUpTo (primeLength T)) t /
            Real.sqrt ((∑ p ∈ primesUpTo (primeLength T), halfWeight p ^ 2) / 2) -
          Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ / criticalScale T|})
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hclose⟩ := exists_volume_log_norm_zeta_sub_primeSum_le
  -- the bound
  have hlim : Tendsto (fun T => 28 * (primeMass T *
      (1 / Real.sqrt (primeMass T / 2) - 1 / criticalScale T) ^ 2) / ε ^ 2 +
      (C / (ε / 2) * (shiftDepth T / criticalScale T) +
        C * Real.exp (-(shiftDepth T / 60000)) + C * T ^ (-(1 / 2) : ℝ) +
        C / (ε / 2) ^ 2 * ((C + Real.log (dlog T)) / criticalScale T ^ 2))) atTop (𝓝 0) := by
    have h1 := (tendsto_primeMass_mul_theta_sq.const_mul 28).div_const (ε ^ 2)
    have h2 := tendsto_shiftDepth_div_scale.const_mul (C / (ε / 2))
    have h3 : Tendsto (fun T => Real.exp (-(shiftDepth T / 60000))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_shiftDepth.atTop_div_const (by norm_num))
    have h4 : Tendsto (fun T : ℝ => T ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have h5 := (tendsto_energy_div_scale_sq C).const_mul (C / (ε / 2) ^ 2)
    have h6 := h1.add (((h2.add (h3.const_mul C)).add (h4.const_mul C)).add h5)
    simpa using h6
  refine squeeze_zero' (Eventually.of_forall fun T => measureReal_nonneg) ?_ hlim
  have hsmall := (tendsto_primeLength_pow_div 4).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [hclose (ε / 2) (by positivity), eventually_gt_atTop 0, hsmall,
    tendsto_primeMass_atTop.eventually_ge_atTop 1, tendsto_dlog.eventually_ge_atTop 1] with
    T hV2 hT0 hY4 hW1 hu1
  have hu : 0 < dlog T := by linarith
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = criticalScale T := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by
    rw [hσ]
    exact Real.sqrt_pos.mpr (by positivity)
  rw [← hσ] at hV2 ⊢
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = primeMass T := ⟨_, rfl⟩
  have hWeq : ∑ p ∈ primesUpTo (primeLength T), halfWeight p ^ 2 = W := by
    rw [hW]
    exact sum_halfWeight_sq _
  rw [hWeq]
  rw [← hW] at hW1 ⊢
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1 / Real.sqrt (W / 2) - 1 / σ := ⟨_, rfl⟩
  rw [← hθ]
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = primeField halfWeight (primesUpTo (primeLength T)) := ⟨_, rfl⟩
  rw [← hF]
  have hFc : Continuous F := hF ▸ continuous_primeField _ _
  have hY1 : 1 ≤ primeLength T := Nat.succ_le_succ (Nat.zero_le _)
  have hint : ∫ t in T..(2 * T), θ ^ 2 * F t ^ 2 ≤ T * (7 * W * θ ^ 2) := by
    rw [intervalIntegral.integral_const_mul, two_mul]
    have h1 := integral_primeField_sq_le hT0 hY1 (show 0 < Sieve.mertensS (primeLength T) by
      have : 0 < W := by linarith
      rw [hW] at this
      exact this)
    rw [← hF, show Sieve.mertensS (primeLength T) = W from hW.symm] at h1
    have h2 : 2 * (primeLength T : ℝ) ^ 4 / T ≤ W := by
      have h3 : (primeLength T : ℝ) ^ 4 / T < 1 / 2 := hY4
      have : 2 * (primeLength T : ℝ) ^ 4 / T = 2 * ((primeLength T : ℝ) ^ 4 / T) := by ring
      rw [this]
      linarith
    have h4 : T * (6 * W + 2 * (primeLength T : ℝ) ^ 4 / T) ≤ T * (7 * W) :=
      mul_le_mul_of_nonneg_left (by linarith) hT0.le
    calc θ ^ 2 * ∫ t in T..(T + T), F t ^ 2 ≤ θ ^ 2 * (T * (7 * W)) :=
          mul_le_mul_of_nonneg_left (h1.trans h4) (sq_nonneg θ)
      _ = _ := by ring
  have hfc : Continuous fun t => θ ^ 2 * F t ^ 2 := continuous_const.mul (hFc.pow 2)
  have hV1 := volume_Icc_setOf_le_le_of_integral (show T ≤ 2 * T by linarith)
    (show 0 < (ε / 2) ^ 2 by positivity) (fun t => by positivity) hfc hint
  -- the pointwise split
  have hsplit : ∀ t ∈ Ioc T (T + T), ε ≤ |F t / Real.sqrt (W / 2) -
      Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ / σ| →
      t ∈ {t | t ∈ Icc T (2 * T) ∧ (ε / 2) ^ 2 ≤ θ ^ 2 * F t ^ 2} ∪
        {t | t ∈ Icc T (2 * T) ∧ ε / 2 * σ ≤
          |Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ - criticalPrimeSum T t|} := by
    intro t ht hle
    have htI : t ∈ Icc T (2 * T) := ⟨ht.1.le, by linarith [ht.2]⟩
    have hprime : criticalPrimeSum T t = F t := by
      rw [hF]
      rfl
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z = Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := ⟨_, rfl⟩
    rw [← hz] at hle
    have e : F t / Real.sqrt (W / 2) - z / σ = F t * θ + (F t - z) / σ := by
      rw [hθ]
      ring
    rw [e] at hle
    by_cases h1 : ε / 2 ≤ |F t * θ|
    · refine Or.inl ⟨htI, ?_⟩
      have h2 := pow_le_pow_left₀ (by positivity) h1 2
      rw [sq_abs] at h2
      calc (ε / 2) ^ 2 ≤ (F t * θ) ^ 2 := h2
        _ = _ := by ring
    · refine Or.inr ⟨htI, ?_⟩
      have h2 := abs_add_le (F t * θ) ((F t - z) / σ)
      have h3 : ε / 2 ≤ |(F t - z) / σ| := by
        have := not_le.mp h1
        linarith
      rw [abs_div, abs_of_pos hσ0, le_div_iff₀ hσ0, abs_sub_comm] at h3
      show ε / 2 * σ ≤ |Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ - criticalPrimeSum T t|
      rw [hprime, ← hz]
      exact h3
  have hV := (measure_union_le _ _).trans (add_le_add hV1 hV2)
  have ha1 : 0 ≤ T * (7 * W * θ ^ 2) / (ε / 2) ^ 2 := by positivity
  have hlog : 0 ≤ Real.log (dlog T) := Real.log_nonneg hu1
  have hκ0 : 0 ≤ shiftDepth T := Real.sqrt_nonneg _
  have hB0 : 0 ≤ C / (ε / 2) * (shiftDepth T / σ) + C * Real.exp (-(shiftDepth T / 60000)) +
      C * T ^ (-(1 / 2) : ℝ) + C / (ε / 2) ^ 2 * ((C + Real.log (dlog T)) / σ ^ 2) := by
    positivity
  have ha2 := mul_nonneg hT0.le hB0
  rw [← ENNReal.ofReal_add ha1 ha2] at hV
  have hfinal := windowMeasure_real_le hT0 hsplit (add_nonneg ha1 ha2) hV
  refine hfinal.trans (le_of_eq ?_)
  have e1 : T⁻¹ * (T * (7 * W * θ ^ 2) / (ε / 2) ^ 2) = 28 * (W * θ ^ 2) / ε ^ 2 := by
    field_simp
    ring
  rw [mul_add, e1, inv_mul_cancel_left₀ hT0.ne']

/-- The critical field is measurable in the height. -/
theorem measurable_log_norm_zeta_line (c : ℝ) :
    Measurable fun t : ℝ => Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ / c := by
  have hmem : ∀ t : ℝ, ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ∈ ({1}ᶜ : Set ℂ) := by
    intro t h
    have := congrArg Complex.re h
    simp at this
  have hc : Continuous fun t : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) :=
    analyticOnNhd_riemannZeta.continuousOn.comp_continuous (by fun_prop) hmem
  exact (Real.measurable_log.comp hc.norm.measurable).div_const c

/-- **Selberg's central limit theorem.** As `T → ∞`, the law of
`log|ζ(½ + it)|/√(½ log log T)` on `(T, 2T]` tends to the standard Gaussian. -/
theorem tendsto_log_norm_zeta_law_gaussian {T : ℕ → ℝ} (hT : ∀ n, 0 < T n)
    (hTtop : Tendsto T atTop atTop) :
    Tendsto (fun n => windowLaw (hT n)
        (fun t => Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ / criticalScale (T n))
        (measurable_log_norm_zeta_line (criticalScale (T n))))
      atTop (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  have hprime := tendsto_primeSum_law_gaussian (T := T) (Y := fun n => primeLength (T n)) hT
    (fun n => Nat.succ_le_succ (Nat.zero_le _)) (tendsto_primeMass_atTop.comp hTtop)
    (fun K => (tendsto_primeLength_pow_div K).comp hTtop)
  exact tendsto_windowLaw_of_close hT _
    (fun n => measurable_log_norm_zeta_line (criticalScale (T n))) hprime fun ε hε =>
    (tendsto_windowMeasure_close hε).comp hTtop

end GaloisForLFunctions.MultiscaleMollifiedZetaField
