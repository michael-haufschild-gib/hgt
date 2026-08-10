import GaloisForLFunctions.RHTower.Sieve.MertensFirst
import GaloisForLFunctions.RHTower.Sieve.ChebyshevMoebius
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The causal von Mangoldt endpoint anomaly

The truncated causal dilation current `∑_{n ≤ N} Λ(n) f(n·)` tested against a test function `φ`
is, after the change of variables `y = nx`, the series `∑_n (Λ(n)/n) ∫ f(y) φ(y/n) dy`.  Its only
divergence is the value of `φ` at the origin: subtracting `φ(0)` leaves a term bounded by
`Λ(n)/n²` times one fixed weighted mass of `f`, and `∑ Λ(n)/n² < ∞`.

Since `∑_{n ≤ N} Λ(n)/n` diverges — Mertens' first theorem — the *unrenormalized* current
converges exactly when the half-line mass of `f` (against the value `φ(0)`) vanishes.  So the
leading endpoint anomaly reads exactly one number, the mass, and nothing else.

* `deningerCausalTerm`, `deningerCausalRenorm` : the tested current and its renormalization.
* `deningerCausalRenorm_summable` : **the renormalized current always converges.**
* `deningerCausalL_tendsto_atTop` : `∑_{n ≤ N} Λ(n)/n → ∞`.
* `deningerCausal_summable_iff` : **the unrenormalized current converges exactly on zero mass.**
-/

namespace RHTower

open MeasureTheory ArithmeticFunction

noncomputable section

/-- The `n`-th term of the truncated causal dilation current, tested against `φ`. -/
def deningerCausalTerm (f φ : ℝ → ℂ) (n : ℕ) : ℂ :=
  ((vonMangoldt n / (n : ℝ) : ℝ) : ℂ) * ∫ y in Set.Ioi (0 : ℝ), f y * φ (y / n)

/-- The `n`-th term with the value at the origin subtracted. -/
def deningerCausalRenorm (f φ : ℝ → ℂ) (n : ℕ) : ℂ :=
  ((vonMangoldt n / (n : ℝ) : ℝ) : ℂ) * ∫ y in Set.Ioi (0 : ℝ), f y * (φ (y / n) - φ 0)

/-! ## The renormalized current converges -/

/-- The weighted mass `∫_0^∞ y |f(y)| dy`. -/
def deningerCausalMass (f : ℝ → ℂ) : ℝ := ∫ y in Set.Ioi (0 : ℝ), y * ‖f y‖

theorem deningerCausalMass_nonneg (f : ℝ → ℂ) : 0 ≤ deningerCausalMass f := by
  refine setIntegral_nonneg measurableSet_Ioi fun y hy => ?_
  exact mul_nonneg (le_of_lt hy) (norm_nonneg _)

/-- The weighted mass is the norm integral of the first moment. -/
theorem deningerCausalMass_integrable {f : ℝ → ℂ}
    (hfy : IntegrableOn (fun y => (y : ℝ) * f y) (Set.Ioi 0)) :
    IntegrableOn (fun y => y * ‖f y‖) (Set.Ioi 0) := by
  refine MeasureTheory.IntegrableOn.congr_fun (hfy.norm) (fun y hy => ?_) measurableSet_Ioi
  show ‖(y : ℂ) * f y‖ = y * ‖f y‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hy)]

/-- **The renormalized term is bounded by `Λ(n)/n²` times the weighted mass.** -/
theorem deningerCausalRenorm_norm_le {f φ : ℝ → ℂ} {C : ℝ}
    (hlip : ∀ x : ℝ, ‖φ x - φ 0‖ ≤ C * |x|)
    (hfy : IntegrableOn (fun y => (y : ℝ) * f y) (Set.Ioi 0)) (n : ℕ) :
    ‖deningerCausalRenorm f φ n‖
      ≤ (C * deningerCausalMass f) * (vonMangoldt n / (n : ℝ) ^ 2) := by
  have hmass := deningerCausalMass_integrable hfy
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hzero : ∀ y : ℝ, φ (y / ((0 : ℕ) : ℝ)) - φ 0 = 0 := by
      intro y
      rw [Nat.cast_zero, div_zero, sub_self]
    rw [deningerCausalRenorm]
    simp only [hzero, mul_zero, integral_zero, mul_zero, norm_zero]
    have h0 : vonMangoldt 0 = 0 := by simp
    rw [h0]
    simp
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hbound : ∀ y ∈ Set.Ioi (0 : ℝ),
        ‖f y * (φ (y / n) - φ 0)‖ ≤ (C / (n : ℝ)) * (y * ‖f y‖) := by
      intro y hy
      have hy0 : (0 : ℝ) < y := hy
      rw [norm_mul]
      have h1 : ‖φ (y / n) - φ 0‖ ≤ C * (y / (n : ℝ)) := by
        have := hlip (y / (n : ℝ))
        rwa [abs_of_nonneg (le_of_lt (div_pos hy0 hnpos))] at this
      calc ‖f y‖ * ‖φ (y / n) - φ 0‖ ≤ ‖f y‖ * (C * (y / (n : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = (C / (n : ℝ)) * (y * ‖f y‖) := by field_simp
    have hint : ‖∫ y in Set.Ioi (0 : ℝ), f y * (φ (y / n) - φ 0)‖
        ≤ ∫ y in Set.Ioi (0 : ℝ), (C / (n : ℝ)) * (y * ‖f y‖) := by
      refine norm_integral_le_of_norm_le (hmass.const_mul _) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact hbound y hy
    have hval : (∫ y in Set.Ioi (0 : ℝ), (C / (n : ℝ)) * (y * ‖f y‖))
        = (C / (n : ℝ)) * deningerCausalMass f := by
      rw [deningerCausalMass, ← integral_const_mul]
    rw [hval] at hint
    rw [deningerCausalRenorm, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg vonMangoldt_nonneg hnpos.le)]
    have hstep : (vonMangoldt n / (n : ℝ)) *
        ‖∫ y in Set.Ioi (0 : ℝ), f y * (φ (y / n) - φ 0)‖
        ≤ (vonMangoldt n / (n : ℝ)) * ((C / (n : ℝ)) * deningerCausalMass f) :=
      mul_le_mul_of_nonneg_left hint (div_nonneg vonMangoldt_nonneg hnpos.le)
    refine le_trans hstep (le_of_eq ?_)
    field_simp

/-- The von Mangoldt weights are square-summable against `n⁻²`. -/
theorem deningerVonMangoldt_summable_div_sq :
    Summable fun n : ℕ => vonMangoldt n / (n : ℝ) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) Sieve.summable_log_div_sq
  · exact div_nonneg vonMangoldt_nonneg (by positivity)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      gcongr
      exact vonMangoldt_le_log

/-- **The renormalized causal current always converges.**  The only divergence of the truncated
causal dilation current is the value of the test function at the origin. -/
theorem deningerCausalRenorm_summable {f φ : ℝ → ℂ} {C : ℝ}
    (hlip : ∀ x : ℝ, ‖φ x - φ 0‖ ≤ C * |x|)
    (hfy : IntegrableOn (fun y => (y : ℝ) * f y) (Set.Ioi 0)) :
    Summable (deningerCausalRenorm f φ) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => deningerCausalRenorm_norm_le hlip hfy n) ?_)
  exact deningerVonMangoldt_summable_div_sq.mul_left _

/-! ## The unrenormalized current -/

/-- The renormalization changes the term by the mass times the value at the origin. -/
theorem deningerCausalTerm_eq {f φ : ℝ → ℂ} {C : ℝ}
    (hlip : ∀ x : ℝ, ‖φ x - φ 0‖ ≤ C * |x|) (hφ : Continuous φ)
    (hf : IntegrableOn f (Set.Ioi 0))
    (hfy : IntegrableOn (fun y => (y : ℝ) * f y) (Set.Ioi 0)) (n : ℕ) :
    deningerCausalTerm f φ n
      = deningerCausalRenorm f φ n
        + ((vonMangoldt n / (n : ℝ) : ℝ) : ℂ) * ((∫ y in Set.Ioi (0 : ℝ), f y) * φ 0) := by
  have hmass := deningerCausalMass_integrable hfy
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (by simpa using hlip 1)
  have hmeas : AEStronglyMeasurable (fun y => f y * φ (y / n))
      (Measure.restrict volume (Set.Ioi 0)) :=
    hf.aestronglyMeasurable.mul
      ((hφ.comp (continuous_id.div_const _)).aestronglyMeasurable)
  have hdom : IntegrableOn (fun y => f y * (φ (y / n) - φ 0)) (Set.Ioi 0) := by
    refine Integrable.mono' (g := fun y => C * (y * ‖f y‖)) (hmass.const_mul C) ?_ ?_
    · exact hf.aestronglyMeasurable.mul
        (((hφ.comp (continuous_id.div_const _)).sub continuous_const).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : (0 : ℝ) < y := hy
      rw [norm_mul]
      have h1 : ‖φ (y / n) - φ 0‖ ≤ C * |y / (n : ℝ)| := hlip _
      have h2 : |y / (n : ℝ)| ≤ y := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [Nat.cast_zero, div_zero, abs_zero]
          exact hy0.le
        · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          rw [abs_of_nonneg (div_nonneg hy0.le (by linarith))]
          exact div_le_self hy0.le hn1
      calc ‖f y‖ * ‖φ (y / n) - φ 0‖ ≤ ‖f y‖ * (C * y) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hCnn)
        _ = C * (y * ‖f y‖) := by ring
  have hprod : IntegrableOn (fun y => f y * φ 0) (Set.Ioi 0) := hf.mul_const _
  have hsplit : (∫ y in Set.Ioi (0 : ℝ), f y * φ (y / n))
      = (∫ y in Set.Ioi (0 : ℝ), f y * (φ (y / n) - φ 0))
        + ∫ y in Set.Ioi (0 : ℝ), f y * φ 0 := by
    rw [← integral_add hdom hprod]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    ring
  rw [deningerCausalTerm, deningerCausalRenorm, hsplit, mul_add, integral_mul_const]

/-- **Mertens' first theorem forces the causal counterterm to diverge.** -/
theorem deningerCausalL_tendsto_atTop :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), vonMangoldt n / (n : ℝ))
      Filter.atTop Filter.atTop := by
  have hle : ∀ N : ℕ, 1 ≤ N →
      Real.log N - 1 - 2 * Sieve.logSqTailConst
        ≤ ∑ n ∈ Finset.range (N + 1), vonMangoldt n / (n : ℝ) := by
    intro N hN
    refine le_trans (Sieve.mertensFirst_lower hN) ?_
    have hsub : Nat.primesLE N ⊆ Finset.range (N + 1) := by
      intro p hp
      rw [Nat.mem_primesLE] at hp
      rw [Finset.mem_range]
      omega
    have hcongr : ∀ p ∈ Nat.primesLE N,
        Real.log p / (p : ℝ) = vonMangoldt p / (p : ℝ) := by
      intro p hp
      rw [Nat.mem_primesLE] at hp
      rw [vonMangoldt_apply_prime hp.2]
    rw [Finset.sum_congr rfl hcongr]
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => ?_
    exact div_nonneg vonMangoldt_nonneg (by positivity)
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_
    (Filter.tendsto_atTop_add_const_right _ (-1 - 2 * Sieve.logSqTailConst)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have := hle N hN
  simpa [sub_eq_add_neg, add_assoc] using this

theorem deningerVonMangoldt_not_summable :
    ¬ Summable fun n : ℕ => vonMangoldt n / (n : ℝ) := by
  intro hsum
  have hnn : ∀ n : ℕ, 0 ≤ vonMangoldt n / (n : ℝ) := fun n =>
    div_nonneg vonMangoldt_nonneg (by positivity)
  have hbdd : ∀ N : ℕ, (∑ n ∈ Finset.range (N + 1), vonMangoldt n / (n : ℝ))
      ≤ ∑' n : ℕ, vonMangoldt n / (n : ℝ) := fun N =>
    hsum.sum_le_tsum _ (fun i _ => hnn i)
  have := deningerCausalL_tendsto_atTop.eventually_ge_atTop
    ((∑' n : ℕ, vonMangoldt n / (n : ℝ)) + 1)
  obtain ⟨N, hN⟩ := this.exists
  have := hbdd N
  linarith

/-- **The causal endpoint anomaly reads exactly one number.**  The unrenormalized truncated causal
current converges if and only if the half-line mass of `f`, weighted by the value of the test
function at the origin, vanishes. -/
theorem deningerCausal_summable_iff {f φ : ℝ → ℂ} {C : ℝ}
    (hlip : ∀ x : ℝ, ‖φ x - φ 0‖ ≤ C * |x|) (hφ : Continuous φ)
    (hf : IntegrableOn f (Set.Ioi 0))
    (hfy : IntegrableOn (fun y => (y : ℝ) * f y) (Set.Ioi 0)) :
    Summable (deningerCausalTerm f φ)
      ↔ (∫ y in Set.Ioi (0 : ℝ), f y) * φ 0 = 0 := by
  have hren := deningerCausalRenorm_summable hlip hfy
  have heq := deningerCausalTerm_eq hlip hφ hf hfy
  constructor
  · intro hsum
    by_contra hne
    have hdiff : Summable fun n : ℕ =>
        ((vonMangoldt n / (n : ℝ) : ℝ) : ℂ) *
          ((∫ y in Set.Ioi (0 : ℝ), f y) * φ 0) := by
      refine (hsum.sub hren).congr fun n => ?_
      rw [heq n]
      ring
    have hscale : Summable fun n : ℕ => ((vonMangoldt n / (n : ℝ) : ℝ) : ℂ) := by
      refine (hdiff.mul_right ((∫ y in Set.Ioi (0 : ℝ), f y) * φ 0)⁻¹).congr fun n => ?_
      rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
    refine deningerVonMangoldt_not_summable ?_
    have := hscale.norm
    refine this.congr fun n => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg vonMangoldt_nonneg (by positivity))]
  · intro hzero
    refine hren.congr fun n => ?_
    rw [heq n, hzero, mul_zero, add_zero]

end

end RHTower
