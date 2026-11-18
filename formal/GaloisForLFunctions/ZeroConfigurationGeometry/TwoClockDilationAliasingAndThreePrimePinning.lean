import GaloisForLFunctions.ZeroConfigurationGeometry.MultiplicativeDilationAnnihilationOfPrimeError
import GaloisForLFunctions.RHTower.ChebyshevErrorExponentLaw
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion
import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightSixtySeven
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-!
# Two-Clock Prime-Error Dilation Aliasing, Three-Prime Pinning, and Unconditional Regimes

For `E(x) = ψ(x) − x`, `1/2 < β < 1`, `γ > 0`, and scale `a > 1`, consider the forward
single-frequency second-order dilation residual

`R_a(β, γ; x) = E(a² x) − 2 a^β cos(γ log a) E(a x) + a^{2β} E(x)`.

This module establishes four unconditional results governing `R_a`:

1. **Exact rescaling bridge and mode annihilation**
   (`dilationSetOp_singleton_sq_mul`, `primeDilationResidual_eq_dilationSetOp`,
   `dilationRecurrenceOp_re_cpow_eq_zero`, `abs_dilationRecurrenceOp_le_of_sqrt_log_sq`):
   `R_a(β, γ; x)` agrees with `dilationSetOp a β {γ} ψ (a² x) − mainTermFactor a β {γ} · (a² x)`,
   identically annihilates every real wave `Re(c x^{β + iω})` satisfying `cos(ω log a) = cos(γ log a)`,
   and preserves `O(√x log² x)` bounds.

2. **All-`ε` Mellin pole-pinning down to `Re s = 1/2`**
   (`re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded`):
   If `|R_a(β, γ; x)| / (√x log² x)` is bounded at large `x` (`a > 1`), then **every** zero `ρ ≠ 1`
   of `ζ` in the entire open half-plane `{Re s > 1/2}` satisfies `Re ρ = β` and
   `cos(Im ρ · log a) = cos(γ log a)`.

3. **Dense `(2, 3)` cross-sign aliasing vs. `(2, 3, 5)` pigeonhole de-aliasing**
   (`isCrossResonantPair_unique`, `abs_eq_or_isCrossResonantPair_of_twoPrime_cos_eq`,
   `dense_exists_isCrossResonantPair`, `abs_eq_of_threePrime_cos_eq`,
   `plantedAliasedDoubleWave_separates_two_and_three_clocks`):
   For two distinct primes `p ≠ q`, joint cosine agreement `cos(ω log p) = cos(γ log p)` and
   `cos(ω log q) = cos(γ log q)` admits, besides `±γ`, at most one positive cross-sign partner
   `ω* ≠ γ`. For `(p, q) = (2, 3)`, such cross-resonant pairs `(γ, ω*)` with `ω* > H` are dense in
   `(0, ∞)` and yield planted two-frequency waves annihilated by both `R_2` and `R_3` while driving
   `|R_5| / (√x log² x)` unbounded. For any three distinct primes `{p₁, p₂, p₃}` (in particular
   `{2, 3, 5}`), pigeonhole over `{±1}` eliminates cross-sign aliasing completely for all `γ ≥ 0`.

4. **Unconditional resolution across three explicit regimes**
   (`not_hasPositivePowerLimsup_of_sub_seven_eighths_lt`,
   `twoClock_unbounded_of_sub_seven_eighths_lt`,
   `hasPositivePowerLimsup_and_all_clocks_unbounded_of_lt_zeroReSup`,
   `threeClock_unbounded_of_le_sixtySeven`, `twoClock_unbounded_of_le_sixtySeven`):
   Unconditionally, the two-clock prime recurrence implication holds for all `β > 20999 / 24000`,
   holds in sharpened all-clock form (`R_a` unbounded for every `a > 1`, including both `a = 2`
   and `a = 3`) whenever `1/2 < β < zeroReSup`, holds for all `0 < γ ≤ 67` on `{2, 3, 5}`, and
   holds on `{2, 3}` for all `0 < γ ≤ 67` without a cross-resonant partner above height `67`.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set Polynomial
open RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-! ### 1. Forward single-frequency dilation operators and asymptotic predicates -/

/-- The Chebyshev prime-counting error `E(x) = ψ(x) − x`. -/
def primeError (x : ℝ) : ℝ :=
  Chebyshev.psi x - x

/-- Forward second-order single-frequency dilation operator
`(D_a(β, γ) f)(x) = f(a² x) − 2 a^β cos(γ log a) f(a x) + a^{2β} f(x)`. -/
def dilationRecurrenceOp (a β γ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (a ^ 2 * x) - 2 * a ^ β * Real.cos (γ * Real.log a) * f (a * x) + a ^ (2 * β) * f x

/-- Forward single-frequency dilation residual `R_a(β, γ; x)` of `E(x) = ψ(x) − x`. -/
def primeDilationResidual (a β γ x : ℝ) : ℝ :=
  dilationRecurrenceOp a β γ primeError x

/-- `f` has positive `x^β` upper limit at `+∞`: `∃ c > 0`, cofinally `c x^β ≤ |f(x)|`. -/
def HasPositivePowerLimsup (f : ℝ → ℝ) (β : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ X₀ : ℝ, ∃ x : ℝ, X₀ ≤ x ∧ c * x ^ β ≤ |f x|

/-- `|g(x)| / (√x log² x)` is unbounded at large `x`. -/
def IsSqrtLogSqUnbounded (g : ℝ → ℝ) : Prop :=
  ∀ M X₀ : ℝ, ∃ x : ℝ, X₀ ≤ x ∧ M < |g x| / (Real.sqrt x * Real.log x ^ 2)

/-- Exact equivalence between `HasPositivePowerLimsup f β` and `Filter.limsup > 0` in `EReal`. -/
theorem hasPositivePowerLimsup_iff_limsup_pos (f : ℝ → ℝ) (β : ℝ) :
    HasPositivePowerLimsup f β ↔
      (0 : EReal) < Filter.limsup (fun x : ℝ => ((|f x| / x ^ β : ℝ) : EReal)) atTop := by
  set u : ℝ → EReal := fun x => ((|f x| / x ^ β : ℝ) : EReal)
  constructor
  · rintro ⟨c, hc, hfreq⟩
    have hc2 : (0 : EReal) < ((c / 2 : ℝ) : EReal) := by exact_mod_cast half_pos hc
    refine lt_of_lt_of_le hc2 (le_sInf fun a ha => ?_)
    obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp ha
    obtain ⟨x, hx, hcx⟩ := hfreq (max X₀ 1)
    have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
    have hxpos : 0 < x ^ β := Real.rpow_pos_of_pos (zero_lt_one.trans_le hx1) β
    have hdiv : c ≤ |f x| / x ^ β := (le_div_iff₀ hxpos).mpr hcx
    have hle_a : ((c : ℝ) : EReal) ≤ a :=
      (EReal.coe_le_coe_iff.mpr hdiv).trans (hX₀ x ((le_max_left _ _).trans hx))
    exact (EReal.coe_le_coe_iff.mpr (by linarith)).trans hle_a
  · intro hpos
    set L : EReal := Filter.limsup u atTop
    have hex : ∃ c : ℝ, 0 < c ∧ ((c : ℝ) : EReal) < L := by
      have hpos' : (0 : EReal) < L := hpos
      clear_value L
      induction L using EReal.rec with
      | bot => exact absurd hpos' (not_lt_of_ge bot_le)
      | coe r =>
        have hr : 0 < r := EReal.coe_pos.mp hpos'
        exact ⟨r / 2, half_pos hr, EReal.coe_lt_coe_iff.mpr (half_lt_self hr)⟩
      | top => exact ⟨1, one_pos, EReal.coe_lt_top 1⟩
    obtain ⟨c, hc, hcL⟩ := hex
    refine ⟨c, hc, fun X₀ => ?_⟩
    have hnot : ¬ (∀ᶠ x in atTop, u x ≤ ((c : ℝ) : EReal)) := fun hev =>
      not_le_of_gt hcL (sInf_le hev)
    rw [Filter.eventually_atTop] at hnot
    push Not at hnot
    obtain ⟨x, hx, hgt⟩ := hnot (max X₀ 1)
    have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
    have hxpos : 0 < x ^ β := Real.rpow_pos_of_pos (zero_lt_one.trans_le hx1) β
    have hgtR : c < |f x| / x ^ β := EReal.coe_lt_coe_iff.mp hgt
    exact ⟨x, (le_max_left _ _).trans hx, ((lt_div_iff₀ hxpos).mp hgtR).le⟩

/-- `IsSqrtLogSqUnbounded g` holds iff `g` admits no eventual `C √x log² x` upper bound. -/
theorem isSqrtLogSqUnbounded_iff_not_eventually_le (g : ℝ → ℝ) :
    IsSqrtLogSqUnbounded g ↔
      ¬ ∃ C X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → |g x| ≤ C * Real.sqrt x * Real.log x ^ 2 := by
  constructor
  · rintro hunb ⟨C, X₀, hC⟩
    obtain ⟨x, hx, hgt⟩ := hunb (max C 0) (max X₀ 2)
    have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
    have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hden_pos : 0 < Real.sqrt x * Real.log x ^ 2 :=
      mul_pos (Real.sqrt_pos.mpr (by linarith)) (sq_pos_of_pos hlog_pos)
    have hle : |g x| ≤ max C 0 * (Real.sqrt x * Real.log x ^ 2) := by
      calc |g x| ≤ C * Real.sqrt x * Real.log x ^ 2 := hC x ((le_max_left _ _).trans hx)
        _ ≤ max C 0 * Real.sqrt x * Real.log x ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg x)) (sq_nonneg _)
        _ = max C 0 * (Real.sqrt x * Real.log x ^ 2) := by ring
    exact not_le_of_gt hgt ((div_le_iff₀ hden_pos).mpr hle)
  · intro hnot M X₀
    by_contra hall
    push Not at hall
    apply hnot
    refine ⟨max M 0, max X₀ 2, fun x hx => ?_⟩
    have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
    have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hden_pos : 0 < Real.sqrt x * Real.log x ^ 2 :=
      mul_pos (Real.sqrt_pos.mpr (by linarith)) (sq_pos_of_pos hlog_pos)
    have hdiv : |g x| / (Real.sqrt x * Real.log x ^ 2) ≤ max M 0 :=
      (hall x ((le_max_left _ _).trans hx)).trans (le_max_left M 0)
    have hmul := (div_le_iff₀ hden_pos).mp hdiv
    linarith

/-! ### 2. Exact rescaling bridge to `dilationSetOp` and planted-wave annihilation -/

theorem dilationRecurrenceOp_congr_cos {a β γ₁ γ₂ : ℝ}
    (hcos : Real.cos (γ₁ * Real.log a) = Real.cos (γ₂ * Real.log a)) :
    dilationRecurrenceOp a β γ₁ = dilationRecurrenceOp a β γ₂ := by
  funext f x
  simp only [dilationRecurrenceOp, hcos]

theorem dilationRecurrenceOp_add (a β γ : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    dilationRecurrenceOp a β γ (fun y => f y + g y) x =
      dilationRecurrenceOp a β γ f x + dilationRecurrenceOp a β γ g x := by
  simp only [dilationRecurrenceOp]
  ring

theorem dilationRecurrenceOp_sub (a β γ : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    dilationRecurrenceOp a β γ (fun y => f y - g y) x =
      dilationRecurrenceOp a β γ f x - dilationRecurrenceOp a β γ g x := by
  simp only [dilationRecurrenceOp]
  ring

theorem natDegree_dilationPairPoly {a : ℝ} (ha : 0 < a) (β γ : ℝ) :
    (dilationPairPoly a β γ).natDegree = 2 := by
  set c₁ : ℝ := 2 * a ^ β * Real.cos (γ * Real.log a)
  set c₂ : ℝ := a ^ (2 * β)
  have hc₂ : c₂ ≠ 0 := (Real.rpow_pos_of_pos ha (2 * β)).ne'
  have hdeg_sub : (1 - C c₁ * X : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_C_mul_le c₁ X).trans (by simp)
  have hle : (dilationPairPoly a β γ).natDegree ≤ 2 := by
    change (1 - C c₁ * X + C c₂ * X ^ 2).natDegree ≤ 2
    refine (natDegree_add_le _ _).trans (max_le (hdeg_sub.trans (by norm_num)) ?_)
    exact (natDegree_C_mul_le c₂ (X ^ 2)).trans (by simp)
  have hcoeff2 : (dilationPairPoly a β γ).coeff 2 = c₂ := by
    simp [dilationPairPoly, Polynomial.coeff_one, c₂]
  exact le_antisymm hle (le_natDegree_of_ne_zero (hcoeff2 ▸ hc₂))

/-- Pointwise expansion of `dilationSetOp a β {γ}` (`a > 0`). -/
theorem dilationSetOp_singleton_apply {a : ℝ} (ha : 0 < a) (β γ : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    dilationSetOp a β {γ} f y =
      f y - 2 * a ^ β * Real.cos (γ * Real.log a) * f (y / a) + a ^ (2 * β) * f (y / a ^ 2) := by
  have hset : dilationSetPoly a β {γ} = dilationPairPoly a β γ := by simp [dilationSetPoly]
  rw [dilationSetOp, hset, dilationPolyOp, natDegree_dilationPairPoly ha]
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero, div_one,
    pow_one]
  have hc0 : (dilationPairPoly a β γ).coeff 0 = 1 := by
    simp [dilationPairPoly, Polynomial.coeff_one]
  have hc1 : (dilationPairPoly a β γ).coeff 1 = -2 * a ^ β * Real.cos (γ * Real.log a) := by
    simp [dilationPairPoly, Polynomial.coeff_one]
  have hc2 : (dilationPairPoly a β γ).coeff 2 = a ^ (2 * β) := by
    simp [dilationPairPoly, Polynomial.coeff_one]
  rw [hc0, hc1, hc2]
  ring

/-- Evaluating `dilationSetOp a β {γ} f` at `a² x` recovers `dilationRecurrenceOp a β γ f x`. -/
theorem dilationSetOp_singleton_sq_mul {a : ℝ} (ha : 0 < a) (β γ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    dilationSetOp a β {γ} f (a ^ 2 * x) = dilationRecurrenceOp a β γ f x := by
  have ha0 : a ≠ 0 := ha.ne'
  rw [dilationSetOp_singleton_apply ha, dilationRecurrenceOp]
  have h1 : a ^ 2 * x / a = a * x := by field_simp
  have h2 : a ^ 2 * x / a ^ 2 = x := by field_simp
  rw [h1, h2]

/-- Exact identity between `primeDilationResidual` and `dilationSetOp` on `Chebyshev.psi`. -/
theorem primeDilationResidual_eq_dilationSetOp {a : ℝ} (ha : 0 < a) (β γ x : ℝ) :
    primeDilationResidual a β γ x =
      dilationSetOp a β {γ} Chebyshev.psi (a ^ 2 * x) - mainTermFactor a β {γ} * (a ^ 2 * x) := by
  rw [primeDilationResidual, ← dilationSetOp_singleton_sq_mul ha]
  have hpe : primeError = fun y => Chebyshev.psi y - id y := rfl
  rw [hpe, dilationSetOp, dilationPolyOp_sub, ← dilationSetOp, ← dilationSetOp, dilationSetOp_id_eq]

/-- Action of `dilationRecurrenceOp` on any complex power `Re(c x^{β + iω})` (`a > 0`, `x > 0`). -/
theorem dilationRecurrenceOp_re_cpow_eq {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (β γ ω : ℝ) (c : ℂ) :
    dilationRecurrenceOp a β γ (fun y => (c * (y : ℂ) ^ ((β : ℂ) + I * ω)).re) x =
      (c * (dilationSymbol a (dilationPairPoly a β γ) ((β : ℂ) + I * ω) *
        ((a ^ 2 * x : ℝ) : ℂ) ^ ((β : ℂ) + I * ω))).re := by
  have hay : 0 < a ^ 2 * x := mul_pos (pow_pos ha 2) hx
  have hset : dilationSetPoly a β {γ} = dilationPairPoly a β γ := by simp [dilationSetPoly]
  rw [← dilationSetOp_singleton_sq_mul ha, dilationSetOp, hset]
  set P := dilationPairPoly a β γ
  have hre : dilationPolyOp a P (fun y => (c * (y : ℂ) ^ ((β : ℂ) + I * ω)).re) (a ^ 2 * x) =
      (c * dilationPolyOpC a P (fun y => (y : ℂ) ^ ((β : ℂ) + I * ω)) (a ^ 2 * x)).re := by
    simp only [dilationPolyOp, dilationPolyOpC, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, mul_comm c (P.coeff k : ℂ), mul_assoc, Complex.re_ofReal_mul]
  rw [hre, dilationPolyOpC_cpow_eq ha hay]

/-- `dilationRecurrenceOp a β γ` identically annihilates `Re(c x^{β + iω})` whenever
`cos(ω log a) = cos(γ log a)`. -/
theorem dilationRecurrenceOp_re_cpow_eq_zero {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    {β γ ω : ℝ} (hcos : Real.cos (ω * Real.log a) = Real.cos (γ * Real.log a)) (c : ℂ) :
    dilationRecurrenceOp a β γ (fun y => (c * (y : ℂ) ^ ((β : ℂ) + I * ω)).re) x = 0 := by
  rw [dilationRecurrenceOp_congr_cos hcos.symm, dilationRecurrenceOp_re_cpow_eq ha hx]
  have hset : dilationPairPoly a β ω = dilationSetPoly a β {ω} := by simp [dilationSetPoly]
  have hmem : ω ∈ oscillationFrequencies ({ω} : Finset ℝ) :=
    Finset.mem_union_left _ (Finset.mem_singleton_self ω)
  rw [hset, dilationSymbol_dilationSetPoly_eq_zero_of_mem ha β {ω} hmem, zero_mul, mul_zero,
    Complex.zero_re]

/-- Stability of `O(√x log² x)` remainders under `dilationRecurrenceOp a β γ` (`a ≥ 1`). -/
theorem abs_dilationRecurrenceOp_le_of_sqrt_log_sq {a β γ K X₀ : ℝ} (ha : 1 ≤ a) (hK : 0 ≤ K)
    {η : ℝ → ℝ}
    (hη : ∀ x : ℝ, X₀ ≤ x → |η x| ≤ K * Real.sqrt x * Real.log x ^ 2) :
    ∃ C X₁ : ℝ, 0 ≤ C ∧ ∀ x : ℝ, X₁ ≤ x →
      |dilationRecurrenceOp a β γ η x| ≤ C * Real.sqrt x * Real.log x ^ 2 := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  set X₁ : ℝ := max X₀ (max 2 (a ^ 2))
  set C : ℝ := K * (9 * a + 8 * a ^ β * Real.sqrt a + a ^ (2 * β))
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, X₁, hC0, fun x hx => ?_⟩
  have hx0 : X₀ ≤ x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxa2 : a ^ 2 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx_pos : 0 < x := by linarith
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hloga_le : Real.log a ≤ Real.log x := by
    have h1 : a ≤ a ^ 2 := by nlinarith
    exact Real.log_le_log ha0 (h1.trans hxa2)
  have hloga2_le : Real.log (a ^ 2) ≤ Real.log x := Real.log_le_log (pow_pos ha0 2) hxa2
  have hax0 : X₀ ≤ a * x := hx0.trans (le_mul_of_one_le_left hx_pos.le ha)
  have ha2x0 : X₀ ≤ a ^ 2 * x := hx0.trans (le_mul_of_one_le_left hx_pos.le (one_le_pow₀ ha))
  have hb0 := hη x hx0
  have hb1 := hη (a * x) hax0
  have hb2 := hη (a ^ 2 * x) ha2x0
  have hlog_ax : Real.log (a * x) ^ 2 ≤ 4 * Real.log x ^ 2 := by
    rw [Real.log_mul ha0.ne' hx_pos.ne']
    have hnonneg : 0 ≤ Real.log a := Real.log_nonneg ha
    nlinarith
  have hlog_a2x : Real.log (a ^ 2 * x) ^ 2 ≤ 9 * Real.log x ^ 2 := by
    rw [Real.log_mul (pow_pos ha0 2).ne' hx_pos.ne']
    have hnonneg : 0 ≤ Real.log (a ^ 2) := Real.log_nonneg (one_le_pow₀ ha)
    nlinarith
  have hsqrt_ax : Real.sqrt (a * x) = Real.sqrt a * Real.sqrt x := Real.sqrt_mul ha0.le x
  have hsqrt_a2x : Real.sqrt (a ^ 2 * x) = a * Real.sqrt x := by
    rw [Real.sqrt_mul (pow_pos ha0 2).le x, Real.sqrt_sq ha0.le]
  have hcos : |Real.cos (γ * Real.log a)| ≤ 1 := Real.abs_cos_le_one _
  have ht2 : |η (a ^ 2 * x)| ≤ 9 * K * a * Real.sqrt x * Real.log x ^ 2 := by
    calc |η (a ^ 2 * x)| ≤ K * (a * Real.sqrt x) * Real.log (a ^ 2 * x) ^ 2 := by
          rwa [hsqrt_a2x] at hb2
      _ ≤ K * (a * Real.sqrt x) * (9 * Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_left hlog_a2x (by positivity)
      _ = 9 * K * a * Real.sqrt x * Real.log x ^ 2 := by ring
  have ht1 : |2 * a ^ β * Real.cos (γ * Real.log a) * η (a * x)| ≤
      8 * K * a ^ β * Real.sqrt a * Real.sqrt x * Real.log x ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2),
      abs_of_pos (Real.rpow_pos_of_pos ha0 β)]
    have hmid : |Real.cos (γ * Real.log a)| * |η (a * x)| ≤
        1 * (K * (Real.sqrt a * Real.sqrt x) * (4 * Real.log x ^ 2)) := by
      refine mul_le_mul hcos ?_ (abs_nonneg _) zero_le_one
      calc |η (a * x)| ≤ K * (Real.sqrt a * Real.sqrt x) * Real.log (a * x) ^ 2 := by
            rwa [hsqrt_ax] at hb1
        _ ≤ K * (Real.sqrt a * Real.sqrt x) * (4 * Real.log x ^ 2) :=
            mul_le_mul_of_nonneg_left hlog_ax (by positivity)
    calc 2 * a ^ β * |Real.cos (γ * Real.log a)| * |η (a * x)|
        = 2 * a ^ β * (|Real.cos (γ * Real.log a)| * |η (a * x)|) := by ring
      _ ≤ 2 * a ^ β * (1 * (K * (Real.sqrt a * Real.sqrt x) * (4 * Real.log x ^ 2))) :=
          mul_le_mul_of_nonneg_left hmid (by positivity)
      _ = 8 * K * a ^ β * Real.sqrt a * Real.sqrt x * Real.log x ^ 2 := by ring
  have ht0 : |a ^ (2 * β) * η x| ≤ K * a ^ (2 * β) * Real.sqrt x * Real.log x ^ 2 := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ha0 (2 * β))]
    calc a ^ (2 * β) * |η x| ≤ a ^ (2 * β) * (K * Real.sqrt x * Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_left hb0 (by positivity)
      _ = K * a ^ (2 * β) * Real.sqrt x * Real.log x ^ 2 := by ring
  have htri : |dilationRecurrenceOp a β γ η x| ≤
      |η (a ^ 2 * x)| + |2 * a ^ β * Real.cos (γ * Real.log a) * η (a * x)| +
        |a ^ (2 * β) * η x| := by
    unfold dilationRecurrenceOp
    exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
  calc |dilationRecurrenceOp a β γ η x|
      ≤ 9 * K * a * Real.sqrt x * Real.log x ^ 2 +
          8 * K * a ^ β * Real.sqrt a * Real.sqrt x * Real.log x ^ 2 +
          K * a ^ (2 * β) * Real.sqrt x * Real.log x ^ 2 := by linarith
    _ = C * Real.sqrt x * Real.log x ^ 2 := by dsimp [C]; ring

/-! ### 3. All-`ε` Mellin pole-pinning down to `Re s = 1/2` -/

/-- Exact trigonometric period characterization via complex exponentials. -/
theorem cos_eq_cos_iff_exists_int (u v : ℝ) :
    Real.cos u = Real.cos v ↔
      ∃ m : ℤ, u = v + (m : ℝ) * (2 * Real.pi) ∨ u = -v + (m : ℝ) * (2 * Real.pi) := by
  have hprod : (cexp (I * u) - cexp (I * v)) * (cexp (I * u) - cexp (-I * v)) =
      2 * cexp (I * u) * ((Real.cos u : ℂ) - (Real.cos v : ℂ)) := by
    rw [Complex.ofReal_cos, Complex.ofReal_cos, Complex.cos, Complex.cos]
    have h1 : (u : ℂ) * I = I * u := mul_comm _ _
    have h2 : -(u : ℂ) * I = -(I * u) := by ring
    have h3 : (v : ℂ) * I = I * v := mul_comm _ _
    have h4 : -(v : ℂ) * I = -(I * v) := by ring
    rw [h1, h2, h3, h4]
    have e1 : cexp (I * u) * cexp (-(I * u)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have e2 : cexp (I * v) * cexp (-(I * v)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    calc (cexp (I * u) - cexp (I * v)) * (cexp (I * u) - cexp (-I * v))
        = (cexp (I * u) - cexp (I * v)) * (cexp (I * u) - cexp (-(I * v))) := by rw [neg_mul]
      _ = cexp (I * u) * (cexp (I * u) - cexp (I * v) - cexp (-(I * v))) +
            cexp (I * v) * cexp (-(I * v)) := by ring
      _ = cexp (I * u) * (cexp (I * u) - cexp (I * v) - cexp (-(I * v))) +
            cexp (I * u) * cexp (-(I * u)) := by rw [e2, e1]
      _ = 2 * cexp (I * u) * ((cexp (I * u) + cexp (-(I * u))) / 2 -
            (cexp (I * v) + cexp (-(I * v))) / 2) := by ring
  constructor
  · intro hcos
    have hzero : (cexp (I * u) - cexp (I * v)) * (cexp (I * u) - cexp (-I * v)) = 0 := by
      rw [hprod, hcos, sub_self, mul_zero]
    rcases mul_eq_zero.mp hzero with h1 | h2
    · have hexp : cexp (I * ((u - v : ℝ) : ℂ)) = 1 := by
        rw [show I * ((u - v : ℝ) : ℂ) = I * u - I * v by push_cast; ring, Complex.exp_sub]
        exact div_eq_one_iff_eq (Complex.exp_ne_zero _) |>.mpr (sub_eq_zero.mp h1)
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
      have him := congrArg Complex.im hm
      simp at him
      exact ⟨m, Or.inl (by linarith)⟩
    · have hexp : cexp (I * ((u + v : ℝ) : ℂ)) = 1 := by
        rw [show I * ((u + v : ℝ) : ℂ) = I * u - (-I * v) by push_cast; ring, Complex.exp_sub]
        exact div_eq_one_iff_eq (Complex.exp_ne_zero _) |>.mpr (sub_eq_zero.mp h2)
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
      have him := congrArg Complex.im hm
      simp at him
      exact ⟨m, Or.inr (by linarith)⟩
  · rintro ⟨m, h1 | h2⟩
    · rw [h1, Real.cos_add_int_mul_two_pi]
    · rw [h2, Real.cos_add_int_mul_two_pi, Real.cos_neg]

theorem cos_mul_log_eq_iff {a : ℝ} (ha : 1 < a) (ω γ : ℝ) :
    Real.cos (ω * Real.log a) = Real.cos (γ * Real.log a) ↔
      ∃ m : ℤ, ω = γ + (m : ℝ) * (2 * Real.pi / Real.log a) ∨
        ω = -γ + (m : ℝ) * (2 * Real.pi / Real.log a) := by
  have hloga : 0 < Real.log a := Real.log_pos ha
  rw [cos_eq_cos_iff_exists_int]
  refine exists_congr fun m => or_congr ?_ ?_
  · constructor
    · intro h
      have hsub : (ω - γ) * Real.log a = (m : ℝ) * (2 * Real.pi) := by linarith
      have hdiv := (eq_div_iff hloga.ne').mpr hsub
      linarith [show (m : ℝ) * (2 * Real.pi) / Real.log a = (m : ℝ) * (2 * Real.pi / Real.log a)
        by ring]
    · intro h; rw [h]; field_simp [hloga.ne']
  · constructor
    · intro h
      have hsub : (ω + γ) * Real.log a = (m : ℝ) * (2 * Real.pi) := by linarith
      have hdiv := (eq_div_iff hloga.ne').mpr hsub
      linarith [show (m : ℝ) * (2 * Real.pi) / Real.log a = (m : ℝ) * (2 * Real.pi / Real.log a)
        by ring]
    · intro h; rw [h]; field_simp [hloga.ne']

private theorem sqrt_mul_log_sq_le_rpow {y δ : ℝ} (hy : 1 ≤ y) (hδ : 0 < δ) :
    Real.sqrt y * Real.log y ^ 2 ≤ (4 / δ ^ 2) * y ^ (1 / 2 + δ) := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hη : 0 < δ / 2 := half_pos hδ
  have hlog : Real.log y ≤ (2 / δ) * y ^ (δ / 2) := by
    have h1 : Real.log (y ^ (δ / 2)) ≤ y ^ (δ / 2) - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy0 _)
    rw [Real.log_rpow hy0] at h1
    have h2 : (δ / 2) * Real.log y ≤ y ^ (δ / 2) := by linarith
    calc Real.log y = (2 / δ) * ((δ / 2) * Real.log y) := by field_simp
      _ ≤ (2 / δ) * y ^ (δ / 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have hlog_sq : Real.log y ^ 2 ≤ (4 / δ ^ 2) * y ^ δ := by
    calc Real.log y ^ 2 ≤ ((2 / δ) * y ^ (δ / 2)) ^ 2 :=
          pow_le_pow_left₀ hlog0 hlog 2
      _ = (4 / δ ^ 2) * (y ^ (δ / 2)) ^ (2 : ℕ) := by ring
      _ = (4 / δ ^ 2) * y ^ δ := by
          rw [← Real.rpow_natCast (y ^ (δ / 2)) 2, ← Real.rpow_mul hy0.le]
          congr 2; push_cast; ring
  calc Real.sqrt y * Real.log y ^ 2
      ≤ y ^ (1 / 2 : ℝ) * ((4 / δ ^ 2) * y ^ δ) := by
        rw [← Real.sqrt_eq_rpow]
        exact mul_le_mul_of_nonneg_left hlog_sq (Real.sqrt_nonneg y)
    _ = (4 / δ ^ 2) * (y ^ (1 / 2 : ℝ) * y ^ δ) := by ring
    _ = (4 / δ ^ 2) * y ^ (1 / 2 + δ) := by rw [← Real.rpow_add hy0]

/-- **All-`ε` Mellin pole-pinning across `{Re s > 1/2}`.** If `|R_a(β, γ; x)| / (√x log² x)` is
not unbounded (`a > 1`), then every zero `ρ ≠ 1` of `ζ` in `{Re s > 1/2}` has `Re ρ = β` and
`cos(Im ρ · log a) = cos(γ log a)`. -/
theorem re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded {a β γ : ℝ} (ha : 1 < a)
    (hbdd : ¬ IsSqrtLogSqUnbounded (primeDilationResidual a β γ))
    {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ ≠ 1) (hζ : riemannZeta ρ = 0) :
    ρ.re = β ∧ Real.cos (ρ.im * Real.log a) = Real.cos (γ * Real.log a) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  obtain ⟨C, X₀, hC⟩ := (isSqrtLogSqUnbounded_iff_not_eventually_le _).not_left.mp hbdd
  set C' : ℝ := max C 0
  set δ : ℝ := (ρ.re - 1 / 2) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  set σ₀ : ℝ := 1 / 2 + δ
  have hσ₀_lt : σ₀ < ρ.re := by dsimp [σ₀, δ]; linarith
  have hbnd : ∀ y : ℝ, a ^ 2 * max X₀ 1 ≤ y →
      |dilationSetOp a β {γ} Chebyshev.psi y - mainTermFactor a β {γ} * y| ≤
        (C' * (4 / δ ^ 2)) * y ^ σ₀ := by
    intro y hy
    set x : ℝ := y / a ^ 2
    have hy_eq : a ^ 2 * x = y := by dsimp [x]; field_simp [ha0.ne']
    have hx_ge : max X₀ 1 ≤ x := by
      rw [le_div_iff₀ (pow_pos ha0 2), mul_comm]
      exact hy
    have hx1 : 1 ≤ x := (le_max_right _ _).trans hx_ge
    have hy1 : 1 ≤ y := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ a ^ 2 * x := mul_le_mul (one_le_pow₀ ha.le) hx1 zero_le_one (by positivity)
        _ = y := hy_eq
    have hx_le_y : x ≤ y := by
      rw [← hy_eq]
      exact le_mul_of_one_le_left (zero_lt_one.trans_le hx1).le (one_le_pow₀ ha.le)
    have h1 := hC x ((le_max_left _ _).trans hx_ge)
    have h2 : C * Real.sqrt x * Real.log x ^ 2 ≤ C' * Real.sqrt x * Real.log x ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg x)) (sq_nonneg _)
    have hlog_mono : Real.log x ^ 2 ≤ Real.log y ^ 2 :=
      pow_le_pow_left₀ (Real.log_nonneg hx1) (Real.log_le_log (zero_lt_one.trans_le hx1) hx_le_y) 2
    have hsqrt_mono : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hx_le_y
    calc |dilationSetOp a β {γ} Chebyshev.psi y - mainTermFactor a β {γ} * y|
        = |primeDilationResidual a β γ x| := by
          rw [← hy_eq, primeDilationResidual_eq_dilationSetOp ha0]
      _ ≤ C' * Real.sqrt x * Real.log x ^ 2 := h1.trans h2
      _ ≤ C' * Real.sqrt y * Real.log y ^ 2 := by
          have hm := mul_le_mul hsqrt_mono hlog_mono (sq_nonneg _) (Real.sqrt_nonneg y)
          calc C' * Real.sqrt x * Real.log x ^ 2 = C' * (Real.sqrt x * Real.log x ^ 2) := by ring
            _ ≤ C' * (Real.sqrt y * Real.log y ^ 2) :=
                mul_le_mul_of_nonneg_left hm (le_max_right C 0)
            _ = C' * Real.sqrt y * Real.log y ^ 2 := by ring
      _ = C' * (Real.sqrt y * Real.log y ^ 2) := by ring
      _ ≤ C' * ((4 / δ ^ 2) * y ^ σ₀) :=
          mul_le_mul_of_nonneg_left (sqrt_mul_log_sq_le_rpow hy1 hδ) (le_max_right C 0)
      _ = (C' * (4 / δ ^ 2)) * y ^ σ₀ := by ring
  obtain ⟨hre, α, hα, m, hm⟩ :=
    re_eq_and_im_mem_periodic_of_dilation_bound ha hbnd hσ₀_lt hρ1 hζ
  refine ⟨hre, (cos_mul_log_eq_iff ha ρ.im γ).mpr ?_⟩
  rcases Finset.mem_union.mp hα with hpos | hneg
  · rw [Finset.mem_singleton.mp hpos] at hm
    exact ⟨m, Or.inl hm⟩
  · obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.mp hneg
    rw [Finset.mem_singleton.mp hω] at hm
    exact ⟨m, Or.inr hm⟩

/-! ### 4. Two-prime cross-sign aliasing vs. three-prime pigeonhole de-aliasing -/

/-- `ω` is a positive cross-resonant ordinate partner of `γ` for primes `(p, q)`: `0 < ω`, `ω ≠ γ`,
and `cos(ω log a) = cos(γ log a)` holds at both `a = p` and `a = q`. -/
def IsCrossResonantPair (p q : ℕ) (γ ω : ℝ) : Prop :=
  0 < ω ∧ ω ≠ γ ∧
    Real.cos (ω * Real.log p) = Real.cos (γ * Real.log p) ∧
    Real.cos (ω * Real.log q) = Real.cos (γ * Real.log q)

private theorem same_sign_lattice_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {m n : ℤ}
    (heq : (m : ℝ) * (2 * Real.pi / Real.log p) = (n : ℝ) * (2 * Real.pi / Real.log q)) :
    m = 0 ∧ n = 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hirr : Irrational (Real.log q / Real.log p) := RHTower.irrational_log_ratio hp hq hpq
  by_cases hm0 : m = 0
  · subst hm0
    simp only [Int.cast_zero, zero_mul] at heq
    have hnR : (n : ℝ) = 0 := by
      rcases mul_eq_zero.mp heq.symm with h | h
      · exact h
      · exfalso
        exact (div_pos (mul_pos two_pos Real.pi_pos) hlogq).ne' h
    exact ⟨rfl, Int.cast_eq_zero.mp hnR⟩
  · exfalso
    have hmR : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm0
    have hpi : 2 * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    have hdiv : (m : ℝ) / Real.log p = (n : ℝ) / Real.log q := by
      apply mul_right_cancel₀ hpi
      calc (m : ℝ) / Real.log p * (2 * Real.pi)
          = (m : ℝ) * (2 * Real.pi / Real.log p) := by ring
        _ = (n : ℝ) * (2 * Real.pi / Real.log q) := heq
        _ = (n : ℝ) / Real.log q * (2 * Real.pi) := by ring
    have hrel := (div_eq_div_iff hlogp.ne' hlogq.ne').mp hdiv
    have hrat : Real.log q / Real.log p = (n : ℝ) / (m : ℝ) := by
      rw [div_eq_div_iff hlogp.ne' hmR]
      linarith
    exact hirr ⟨(n : ℚ) / (m : ℚ), by push_cast; exact hrat.symm⟩

/-- **Uniqueness of the cross-resonant partner.** For distinct primes `p ≠ q` and `γ > 0`, at most
one `ω > 0` satisfies `IsCrossResonantPair p q γ ω`. -/
theorem isCrossResonantPair_unique {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {γ ω₁ ω₂ : ℝ} (hγ : 0 < γ)
    (h₁ : IsCrossResonantPair p q γ ω₁) (h₂ : IsCrossResonantPair p q γ ω₂) :
    ω₁ = ω₂ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hnorm : ∀ ω : ℝ, IsCrossResonantPair p q γ ω →
      ∃ ε m n : ℤ, (ε = 1 ∨ ε = -1) ∧
        (ε : ℝ) * ω = γ + (m : ℝ) * (2 * Real.pi / Real.log p) ∧
        (ε : ℝ) * ω = -γ + (n : ℝ) * (2 * Real.pi / Real.log q) := by
    rintro ω ⟨hω_pos, hω_ne, hcp, hcq⟩
    obtain ⟨mp, hp_case⟩ := (cos_mul_log_eq_iff hp1 ω γ).mp hcp
    obtain ⟨nq, hq_case⟩ := (cos_mul_log_eq_iff hq1 ω γ).mp hcq
    rcases hp_case with hp_pos | hp_neg <;> rcases hq_case with hq_pos | hq_neg
    · exfalso
      have hmn := same_sign_lattice_eq hp hq hpq (by linarith : (mp : ℝ) * _ = (nq : ℝ) * _)
      rw [hmn.1] at hp_pos; simp at hp_pos; exact hω_ne hp_pos
    · exact ⟨1, mp, nq, Or.inl rfl, by simp [hp_pos], by simp [hq_neg]⟩
    · refine ⟨-1, -mp, -nq, Or.inr rfl, ?_, ?_⟩
      · push_cast; linarith [hp_neg]
      · push_cast; linarith [hq_pos]
    · exfalso
      have hmn := same_sign_lattice_eq hp hq hpq (by linarith : (mp : ℝ) * _ = (nq : ℝ) * _)
      rw [hmn.1] at hp_neg; simp at hp_neg; linarith
  obtain ⟨ε₁, m₁, n₁, hε₁, h₁p, h₁q⟩ := hnorm ω₁ h₁
  obtain ⟨ε₂, m₂, n₂, hε₂, h₂p, h₂q⟩ := hnorm ω₂ h₂
  have hrel : ((m₁ - m₂ : ℤ) : ℝ) * (2 * Real.pi / Real.log p) =
      ((n₁ - n₂ : ℤ) : ℝ) * (2 * Real.pi / Real.log q) := by
    push_cast; linarith
  have hmn := same_sign_lattice_eq hp hq hpq hrel
  have hm_eq : m₁ = m₂ := sub_eq_zero.mp hmn.1
  subst hm_eq
  have hε_eq : (ε₁ : ℝ) * ω₁ = (ε₂ : ℝ) * ω₂ := h₁p.trans h₂p.symm
  have habs : |(ε₁ : ℝ) * ω₁| = |(ε₂ : ℝ) * ω₂| := congrArg abs hε_eq
  have ha1 : |(ε₁ : ℝ)| = 1 := by rcases hε₁ with rfl | rfl <;> norm_num
  have ha2 : |(ε₂ : ℝ)| = 1 := by rcases hε₂ with rfl | rfl <;> norm_num
  rw [abs_mul, abs_mul, ha1, ha2, one_mul, one_mul, abs_of_pos h₁.1, abs_of_pos h₂.1] at habs
  exact habs

/-- **Complete two-prime cosine classification.** For distinct primes `p ≠ q`, `γ > 0`, and any
`ω ≠ 0` satisfying `cos(ω log p) = cos(γ log p)` and `cos(ω log q) = cos(γ log q)`, either
`|ω| = γ` (`ω = ±γ`) or `IsCrossResonantPair p q γ |ω|`. -/
theorem abs_eq_or_isCrossResonantPair_of_twoPrime_cos_eq {p q : ℕ} {γ ω : ℝ} (hω : ω ≠ 0)
    (hcp : Real.cos (ω * Real.log p) = Real.cos (γ * Real.log p))
    (hcq : Real.cos (ω * Real.log q) = Real.cos (γ * Real.log q)) :
    |ω| = γ ∨ IsCrossResonantPair p q γ |ω| := by
  by_cases heq : |ω| = γ
  · exact Or.inl heq
  · right
    have hcos_abs : ∀ L : ℝ, Real.cos (|ω| * L) = Real.cos (ω * L) := fun L => by
      rcases abs_choice ω with h | h <;> rw [h]
      simp [neg_mul, Real.cos_neg]
    exact ⟨abs_pos.mpr hω, heq, (hcos_abs _).trans hcp, (hcos_abs _).trans hcq⟩

/-- **Density of `(2, 3)` cross-resonant pairs with arbitrarily high partner ordinate.**
Every open interval `(a, b) ⊂ (0, ∞)` contains a frequency `γ ∈ (a, b)` admitting a `(2, 3)`
cross-resonant partner `ω* > H` (`IsCrossResonantPair 2 3 γ ω*`). -/
theorem dense_exists_isCrossResonantPair {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (H : ℝ) :
    ∃ γ ω : ℝ, a < γ ∧ γ < b ∧ H < ω ∧ IsCrossResonantPair 2 3 γ ω := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hirr : Irrational (Real.log 2 / Real.log 3) :=
    RHTower.irrational_log_ratio Nat.prime_three Nat.prime_two (by decide)
  set gap : ℝ := b - a
  have hgap : 0 < gap := sub_pos.mpr hab
  -- Choose `Q ≥ 3` large enough that `π / (Q * log 2) < min (gap / 6) (gap * (π / log 3) / (3 * (max H 1 + 1)))`
  set target : ℝ := min (gap / 6) (gap * (Real.pi / Real.log 3) / (3 * (max H 1 + 1)))
  have htarget : 0 < target := by
    refine lt_min (by positivity) ?_
    positivity
  obtain ⟨Q₀, hQ₀⟩ := exists_nat_gt (Real.pi / (Real.log 2 * target))
  set Q : ℕ := max Q₀ 3
  have hQ_pos : 0 < Q := by omega
  have hQ3 : (3 : ℝ) ≤ Q := by exact_mod_cast (le_max_right Q₀ 3)
  have hQ_gt : Real.pi / (Real.log 2 * target) < Q :=
    hQ₀.trans_le (by exact_mod_cast (le_max_left Q₀ 3))
  have hstep_bound : Real.pi / ((Q : ℝ) * Real.log 2) < target := by
    have hQlog : 0 < (Q : ℝ) * Real.log 2 := mul_pos (by positivity) hlog2
    rw [div_lt_iff₀ hQlog]
    have hmul := (div_lt_iff₀ (mul_pos hlog2 htarget)).mp hQ_gt
    linarith [show Real.pi < (Q : ℝ) * (Real.log 2 * target) from hmul]
  obtain ⟨n, hn1, _, hclose⟩ :=
    HTGeometry.exists_simultaneous_dirichlet (fun _ : Fin 1 => Real.log 2 / Real.log 3) hQ_pos
  obtain ⟨m, hm⟩ := hclose 0
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm_pos : 0 < m := by
    by_contra hm_le
    push Not at hm_le
    have hmR : (m : ℝ) ≤ 0 := by exact_mod_cast hm_le
    have hratio_gt : (1 : ℝ) / 2 < Real.log 2 / Real.log 3 := by
      rw [div_lt_div_iff₀ (by norm_num) hlog3]
      have h3_lt_4 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
      have hlog4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
      linarith
    have h1 : (1 : ℝ) / 2 < (n : ℝ) * (Real.log 2 / Real.log 3) - m := by
      have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hprod : 1 * (1 / 2 : ℝ) < (n : ℝ) * (Real.log 2 / Real.log 3) :=
        mul_lt_mul' hnR1 hratio_gt (by norm_num) hn_pos
      linarith
    have h2 : |(n : ℝ) * (Real.log 2 / Real.log 3) - m| < 1 / 3 :=
      hm.trans_le (one_div_le_one_div_of_le (by norm_num) hQ3)
    rw [abs_lt] at h2
    linarith
  have hdiff_ne : (n : ℝ) * (Real.log 2 / Real.log 3) - m ≠ 0 := by
    intro h0
    have hrat : Real.log 2 / Real.log 3 = (m : ℝ) / (n : ℝ) := by
      rw [eq_div_iff hn_pos.ne']
      linarith
    exact hirr ⟨(m : ℚ) / (n : ℚ), by push_cast; exact hrat.symm⟩
  set raw : ℝ := (n : ℝ) * (Real.pi / Real.log 3) - (m : ℝ) * (Real.pi / Real.log 2)
  have hraw_eq : raw = (Real.pi / Real.log 2) * ((n : ℝ) * (Real.log 2 / Real.log 3) - m) := by
    dsimp [raw]; field_simp [hlog2.ne', hlog3.ne']
  set δ : ℝ := |raw|
  have hδ_pos : 0 < δ := abs_pos.mpr (by rw [hraw_eq]; exact mul_ne_zero (by positivity) hdiff_ne)
  have hδ_lt : δ < target := by
    dsimp [δ]
    rw [hraw_eq, abs_mul, abs_of_pos (div_pos Real.pi_pos hlog2)]
    calc (Real.pi / Real.log 2) * |(n : ℝ) * (Real.log 2 / Real.log 3) - m|
        < (Real.pi / Real.log 2) * (1 / (Q : ℝ)) :=
          mul_lt_mul_of_pos_left hm (div_pos Real.pi_pos hlog2)
      _ = Real.pi / ((Q : ℝ) * Real.log 2) := by ring
      _ < target := hstep_bound
  have hδ_gap : δ < gap / 6 := hδ_lt.trans_le (min_le_left _ _)
  set k : ℕ := ⌊(a + gap / 3) / δ⌋₊ + 1
  have hk_pos : 0 < k := by omega
  have hkR_gt : (a + gap / 3) / δ < (k : ℝ) := by
    dsimp [k]; push_cast
    exact Nat.lt_floor_add_one _
  have hkR_le : (k : ℝ) ≤ (a + gap / 3) / δ + 1 := by
    dsimp [k]; push_cast
    have hnum0 : 0 ≤ a + gap / 3 := add_nonneg ha (div_nonneg hgap.le (by norm_num : (0 : ℝ) ≤ 3))
    have hfl := Nat.floor_le (div_nonneg hnum0 hδ_pos.le)
    linarith
  set γ : ℝ := (k : ℝ) * δ
  have hγ_gt_a : a < γ := by
    have h := mul_lt_mul_of_pos_right hkR_gt hδ_pos
    rw [div_mul_cancel₀ _ hδ_pos.ne'] at h
    linarith
  have hγ_lt_b : γ < b := by
    have h := mul_le_mul_of_nonneg_right hkR_le hδ_pos.le
    rw [add_mul, div_mul_cancel₀ _ hδ_pos.ne', one_mul] at h
    dsimp [gap] at h hδ_gap
    linarith
  have hk_large : gap / (3 * δ) < (k : ℝ) := by
    have h1 : gap / (3 * δ) = (gap / 3) / δ := by ring
    have h2 : (gap / 3) / δ ≤ (a + gap / 3) / δ :=
      div_le_div_of_nonneg_right (by linarith) hδ_pos.le
    linarith
  set ω : ℝ := (k : ℝ) * ((n : ℝ) * (Real.pi / Real.log 3) + (m : ℝ) * (Real.pi / Real.log 2))
  have hmR_pos : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hω_gt_H : H < ω := by
    have hn_ge1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hsum_ge : Real.pi / Real.log 3 <
        (n : ℝ) * (Real.pi / Real.log 3) + (m : ℝ) * (Real.pi / Real.log 2) := by
      have h1 : Real.pi / Real.log 3 ≤ (n : ℝ) * (Real.pi / Real.log 3) :=
        le_mul_of_one_le_left (by positivity) hn_ge1
      have h2 : 0 < (m : ℝ) * (Real.pi / Real.log 2) := mul_pos hmR_pos (by positivity)
      linarith
    have hδ_bound2 : δ < gap * (Real.pi / Real.log 3) / (3 * (max H 1 + 1)) :=
      hδ_lt.trans_le (min_le_right _ _)
    have h3δ : (max H 1 + 1) * (3 * δ) < gap * (Real.pi / Real.log 3) := by
      have hpos_den : 0 < 3 * (max H 1 + 1) := by positivity
      have hm := (lt_div_iff₀ hpos_den).mp hδ_bound2
      linarith
    have hk_bound : max H 1 + 1 < (k : ℝ) * (Real.pi / Real.log 3) := by
      have h1 : max H 1 + 1 < (gap / (3 * δ)) * (Real.pi / Real.log 3) := by
        rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
        exact h3δ
      exact h1.trans (mul_lt_mul_of_pos_right hk_large (by positivity))
    have hω_gt : (k : ℝ) * (Real.pi / Real.log 3) < ω :=
      mul_lt_mul_of_pos_left hsum_ge (by exact_mod_cast hk_pos)
    linarith [le_max_left H 1]
  have hω_pos : 0 < ω := by
    have h1 : 0 < (n : ℝ) * (Real.pi / Real.log 3) + (m : ℝ) * (Real.pi / Real.log 2) := by
      positivity
    exact mul_pos (by exact_mod_cast hk_pos) h1
  have hω_ne_γ : ω ≠ γ := by
    dsimp [ω, γ, δ]
    rcases le_or_gt 0 raw with hraw0 | hraw_neg
    · rw [abs_of_nonneg hraw0]
      intro heq
      have hsub := mul_left_cancel₀ (show (k : ℝ) ≠ 0 by exact_mod_cast hk_pos.ne') heq
      dsimp [raw] at hsub
      have : (m : ℝ) * (Real.pi / Real.log 2) = 0 := by linarith
      exact (mul_pos hmR_pos (div_pos Real.pi_pos hlog2)).ne' this
    · rw [abs_of_neg hraw_neg]
      intro heq
      have hsub := mul_left_cancel₀ (show (k : ℝ) ≠ 0 by exact_mod_cast hk_pos.ne') heq
      dsimp [raw] at hsub
      have : (n : ℝ) * (Real.pi / Real.log 3) = 0 := by linarith
      exact (mul_pos hn_pos (div_pos Real.pi_pos hlog3)).ne' this
  have hcos2 : Real.cos (ω * Real.log 2) = Real.cos (γ * Real.log 2) := by
    rw [cos_mul_log_eq_iff (by norm_num : (1 : ℝ) < 2)]
    rcases le_or_gt 0 raw with hraw0 | hraw_neg
    · refine ⟨(k : ℤ) * m, Or.inl ?_⟩
      dsimp [ω, γ, δ]; rw [abs_of_nonneg hraw0]; dsimp [raw]; push_cast; ring
    · refine ⟨(k : ℤ) * m, Or.inr ?_⟩
      dsimp [ω, γ, δ]; rw [abs_of_neg hraw_neg]; dsimp [raw]; push_cast; ring
  have hcos3 : Real.cos (ω * Real.log 3) = Real.cos (γ * Real.log 3) := by
    rw [cos_mul_log_eq_iff (by norm_num : (1 : ℝ) < 3)]
    rcases le_or_gt 0 raw with hraw0 | hraw_neg
    · refine ⟨(k : ℤ) * n, Or.inr ?_⟩
      dsimp [ω, γ, δ]; rw [abs_of_nonneg hraw0]; dsimp [raw]; push_cast; ring
    · refine ⟨(k : ℤ) * n, Or.inl ?_⟩
      dsimp [ω, γ, δ]; rw [abs_of_neg hraw_neg]; dsimp [raw]; push_cast; ring
  exact ⟨γ, ω, hγ_gt_a, hγ_lt_b, hω_gt_H, hω_pos, hω_ne_γ, hcos2, hcos3⟩

/-- **Three-prime pigeonhole de-aliasing theorem.** For any three pairwise distinct primes
`p₁, p₂, p₃` and `γ ≥ 0`, simultaneous cosine agreement `cos(ω log p_i) = cos(γ log p_i)`
(`i = 1, 2, 3`) holds if and only if `|ω| = γ` (`ω = γ ∨ ω = -γ`). -/
theorem abs_eq_of_threePrime_cos_eq {p₁ p₂ p₃ : ℕ}
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    {γ ω : ℝ} (hγ : 0 ≤ γ) :
    (Real.cos (ω * Real.log p₁) = Real.cos (γ * Real.log p₁) ∧
      Real.cos (ω * Real.log p₂) = Real.cos (γ * Real.log p₂) ∧
      Real.cos (ω * Real.log p₃) = Real.cos (γ * Real.log p₃)) ↔ |ω| = γ := by
  constructor
  · rintro ⟨hc1, hc2, hc3⟩
    obtain ⟨m₁, h₁⟩ := (cos_mul_log_eq_iff (by exact_mod_cast hp₁.one_lt) ω γ).mp hc1
    obtain ⟨m₂, h₂⟩ := (cos_mul_log_eq_iff (by exact_mod_cast hp₂.one_lt) ω γ).mp hc2
    obtain ⟨m₃, h₃⟩ := (cos_mul_log_eq_iff (by exact_mod_cast hp₃.one_lt) ω γ).mp hc3
    have hfinish_pos : ω = γ → |ω| = γ := fun h => by rw [h, abs_of_nonneg hγ]
    have hfinish_neg : ω = -γ → |ω| = γ := fun h => by rw [h, abs_neg, abs_of_nonneg hγ]
    rcases h₁ with h1p | h1n <;> rcases h₂ with h2p | h2n
    · have hm := same_sign_lattice_eq hp₁ hp₂ h12 (by linarith : (m₁ : ℝ) * _ = (m₂ : ℝ) * _)
      exact hfinish_pos (by rw [hm.1] at h1p; simpa using h1p)
    · rcases h₃ with h3p | h3n
      · have hm := same_sign_lattice_eq hp₁ hp₃ h13 (by linarith : (m₁ : ℝ) * _ = (m₃ : ℝ) * _)
        exact hfinish_pos (by rw [hm.1] at h1p; simpa using h1p)
      · have hm := same_sign_lattice_eq hp₂ hp₃ h23 (by linarith : (m₂ : ℝ) * _ = (m₃ : ℝ) * _)
        exact hfinish_neg (by rw [hm.1] at h2n; simpa using h2n)
    · rcases h₃ with h3p | h3n
      · have hm := same_sign_lattice_eq hp₂ hp₃ h23 (by linarith : (m₂ : ℝ) * _ = (m₃ : ℝ) * _)
        exact hfinish_pos (by rw [hm.1] at h2p; simpa using h2p)
      · have hm := same_sign_lattice_eq hp₁ hp₃ h13 (by linarith : (m₁ : ℝ) * _ = (m₃ : ℝ) * _)
        exact hfinish_neg (by rw [hm.1] at h1n; simpa using h1n)
    · have hm := same_sign_lattice_eq hp₁ hp₂ h12 (by linarith : (m₁ : ℝ) * _ = (m₂ : ℝ) * _)
      exact hfinish_neg (by rw [hm.1] at h1n; simpa using h1n)
  · intro habs
    have hcos : ∀ L : ℝ, Real.cos (ω * L) = Real.cos (γ * L) := fun L => by
      rw [← habs]
      rcases abs_choice ω with h | h <;> rw [h]
      simp [neg_mul, Real.cos_neg]
    exact ⟨hcos _, hcos _, hcos _⟩

/-- **Planted two-wave separation between two clocks `{2, 3}` and three clocks `{2, 3, 5}`.**
At every `(2, 3)` cross-resonant pair `(γ, ω*)` with `γ > 0` and `β ∈ (1/2, 1)`, the two-frequency
real wave `f(x) = Re(x^{β + iγ}) + Re(x^{β + iω*})` satisfies `HasPositivePowerLimsup f β` and is
identically annihilated on `(0, ∞)` by both `dilationRecurrenceOp 2 β γ` and
`dilationRecurrenceOp 3 β γ`, whereas `dilationRecurrenceOp 5 β γ f` has unbounded ratio against
`√x log² x`. -/
theorem plantedAliasedDoubleWave_separates_two_and_three_clocks
    {β γ ω : ℝ} (hβ : 1 / 2 < β) (hγ : 0 < γ) (hres : IsCrossResonantPair 2 3 γ ω) :
    let f : ℝ → ℝ := fun x =>
      ((1 : ℂ) * (x : ℂ) ^ ((β : ℂ) + I * γ)).re +
        ((1 : ℂ) * (x : ℂ) ^ ((β : ℂ) + I * ω)).re
    HasPositivePowerLimsup f β ∧
      (∀ x : ℝ, 0 < x → dilationRecurrenceOp 2 β γ f x = 0) ∧
      (∀ x : ℝ, 0 < x → dilationRecurrenceOp 3 β γ f x = 0) ∧
      IsSqrtLogSqUnbounded (dilationRecurrenceOp 5 β γ f) := by
  intro f
  have h2_zero : ∀ x : ℝ, 0 < x → dilationRecurrenceOp 2 β γ f x = 0 := fun x hx => by
    rw [dilationRecurrenceOp_add,
      dilationRecurrenceOp_re_cpow_eq_zero (a := 2) (by norm_num) hx rfl 1,
      dilationRecurrenceOp_re_cpow_eq_zero (a := 2) (by norm_num) hx (by simpa using hres.2.2.1) 1,
      add_zero]
  have h3_zero : ∀ x : ℝ, 0 < x → dilationRecurrenceOp 3 β γ f x = 0 := fun x hx => by
    rw [dilationRecurrenceOp_add,
      dilationRecurrenceOp_re_cpow_eq_zero (a := 3) (by norm_num) hx rfl 1,
      dilationRecurrenceOp_re_cpow_eq_zero (a := 3) (by norm_num) hx (by simpa using hres.2.2.2) 1,
      add_zero]
  -- At clock 5, `cos(ω log 5) ≠ cos(γ log 5)` by three-prime de-aliasing
  have hcos5_ne : Real.cos (ω * Real.log 5) ≠ Real.cos (γ * Real.log 5) := by
    intro hc5
    have habs := (abs_eq_of_threePrime_cos_eq Nat.prime_two Nat.prime_three Nat.prime_five
      (by decide) (by decide) (by decide) hγ.le).mp ⟨hres.2.2.1, hres.2.2.2, hc5⟩
    rw [abs_of_pos hres.1] at habs
    exact hres.2.1 habs
  -- Compute `dilationRecurrenceOp 5 β γ f x` for `x > 0`
  set D₅ : ℂ := dilationSymbol 5 (dilationPairPoly 5 β γ) ((β : ℂ) + I * ω) *
    ((25 : ℝ) : ℂ) ^ ((β : ℂ) + I * ω)
  have hD₅_ne : D₅ ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro hsym
      have hset : dilationPairPoly 5 β γ = dilationSetPoly 5 β {γ} := by simp [dilationSetPoly]
      rw [hset, dilationSymbol_dilationSetPoly_eq (by norm_num : (0 : ℝ) < 5),
        Finset.prod_singleton] at hsym
      have hextract : ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
          (5 : ℂ) ^ (((β : ℂ) + I * (sgn * γ : ℝ)) - ((β : ℂ) + I * ω)) = 1 → False := by
        intro sgn hsgn h1
        have hlog5_eq : Complex.log 5 = (Real.log 5 : ℂ) := by
          rw [show (5 : ℂ) = ((5 : ℝ) : ℂ) by norm_num,
            ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 5)]
        rw [Complex.cpow_def_of_ne_zero (by norm_num), hlog5_eq, Complex.exp_eq_one_iff] at h1
        obtain ⟨m, hm⟩ := h1
        have him : Real.log 5 * (sgn * γ - ω) = (m : ℝ) * (2 * Real.pi) := by
          have h := congrArg Complex.im hm
          simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat,
            Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
            Complex.I_re, Complex.I_im] at h
          linear_combination h
        apply hcos5_ne
        rw [cos_eq_cos_iff_exists_int]
        refine ⟨-m, ?_⟩
        rcases hsgn with rfl | rfl
        · left; push_cast; linarith
        · right; push_cast; linarith
      rcases mul_eq_zero.mp hsym with hpos | hneg
      · refine hextract 1 (Or.inl rfl) ?_
        simpa using (sub_eq_zero.mp hpos).symm
      · refine hextract (-1) (Or.inr rfl) ?_
        have hrew : (β : ℂ) + I * ((-1 * γ : ℝ) : ℂ) - ((β : ℂ) + I * ω) =
            (β : ℂ) - I * γ - ((β : ℂ) + I * ω) := by push_cast; ring
        rw [hrew]
        exact (sub_eq_zero.mp hneg).symm
    · rw [Complex.cpow_def_of_ne_zero (by norm_num)]
      exact Complex.exp_ne_zero _
  have h5_eval : ∀ x : ℝ, 0 < x →
      dilationRecurrenceOp 5 β γ f x = (D₅ * (x : ℂ) ^ ((β : ℂ) + I * ω)).re := by
    intro x hx
    rw [dilationRecurrenceOp_add,
      dilationRecurrenceOp_re_cpow_eq_zero (by norm_num) hx rfl 1, zero_add,
      dilationRecurrenceOp_re_cpow_eq (by norm_num) hx]
    have hmul : ((5 ^ 2 * x : ℝ) : ℂ) ^ ((β : ℂ) + I * ω) =
        ((25 : ℝ) : ℂ) ^ ((β : ℂ) + I * ω) * (x : ℂ) ^ ((β : ℂ) + I * ω) := by
      rw [show (5 : ℝ) ^ 2 * x = 25 * x by norm_num, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (by norm_num) hx.le]
    rw [hmul]
    dsimp [D₅]
    ring_nf
  -- Along `u_k = (-arg D₅ + 2π k) / ω`, `(D₅ * (e^{u_k})^{β + iω}).re = ‖D₅‖ e^{β u_k}`
  have hD₅_limsup : HasPositivePowerLimsup (dilationRecurrenceOp 5 β γ f) β := by
    refine ⟨‖D₅‖, norm_pos_iff.mpr hD₅_ne, fun X₀ => ?_⟩
    set U₀ : ℝ := Real.log (max X₀ 1)
    obtain ⟨k, hk⟩ := exists_nat_gt ((ω * U₀ + Complex.arg D₅) / (2 * Real.pi))
    set u : ℝ := (-Complex.arg D₅ + (k : ℝ) * (2 * Real.pi)) / ω
    have hu_gt : U₀ < u := by
      rw [lt_div_iff₀ hres.1]
      have hm := (div_lt_iff₀ (mul_pos two_pos Real.pi_pos)).mp hk
      linarith
    set x : ℝ := Real.exp u
    have hx_pos : 0 < x := Real.exp_pos u
    have hx_ge : X₀ ≤ x := by
      calc X₀ ≤ max X₀ 1 := le_max_left _ _
        _ = Real.exp U₀ := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp u := Real.exp_le_exp.mpr hu_gt.le
    refine ⟨x, hx_ge, ?_⟩
    rw [h5_eval x hx_pos]
    have hcpow : (x : ℂ) ^ ((β : ℂ) + I * ω) =
        (Real.exp (β * u) : ℂ) * cexp (I * ((ω * u : ℝ) : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx_pos.ne'),
        ← Complex.ofReal_log hx_pos.le, show Real.log x = u from Real.log_exp u,
        show (u : ℂ) * ((β : ℂ) + I * ω) = ((β * u : ℝ) : ℂ) + I * ((ω * u : ℝ) : ℂ) by
          push_cast; ring,
        Complex.exp_add, Complex.ofReal_exp]
    have hphase : cexp (I * ((ω * u : ℝ) : ℂ)) = cexp (-I * Complex.arg D₅) := by
      have hωu : ω * u = -Complex.arg D₅ + (k : ℝ) * (2 * Real.pi) := by
        dsimp [u]; exact mul_div_cancel₀ _ hres.1.ne'
      rw [hωu, show I * ((-Complex.arg D₅ + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) =
        -I * Complex.arg D₅ + (k : ℂ) * (2 * Real.pi * I) by push_cast; ring,
        Complex.exp_add, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, mul_one]
    have hprod_D : D₅ * cexp (-I * Complex.arg D₅) = (‖D₅‖ : ℂ) := by
      calc D₅ * cexp (-I * Complex.arg D₅)
          = (‖D₅‖ * cexp (Complex.arg D₅ * I)) * cexp (-(Complex.arg D₅ * I)) := by
            rw [Complex.norm_mul_exp_arg_mul_I D₅]
            congr 2; ring
        _ = (‖D₅‖ : ℂ) * (cexp (Complex.arg D₅ * I) * cexp (-(Complex.arg D₅ * I))) := by ring
        _ = (‖D₅‖ : ℂ) := by rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    have hval : (D₅ * (x : ℂ) ^ ((β : ℂ) + I * ω)).re = ‖D₅‖ * x ^ β := by
      rw [hcpow, hphase, show D₅ * ((Real.exp (β * u) : ℂ) * cexp (-I * Complex.arg D₅)) =
        (Real.exp (β * u) : ℂ) * (D₅ * cexp (-I * Complex.arg D₅)) by ring,
        hprod_D, ← Complex.ofReal_mul, Complex.ofReal_re]
      have hxβ : x ^ β = Real.exp (β * u) := by
        dsimp [x]; rw [← Real.exp_mul]; ring_nf
      rw [hxβ, mul_comm]
    rw [hval, abs_of_pos (mul_pos (norm_pos_iff.mpr hD₅_ne) (Real.rpow_pos_of_pos hx_pos β))]
  -- From `HasPositivePowerLimsup (dilationRecurrenceOp 5 β γ f) β` (`β > 1/2`), deduce unboundedness
  have h5_unb : IsSqrtLogSqUnbounded (dilationRecurrenceOp 5 β γ f) := by
    rw [isSqrtLogSqUnbounded_iff_not_eventually_le]
    rintro ⟨C, X₀, hC⟩
    obtain ⟨c, hc, hfreq⟩ := hD₅_limsup
    set δ : ℝ := (β - 1 / 2) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    set C₁ : ℝ := max C 0 * (4 / δ ^ 2) + 1
    have hC₁ : 0 < C₁ := by positivity
    set X₁ : ℝ := max X₀ (max 2 ((C₁ / c) ^ (1 / δ) + 1))
    obtain ⟨x, hx, hcx⟩ := hfreq X₁
    have hx0 : X₀ ≤ x := (le_max_left _ _).trans hx
    have hx2 : 2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
    have hlarge : (C₁ / c) ^ (1 / δ) < x := by
      have := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
      linarith
    have hx1 : 1 ≤ x := by linarith
    have hx_pos : 0 < x := by linarith
    have hub : |dilationRecurrenceOp 5 β γ f x| ≤ C₁ * x ^ (1 / 2 + δ) := by
      calc |dilationRecurrenceOp 5 β γ f x|
          ≤ C * Real.sqrt x * Real.log x ^ 2 := hC x hx0
        _ ≤ max C 0 * Real.sqrt x * Real.log x ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg x)) (sq_nonneg _)
        _ = max C 0 * (Real.sqrt x * Real.log x ^ 2) := by ring
        _ ≤ max C 0 * ((4 / δ ^ 2) * x ^ (1 / 2 + δ)) :=
            mul_le_mul_of_nonneg_left (sqrt_mul_log_sq_le_rpow hx1 hδ) (le_max_right C 0)
        _ ≤ C₁ * x ^ (1 / 2 + δ) := by
            dsimp [C₁]
            have : 0 < x ^ (1 / 2 + δ) := Real.rpow_pos_of_pos hx_pos _
            nlinarith
    have hxδ : C₁ / c < x ^ δ := by
      have h1 := Real.rpow_lt_rpow (by positivity) hlarge hδ
      rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hδ.ne', Real.rpow_one] at h1
    have hgt : C₁ * x ^ (1 / 2 + δ) < c * x ^ β := by
      have hmul := mul_lt_mul_of_pos_left hxδ hc
      rw [mul_div_cancel₀ _ hc.ne'] at hmul
      have hpow : x ^ β = x ^ (1 / 2 + δ) * x ^ δ := by
        rw [← Real.rpow_add hx_pos]; congr 1; dsimp [δ]; ring
      rw [hpow]
      nlinarith [Real.rpow_pos_of_pos hx_pos (1 / 2 + δ)]
    linarith
  -- Deduce `HasPositivePowerLimsup f β` from `hD₅_limsup` (`D_5` cannot create `x^β` out of `o(x^β)`)
  have hf_limsup : HasPositivePowerLimsup f β := by
    obtain ⟨c₅, hc₅, hfreq₅⟩ := hD₅_limsup
    set M₅ : ℝ := 25 ^ β + 2 * 5 ^ β * 5 ^ β + 5 ^ (2 * β)
    have hM₅ : 0 < M₅ := by dsimp [M₅]; positivity
    refine ⟨c₅ / (3 * M₅), div_pos hc₅ (by positivity), fun X₀ => ?_⟩
    obtain ⟨x, hx, hcx⟩ := hfreq₅ (max X₀ 1)
    have hx0 : X₀ ≤ x := (le_max_left _ _).trans hx
    have hx_pos : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx)
    by_contra hall
    push Not at hall
    set c₀ : ℝ := c₅ / (3 * M₅)
    have hx0' : |f x| < c₀ * x ^ β := hall x hx0
    have hx1' : |f (5 * x)| < c₀ * (5 * x) ^ β := hall (5 * x) (by linarith)
    have hx2' : |f (5 ^ 2 * x)| < c₀ * (5 ^ 2 * x) ^ β := hall (5 ^ 2 * x) (by linarith)
    have h5x : (5 * x) ^ β = 5 ^ β * x ^ β := Real.mul_rpow (by norm_num) hx_pos.le
    have h25x : (5 ^ 2 * x) ^ β = 25 ^ β * x ^ β := by
      rw [show (5 : ℝ) ^ 2 = 25 by norm_num]
      exact Real.mul_rpow (by norm_num) hx_pos.le
    have hcos_le : |Real.cos (γ * Real.log 5)| ≤ 1 := Real.abs_cos_le_one _
    have htri : |dilationRecurrenceOp 5 β γ f x| ≤
        |f (5 ^ 2 * x)| + 2 * 5 ^ β * |f (5 * x)| + 5 ^ (2 * β) * |f x| := by
      unfold dilationRecurrenceOp
      have h1 : |f (5 ^ 2 * x) - 2 * 5 ^ β * Real.cos (γ * Real.log 5) * f (5 * x) +
            5 ^ (2 * β) * f x| ≤
          |f (5 ^ 2 * x)| + |2 * 5 ^ β * Real.cos (γ * Real.log 5) * f (5 * x)| +
            |5 ^ (2 * β) * f x| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      have h2 : |2 * 5 ^ β * Real.cos (γ * Real.log 5) * f (5 * x)| ≤ 2 * 5 ^ β * |f (5 * x)| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos two_pos,
          abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 5) β)]
        calc 2 * 5 ^ β * |Real.cos (γ * Real.log 5)| * |f (5 * x)|
            ≤ 2 * 5 ^ β * 1 * |f (5 * x)| :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcos_le (by positivity)) (abs_nonneg _)
          _ = 2 * 5 ^ β * |f (5 * x)| := by ring
      have h3 : |5 ^ (2 * β) * f x| = 5 ^ (2 * β) * |f x| := by
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 5) (2 * β))]
      linarith
    have hsum_lt : |dilationRecurrenceOp 5 β γ f x| < c₀ * M₅ * x ^ β := by
      have ht2 : |f (5 ^ 2 * x)| < c₀ * 25 ^ β * x ^ β := by
        calc |f (5 ^ 2 * x)| < c₀ * (5 ^ 2 * x) ^ β := hx2'
          _ = c₀ * 25 ^ β * x ^ β := by rw [h25x]; ring
      have ht1 : 2 * 5 ^ β * |f (5 * x)| < c₀ * (2 * 5 ^ β * 5 ^ β) * x ^ β := by
        have hpos : (0 : ℝ) < 2 * 5 ^ β :=
          mul_pos two_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 5) β)
        calc 2 * 5 ^ β * |f (5 * x)| < 2 * 5 ^ β * (c₀ * (5 * x) ^ β) :=
              mul_lt_mul_of_pos_left hx1' hpos
          _ = c₀ * (2 * 5 ^ β * 5 ^ β) * x ^ β := by rw [h5x]; ring
      have ht0 : 5 ^ (2 * β) * |f x| < c₀ * 5 ^ (2 * β) * x ^ β := by
        have hpos : (0 : ℝ) < 5 ^ (2 * β) :=
          Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 5) (2 * β)
        calc 5 ^ (2 * β) * |f x| < 5 ^ (2 * β) * (c₀ * x ^ β) :=
              mul_lt_mul_of_pos_left hx0' hpos
          _ = c₀ * 5 ^ (2 * β) * x ^ β := by ring
      have hsum3 : |f (5 ^ 2 * x)| + 2 * 5 ^ β * |f (5 * x)| + 5 ^ (2 * β) * |f x| <
          c₀ * M₅ * x ^ β := by
        calc |f (5 ^ 2 * x)| + 2 * 5 ^ β * |f (5 * x)| + 5 ^ (2 * β) * |f x|
            < c₀ * 25 ^ β * x ^ β + c₀ * (2 * 5 ^ β * 5 ^ β) * x ^ β +
                c₀ * 5 ^ (2 * β) * x ^ β := add_lt_add (add_lt_add ht2 ht1) ht0
          _ = c₀ * M₅ * x ^ β := by dsimp [M₅]; ring
      exact htri.trans_lt hsum3
    have hc₀M : c₀ * M₅ * x ^ β = (c₅ / 3) * x ^ β := by
      have h1 : c₀ * M₅ = c₅ / 3 := by dsimp [c₀]; field_simp [hM₅.ne']
      rw [h1]
    rw [hc₀M] at hsum_lt
    have hxβ_pos : 0 < x ^ β := Real.rpow_pos_of_pos hx_pos β
    have hthird : (c₅ / 3) * x ^ β < c₅ * x ^ β :=
      mul_lt_mul_of_pos_right (by linarith) hxβ_pos
    linarith
  exact ⟨hf_limsup, h2_zero, h3_zero, h5_unb⟩

/-! ### 5. Unconditional zones for `primeError` (`β > 20999/24000`, `β < Θ`, `γ ≤ 67`) -/

/-- Above `RHTower.zeroReSup`, `primeError` satisfies `¬ HasPositivePowerLimsup primeError β`. -/
theorem not_hasPositivePowerLimsup_of_zeroReSup_lt {β : ℝ} (hβ : RHTower.zeroReSup < β) :
    ¬ HasPositivePowerLimsup primeError β := by
  set b : ℝ := (RHTower.zeroReSup + β) / 2
  have hb_gt : RHTower.zeroReSup < b := by dsimp [b]; linarith
  have hb_lt : b < β := by dsimp [b]; linarith
  obtain ⟨C, hC0, hC⟩ := RHTower.exists_abs_chebyshevPsi_sub_le_rpow hb_gt
  rintro ⟨c, hc, hfreq⟩
  set δ : ℝ := β - b
  have hδ : 0 < δ := sub_pos.mpr hb_lt
  set X₁ : ℝ := max 1 (((C + 1) / c) ^ (1 / δ) + 1)
  obtain ⟨x, hx, hcx⟩ := hfreq X₁
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx_pos : 0 < x := zero_lt_one.trans_le hx1
  have hlarge : ((C + 1) / c) ^ (1 / δ) < x := by
    have := (le_max_right _ _).trans hx; linarith
  have hxδ : (C + 1) / c < x ^ δ := by
    have h1 := Real.rpow_lt_rpow (by positivity) hlarge hδ
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hδ.ne', Real.rpow_one] at h1
  have hmul := mul_lt_mul_of_pos_left hxδ hc
  rw [mul_div_cancel₀ _ hc.ne'] at hmul
  have hpow : x ^ β = x ^ b * x ^ δ := by
    rw [← Real.rpow_add hx_pos]; congr 1; dsimp [δ]; ring
  have hpe : |primeError x| ≤ C * x ^ b := hC x hx1
  have hxb_pos : 0 < x ^ b := Real.rpow_pos_of_pos hx_pos b
  rw [hpow] at hcx
  nlinarith

theorem zeroReSup_le_sub_seven_eighths : RHTower.zeroReSup ≤ 20999 / 24000 := by
  refine RHTower.zeroReSup_le_of_forall_re_le fun q => ?_
  exact (MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip
    (xiZeroCopy_re_pos q) (riemannZeta_eq_zero_of_xiZeroCopy q)).2

/-- **Unconditional quasi-RH upper zone (`β > 20999 / 24000`).** For every `β > 20999 / 24000`,
`limsup_{x → ∞} |ψ(x) − x| / x^β = 0`. -/
theorem not_hasPositivePowerLimsup_of_sub_seven_eighths_lt {β : ℝ} (hβ : 20999 / 24000 < β) :
    ¬ HasPositivePowerLimsup primeError β :=
  not_hasPositivePowerLimsup_of_zeroReSup_lt (zeroReSup_le_sub_seven_eighths.trans_lt hβ)

/-- **Unconditional two-clock recurrence law on `(20999 / 24000, 1)`.** -/
theorem twoClock_unbounded_of_sub_seven_eighths_lt {β γ : ℝ} (hβ : 20999 / 24000 < β)
    (hlim : HasPositivePowerLimsup primeError β) :
    IsSqrtLogSqUnbounded (primeDilationResidual 2 β γ) ∨
      IsSqrtLogSqUnbounded (primeDilationResidual 3 β γ) :=
  False.elim (not_hasPositivePowerLimsup_of_sub_seven_eighths_lt hβ hlim)

/-- **Unconditional sub-abscissa zone (`1/2 < β < zeroReSup`).** Whenever `1/2 < β < zeroReSup`,
`HasPositivePowerLimsup primeError β` holds **and** `|R_a(β, γ; x)| / (√x log² x)` is unbounded
for **every** clock `a > 1` (in particular for both `a = 2` and `a = 3` simultaneously). -/
theorem hasPositivePowerLimsup_and_all_clocks_unbounded_of_lt_zeroReSup {β : ℝ}
    (hlo : 1 / 2 < β) (hhi : β < RHTower.zeroReSup) :
    HasPositivePowerLimsup primeError β ∧
      ∀ a : ℝ, 1 < a → ∀ γ : ℝ, IsSqrtLogSqUnbounded (primeDilationResidual a β γ) := by
  refine ⟨⟨1, one_pos, fun X₀ => ?_⟩, fun a ha γ => ?_⟩
  · have hfreq := RHTower.frequently_rpow_lt_chebyshevPsi_sub hhi
    rw [Filter.frequently_atTop] at hfreq
    obtain ⟨x, hx, hgt⟩ := hfreq (max X₀ 1)
    have hx_pos : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx)
    refine ⟨x, (le_max_left _ _).trans hx, ?_⟩
    rw [one_mul, primeError]
    exact hgt.le.trans (le_abs_self _)
  · by_contra hbdd
    have hall : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β := by
      intro q
      rcases le_or_gt (q.1 : ℂ).re (1 / 2) with hle | hgt
      · exact hle.trans hlo.le
      · have hre := (re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded ha hbdd hgt
          (xiZeroCopy_ne_one q) (riemannZeta_eq_zero_of_xiZeroCopy q)).1
        exact hre.le
    exact not_le_of_gt hhi (RHTower.zeroReSup_le_of_forall_re_le hall)

/-- Every off-line nontrivial zero `ρ` of `ζ` satisfies `67 < |Im ρ|`. -/
theorem sixtySeven_lt_abs_im_of_offLine_zeta_zero {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hoff : ρ.re ≠ 1 / 2) :
    67 < |ρ.im| := by
  by_contra hle
  push Not at hle
  have hne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  have hxi : xi ρ = 0 := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mpr hζ
  obtain ⟨q, hq_eq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  have him_ne : ρ.im ≠ 0 := by
    have h4 := four_lt_abs_zeroOrdinate q
    rw [zeroOrdinate, hq_eq] at h4
    intro h0'; rw [h0', abs_zero] at h4; linarith
  rcases lt_or_gt_of_ne him_ne with hneg | hpos
  · have hxi_c : xi (starRingEnd ℂ ρ) = 0 := by rw [xi_conj, hxi, map_zero]
    have hhalf := VerifiedHeightRungs.HadamardBudget.rhVerifiedThrough_sixtySeven hxi_c
      (by simpa using h0) (by simpa using h1) (by simpa using hneg)
      (by simpa [abs_of_neg hneg] using hle)
    exact hoff (by simpa using hhalf)
  · have hhalf := VerifiedHeightRungs.HadamardBudget.rhVerifiedThrough_sixtySeven hxi h0 h1 hpos
      (by rwa [abs_of_pos hpos] at hle)
    exact hoff hhalf

/-- **Unconditional verified-height-67 resolution for three clocks `{2, 3, 5}`.**
For every `β > 1/2` and `0 < γ ≤ 67`, if `HasPositivePowerLimsup primeError β`, then at least one
of `R_2, R_3, R_5` has unbounded ratio against `√x log² x`. -/
theorem threeClock_unbounded_of_le_sixtySeven {β γ : ℝ} (hβ : 1 / 2 < β)
    (hγ0 : 0 < γ) (hγ67 : γ ≤ 67) (hlim : HasPositivePowerLimsup primeError β) :
    IsSqrtLogSqUnbounded (primeDilationResidual 2 β γ) ∨
      IsSqrtLogSqUnbounded (primeDilationResidual 3 β γ) ∨
      IsSqrtLogSqUnbounded (primeDilationResidual 5 β γ) := by
  by_contra hnot
  push Not at hnot
  obtain ⟨hb2, hb3, hb5⟩ := hnot
  have hall_half : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 := by
    intro q
    by_contra hgt
    push Not at hgt
    have hp2 := re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded (by norm_num : (1 : ℝ) < 2)
      hb2 hgt (xiZeroCopy_ne_one q) (riemannZeta_eq_zero_of_xiZeroCopy q)
    have hp3 := re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded (by norm_num : (1 : ℝ) < 3)
      hb3 hgt (xiZeroCopy_ne_one q) (riemannZeta_eq_zero_of_xiZeroCopy q)
    have hp5 := re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded (by norm_num : (1 : ℝ) < 5)
      hb5 hgt (xiZeroCopy_ne_one q) (riemannZeta_eq_zero_of_xiZeroCopy q)
    have habs : |(q.1 : ℂ).im| = γ :=
      (abs_eq_of_threePrime_cos_eq Nat.prime_two Nat.prime_three Nat.prime_five
        (by decide) (by decide) (by decide) hγ0.le).mp ⟨hp2.2, hp3.2, hp5.2⟩
    have h67 := sixtySeven_lt_abs_im_of_offLine_zeta_zero (riemannZeta_eq_zero_of_xiZeroCopy q)
      (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q) (by linarith)
    linarith
  exact not_hasPositivePowerLimsup_of_zeroReSup_lt
    ((RHTower.zeroReSup_le_of_forall_re_le hall_half).trans_lt hβ) hlim

/-- **Unconditional verified-height-67 resolution for two clocks `{2, 3}`.**
For every `β > 1/2` and `0 < γ ≤ 67` admitting no `(2, 3)` cross-resonant partner above `67`
(in particular every non-cross-resonant `γ ∈ (0, 67]`), `HasPositivePowerLimsup primeError β`
forces `R_2` or `R_3` to have unbounded ratio against `√x log² x`. -/
theorem twoClock_unbounded_of_le_sixtySeven {β γ : ℝ} (hβ : 1 / 2 < β)
    (_hγ0 : 0 < γ) (hγ67 : γ ≤ 67)
    (hno_high_alias : ∀ ω : ℝ, IsCrossResonantPair 2 3 γ ω → ω ≤ 67)
    (hlim : HasPositivePowerLimsup primeError β) :
    IsSqrtLogSqUnbounded (primeDilationResidual 2 β γ) ∨
      IsSqrtLogSqUnbounded (primeDilationResidual 3 β γ) := by
  by_contra hnot
  push Not at hnot
  obtain ⟨hb2, hb3⟩ := hnot
  have hall_half : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 := by
    intro q
    by_contra hgt
    push Not at hgt
    have hp2 := re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded (by norm_num : (1 : ℝ) < 2)
      hb2 hgt (xiZeroCopy_ne_one q) (riemannZeta_eq_zero_of_xiZeroCopy q)
    have hp3 := re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded (by norm_num : (1 : ℝ) < 3)
      hb3 hgt (xiZeroCopy_ne_one q) (riemannZeta_eq_zero_of_xiZeroCopy q)
    have h67 := sixtySeven_lt_abs_im_of_offLine_zeta_zero (riemannZeta_eq_zero_of_xiZeroCopy q)
      (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q) (by linarith)
    have him_ne : (q.1 : ℂ).im ≠ 0 := by intro h0; rw [h0, abs_zero] at h67; linarith
    rcases abs_eq_or_isCrossResonantPair_of_twoPrime_cos_eq (p := 2) (q := 3) him_ne hp2.2 hp3.2
      with habs | halias
    · linarith
    · linarith [hno_high_alias |(q.1 : ℂ).im| halias]
  exact not_hasPositivePowerLimsup_of_zeroReSup_lt
    ((RHTower.zeroReSup_le_of_forall_re_le hall_half).trans_lt hβ) hlim

#print axioms primeDilationResidual_eq_dilationSetOp
#print axioms re_eq_and_cos_im_eq_of_not_isSqrtLogSqUnbounded
#print axioms isCrossResonantPair_unique
#print axioms dense_exists_isCrossResonantPair
#print axioms abs_eq_of_threePrime_cos_eq
#print axioms plantedAliasedDoubleWave_separates_two_and_three_clocks
#print axioms twoClock_unbounded_of_sub_seven_eighths_lt
#print axioms hasPositivePowerLimsup_and_all_clocks_unbounded_of_lt_zeroReSup
#print axioms threeClock_unbounded_of_le_sixtySeven
#print axioms twoClock_unbounded_of_le_sixtySeven

end GaloisForLFunctions.ZeroConfigurationGeometry
