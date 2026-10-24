import GaloisForLFunctions.TransHorizonIncidenceMechanics.ThePhaseLawOfOscillatingPrimePatterns
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ThePrimeMeanIsQuantizedHeightByHeight
import GaloisForLFunctions.TransHorizonIncidenceMechanics.PrefixStabilityAndCriticalWienerClosureOfMoebiusRows

/-!
# Multi-frequency prime patterns, prime-varying amplitudes, and general multiplicative spectra

This module extends the multiplicative phase diagrams of §3.18 to general completely multiplicative
spectra `f : ℕ →*₀ ℝ` with `|f(p)| ≤ 1`, finite multi-frequency oscillating prime patterns, and
prime-varying amplitudes:

1. **General multiplicative spectra via the prime Dirichlet series (`primeDirichletSeries`)**
   (`abs_log_norm_patternSeries_sub_re_primeDirichletSeries_le`,
   `not_receiverBounded_pattern_half_of_primeDirichletSeries_re_ge`,
   `int_localPrimeMean_of_receiverBounded_damped`):
   For every completely multiplicative `f : ℕ →*₀ ℝ` with `|f(p)| ≤ 1` and `Re w > 1`, the Euler
   product compares `log ‖∑_n f(n) n^{-w}‖` within `S = ∑_p p^{-2}` to the real part of the prime
   Dirichlet series `ℓ_f(w) = ∑_p f(p) p^{-w}`. Consequently:
   - at half damping (`ε = 1/2`), if at any height `t₀ ∈ ℝ` with `ζ(1/2 + i t₀) ≠ 0` the prime sum
     obeys `Re ℓ_f(1 + u + i(t₀ + τ)) ≥ (1/2) log(1/(u + τ)) − B` for small `u > 0, τ ≥ 0`, the
     boundary line energy grows like `log(1/u)` and `f(d) d^{-1/2}` is unpaid;
   - below half damping (`0 < ε < 1/2`), if at any height `t₀ ≠ 0` the prime sum along the
     horizontal ray `1 + u + i t₀` obeys `|Re ℓ_f(1 + u + i t₀) − ν log(1/u)| ≤ B`, a paid receiver
     forces `ν ∈ ℤ` (and `ν = 0` whenever `|ν| < 1`).

2. **Multi-singularity line-energy criterion and separated product collapse**
   (`exists_lineEnergy_le_of_majorant_finset`, `receiverBounded_pattern_half_of_sum_bounds`,
   `exists_prod_rpow_neg_add_one_le_sum`, `norm_patternSeries_le_prod_of_prime_sum`):
   Dominating `‖F(w)‖` on `1 < Re w ≤ 2` by `A (1 + ∑_{k ∈ K} |Im w − t_k|^{-b_k})` with `2 b_k < 1`
   on `(0, T]` and by `B₁ (Im w)^{1/4}` above `T` pays the half-damped receiver. For pairwise
   distinct frequencies `t_k`, the product `∏_{k ∈ K} (|y − t_k|^{-b_k} + 1)` collapses to a linear
   combination `C (1 + ∑_{k ∈ K} |y − t_k|^{-b_k})` because `|t_j − t_k| ≤ |y − t_j| + |y − t_k|`
   prevents simultaneous proximity to two distinct heights.

3. **The complete phase diagram of multi-frequency prime patterns**
   (`receiverBounded_multiPhaseWeight_of_forall_lt_one`,
   `not_receiverBounded_multiPhaseWeight_of_eq_one`, `receiverBounded_multiPhaseWeight_iff`,
   `receiverBounded_multiPhaseWeight_of_two_active`,
   `cos_coeff_eq_zero_of_receiverBounded_multiPhase_damped`):
   For `f(p) = ∑_{k ∈ K} a_k cos(t_k log p + φ_k)` with pairwise distinct positive frequencies
   `t_k > 0`:
   - if `|f(p)| ≤ 1`, `|a_k| ≤ 1`, and `a_k cos φ_k < 1` for all `k ∈ K`, the half-damped weight is
     paid;
   - if `a_{k₀} cos φ_{k₀} = 1` for some `k₀ ∈ K` and `ζ(1/2 + i t_{k₀}) ≠ 0`, the half-damped
     weight is unpaid;
   - under the amplitude budget `∑_{k ∈ K} |a_k| ≤ 1`, `multiPhaseWeight K a t φ` is paid if and
     only if `∀ k ∈ K, a_k cos φ_k < 1 ∨ ζ(1/2 + i t_k) = 0`; in particular, sharing the budget
     across two or more active frequencies (`a_{k₁} ≠ 0, a_{k₂} ≠ 0`) always pays the half-damped
     receiver unconditionally;
   - below half damping (`0 < ε < 1/2`), payment forces `a_k cos φ_k = 0` at every frequency `k ∈ K`.

4. **Prime-varying amplitudes and critical Wiener prime-perturbation invariance**
   (`criticalWiener_mul_patternMoebiusAF`, `receiverBounded_of_summable_prime_diff`,
   `receiverBounded_iff_of_summable_prime_diff`, `horizonRows_bounded_of_summable_prime_diff`,
   `receiverBounded_primeVaryingPhase_half_iff`, `receiverBounded_primeVaryingMultiPhase_half_iff`):
   For any multiplicative `f' : ArithmeticFunction ℝ` with `|f'(n)| ≤ 1` and any completely
   multiplicative `f : ℕ →*₀ ℝ` with `|f(p)| ≤ 1`, the defect kernel `g = f' ⋆ μf` satisfies
   `g(p^{m+1}) = f'(p^{m+1}) − f(p) f'(p^m)` with no unimodularity assumption. Whenever
   `∑_p |f'(p) − f(p)| p^{-(1/2 + ε)} < ∞` (`ε > 0`), `g d^{-ε}` lies in `CriticalWiener`, so both
   full-receiver payment and uniform horizon-row payment transfer between `f` and `f'`.
-/

open Finset Filter Topology MeasureTheory Complex Set
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### §1. General multiplicative spectra via the prime Dirichlet series -/

/-- The prime Dirichlet series (prime Euler logarithm) `ℓ_f(w) = ∑_p f(p) p^{-w}` of a completely
multiplicative pattern `f : ℕ →*₀ ℝ`. -/
def primeDirichletSeries (f : ℕ →*₀ ℝ) (w : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (f p : ℂ) * ((p : ℕ) : ℂ) ^ (-w)

theorem summable_primeDirichletSeries {f : ℕ →*₀ ℝ} (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1)
    {w : ℂ} (hw : 1 < w.re) :
    Summable (fun p : Nat.Primes => (f p : ℂ) * ((p : ℕ) : ℂ) ^ (-w)) := by
  refine (summable_prime_cpow_neg hw).norm.of_norm_bounded fun p => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hf p p.2)

/-- For any completely multiplicative `f` with `|f(p)| ≤ 1`, the Dirichlet series `∑_n f(n) n^{-w}`
is nonvanishing on `Re w > 1` (by its Euler product). -/
theorem patternSeries_ne_zero {f : ℕ →*₀ ℝ} (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1)
    {w : ℂ} (hw : 1 < w.re) :
    ∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) ≠ 0 := by
  set g := cweightedPatternHom f w
  have habs := abs_patternHom_le_one f hf
  have hsum : Summable (fun n => ‖g n‖) := by
    refine (Real.summable_nat_rpow.mpr (show -w.re < -1 by linarith)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun n => ?_
    simp only [g, cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow (show -w.re ≠ 0 by intro h; linarith)]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hn0.le _) (habs n)
  have hE := EulerProduct.exp_tsum_primes_log_eq_tsum hsum
  have hFn : ∑' n, g n = ∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) := tsum_congr fun n => rfl
  rw [← hFn, ← hE]
  exact Complex.exp_ne_zero _

/-- **Two-sided Euler-logarithm comparison for general multiplicative patterns.** On `Re w > 1`,
`|log ‖∑_n f(n) n^{-w}‖ − Re ℓ_f(w)| ≤ S`, where `S = ∑_p p^{-2}`. -/
theorem abs_log_norm_patternSeries_sub_re_primeDirichletSeries_le {f : ℕ →*₀ ℝ}
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) {w : ℂ} (hw : 1 < w.re) :
    |Real.log ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ - (primeDirichletSeries f w).re| ≤
      primeSquareMass := by
  have habs := abs_patternHom_le_one f hf
  have hF := abs_log_norm_tsum_sub_re_le (cweightedPatternHom f w) hw fun n => by
    simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_natCast]
    exact mul_le_of_le_one_left (norm_nonneg _) (habs n)
  have hFn : ∑' n, cweightedPatternHom f w n = ∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) :=
    tsum_congr fun n => rfl
  have hFp : ∑' p : Nat.Primes, cweightedPatternHom f w p = primeDirichletSeries f w :=
    tsum_congr fun p => by
      simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
        Complex.ofReal_natCast]
  rwa [hFn, hFp, ← primeSquareMass] at hF

/-- **Exponential Euler pinch for general multiplicative patterns.** On `Re w > 1`,
`e^{-S + Re ℓ_f(w)} ≤ ‖∑_n f(n) n^{-w}‖ ≤ e^{S + Re ℓ_f(w)}`. -/
theorem norm_patternSeries_bounds_of_primeDirichletSeries {f : ℕ →*₀ ℝ}
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) {w : ℂ} (hw : 1 < w.re) :
    Real.exp (-primeSquareMass + (primeDirichletSeries f w).re) ≤
        ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ∧
      ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        Real.exp (primeSquareMass + (primeDirichletSeries f w).re) := by
  have hpos := norm_pos_iff.mpr (patternSeries_ne_zero hf hw)
  have h := abs_le.mp (abs_log_norm_patternSeries_sub_re_primeDirichletSeries_le hf hw)
  rw [← Real.exp_log hpos]
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩

/-- **Universal half-damped critical lower-bound obstruction.** Let `f : ℕ →*₀ ℝ` satisfy
`|f(p)| ≤ 1`. If at some height `t₀ ∈ ℝ` with `ζ(1/2 + i t₀) ≠ 0`, the real part of the prime
Dirichlet series obeys
`(1/2) log(1/(u + τ)) − B ≤ Re ℓ_f(1 + u + i(t₀ + τ))`
for `0 < u ≤ r₁` and `0 ≤ τ ≤ r₁` (`r₁ > 0`), then the half-damped weight `f(d) d^{-1/2}` has
unbounded receiver. -/
theorem not_receiverBounded_pattern_half_of_primeDirichletSeries_re_ge {f : ℕ →*₀ ℝ}
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) {t₀ r₁ B : ℝ}
    (hz : riemannZeta (1 / 2 + (t₀ : ℂ) * I) ≠ 0) (hr₁ : 0 < r₁)
    (hre : ∀ u τ : ℝ, 0 < u → u ≤ r₁ → 0 ≤ τ → τ ≤ r₁ →
      (1 / 2 : ℝ) * Real.log ((u + τ)⁻¹) - B ≤
        (primeDirichletSeries f (((1 + u : ℝ) : ℂ) + ((t₀ + τ : ℝ) : ℂ) * I)).re) :
    ¬ ReceiverBounded (fun d => f d * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by
  rintro ⟨E, hE⟩
  set c : ℕ → ℝ := fun d => f d * (d : ℝ) ^ (-(1 / 2 : ℝ))
  have habs := abs_patternHom_le_one f hf
  have hc : DampedClass 1 (1 / 2) c := fun d => by
    simp only [c]
    rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (habs d)
  set m : ℝ := ∑' d : ℕ, c d / d
  have hs₀1 : (1 / 2 + (t₀ : ℂ) * I : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num at this
  obtain ⟨r₀, hr₀, hζ0⟩ := exists_norm_zeta_gt_near hs₀1 hz
  have hc₀ : 0 < ‖riemannZeta (1 / 2 + (t₀ : ℂ) * I)‖ := norm_pos_iff.mpr hz
  set r : ℝ := min (min (r₀ / 4) r₁) (1 / 4)
  have hr : 0 < r := lt_min (lt_min (by positivity) hr₁) (by norm_num)
  have hr4 : r ≤ 1 / 4 := min_le_right _ _
  have hrr₁ : r ≤ r₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hrr₀ : 2 * r < r₀ := by
    have := (min_le_left (min (r₀ / 4) r₁) (1 / 4)).trans (min_le_left _ _)
    linarith
  set A₀ : ℝ := ((‖riemannZeta (1 / 2 + (t₀ : ℂ) * I)‖ / 2) / (‖(1 / 2 + (t₀ : ℂ) * I : ℂ)‖ + 1)) ^ 2
  have hA₀ : 0 < A₀ := by positivity
  set κ : ℝ := A₀ * Real.exp (-(2 * (primeSquareMass + B))) / 2
  have hκ : 0 < κ := by positivity
  set C' : ℝ := A₀ * m ^ 2
  -- Pointwise lower bound on the line integrand for `0 < u ≤ r, 0 ≤ τ ≤ r`
  have hpt : ∀ u τ : ℝ, 0 < u → u ≤ r → 0 ≤ τ → τ ≤ r →
      κ / (u + τ) - C' ≤ lineIntegrand c m (1 / 2 + u) (t₀ + τ) := by
    intro u τ hu hur hτ hτr
    set s : ℂ := ((1 / 2 + u : ℝ) : ℂ) + ((t₀ + τ : ℝ) : ℂ) * I
    have hss₀ : s - (1 / 2 + (t₀ : ℂ) * I) = (u : ℂ) + (τ : ℂ) * I := by
      simp only [s]; push_cast; ring
    have hnorm_ut : ‖(u : ℂ) + (τ : ℂ) * I‖ ≤ u + τ := by
      have := Complex.norm_le_abs_re_add_abs_im ((u : ℂ) + (τ : ℂ) * I)
      simpa [abs_of_pos hu, abs_of_nonneg hτ] using this
    have hut : 0 < u + τ := by linarith
    have hζs := hζ0 s (by rw [hss₀]; linarith)
    have hs1 : ‖s‖ ≤ ‖(1 / 2 + (t₀ : ℂ) * I : ℂ)‖ + 1 := by
      have h : ‖s‖ ≤ ‖(1 / 2 + (t₀ : ℂ) * I : ℂ)‖ + ‖s - (1 / 2 + (t₀ : ℂ) * I)‖ := by
        calc ‖s‖ = ‖(1 / 2 + (t₀ : ℂ) * I : ℂ) + (s - (1 / 2 + (t₀ : ℂ) * I))‖ := by congr 1; ring
          _ ≤ _ := norm_add_le _ _
      rw [hss₀] at h; linarith
    have hsre : s.re = 1 / 2 + u := by simp [s]
    have hs0 : 0 < ‖s‖ := by
      have := Complex.abs_re_le_norm s
      rw [hsre, abs_of_pos (by linarith)] at this; linarith
    set w : ℂ := ((1 + u : ℝ) : ℂ) + ((t₀ + τ : ℝ) : ℂ) * I
    have hw_eq : s + 1 / 2 = w := by simp only [s, w]; push_cast; ring
    have hwre : 1 < w.re := by simp [w]; linarith
    have hP := (norm_patternSeries_bounds_of_primeDirichletSeries hf hwre).1
    have hre_ut := hre u τ hu (hur.trans hrr₁) hτ (hτr.trans hrr₁)
    set Pn := ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
    have hPn_low : Real.exp (-(primeSquareMass + B)) * ((u + τ)⁻¹) ^ (1 / 2 : ℝ) ≤ Pn := by
      have hexp : Real.exp (-(primeSquareMass + B)) * ((u + τ)⁻¹) ^ (1 / 2 : ℝ) =
          Real.exp (-primeSquareMass + ((1 / 2 : ℝ) * Real.log ((u + τ)⁻¹) - B)) := by
        rw [Real.rpow_def_of_pos (inv_pos.mpr hut), ← Real.exp_add, mul_comm (Real.log _)]
        congr 1; ring
      rw [hexp]
      exact (Real.exp_le_exp.mpr (by linarith)).trans hP
    have hP2 : Real.exp (-(2 * (primeSquareMass + B))) * (u + τ)⁻¹ ≤ Pn ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) hPn_low 2
      rw [mul_pow, rpow_half_sq (by positivity), ← Real.exp_nat_mul,
        show ((2 : ℕ) : ℝ) * -(primeSquareMass + B) = -(2 * (primeSquareMass + B)) by
          push_cast; ring] at h
      exact h
    set Y := ‖weightDirichletSeries c s - (m : ℂ)‖
    have hPY : Pn ≤ Y + |m| := by
      have h := norm_sub_norm_le (weightDirichletSeries c s) (m : ℂ)
      have hW : ‖weightDirichletSeries c s‖ = Pn := by
        rw [weightDirichletSeries_pattern f s, hw_eq]
      rw [hW, Complex.norm_real, Real.norm_eq_abs] at h
      linarith
    have hY0 : 0 ≤ Y := norm_nonneg _
    have hYP : Pn ^ 2 / 2 - m ^ 2 ≤ Y ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) hPY 2
      nlinarith [sq_nonneg (Y - |m|), sq_abs m]
    have hint : lineIntegrand c m (1 / 2 + u) (t₀ + τ) = (‖riemannZeta s‖ * Y / ‖s‖) ^ 2 := by
      simp only [lineIntegrand, norm_div, norm_mul]; rfl
    rw [hint]
    have hbound := sq_div_ge_of_bounds (by positivity) hζs.le hs0 hs1 hY0 hYP hP2
    refine le_trans (le_of_eq ?_) hbound
    simp only [κ, C', A₀]
    field_simp
  -- Contradict the uniform line-energy bound `4πE` as `u ↓ 0`
  have hE0 : 0 ≤ E := by simpa [weightPronicEnergy] using hE 0
  have hup : ∀ u : ℝ, 0 < u → u ≤ r → ∫ t, lineIntegrand c m (1 / 2 + u) t ≤ 4 * Real.pi * E := by
    intro u hu hur
    have hσ : 1 / 2 < 1 / 2 + u := by linarith
    have hσ1 : 1 / 2 + u < 1 := by linarith
    have hid := sum_sq_mul_mellinCell_eq_lineEnergy hc hσ hσ1
    have hcap := tsum_sq_mul_mellinCell_le_of_energy (weightCenteredPrefix_zero c m) hσ.le hE
    have h : (1 / 2 + u) / Real.pi * ∫ t, lineIntegrand c m (1 / 2 + u) t ≤ 4 * (1 / 2 + u) * E :=
      hid.symm.le.trans hcap
    have hpi := Real.pi_pos
    rw [div_mul_eq_mul_div, div_le_iff₀ hpi] at h
    nlinarith
  have hlow : ∀ u : ℝ, 0 < u → u ≤ r →
      κ * Real.log ((u + r) / u) - C' * r ≤ ∫ t, lineIntegrand c m (1 / 2 + u) t := by
    intro u hu hur
    have hσ : 1 / 2 < 1 / 2 + u := by linarith
    have hσ1 : 1 / 2 + u < 1 := by linarith
    have hfi : Integrable (lineIntegrand c m (1 / 2 + u)) := integrable_lineEnergy hc hσ hσ1
    have hf0 : 0 ≤ᵐ[volume] lineIntegrand c m (1 / 2 + u) :=
      Eventually.of_forall fun t => by simp only [Pi.zero_apply, lineIntegrand]; positivity
    have hinv : IntervalIntegrable (fun τ : ℝ => (u + τ)⁻¹) volume 0 r := by
      refine ContinuousOn.intervalIntegrable ((continuousOn_const.add continuousOn_id).inv₀ ?_)
      intro τ hτ
      rw [uIcc_of_le hr.le] at hτ
      have : 0 < u + τ := by linarith [hτ.1]
      exact this.ne'
    have hg : IntervalIntegrable (fun τ : ℝ => κ * (u + τ)⁻¹ - C') volume 0 r :=
      (hinv.const_mul κ).sub intervalIntegrable_const
    have hval : ∫ τ in (0 : ℝ)..r, (κ * (u + τ)⁻¹ - C') =
        κ * Real.log ((u + r) / u) - C' * r := by
      rw [intervalIntegral.integral_sub (hinv.const_mul κ) intervalIntegrable_const,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_add_left (fun x => x⁻¹), add_zero,
        integral_inv_of_pos hu (by linarith), intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hfs : IntervalIntegrable (fun τ => lineIntegrand c m (1 / 2 + u) (t₀ + τ)) volume 0 r :=
      (hfi.comp_add_left t₀).intervalIntegrable
    have hshift : ∫ τ in (0 : ℝ)..r, lineIntegrand c m (1 / 2 + u) (t₀ + τ) =
        ∫ t in t₀..t₀ + r, lineIntegrand c m (1 / 2 + u) t := by
      rw [intervalIntegral.integral_comp_add_left (fun t => lineIntegrand c m (1 / 2 + u) t) t₀,
        add_zero]
    calc κ * Real.log ((u + r) / u) - C' * r
        = ∫ τ in (0 : ℝ)..r, (κ * (u + τ)⁻¹ - C') := hval.symm
      _ ≤ ∫ τ in (0 : ℝ)..r, lineIntegrand c m (1 / 2 + u) (t₀ + τ) :=
          intervalIntegral.integral_mono_on hr.le hg hfs fun τ hτ => by
            have := hpt u τ hu hur hτ.1 hτ.2
            rwa [div_eq_mul_inv] at this
      _ = ∫ t in t₀..t₀ + r, lineIntegrand c m (1 / 2 + u) t := hshift
      _ = ∫ t in Ioc t₀ (t₀ + r), lineIntegrand c m (1 / 2 + u) t :=
          intervalIntegral.integral_of_le (by linarith)
      _ ≤ ∫ t, lineIntegrand c m (1 / 2 + u) t := setIntegral_le_integral hfi hf0
  set X : ℝ := (4 * Real.pi * E + |C'| * r + 1) / κ
  have hX : 0 < X := by have := Real.pi_pos; positivity
  set u : ℝ := r * Real.exp (-X)
  have hu : 0 < u := by positivity
  have hur : u ≤ r := mul_le_of_le_one_right hr.le (Real.exp_le_one_iff.mpr (by linarith))
  have hlog : X ≤ Real.log ((u + r) / u) := by
    have hru : r / u = Real.exp X := by
      simp only [u]
      rw [div_mul_eq_div_div, div_self hr.ne', one_div, ← Real.exp_neg, neg_neg]
    calc X = Real.log (r / u) := by rw [hru, Real.log_exp]
      _ ≤ Real.log ((u + r) / u) :=
          Real.log_le_log (div_pos hr hu) (div_le_div_of_nonneg_right (by linarith) hu.le)
  have h1 := hlow u hu hur
  have h2 := hup u hu hur
  have hκX : κ * X = 4 * Real.pi * E + |C'| * r + 1 := by simp only [X]; field_simp
  have hC'r : C' * r ≤ |C'| * r := mul_le_mul_of_nonneg_right (le_abs_self C') hr.le
  nlinarith [mul_le_mul_of_nonneg_left hlog hκ.le]

/-- **Universal height-local prime-mean quantization below half damping.** Let `f : ℕ →*₀ ℝ`
satisfy `|f(p)| ≤ 1`, and let `0 < ε < 1/2` and `t₀ ≠ 0`. If `f` has local logarithmic prime mean
`ν ∈ ℝ` at height `t₀` along the horizontal ray `1 + u + i t₀`:
`|Re ℓ_f(1 + u + i t₀) − ν log(1/u)| ≤ B` for `0 < u < u₀` (`u₀ > 0`),
and `f(d) d^{-ε}` has bounded receiver, then `ν` is an integer (`∃ k : ℤ, ν = k`). -/
theorem int_localPrimeMean_of_receiverBounded_damped {f : ℕ →*₀ ℝ}
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) {t₀ ε ν B u₀ : ℝ}
    (ht₀ : t₀ ≠ 0) (hε : 0 < ε) (hε2 : ε < 1 / 2) (hu₀ : 0 < u₀)
    (hmean : ∀ u : ℝ, 0 < u → u < u₀ →
      |(primeDirichletSeries f (((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I)).re - ν * Real.log (u⁻¹)| ≤ B)
    (hR : ReceiverBounded (dampedSignWeight f ε)) :
    ∃ k : ℤ, ν = k := by
  obtain ⟨E, hE⟩ := hR
  set c := dampedSignWeight f ε
  have habs := abs_patternHom_le_one f hf
  have hc : DampedClass 1 ε c := fun d => by
    simp only [c, dampedSignWeight]
    rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (habs d)
  set s₁ : ℂ := ((1 - ε : ℝ) : ℂ) + (t₀ : ℂ) * I
  have hs₁1 : s₁ ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp [s₁] at this; exact ht₀ this
  have hs₁re : s₁.re = 1 - ε := by simp [s₁]
  have hΦ : AnalyticAt ℂ (complexMellinPairing (weightCenteredPrefix c (∑' d : ℕ, c d / d))) s₁ :=
    (differentiableOn_complexMellinPairing (weightCenteredPrefix_zero _ _) fun T => hE T).analyticAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) / 2 < s₁.re by rw [hs₁re]; linarith))
  have hζ : AnalyticAt ℂ riemannZeta s₁ := analyticOn_riemannZeta s₁ hs₁1
  set Q : ℂ → ℂ := fun z => complexMellinPairing (weightCenteredPrefix c (∑' d : ℕ, c d / d)) z +
    ((∑' d : ℕ, c d / d : ℝ) : ℂ) * riemannZeta z
  have hQ : AnalyticAt ℂ Q s₁ := hΦ.add (analyticAt_const.mul hζ)
  have hray : ∀ u : ℝ, 0 < u → u < ε →
      weightDirichletSeries c (s₁ + u) * riemannZeta (s₁ + u) = Q (s₁ + u) := by
    intro u hu huε
    have hre : (s₁ + u).re = 1 - ε + u := by rw [Complex.add_re, hs₁re, Complex.ofReal_re]
    have hid := complexMellinPairing_eq_zeta_mul_of_summable (c := c) (θ := 1 - ε + u / 2)
      (s := s₁ + u) (by linarith) (by rw [hre]; linarith) (by rw [hre]; linarith)
      (summable_abs_mul_rpow_of_dampedClass hε hc (by linarith))
    simp only [Q]; rw [hid]; ring
  set κ : ℝ := Real.exp (-(primeSquareMass + |B|))
  set K : ℝ := Real.exp (primeSquareMass + |B|)
  have hκ : 0 < κ := Real.exp_pos _
  have hbd : ∀ u : ℝ, 0 < u → u < u₀ →
      κ * u ^ (-ν) ≤
        ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I))‖ ∧
      ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I))‖ ≤
        K * u ^ (-ν) := by
    intro u hu huu₀
    set w : ℂ := ((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I
    have hwre : 1 < w.re := by simp [w]; linarith
    have hP := norm_patternSeries_bounds_of_primeDirichletSeries hf hwre
    have hm := abs_le.mp ((hmean u hu huu₀).trans (le_abs_self B))
    have hpow : u ^ (-ν) = Real.exp (ν * Real.log (u⁻¹)) := by
      rw [Real.rpow_def_of_pos hu, Real.log_inv]; ring_nf
    rw [hpow, ← Real.exp_add, ← Real.exp_add]
    exact ⟨(Real.exp_le_exp.mpr (by linarith)).trans hP.1,
      hP.2.trans (Real.exp_le_exp.mpr (by linarith))⟩
  have hCeq : ∀ u : ℝ, weightDirichletSeries c (s₁ + u) =
      ∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I)) := by
    intro u
    rw [weightDirichletSeries_dampedSignWeight,
      show s₁ + (u : ℂ) + (ε : ℂ) = ((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I by
        simp only [s₁]; push_cast; ring]
  have hIoo : Set.Ioo (0 : ℝ) (min u₀ ε) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (lt_min hu₀ hε)
  have hζ0 : ¬ ∀ᶠ z in 𝓝 s₁, riemannZeta z = 0 := fun h =>
    RHTower.analyticOrderAt_riemannZeta_ne_top_of_ne_one hs₁1 (analyticOrderAt_eq_top.mpr h)
  obtain ⟨q, Aζ, Bζ, hAζ, hBζ, hζray⟩ := exists_ray_bounds_of_order hζ hζ0
  by_cases hQ0 : ∀ᶠ z in 𝓝 s₁, Q z = 0
  · have hpath : Tendsto (fun u : ℝ => s₁ + (u : ℂ)) (𝓝[>] 0) (𝓝 s₁) := by
      have hcont : Continuous (fun u : ℝ => s₁ + (u : ℂ)) :=
        continuous_const.add Complex.continuous_ofReal
      have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [Complex.ofReal_zero, add_zero] at h
    obtain ⟨u, hQu, hζu, hu⟩ := ((hpath.eventually hQ0).and (hζray.and hIoo)).exists
    have hCu := (hbd u hu.1 (lt_of_lt_of_le hu.2 (min_le_left _ _))).1
    have hprod := hray u hu.1 (lt_of_lt_of_le hu.2 (min_le_right _ _))
    rw [hQu, hCeq] at hprod
    have h1 : 0 < κ * u ^ (-ν) := mul_pos hκ (Real.rpow_pos_of_pos hu.1 _)
    have h2 : 0 < Aζ * u ^ (q : ℝ) := mul_pos hAζ (Real.rpow_pos_of_pos hu.1 _)
    have hpos := mul_pos (lt_of_lt_of_le h1 hCu) (lt_of_lt_of_le h2 hζu.1)
    rw [← norm_mul, hprod, norm_zero] at hpos
    exact absurd hpos (lt_irrefl _)
  obtain ⟨p, AQ, BQ, hAQ, hBQ, hQray⟩ := exists_ray_bounds_of_order hQ hQ0
  have hup : ∀ᶠ u in 𝓝[>] (0 : ℝ), κ * u ^ (-ν) ≤ (BQ / Aζ) * u ^ ((p : ℝ) - q) := by
    filter_upwards [hζray, hQray, hIoo] with u hζu hQu hu
    have hCu := (hbd u hu.1 (lt_of_lt_of_le hu.2 (min_le_left _ _))).1
    have hprod := hray u hu.1 (lt_of_lt_of_le hu.2 (min_le_right _ _))
    rw [hCeq] at hprod
    have hζpos : 0 < Aζ * u ^ (q : ℝ) := mul_pos hAζ (Real.rpow_pos_of_pos hu.1 _)
    have hnorm := congrArg norm hprod
    rw [norm_mul] at hnorm
    rw [Real.rpow_sub hu.1, div_mul_div_comm, le_div_iff₀ hζpos]
    calc κ * u ^ (-ν) * (Aζ * u ^ (q : ℝ))
        ≤ ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I))‖ *
            ‖riemannZeta (s₁ + u)‖ :=
          mul_le_mul hCu hζu.1 hζpos.le (norm_nonneg _)
      _ = ‖Q (s₁ + u)‖ := hnorm
      _ ≤ BQ * u ^ (p : ℝ) := hQu.2
  have hlow : ∀ᶠ u in 𝓝[>] (0 : ℝ), (AQ / Bζ) * u ^ ((p : ℝ) - q) ≤ K * u ^ (-ν) := by
    filter_upwards [hζray, hQray, hIoo] with u hζu hQu hu
    have hCu := (hbd u hu.1 (lt_of_lt_of_le hu.2 (min_le_left _ _))).2
    have hprod := hray u hu.1 (lt_of_lt_of_le hu.2 (min_le_right _ _))
    rw [hCeq] at hprod
    have hζpos : 0 < Bζ * u ^ (q : ℝ) := mul_pos hBζ (Real.rpow_pos_of_pos hu.1 _)
    have hnorm := congrArg norm hprod
    rw [norm_mul] at hnorm
    rw [Real.rpow_sub hu.1, div_mul_div_comm, div_le_iff₀ hζpos]
    have hKpos : 0 ≤ K * u ^ (-ν) := (norm_nonneg _).trans hCu
    calc AQ * u ^ (p : ℝ) ≤ ‖Q (s₁ + u)‖ := hQu.1
      _ = ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I))‖ *
            ‖riemannZeta (s₁ + u)‖ := hnorm.symm
      _ ≤ K * u ^ (-ν) * (Bζ * u ^ (q : ℝ)) :=
          mul_le_mul hCu hζu.2 (norm_nonneg _) hKpos
  have heq := eq_of_rpow_le_rpow_nhdsGT hκ (div_pos hAQ hBζ) hup hlow
  refine ⟨(q : ℤ) - (p : ℤ), ?_⟩
  push_cast
  linarith

/-- If `|ν| < 1` in `int_localPrimeMean_of_receiverBounded_damped`, then `ν = 0`. -/
theorem localPrimeMean_eq_zero_of_receiverBounded_damped {f : ℕ →*₀ ℝ}
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) {t₀ ε ν B u₀ : ℝ}
    (ht₀ : t₀ ≠ 0) (hε : 0 < ε) (hε2 : ε < 1 / 2) (hν : |ν| < 1) (hu₀ : 0 < u₀)
    (hmean : ∀ u : ℝ, 0 < u → u < u₀ →
      |(primeDirichletSeries f (((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I)).re - ν * Real.log (u⁻¹)| ≤ B)
    (hR : ReceiverBounded (dampedSignWeight f ε)) :
    ν = 0 := by
  obtain ⟨k, rfl⟩ := int_localPrimeMean_of_receiverBounded_damped hf ht₀ hε hε2 hu₀ hmean hR
  have hk : |k| < 1 := by exact_mod_cast hν
  have hk' := abs_lt.mp hk
  have hk0 : k = 0 := by omega
  simp [hk0]

/-! ### §2. Multi-singularity line-energy criterion and separated product collapse -/

/-- **An integrable local majorant off a finite set of heights pays the line energy.** -/
theorem exists_lineEnergy_le_of_majorant_finset {c : ℕ → ℝ} {P T B₁ : ℝ} {S : Finset ℝ}
    {g : ℝ → ℝ} (hT : 2 ≤ T) (hg : IntegrableOn g (Ioc 0 T))
    (hsmall : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < t → t ≤ T → t ∉ S →
      lineIntegrand c P σ t ≤ g t)
    (hlarge : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → T < t →
      ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤ B₁ * t ^ (1 / 4 : ℝ)) :
    ∃ M : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ < 3 / 4 → ∫ t : ℝ, lineIntegrand c P σ t ≤ M := by
  obtain ⟨M₂, hM₂⟩ := exists_integral_zeta_sq_rpow_le
  set Λ : ℝ := B₁ ^ 2
  refine ⟨2 * ((∫ t in Ioc 0 T, g t) + Λ * M₂), fun σ hσ hσ' => ?_⟩
  set Φ : ℝ → ℝ := lineIntegrand c P σ with hΦ
  change ∫ t : ℝ, Φ t ≤ _
  obtain ⟨hint2, hbound2⟩ := hM₂ σ hσ.le (by linarith)
  have hΦform : ∀ t, Φ t = ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 *
      ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2 / ‖(σ : ℂ) + t * I‖ ^ 2 :=
    fun t => by simp only [hΦ, lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
  have hlarge' : ∀ u : ℝ, T < u →
      Φ u ≤ Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) := by
    intro u hu
    have hu0 : 0 < u := by linarith
    have hsn : u ≤ ‖(σ : ℂ) + u * I‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + u * I)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add] at this
      rwa [abs_of_pos hu0] at this
    rw [hΦform u, div_le_iff₀ (pow_pos (lt_of_lt_of_le hu0 hsn) 2)]
    have hX := pow_le_pow_left₀ (norm_nonneg _) (hlarge σ u hσ hσ' hu) 2
    have hq2 : (u ^ (1 / 4 : ℝ)) ^ 2 = u ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
    have hpow : u ^ (-(3 / 2 : ℝ)) * u ^ 2 = u ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hu0]; norm_num
    have hs2 : u ^ 2 ≤ ‖(σ : ℂ) + u * I‖ ^ 2 := pow_le_pow_left₀ hu0.le hsn 2
    calc ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 *
          ‖weightDirichletSeries c ((σ : ℂ) + u * I) - (P : ℂ)‖ ^ 2
        ≤ ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * (Λ * u ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (hX.trans (le_of_eq ?_)) (sq_nonneg _)
          rw [mul_pow, hq2]
      _ = Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) * u ^ 2 := by
          rw [← hpow]; ring
      _ ≤ Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) *
            ‖(σ : ℂ) + u * I‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hs2 (by positivity)
  set G : ℝ → ℝ := fun u => if u ≤ T then g u
    else Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)))
  have hint2T : IntegrableOn
      (fun u : ℝ => ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) (Ioi T) :=
    hint2.mono_set (Ioi_subset_Ioi hT)
  have hsplit : Ioi (0 : ℝ) = Ioc 0 T ∪ Ioi T := (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  have hGint : IntegrableOn G (Ioi 0) := by
    rw [hsplit]
    refine IntegrableOn.union ?_ ?_
    · exact hg.congr_fun (fun u hu => by simp only [G, if_pos hu.2]) measurableSet_Ioc
    · refine IntegrableOn.congr_fun (hint2T.const_mul Λ) (fun u hu => ?_) measurableSet_Ioi
      have : ¬ u ≤ T := not_le.mpr hu
      simp only [G, if_neg this]
  have hΦ0 : ∀ u, 0 ≤ Φ u := fun u => by simp only [hΦ, lineIntegrand]; positivity
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ (S : Set ℝ) :=
    compl_mem_ae_iff.mpr (S.finite_toSet.measure_zero volume)
  have hΦle : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), Φ u ≤ G u := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (hne.mono fun u hu hpos => ?_)
    simp only [G]
    split_ifs with huT
    · exact hsmall σ u hσ hσ' hpos huT hu
    · exact hlarge' u (not_le.mp huT)
  have hhalf : ∫ u in Ioi (0 : ℝ), Φ u ≤ ∫ u in Ioi (0 : ℝ), G u :=
    integral_mono_of_nonneg (Eventually.of_forall hΦ0) hGint hΦle
  have hG1 : ∫ u in Ioc 0 T, G u = ∫ u in Ioc 0 T, g u :=
    setIntegral_congr_fun measurableSet_Ioc (fun u hu => by simp only [G, if_pos hu.2])
  have hG2 : ∫ u in Ioi T, G u =
      Λ * ∫ u in Ioi T, ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)) := by
    rw [setIntegral_congr_fun
        (g := fun u : ℝ => Λ * (‖riemannZeta ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))))
        measurableSet_Ioi (fun u hu => by
          have : ¬ u ≤ T := not_le.mpr hu
          simp only [G, if_neg this]), integral_const_mul]
  have hGval : ∫ u in Ioi (0 : ℝ), G u = (∫ u in Ioc 0 T, g u) +
      Λ * ∫ u in Ioi T, ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)) := by
    rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hGint.mono_set (by rw [hsplit]; exact subset_union_left))
      (hGint.mono_set (by rw [hsplit]; exact subset_union_right)), hG1, hG2]
  have htail : ∫ u in Ioi T, ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)) ≤ M₂ := by
    refine le_trans (setIntegral_mono_set hint2 ?_ (Ioi_subset_Ioi hT).eventuallyLE) hbound2
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [mem_Ioi.mp hu]) _)
  have heven : ∫ t : ℝ, Φ t = 2 * ∫ u in Ioi (0 : ℝ), Φ u := by
    rw [← integral_comp_abs]
    congr 1
    funext t
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, hΦ, lineIntegrand_neg]
  rw [heven]
  have := mul_le_mul_of_nonneg_left htail (sq_nonneg B₁)
  linarith

/-- Squaring a finite sum against a constant: `(1 + ∑_{k ∈ I} x_k)² ≤ C (1 + ∑_{k ∈ I} x_k²)`. -/
theorem exists_sq_one_add_sum_le {ι : Type*} (I : Finset ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ι → ℝ,
      (1 + ∑ k ∈ I, x k) ^ 2 ≤ C * (1 + ∑ k ∈ I, (x k) ^ 2) := by
  classical
  induction I using Finset.induction with
  | empty => exact ⟨1, zero_le_one, fun x => by simp⟩
  | @insert a s ha ih =>
    obtain ⟨Cs, hCs0, ih⟩ := ih
    refine ⟨2 + 2 * Cs, by positivity, fun x => ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hab : (1 + (x a + ∑ k ∈ s, x k)) ^ 2 ≤ 2 * (x a) ^ 2 + 2 * (1 + ∑ k ∈ s, x k) ^ 2 := by
      nlinarith [sq_nonneg (x a - (1 + ∑ k ∈ s, x k))]
    have hih := ih x
    have hsum0 : 0 ≤ ∑ k ∈ s, (x k) ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    nlinarith [sq_nonneg (x a)]

/-- **Multi-singularity strip bounds pay a half-damped pattern.** Let `|f| ≤ 1` be completely
multiplicative. If on `1 < Re w ≤ 2`, `0 < Im w ≤ T` (`T ≥ 2`), off the heights `{t_k : k ∈ K}`,
`|F(w)| ≤ A(1 + ∑_{k ∈ K} |Im w − t_k|^{-b_k})` with `0 ≤ b_k` and `2b_k < 1`, and
`|F(w)| ≤ B₁(Im w)^{1/4}` for `Im w > T`, then `f(d) d^{-1/2}` has bounded receiver. -/
theorem receiverBounded_pattern_half_of_sum_bounds {ι : Type*} (K : Finset ι) {f : ℕ →*₀ ℝ}
    (hf : ∀ n, |f n| ≤ 1) {t b : ι → ℝ} {T A B₁ : ℝ} (hT : 2 ≤ T) (_hA : 0 ≤ A)
    (hb1 : ∀ k ∈ K, 2 * b k < 1)
    (hsmall : ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 0 < w.im → w.im ≤ T → (∀ k ∈ K, w.im ≠ t k) →
      ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤ A * (1 + ∑ k ∈ K, |w.im - t k| ^ (-b k)))
    (hlarge : ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → T < w.im →
      ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤ B₁ * w.im ^ (1 / 4 : ℝ)) :
    ReceiverBounded (fun d => f d * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by
  classical
  set c : ℕ → ℝ := fun d => f d * (d : ℝ) ^ (-(1 / 2 : ℝ))
  have hc : DampedClass 1 (1 / 2) c := fun d => by
    simp only [c]
    rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hf d)
  set P : ℝ := ∑' d : ℕ, c d / d
  obtain ⟨Z₀, hZ₀, hZ⟩ := exists_norm_zeta_le_on_tall_box T
  obtain ⟨Csq, hCsq0, hCsq⟩ := exists_sq_one_add_sum_le K
  have hAint : 0 ≤ 4 * Z₀ ^ 2 * (2 * A ^ 2 * Csq + 2 * P ^ 2) := by positivity
  set Aint : ℝ := 4 * Z₀ ^ 2 * (2 * A ^ 2 * Csq + 2 * P ^ 2)
  have hwre : ∀ σ y : ℝ, ((σ : ℂ) + y * I + 1 / 2).re = σ + 1 / 2 := fun σ y => by simp
  have hwim : ∀ σ y : ℝ, ((σ : ℂ) + y * I + 1 / 2).im = y := fun σ y => by simp
  set g : ℝ → ℝ := fun y => Aint * (1 + ∑ k ∈ K, |y - t k| ^ (-(2 * b k)))
  have hg : IntegrableOn g (Ioc 0 T) := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp ?_
    refine (intervalIntegrable_const.add ?_).const_mul Aint
    exact (IntervalIntegrable.sum K fun k hk =>
      intervalIntegrable_abs_sub_rpow (by linarith [hb1 k hk]) (t k) 0 T).congr
      (fun x _ => Finset.sum_apply x K _)
  set S : Finset ℝ := K.image t
  have hsmall' : ∀ σ y : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < y → y ≤ T → y ∉ S →
      lineIntegrand c P σ y ≤ g y := by
    intro σ y hσ hσ' hy hyT hyS
    have hyk : ∀ k ∈ K, y ≠ t k := fun k hk h => hyS (h ▸ Finset.mem_image_of_mem t hk)
    have hF := hsmall ((σ : ℂ) + y * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim]; exact hy) (by rw [hwim]; exact hyT) (by rw [hwim]; exact hyk)
    rw [hwim] at hF
    have hC : ‖weightDirichletSeries c ((σ : ℂ) + y * I) - (P : ℂ)‖ ≤
        A * (1 + ∑ k ∈ K, |y - t k| ^ (-b k)) + |P| := by
      rw [weightDirichletSeries_pattern]
      refine (norm_sub_le _ _).trans (add_le_add hF (by rw [Complex.norm_real, Real.norm_eq_abs]))
    have hsq_sum : (1 + ∑ k ∈ K, |y - t k| ^ (-b k)) ^ 2 ≤
        Csq * (1 + ∑ k ∈ K, |y - t k| ^ (-(2 * b k))) := by
      refine (hCsq fun k => |y - t k| ^ (-b k)).trans (le_of_eq ?_)
      congr 2
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 1; push_cast; ring
    have hsum_nonneg : 0 ≤ ∑ k ∈ K, |y - t k| ^ (-(2 * b k)) :=
      Finset.sum_nonneg fun k _ => Real.rpow_nonneg (abs_nonneg _) _
    have hsq : ‖weightDirichletSeries c ((σ : ℂ) + y * I) - (P : ℂ)‖ ^ 2 ≤
        (2 * A ^ 2 * Csq + 2 * P ^ 2) * (1 + ∑ k ∈ K, |y - t k| ^ (-(2 * b k))) := by
      have h := pow_le_pow_left₀ (norm_nonneg _) hC 2
      have hab : ∀ u v : ℝ, (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := fun u v => by
        nlinarith [sq_nonneg (u - v)]
      refine h.trans ((hab _ _).trans ?_)
      rw [mul_pow, sq_abs]
      nlinarith [sq_nonneg A, sq_nonneg P, mul_le_mul_of_nonneg_left hsq_sum (sq_nonneg A)]
    have hζs := hZ σ y hσ.le hσ'.le (by rw [abs_of_pos hy]; exact hyT)
    have hsn : σ ≤ ‖(σ : ℂ) + y * I‖ := by
      have := Complex.abs_re_le_norm ((σ : ℂ) + y * I)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
      linarith [le_abs_self σ]
    have hs2 : (1 / 2 : ℝ) ^ 2 ≤ ‖(σ : ℂ) + y * I‖ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hden : 0 < ‖(σ : ℂ) + y * I‖ ^ 2 := lt_of_lt_of_le (by norm_num) hs2
    have hzsq : ‖riemannZeta ((σ : ℂ) + y * I)‖ ^ 2 ≤ Z₀ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hζs 2
    simp only [lineIntegrand, norm_div, norm_mul, div_pow, mul_pow, g]
    rw [div_le_iff₀ hden]
    calc ‖riemannZeta ((σ : ℂ) + y * I)‖ ^ 2 *
          ‖weightDirichletSeries c ((σ : ℂ) + y * I) - (P : ℂ)‖ ^ 2
        ≤ Z₀ ^ 2 * ((2 * A ^ 2 * Csq + 2 * P ^ 2) * (1 + ∑ k ∈ K, |y - t k| ^ (-(2 * b k)))) :=
          mul_le_mul hzsq hsq (sq_nonneg _) (sq_nonneg _)
      _ = Aint * (1 + ∑ k ∈ K, |y - t k| ^ (-(2 * b k))) * (1 / 2) ^ 2 := by
          simp only [Aint]; ring
      _ ≤ Aint * (1 + ∑ k ∈ K, |y - t k| ^ (-(2 * b k))) * ‖(σ : ℂ) + y * I‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hs2 (mul_nonneg hAint (by linarith))
  have hlarge' : ∀ σ y : ℝ, 1 / 2 < σ → σ < 3 / 4 → T < y →
      ‖weightDirichletSeries c ((σ : ℂ) + y * I) - (P : ℂ)‖ ≤ (|B₁| + |P|) * y ^ (1 / 4 : ℝ) := by
    intro σ y hσ hσ' hy
    have hF := hlarge ((σ : ℂ) + y * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim]; exact hy)
    rw [hwim] at hF
    rw [weightDirichletSeries_pattern]
    refine (norm_sub_le _ _).trans ?_
    have h1 : 1 ≤ y ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [le_abs_self B₁, abs_nonneg P, abs_nonneg B₁,
      mul_le_mul_of_nonneg_right (le_abs_self B₁) (by positivity : (0 : ℝ) ≤ y ^ (1 / 4 : ℝ))]
  obtain ⟨M, hM⟩ := exists_lineEnergy_le_of_majorant_finset (c := c) (S := S) hT hg hsmall' hlarge'
  exact ⟨3 * M / (4 * Real.pi), weightPronicEnergy_le_of_lineEnergy_le hc hM⟩

/-- **Separated singular factors collapse to a sum.** For `t₁ ≠ t₂`, `b₁, b₂ ≥ 0`, and
`y ≠ t₁, t₂`, at least one of `|y − t₁|, |y − t₂|` is `≥ |t₁ − t₂|/2`, so the product
`|y − t₁|^{-b₁} |y − t₂|^{-b₂}` is bounded by a linear combination of the two factors. -/
theorem rpow_neg_mul_rpow_neg_le_add_of_ne {t₁ t₂ b₁ b₂ y : ℝ} (hne : t₁ ≠ t₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hy₁ : y ≠ t₁) (hy₂ : y ≠ t₂) :
    |y - t₁| ^ (-b₁) * |y - t₂| ^ (-b₂) ≤
      (|t₁ - t₂| / 2) ^ (-b₂) * |y - t₁| ^ (-b₁) +
        (|t₁ - t₂| / 2) ^ (-b₁) * |y - t₂| ^ (-b₂) := by
  set δ : ℝ := |t₁ - t₂| / 2
  have hδ : 0 < δ := half_pos (abs_pos.mpr (sub_ne_zero.mpr hne))
  have hx₁ : 0 < |y - t₁| := abs_pos.mpr (sub_ne_zero.mpr hy₁)
  have hx₂ : 0 < |y - t₂| := abs_pos.mpr (sub_ne_zero.mpr hy₂)
  have htri : 2 * δ ≤ |y - t₁| + |y - t₂| := by
    calc 2 * δ = |t₁ - t₂| := by simp only [δ]; ring
      _ = |(t₁ - y) + (y - t₂)| := by ring_nf
      _ ≤ |t₁ - y| + |y - t₂| := abs_add_le _ _
      _ = |y - t₁| + |y - t₂| := by rw [abs_sub_comm]
  have hnonneg₁ : 0 ≤ δ ^ (-b₂) * |y - t₁| ^ (-b₁) := by positivity
  have hnonneg₂ : 0 ≤ δ ^ (-b₁) * |y - t₂| ^ (-b₂) := by positivity
  rcases le_total δ |y - t₂| with h2 | h2
  · have hp2 : |y - t₂| ^ (-b₂) ≤ δ ^ (-b₂) :=
      Real.rpow_le_rpow_of_nonpos hδ h2 (by linarith)
    have hm := mul_le_mul_of_nonneg_left hp2 (Real.rpow_nonneg hx₁.le (-b₁))
    linarith
  · have h1 : δ ≤ |y - t₁| := by linarith
    have hp1 : |y - t₁| ^ (-b₁) ≤ δ ^ (-b₁) :=
      Real.rpow_le_rpow_of_nonpos hδ h1 (by linarith)
    have hm := mul_le_mul_of_nonneg_right hp1 (Real.rpow_nonneg hx₂.le (-b₂))
    linarith

/-- **Finite product of separated singular factors collapses to a sum.** For pairwise distinct
heights `t_k` (`k ∈ I`) and nonnegative exponents `b_k ≥ 0`, there is `C ≥ 0` such that
`∏_{k ∈ I} (|y − t_k|^{-b_k} + 1) ≤ C(1 + ∑_{k ∈ I} |y − t_k|^{-b_k})` off `{t_k : k ∈ I}`. -/
theorem exists_prod_rpow_neg_add_one_le_sum {ι : Type*} (I : Finset ι)
    (t b : ι → ℝ) (hinj : Set.InjOn t (I : Set ι)) (hb : ∀ k ∈ I, 0 ≤ b k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, (∀ k ∈ I, y ≠ t k) →
      ∏ k ∈ I, (|y - t k| ^ (-b k) + 1) ≤ C * (1 + ∑ k ∈ I, |y - t k| ^ (-b k)) := by
  classical
  induction I using Finset.induction with
  | empty => exact ⟨1, zero_le_one, fun y _ => by simp⟩
  | @insert a s ha ih =>
    have hinj_s : Set.InjOn t (s : Set ι) :=
      hinj.mono fun x hx => Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx))
    have hb_s : ∀ k ∈ s, 0 ≤ b k := fun k hk => hb k (Finset.mem_insert_of_mem hk)
    have hba : 0 ≤ b a := hb a (Finset.mem_insert_self a s)
    obtain ⟨Cs, hCs0, ih⟩ := ih hinj_s hb_s
    set Dk : ι → ℝ := fun k => (|t a - t k| / 2) ^ (-b k) + (|t a - t k| / 2) ^ (-b a)
    have hDk0 : ∀ k, 0 ≤ Dk k := fun k => by simp only [Dk]; positivity
    set D : ℝ := 1 + ∑ k ∈ s, Dk k
    have hD0 : 0 ≤ D := add_nonneg zero_le_one (Finset.sum_nonneg fun k _ => hDk0 k)
    refine ⟨Cs * D, mul_nonneg hCs0 hD0, fun y hy => ?_⟩
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hya : y ≠ t a := hy a (Finset.mem_insert_self a s)
    have hys : ∀ k ∈ s, y ≠ t k := fun k hk => hy k (Finset.mem_insert_of_mem hk)
    have hih := ih y hys
    set xa : ℝ := |y - t a| ^ (-b a)
    set xs : ι → ℝ := fun k => |y - t k| ^ (-b k)
    have hxa0 : 0 ≤ xa := Real.rpow_nonneg (abs_nonneg _) _
    have hxs0 : ∀ k, 0 ≤ xs k := fun k => Real.rpow_nonneg (abs_nonneg _) _
    set Stot : ℝ := 1 + (xa + ∑ k ∈ s, xs k)
    have hxa_le : xa ≤ Stot := by
      have : 0 ≤ ∑ k ∈ s, xs k := Finset.sum_nonneg fun k _ => hxs0 k
      simp only [Stot]; linarith
    have hxs_le : ∀ k ∈ s, xs k ≤ Stot := fun k hk => by
      have hle : xs k ≤ ∑ j ∈ s, xs j := Finset.single_le_sum (fun j _ => hxs0 j) hk
      simp only [Stot]; linarith
    have hterm : ∀ k ∈ s, xa * xs k ≤ Dk k * Stot := fun k hk => by
      have hne : t a ≠ t k := fun h =>
        ha (hinj (Finset.mem_coe.mpr (Finset.mem_insert_self a s))
          (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hk)) h ▸ hk)
      have hcoll := rpow_neg_mul_rpow_neg_le_add_of_ne hne hba (hb_s k hk) hya (hys k hk)
      have h1 : (|t a - t k| / 2) ^ (-b k) * xa ≤ (|t a - t k| / 2) ^ (-b k) * Stot :=
        mul_le_mul_of_nonneg_left hxa_le (by positivity)
      have h2 : (|t a - t k| / 2) ^ (-b a) * xs k ≤ (|t a - t k| / 2) ^ (-b a) * Stot :=
        mul_le_mul_of_nonneg_left (hxs_le k hk) (by positivity)
      simp only [Dk, add_mul]
      exact hcoll.trans (add_le_add h1 h2)
    have hsum_le : ∑ k ∈ s, xa * xs k ≤ (∑ k ∈ s, Dk k) * Stot := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hterm
    calc (xa + 1) * ∏ k ∈ s, (xs k + 1)
        ≤ (xa + 1) * (Cs * (1 + ∑ k ∈ s, xs k)) :=
          mul_le_mul_of_nonneg_left hih (by linarith)
      _ = Cs * (Stot + ∑ k ∈ s, xa * xs k) := by
          simp only [Stot, ← Finset.mul_sum]; ring
      _ ≤ Cs * (Stot + (∑ k ∈ s, Dk k) * Stot) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum_le) hCs0
      _ = Cs * D * Stot := by simp only [D]; ring

/-- **Prime-additive decomposition of `primeDirichletSeries`.** If `f(p) = ∑_{k ∈ K} g_k(p)` at all
primes `p`, then `ℓ_f(w) = ∑_{k ∈ K} ℓ_{g_k}(w)` on `Re w > 1`. -/
theorem primeDirichletSeries_eq_sum {ι : Type*} (K : Finset ι) {f : ℕ →*₀ ℝ}
    {g : ι → ℕ →*₀ ℝ} (hg : ∀ k ∈ K, ∀ p : ℕ, p.Prime → |g k p| ≤ 1)
    (hsum : ∀ p : ℕ, p.Prime → f p = ∑ k ∈ K, g k p) {w : ℂ} (hw : 1 < w.re) :
    primeDirichletSeries f w = ∑ k ∈ K, primeDirichletSeries (g k) w := by
  simp only [primeDirichletSeries]
  rw [← Summable.tsum_finsetSum (fun k hk => summable_primeDirichletSeries (hg k hk) hw)]
  refine tsum_congr fun p => ?_
  simp only [hsum p.1 p.2, Complex.ofReal_sum, Finset.sum_mul]

/-- **Prime-additive Euler product upper factorization.** If `f(p) = ∑_{k ∈ K} g_k(p)` at all
primes `p`, with `|f(p)| ≤ 1` and `|g_k(p)| ≤ 1`, then on `Re w > 1`,
`‖F_f(w)‖ ≤ e^S ∏_{k ∈ K} (e^S ‖F_{g_k}(w)‖)`. -/
theorem norm_patternSeries_le_prod_of_prime_sum {ι : Type*} (K : Finset ι) {f : ℕ →*₀ ℝ}
    {g : ι → ℕ →*₀ ℝ} (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1)
    (hg : ∀ k ∈ K, ∀ p : ℕ, p.Prime → |g k p| ≤ 1)
    (hsum : ∀ p : ℕ, p.Prime → f p = ∑ k ∈ K, g k p) {w : ℂ} (hw : 1 < w.re) :
    ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
      Real.exp primeSquareMass *
        ∏ k ∈ K, (Real.exp primeSquareMass * ‖∑' n : ℕ, (g k n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖) := by
  have hF := (norm_patternSeries_bounds_of_primeDirichletSeries hf hw).2
  have hre : (primeDirichletSeries f w).re = ∑ k ∈ K, (primeDirichletSeries (g k) w).re := by
    rw [primeDirichletSeries_eq_sum K hg hsum hw, Complex.re_sum]
  calc ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
      ≤ Real.exp (primeSquareMass + (primeDirichletSeries f w).re) := hF
    _ = Real.exp primeSquareMass * ∏ k ∈ K, Real.exp ((primeDirichletSeries (g k) w).re) := by
        rw [Real.exp_add, hre, Real.exp_sum]
    _ ≤ Real.exp primeSquareMass *
          ∏ k ∈ K, (Real.exp primeSquareMass *
            ‖∑' n : ℕ, (g k n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖) := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun k _ => (Real.exp_pos _).le)
          fun k hk => ?_) (Real.exp_pos _).le
        have hgk := (norm_patternSeries_bounds_of_primeDirichletSeries (hg k hk) hw).1
        calc Real.exp ((primeDirichletSeries (g k) w).re)
            = Real.exp primeSquareMass *
                Real.exp (-primeSquareMass + (primeDirichletSeries (g k) w).re) := by
              rw [← Real.exp_add]; ring_nf
          _ ≤ Real.exp primeSquareMass * ‖∑' n : ℕ, (g k n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ :=
              mul_le_mul_of_nonneg_left hgk (Real.exp_pos _).le

/-! ### §3. Complete phase diagram of multi-frequency prime patterns -/

/-- The multi-frequency oscillating prime pattern
`f(p) = ∑_{k ∈ K} a_k cos(t_k log p + φ_k)`. -/
def multiPhasePattern {ι : Type*} (K : Finset ι) (a t φ : ι → ℝ) : ℕ →*₀ ℝ :=
  primeValueHom fun p => ∑ k ∈ K, a k * Real.cos (t k * Real.log p + φ k)

theorem multiPhasePattern_prime {ι : Type*} (K : Finset ι) (a t φ : ι → ℝ) {p : ℕ}
    (hp : p.Prime) :
    multiPhasePattern K a t φ p = ∑ k ∈ K, a k * Real.cos (t k * Real.log p + φ k) :=
  primeValueHom_prime _ hp

theorem multiPhasePattern_prime_eq_sum_phasePattern {ι : Type*} (K : Finset ι) (a t φ : ι → ℝ)
    {p : ℕ} (hp : p.Prime) :
    multiPhasePattern K a t φ p = ∑ k ∈ K, phasePattern (a k) (t k) (φ k) p := by
  rw [multiPhasePattern_prime K a t φ hp]
  exact Finset.sum_congr rfl fun k _ => (phasePattern_prime (a k) (t k) (φ k) hp).symm

/-- If `∑_{k ∈ K} |a_k| ≤ 1`, then `|multiPhasePattern K a t φ n| ≤ 1` for all `n`. -/
theorem abs_multiPhasePattern_le_of_sum_abs_le_one {ι : Type*} {K : Finset ι} {a : ι → ℝ}
    (ha : ∑ k ∈ K, |a k| ≤ 1) (t φ : ι → ℝ) (n : ℕ) :
    |multiPhasePattern K a t φ n| ≤ 1 :=
  abs_patternHom_le_one _ (fun p hp => by
    rw [multiPhasePattern_prime K a t φ hp]
    calc |∑ k ∈ K, a k * Real.cos (t k * Real.log p + φ k)|
        ≤ ∑ k ∈ K, |a k * Real.cos (t k * Real.log p + φ k)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ K, |a k| := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      _ ≤ 1 := ha) n

/-- The half-damped multi-frequency prime weight `f(d) d^{-1/2}`. -/
def multiPhaseWeight {ι : Type*} (K : Finset ι) (a t φ : ι → ℝ) (d : ℕ) : ℝ :=
  multiPhasePattern K a t φ d * (d : ℝ) ^ (-(1 / 2 : ℝ))

/-- Opposite amplitude negates `phasePattern` at every prime. -/
theorem phasePattern_neg_amp_prime (a t₀ φ : ℝ) {p : ℕ} (hp : p.Prime) :
    phasePattern (-a) t₀ φ p = -phasePattern a t₀ φ p := by
  rw [phasePattern_prime (-a) t₀ φ hp, phasePattern_prime a t₀ φ hp, neg_mul]

/-- Opposite amplitude negates `primeDirichletSeries` of `phasePattern`. -/
theorem primeDirichletSeries_phasePattern_neg_amp (a t₀ φ : ℝ) (w : ℂ) :
    primeDirichletSeries (phasePattern (-a) t₀ φ) w =
      -primeDirichletSeries (phasePattern a t₀ φ) w := by
  simp only [primeDirichletSeries, ← tsum_neg]
  refine tsum_congr fun p => ?_
  simp only [phasePattern_neg_amp_prime a t₀ φ p.2, Complex.ofReal_neg, neg_mul]

/-- **Single-mode small-height bound on an arbitrary interval `(0, T]`** (`T ≥ 2`, `t₀ > 0`). -/
theorem exists_norm_phaseSeries_le_on_Ioc {a t₀ : ℝ} (ha : |a| ≤ 1) (ht₀ : 0 < t₀) (φ : ℝ)
    {T : ℝ} (hT : 2 ≤ T) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 0 < w.im → w.im ≤ T → w.im ≠ t₀ →
      ‖∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        A * (|w.im - t₀| ^ (-(max (a * Real.cos φ) 0 / 2)) + 1) := by
  obtain ⟨A₀, hA₀, hsmall⟩ := exists_norm_phaseSeries_le_small ha ht₀ φ
  obtain ⟨B₁, hlarge⟩ := exists_norm_phaseSeries_le_large ha ht₀ φ
  have hT0 : 0 ≤ T ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
  refine ⟨A₀ + |B₁| * T ^ (1 / 4 : ℝ), by positivity, fun w hw hw2 hy hyT hne => ?_⟩
  set b : ℝ := max (a * Real.cos φ) 0 / 2
  have hb0 : 0 ≤ |w.im - t₀| ^ (-b) := Real.rpow_nonneg (abs_nonneg _) _
  rcases le_or_gt w.im (2 * t₀ + 18) with hle | hgt
  · refine (hsmall w hw hw2 hy hle hne).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith [ mul_nonneg (abs_nonneg B₁) hT0 ]) (by linarith)
  · have hL := hlarge w hw hw2 hgt
    have hy_rpow : w.im ^ (1 / 4 : ℝ) ≤ T ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hy.le hyT (by norm_num)
    calc ‖∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
        ≤ B₁ * w.im ^ (1 / 4 : ℝ) := hL
      _ ≤ |B₁| * w.im ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self B₁) (Real.rpow_nonneg hy.le _)
      _ ≤ |B₁| * T ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left hy_rpow (abs_nonneg B₁)
      _ ≤ (A₀ + |B₁| * T ^ (1 / 4 : ℝ)) * (|w.im - t₀| ^ (-b) + 1) := by
          nlinarith [mul_nonneg (abs_nonneg B₁) hT0]

/-- **Single-mode polylogarithmic bound at large heights**: for `Im w > 2t₀ + 18`,
`‖F(w)‖ ≤ C (log Im w)^9`. -/
theorem exists_norm_phaseSeries_le_log_pow_nine {a t₀ : ℝ} (ha : |a| ≤ 1) (ht₀ : 0 < t₀)
    (φ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 2 * t₀ + 18 < w.im →
      ‖∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        C * Real.log w.im ^ 9 := by
  obtain ⟨CL, hCL⟩ := RHTower.exists_norm_zetaEulerLog_le_large
  refine ⟨Real.exp (2 * primeSquareMass + CL) * 2 ^ 9, by positivity, fun w hw hw2 ht => ?_⟩
  set y := w.im
  have hy : 18 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hvm : w - t₀ * I = (w.re : ℂ) + ((y - t₀ : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [y]
  have hvp : w + t₀ * I = (w.re : ℂ) + ((y + t₀ : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [y]
  have hm := hCL w.re (y - t₀) hw hw2 (by rw [abs_of_pos (by linarith)]; linarith)
  have hp := hCL w.re (y + t₀) hw hw2 (by rw [abs_of_pos (by linarith)]; linarith)
  rw [← hvm, abs_of_pos (by linarith)] at hm
  rw [← hvp, abs_of_pos (by linarith)] at hp
  have h2log : Real.log (y + t₀) ≤ 2 * Real.log y := by
    rw [← Real.log_rpow (by linarith), Real.rpow_two]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hLm : Real.log (Real.log (y - t₀)) ≤ Real.log (2 * Real.log y) :=
    Real.log_le_log (Real.log_pos (by linarith))
      ((Real.log_le_log (by linarith) (by linarith)).trans h2log)
  have hLp : Real.log (Real.log (y + t₀)) ≤ Real.log (2 * Real.log y) :=
    Real.log_le_log (Real.log_pos (by linarith)) h2log
  have hexp9 : Real.exp (9 * Real.log (2 * Real.log y)) = (2 * Real.log y) ^ 9 := by
    rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log (by positivity)]
  calc ‖∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
      ≤ Real.exp (2 * primeSquareMass + (‖RHTower.zetaEulerLog (w - t₀ * I)‖ +
          ‖RHTower.zetaEulerLog (w + t₀ * I)‖) / 2) := norm_phaseSeries_le_exp ha t₀ φ hw
    _ ≤ Real.exp (2 * primeSquareMass + CL + 9 * Real.log (2 * Real.log y)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (2 * primeSquareMass + CL) * 2 ^ 9 * Real.log y ^ 9 := by
        rw [Real.exp_add, hexp9]; ring

/-- Selecting constants across a finite index set: if `∀ k ∈ K, ∃ A ≥ 0, P k A`, there is a
function `A : ι → ℝ` with `∀ k ∈ K, 0 ≤ A k ∧ P k (A k)`. -/
theorem exists_fun_of_forall_mem {ι : Type*} (K : Finset ι) {P : ι → ℝ → Prop}
    (h : ∀ k ∈ K, ∃ A : ℝ, 0 ≤ A ∧ P k A) :
    ∃ A : ι → ℝ, ∀ k ∈ K, 0 ≤ A k ∧ P k (A k) := by
  classical
  refine ⟨fun k => if hk : k ∈ K then Classical.choose (h k hk) else 0, fun k hk => ?_⟩
  dsimp only
  rw [dif_pos hk]
  exact Classical.choose_spec (h k hk)

/-- **Multi-frequency small-height bound.** For pairwise distinct positive frequencies `t_k > 0`
(`k ∈ K`), `|a_k| ≤ 1`, and `|f(p)| ≤ 1`, on `1 < Re w ≤ 2`, `0 < Im w ≤ T` (`T ≥ 2`), off
`{t_k : k ∈ K}`, `‖F(w)‖ ≤ A(1 + ∑_{k ∈ K} |Im w − t_k|^{-(a_k cos φ_k)⁺/2})`. -/
theorem exists_norm_multiPhaseSeries_le_small {ι : Type*} (K : Finset ι) {a t φ : ι → ℝ}
    (hf : ∀ p : ℕ, p.Prime → |multiPhasePattern K a t φ p| ≤ 1)
    (ha : ∀ k ∈ K, |a k| ≤ 1) (ht : ∀ k ∈ K, 0 < t k) (hinj : Set.InjOn t (K : Set ι))
    {T : ℝ} (hT : 2 ≤ T) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 0 < w.im → w.im ≤ T →
      (∀ k ∈ K, w.im ≠ t k) →
        ‖∑' n : ℕ, (multiPhasePattern K a t φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
          A * (1 + ∑ k ∈ K, |w.im - t k| ^ (-(max (a k * Real.cos (φ k)) 0 / 2))) := by
  set b : ι → ℝ := fun k => max (a k * Real.cos (φ k)) 0 / 2
  have hb0 : ∀ k ∈ K, 0 ≤ b k := fun k _ => by simp only [b]; positivity
  obtain ⟨Ak, hAk⟩ := exists_fun_of_forall_mem K fun k hk =>
    exists_norm_phaseSeries_le_on_Ioc (ha k hk) (ht k hk) (φ k) hT
  obtain ⟨Cprod, hCprod0, hprod⟩ := exists_prod_rpow_neg_add_one_le_sum K t b hinj hb0
  set C₀ : ℝ := Real.exp primeSquareMass * ∏ k ∈ K, (Real.exp primeSquareMass * Ak k)
  have hC₀0 : 0 ≤ C₀ := mul_nonneg (Real.exp_pos _).le
    (Finset.prod_nonneg fun k hk => mul_nonneg (Real.exp_pos _).le (hAk k hk).1)
  refine ⟨C₀ * Cprod, mul_nonneg hC₀0 hCprod0, fun w hw hw2 hy hyT hne => ?_⟩
  have hfact := norm_patternSeries_le_prod_of_prime_sum K hf
    (fun k hk p _ => abs_phasePattern_le (ha k hk) (t k) (φ k) p)
    (fun p hp => multiPhasePattern_prime_eq_sum_phasePattern K a t φ hp) hw
  calc ‖∑' n : ℕ, (multiPhasePattern K a t φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
      ≤ Real.exp primeSquareMass * ∏ k ∈ K,
          (Real.exp primeSquareMass *
            ‖∑' n : ℕ, (phasePattern (a k) (t k) (φ k) n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖) := hfact
    _ ≤ Real.exp primeSquareMass * ∏ k ∈ K,
          (Real.exp primeSquareMass * (Ak k * (|w.im - t k| ^ (-b k) + 1))) := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun k _ => by positivity)
          fun k hk => mul_le_mul_of_nonneg_left
            ((hAk k hk).2 w hw hw2 hy hyT (hne k hk)) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = C₀ * ∏ k ∈ K, (|w.im - t k| ^ (-b k) + 1) := by
        simp only [C₀, ← mul_assoc]
        rw [Finset.prod_mul_distrib, ← mul_assoc]
    _ ≤ C₀ * (Cprod * (1 + ∑ k ∈ K, |w.im - t k| ^ (-b k))) :=
        mul_le_mul_of_nonneg_left (hprod w.im hne) hC₀0
    _ = C₀ * Cprod * (1 + ∑ k ∈ K, |w.im - t k| ^ (-b k)) := by ring

/-- **Multi-frequency large-height bound.** For `Im w > 2 + ∑_{k ∈ K} (2t_k + 18)`,
`‖F(w)‖ ≤ B₁ (Im w)^{1/4}`. -/
theorem exists_norm_multiPhaseSeries_le_large {ι : Type*} (K : Finset ι) {a t φ : ι → ℝ}
    (hf : ∀ p : ℕ, p.Prime → |multiPhasePattern K a t φ p| ≤ 1)
    (ha : ∀ k ∈ K, |a k| ≤ 1) (ht : ∀ k ∈ K, 0 < t k) :
    ∃ B₁ : ℝ, ∀ w : ℂ, 1 < w.re → w.re ≤ 2 →
      2 + ∑ k ∈ K, (2 * t k + 18) < w.im →
        ‖∑' n : ℕ, (multiPhasePattern K a t φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
          B₁ * w.im ^ (1 / 4 : ℝ) := by
  obtain ⟨Ck, hCk⟩ := exists_fun_of_forall_mem K fun k hk =>
    exists_norm_phaseSeries_le_log_pow_nine (ha k hk) (ht k hk) (φ k)
  set C₀ : ℝ := Real.exp primeSquareMass * ∏ k ∈ K, (Real.exp primeSquareMass * Ck k)
  have hC₀0 : 0 ≤ C₀ := mul_nonneg (Real.exp_pos _).le
    (Finset.prod_nonneg fun k hk => mul_nonneg (Real.exp_pos _).le (hCk k hk).1)
  set N : ℕ := K.card * 9
  refine ⟨C₀ * (4 * ((N : ℝ) + 1)) ^ N, fun w hw hw2 hy => ?_⟩
  have hsum_pos : ∀ k ∈ K, 0 ≤ 2 * t k + 18 := fun k hk => by linarith [ht k hk]
  have hy1 : 1 ≤ w.im := by
    have : 0 ≤ ∑ k ∈ K, (2 * t k + 18) := Finset.sum_nonneg hsum_pos
    linarith
  have hlogy0 : 0 ≤ Real.log w.im := Real.log_nonneg hy1
  have hyk : ∀ k ∈ K, 2 * t k + 18 < w.im := fun k hk => by
    have hle := Finset.single_le_sum hsum_pos hk
    linarith
  have hfact := norm_patternSeries_le_prod_of_prime_sum K hf
    (fun k hk p _ => abs_phasePattern_le (ha k hk) (t k) (φ k) p)
    (fun p hp => multiPhasePattern_prime_eq_sum_phasePattern K a t φ hp) hw
  have hprod_pow : ∏ _k ∈ K, Real.log w.im ^ 9 = Real.log w.im ^ N := by
    rw [Finset.prod_const, ← pow_mul, mul_comm]
  calc ‖∑' n : ℕ, (multiPhasePattern K a t φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
      ≤ Real.exp primeSquareMass * ∏ k ∈ K,
          (Real.exp primeSquareMass *
            ‖∑' n : ℕ, (phasePattern (a k) (t k) (φ k) n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖) := hfact
    _ ≤ Real.exp primeSquareMass * ∏ k ∈ K,
          (Real.exp primeSquareMass * (Ck k * Real.log w.im ^ 9)) := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun k _ => by positivity)
          fun k hk => mul_le_mul_of_nonneg_left
            ((hCk k hk).2 w hw hw2 (hyk k hk)) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = C₀ * ∏ _k ∈ K, Real.log w.im ^ 9 := by
        simp only [C₀, ← mul_assoc]
        rw [Finset.prod_mul_distrib, ← mul_assoc]
    _ = C₀ * Real.log w.im ^ N := by rw [hprod_pow]
    _ ≤ C₀ * ((4 * ((N : ℝ) + 1)) ^ N * w.im ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (log_pow_le_rpow_quarter hy1 N) hC₀0
    _ = C₀ * (4 * ((N : ℝ) + 1)) ^ N * w.im ^ (1 / 4 : ℝ) := by ring

/-- **Multi-frequency payment below full real amplitude.** For pairwise distinct positive
frequencies `t_k > 0` (`k ∈ I`) with `|a_k| ≤ 1`, `|f(p)| ≤ 1`, and `a_k cos φ_k < 1` for every
`k ∈ I`, the half-damped weight `multiPhaseWeight I a t φ` has bounded receiver. -/
theorem receiverBounded_multiPhaseWeight_of_forall_lt_one {ι : Type*} (I : Finset ι)
    {a t φ : ι → ℝ} (hf : ∀ p : ℕ, p.Prime → |multiPhasePattern I a t φ p| ≤ 1)
    (ha : ∀ k ∈ I, |a k| ≤ 1) (ht : ∀ k ∈ I, 0 < t k) (hinj : Set.InjOn t (I : Set ι))
    (hα : ∀ k ∈ I, a k * Real.cos (φ k) < 1) :
    ReceiverBounded (multiPhaseWeight I a t φ) := by
  set T : ℝ := 2 + ∑ k ∈ I, (2 * t k + 18)
  have hT : 2 ≤ T := by
    have : 0 ≤ ∑ k ∈ I, (2 * t k + 18) := Finset.sum_nonneg fun k hk => by linarith [ht k hk]
    simp only [T]; linarith
  obtain ⟨A, hA0, hsmall⟩ := exists_norm_multiPhaseSeries_le_small I hf ha ht hinj hT
  obtain ⟨B₁, hlarge⟩ := exists_norm_multiPhaseSeries_le_large I hf ha ht
  have hb1 : ∀ k ∈ I, 2 * (max (a k * Real.cos (φ k)) 0 / 2) < 1 := fun k hk => by
    have := max_lt (hα k hk) (show (0 : ℝ) < 1 by norm_num)
    linarith
  exact receiverBounded_pattern_half_of_sum_bounds I (abs_patternHom_le_one _ hf) hT hA0 hb1
    hsmall hlarge

/-- Near a distinct height `t₁ ≠ t₀`, the prime Dirichlet series of `phasePattern a t₀ φ` is
bounded below on `(1 + u) + i(t₁ + τ)`. -/
theorem exists_primeDirichletSeries_phasePattern_re_ge_of_ne {a t₀ φ t₁ : ℝ}
    (ha : |a| ≤ 1) (ht₀ : 0 < t₀) (ht₁ : 0 < t₁) (hne : t₀ ≠ t₁) :
    ∃ r B : ℝ, 0 < r ∧ ∀ u τ : ℝ, 0 < u → u ≤ r → 0 ≤ τ → τ ≤ r →
      -B ≤ (primeDirichletSeries (phasePattern a t₀ φ)
        (((1 + u : ℝ) : ℂ) + ((t₁ + τ : ℝ) : ℂ) * I)).re := by
  set δ : ℝ := |t₁ - t₀| / 2
  have hδ : 0 < δ := half_pos (abs_pos.mpr (sub_ne_zero.mpr hne.symm))
  set r : ℝ := min δ 1
  have hr : 0 < r := lt_min hδ zero_lt_one
  set T : ℝ := t₁ + r + 2
  have hT : 2 ≤ T := by simp only [T]; linarith
  have hna : |-a| ≤ 1 := by rwa [abs_neg]
  obtain ⟨A, hA0, hsmall⟩ := exists_norm_phaseSeries_le_on_Ioc hna ht₀ φ hT
  set b : ℝ := max (-a * Real.cos φ) 0 / 2
  set M : ℝ := A * (δ ^ (-b) + 1) + 1
  have hM0 : 0 < M := by positivity
  refine ⟨r, Real.log M + primeSquareMass, hr, fun u τ hu hur hτ hτr => ?_⟩
  set w : ℂ := ((1 + u : ℝ) : ℂ) + ((t₁ + τ : ℝ) : ℂ) * I
  have hwre : w.re = 1 + u := by simp [w]
  have hwim : w.im = t₁ + τ := by simp [w]
  have hw1 : 1 < w.re := by rw [hwre]; linarith
  have hw2 : w.re ≤ 2 := by rw [hwre]; linarith [min_le_right δ 1]
  have hwy0 : 0 < w.im := by rw [hwim]; linarith
  have hwyT : w.im ≤ T := by rw [hwim]; simp only [T]; linarith
  have hdist : δ ≤ |w.im - t₀| := by
    rw [hwim]
    have htri : 2 * δ ≤ |t₁ + τ - t₀| + |τ| := by
      calc 2 * δ = |t₁ - t₀| := by simp only [δ]; ring
        _ = |(t₁ + τ - t₀) - τ| := by ring_nf
        _ ≤ |t₁ + τ - t₀| + |-τ| := abs_add_le _ _
        _ = |t₁ + τ - t₀| + |τ| := by rw [abs_neg]
    rw [abs_of_nonneg hτ] at htri
    have hτδ : τ ≤ δ := hτr.trans (min_le_left δ 1)
    linarith
  have hwne : w.im ≠ t₀ := fun h => by rw [h, sub_self, abs_zero] at hdist; linarith
  have hF := hsmall w hw1 hw2 hwy0 hwyT hwne
  have hpow : |w.im - t₀| ^ (-b) ≤ δ ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos hδ hdist (neg_nonpos.mpr (by simp only [b]; positivity))
  have hFM : ‖∑' n : ℕ, (phasePattern (-a) t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤ M := by
    have := hF.trans (mul_le_mul_of_nonneg_left (add_le_add hpow le_rfl) hA0)
    simp only [M]; linarith
  have hP := (norm_patternSeries_bounds_of_primeDirichletSeries
    (fun p _ => abs_phasePattern_le hna t₀ φ p) hw1).1
  have hlog : Real.exp (-primeSquareMass + (primeDirichletSeries (phasePattern (-a) t₀ φ) w).re) ≤
      Real.exp (Real.log M) := by
    rw [Real.exp_log hM0]
    exact hP.trans hFM
  have hexp := Real.exp_le_exp.mp hlog
  have hneg : (primeDirichletSeries (phasePattern (-a) t₀ φ) w).re =
      -(primeDirichletSeries (phasePattern a t₀ φ) w).re := by
    rw [primeDirichletSeries_phasePattern_neg_amp, Complex.neg_re]
  linarith

/-- At a resonant mode `a cos φ = 1` (`t₀ > 0`), the prime Dirichlet series has a `(1/2) log(1/(u+τ))`
lower bound near `1 + i t₀`. -/
theorem exists_primeDirichletSeries_phasePattern_re_ge_log_of_eq_one {a t₀ φ : ℝ}
    (ha : |a| ≤ 1) (h1 : a * Real.cos φ = 1) (ht₀ : 0 < t₀) :
    ∃ r B : ℝ, 0 < r ∧ ∀ u τ : ℝ, 0 < u → u ≤ r → 0 ≤ τ → τ ≤ r →
      1 / 2 * Real.log ((u + τ)⁻¹) - B ≤
        (primeDirichletSeries (phasePattern a t₀ φ)
          (((1 + u : ℝ) : ℂ) + ((t₀ + τ : ℝ) : ℂ) * I)).re := by
  have hpat : phasePattern a t₀ φ = oscPattern 1 t₀ := phasePattern_eq_oscPattern_one ha h1 t₀
  rw [hpat]
  have hq1 : (1 + 2 * (t₀ : ℂ) * I) ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hqz : riemannZeta (1 + 2 * (t₀ : ℂ) * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  obtain ⟨ρ, hρ, hζ1⟩ := exists_norm_zeta_ge_near_one
  obtain ⟨rq, hrq, hζp⟩ := exists_norm_zeta_gt_near hq1 hqz
  have hcq : 0 < ‖riemannZeta (1 + 2 * (t₀ : ℂ) * I)‖ / 2 :=
    half_pos (norm_pos_iff.mpr hqz)
  set cq : ℝ := ‖riemannZeta (1 + 2 * (t₀ : ℂ) * I)‖ / 2
  set r : ℝ := min (min ρ rq / 4) (1 / 4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr_ρ : 2 * r < ρ := by
    calc 2 * r ≤ 2 * (min ρ rq / 4) := mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
      _ < min ρ rq := by linarith [lt_min hρ hrq]
      _ ≤ ρ := min_le_left _ _
  have hr_rq : 2 * r < rq := by
    calc 2 * r ≤ 2 * (min ρ rq / 4) := mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
      _ < min ρ rq := by linarith [lt_min hρ hrq]
      _ ≤ rq := min_le_right _ _
  refine ⟨r, 3 * primeSquareMass - 1 / 2 * Real.log (cq / 2), hr, fun u τ hu hur hτ hτr => ?_⟩
  set w : ℂ := ((1 + u : ℝ) : ℂ) + ((t₀ + τ : ℝ) : ℂ) * I
  have hwre : 1 < w.re := by simp [w]; linarith
  have hwm : w - (t₀ : ℂ) * I - 1 = (u : ℂ) + (τ : ℂ) * I := by simp only [w]; push_cast; ring
  have hwp : w + (t₀ : ℂ) * I - (1 + 2 * (t₀ : ℂ) * I) = (u : ℂ) + (τ : ℂ) * I := by
    simp only [w]; push_cast; ring
  have hnorm_ut : ‖(u : ℂ) + (τ : ℂ) * I‖ ≤ u + τ := by
    have := Complex.norm_le_abs_re_add_abs_im ((u : ℂ) + (τ : ℂ) * I)
    simpa [abs_of_pos hu, abs_of_nonneg hτ] using this
  have hnorm_ut0 : u ≤ ‖(u : ℂ) + (τ : ℂ) * I‖ := by
    have := Complex.abs_re_le_norm ((u : ℂ) + (τ : ℂ) * I)
    simpa [abs_of_pos hu] using this
  have hut : 0 < u + τ := by linarith
  have hwm1 : w - (t₀ : ℂ) * I ≠ 1 := by
    intro h
    have h0 : w - (t₀ : ℂ) * I - 1 = 0 := by rw [h, sub_self]
    rw [hwm] at h0; rw [h0, norm_zero] at hnorm_ut0; linarith
  have hZm : 1 / (2 * (u + τ)) ≤ ‖riemannZeta (w - (t₀ : ℂ) * I)‖ := by
    have h := hζ1 (w - (t₀ : ℂ) * I) hwm1 (by rw [hwm]; linarith)
    rw [hwm] at h
    exact le_trans (one_div_le_one_div_of_le (by linarith) (by linarith)) h
  have hZp := hζp (w + (t₀ : ℂ) * I) (by rw [hwp]; linarith)
  have hprod : cq / 2 * (u + τ)⁻¹ ≤
      ‖riemannZeta (w - (t₀ : ℂ) * I)‖ * ‖riemannZeta (w + (t₀ : ℂ) * I)‖ := by
    calc cq / 2 * (u + τ)⁻¹ = 1 / (2 * (u + τ)) * cq := by field_simp
      _ ≤ _ := mul_le_mul hZm hZp.le (by positivity) (norm_nonneg _)
  have hosc := (norm_oscSeries_le_ge (a := 1) (by norm_num) t₀ hwre).2
  have hP := (norm_patternSeries_bounds_of_primeDirichletSeries
    (fun p _ => abs_oscPattern_le (a := 1) (by norm_num) t₀ p) hwre).2
  have hpos_lhs : 0 < cq / 2 * (u + τ)⁻¹ := by positivity
  have hexp_le : Real.exp (-(2 * primeSquareMass) + 1 / 2 * Real.log (cq / 2) +
      1 / 2 * Real.log ((u + τ)⁻¹)) ≤
        Real.exp (primeSquareMass + (primeDirichletSeries (oscPattern 1 t₀) w).re) := by
    have h1 : Real.exp (-(2 * primeSquareMass) + 1 / 2 * Real.log (cq / 2) +
        1 / 2 * Real.log ((u + τ)⁻¹)) =
          Real.exp (-(2 * primeSquareMass)) * (cq / 2 * (u + τ)⁻¹) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hpos_lhs, Real.log_mul (by positivity) (by positivity),
        ← Real.exp_add]
      congr 1; ring
    rw [h1]
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hpos_lhs.le hprod (by norm_num))
      (Real.exp_pos _).le).trans (hosc.trans hP)
  have := Real.exp_le_exp.mp hexp_le
  linarith

/-- **A resonant mode at a nonzero critical value leaves the multi-frequency weight unpaid.** -/
theorem not_receiverBounded_multiPhaseWeight_of_eq_one {ι : Type*} (K : Finset ι)
    {a t φ : ι → ℝ} (hf : ∀ p : ℕ, p.Prime → |multiPhasePattern K a t φ p| ≤ 1)
    (ha : ∀ k ∈ K, |a k| ≤ 1) (ht : ∀ k ∈ K, 0 < t k) (hinj : Set.InjOn t (K : Set ι))
    {k₀ : ι} (hk₀ : k₀ ∈ K) (h1 : a k₀ * Real.cos (φ k₀) = 1)
    (hz : riemannZeta (1 / 2 + (t k₀ : ℂ) * I) ≠ 0) :
    ¬ ReceiverBounded (multiPhaseWeight K a t φ) := by
  classical
  obtain ⟨r₀, B₀, hr₀, h0⟩ :=
    exists_primeDirichletSeries_phasePattern_re_ge_log_of_eq_one (ha k₀ hk₀) h1 (ht k₀ hk₀)
  set J : Finset ι := K.erase k₀
  have hJ : ∀ k ∈ J, ∃ r B : ℝ, 0 < r ∧ ∀ u τ : ℝ, 0 < u → u ≤ r → 0 ≤ τ → τ ≤ r →
      -B ≤ (primeDirichletSeries (phasePattern (a k) (t k) (φ k))
        (((1 + u : ℝ) : ℂ) + ((t k₀ + τ : ℝ) : ℂ) * I)).re := by
    intro k hk
    have hkK : k ∈ K := Finset.mem_of_mem_erase hk
    have hkne : k ≠ k₀ := Finset.ne_of_mem_erase hk
    have htne : t k ≠ t k₀ := fun h =>
      hkne (hinj (Finset.mem_coe.mpr hkK) (Finset.mem_coe.mpr hk₀) h)
    obtain ⟨r, B, hr, hB⟩ := exists_primeDirichletSeries_phasePattern_re_ge_of_ne
      (ha k hkK) (ht k hkK) (ht k₀ hk₀) htne
    exact ⟨r, |B|, hr, fun u τ hu hur hτ hτr =>
      (neg_le_neg (le_abs_self B)).trans (hB u τ hu hur hτ hτr)⟩
  -- combine `r` and `B` across `J` by finite induction
  have hJ_sum : ∀ S : Finset ι, (∀ k ∈ S, ∃ r B : ℝ, 0 < r ∧ ∀ u τ : ℝ, 0 < u → u ≤ r →
      0 ≤ τ → τ ≤ r →
        -B ≤ (primeDirichletSeries (phasePattern (a k) (t k) (φ k))
          (((1 + u : ℝ) : ℂ) + ((t k₀ + τ : ℝ) : ℂ) * I)).re) →
      ∃ rJ BJ : ℝ, 0 < rJ ∧ ∀ u τ : ℝ, 0 < u → u ≤ rJ → 0 ≤ τ → τ ≤ rJ →
        -BJ ≤ ∑ k ∈ S, (primeDirichletSeries (phasePattern (a k) (t k) (φ k))
          (((1 + u : ℝ) : ℂ) + ((t k₀ + τ : ℝ) : ℂ) * I)).re := by
    intro S
    induction S using Finset.induction with
    | empty => intro _; exact ⟨1, 0, zero_lt_one, fun _ _ _ _ _ _ => by simp⟩
    | @insert j s hj ih =>
      intro hjJ
      obtain ⟨rj, Bj, hrj, hBj⟩ := hjJ j (Finset.mem_insert_self j s)
      obtain ⟨rs, Bs, hrs, hBs⟩ := ih (fun k hk => hjJ k (Finset.mem_insert_of_mem hk))
      refine ⟨min rj rs, Bj + Bs, lt_min hrj hrs, fun u τ hu hur hτ hτr => ?_⟩
      rw [Finset.sum_insert hj]
      have h1' := hBj u τ hu (hur.trans (min_le_left _ _)) hτ (hτr.trans (min_le_left _ _))
      have h2' := hBs u τ hu (hur.trans (min_le_right _ _)) hτ (hτr.trans (min_le_right _ _))
      linarith
  obtain ⟨rJ, BJ, hrJ, hBJ⟩ := hJ_sum J hJ
  refine not_receiverBounded_pattern_half_of_primeDirichletSeries_re_ge hf hz
    (r₁ := min r₀ rJ) (B := B₀ + BJ) (lt_min hr₀ hrJ) fun u τ hu hur hτ hτr => ?_
  set w : ℂ := ((1 + u : ℝ) : ℂ) + ((t k₀ + τ : ℝ) : ℂ) * I
  have hwre : 1 < w.re := by simp [w]; linarith
  have hsum := primeDirichletSeries_eq_sum K
    (fun k hk p _ => abs_phasePattern_le (ha k hk) (t k) (φ k) p)
    (fun p hp => multiPhasePattern_prime_eq_sum_phasePattern K a t φ hp) hwre
  rw [hsum, Complex.re_sum, ← Finset.insert_erase hk₀,
    Finset.sum_insert (Finset.notMem_erase k₀ K)]
  have h_main := h0 u τ hu (hur.trans (min_le_left _ _)) hτ (hτr.trans (min_le_left _ _))
  have h_rest := hBJ u τ hu (hur.trans (min_le_right _ _)) hτ (hτr.trans (min_le_right _ _))
  linarith

/-- Under the amplitude budget `∑_{k ∈ K} |a_k| ≤ 1`, if `a_{k₀} cos φ_{k₀} ≥ 1` at some `k₀ ∈ K`,
then `a_{k₀} cos φ_{k₀} = 1`, `|a_{k₀}| = 1`, and `a_k = 0` for all `k ≠ k₀`, so the multi-frequency
weight reduces to `oscWeight 1 (t k₀)`. -/
theorem multiPhaseWeight_eq_oscWeight_one_of_sum_abs_le_one {ι : Type*} {K : Finset ι}
    {a : ι → ℝ} (ha : ∑ k ∈ K, |a k| ≤ 1) (t φ : ι → ℝ) {k₀ : ι} (hk₀ : k₀ ∈ K)
    (hge : 1 ≤ a k₀ * Real.cos (φ k₀)) :
    a k₀ * Real.cos (φ k₀) = 1 ∧ multiPhaseWeight K a t φ = oscWeight 1 (t k₀) := by
  classical
  have hcos : a k₀ * Real.cos (φ k₀) ≤ |a k₀| :=
    (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
  have hsplit : |a k₀| + ∑ k ∈ K.erase k₀, |a k| = ∑ k ∈ K, |a k| :=
    Finset.add_sum_erase _ (fun k => |a k|) hk₀
  have hrest_nonneg : 0 ≤ ∑ k ∈ K.erase k₀, |a k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have h1 : a k₀ * Real.cos (φ k₀) = 1 := by linarith
  have hak₀ : |a k₀| ≤ 1 := by linarith
  have hrest0 : ∑ k ∈ K.erase k₀, |a k| = 0 := by linarith
  have hak_zero : ∀ k ∈ K.erase k₀, a k = 0 := fun k hk => by
    have hle := Finset.single_le_sum (fun j _ => abs_nonneg (a j)) hk
    exact abs_eq_zero.mp (le_antisymm (hrest0 ▸ hle) (abs_nonneg _))
  refine ⟨h1, ?_⟩
  have hpat : multiPhasePattern K a t φ = phasePattern (a k₀) (t k₀) (φ k₀) := by
    unfold multiPhasePattern phasePattern
    congr 1; funext p
    rw [← Finset.insert_erase hk₀, Finset.sum_insert (Finset.notMem_erase k₀ K),
      Finset.sum_eq_zero (fun k hk => by rw [hak_zero k hk, zero_mul]), add_zero]
  funext d
  simp only [multiPhaseWeight, oscWeight, hpat, phasePattern_eq_oscPattern_one hak₀ h1 (t k₀)]

/-- **The multi-frequency phase law.** For pairwise distinct positive frequencies `t_k > 0`
(`k ∈ K`) and amplitudes satisfying `∑_{k ∈ K} |a_k| ≤ 1`, the half-damped weight
`multiPhaseWeight K a t φ` is paid if and only if for every `k ∈ K`,
`a_k cos φ_k < 1` or `ζ(1/2 + i t_k) = 0`. -/
theorem receiverBounded_multiPhaseWeight_iff {ι : Type*} (K : Finset ι) {a t φ : ι → ℝ}
    (ha : ∑ k ∈ K, |a k| ≤ 1) (ht : ∀ k ∈ K, 0 < t k) (hinj : Set.InjOn t (K : Set ι)) :
    ReceiverBounded (multiPhaseWeight K a t φ) ↔
      ∀ k ∈ K, a k * Real.cos (φ k) < 1 ∨ riemannZeta (1 / 2 + (t k : ℂ) * I) = 0 := by
  have hf : ∀ p : ℕ, p.Prime → |multiPhasePattern K a t φ p| ≤ 1 :=
    fun p _ => abs_multiPhasePattern_le_of_sum_abs_le_one ha t φ p
  have hak : ∀ k ∈ K, |a k| ≤ 1 := fun k hk =>
    (Finset.single_le_sum (fun j _ => abs_nonneg (a j)) hk).trans ha
  by_cases h_all : ∀ k ∈ K, a k * Real.cos (φ k) < 1
  · exact ⟨fun _ k hk => Or.inl (h_all k hk),
      fun _ => receiverBounded_multiPhaseWeight_of_forall_lt_one K hf hak ht hinj h_all⟩
  push Not at h_all
  obtain ⟨k₀, hk₀, hge⟩ := h_all
  obtain ⟨h1, hw⟩ := multiPhaseWeight_eq_oscWeight_one_of_sum_abs_le_one ha t φ hk₀ hge
  rw [hw, receiverBounded_oscWeight_iff (by norm_num) le_rfl]
  have ht0 : t k₀ ≠ 0 := (ht k₀ hk₀).ne'
  simp only [ht0, false_and, false_or, ne_eq, not_false_eq_true, true_and, lt_irrefl]
  constructor
  · intro hz k hk
    by_cases hlt : a k * Real.cos (φ k) < 1
    · exact Or.inl hlt
    · obtain ⟨hk1, hwk⟩ := multiPhaseWeight_eq_oscWeight_one_of_sum_abs_le_one ha t φ hk
        (not_lt.mp hlt)
      -- since `a k ≠ 0` and `a_j = 0` for `j ≠ k₀`, `k = k₀`
      have h_eq : k = k₀ := by
        by_contra hne
        have hcos : a k * Real.cos (φ k) ≤ |a k| :=
          (le_abs_self _).trans (by
            rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
        have hpair : |a k₀| + |a k| ≤ ∑ j ∈ K, |a j| := by
          classical
          have hsub : ({k₀, k} : Finset ι) ⊆ K := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact hk₀
            · exact Finset.mem_singleton.mp hx ▸ hk
          have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => abs_nonneg (a j))
          rwa [Finset.sum_pair (Ne.symm hne)] at this
        have hcos0 : a k₀ * Real.cos (φ k₀) ≤ |a k₀| :=
          (le_abs_self _).trans (by
            rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
        linarith
      exact Or.inr (h_eq ▸ hz)
  · intro h
    rcases h k₀ hk₀ with hlt | hz
    · linarith
    · exact hz

/-- **Two or more active frequencies under a unit amplitude budget always pay the receiver.** -/
theorem receiverBounded_multiPhaseWeight_of_two_active {ι : Type*} (I : Finset ι)
    {a t φ : ι → ℝ} (ha : ∑ k ∈ I, |a k| ≤ 1) (ht : ∀ k ∈ I, 0 < t k)
    (hinj : Set.InjOn t (I : Set ι)) {k₁ k₂ : ι} (hk₁ : k₁ ∈ I) (hk₂ : k₂ ∈ I)
    (hne : k₁ ≠ k₂) (ha₁ : a k₁ ≠ 0) (ha₂ : a k₂ ≠ 0) :
    ReceiverBounded (multiPhaseWeight I a t φ) := by
  have hf : ∀ p : ℕ, p.Prime → |multiPhasePattern I a t φ p| ≤ 1 :=
    fun p _ => abs_multiPhasePattern_le_of_sum_abs_le_one ha t φ p
  have hak : ∀ k ∈ I, |a k| < 1 := by
    intro k hk
    classical
    by_cases hk1 : k = k₁
    · subst hk1
      have hsub : ({k, k₂} : Finset ι) ⊆ I := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hk
        · exact Finset.mem_singleton.mp hx ▸ hk₂
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => abs_nonneg (a j))
      rw [Finset.sum_pair hne] at hle
      have hpos : 0 < |a k₂| := abs_pos.mpr ha₂
      linarith
    · have hsub : ({k, k₁} : Finset ι) ⊆ I := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hk
        · exact Finset.mem_singleton.mp hx ▸ hk₁
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => abs_nonneg (a j))
      rw [Finset.sum_pair hk1] at hle
      have hpos : 0 < |a k₁| := abs_pos.mpr ha₁
      linarith
  refine receiverBounded_multiPhaseWeight_of_forall_lt_one I hf (fun k hk => (hak k hk).le)
    ht hinj fun k hk => ?_
  calc a k * Real.cos (φ k) ≤ |a k * Real.cos (φ k)| := le_abs_self _
    _ = |a k| * |Real.cos (φ k)| := abs_mul _ _
    _ ≤ |a k| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
    _ < 1 := by linarith [hak k hk]

/-- Along the horizontal ray `1 + u + i t₀` (`t₀ > 0`, `0 < u ≤ 1`), the prime Dirichlet series of
`phasePattern a t₀ φ` has real part `(a cos φ / 2) log(1/u) + O(1)`. -/
theorem exists_abs_primeDirichletSeries_phasePattern_re_sub_log_le {a t₀ φ : ℝ}
    (ha : |a| ≤ 1) (ht₀ : 0 < t₀) :
    ∃ B : ℝ, ∀ u : ℝ, 0 < u → u ≤ 1 →
      |(primeDirichletSeries (phasePattern a t₀ φ)
          (((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I)).re -
        (a * Real.cos φ / 2) * Real.log (u⁻¹)| ≤ B := by
  set H : ℝ := 2 * t₀ + 1
  obtain ⟨C, hC⟩ := RHTower.exists_abs_im_zetaEulerLog_le H
  obtain ⟨m, K, hm, hmK⟩ := RHTower.exists_norm_zeta_mul_sub_one_bounds H
  have hD : 1 ≤ 1 + H := by simp only [H]; linarith
  set Lbd : ℝ := max (|Real.log m|) (|Real.log K|) +
    max (|Real.log (m / (1 + H))|) (|Real.log (K / (2 * t₀))|)
  refine ⟨3 * primeSquareMass + C + Lbd, fun u hu hu1 => ?_⟩
  set w : ℂ := ((1 + u : ℝ) : ℂ) + (t₀ : ℂ) * I
  have hwre : 1 < w.re := by simp [w]; linarith
  have hw2 : w.re ≤ 2 := by simp [w]; linarith
  have hwm : w - (t₀ : ℂ) * I = ((1 + u : ℝ) : ℂ) + (0 : ℝ) * I := by simp [w]
  have hwp : w + (t₀ : ℂ) * I = ((1 + u : ℝ) : ℂ) + ((2 * t₀ : ℝ) : ℂ) * I := by
    simp only [w]; push_cast; ring
  have h1 := abs_log_norm_patternSeries_sub_re_primeDirichletSeries_le
    (fun p _ => abs_phasePattern_le ha t₀ φ p) hwre
  have h2 := abs_log_norm_phaseSeries_sub_le ha t₀ φ hwre
  set E : ℝ := (((a / 2 : ℝ) : ℂ) * Complex.exp (φ * I) * RHTower.zetaEulerLog (w - t₀ * I) +
    ((a / 2 : ℝ) : ℂ) * Complex.exp (((-φ : ℝ) : ℂ) * I) * RHTower.zetaEulerLog (w + t₀ * I)).re
  have hPE : |(primeDirichletSeries (phasePattern a t₀ φ) w).re - E| ≤ 3 * primeSquareMass := by
    have := abs_sub_le (primeDirichletSeries (phasePattern a t₀ φ) w).re
      (Real.log ‖∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖) E
    rw [abs_sub_comm] at h1
    linarith
  have hE_eq : E = (a * Real.cos φ / 2) *
      (Real.log ‖riemannZeta (w - t₀ * I)‖ + Real.log ‖riemannZeta (w + t₀ * I)‖) -
      (a * Real.sin φ / 2) *
        ((RHTower.zetaEulerLog (w - t₀ * I)).im - (RHTower.zetaEulerLog (w + t₀ * I)).im) := by
    simp only [E]
    rw [Complex.add_re, re_mul_exp_mul_I, re_mul_exp_mul_I,
      RHTower.re_zetaEulerLog (by simpa using hwre), RHTower.re_zetaEulerLog (by simpa using hwre),
      Real.cos_neg, Real.sin_neg]
    ring
  -- argument bound
  have hCm := hC u 0 hu hu1 (by simp [H]; linarith)
  have hCp := hC u (2 * t₀) hu hu1 (by rw [abs_of_pos (by linarith)]; simp [H])
  rw [← hwm] at hCm
  rw [← hwp] at hCp
  have hasin : |a * Real.sin φ| ≤ 1 := by
    rw [abs_mul]; exact mul_le_one₀ ha (abs_nonneg _) (Real.abs_sin_le_one φ)
  have harg : |(a * Real.sin φ / 2) *
      ((RHTower.zetaEulerLog (w - t₀ * I)).im - (RHTower.zetaEulerLog (w + t₀ * I)).im)| ≤ C := by
    rw [abs_mul, abs_div, abs_two]
    have hdiff_im := (abs_sub _ _).trans (add_le_add hCm hCp)
    nlinarith [abs_nonneg ((RHTower.zetaEulerLog (w - t₀ * I)).im -
      (RHTower.zetaEulerLog (w + t₀ * I)).im)]
  -- modulus bounds on `ζ(w - it₀) = ζ(1 + u)` and `ζ(w + it₀) = ζ(1 + u + 2it₀)`
  obtain ⟨hm1, hK1⟩ := hmK (w - t₀ * I) (by simpa using hwre) (by simpa using hw2)
    (by rw [hwm]; simp [H]; linarith)
  obtain ⟨hm2, hK2⟩ := hmK (w + t₀ * I) (by simpa using hwre) (by simpa using hw2)
    (by rw [hwp]; simp [H, abs_of_pos (by linarith : 0 < 2 * t₀)])
  have hnorm_wm : ‖w - t₀ * I - 1‖ = u := by
    rw [hwm, show ((1 + u : ℝ) : ℂ) + (0 : ℝ) * I - 1 = (u : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  rw [hnorm_wm] at hm1 hK1
  have hzm_pos : 0 < ‖riemannZeta (w - t₀ * I)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by simpa using hwre.le))
  have hK_pos : 0 < K := lt_of_lt_of_le hm (hm1.trans hK1)
  have hlog_m1 : Real.log m ≤ Real.log ‖riemannZeta (w - t₀ * I)‖ - Real.log (u⁻¹) := by
    rw [Real.log_inv, sub_neg_eq_add, ← Real.log_mul hzm_pos.ne' hu.ne']
    exact Real.log_le_log hm hm1
  have hlog_K1 : Real.log ‖riemannZeta (w - t₀ * I)‖ - Real.log (u⁻¹) ≤ Real.log K := by
    rw [Real.log_inv, sub_neg_eq_add, ← Real.log_mul hzm_pos.ne' hu.ne']
    exact Real.log_le_log (mul_pos hzm_pos hu) hK1
  have habs1 : |Real.log ‖riemannZeta (w - t₀ * I)‖ - Real.log (u⁻¹)| ≤
      max (|Real.log m|) (|Real.log K|) := by
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le (Real.log m), le_max_left (|Real.log m|) (|Real.log K|)],
      by linarith [le_abs_self (Real.log K), le_max_right (|Real.log m|) (|Real.log K|)]⟩
  have hdp_low : 2 * t₀ ≤ ‖w + t₀ * I - 1‖ := by
    have := Complex.abs_im_le_norm (w + t₀ * I - 1)
    have him : (w + t₀ * I - 1).im = 2 * t₀ := by simp [w]; ring
    rw [him, abs_of_pos (by linarith : 0 < 2 * t₀)] at this
    exact this
  have hdp_up : ‖w + t₀ * I - 1‖ ≤ 1 + H := by
    calc ‖w + t₀ * I - 1‖ ≤ |(w + t₀ * I - 1).re| + |(w + t₀ * I - 1).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + H := by
          rw [hwp]
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            add_zero, sub_re, one_re, add_im, mul_im, zero_add, sub_im, one_im, sub_zero]
          rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
          simp only [H]; linarith
  have hzp_pos : 0 < ‖riemannZeta (w + t₀ * I)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by simpa using hwre.le))
  have hzp_low : m / (1 + H) ≤ ‖riemannZeta (w + t₀ * I)‖ := by
    rw [div_le_iff₀ (by linarith)]
    exact hm2.trans (mul_le_mul_of_nonneg_left hdp_up hzp_pos.le)
  have hzp_up : ‖riemannZeta (w + t₀ * I)‖ ≤ K / (2 * t₀) := by
    rw [le_div_iff₀ (by linarith)]
    exact (mul_le_mul_of_nonneg_left hdp_low hzp_pos.le).trans hK2
  have hlog_m2 : Real.log (m / (1 + H)) ≤ Real.log ‖riemannZeta (w + t₀ * I)‖ :=
    Real.log_le_log (by positivity) hzp_low
  have hlog_K2 : Real.log ‖riemannZeta (w + t₀ * I)‖ ≤ Real.log (K / (2 * t₀)) :=
    Real.log_le_log hzp_pos hzp_up
  have habs2 : |Real.log ‖riemannZeta (w + t₀ * I)‖| ≤
      max (|Real.log (m / (1 + H))|) (|Real.log (K / (2 * t₀))|) := by
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le (Real.log (m / (1 + H))),
        le_max_left (|Real.log (m / (1 + H))|) (|Real.log (K / (2 * t₀))|)],
      by linarith [le_abs_self (Real.log (K / (2 * t₀))),
        le_max_right (|Real.log (m / (1 + H))|) (|Real.log (K / (2 * t₀))|)]⟩
  have hacos : |a * Real.cos φ / 2| ≤ 1 := by
    rw [abs_div, abs_two, abs_mul]
    have := mul_le_one₀ ha (abs_nonneg _) (Real.abs_cos_le_one φ)
    linarith
  have hmod : |(a * Real.cos φ / 2) *
      (Real.log ‖riemannZeta (w - t₀ * I)‖ + Real.log ‖riemannZeta (w + t₀ * I)‖ -
        Real.log (u⁻¹))| ≤ Lbd := by
    rw [abs_mul]
    have hsum_abs : |Real.log ‖riemannZeta (w - t₀ * I)‖ + Real.log ‖riemannZeta (w + t₀ * I)‖ -
        Real.log (u⁻¹)| ≤ Lbd := by
      calc |Real.log ‖riemannZeta (w - t₀ * I)‖ + Real.log ‖riemannZeta (w + t₀ * I)‖ -
              Real.log (u⁻¹)|
          = |(Real.log ‖riemannZeta (w - t₀ * I)‖ - Real.log (u⁻¹)) +
              Real.log ‖riemannZeta (w + t₀ * I)‖| := by ring_nf
        _ ≤ |Real.log ‖riemannZeta (w - t₀ * I)‖ - Real.log (u⁻¹)| +
              |Real.log ‖riemannZeta (w + t₀ * I)‖| := abs_add_le _ _
        _ ≤ Lbd := add_le_add habs1 habs2
    nlinarith [abs_nonneg (Real.log ‖riemannZeta (w - t₀ * I)‖ +
      Real.log ‖riemannZeta (w + t₀ * I)‖ - Real.log (u⁻¹))]
  have hE_log : |E - (a * Real.cos φ / 2) * Real.log (u⁻¹)| ≤ C + Lbd := by
    have heq : E - (a * Real.cos φ / 2) * Real.log (u⁻¹) =
        (a * Real.cos φ / 2) *
          (Real.log ‖riemannZeta (w - t₀ * I)‖ + Real.log ‖riemannZeta (w + t₀ * I)‖ -
            Real.log (u⁻¹)) -
        (a * Real.sin φ / 2) *
          ((RHTower.zetaEulerLog (w - t₀ * I)).im - (RHTower.zetaEulerLog (w + t₀ * I)).im) := by
      rw [hE_eq]; ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)
  have htri := abs_sub_le (primeDirichletSeries (phasePattern a t₀ φ) w).re E
    ((a * Real.cos φ / 2) * Real.log (u⁻¹))
  linarith

/-- Near a distinct height `t₁ ≠ t₀`, the prime Dirichlet series of `phasePattern a t₀ φ` is
bounded in absolute value along `1 + u + i t₁`. -/
theorem exists_abs_primeDirichletSeries_phasePattern_re_le_of_ne {a t₀ φ t₁ : ℝ}
    (ha : |a| ≤ 1) (ht₀ : 0 < t₀) (ht₁ : 0 < t₁) (hne : t₀ ≠ t₁) :
    ∃ r B : ℝ, 0 < r ∧ ∀ u : ℝ, 0 < u → u ≤ r →
      |(primeDirichletSeries (phasePattern a t₀ φ) (((1 + u : ℝ) : ℂ) + (t₁ : ℂ) * I)).re| ≤ B := by
  obtain ⟨r₁, B₁, hr₁, h1⟩ :=
    exists_primeDirichletSeries_phasePattern_re_ge_of_ne ha ht₀ ht₁ hne
  have hna : |-a| ≤ 1 := by rwa [abs_neg]
  obtain ⟨r₂, B₂, hr₂, h2⟩ :=
    exists_primeDirichletSeries_phasePattern_re_ge_of_ne (φ := φ) hna ht₀ ht₁ hne
  refine ⟨min r₁ r₂, max (|B₁|) (|B₂|), lt_min hr₁ hr₂, fun u hu hur => ?_⟩
  set w : ℂ := ((1 + u : ℝ) : ℂ) + (t₁ : ℂ) * I
  have hw0 : ((1 + u : ℝ) : ℂ) + ((t₁ + (0 : ℝ) : ℝ) : ℂ) * I = w := by simp [w]
  have hb1 := h1 u 0 hu (hur.trans (min_le_left _ _)) le_rfl (by linarith [lt_min hr₁ hr₂])
  have hb2 := h2 u 0 hu (hur.trans (min_le_right _ _)) le_rfl (by linarith [lt_min hr₁ hr₂])
  rw [hw0] at hb1 hb2
  rw [primeDirichletSeries_phasePattern_neg_amp, Complex.neg_re] at hb2
  rw [abs_le]
  exact ⟨by linarith [le_abs_self B₁, le_max_left (|B₁|) (|B₂|)],
    by linarith [le_abs_self B₂, le_max_right (|B₁|) (|B₂|)]⟩

/-- **Below half damping, a paid multi-frequency pattern has `a_k cos φ_k = 0` at every mode.** -/
theorem cos_coeff_eq_zero_of_receiverBounded_multiPhase_damped {ι : Type*} (K : Finset ι)
    {a t φ : ι → ℝ} (hf : ∀ p : ℕ, p.Prime → |multiPhasePattern K a t φ p| ≤ 1)
    (ha : ∀ k ∈ K, |a k| ≤ 1) (ht : ∀ k ∈ K, 0 < t k) (hinj : Set.InjOn t (K : Set ι))
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hR : ReceiverBounded (dampedSignWeight (multiPhasePattern K a t φ) ε)) :
    ∀ k ∈ K, a k * Real.cos (φ k) = 0 := by
  classical
  intro k₀ hk₀
  obtain ⟨B₀, hB₀⟩ :=
    exists_abs_primeDirichletSeries_phasePattern_re_sub_log_le (φ := φ k₀) (ha k₀ hk₀) (ht k₀ hk₀)
  set J : Finset ι := K.erase k₀
  have hJ : ∀ k ∈ J, ∃ r B : ℝ, 0 < r ∧ ∀ u : ℝ, 0 < u → u ≤ r →
      |(primeDirichletSeries (phasePattern (a k) (t k) (φ k))
        (((1 + u : ℝ) : ℂ) + (t k₀ : ℂ) * I)).re| ≤ B := by
    intro k hk
    have hkK : k ∈ K := Finset.mem_of_mem_erase hk
    have hkne : k ≠ k₀ := Finset.ne_of_mem_erase hk
    have htne : t k ≠ t k₀ := fun h =>
      hkne (hinj (Finset.mem_coe.mpr hkK) (Finset.mem_coe.mpr hk₀) h)
    exact exists_abs_primeDirichletSeries_phasePattern_re_le_of_ne
      (ha k hkK) (ht k hkK) (ht k₀ hk₀) htne
  have hJ_sum : ∀ S : Finset ι, (∀ k ∈ S, ∃ r B : ℝ, 0 < r ∧ ∀ u : ℝ, 0 < u → u ≤ r →
      |(primeDirichletSeries (phasePattern (a k) (t k) (φ k))
        (((1 + u : ℝ) : ℂ) + (t k₀ : ℂ) * I)).re| ≤ B) →
      ∃ rJ BJ : ℝ, 0 < rJ ∧ ∀ u : ℝ, 0 < u → u ≤ rJ →
        |∑ k ∈ S, (primeDirichletSeries (phasePattern (a k) (t k) (φ k))
          (((1 + u : ℝ) : ℂ) + (t k₀ : ℂ) * I)).re| ≤ BJ := by
    intro S
    induction S using Finset.induction with
    | empty => intro _; exact ⟨1, 0, zero_lt_one, fun _ _ _ => by simp⟩
    | @insert j s hj ih =>
      intro hjJ
      obtain ⟨rj, Bj, hrj, hBj⟩ := hjJ j (Finset.mem_insert_self j s)
      obtain ⟨rs, Bs, hrs, hBs⟩ := ih (fun k hk => hjJ k (Finset.mem_insert_of_mem hk))
      refine ⟨min rj rs, Bj + Bs, lt_min hrj hrs, fun u hu hur => ?_⟩
      rw [Finset.sum_insert hj]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · exact hBj u hu (hur.trans (min_le_left _ _))
      · exact hBs u hu (hur.trans (min_le_right _ _))
  obtain ⟨rJ, BJ, hrJ, hBJ⟩ := hJ_sum J hJ
  have hν_lt : |a k₀ * Real.cos (φ k₀) / 2| < 1 := by
    rw [abs_div, abs_two, abs_mul]
    have := mul_le_one₀ (ha k₀ hk₀) (abs_nonneg _) (Real.abs_cos_le_one (φ k₀))
    linarith
  have hν0 := localPrimeMean_eq_zero_of_receiverBounded_damped hf (ht k₀ hk₀).ne' hε hε2 hν_lt
    (u₀ := min rJ 1) (B := B₀ + BJ) (lt_min hrJ zero_lt_one)
    (fun u hu hur => by
      set w : ℂ := ((1 + u : ℝ) : ℂ) + (t k₀ : ℂ) * I
      have hwre : 1 < w.re := by simp [w]; linarith
      have hsum := primeDirichletSeries_eq_sum K
        (fun k hk p _ => abs_phasePattern_le (ha k hk) (t k) (φ k) p)
        (fun p hp => multiPhasePattern_prime_eq_sum_phasePattern K a t φ hp) hwre
      rw [hsum, Complex.re_sum, ← Finset.insert_erase hk₀,
        Finset.sum_insert (Finset.notMem_erase k₀ K)]
      have h_main := hB₀ u hu (hur.le.trans (min_le_right _ _))
      have h_rest := hBJ u hu (hur.le.trans (min_le_left _ _))
      calc |(primeDirichletSeries (phasePattern (a k₀) (t k₀) (φ k₀)) w).re +
              (∑ x ∈ J, (primeDirichletSeries (phasePattern (a x) (t x) (φ x)) w).re) -
              a k₀ * Real.cos (φ k₀) / 2 * Real.log (u⁻¹)|
          = |((primeDirichletSeries (phasePattern (a k₀) (t k₀) (φ k₀)) w).re -
              a k₀ * Real.cos (φ k₀) / 2 * Real.log (u⁻¹)) +
              ∑ x ∈ J, (primeDirichletSeries (phasePattern (a x) (t x) (φ x)) w).re| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ B₀ + BJ := add_le_add h_main h_rest)
    hR
  linarith

/-! ### §4. Prime-varying amplitudes and critical Wiener prime-perturbation invariance -/

/-- A completely multiplicative pattern `f : ℕ →*₀ ℝ` as an `ArithmeticFunction ℝ`. -/
def patternAF (f : ℕ →*₀ ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n, map_zero f⟩

theorem isMultiplicative_patternAF (f : ℕ →*₀ ℝ) : (patternAF f).IsMultiplicative :=
  ⟨map_one f, fun {m n} _ => map_mul f m n⟩

/-- `μf`, the Dirichlet inverse of a completely multiplicative pattern `f : ℕ →*₀ ℝ`. -/
def patternMoebiusAF (f : ℕ →*₀ ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => moebiusReal n * f n, by simp⟩

theorem isMultiplicative_patternMoebiusAF (f : ℕ →*₀ ℝ) :
    (patternMoebiusAF f).IsMultiplicative := by
  refine ⟨by simp [patternMoebiusAF, moebiusReal], fun {m n} hmn => ?_⟩
  simp only [patternMoebiusAF, ArithmeticFunction.coe_mk, moebiusReal, map_mul,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
  push_cast; ring

theorem patternMoebiusAF_mul_patternAF (f : ℕ →*₀ ℝ) :
    patternMoebiusAF f * patternAF f = 1 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply]
  have h : ∀ p ∈ n.divisorsAntidiagonal, patternMoebiusAF f p.1 * patternAF f p.2 =
      moebiusReal p.1 * f n := fun p hp => by
    obtain ⟨hpn, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    simp only [patternMoebiusAF, patternAF, ArithmeticFunction.coe_mk]
    rw [← hpn, map_mul]; ring
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul,
    Nat.sum_divisorsAntidiagonal (fun a _ => moebiusReal a)]
  have hμ := congrArg (fun F : ArithmeticFunction ℝ => F n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply] at hμ
  rw [show ∑ i ∈ n.divisors, moebiusReal i = (1 : ArithmeticFunction ℝ) n from hμ]
  rcases eq_or_ne n 1 with rfl | hn1
  · simp
  · simp [hn1]

/-- For any arithmetic function `f'` and completely multiplicative `f : ℕ →*₀ ℝ`, the defect kernel
`g = f' ⋆ μf` at prime powers satisfies `g(p^{m+1}) = f'(p^{m+1}) − f(p) f'(p^m)`. -/
theorem mul_patternMoebiusAF_apply_prime_pow (f' : ArithmeticFunction ℝ) (f : ℕ →*₀ ℝ)
    {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (f' * patternMoebiusAF f) (p ^ (m + 1)) = f' (p ^ (m + 1)) - f p * f' (p ^ m) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => f' a * patternMoebiusAF f b),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero : ∀ j ∈ Finset.range m, f' (p ^ j) * patternMoebiusAF f (p ^ (m + 1) / p ^ j) = 0 :=
    fun j hj => by
      have hj := Finset.mem_range.mp hj
      rw [Nat.pow_div (by omega) hp.pos]
      have hsq : ¬ Squarefree (p ^ (m + 1 - j)) := by
        rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]; omega
      simp [patternMoebiusAF, moebiusReal,
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
  rw [Finset.sum_eq_zero hzero, zero_add, Nat.pow_div (by omega) hp.pos, Nat.pow_div le_rfl hp.pos,
    show m + 1 - m = 1 by omega, Nat.sub_self, pow_one, pow_zero]
  simp [patternMoebiusAF, moebiusReal, ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- `f' d^{-ε} = (f' ⋆ μf) d^{-ε} ⋆ f d^{-ε}` for any `f' : ArithmeticFunction ℝ` and
`f : ℕ →*₀ ℝ`. -/
theorem dampedSignWeight_eq_dirichletConv_patternMoebiusAF (f' : ArithmeticFunction ℝ)
    (f : ℕ →*₀ ℝ) (ε : ℝ) :
    dampedSignWeight ⇑f' ε = RHTower.dirichletConv
      (dampedSignWeight ⇑(f' * patternMoebiusAF f) ε) (dampedSignWeight f ε) := by
  funext n
  have hfg : f' = (f' * patternMoebiusAF f) * patternAF f := by
    rw [mul_assoc, patternMoebiusAF_mul_patternAF, mul_one]
  have h : f' n = ((f' * patternMoebiusAF f) * patternAF f) n := congrArg (fun F => F n) hfg
  rw [dampedSignWeight, h, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => (f' * patternMoebiusAF f) a * patternAF f b),
    RHTower.dirichletConv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [Nat.mul_div_cancel_left k hd0]
  simp only [patternAF, ArithmeticFunction.coe_mk, dampedSignWeight, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

/-- **Critical Wiener prime-perturbation theorem.** Let `f : ℕ →*₀ ℝ` be completely multiplicative
with `|f(p)| ≤ 1`, and let `f' : ArithmeticFunction ℝ` be multiplicative (`f'.IsMultiplicative`)
with `|f'(n)| ≤ 1`. If `∑_p |f'(p) − f(p)| p^{-(1/2 + ε)} < ∞` (`ε > 0`), then the defect kernel
`(f' ⋆ μf)(d) d^{-ε}` lies in the critical Wiener algebra. -/
theorem criticalWiener_mul_patternMoebiusAF {f' : ArithmeticFunction ℝ} (hf' : f'.IsMultiplicative)
    (hbd : ∀ n, |f' n| ≤ 1) {f : ℕ →*₀ ℝ} (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) {ε : ℝ}
    (hε : 0 < ε)
    (hdiff : Summable (fun p : ℕ => if p.Prime then |f' p - f p| * (p : ℝ) ^ (-(1 / 2 + ε)) else 0)) :
    CriticalWiener (dampedSignWeight ⇑(f' * patternMoebiusAF f) ε) := by
  set g := f' * patternMoebiusAF f
  have hg : g.IsMultiplicative := hf'.mul (isMultiplicative_patternMoebiusAF f)
  set σ : ℝ := 1 / 2 + ε
  let M : ArithmeticFunction ℝ := ⟨fun n => |g n| * (n : ℝ) ^ (-σ), by simp⟩
  have hM : M.IsMultiplicative := by
    refine ⟨by simp [M, hg.map_one], fun {m n} hmn => ?_⟩
    simp only [M, ArithmeticFunction.coe_mk, hg.map_mul_of_coprime hmn, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  have hM0 : ∀ n, 0 ≤ M n := fun n => by simp only [M, ArithmeticFunction.coe_mk]; positivity
  have hloc : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => M (p ^ k)) ∧
      ∑' k : ℕ, M (p ^ k) ≤
        Real.exp (|f' p - f p| * (p : ℝ) ^ (-σ) + 8 * (p : ℝ) ^ (-(1 + 2 * ε))) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    set x := (p : ℝ) ^ (-σ) with hxdef
    have hx : ∀ k : ℕ, ((p ^ k : ℕ) : ℝ) ^ (-σ) = x ^ k := fun k => by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast,
        ← Real.rpow_mul hp0.le, mul_comm]
    have hx0 : 0 ≤ x := Real.rpow_nonneg hp0.le _
    have hx2 : x ^ 2 = (p : ℝ) ^ (-(1 + 2 * ε)) := by
      rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      congr 1; simp only [σ]; push_cast; ring
    have hxsq : x ^ 2 ≤ 1 / 2 := by
      rw [hx2]
      calc (p : ℝ) ^ (-(1 + 2 * ε)) ≤ (p : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
        _ ≤ 1 / 2 := by gcongr
    have hx34 : x ≤ 3 / 4 := by nlinarith
    have hxlt : x < 1 := by linarith
    have hM1 : M p = |f' p - f p| * x := by
      have := mul_patternMoebiusAF_apply_prime_pow f' f hp 0
      rw [zero_add, pow_one, pow_zero, hf'.map_one, mul_one] at this
      have hx1 := hx 1
      rw [pow_one, pow_one] at hx1
      simp only [M, ArithmeticFunction.coe_mk, g, this, hx1]
    have hMk : ∀ m : ℕ, 1 ≤ m → M (p ^ (m + 1)) ≤ 2 * x ^ (m + 1) := fun m _ => by
      simp only [M, ArithmeticFunction.coe_mk]
      rw [mul_patternMoebiusAF_apply_prime_pow f' f hp m, hx (m + 1)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc |f' (p ^ (m + 1)) - f p * f' (p ^ m)|
          ≤ |f' (p ^ (m + 1))| + |f p| * |f' (p ^ m)| := by rw [← abs_mul]; exact abs_sub _ _
        _ ≤ 1 + 1 * 1 := add_le_add (hbd _) (mul_le_mul (hf p hp) (hbd _) (abs_nonneg _) zero_le_one)
        _ = 2 := by norm_num
    have hgeo := hasSum_geometric_of_lt_one hx0 hxlt
    set μk : ℕ → ℝ := fun k => (if k = 0 then (1 : ℝ) else 0) +
      (if k = 1 then |f' p - f p| * x else 0) + 2 * x ^ k -
      (if k = 0 then (2 : ℝ) else 0) - (if k = 1 then 2 * x else 0)
    have hmaj : HasSum μk (1 + |f' p - f p| * x + 2 * (1 - x)⁻¹ - 2 - 2 * x) :=
      ((((hasSum_ite_eq 0 (1 : ℝ)).add (hasSum_ite_eq 1 (|f' p - f p| * x))).add
        (hgeo.mul_left 2)).sub (hasSum_ite_eq 0 (2 : ℝ))).sub (hasSum_ite_eq 1 (2 * x))
    have hbound : ∀ k : ℕ, M (p ^ k) ≤ μk k := fun k => by
      rcases k with _ | _ | m
      · simp [M, μk, hg.map_one]
      · simp [zero_add, pow_one, hM1, μk]
      · have hm := hMk (m + 1) (by omega)
        simp only [μk, if_neg (by omega : m + 2 ≠ 0), if_neg (by omega : m + 2 ≠ 1)]
        linarith
    have hsumM : Summable (fun k : ℕ => M (p ^ k)) :=
      hmaj.summable.of_nonneg_of_le (fun k => hM0 _) hbound
    refine ⟨hsumM, ?_⟩
    have hle := hsumM.tsum_le_tsum hbound hmaj.summable
    rw [hmaj.tsum_eq] at hle
    refine hle.trans ?_
    have htail : 2 * (1 - x)⁻¹ - 2 - 2 * x ≤ 8 * x ^ 2 := by
      have h1x : 0 < 1 - x := by linarith
      rw [show 2 * (1 - x)⁻¹ - 2 - 2 * x = (2 - 2 * (1 + x) * (1 - x)) / (1 - x) by
        field_simp; ring, div_le_iff₀ h1x]
      nlinarith
    calc 1 + |f' p - f p| * x + 2 * (1 - x)⁻¹ - 2 - 2 * x
        ≤ (|f' p - f p| * x + 8 * x ^ 2) + 1 := by linarith
      _ ≤ Real.exp (|f' p - f p| * x + 8 * x ^ 2) := Real.add_one_le_exp _
      _ = Real.exp (|f' p - f p| * (p : ℝ) ^ (-σ) + 8 * (p : ℝ) ^ (-(1 + 2 * ε))) := by rw [hx2]
  set b : ℕ → ℝ := fun n =>
    (if n.Prime then |f' n - f n| * (n : ℝ) ^ (-σ) else 0) +
      (if n.Prime then 8 * (n : ℝ) ^ (-(1 + 2 * ε)) else 0)
  have hb0 : ∀ n, 0 ≤ b n := fun n => by simp only [b]; split_ifs <;> positivity
  have hb2 : Summable (fun n : ℕ => if n.Prime then 8 * (n : ℝ) ^ (-(1 + 2 * ε)) else 0) :=
    ((Real.summable_nat_rpow.mpr (by linarith : -(1 + 2 * ε) < -1)).mul_left 8).of_nonneg_of_le
      (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> [exact le_rfl; positivity])
  have hb : Summable b := hdiff.add hb2
  have hsum := RHTower.pm_summable_of_multiplicative_local_bound M hM hM0
    (fun hp => (hloc hp).1) b hb0 hb (fun {p} hp => by simpa only [b, if_pos hp] using (hloc hp).2)
  unfold CriticalWiener
  refine hsum.congr fun n => ?_
  simp only [M, ArithmeticFunction.coe_mk, dampedSignWeight]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (show -σ ≠ 0 by simp only [σ]; linarith),
      Real.zero_rpow (show -ε ≠ 0 by linarith)]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hn0.le _), mul_assoc, ← Real.rpow_add hn0]
    congr 2; simp only [σ]; ring

/-- **Prime-perturbation transfer of `ReceiverBounded`.** If `f : ℕ →*₀ ℝ` has `|f(p)| ≤ 1`,
`f' : ArithmeticFunction ℝ` is multiplicative with `|f'(n)| ≤ 1`, and
`∑_p |f'(p) − f(p)| p^{-(1/2 + ε)} < ∞` (`ε > 0`), then a bounded receiver for `f(d) d^{-ε}`
transfers to `f'(d) d^{-ε}`. -/
theorem receiverBounded_of_summable_prime_diff {f' : ArithmeticFunction ℝ}
    (hf' : f'.IsMultiplicative) (hbd : ∀ n, |f' n| ≤ 1) {f : ℕ →*₀ ℝ}
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (hdiff : Summable (fun p : ℕ => if p.Prime then |f' p - f p| * (p : ℝ) ^ (-(1 / 2 + ε)) else 0))
    (hR : ReceiverBounded (dampedSignWeight f ε)) :
    ReceiverBounded (dampedSignWeight ⇑f' ε) := by
  rw [dampedSignWeight_eq_dirichletConv_patternMoebiusAF f' f ε]
  exact receiverBounded_dirichletConv (criticalWiener_mul_patternMoebiusAF hf' hbd hf hε hdiff)
    (summable_abs_dampedSign_div_of_abs_le (abs_patternHom_le_one f hf) hε) hR

/-- **Prime-perturbation equivalence of `ReceiverBounded` for completely multiplicative patterns.**
If `f, f' : ℕ →*₀ ℝ` have `|f(p)| ≤ 1`, `|f'(p)| ≤ 1`, and
`∑_p |f'(p) − f(p)| p^{-(1/2 + ε)} < ∞` (`ε > 0`), then `f'(d) d^{-ε}` is paid iff `f(d) d^{-ε}`
is paid. -/
theorem receiverBounded_iff_of_summable_prime_diff {f f' : ℕ →*₀ ℝ}
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (hf' : ∀ p : ℕ, p.Prime → |f' p| ≤ 1) {ε : ℝ}
    (hε : 0 < ε)
    (hdiff : Summable (fun p : ℕ => if p.Prime then |f' p - f p| * (p : ℝ) ^ (-(1 / 2 + ε)) else 0)) :
    ReceiverBounded (dampedSignWeight f' ε) ↔ ReceiverBounded (dampedSignWeight f ε) := by
  have hdiff_symm : Summable (fun p : ℕ =>
      if p.Prime then |f p - f' p| * (p : ℝ) ^ (-(1 / 2 + ε)) else 0) :=
    hdiff.congr fun p => by rw [abs_sub_comm]
  exact ⟨fun hR => receiverBounded_of_summable_prime_diff (isMultiplicative_patternAF f)
      (abs_patternHom_le_one f hf) hf' hε hdiff_symm hR,
    fun hR => receiverBounded_of_summable_prime_diff (isMultiplicative_patternAF f')
      (abs_patternHom_le_one f' hf') hf hε hdiff hR⟩

/-- **Prime-perturbation transfer of uniform horizon-row boundedness.** Under the same prime
perturbation hypothesis, a uniform horizon-row bound transfers from `f(d) d^{-ε}` to
`f'(d) d^{-ε}`. -/
theorem horizonRows_bounded_of_summable_prime_diff {f' : ArithmeticFunction ℝ}
    (hf' : f'.IsMultiplicative) (hbd : ∀ n, |f' n| ≤ 1) {f : ℕ →*₀ ℝ}
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (hdiff : Summable (fun p : ℕ => if p.Prime then |f' p - f p| * (p : ℝ) ^ (-(1 / 2 + ε)) else 0))
    (hrow : ∃ E : ℝ, ∀ N T : ℕ,
      weightPronicEnergy (horizonRow (dampedSignWeight f ε) N)
        (horizonRowMean (dampedSignWeight f ε) N) T ≤ E) :
    ∃ E' : ℝ, ∀ N T : ℕ,
      weightPronicEnergy (horizonRow (dampedSignWeight ⇑f' ε) N)
        (horizonRowMean (dampedSignWeight ⇑f' ε) N) T ≤ E' := by
  rw [dampedSignWeight_eq_dirichletConv_patternMoebiusAF f' f ε]
  exact horizonRows_bounded_dirichletConv (criticalWiener_mul_patternMoebiusAF hf' hbd hf hε hdiff)
    (summable_abs_dampedSign_div_of_abs_le (abs_patternHom_le_one f hf) hε) hrow

/-- **Prime-varying amplitude phase law at half damping.** Let `a(p)` be a prime-varying amplitude
with `|a(p)| ≤ 1`, `|a₀| ≤ 1`, `t₀ ≠ 0`, and `∑_p |a(p) − a₀| p^{-1} < ∞`. Then the half-damped
weight of `f(p) = a(p) cos(t₀ log p + φ)` is paid iff `a₀ cos φ < 1` or `ζ(1/2 + i t₀) = 0`. -/
theorem receiverBounded_primeVaryingPhase_half_iff {a : ℕ → ℝ} {a₀ t₀ φ : ℝ}
    (ha : ∀ p : ℕ, p.Prime → |a p| ≤ 1) (ha₀ : |a₀| ≤ 1) (ht₀ : t₀ ≠ 0)
    (hdiff : Summable (fun p : ℕ => if p.Prime then |a p - a₀| * (p : ℝ) ^ (-1 : ℝ) else 0)) :
    ReceiverBounded (dampedSignWeight
      (primeValueHom fun p => a p * Real.cos (t₀ * Real.log p + φ)) (1 / 2)) ↔
        a₀ * Real.cos φ < 1 ∨ riemannZeta (1 / 2 + (t₀ : ℂ) * I) = 0 := by
  set f' : ℕ →*₀ ℝ := primeValueHom fun p => a p * Real.cos (t₀ * Real.log p + φ)
  have hf' : ∀ p : ℕ, p.Prime → |f' p| ≤ 1 := fun p hp => by
    rw [primeValueHom_prime _ hp, abs_mul]
    exact mul_le_one₀ (ha p hp) (abs_nonneg _) (Real.abs_cos_le_one _)
  have hf : ∀ p : ℕ, p.Prime → |phasePattern a₀ t₀ φ p| ≤ 1 :=
    fun p _ => abs_phasePattern_le ha₀ t₀ φ p
  have hdiff_pat : Summable (fun p : ℕ =>
      if p.Prime then |f' p - phasePattern a₀ t₀ φ p| * (p : ℝ) ^ (-(1 / 2 + (1 / 2 : ℝ)))
      else 0) := by
    refine hdiff.of_nonneg_of_le (fun p => by split_ifs <;> positivity) fun p => ?_
    split_ifs with hp
    · rw [show -(1 / 2 + (1 / 2 : ℝ)) = (-1 : ℝ) by norm_num, primeValueHom_prime _ hp,
        phasePattern_prime a₀ t₀ φ hp, ← sub_mul, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · exact le_rfl
  rw [receiverBounded_iff_of_summable_prime_diff hf hf' (by norm_num) hdiff_pat,
    show dampedSignWeight (phasePattern a₀ t₀ φ) (1 / 2) = phaseWeight a₀ t₀ φ from rfl,
    receiverBounded_phaseWeight_iff ha₀ ht₀]

/-- **Multi-frequency prime-varying amplitude phase law at half damping.** Let `a_k(p)` (`k ∈ K`) be
prime-varying amplitudes with `∑_{k ∈ K} |a_k(p)| ≤ 1` at all primes `p`, `∑_{k ∈ K} |a₀_k| ≤ 1`,
pairwise distinct positive frequencies `t_k > 0`, and `∑_p |a_k(p) − a₀_k| p^{-1} < ∞` for each
`k ∈ K`. Then the half-damped weight of `f'(p) = ∑_{k ∈ K} a_k(p) cos(t_k log p + φ_k)` is paid iff
`∀ k ∈ K, a₀_k cos φ_k < 1 ∨ ζ(1/2 + i t_k) = 0`. -/
theorem receiverBounded_primeVaryingMultiPhase_half_iff {ι : Type*} (K : Finset ι)
    {a : ι → ℕ → ℝ} {a₀ t φ : ι → ℝ}
    (ha : ∀ p : ℕ, p.Prime → ∑ k ∈ K, |a k p| ≤ 1)
    (ha₀ : ∑ k ∈ K, |a₀ k| ≤ 1) (ht : ∀ k ∈ K, 0 < t k) (hinj : Set.InjOn t (K : Set ι))
    (hdiff : ∀ k ∈ K,
      Summable (fun p : ℕ => if p.Prime then |a k p - a₀ k| * (p : ℝ) ^ (-1 : ℝ) else 0)) :
    ReceiverBounded (dampedSignWeight
      (primeValueHom fun p => ∑ k ∈ K, a k p * Real.cos (t k * Real.log p + φ k)) (1 / 2)) ↔
        ∀ k ∈ K, a₀ k * Real.cos (φ k) < 1 ∨ riemannZeta (1 / 2 + (t k : ℂ) * I) = 0 := by
  set f' : ℕ →*₀ ℝ := primeValueHom fun p => ∑ k ∈ K, a k p * Real.cos (t k * Real.log p + φ k)
  have hf' : ∀ p : ℕ, p.Prime → |f' p| ≤ 1 := fun p hp => by
    rw [primeValueHom_prime _ hp]
    calc |∑ k ∈ K, a k p * Real.cos (t k * Real.log p + φ k)|
        ≤ ∑ k ∈ K, |a k p * Real.cos (t k * Real.log p + φ k)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ K, |a k p| := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      _ ≤ 1 := ha p hp
  have hf : ∀ p : ℕ, p.Prime → |multiPhasePattern K a₀ t φ p| ≤ 1 :=
    fun p _ => abs_multiPhasePattern_le_of_sum_abs_le_one ha₀ t φ p
  have hsum_diff : Summable (fun p : ℕ => ∑ k ∈ K,
      (if p.Prime then |a k p - a₀ k| * (p : ℝ) ^ (-1 : ℝ) else 0)) :=
    summable_sum fun k hk => hdiff k hk
  have hdiff_pat : Summable (fun p : ℕ =>
      if p.Prime then |f' p - multiPhasePattern K a₀ t φ p| * (p : ℝ) ^ (-(1 / 2 + (1 / 2 : ℝ)))
      else 0) := by
    refine hsum_diff.of_nonneg_of_le (fun p => by split_ifs <;> positivity) fun p => ?_
    split_ifs with hp
    · rw [show -(1 / 2 + (1 / 2 : ℝ)) = (-1 : ℝ) by norm_num, primeValueHom_prime _ hp,
        multiPhasePattern_prime K a₀ t φ hp, ← Finset.sum_sub_distrib, ← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [← sub_mul, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · simp
  rw [receiverBounded_iff_of_summable_prime_diff hf hf' (by norm_num) hdiff_pat,
    show dampedSignWeight (multiPhasePattern K a₀ t φ) (1 / 2) = multiPhaseWeight K a₀ t φ from rfl,
    receiverBounded_multiPhaseWeight_iff K ha₀ ht hinj]

/-- **Below half damping, a paid prime-varying multi-frequency pattern has `a₀_k cos φ_k = 0` at
every mode.** -/
theorem cos_coeff_eq_zero_of_receiverBounded_primeVaryingMultiPhase_damped {ι : Type*}
    (K : Finset ι) {a : ι → ℕ → ℝ} {a₀ t φ : ι → ℝ}
    (ha : ∀ p : ℕ, p.Prime → ∑ k ∈ K, |a k p| ≤ 1)
    (ha₀ : ∑ k ∈ K, |a₀ k| ≤ 1) (ht : ∀ k ∈ K, 0 < t k) (hinj : Set.InjOn t (K : Set ι))
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (hdiff : ∀ k ∈ K,
      Summable (fun p : ℕ => if p.Prime then |a k p - a₀ k| * (p : ℝ) ^ (-(1 / 2 + ε)) else 0))
    (hR : ReceiverBounded (dampedSignWeight
      (primeValueHom fun p => ∑ k ∈ K, a k p * Real.cos (t k * Real.log p + φ k)) ε)) :
    ∀ k ∈ K, a₀ k * Real.cos (φ k) = 0 := by
  set f' : ℕ →*₀ ℝ := primeValueHom fun p => ∑ k ∈ K, a k p * Real.cos (t k * Real.log p + φ k)
  have hf' : ∀ p : ℕ, p.Prime → |f' p| ≤ 1 := fun p hp => by
    rw [primeValueHom_prime _ hp]
    calc |∑ k ∈ K, a k p * Real.cos (t k * Real.log p + φ k)|
        ≤ ∑ k ∈ K, |a k p * Real.cos (t k * Real.log p + φ k)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ K, |a k p| := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      _ ≤ 1 := ha p hp
  have hf : ∀ p : ℕ, p.Prime → |multiPhasePattern K a₀ t φ p| ≤ 1 :=
    fun p _ => abs_multiPhasePattern_le_of_sum_abs_le_one ha₀ t φ p
  have hak₀ : ∀ k ∈ K, |a₀ k| ≤ 1 := fun k hk =>
    (Finset.single_le_sum (fun j _ => abs_nonneg (a₀ j)) hk).trans ha₀
  have hsum_diff : Summable (fun p : ℕ => ∑ k ∈ K,
      (if p.Prime then |a k p - a₀ k| * (p : ℝ) ^ (-(1 / 2 + ε)) else 0)) :=
    summable_sum fun k hk => hdiff k hk
  have hdiff_pat : Summable (fun p : ℕ =>
      if p.Prime then |f' p - multiPhasePattern K a₀ t φ p| * (p : ℝ) ^ (-(1 / 2 + ε))
      else 0) := by
    refine hsum_diff.of_nonneg_of_le (fun p => by split_ifs <;> positivity) fun p => ?_
    split_ifs with hp
    · rw [primeValueHom_prime _ hp, multiPhasePattern_prime K a₀ t φ hp,
        ← Finset.sum_sub_distrib, ← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [← sub_mul, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · simp
  have hR₀ := (receiverBounded_iff_of_summable_prime_diff hf hf' hε hdiff_pat).mp hR
  exact cos_coeff_eq_zero_of_receiverBounded_multiPhase_damped K hf hak₀ ht hinj hε hε2 hR₀

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics

