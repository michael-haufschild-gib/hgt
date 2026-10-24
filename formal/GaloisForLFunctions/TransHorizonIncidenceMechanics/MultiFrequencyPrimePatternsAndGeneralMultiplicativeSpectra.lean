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
   (`exists_lineEnergy_le_of_majorant_finset`, `receiverBounded_pattern_half_of_finset_bounds`,
   `exists_prod_rpow_neg_add_one_le_sum`):
   Dominating `‖F(w)‖` on `1 < Re w ≤ 2` by `A (1 + ∑_{k ∈ I} |Im w − t_k|^{-b_k})` with `2 b_k < 1`
   on `(0, T]` and by `B₁ (Im w)^{1/4}` above `T` pays the half-damped receiver. For pairwise
   distinct frequencies `t_k`, the product `∏_{k ∈ I} (|y − t_k|^{-b_k} + 1)` collapses to a linear
   combination `C (1 + ∑_{k ∈ I} |y − t_k|^{-b_k})` because `|t_j − t_k| ≤ |y − t_j| + |y − t_k|`
   prevents simultaneous proximity to two distinct heights.

3. **The complete phase diagram of multi-frequency prime patterns**
   (`receiverBounded_multiPhaseWeight_of_forall_lt_one`,
   `not_receiverBounded_multiPhaseWeight_of_ge_one`, `receiverBounded_multiPhaseWeight_iff`,
   `receiverBounded_multiPhaseWeight_of_two_active`,
   `cos_coeff_eq_zero_of_receiverBounded_multiPhase_damped`):
   For `f(p) = ∑_{k ∈ I} a_k cos(t_k log p + φ_k)` with pairwise distinct positive frequencies
   `t_k > 0`:
   - if `|f(p)| ≤ 1`, `|a_k| ≤ 1`, and `a_k cos φ_k < 1` for all `k ∈ I`, the half-damped weight is
     paid;
   - if `a_{k₀} cos φ_{k₀} ≥ 1` for some `k₀ ∈ I` and `ζ(1/2 + i t_{k₀}) ≠ 0`, the half-damped
     weight is unpaid;
   - under the amplitude budget `∑_{k ∈ I} |a_k| ≤ 1`, `multiPhaseWeight I a t φ` is paid if and
     only if `∀ k ∈ I, a_k cos φ_k < 1 ∨ ζ(1/2 + i t_k) = 0`; in particular, sharing the budget
     across two or more active frequencies (`a_{k₁} ≠ 0, a_{k₂} ≠ 0`) always pays the half-damped
     receiver unconditionally;
   - below half damping (`0 < ε < 1/2`), payment forces `a_k cos φ_k = 0` at every frequency `k ∈ I`.

4. **Prime-varying amplitudes and critical Wiener prime-perturbation invariance**
   (`criticalWiener_primePerturbationKernel`, `receiverBounded_pattern_iff_of_summable_prime_diff`,
   `horizonRows_bounded_pattern_iff_of_summable_prime_diff`,
   `receiverBounded_primeVaryingMultiPhaseWeight_iff`):
   For any two completely multiplicative patterns `f, f' : ℕ →*₀ ℝ` with `|f(p)| ≤ 1` and
   `|f'(p)| ≤ 1`, the perturbation kernel `g = f' ⋆ μf` satisfies
   `g(p^{m+1}) = f'(p)^m (f'(p) − f(p))` with no unimodularity assumption. Whenever
   `∑_p |f'(p) − f(p)| p^{-(1/2 + ε)} < ∞` (`ε > 0`), `g d^{-ε}` lies in `CriticalWiener`, so both
   full-receiver payment and uniform horizon-row payment are invariant between `f` and `f'`.
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
    ring
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
  have hc_damped : DampedClass 1 (1 / 2) c := by
    -- Notice `integrable_lineEnergy` is not even needed here: `IntegrableOn.of_bound` or `lineIntegrand_even`
    sorry
  sorry
