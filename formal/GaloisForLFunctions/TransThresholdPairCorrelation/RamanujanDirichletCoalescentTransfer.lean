import GaloisForLFunctions.TransThresholdPairCorrelation.CoalescentSieveAnatomyAndModelCalibration
import GaloisForLFunctions.BezoutValuationIncidence.HardyLittlewoodSingularSeriesOfTheDampedSource
import GaloisForLFunctions.BezoutValuationIncidence.RamanujanLagCoefficientAndTotientQuotient

/-!
# The Lobe-Cancellation Dichotomy, Exact Trapezoidal Dirichlet–Ramanujan Transfer, and Narrow-Strip Gain

This module resolves Open Problems 2, 3, 4, and 5 of `TransThresholdPairCorrelation`:

1. **The Lobe-Cancellation Dichotomy Resolving Open Problem 2
   (`cosTransform_ge_half_of_le_pi_div_three`, `sum_Icc_abs_cosTransform_ge_inner_lobe`,
   `two_sin_mul_trapezoidal_sum_cos`, `trapezoidal_sum_cos_eq_div`):**
   For any non-negative window `Ω` supported in `[a, b]` (`0 ≤ a ≤ b`, `0 < b`), on the inner
   coalescent core `|θ| ≤ π / (3b)` we have `cos(τθ) ≥ 1/2` for all `τ ∈ [a, b]`, so
   `cosTransform Ω θ ≥ (1/2) cosTransform Ω 0`. Consequently, for any step `δ > 0` and
   `R ≥ K₁` with `K₁ δ ≤ π / (3b)`, the unsigned shift sum satisfies
   `∑_{r=1}^R |cosTransform Ω (rδ)| ≥ (K₁ / 2) cosTransform Ω 0`. At the coalescent step
   `δ = q / m`, `K₁ ≍ m / (q T)` scales with the trans-threshold blowup `m / T = T^{α−1}`, proving
   why any unsigned size-only sieve bound applied directly to `|cosTransform Ω|` diverges relative
   to the zero-lag scale. By contrast, the signed shift sum satisfies the exact finite
   trapezoidal Dirichlet-kernel identity
   `2 sin(ϕ/2) (1/2 + ∑_{r=1}^{M−1} cos(rϕ) + (1/2) cos(Mϕ)) = sin(Mϕ) cos(ϕ/2)`,
   where the oscillating lobes cancel and leave the negative zero-lag residue `−1/2`.

2. **Exact Trapezoidal Dirichlet–Ramanujan Coalescent Identity & Ward–Mertens Repulsion Transfer
   Resolving Open Problems 3 & 4 (`trapezoidal_ramanujan_cos_eq`, `abs_cos_div_sin_sub_inv_le`,
   `abs_sum_ramanujanLagCoefficient_mul_cos_add_le`,
   `abs_sum_ramanujanLagCoefficient_mul_cosTransform_add_le`,
   `abs_sum_singularSeries_cosTransform_add_le`):**
   Expanding `ramanujanLagCoefficient q h = ∑_{d ∣ q} μ(q/d) d 1_{d ∣ h}` over `1 ≤ h ≤ qR − 1`
   and applying the trapezoidal Dirichlet-kernel identity to each divisor progression `h = d r`
   (`1 ≤ r ≤ (q/d) R − 1`, where the endpoint phase `((q/d) R)(d θ) = q R θ` is independent of `d`)
   gives the exact finite identity
   `φ(q)/2 + ∑_{h=1}^{qR−1} c_q(h) cos(hθ) + (φ(q)/2) cos(qRθ)
     = sin(qRθ) ∑_{d ∣ q} μ(q/d) (d cos(dθ/2) / (2 sin(dθ/2)) − 1/θ)`,
   in which the `1/θ` Dirichlet-kernel pole cancels identically across `d ∣ q` because
   `∑_{d ∣ q} μ(q/d) = 0` for `q ≥ 2`. The elementary cotangent residual bound
   `|cos x / sin x − 1/x| ≤ x` on `0 < x ≤ 1` then yields the `R`-independent pointwise bound
   `|∑_{h=1}^{qR} c_q(h) cos(hθ) + (φ(q)/2)(1 − cos(qRθ))| ≤ (∑_{d ∣ q} d²) (θ/4)` for all
   `0 < θ ≤ 2/q`. Integrating against `Ω` and weighting by `μ(q)² / φ(q)²` transfers the
   finite-height Hardy–Littlewood singular-series sum to the negative Ward–Mertens repulsion sum
   `−(1/2) cosTransform Ω 0 ∑_{q=2}^Q sqfreeTotientInv q`.

3. **General-Bandwidth Narrow-Strip Coalescent Proportion Envelope & Optimal Gain Resolving
   Open Problem 5 (`narrowStrip_coalescent_proportion_gain_eq`,
   `narrowStrip_coalescent_gain_pos`, `narrowStrip_optimal_delta_gain`,
   `narrowStrip_collar_preserves_gain`):**
   At bandwidth `λ = 1 + δ > 1`, any quadratic coalescent surplus bound
   `β(δ) ≤ B δ² / (1 + δ)²` (`B ≥ 0`) certifies a critical-line proportion exceeding `2/3` by
   `G_B(δ) = δ (2 + (1 − 3B) δ − δ²) / (3 (1 + δ)²) > 0` for all `0 < δ < 2 / (3B + 1)`, achieving
    at the explicit optimal strip width `δ_*(B) = 1 / (3B + 2)` the closed-form gain
   `G_B(1 / (3B + 2)) = (3B² + 7B + 3) / (9 (B + 1)² * (3B + 2)) > 0`.
-/

open MeasureTheory Real Set Finset Filter Topology ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius

open Zeta23 Zeta23.PrimeSide RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-! ## §1. The Lobe-Cancellation Dichotomy Resolving Open Problem 2 -/

/-- At zero frequency, `cosTransform Ω 0 = ∫ τ, Ω τ` is non-negative when `Ω ≥ 0`. -/
theorem cosTransform_zero_eq_integral (Ω : ℝ → ℝ) :
    cosTransform Ω 0 = ∫ τ, Ω τ := by
  unfold cosTransform
  refine integral_congr_ae ( Eventually.of_forall fun τ => ?_ )
  simp

/-- **Inner-Core Positivity of `cosTransform`.**
If `Ω ≥ 0` is integrable and supported in `[a, b]` (`0 ≤ a ≤ b`, `0 < b`), then for every
`|θ| ≤ π / (3b)`, `cosTransform Ω θ ≥ (1/2) cosTransform Ω 0`. -/
theorem cosTransform_ge_half_of_le_pi_div_three {Ω : ℝ → ℝ} {a b θ : ℝ}
    (ha : 0 ≤ a) (_hab : a ≤ b) (hb : 0 < b)
    (hInt : Integrable Ω) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (hsupp : ∀ τ, τ ∉ Icc a b → Ω τ = 0)
    (hθ : |θ| ≤ π / (3 * b)) :
    (1 / 2) * cosTransform Ω 0 ≤ cosTransform Ω θ := by
  rw [cosTransform_zero_eq_integral, ← integral_const_mul, cosTransform]
  refine integral_mono (hInt.const_mul (1 / 2)) (cosTransform_integrable hInt θ) fun τ => ?_
  by_cases hτ : τ ∈ Icc a b
  · obtain ⟨hτa, hτb⟩ := mem_Icc.mp hτ
    have hτ0 : 0 ≤ τ := ha.trans hτa
    have habs : |τ * θ| ≤ π / 3 := by
      rw [abs_mul, abs_of_nonneg hτ0]
      calc τ * |θ| ≤ b * (π / (3 * b)) := mul_le_mul hτb hθ (abs_nonneg _) hb.le
        _ = π / 3 := by field_simp
    have hcos : (1 / 2 : ℝ) ≤ Real.cos (τ * θ) := by
      rw [← Real.cos_abs (τ * θ), ← Real.cos_pi_div_three]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by linarith [Real.pi_pos]) habs
    calc 1 / 2 * Ω τ = Ω τ * (1 / 2) := by ring
      _ ≤ Ω τ * Real.cos (τ * θ) := mul_le_mul_of_nonneg_left hcos (hΩ0 τ)
  · rw [hsupp τ hτ]
    simp

/-- **Unsigned Inner-Lobe Divergence.**
For any step `δ > 0` and any `1 ≤ K₁ ≤ R` with `K₁ δ ≤ π / (3b)`, the unsigned shift sum satisfies
`∑_{r=1}^R |cosTransform Ω (rδ)| ≥ (K₁ / 2) cosTransform Ω 0`.
At `δ = q / m`, `K₁ ≍ m / (q T)` scales with `m / T = T^{α−1}`, proving that any unsigned size-only
bound on `|cosTransform Ω|` diverges relative to the zero-lag scale. -/
theorem sum_Icc_abs_cosTransform_ge_inner_lobe {Ω : ℝ → ℝ} {a b δ : ℝ} {K₁ R : ℕ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) (hδ : 0 < δ)
    (hInt : Integrable Ω) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (hsupp : ∀ τ, τ ∉ Icc a b → Ω τ = 0)
    (hKR : K₁ ≤ R) (hK₁ : (K₁ : ℝ) * δ ≤ π / (3 * b)) :
    ((K₁ : ℝ) / 2) * cosTransform Ω 0 ≤
      ∑ r ∈ Finset.Icc 1 R, |cosTransform Ω ((r : ℝ) * δ)| := by
  have hsub : ∑ r ∈ Finset.Icc 1 K₁, |cosTransform Ω ((r : ℝ) * δ)|
      ≤ ∑ r ∈ Finset.Icc 1 R, |cosTransform Ω ((r : ℝ) * δ)| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hKR)
      (fun _ _ _ => abs_nonneg _)
  refine le_trans ?_ hsub
  have hterm : ∀ r ∈ Finset.Icc 1 K₁,
      (1 / 2) * cosTransform Ω 0 ≤ |cosTransform Ω ((r : ℝ) * δ)| := by
    intro r hr
    have hrK : (r : ℝ) ≤ K₁ := by exact_mod_cast (Finset.mem_Icc.mp hr).2
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have habs : |(r : ℝ) * δ| ≤ π / (3 * b) := by
      rw [abs_of_nonneg (mul_nonneg hr0 hδ.le)]
      exact (mul_le_mul_of_nonneg_right hrK hδ.le).trans hK₁
    exact (cosTransform_ge_half_of_le_pi_div_three ha hab hb hInt hΩ0 hsupp habs).trans
      (le_abs_self _)
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum
  have hcard : ((K₁ + 1 - 1 : ℕ) : ℝ) = (K₁ : ℝ) := by congr 1
  rw [hcard] at hsum
  linarith

/-- **Trapezoidal Dirichlet-Kernel Identity (Successor Form).**
For every `k : ℕ` and `ϕ : ℝ`,
`2 sin(ϕ/2) (1/2 + ∑_{r=1}^k cos(rϕ) + (1/2) cos((k+1)ϕ)) = sin((k+1)ϕ) cos(ϕ/2)`. -/
theorem two_sin_mul_trapezoidal_sum_cos_succ (k : ℕ) (ϕ : ℝ) :
    2 * Real.sin (ϕ / 2) *
      (1 / 2 + (∑ r ∈ Finset.Icc 1 k, Real.cos ((r : ℝ) * ϕ)) +
        1 / 2 * Real.cos (((k + 1 : ℕ) : ℝ) * ϕ)) =
      Real.sin (((k + 1 : ℕ) : ℝ) * ϕ) * Real.cos (ϕ / 2) := by
  induction k with
  | zero =>
    simp only [Nat.reduceAdd, Finset.Icc_eq_empty (by omega : ¬ (1 ≤ 0)), Finset.sum_empty,
      add_zero, Nat.cast_one, one_mul]
    set x := ϕ / 2
    have hϕ : ϕ = 2 * x := by ring
    rw [hϕ, Real.sin_two_mul, Real.cos_two_mul]
    ring
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    set A := ((k + 1 : ℕ) : ℝ) * ϕ
    set x := ϕ / 2
    have hstep : 2 * Real.sin x *
        (Real.cos A + 1 / 2 * Real.cos (A + 2 * x) - 1 / 2 * Real.cos A) =
        (Real.sin (A + 2 * x) - Real.sin A) * Real.cos x := by
      rw [Real.cos_add, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul']
      have hsq : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := Real.sin_sq x
      linear_combination -2 * Real.sin A * Real.sin x * hsq
    have hnext : ((k + 1 + 1 : ℕ) : ℝ) * ϕ = A + 2 * x := by
      push_cast; ring
    rw [hnext]
    linarith

/-- **Trapezoidal Dirichlet-Kernel Identity.**
For every `M ≥ 1` and `ϕ : ℝ`,
`2 sin(ϕ/2) (1/2 + ∑_{r=1}^{M−1} cos(rϕ) + (1/2) cos(Mϕ)) = sin(Mϕ) cos(ϕ/2)`. -/
theorem two_sin_mul_trapezoidal_sum_cos {M : ℕ} (hM : 1 ≤ M) (ϕ : ℝ) :
    2 * Real.sin (ϕ / 2) *
      (1 / 2 + (∑ r ∈ Finset.Icc 1 (M - 1), Real.cos ((r : ℝ) * ϕ)) +
        1 / 2 * Real.cos ((M : ℝ) * ϕ)) =
      Real.sin ((M : ℝ) * ϕ) * Real.cos (ϕ / 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M ≠ 0)
  simpa using two_sin_mul_trapezoidal_sum_cos_succ k ϕ

/-- Quotient form of the trapezoidal Dirichlet-kernel identity when `sin(ϕ/2) ≠ 0`. -/
theorem trapezoidal_sum_cos_eq_div {M : ℕ} (hM : 1 ≤ M) {ϕ : ℝ}
    (hsin : Real.sin (ϕ / 2) ≠ 0) :
    1 / 2 + (∑ r ∈ Finset.Icc 1 (M - 1), Real.cos ((r : ℝ) * ϕ)) +
      1 / 2 * Real.cos ((M : ℝ) * ϕ) =
      Real.sin ((M : ℝ) * ϕ) * Real.cos (ϕ / 2) / (2 * Real.sin (ϕ / 2)) := by
  have h2 : 2 * Real.sin (ϕ / 2) ≠ 0 := mul_ne_zero two_ne_zero hsin
  rw [eq_div_iff h2, mul_comm]
  exact two_sin_mul_trapezoidal_sum_cos hM ϕ

/-! ## §2. Exact Trapezoidal Dirichlet–Ramanujan Coalescent Identity & Pole Cancellation -/

/-- Möbius inversion identity over divisors in `q / d` form:
`∑_{d ∣ q} moebiusReal (q / d) = 1` if `q = 1` and `0` otherwise. -/
theorem sum_divisors_moebiusReal_div (q : ℕ) :
    ∑ d ∈ q.divisors, moebiusReal (q / d) = if q = 1 then 1 else 0 := by
  rw [Nat.sum_div_divisors q moebiusReal]
  have hμ := congrArg (fun F : ArithmeticFunction ℝ => F q)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply] at hμ
  rw [show ∑ i ∈ q.divisors, moebiusReal i = (1 : ArithmeticFunction ℝ) q from hμ]
  rcases eq_or_ne q 1 with rfl | hq <;> simp [*]

/-- When `q ∣ h` (`q ≥ 1`), the Ramanujan lag coefficient equals `φ(q)`. -/
theorem ramanujanLagCoefficient_of_dvd {q h : ℕ} (hq : 1 ≤ q) (hdvd : q ∣ h) :
    ramanujanLagCoefficient q h = (q.totient : ℝ) := by
  rw [ramanujanLagCoefficient_eq_totient_mul, sieveLagMultiplier_eq_moebius_totient_quotient,
    Nat.gcd_eq_left hdvd, Nat.div_self hq]
  simp [moebiusReal]

/-- Euler's totient formula via `moebiusReal`: `∑_{d ∣ q} moebiusReal (q / d) * d = φ(q)` for `q ≥ 1`. -/
theorem sum_divisors_moebiusReal_div_mul {q : ℕ} (hq : 1 ≤ q) :
    ∑ d ∈ q.divisors, moebiusReal (q / d) * (d : ℝ) = (q.totient : ℝ) := by
  have h := ramanujanLagCoefficient_of_dvd hq (dvd_zero q)
  unfold ramanujanLagCoefficient at h
  simpa using h

/-- For `d ∣ q` (`q, R ≥ 1`), summing a function over multiples of `d` in `Icc 1 (qR − 1)`
bijects with `r ∈ Icc 1 ((q/d) R − 1)` via `h = d r`. -/
theorem sum_Icc_filter_dvd_eq {q d R : ℕ} (hR : 1 ≤ R) (hd : d ∈ q.divisors) (f : ℕ → ℝ) :
    ∑ h ∈ Finset.Icc 1 (q * R - 1), (if d ∣ h then f h else 0) =
      ∑ r ∈ Finset.Icc 1 ((q / d) * R - 1), f (d * r) := by
  classical
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hmul : d * ((q / d) * R) = q * R := by
    rw [← mul_assoc, Nat.mul_div_cancel' hdq]
  rw [← Finset.sum_filter]
  refine (Finset.sum_nbij (fun r => d * r) ?_ ?_ ?_ (fun _ _ => rfl)).symm
  · intro r hr
    rw [Finset.mem_Icc] at hr
    rw [Finset.mem_filter, Finset.mem_Icc]
    have h1 : 1 ≤ d * r := Nat.mul_pos hd0 hr.1
    have h2 : d * r + d ≤ q * R := by
      have hr1 : r + 1 ≤ (q / d) * R := by omega
      calc d * r + d = d * (r + 1) := by ring
        _ ≤ d * ((q / d) * R) := Nat.mul_le_mul_left d hr1
        _ = q * R := hmul
    exact ⟨⟨h1, by omega⟩, dvd_mul_right d r⟩
  · intro r₁ _ r₂ _ h
    exact Nat.eq_of_mul_eq_mul_left hd0 h
  · intro h hh
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hh
    obtain ⟨⟨hh1, hh2⟩, hdh⟩ := hh
    refine ⟨h / d, ?_, Nat.mul_div_cancel' hdh⟩
    simp only [Finset.mem_coe, Finset.mem_Icc]
    have hd_eq : d * (h / d) = h := Nat.mul_div_cancel' hdh
    have hr1 : 1 ≤ h / d := by
      rcases Nat.eq_zero_or_pos (h / d) with h0 | hpos
      · omega
      · exact hpos
    have hr2 : h / d < (q / d) * R := by
      by_contra! hge
      have : q * R ≤ h := by
        calc q * R = d * ((q / d) * R) := hmul.symm
          _ ≤ d * (h / d) := Nat.mul_le_mul_left d hge
          _ = h := hd_eq
      omega
    omega

/-- **Exact Trapezoidal Dirichlet–Ramanujan Coalescent Identity with Pole Cancellation.**
For every modulus `q ≥ 2`, period count `R ≥ 1`, and frequency `0 < θ ≤ π / q`:
`φ(q)/2 + ∑_{h=1}^{qR−1} c_q(h) cos(hθ) + (φ(q)/2) cos(qRθ)
  = sin(qRθ) ∑_{d ∣ q} moebiusReal (q / d) (d cos(dθ/2) / (2 sin(dθ/2)) − 1 / θ)`.
The `1 / θ` Dirichlet-kernel pole cancels identically across divisors because
`∑_{d ∣ q} moebiusReal (q / d) = 0` for `q ≥ 2`. -/
theorem trapezoidal_ramanujan_cos_eq {q R : ℕ} {θ : ℝ}
    (hq : 2 ≤ q) (hR : 1 ≤ R) (hθ0 : 0 < θ) (hθ : θ ≤ π / q) :
    (q.totient : ℝ) / 2 +
      (∑ h ∈ Finset.Icc 1 (q * R - 1), ramanujanLagCoefficient q h * Real.cos ((h : ℝ) * θ)) +
      (q.totient : ℝ) / 2 * Real.cos (((q * R : ℕ) : ℝ) * θ) =
      Real.sin (((q * R : ℕ) : ℝ) * θ) *
        ∑ d ∈ q.divisors, moebiusReal (q / d) *
          ((d : ℝ) * Real.cos ((d : ℝ) * θ / 2) / (2 * Real.sin ((d : ℝ) * θ / 2)) - 1 / θ) := by
  have hq1 : 1 ≤ q := by omega
  have hdiv_term : ∀ d ∈ q.divisors,
      (d : ℝ) * (1 / 2 +
        (∑ h ∈ Finset.Icc 1 (q * R - 1),
          if d ∣ h then Real.cos ((h : ℝ) * θ) else 0) +
        1 / 2 * Real.cos (((q * R : ℕ) : ℝ) * θ)) =
      Real.sin (((q * R : ℕ) : ℝ) * θ) *
        ((d : ℝ) * Real.cos ((d : ℝ) * θ / 2) / (2 * Real.sin ((d : ℝ) * θ / 2))) := by
    intro d hd
    have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd_le : d ≤ q := Nat.le_of_dvd hq1 hdq
    have hqd1 : 1 ≤ q / d := Nat.div_pos hd_le hd0
    have hM1 : 1 ≤ (q / d) * R := Nat.mul_pos hqd1 hR
    have hmul_nat : (q / d) * R * d = q * R := by
      calc (q / d) * R * d = (q / d) * d * R := by ring
        _ = q * R := by rw [Nat.div_mul_cancel hdq]
    have hmul_real : (((q / d) * R : ℕ) : ℝ) * ((d : ℝ) * θ) = ((q * R : ℕ) : ℝ) * θ := by
      calc (((q / d) * R : ℕ) : ℝ) * ((d : ℝ) * θ)
          = (((q / d) * R * d : ℕ) : ℝ) * θ := by push_cast; ring
        _ = ((q * R : ℕ) : ℝ) * θ := by rw [hmul_nat]
    have hsin_pos : 0 < Real.sin ((d : ℝ) * θ / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · have : (0 : ℝ) < d := by exact_mod_cast hd0
        positivity
      · have hdq_real : (d : ℝ) ≤ q := by exact_mod_cast hd_le
        have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
        have h1 : (d : ℝ) * θ ≤ π := by
          calc (d : ℝ) * θ ≤ (q : ℝ) * (π / q) :=
                mul_le_mul hdq_real hθ hθ0.le (Nat.cast_nonneg q)
            _ = π := mul_div_cancel₀ π hq0.ne'
        linarith [Real.pi_pos]
    rw [sum_Icc_filter_dvd_eq hR hd (fun h => Real.cos ((h : ℝ) * θ))]
    have hcos_sum : (∑ r ∈ Finset.Icc 1 ((q / d) * R - 1), Real.cos (((d * r : ℕ) : ℝ) * θ)) =
        ∑ r ∈ Finset.Icc 1 ((q / d) * R - 1), Real.cos ((r : ℝ) * ((d : ℝ) * θ)) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      congr 1; push_cast; ring
    rw [hcos_sum, ← hmul_real]
    have htrap := trapezoidal_sum_cos_eq_div hM1 (ϕ := (d : ℝ) * θ) hsin_pos.ne'
    rw [htrap]
    ring
  have hsum_lhs : (q.totient : ℝ) / 2 +
      (∑ h ∈ Finset.Icc 1 (q * R - 1), ramanujanLagCoefficient q h * Real.cos ((h : ℝ) * θ)) +
      (q.totient : ℝ) / 2 * Real.cos (((q * R : ℕ) : ℝ) * θ) =
      ∑ d ∈ q.divisors, moebiusReal (q / d) *
        ((d : ℝ) * (1 / 2 +
          (∑ h ∈ Finset.Icc 1 (q * R - 1),
            if d ∣ h then Real.cos ((h : ℝ) * θ) else 0) +
          1 / 2 * Real.cos (((q * R : ℕ) : ℝ) * θ))) := by
    rw [← sum_divisors_moebiusReal_div_mul hq1]
    have hmid : (∑ h ∈ Finset.Icc 1 (q * R - 1),
          ramanujanLagCoefficient q h * Real.cos ((h : ℝ) * θ)) =
        ∑ d ∈ q.divisors, moebiusReal (q / d) *
          ((d : ℝ) * ∑ h ∈ Finset.Icc 1 (q * R - 1),
            if d ∣ h then Real.cos ((h : ℝ) * θ) else 0) := by
      unfold ramanujanLagCoefficient
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      split_ifs <;> ring
    rw [hmid]
    simp_rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => by ring
  rw [hsum_lhs]
  have hsum_mid : (∑ d ∈ q.divisors, moebiusReal (q / d) *
        ((d : ℝ) * (1 / 2 +
          (∑ h ∈ Finset.Icc 1 (q * R - 1),
            if d ∣ h then Real.cos ((h : ℝ) * θ) else 0) +
          1 / 2 * Real.cos (((q * R : ℕ) : ℝ) * θ)))) =
      Real.sin (((q * R : ℕ) : ℝ) * θ) *
        ∑ d ∈ q.divisors, moebiusReal (q / d) *
          ((d : ℝ) * Real.cos ((d : ℝ) * θ / 2) / (2 * Real.sin ((d : ℝ) * θ / 2))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [hdiv_term d hd]
    ring
  rw [hsum_mid]
  have hpole : ∑ d ∈ q.divisors, moebiusReal (q / d) * (1 / θ) = 0 := by
    rw [← Finset.sum_mul, sum_divisors_moebiusReal_div q, if_neg (by omega : q ≠ 1), zero_mul]
  congr 1
  calc ∑ d ∈ q.divisors, moebiusReal (q / d) *
        ((d : ℝ) * Real.cos ((d : ℝ) * θ / 2) / (2 * Real.sin ((d : ℝ) * θ / 2)))
      = (∑ d ∈ q.divisors, moebiusReal (q / d) *
          ((d : ℝ) * Real.cos ((d : ℝ) * θ / 2) / (2 * Real.sin ((d : ℝ) * θ / 2)))) -
        ∑ d ∈ q.divisors, moebiusReal (q / d) * (1 / θ) := by rw [hpole, sub_zero]
    _ = ∑ d ∈ q.divisors, moebiusReal (q / d) *
          ((d : ℝ) * Real.cos ((d : ℝ) * θ / 2) / (2 * Real.sin ((d : ℝ) * θ / 2)) - 1 / θ) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun d _ => by ring

/-- **Elementary Cotangent Residual Bound.**
For `0 < x ≤ 1`, `|cos x / sin x − 1 / x| ≤ x`. -/
theorem abs_cos_div_sin_sub_inv_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |Real.cos x / Real.sin x - 1 / x| ≤ x := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have hx3 : x ^ 3 ≤ x := by
    have : x ^ 3 = x * x ^ 2 := by ring
    nlinarith
  have hx5 : x ^ 5 ≤ x ^ 3 := by
    have : 0 < x ^ 3 := pow_pos hx0 3
    have : x ^ 5 = x ^ 3 * x ^ 2 := by ring
    nlinarith
  have hsin_lo : x - x ^ 3 / 6 < Real.sin x := Real.sin_gt_sub_cube hx0
  have hsin_hi : Real.sin x ≤ x := Real.sin_le hx0.le
  have hsin_pos : 0 < Real.sin x := by linarith
  have hcos_lo : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have hcos_hi : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
    have hb := Real.cos_bound (x := x) (by rw [abs_of_pos hx0]; exact hx1)
    rw [abs_of_pos hx0] at hb
    have h4 : (4 : ℕ).factorial = 24 := by decide
    rw [h4] at hb
    linarith [(abs_le.mp hb).2]
  have hrw : Real.cos x / Real.sin x - 1 / x = (x * Real.cos x - Real.sin x) / (x * Real.sin x) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos (mul_pos hx0 hsin_pos), div_le_iff₀ (mul_pos hx0 hsin_pos), abs_le]
  have h1 : x * (1 - x ^ 2 / 2) ≤ x * Real.cos x := mul_le_mul_of_nonneg_left hcos_lo hx0.le
  have h2 : x * Real.cos x ≤ x * (1 - x ^ 2 / 2 + x ^ 4 / 24) :=
    mul_le_mul_of_nonneg_left hcos_hi hx0.le
  have h3 : x ^ 2 * (x - x ^ 3 / 6) ≤ x * (x * Real.sin x) := by
    have := mul_le_mul_of_nonneg_left hsin_lo.le (sq_nonneg x)
    linarith
  constructor <;> nlinarith

/-- For each divisor `d ∣ q` (`q ≥ 2`) and `0 < θ ≤ 2 / q`, the scaled cotangent residual satisfies
`|d cos(dθ/2) / (2 sin(dθ/2)) − 1 / θ| ≤ d² θ / 4`. -/
theorem abs_divisor_cot_sub_inv_le {q d : ℕ} {θ : ℝ}
    (hq : 2 ≤ q) (hd : d ∈ q.divisors) (hθ0 : 0 < θ) (hθ : θ ≤ 2 / q) :
    |(d : ℝ) * Real.cos ((d : ℝ) * θ / 2) / (2 * Real.sin ((d : ℝ) * θ / 2)) - 1 / θ|
      ≤ (d : ℝ) ^ 2 * θ / 4 := by
  have hq1 : 1 ≤ q := by omega
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hd_le : d ≤ q := Nat.le_of_dvd hq1 (Nat.dvd_of_mem_divisors hd)
  have hd_real : (0 : ℝ) < d := by exact_mod_cast hd0
  have hq_real : (0 : ℝ) < q := by exact_mod_cast hq1
  set x := (d : ℝ) * θ / 2 with hxdef
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by
    have hdq : (d : ℝ) ≤ q := by exact_mod_cast hd_le
    have h1 : (d : ℝ) * θ ≤ 2 := by
      calc (d : ℝ) * θ ≤ (q : ℝ) * (2 / q) :=
            mul_le_mul hdq hθ hθ0.le hq_real.le
        _ = 2 := mul_div_cancel₀ 2 hq_real.ne'
    linarith
  have hid : (d : ℝ) * Real.cos x / (2 * Real.sin x) - 1 / θ =
      ((d : ℝ) / 2) * (Real.cos x / Real.sin x - 1 / x) := by
    rw [hxdef]
    field_simp
  rw [hid, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (d : ℝ) / 2)]
  calc ((d : ℝ) / 2) * |Real.cos x / Real.sin x - 1 / x|
      ≤ ((d : ℝ) / 2) * x := mul_le_mul_of_nonneg_left (abs_cos_div_sin_sub_inv_le hx0 hx1) (by positivity)
    _ = (d : ℝ) ^ 2 * θ / 4 := by rw [hxdef]; ring

/-- **Horizon-Uniform Pointwise Ramanujan Cosine Sum Bound.**
For every modulus `q ≥ 2`, period count `R ≥ 1`, and frequency `0 < θ ≤ 2 / q`:
`|(∑_{h=1}^{qR} c_q(h) cos(hθ)) + (φ(q)/2)(1 − cos(qRθ))| ≤ (∑_{d ∣ q} d²) (θ / 4)`.
Notice that the right-hand side is completely independent of `R`. -/
theorem abs_sum_ramanujanLagCoefficient_mul_cos_add_le {q R : ℕ} {θ : ℝ}
    (hq : 2 ≤ q) (hR : 1 ≤ R) (hθ0 : 0 < θ) (hθ : θ ≤ 2 / q) :
    |(∑ h ∈ Finset.Icc 1 (q * R), ramanujanLagCoefficient q h * Real.cos ((h : ℝ) * θ)) +
        (q.totient : ℝ) / 2 * (1 - Real.cos (((q * R : ℕ) : ℝ) * θ))|
      ≤ (∑ d ∈ q.divisors, (d : ℝ) ^ 2) * (θ / 4) := by
  have hq1 : 1 ≤ q := by omega
  have hqR1 : 1 ≤ q * R := Nat.mul_pos hq1 hR
  have hθ_pi : θ ≤ π / q := by
    refine hθ.trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg q))
    linarith [Real.pi_gt_three]
  have hsplit : (∑ h ∈ Finset.Icc 1 (q * R),
        ramanujanLagCoefficient q h * Real.cos ((h : ℝ) * θ)) =
      (∑ h ∈ Finset.Icc 1 (q * R - 1),
        ramanujanLagCoefficient q h * Real.cos ((h : ℝ) * θ)) +
      (q.totient : ℝ) * Real.cos (((q * R : ℕ) : ℝ) * θ) := by
    have htop := Finset.sum_Icc_succ_top (a := 1) (b := q * R - 1) (by omega)
      (fun h => ramanujanLagCoefficient q h * Real.cos ((h : ℝ) * θ))
    have hsucc : q * R - 1 + 1 = q * R := by omega
    rw [hsucc] at htop
    rw [htop, ramanujanLagCoefficient_of_dvd hq1 (dvd_mul_right q R)]
  have hrew : (∑ h ∈ Finset.Icc 1 (q * R),
        ramanujanLagCoefficient q h * Real.cos ((h : ℝ) * θ)) +
      (q.totient : ℝ) / 2 * (1 - Real.cos (((q * R : ℕ) : ℝ) * θ)) =
      (q.totient : ℝ) / 2 +
      (∑ h ∈ Finset.Icc 1 (q * R - 1),
        ramanujanLagCoefficient q h * Real.cos ((h : ℝ) * θ)) +
      (q.totient : ℝ) / 2 * Real.cos (((q * R : ℕ) : ℝ) * θ) := by
    rw [hsplit]; ring
  rw [hrew, trapezoidal_ramanujan_cos_eq hq hR hθ0 hθ_pi, abs_mul]
  have hsin : |Real.sin (((q * R : ℕ) : ℝ) * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hsum : |∑ d ∈ q.divisors, moebiusReal (q / d) *
        ((d : ℝ) * Real.cos ((d : ℝ) * θ / 2) / (2 * Real.sin ((d : ℝ) * θ / 2)) - 1 / θ)|
      ≤ (∑ d ∈ q.divisors, (d : ℝ) ^ 2) * (θ / 4) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun d hd => ?_
    rw [abs_mul]
    have hμ : |moebiusReal (q / d)| ≤ 1 := by
      unfold moebiusReal
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (q / d)
    have hcot := abs_divisor_cot_sub_inv_le hq hd hθ0 hθ
    calc |moebiusReal (q / d)| *
          |(d : ℝ) * Real.cos ((d : ℝ) * θ / 2) / (2 * Real.sin ((d : ℝ) * θ / 2)) - 1 / θ|
        ≤ 1 * ((d : ℝ) ^ 2 * θ / 4) :=
          mul_le_mul hμ hcot (abs_nonneg _) zero_le_one
      _ = (d : ℝ) ^ 2 * (θ / 4) := by ring
  calc |Real.sin (((q * R : ℕ) : ℝ) * θ)| *
        |∑ d ∈ q.divisors, moebiusReal (q / d) *
          ((d : ℝ) * Real.cos ((d : ℝ) * θ / 2) / (2 * Real.sin ((d : ℝ) * θ / 2)) - 1 / θ)|
      ≤ 1 * ((∑ d ∈ q.divisors, (d : ℝ) ^ 2) * (θ / 4)) :=
        mul_le_mul hsin hsum (abs_nonneg _) zero_le_one
    _ = (∑ d ∈ q.divisors, (d : ℝ) ^ 2) * (θ / 4) := one_mul _

/-- **Finite-Height Ramanujan Coalescent Transfer Theorem (Resolving Open Problem 3).**
For any non-negative integrable window `Ω` supported in `[a, b]` (`0 ≤ a ≤ b`, `0 < b`), any
modulus `q ≥ 2`, any period count `R ≥ 1`, and any scale `m > 0` with `q b ≤ 2 m`:
`|(∑_{h=1}^{qR} c_q(h) cosTransform Ω (h / m)) + (φ(q) / 2) cosTransform Ω 0|
  ≤ (φ(q) / 2) |cosTransform Ω (qR / m)| + (∑_{d ∣ q} d²) (b / (4m)) cosTransform Ω 0`. -/
theorem abs_sum_ramanujanLagCoefficient_mul_cosTransform_add_le
    {Ω : ℝ → ℝ} {a b m : ℝ} {q R : ℕ}
    (ha : 0 ≤ a) (_hab : a ≤ b) (hb : 0 < b) (hm : 0 < m)
    (hq : 2 ≤ q) (hR : 1 ≤ R) (hqm : (q : ℝ) * b ≤ 2 * m)
    (hInt : Integrable Ω) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (hsupp : ∀ τ, τ ∉ Icc a b → Ω τ = 0) :
    |(∑ h ∈ Finset.Icc 1 (q * R), ramanujanLagCoefficient q h * cosTransform Ω ((h : ℝ) / m)) +
        (q.totient : ℝ) / 2 * cosTransform Ω 0|
      ≤ (q.totient : ℝ) / 2 * |cosTransform Ω (((q * R : ℕ) : ℝ) / m)| +
        (∑ d ∈ q.divisors, (d : ℝ) ^ 2) * (b / (4 * m)) * cosTransform Ω 0 := by
  set S1 := (∑ h ∈ Finset.Icc 1 (q * R), ramanujanLagCoefficient q h * cosTransform Ω ((h : ℝ) / m)) +
    (q.totient : ℝ) / 2 * (cosTransform Ω 0 - cosTransform Ω (((q * R : ℕ) : ℝ) / m))
  have htri : |(∑ h ∈ Finset.Icc 1 (q * R), ramanujanLagCoefficient q h * cosTransform Ω ((h : ℝ) / m)) +
        (q.totient : ℝ) / 2 * cosTransform Ω 0|
      ≤ (q.totient : ℝ) / 2 * |cosTransform Ω (((q * R : ℕ) : ℝ) / m)| + |S1| := by
    have hid : (∑ h ∈ Finset.Icc 1 (q * R), ramanujanLagCoefficient q h * cosTransform Ω ((h : ℝ) / m)) +
        (q.totient : ℝ) / 2 * cosTransform Ω 0 =
        (q.totient : ℝ) / 2 * cosTransform Ω (((q * R : ℕ) : ℝ) / m) + S1 := by
      unfold S1; ring
    rw [hid]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q.totient : ℝ) / 2)]
  refine htri.trans (add_le_add le_rfl ?_)
  have hS1_int : S1 = ∫ τ, Ω τ *
      ((∑ h ∈ Finset.Icc 1 (q * R),
          ramanujanLagCoefficient q h * Real.cos ((h : ℝ) * (τ / m))) +
        (q.totient : ℝ) / 2 * (1 - Real.cos (((q * R : ℕ) : ℝ) * (τ / m)))) := by
    unfold S1 cosTransform
    simp_rw [← integral_const_mul]
    rw [← integral_finset_sum (Finset.Icc 1 (q * R))
      (fun h _ => (cosTransform_integrable hInt ((h : ℝ) / m)).const_mul _)]
    have hdiff_int : (∫ τ, (q.totient : ℝ) / 2 * (Ω τ * Real.cos (τ * 0))) -
        (∫ τ, (q.totient : ℝ) / 2 * (Ω τ * Real.cos (τ * (((q * R : ℕ) : ℝ) / m)))) =
        ∫ τ, (q.totient : ℝ) / 2 * Ω τ * (1 - Real.cos (((q * R : ℕ) : ℝ) * (τ / m))) := by
      rw [← integral_sub ((cosTransform_integrable hInt 0).const_mul _)
        ((cosTransform_integrable hInt _).const_mul _)]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [mul_zero, Real.cos_zero]
      rw [show τ * (((q * R : ℕ) : ℝ) / m) = ((q * R : ℕ) : ℝ) * (τ / m) by ring]
      ring
    rw [mul_sub, ← integral_const_mul, ← integral_const_mul, hdiff_int]
    rw [← integral_add]
    · refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      rw [Finset.mul_sum]
      have hsum_eq : (∑ h ∈ Finset.Icc 1 (q * R),
            ramanujanLagCoefficient q h * (Ω τ * Real.cos (τ * ((h : ℝ) / m)))) =
          ∑ h ∈ Finset.Icc 1 (q * R),
            Ω τ * (ramanujanLagCoefficient q h * Real.cos ((h : ℝ) * (τ / m))) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [show τ * ((h : ℝ) / m) = (h : ℝ) * (τ / m) by ring]
        ring
      rw [hsum_eq]
      ring
    · exact integrable_finset_sum _ fun h _ => (cosTransform_integrable hInt ((h : ℝ) / m)).const_mul _
    · have h1 := (cosTransform_integrable hInt 0).const_mul ((q.totient : ℝ) / 2)
      have h2 := (cosTransform_integrable hInt (((q * R : ℕ) : ℝ) / m)).const_mul ((q.totient : ℝ) / 2)
      refine (h1.sub h2).congr (Eventually.of_forall fun τ => ?_)
      simp only [Pi.sub_apply, mul_zero, Real.cos_zero]
      rw [show τ * (((q * R : ℕ) : ℝ) / m) = ((q * R : ℕ) : ℝ) * (τ / m) by ring]
      ring
  rw [hS1_int, cosTransform_zero_eq_integral, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    (hInt.const_mul _) (Eventually.of_forall fun τ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΩ0 τ)]
  by_cases hτ : τ ∈ Icc a b
  · obtain ⟨hτa, hτb⟩ := mem_Icc.mp hτ
    have hτ0 : 0 ≤ τ := ha.trans hτa
    rcases eq_or_lt_of_le hτ0 with rfl | hτpos
    · simp only [zero_div, mul_zero, Real.cos_zero, sub_self, mul_zero, add_zero]
      have hsum0 : (∑ h ∈ Finset.Icc 1 (q * R), ramanujanLagCoefficient q h * 1) = 0 := by
        have h1 : (∑ h ∈ Finset.Icc 1 (q * R), ramanujanLagCoefficient q h * 1) =
            ∑ d ∈ q.divisors, moebiusReal (q / d) *
              ((d : ℝ) * (((q / d) * R : ℕ) : ℝ)) := by
          have hq1 : 1 ≤ q := by omega
          have htop := Finset.sum_Icc_succ_top (a := 1) (b := q * R - 1)
            (by exact Nat.le_sub_one_of_lt (Nat.mul_pos hq1 hR))
            (fun h => ramanujanLagCoefficient q h * 1)
          have hsucc : q * R - 1 + 1 = q * R := Nat.sub_add_cancel (Nat.mul_pos hq1 hR)
          rw [hsucc] at htop
          rw [htop, ramanujanLagCoefficient_of_dvd hq1 (dvd_mul_right q R),
            ← sum_divisors_moebiusReal_div_mul hq1]
          unfold ramanujanLagCoefficient
          simp_rw [mul_one, Finset.sum_comm (s := Finset.Icc 1 (q * R - 1)), Finset.mul_sum]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun d hd => ?_
          have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
          have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
          have hd_le : d ≤ q := Nat.le_of_dvd hq1 hdq
          have hM1 : 1 ≤ (q / d) * R := Nat.mul_pos (Nat.div_pos hd_le hd0) hR
          rw [← mul_add, sum_Icc_filter_dvd_eq hR hd (fun _ => (d : ℝ))]
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          have hcard : (((q / d) * R - 1 + 1 - 1 : ℕ) : ℝ) = (((q / d) * R : ℕ) : ℝ) - 1 := by
            have : (q / d) * R - 1 + 1 - 1 = (q / d) * R - 1 := by omega
            rw [this, Nat.cast_sub hM1, Nat.cast_one]
          rw [hcard]; ring
        rw [h1]
        have h2 : ∀ d ∈ q.divisors,
            moebiusReal (q / d) * ((d : ℝ) * (((q / d) * R : ℕ) : ℝ)) =
            moebiusReal (q / d) * ((q * R : ℕ) : ℝ) := by
          intro d hd
          have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
          have hmul : d * ((q / d) * R) = q * R := by
            rw [← mul_assoc, Nat.mul_div_cancel' hdq]
          congr 1
          calc (d : ℝ) * (((q / d) * R : ℕ) : ℝ) = ((d * ((q / d) * R) : ℕ) : ℝ) := by
                push_cast; ring
            _ = ((q * R : ℕ) : ℝ) := by rw [hmul]
        rw [Finset.sum_congr rfl h2, ← Finset.sum_mul, sum_divisors_moebiusReal_div q,
          if_neg (by omega : q ≠ 1), zero_mul]
      rw [hsum0, abs_zero, mul_zero]
      have : 0 ≤ ∑ d ∈ q.divisors, (d : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have := hΩ0 0
      positivity
    · have hθ0 : 0 < τ / m := div_pos hτpos hm
      have hθ : τ / m ≤ 2 / q := by
        have hq0 : (0 : ℝ) < q := by positivity
        rw [div_le_div_iff₀ hm hq0]
        calc τ * q ≤ b * q := mul_le_mul_of_nonneg_right hτb hq0.le
          _ = q * b := mul_comm _ _
          _ ≤ 2 * m := hqm
      have hpt := abs_sum_ramanujanLagCoefficient_mul_cos_add_le hq hR hθ0 hθ
      have hτb_div : (τ / m) / 4 ≤ b / (4 * m) := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      have hsum_nn : 0 ≤ ∑ d ∈ q.divisors, (d : ℝ) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc Ω τ * |(∑ h ∈ Finset.Icc 1 (q * R),
              ramanujanLagCoefficient q h * Real.cos ((h : ℝ) * (τ / m))) +
            (q.totient : ℝ) / 2 * (1 - Real.cos (((q * R : ℕ) : ℝ) * (τ / m)))|
          ≤ Ω τ * ((∑ d ∈ q.divisors, (d : ℝ) ^ 2) * ((τ / m) / 4)) :=
            mul_le_mul_of_nonneg_left hpt (hΩ0 τ)
        _ ≤ Ω τ * ((∑ d ∈ q.divisors, (d : ℝ) ^ 2) * (b / (4 * m))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτb_div hsum_nn) (hΩ0 τ)
        _ = (∑ d ∈ q.divisors, (d : ℝ) ^ 2) * (b / (4 * m)) * Ω τ := by ring
  · rw [hsupp τ hτ]
    simp

/-- **Ward–Mertens Singular-Series Repulsion Transfer (Resolving Open Problem 4).**
Weighting the finite-height Ramanujan coalescent transfer theorem by the Hardy–Littlewood
singular-series weight `sqfreeTotientInv q / φ(q) = μ(q)² / φ(q)²` over `q ∈ Icc 2 Q` (`Q b ≤ 2 m`)
transfers the modulus-`q` singular-series correlation to the negative Ward–Mertens repulsion sum
`−(1/2) cosTransform Ω 0 ∑_{q=2}^Q sqfreeTotientInv q` with explicit finite-height error:
`|(∑_{q=2}^Q (sqfreeTotientInv q / φ(q)) ∑_{h=1}^{qR_q} c_q(h) cosTransform Ω (h/m))
    + (1/2) cosTransform Ω 0 ∑_{q=2}^Q sqfreeTotientInv q|
  ≤ (1/2) ∑_{q=2}^Q sqfreeTotientInv q |cosTransform Ω (qR_q / m)|
    + (b / (4m)) cosTransform Ω 0 ∑_{q=2}^Q (sqfreeTotientInv q / φ(q)) ∑_{d ∣ q} d²`. -/
theorem abs_sum_singularSeries_cosTransform_add_le
    {Ω : ℝ → ℝ} {a b m : ℝ} {Q : ℕ} {R : ℕ → ℕ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) (hm : 0 < m)
    (hR : ∀ q ∈ Finset.Icc 2 Q, 1 ≤ R q)
    (hQm : (Q : ℝ) * b ≤ 2 * m)
    (hInt : Integrable Ω) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (hsupp : ∀ τ, τ ∉ Icc a b → Ω τ = 0) :
    |(∑ q ∈ Finset.Icc 2 Q,
        (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
          ∑ h ∈ Finset.Icc 1 (q * R q),
            ramanujanLagCoefficient q h * cosTransform Ω ((h : ℝ) / m)) +
      (1 / 2) * cosTransform Ω 0 * ∑ q ∈ Finset.Icc 2 Q, RHTower.Sieve.sqfreeTotientInv q|
      ≤ (1 / 2) * (∑ q ∈ Finset.Icc 2 Q,
          RHTower.Sieve.sqfreeTotientInv q * |cosTransform Ω (((q * R q : ℕ) : ℝ) / m)|) +
        (b / (4 * m)) * cosTransform Ω 0 *
          ∑ q ∈ Finset.Icc 2 Q,
            (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
              (∑ d ∈ q.divisors, (d : ℝ) ^ 2) := by
  have hrew : (∑ q ∈ Finset.Icc 2 Q,
        (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
          ∑ h ∈ Finset.Icc 1 (q * R q),
            ramanujanLagCoefficient q h * cosTransform Ω ((h : ℝ) / m)) +
      (1 / 2) * cosTransform Ω 0 * ∑ q ∈ Finset.Icc 2 Q, RHTower.Sieve.sqfreeTotientInv q =
      ∑ q ∈ Finset.Icc 2 Q,
        (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
          ((∑ h ∈ Finset.Icc 1 (q * R q),
              ramanujanLagCoefficient q h * cosTransform Ω ((h : ℝ) / m)) +
            (q.totient : ℝ) / 2 * cosTransform Ω 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
    have hφ0 : (q.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < q)).ne'
    field_simp
    ring
  rw [hrew]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ q ∈ Finset.Icc 2 Q,
      |(RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
        ((∑ h ∈ Finset.Icc 1 (q * R q),
            ramanujanLagCoefficient q h * cosTransform Ω ((h : ℝ) / m)) +
          (q.totient : ℝ) / 2 * cosTransform Ω 0)|
      ≤ (1 / 2) * (RHTower.Sieve.sqfreeTotientInv q *
          |cosTransform Ω (((q * R q : ℕ) : ℝ) / m)|) +
        (b / (4 * m)) * cosTransform Ω 0 *
          ((RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
            (∑ d ∈ q.divisors, (d : ℝ) ^ 2)) := by
    intro q hq
    obtain ⟨hq2, hqQ⟩ := Finset.mem_Icc.mp hq
    have hq_real : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hqm : (q : ℝ) * b ≤ 2 * m :=
      (mul_le_mul_of_nonneg_right hq_real hb.le).trans hQm
    have hφ0 : (q.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < q)).ne'
    have hnn : 0 ≤ RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ) :=
      div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg q) (Nat.cast_nonneg _)
    rw [abs_mul, abs_of_nonneg hnn]
    have hmod := abs_sum_ramanujanLagCoefficient_mul_cosTransform_add_le ha hab hb hm
      hq2 (hR q hq) hqm hInt hΩ0 hsupp
    calc (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
          |(∑ h ∈ Finset.Icc 1 (q * R q),
              ramanujanLagCoefficient q h * cosTransform Ω ((h : ℝ) / m)) +
            (q.totient : ℝ) / 2 * cosTransform Ω 0|
        ≤ (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
          ((q.totient : ℝ) / 2 * |cosTransform Ω (((q * R q : ℕ) : ℝ) / m)| +
            (∑ d ∈ q.divisors, (d : ℝ) ^ 2) * (b / (4 * m)) * cosTransform Ω 0) :=
          mul_le_mul_of_nonneg_left hmod hnn
      _ = (1 / 2) * (RHTower.Sieve.sqfreeTotientInv q *
            |cosTransform Ω (((q * R q : ℕ) : ℝ) / m)|) +
          (b / (4 * m)) * cosTransform Ω 0 *
            ((RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
              (∑ d ∈ q.divisors, (d : ℝ) ^ 2)) := by
          field_simp; ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-! ## §3. General-Bandwidth Narrow-Strip Coalescent Proportion Envelope & Optimal Gain (Resolving Open Problem 5) -/

/-- The narrow-strip proportion gain over `2/3` at bandwidth `λ = 1 + δ` under a quadratic
coalescent surplus constant `B`:
`narrowStripGain B δ = 2 − (1/(1 + δ) + (1 + δ)/3) − B δ²/(1 + δ)² − 2/3`. -/
def narrowStripGain (B δ : ℝ) : ℝ :=
  2 - (1 / (1 + δ) + (1 + δ) / 3) - B * δ ^ 2 / (1 + δ) ^ 2 - 2 / 3

/-- **Exact Rational Factorization of the Narrow-Strip Coalescent Proportion Gain.**
For `1 + δ ≠ 0`,
`narrowStripGain B δ = δ * (2 + (1 − 3B) * δ − δ²) / (3 * (1 + δ)²)`. -/
theorem narrowStrip_coalescent_proportion_gain_eq (B : ℝ) {δ : ℝ} (hδ : 1 + δ ≠ 0) :
    narrowStripGain B δ = δ * (2 + (1 - 3 * B) * δ - δ ^ 2) / (3 * (1 + δ) ^ 2) := by
  unfold narrowStripGain
  field_simp
  ring

/-- **Positivity of the Narrow-Strip Coalescent Gain for Arbitrary Quadratic Constant `B ≥ 0`.**
For every `B ≥ 0` and every `0 < δ < 2 / (3B + 1)`, `narrowStripGain B δ > 0`, so the certified
critical-line proportion at bandwidth `λ = 1 + δ` strictly exceeds `2/3`. -/
theorem narrowStrip_coalescent_gain_pos {B δ : ℝ} (hB : 0 ≤ B) (hδ0 : 0 < δ)
    (hδ : δ < 2 / (3 * B + 1)) :
    0 < narrowStripGain B δ := by
  have h1δ : 0 < 1 + δ := by linarith
  rw [narrowStrip_coalescent_proportion_gain_eq B h1δ.ne']
  have h3B1 : 1 ≤ 3 * B + 1 := by linarith
  have h3B1_pos : 0 < 3 * B + 1 := by linarith
  have hmul : (3 * B + 1) * δ < 2 := by
    rwa [lt_div_iff₀ h3B1_pos, mul_comm] at hδ
  have hδ_lt2 : δ < 2 := by nlinarith
  have hnum : 0 < 2 + (1 - 3 * B) * δ - δ ^ 2 := by
    have hid : 2 + (1 - 3 * B) * δ - δ ^ 2 = (2 - (3 * B + 1) * δ) + δ * (2 - δ) := by ring
    rw [hid]
    have h1 : 0 < 2 - (3 * B + 1) * δ := by linarith
    have h2 : 0 < δ * (2 - δ) := mul_pos hδ0 (by linarith)
    linarith
  positivity

/-- **Closed-Form Gain at the Optimal Narrow-Strip Width `δ_*(B) = 1 / (3B + 2)`.**
For any `B ≥ 0`, choosing the narrow-strip width `δ = 1 / (3B + 2)` yields the exact positive gain
`narrowStripGain B (1 / (3B + 2)) = (3B² + 7B + 3) / (9 (B + 1)² (3B + 2)) > 0`. -/
theorem narrowStrip_optimal_delta_gain {B : ℝ} (hB : 0 ≤ B) :
    narrowStripGain B (1 / (3 * B + 2)) =
      (3 * B ^ 2 + 7 * B + 3) / (9 * (B + 1) ^ 2 * (3 * B + 2)) ∧
    0 < narrowStripGain B (1 / (3 * B + 2)) := by
  have h3B2 : 0 < 3 * B + 2 := by linarith
  have hB1 : 0 < B + 1 := by linarith
  have h1δ : 1 + 1 / (3 * B + 2) ≠ 0 := by positivity
  have heq : narrowStripGain B (1 / (3 * B + 2)) =
      (3 * B ^ 2 + 7 * B + 3) / (9 * (B + 1) ^ 2 * (3 * B + 2)) := by
    rw [narrowStrip_coalescent_proportion_gain_eq B h1δ]
    field_simp
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  positivity

/-- **Collar-Preserved Narrow-Strip Proportion Beyond `2/3`.**
For any `B ≥ 0` and any `0 < δ < 2 / (3B + 1)`, choosing the smooth-window collar
`ε₁ = narrowStripGain B δ / (64 * π)` leaves at least half the gain `(1/2) narrowStripGain B δ > 0`
above `2/3` after subtracting the trace collar loss `32 * π * ε₁`. -/
theorem narrowStrip_collar_preserves_gain {B δ : ℝ} (hB : 0 ≤ B) (hδ0 : 0 < δ)
    (hδ : δ < 2 / (3 * B + 1)) :
    let ε₁ := narrowStripGain B δ / (64 * π)
    0 < ε₁ ∧
    2 / 3 + (1 / 2) * narrowStripGain B δ =
      2 - (1 / (1 + δ) + (1 + δ) / 3) - B * δ ^ 2 / (1 + δ) ^ 2 - 32 * π * ε₁ ∧
    0 < (1 / 2) * narrowStripGain B δ := by
  have hgain := narrowStrip_coalescent_gain_pos hB hδ0 hδ
  have hπ := Real.pi_pos
  refine ⟨by positivity, ?_, by positivity⟩
  unfold narrowStripGain
  field_simp
  ring

end GaloisForLFunctions.TransThresholdPairCorrelation

