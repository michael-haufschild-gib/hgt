import GaloisForLFunctions.RHTower.ModularArcForwardDilationAllIntegerBlind

/-!
# Quantitative sub-harmonic moment bounds and spectral convergence for integer-dilated arc witnesses

In `ModularArcAtomicSublatticeBlind`, applying the 5-point atomic pole filter at `b = log k` (`k ≥ 2`)
to the continuous modular arc witness `ν` produced a self-reciprocal (`h(1/x) = |x| h(x)`), even,
zero-mean, strictly positive definite function `H_k = arcLineAtomicVector (log k) ν` in the full
`O(e^{−3|v|/2})` Weil decay class that:
- is identically blind on the infinite `k²`-sublattice `arcFreq (k²(m+1) − 1)` (`m ∈ ℕ`),
- reduces on the `k`-sublattice `arcFreq (k(m+1) − 1)` to a single `−2 log k` sub-harmonic term, and
- reduces at every integer frequency `arcFreq n = 2π(n+1)` to the two negative-dilation sub-harmonics
  `−log k` and `−2 log k`.

In this module we establish the **general Basset–Whittaker integral identity** for `arcLineDeriv ν` at
arbitrary positive real frequencies `c > 0` (`integral_arcLineDeriv_mul_sin_eq_half_integral_arcPairSineMoment`)
and combine it with the sub-harmonic reduction theorems to prove sharp quantitative bounds and
asymptotic convergence laws as `k → ∞`:

1. **Uniform dilation-invariant Basset bound (`abs_exp_mul_integral_arcLineDeriv_mul_sin_le`):**
   For any finite measure `ν`, any `c > 0`, and any dilation shift `w ∈ ℝ`,
   `|e^{−w/2} ∫ h_ν'(t) sin(c e^w t) dt| ≤ 2√(π/2) · ν.real univ · √c`.
2. **Quantitative sub-harmonic bound at all integers (`abs_integral_arcLineAtomicDeriv_log_mul_sin_le`):**
   Because the three shifts `0, log k, 2 log k` are annihilated by `ν` at every integer frequency
   `arcFreq n`, only the two negative shifts `−log k` and `−2 log k` contribute:
   `|∫ H_k'(x) sin(arcFreq n · x) dx| ≤ 2√(π/2) · ν.real univ · √(arcFreq n) · (1/cosh(½ log k) + 1/(4 cosh²(½ log k)))`.
3. **Quadratic-cosh improvement on the `k`-sublattice (`abs_integral_arcLineAtomicDeriv_log_mul_sin_mul_le`):**
   On `arcFreq (k(m+1) − 1)`, the `−log k` shift also vanishes, leaving only the `1/(4 cosh²(½ log k))`
   second-order factor:
   `|∫ H_k'(x) sin(arcFreq (k(m+1) − 1) · x) dx| ≤ 2√(π/2) · ν.real univ · √(arcFreq (k(m+1) − 1)) / (4 cosh²(½ log k))`.
4. **Simultaneous integer-moment vanishing and critical-line spectral convergence (`k → ∞`):**
   - `tendsto_integral_arcLineAtomicDeriv_log_mul_sin_atTop`: for every `n ∈ ℕ`,
     `∫ H_k'(x) sin(arcFreq n · x) dx → 0` as `k → ∞`.
   - `tendsto_integral_cos_mul_arcLineAtomicProfile_log_atTop`: for every `τ ∈ ℝ`,
     `∫ cos(τv) (e^{v/2} H_k(e^v)) dv → ∫ cos(τv) B_ν(v) dv > 0` as `k → ∞`.
   - `exists_logNat_decayClass_asymptotic_arcWitness`: unconditional master theorem packaging all
     finite-`k` sublattice blindness properties, quantitative bounds, and `k → ∞` limits.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### General Basset–Whittaker sine moment identity for `arcLineDeriv ν` -/

theorem continuous_arcPairSineMoment_of_pos {c : ℝ} (hc : 0 < c) :
    Continuous fun u : ArcParam => arcPairSineMoment u c := by
  unfold arcPairSineMoment modularArcHeight
  have h1 : Continuous fun u : ArcParam =>
      4 * c * Real.sqrt (Real.sqrt (1 - (u : ℝ) ^ 2)) := by fun_prop
  have hk : Continuous fun u : ArcParam =>
      kMoment 0 (c * Real.sqrt (1 - (u : ℝ) ^ 2)) :=
    (continuousOn_kMoment 0).comp_continuous (by fun_prop) fun u =>
      mul_pos hc (modularArcHeight_pos u.2)
  have h2 : Continuous fun u : ArcParam => Real.cos (c * (u : ℝ)) := by fun_prop
  exact (h1.mul hk).mul h2 |>.neg

/-- **General Basset–Whittaker formula for `arcLineDeriv ν` at any positive frequency `c > 0`.** -/
theorem integral_arcLineDeriv_mul_sin_eq_half_integral_arcPairSineMoment
    (ν : Measure ArcParam) [IsFiniteMeasure ν] {c : ℝ} (hc : 0 < c) :
    ∫ x, arcLineDeriv ν x * Real.sin (c * x) =
      (1 / 2 : ℝ) * ∫ u, arcPairSineMoment u c ∂ν := by
  have hint := integrable_arcLineKernel_prod ν (g := fun x => Real.sin (c * x))
    (by fun_prop) fun x => Real.abs_sin_le_one _
  have hswap := integral_integral_swap (f := fun x u => arcLineKernel x u *
    Real.sin (c * x)) hint
  have hl : ∫ x, arcLineDeriv ν x * Real.sin (c * x) =
      -∫ x, ∫ u, arcLineKernel x u * Real.sin (c * x) ∂ν := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [arcLineDeriv, arcLineKernel]
    rw [neg_mul, integral_mul_const]
  rw [hl, hswap]
  have hinner : ∀ u : ArcParam, ∫ x, arcLineKernel x u * Real.sin (c * x) =
      -((1 / 2 : ℝ) * arcPairSineMoment u c) := by
    intro u
    rw [integral_arcLineKernel_mul_sin u hc]
    unfold arcPairSineMoment
    ring
  simp_rw [hinner]
  rw [integral_neg, integral_const_mul, neg_neg]

/-- **Uniform dilation-invariant bound on the sine moments of `arcLineDeriv ν`.**
For any finite measure `ν`, any `c > 0`, and any dilation shift `w ∈ ℝ`,
`|e^{−w/2} ∫ h_ν'(t) sin(c e^w t) dt| ≤ 2√(π/2) · ν.real univ · √c`. -/
theorem abs_exp_mul_integral_arcLineDeriv_mul_sin_le
    (ν : Measure ArcParam) [IsFiniteMeasure ν] {c : ℝ} (hc : 0 < c) (w : ℝ) :
    |Real.exp (-(w / 2)) * ∫ t, arcLineDeriv ν t * Real.sin (c * Real.exp w * t)| ≤
      2 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c := by
  have hcw : 0 < c * Real.exp w := mul_pos hc (Real.exp_pos w)
  rw [integral_arcLineDeriv_mul_sin_eq_half_integral_arcPairSineMoment ν hcw,
    ← mul_assoc, mul_comm (Real.exp (-(w / 2))) (1 / 2 : ℝ), mul_assoc,
    ← integral_const_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hcont : Continuous fun u : ArcParam =>
      Real.exp (-(w / 2)) * arcPairSineMoment u (c * Real.exp w) :=
    continuous_const.mul (continuous_arcPairSineMoment_of_pos hcw)
  calc (1 / 2 : ℝ) * |∫ u, Real.exp (-(w / 2)) * arcPairSineMoment u (c * Real.exp w) ∂ν|
      ≤ (1 / 2 : ℝ) * ∫ u, |Real.exp (-(w / 2)) * arcPairSineMoment u (c * Real.exp w)| ∂ν :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ∫ _, 4 * Real.sqrt (Real.pi / 2) * Real.sqrt c ∂ν := by
        refine mul_le_mul_of_nonneg_left
          (integral_mono (integrable_of_continuous_arc hcont).abs (integrable_const _)
            fun u => abs_exp_mul_arcPairSineMoment_le u hc w) (by norm_num)
    _ = 2 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c := by
        rw [integral_const, smul_eq_mul]; ring

/-! ### Quantitative sub-harmonic bounds at `b = log k` -/

/-- **Quantitative sub-harmonic sine moment bound for `arcLineAtomicDeriv (log k) ν`.**
Because the three non-negative shifts `0, log k, 2 log k` vanish identically at every integer
frequency `arcFreq n`, only the two negative shifts `−log k` (weight `−1/cosh(½ log k)`) and
`−2 log k` (weight `1/(4 cosh²(½ log k))`) contribute. -/
theorem abs_integral_arcLineAtomicDeriv_log_mul_sin_le
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    |∫ x, arcLineAtomicDeriv (Real.log k) ν x * Real.sin (arcFreq n * x)| ≤
      2 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n) *
        (1 / Real.cosh (Real.log k / 2) + 1 / (4 * Real.cosh (Real.log k / 2) ^ 2)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hc : 0 < arcFreq n := arcFreq_pos n
  rw [integral_arcLineAtomicDeriv_log_mul_sin_eq_subharmonics hblind hk n]
  set B := 2 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n)
  have h1 : |Real.sqrt k * ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n / k * t)| ≤ B := by
    have he1 : Real.sqrt k = Real.exp (-(-Real.log k / 2)) := by
      rw [neg_div, neg_neg, Real.exp_half, Real.exp_log hkpos]
    have hf1 : arcFreq n / (k : ℝ) = arcFreq n * Real.exp (-Real.log k) := by
      rw [Real.exp_neg, Real.exp_log hkpos, div_eq_mul_inv]
    have hbound := abs_exp_mul_integral_arcLineDeriv_mul_sin_le ν hc (-Real.log k)
    rwa [← he1, ← hf1] at hbound
  have h2 : |(k : ℝ) * ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n / (k : ℝ) ^ 2 * t)| ≤ B := by
    have he2 : (k : ℝ) = Real.exp (-(-(2 * Real.log k) / 2)) := by
      rw [show -(-(2 * Real.log k) / 2) = Real.log k by ring, Real.exp_log hkpos]
    have hf2 : arcFreq n / (k : ℝ) ^ 2 = arcFreq n * Real.exp (-(2 * Real.log k)) := by
      rw [Real.exp_neg, show (2 : ℝ) * Real.log k = ((2 : ℕ) : ℝ) * Real.log k by norm_num,
        Real.exp_nat_mul, Real.exp_log hkpos, div_eq_mul_inv]
    have hbound := abs_exp_mul_integral_arcLineDeriv_mul_sin_le ν hc (-(2 * Real.log k))
    rwa [← he2, ← hf2] at hbound
  have hC := Real.cosh_pos (Real.log k / 2)
  have hw1 : |atomW1 (Real.log k)| = 1 / Real.cosh (Real.log k / 2) := by
    unfold atomW1; rw [abs_neg, abs_of_pos (by positivity)]
  have hw2 : |atomW2 (Real.log k)| = 1 / (4 * Real.cosh (Real.log k / 2) ^ 2) := by
    unfold atomW2; rw [abs_of_pos (by positivity)]
  calc |atomW1 (Real.log k) * (Real.sqrt k *
          ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n / k * t)) +
        atomW2 (Real.log k) * ((k : ℝ) *
          ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n / (k : ℝ) ^ 2 * t))|
      ≤ |atomW1 (Real.log k)| *
          |Real.sqrt k * ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n / k * t)| +
        |atomW2 (Real.log k)| *
          |(k : ℝ) * ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n / (k : ℝ) ^ 2 * t)| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ |atomW1 (Real.log k)| * B + |atomW2 (Real.log k)| * B := by gcongr
    _ = B * (1 / Real.cosh (Real.log k / 2) + 1 / (4 * Real.cosh (Real.log k / 2) ^ 2)) := by
        rw [hw1, hw2]; ring

/-- **Improved quadratic-cosh bound on the `k`-divisible sublattice.**
At frequencies `arcFreq (k(m+1) − 1) = 2π k(m+1)`, the `−log k` sub-harmonic vanishes identically,
so the moment is bounded purely by the second-order weight `1 / (4 cosh²(½ log k))`. -/
theorem abs_integral_arcLineAtomicDeriv_log_mul_sin_mul_le
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    |∫ x, arcLineAtomicDeriv (Real.log k) ν x *
        Real.sin (arcFreq (k * (m + 1) - 1) * x)| ≤
      2 * Real.sqrt (Real.pi / 2) * ν.real univ *
        Real.sqrt (arcFreq (k * (m + 1) - 1)) *
        (1 / (4 * Real.cosh (Real.log k / 2) ^ 2)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hc : 0 < arcFreq (k * (m + 1) - 1) := arcFreq_pos _
  rw [integral_arcLineAtomicDeriv_log_mul_sin_mul_eq_single_subharmonic hblind hk m,
    abs_mul]
  have hmul : arcFreq (k * (m + 1) - 1) = arcFreq m * k := by
    rw [Nat.mul_comm k (m + 1), ← arcFreq_mul_nat hk m]
  have hf2 : arcFreq m / (k : ℝ) =
      arcFreq (k * (m + 1) - 1) * Real.exp (-(2 * Real.log k)) := by
    rw [hmul, Real.exp_neg, show (2 : ℝ) * Real.log k = ((2 : ℕ) : ℝ) * Real.log k by norm_num,
      Real.exp_nat_mul, Real.exp_log hkpos]
    have := hkpos.ne'
    field_simp
  have he2 : (k : ℝ) = Real.exp (-(-(2 * Real.log k) / 2)) := by
    rw [show -(-(2 * Real.log k) / 2) = Real.log k by ring, Real.exp_log hkpos]
  have h2 : |(k : ℝ) * ∫ t, arcLineDeriv ν t * Real.sin (arcFreq m / k * t)| ≤
      2 * Real.sqrt (Real.pi / 2) * ν.real univ *
        Real.sqrt (arcFreq (k * (m + 1) - 1)) := by
    have hbound := abs_exp_mul_integral_arcLineDeriv_mul_sin_le ν hc (-(2 * Real.log k))
    rwa [← he2, ← hf2] at hbound
  have hC := Real.cosh_pos (Real.log k / 2)
  have hw2 : |atomW2 (Real.log k)| = 1 / (4 * Real.cosh (Real.log k / 2) ^ 2) := by
    unfold atomW2; rw [abs_of_pos (by positivity)]
  rw [hw2, mul_comm (2 * Real.sqrt (Real.pi / 2) * ν.real univ *
    Real.sqrt (arcFreq (k * (m + 1) - 1)))]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-! ### Asymptotic vanishing of integer moments and critical-line convergence as `k → ∞` -/

theorem sqrt_le_two_mul_cosh_half_log {k : ℕ} (hk : 1 ≤ k) :
    Real.sqrt k ≤ 2 * Real.cosh (Real.log k / 2) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  rw [Real.cosh_eq, Real.exp_half, Real.exp_log hkpos]
  linarith [Real.exp_pos (-(Real.log k / 2))]

theorem inv_cosh_half_log_le {k : ℕ} (hk : 1 ≤ k) :
    1 / Real.cosh (Real.log k / 2) ≤ 2 * (Real.sqrt k)⁻¹ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hC := Real.cosh_pos (Real.log k / 2)
  have hs := Real.sqrt_pos.mpr hkpos
  rw [div_le_iff₀ hC]
  have h1 := sqrt_le_two_mul_cosh_half_log hk
  have h2 : (Real.sqrt k)⁻¹ * Real.sqrt k ≤ (Real.sqrt k)⁻¹ * (2 * Real.cosh (Real.log k / 2)) :=
    mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hs.le)
  rw [inv_mul_cancel₀ hs.ne'] at h2
  linarith

theorem tendsto_inv_cosh_half_log_atTop :
    Tendsto (fun k : ℕ => 1 / Real.cosh (Real.log k / 2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun k : ℕ => 2 * (Real.sqrt k)⁻¹) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop).const_mul 2
  refine squeeze_zero' (eventually_ge_atTop 1 |>.mono fun k _ => by positivity)
    (eventually_ge_atTop 1 |>.mono fun k hk => inv_cosh_half_log_le hk) ht

/-- **Asymptotic vanishing of every integer sine moment as `k → ∞`.** -/
theorem tendsto_integral_arcLineAtomicDeriv_log_mul_sin_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0) (n : ℕ) :
    Tendsto (fun k : ℕ => ∫ x, arcLineAtomicDeriv (Real.log k) ν x * Real.sin (arcFreq n * x))
      atTop (𝓝 0) := by
  set B := 2 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n)
  have h1 := tendsto_inv_cosh_half_log_atTop
  have h2 : Tendsto (fun k : ℕ => 1 / (4 * Real.cosh (Real.log k / 2) ^ 2)) atTop (𝓝 0) := by
    have hsq := (h1.pow 2).const_mul (1 / 4 : ℝ)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hsq
    refine hsq.congr fun k => ?_
    ring
  have hbound : Tendsto (fun k : ℕ => B *
      (1 / Real.cosh (Real.log k / 2) + 1 / (4 * Real.cosh (Real.log k / 2) ^ 2)))
      atTop (𝓝 0) := by
    simpa using (h1.add h2).const_mul B
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [Real.norm_eq_abs]
  exact abs_integral_arcLineAtomicDeriv_log_mul_sin_le hblind hk n

/-- **Critical-line spectral convergence as `k → ∞`.** For every `τ ∈ ℝ`, the cosine transform of
`arcLineAtomicProfile (log k) ν` converges to the cosine transform of `arcPoissonProfile ν`. -/
theorem tendsto_integral_cos_mul_arcLineAtomicProfile_log_atTop
    (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    Tendsto (fun k : ℕ => ∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v)
      atTop (𝓝 (∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)) := by
  simp_rw [integral_cos_mul_arcLineAtomicProfile]
  have hcos : Tendsto (fun k : ℕ => Real.cos (Real.log k * τ) / Real.cosh (Real.log k / 2))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm'
      (Eventually.of_forall fun k => ?_) tendsto_inv_cosh_half_log_atTop
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.cosh_pos _)]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (Real.cosh_pos _).le
  have hmult : Tendsto (fun k : ℕ => (1 - Real.cos (Real.log k * τ) / Real.cosh (Real.log k / 2)) ^ 2)
      atTop (𝓝 1) := by
    have := (((tendsto_const_nhds (x := (1 : ℝ))).sub hcos).pow 2)
    simpa using this
  simpa using hmult.mul_const (∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)

/-! ### Master unconditional asymptotic and sublattice witness theorem -/

/-- **Master unconditional theorem for the integer-dilated continuous modular arc witnesses.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2`, `H_k = arcLineAtomicVector (log k) ν` is an even, self-reciprocal
(`H_k(1/x) = |x| H_k(x)`), zero-mean, strictly positive definite function in the `O(e^{−3|v|/2})`
Weil decay class satisfying:
1. Exact blindness along the infinite sublattice `arcFreq (k²(m+1) − 1)` for all `m ∈ ℕ`;
2. The quantitative `O(k^{−1})` sub-harmonic bound on `arcFreq (k(m+1) − 1)` and `O(k^{−1/2})`
   bound on all `arcFreq n`;
3. Asymptotic vanishing of every integer sine moment `∫ H_k'(x) sin(arcFreq n · x) dx → 0` as
   `k → ∞`, simultaneously with convergence of the critical-line cosine transform at every `τ ∈ ℝ`
   to the strictly positive transform of `arcPoissonProfile ν`. -/
theorem exists_logNat_decayClass_asymptotic_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ x, arcLineAtomicVector (Real.log k) ν (-x) = arcLineAtomicVector (Real.log k) ν x) ∧
        (∀ x, x ≠ 0 → arcLineAtomicVector (Real.log k) ν (1 / x) =
          |x| * arcLineAtomicVector (Real.log k) ν x) ∧
        ∫ x, arcLineAtomicVector (Real.log k) ν x = 0 ∧
        (∀ v, |arcLineAtomicProfile (Real.log k) ν v| ≤
          5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2))) ∧
        (∀ m : ℕ, ∫ x, arcLineAtomicDeriv (Real.log k) ν x *
          Real.sin (arcFreq (k ^ 2 * (m + 1) - 1) * x) = 0) ∧
        (∀ m : ℕ, |∫ x, arcLineAtomicDeriv (Real.log k) ν x *
            Real.sin (arcFreq (k * (m + 1) - 1) * x)| ≤
          2 * Real.sqrt (Real.pi / 2) * ν.real univ *
            Real.sqrt (arcFreq (k * (m + 1) - 1)) *
            (1 / (4 * Real.cosh (Real.log k / 2) ^ 2))) ∧
        ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v) ∧
      (∀ n : ℕ, Tendsto (fun k : ℕ =>
        ∫ x, arcLineAtomicDeriv (Real.log k) ν x * Real.sin (arcFreq n * x)) atTop (𝓝 0)) ∧
      ∀ τ : ℝ, Tendsto (fun k : ℕ =>
        ∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v)
        atTop (𝓝 (∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym, hpd, fun k hk => ?_,
    tendsto_integral_arcLineAtomicDeriv_log_mul_sin_atTop hblind,
    tendsto_integral_cos_mul_arcLineAtomicProfile_log_atTop ν⟩
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk1)
  have hkgt1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le one_lt_two hk)
  have hb : 0 < Real.log k := Real.log_pos hkgt1
  refine ⟨arcLineAtomicVector_neg_of_map_arcNeg (Real.log k) hsym,
    fun x hx => arcLineAtomicVector_inv (Real.log k) ν hx,
    integral_arcLineAtomicVector_eq_zero hb.le hsym,
    fun v => ?_,
    integral_arcLineAtomicDeriv_log_mul_sin_sq_mul_eq_zero hblind hk1,
    abs_integral_arcLineAtomicDeriv_log_mul_sin_mul_le hblind hk1,
    fun τ => integral_cos_mul_arcLineAtomicProfile_pos hb ν hpd τ⟩
  have hexp3 : Real.exp (3 * Real.log k) = (k : ℝ) ^ 3 := by
    rw [show (3 : ℝ) * Real.log k = ((3 : ℕ) : ℝ) * Real.log k by norm_num,
      Real.exp_nat_mul, Real.exp_log hkpos]
  simpa [hexp3] using abs_arcLineAtomicProfile_le hb.le hsym v

end

end RHTower
