import GaloisForLFunctions.RHTower.ModularArcDyadicCrossScaleHilbertPairing

/-!
# Quantitative `k → ∞` scale-limit convergence of the dyadic modular arc tower to the Poisson line model in `L^∞`, weighted power-law, and strip-weighted `L²` Hilbert norms

In `ModularArcDyadicCrossScaleHilbertPairing`, we established the cross-scale strip-weighted Hilbert
inner product `∫_{x > 0} x^{l₁ + l₂} V_{k₁}(x) V_{k₂}(x) dx`, the exact strip-weighted polarization
identity `∫_{x > 0} x^{2l} (V_{k₁}(x) − V_{k₂}(x))² dx = E_{k₁}(l) − 2 ⟨V_{k₁}, V_{k₂}⟩_l + E_{k₂}(l)`,
the two-scale two-point Cauchy–Schwarz inequality, and global multiplicative log-convexity across
the open critical strip `l ∈ (−1/2, 1/2)`.

Whereas `ModularArcDyadicHilbertEnergyConvergence` only compared `V_k = arcLineInfiniteDyadicVector k ν`
as `k → ∞` against the *moving* `k`-dependent atomic generator `arcLineAtomicVector (log k) ν`, in
this module we prove **quantitative `k → ∞` convergence to the fixed (`k`-independent) modular arc
Poisson profile `B_ν = arcPoissonProfile ν` and line vector `arcLineVector ν`** across all norms and
energy moments simultaneously:

1. **Uniform `O((√k)⁻¹)` `L^∞(ℝ)` and joint exponential `O(exp(−|v|/4) / cosh((log k)/4))` profile
   scale-limit bounds (`abs_arcLineAtomicProfile_sub_arcPoissonProfile_le_uniform`,
   `abs_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_uniform`,
   `abs_arcLineAtomicProfile_sub_arcPoissonProfile_le_exp_quarter`,
   `abs_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_exp_quarter`):**
   - For every `b ∈ ℝ` and `v ∈ ℝ`,
     `|arcLineAtomicProfile b ν v − arcPoissonProfile ν v| ≤ 6 · ν.real univ / cosh(b/2)`
     and
     `|arcLineAtomicProfile b ν v − arcPoissonProfile ν v| ≤ (15 · ν.real univ / cosh(b/4)) · exp(−|v|/4)`.
   - Combining with the dyadic tail from `r = 0` to `∞` proves that for every `k ≥ 2` and `v ∈ ℝ`,
     `|Φ_k(v) − B_ν(v)| ≤ 300 · ν.real univ · (√k)⁻¹`
     and
     `|Φ_k(v) − B_ν(v)| ≤ (4140 · ν.real univ / cosh((log k)/4)) · exp(−|v|/4)`.
2. **Two-sided multiplicative power-law scale-limit bounds on `ℝ \ {0}`
   (`arcLineVector_eq_exp_neg_half_mul_profile`,
   `abs_arcLineInfiniteDyadicVector_sub_arcLineVector_le_rpow_quarter_uniform`,
   `abs_arcLineInfiniteDyadicVector_sub_arcLineVector_le_rpow_quarter_near_zero`):**
   For every `k ≥ 2`, `|V_k(x) − arcLineVector ν x|` is bounded by
   `(4140 · ν.real univ / cosh((log k)/4)) · |x|^{−3/4}` on `|x| ≥ 1` and by
   `(4140 · ν.real univ / cosh((log k)/4)) · |x|^{−1/4}` on `0 < |x| ≤ 1`.
3. **Strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert norm convergence to `arcLineVector ν` and
   cross-scale Cauchy inequality across `|l| < 1/4`
   (`sq_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_exp_half`,
   `setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_arcLineVector_eq`,
   `setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_arcLineVector_le`,
   `tendsto_setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_arcLineVector_atTop`,
   `setIntegral_Ioi_rpow_two_mul_sq_sub_arcLineInfiniteDyadicVector_le_cauchy`):**
   Because `1 / cosh((log k)/4)² ≤ 2 / cosh((log k)/2) ≤ 4 · (√k)⁻¹`, squaring the joint exponential
   bound yields `(Φ_k(v) − B_ν(v))² ≤ 68558400 · (ν.real univ)² · (√k)⁻¹ · exp(−|v|/2)`.
   Integrating against `e^{2lv}` proves that for all `k ≥ 2` and `|l| < 1/4`:
   - `∫_{x > 0} x^{2l} (V_k(x) − arcLineVector ν x)² dx ≤ (68558400 · (ν.real univ)² / (1/4 − |l|)) · (√k)⁻¹ → 0` as `k → ∞`,
   - and for any two scales `k₁, k₂ ≥ 2`:
     `∫_{x > 0} x^{2l} (V_{k₁}(x) − V_{k₂}(x))² dx ≤ (137116800 · (ν.real univ)² / (1/4 − |l|)) · ((√k₁)⁻¹ + (√k₂)⁻¹)`.
4. **Asymptotic `k → ∞` convergence of the strip-weighted Hilbert energy `E_k(l)` and all
   logarithmic energy moments `M_n(k, ν) = ∫_{v > 0} v^n (Φ_k(v))² dv`
   (`abs_setIntegral_Ioi_rpow_two_mul_sq_sub_arcLineVector_le`,
   `tendsto_setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_atTop`,
   `abs_setIntegral_Ioi_zero_pow_mul_sq_sub_arcPoissonProfile_le`,
   `tendsto_setIntegral_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile_atTop`,
   `exists_dyadic_scaleLimit_hilbertConvergence_arcWitness`):**
   - For every `|l| < 1/4`, `E_k(l) = ∫_{x > 0} x^{2l} (V_k(x))² dx → ∫_{x > 0} x^{2l} (arcLineVector ν x)² dx` as `k → ∞`.
   - For every moment order `n ∈ ℕ`,
     `|∫_{v > 0} v^n (Φ_k(v))² dv − ∫_{v > 0} v^n (B_ν(v))² dv| ≤ 996000 · (ν.real univ)² · n! · 8^n · (√k)⁻¹ → 0` as `k → ∞`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Elementary hyperbolic double-angle and half-angle comparison bounds -/

/-- For every `u ∈ ℝ`, `(cosh u)² ≤ cosh(2u)`. -/
theorem cosh_sq_le_cosh_two_mul (u : ℝ) : Real.cosh u ^ 2 ≤ Real.cosh (2 * u) := by
  have h1 : 1 ≤ Real.cosh u := Real.one_le_cosh u
  rw [Real.cosh_two_mul]
  nlinarith

/-- For every `u ∈ ℝ`, `cosh u ≤ cosh(2u)`. -/
theorem cosh_le_cosh_two_mul (u : ℝ) : Real.cosh u ≤ Real.cosh (2 * u) := by
  have h1 : 1 ≤ Real.cosh u := Real.one_le_cosh u
  have h2 := cosh_sq_le_cosh_two_mul u
  nlinarith

/-- For every `u ∈ ℝ`, `cosh u / cosh(2u) ≤ 1 / cosh u`. -/
theorem cosh_div_cosh_two_mul_le (u : ℝ) :
    Real.cosh u / Real.cosh (2 * u) ≤ 1 / Real.cosh u := by
  have hcu : 0 < Real.cosh u := Real.cosh_pos u
  have hc2u : 0 < Real.cosh (2 * u) := Real.cosh_pos (2 * u)
  rw [div_le_iff₀ hc2u, div_mul_eq_mul_div, le_div_iff₀ hcu, one_mul, ← sq]
  exact cosh_sq_le_cosh_two_mul u

/-- For every `w ∈ ℝ`, `cosh w ≤ 2 · (cosh(w/2))²`. -/
theorem cosh_le_two_mul_cosh_half_sq (w : ℝ) :
    Real.cosh w ≤ 2 * Real.cosh (w / 2) ^ 2 := by
  have h := Real.cosh_two_mul (w / 2)
  rw [show 2 * (w / 2) = w by ring] at h
  have hs := Real.cosh_sq (w / 2)
  linarith

/-- For every `b ∈ ℝ`, `1 / (cosh(b/4))² ≤ 2 / cosh(b/2)`. -/
theorem inv_cosh_quarter_sq_le_two_div_cosh_half (b : ℝ) :
    1 / Real.cosh (b / 4) ^ 2 ≤ 2 / Real.cosh (b / 2) := by
  have hc4 : 0 < Real.cosh (b / 4) ^ 2 := by positivity
  have hc2 : 0 < Real.cosh (b / 2) := Real.cosh_pos (b / 2)
  rw [div_le_iff₀ hc4, div_mul_eq_mul_div, le_div_iff₀ hc2, one_mul]
  have h := cosh_le_two_mul_cosh_half_sq (b / 2)
  rwa [show b / 2 / 2 = b / 4 by ring] at h

/-- For every `k ≥ 1`, `1 / (cosh((log k)/4))² ≤ 4 · (√k)⁻¹`. -/
theorem inv_cosh_quarter_log_sq_le_four_mul_inv_sqrt {k : ℕ} (hk : 1 ≤ k) :
    1 / Real.cosh (Real.log k / 4) ^ 2 ≤ 4 * (Real.sqrt k)⁻¹ := by
  have h1 := inv_cosh_quarter_sq_le_two_div_cosh_half (Real.log k)
  have h2 := inv_cosh_half_log_le hk
  have h3 : 2 / Real.cosh (Real.log k / 2) = 2 * (1 / Real.cosh (Real.log k / 2)) := by ring
  linarith

/-- For every `k ≥ 1`, `((k : ℝ))⁻¹ ≤ (√k)⁻¹`. -/
theorem inv_natCast_le_inv_sqrt {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℝ))⁻¹ ≤ (Real.sqrt k)⁻¹ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsqrt_pos : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by positivity)
  have hle : Real.sqrt k ≤ k := by
    have hsq : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (by positivity)
    have h1 : 1 ≤ Real.sqrt k := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hk1
    nlinarith
  exact inv_anti₀ hsqrt_pos hle

/-- For every `k ≥ 1`, `((k : ℝ))⁻¹ ≤ 1 / cosh(log k)`. -/
theorem inv_natCast_le_inv_cosh_log {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℝ))⁻¹ ≤ 1 / Real.cosh (Real.log k) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hcosh : Real.cosh (Real.log k) ≤ k := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hlog : 0 ≤ Real.log k := Real.log_nonneg hk1
    have hinv : Real.exp (-Real.log k) ≤ Real.exp (Real.log k) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.cosh_eq, Real.exp_log hkpos]
    rw [Real.exp_log hkpos] at hinv
    linarith
  rw [one_div]
  exact inv_anti₀ (Real.cosh_pos _) hcosh

/-- `1 / cosh((log k)/4) → 0` as `k → ∞`. -/
theorem tendsto_inv_cosh_quarter_log_atTop :
    Tendsto (fun k : ℕ => 1 / Real.cosh (Real.log k / 4)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun k : ℕ => 1 / Real.cosh (Real.log k / 4) ^ 2) atTop (𝓝 0) := by
    have ht : Tendsto (fun k : ℕ => 4 * (Real.sqrt k)⁻¹) atTop (𝓝 0) := by
      simpa using
        ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop).const_mul 4
    exact squeeze_zero' (eventually_ge_atTop 1 |>.mono fun k _ => by positivity)
      (eventually_ge_atTop 1 |>.mono fun k hk => inv_cosh_quarter_log_sq_le_four_mul_inv_sqrt hk) ht
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun k => ?_
  have hc : 0 < Real.cosh (Real.log k / 4) := Real.cosh_pos _
  rw [one_div, ← inv_pow, Real.sqrt_sq (inv_nonneg.mpr hc.le), one_div]

/-! ### Uniform `L^∞(ℝ)` and exponential-weighted `O(exp(−|v|/4))` scale-limit bounds for `arcLineAtomicProfile` and `arcLineInfiniteDyadicProfile` -/

/-- Exact 5-point difference decomposition of `arcLineAtomicProfile b ν v − arcPoissonProfile ν v`. -/
theorem arcLineAtomicProfile_sub_arcPoissonProfile_eq
    (b : ℝ) (ν : Measure ArcParam) (v : ℝ) :
    arcLineAtomicProfile b ν v - arcPoissonProfile ν v =
      (1 / (2 * Real.cosh (b / 2) ^ 2)) * arcPoissonProfile ν v +
        atomW1 b * (arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b)) +
        atomW2 b * (arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b)) := by
  simp only [arcLineAtomicProfile, Fin.sum_univ_five, atomWeight, atomShift,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, sub_zero, sub_neg_eq_add, atomW0]
  ring

/-- **Uniform `L^∞(ℝ)` bound for `arcLineAtomicProfile b ν − arcPoissonProfile ν`:**
For every `b ∈ ℝ` and `v ∈ ℝ`,
`|arcLineAtomicProfile b ν v − arcPoissonProfile ν v| ≤ 6 · ν.real univ / cosh(b/2)`. -/
theorem abs_arcLineAtomicProfile_sub_arcPoissonProfile_le_uniform
    (b : ℝ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (v : ℝ) :
    |arcLineAtomicProfile b ν v - arcPoissonProfile ν v| ≤
      6 * ν.real univ / Real.cosh (b / 2) := by
  rw [arcLineAtomicProfile_sub_arcPoissonProfile_eq]
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  have hC1 : 1 ≤ Real.cosh (b / 2) := Real.one_le_cosh (b / 2)
  have hCpos : 0 < Real.cosh (b / 2) := Real.cosh_pos (b / 2)
  have hCsq : Real.cosh (b / 2) ≤ Real.cosh (b / 2) ^ 2 := by nlinarith
  have hinv_sq : 1 / Real.cosh (b / 2) ^ 2 ≤ 1 / Real.cosh (b / 2) :=
    one_div_le_one_div_of_le hCpos hCsq
  have h0 := abs_arcPoissonProfile_le_two ν v
  have h1m := abs_arcPoissonProfile_le_two ν (v - b)
  have h1p := abs_arcPoissonProfile_le_two ν (v + b)
  have h2m := abs_arcPoissonProfile_le_two ν (v - 2 * b)
  have h2p := abs_arcPoissonProfile_le_two ν (v + 2 * b)
  have ht0 : |(1 / (2 * Real.cosh (b / 2) ^ 2)) * arcPoissonProfile ν v| ≤
      ν.real univ * (1 / Real.cosh (b / 2)) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc (1 / (2 * Real.cosh (b / 2) ^ 2)) * |arcPoissonProfile ν v|
        ≤ (1 / (2 * Real.cosh (b / 2) ^ 2)) * (2 * ν.real univ) :=
          mul_le_mul_of_nonneg_left h0 (by positivity)
      _ = ν.real univ * (1 / Real.cosh (b / 2) ^ 2) := by ring
      _ ≤ ν.real univ * (1 / Real.cosh (b / 2)) := mul_le_mul_of_nonneg_left hinv_sq hν0
  have ht1 : |atomW1 b * (arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b))| ≤
      4 * ν.real univ * (1 / Real.cosh (b / 2)) := by
    rw [abs_mul, show |atomW1 b| = 1 / Real.cosh (b / 2) by
      unfold atomW1; rw [abs_neg, abs_of_pos (by positivity)]]
    have hsum : |arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b)| ≤ 4 * ν.real univ := by
      have := (abs_add_le _ _).trans (add_le_add h1m h1p)
      linarith
    calc (1 / Real.cosh (b / 2)) * |arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b)|
        ≤ (1 / Real.cosh (b / 2)) * (4 * ν.real univ) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 4 * ν.real univ * (1 / Real.cosh (b / 2)) := by ring
  have ht2 : |atomW2 b * (arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b))| ≤
      ν.real univ * (1 / Real.cosh (b / 2)) := by
    rw [abs_mul, show |atomW2 b| = 1 / (4 * Real.cosh (b / 2) ^ 2) by
      unfold atomW2; rw [abs_of_pos (by positivity)]]
    have hsum : |arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b)| ≤
        4 * ν.real univ := by
      have := (abs_add_le _ _).trans (add_le_add h2m h2p)
      linarith
    calc (1 / (4 * Real.cosh (b / 2) ^ 2)) *
            |arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b)|
        ≤ (1 / (4 * Real.cosh (b / 2) ^ 2)) * (4 * ν.real univ) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ν.real univ * (1 / Real.cosh (b / 2) ^ 2) := by ring
      _ ≤ ν.real univ * (1 / Real.cosh (b / 2)) := mul_le_mul_of_nonneg_left hinv_sq hν0
  have htri := (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add ht0 ht1)) ht2)
  have hgoal :
      ν.real univ * (1 / Real.cosh (b / 2)) +
        4 * ν.real univ * (1 / Real.cosh (b / 2)) +
        ν.real univ * (1 / Real.cosh (b / 2)) =
      6 * ν.real univ / Real.cosh (b / 2) := by ring
  linarith

/-- **Uniform `O((√k)⁻¹)` `L^∞(ℝ)` bound for `arcLineInfiniteDyadicProfile k ν − arcPoissonProfile ν` (`k ≥ 2`):**
For every `k ≥ 2` and `v ∈ ℝ`,
`|arcLineInfiniteDyadicProfile k ν v − arcPoissonProfile ν v| ≤ 300 · ν.real univ · (√k)⁻¹`. -/
theorem abs_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_uniform
    {k : ℕ} (hk : 2 ≤ k) (ν : Measure ArcParam) [IsFiniteMeasure ν] (v : ℝ) :
    |arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v| ≤
      300 * ν.real univ * (Real.sqrt k)⁻¹ := by
  have hk1 : 1 ≤ k := by omega
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  have htail : |arcLineInfiniteDyadicProfile k ν v - arcLineAtomicProfile (Real.log k) ν v| ≤
      288 * ν.real univ * (Real.sqrt k)⁻¹ := by
    have h1 := abs_arcLineInfiniteDyadicProfile_sub_le hk 0 ν v
    simp only [pow_zero, pow_one] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (inv_natCast_le_inv_sqrt hk1) (by positivity))
  have hatom : |arcLineAtomicProfile (Real.log k) ν v - arcPoissonProfile ν v| ≤
      12 * ν.real univ * (Real.sqrt k)⁻¹ := by
    have h1 := abs_arcLineAtomicProfile_sub_arcPoissonProfile_le_uniform (Real.log k) ν v
    rw [div_eq_mul_one_div] at h1
    have h2 := inv_cosh_half_log_le hk1
    calc |arcLineAtomicProfile (Real.log k) ν v - arcPoissonProfile ν v|
        ≤ 6 * ν.real univ * (1 / Real.cosh (Real.log k / 2)) := h1
      _ ≤ 6 * ν.real univ * (2 * (Real.sqrt k)⁻¹) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 12 * ν.real univ * (Real.sqrt k)⁻¹ := by ring
  have hsplit : arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v =
      (arcLineInfiniteDyadicProfile k ν v - arcLineAtomicProfile (Real.log k) ν v) +
        (arcLineAtomicProfile (Real.log k) ν v - arcPoissonProfile ν v) := by ring
  rw [hsplit]
  have htri := (abs_add_le _ _).trans (add_le_add htail hatom)
  linarith

/-- **Joint exponential `O(exp(−|v|/4) / cosh(b/4))` bound for `arcLineAtomicProfile b ν − arcPoissonProfile ν`:**
For every `b ∈ ℝ` and `v ∈ ℝ`,
`|arcLineAtomicProfile b ν v − arcPoissonProfile ν v| ≤ (15 · ν.real univ / cosh(b/4)) · exp(−|v|/4)`. -/
theorem abs_arcLineAtomicProfile_sub_arcPoissonProfile_le_exp_quarter
    (b : ℝ) {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineAtomicProfile b ν v - arcPoissonProfile ν v| ≤
      (15 * ν.real univ / Real.cosh (b / 4)) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
  rw [arcLineAtomicProfile_sub_arcPoissonProfile_eq]
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  have hC4_pos : 0 < Real.cosh (b / 4) := Real.cosh_pos (b / 4)
  have hC2_pos : 0 < Real.cosh (b / 2) := Real.cosh_pos (b / 2)
  have hC4_le_C2 : Real.cosh (b / 4) ≤ Real.cosh (b / 2) := by
    have h := cosh_le_cosh_two_mul (b / 4)
    rwa [show 2 * (b / 4) = b / 2 by ring] at h
  have hC2_le_sq : Real.cosh (b / 2) ≤ Real.cosh (b / 2) ^ 2 := by
    have h1 : 1 ≤ Real.cosh (b / 2) := Real.one_le_cosh (b / 2)
    nlinarith
  have hinv_sq : 1 / Real.cosh (b / 2) ^ 2 ≤ 1 / Real.cosh (b / 4) :=
    one_div_le_one_div_of_le hC4_pos (hC4_le_C2.trans hC2_le_sq)
  have hinv_C2 : 1 / Real.cosh (b / 2) ≤ 1 / Real.cosh (b / 4) :=
    one_div_le_one_div_of_le hC4_pos hC4_le_C2
  have hratio_b4 : Real.cosh (b / 4) / Real.cosh (b / 2) ≤ 1 / Real.cosh (b / 4) := by
    have h := cosh_div_cosh_two_mul_le (b / 4)
    rwa [show 2 * (b / 4) = b / 2 by ring] at h
  have hratio_b2 : Real.cosh (b / 2) / Real.cosh (b / 2) ^ 2 ≤ 1 / Real.cosh (b / 4) := by
    rw [sq, div_mul_cancel_left₀ hC2_pos.ne']
    simpa only [one_div] using hinv_C2
  have hc : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  have hc0 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have h0 := abs_arcPoissonProfile_le_exp_mul hν hc v
  have h1m := abs_arcPoissonProfile_le_exp_mul hν hc (v - b)
  have h1p := abs_arcPoissonProfile_le_exp_mul hν hc (v + b)
  have h2m := abs_arcPoissonProfile_le_exp_mul hν hc (v - 2 * b)
  have h2p := abs_arcPoissonProfile_le_exp_mul hν hc (v + 2 * b)
  have hshift1 : |arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b)| ≤
      10 * ν.real univ * Real.cosh (b / 4) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    have htri := (abs_add_le _ _).trans (add_le_add h1m h1p)
    have hcosh := exp_neg_mul_abs_sub_add_le_two_cosh hc0 v b
    rw [show (1 / 4 : ℝ) * b = b / 4 by ring] at hcosh
    calc |arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b)|
        ≤ 10 * ν.real univ *
            ((Real.exp (-((1 / 4 : ℝ) * |v - b|)) + Real.exp (-((1 / 4 : ℝ) * |v + b|))) / 2) := by
          linarith
      _ ≤ 10 * ν.real univ * (Real.cosh (b / 4) * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul_of_nonneg_left hcosh (by positivity)
      _ = 10 * ν.real univ * Real.cosh (b / 4) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring
  have hshift2 : |arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b)| ≤
      10 * ν.real univ * Real.cosh (b / 2) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    have htri := (abs_add_le _ _).trans (add_le_add h2m h2p)
    have hcosh := exp_neg_mul_abs_sub_add_le_two_cosh hc0 v (2 * b)
    rw [show (1 / 4 : ℝ) * (2 * b) = b / 2 by ring] at hcosh
    calc |arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b)|
        ≤ 10 * ν.real univ *
            ((Real.exp (-((1 / 4 : ℝ) * |v - 2 * b|)) +
              Real.exp (-((1 / 4 : ℝ) * |v + 2 * b|))) / 2) := by
          linarith
      _ ≤ 10 * ν.real univ * (Real.cosh (b / 2) * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul_of_nonneg_left hcosh (by positivity)
      _ = 10 * ν.real univ * Real.cosh (b / 2) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring
  have ht0 : |(1 / (2 * Real.cosh (b / 2) ^ 2)) * arcPoissonProfile ν v| ≤
      ((5 / 2 : ℝ) * ν.real univ / Real.cosh (b / 4)) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc (1 / (2 * Real.cosh (b / 2) ^ 2)) * |arcPoissonProfile ν v|
        ≤ (1 / (2 * Real.cosh (b / 2) ^ 2)) *
            (5 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul_of_nonneg_left h0 (by positivity)
      _ = (1 / Real.cosh (b / 2) ^ 2) *
            ((5 / 2 : ℝ) * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
      _ ≤ (1 / Real.cosh (b / 4)) *
            ((5 / 2 : ℝ) * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul_of_nonneg_right hinv_sq (by positivity)
      _ = ((5 / 2 : ℝ) * ν.real univ / Real.cosh (b / 4)) *
            Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring
  have ht1 : |atomW1 b * (arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b))| ≤
      (10 * ν.real univ / Real.cosh (b / 4)) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    rw [abs_mul, show |atomW1 b| = 1 / Real.cosh (b / 2) by
      unfold atomW1; rw [abs_neg, abs_of_pos (by positivity)]]
    calc (1 / Real.cosh (b / 2)) * |arcPoissonProfile ν (v - b) + arcPoissonProfile ν (v + b)|
        ≤ (1 / Real.cosh (b / 2)) *
            (10 * ν.real univ * Real.cosh (b / 4) * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul_of_nonneg_left hshift1 (by positivity)
      _ = (Real.cosh (b / 4) / Real.cosh (b / 2)) *
            (10 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
      _ ≤ (1 / Real.cosh (b / 4)) *
            (10 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul_of_nonneg_right hratio_b4 (by positivity)
      _ = (10 * ν.real univ / Real.cosh (b / 4)) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring
  have ht2 : |atomW2 b * (arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b))| ≤
      ((5 / 2 : ℝ) * ν.real univ / Real.cosh (b / 4)) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    rw [abs_mul, show |atomW2 b| = 1 / (4 * Real.cosh (b / 2) ^ 2) by
      unfold atomW2; rw [abs_of_pos (by positivity)]]
    calc (1 / (4 * Real.cosh (b / 2) ^ 2)) *
            |arcPoissonProfile ν (v - 2 * b) + arcPoissonProfile ν (v + 2 * b)|
        ≤ (1 / (4 * Real.cosh (b / 2) ^ 2)) *
            (10 * ν.real univ * Real.cosh (b / 2) * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul_of_nonneg_left hshift2 (by positivity)
      _ = (Real.cosh (b / 2) / Real.cosh (b / 2) ^ 2) *
            ((5 / 2 : ℝ) * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
      _ ≤ (1 / Real.cosh (b / 4)) *
            ((5 / 2 : ℝ) * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul_of_nonneg_right hratio_b2 (by positivity)
      _ = ((5 / 2 : ℝ) * ν.real univ / Real.cosh (b / 4)) *
            Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring
  have htri := (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add ht0 ht1)) ht2)
  have hgoal :
      ((5 / 2 : ℝ) * ν.real univ / Real.cosh (b / 4)) * Real.exp (-((1 / 4 : ℝ) * |v|)) +
        (10 * ν.real univ / Real.cosh (b / 4)) * Real.exp (-((1 / 4 : ℝ) * |v|)) +
        ((5 / 2 : ℝ) * ν.real univ / Real.cosh (b / 4)) * Real.exp (-((1 / 4 : ℝ) * |v|)) =
      (15 * ν.real univ / Real.cosh (b / 4)) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring
  linarith

/-- **Joint exponential `O(exp(−|v|/4) / cosh((log k)/2))` bound for the dyadic tail from `r = 0` to `∞` (`k ≥ 2`):**
`|arcLineInfiniteDyadicProfile k ν v − arcLineAtomicProfile (log k) ν v| ≤ (4125 · ν.real univ / cosh((log k)/2)) · exp(−|v|/4)`. -/
theorem abs_arcLineInfiniteDyadicProfile_sub_arcLineAtomicProfile_le_exp_quarter
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineInfiniteDyadicProfile k ν v - arcLineAtomicProfile (Real.log k) ν v| ≤
      (4125 * ν.real univ / Real.cosh (Real.log k / 2)) *
        Real.exp (-((1 / 4 : ℝ) * |v|)) := by
  have hk1 : 1 ≤ k := by omega
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  have hC2_pos : 0 < Real.cosh (Real.log k / 2) := Real.cosh_pos _
  have hC_pos : 0 < Real.cosh (Real.log k) := Real.cosh_pos _
  have hC2_le_C : Real.cosh (Real.log k / 2) ≤ Real.cosh (Real.log k) := by
    have h := cosh_le_cosh_two_mul (Real.log k / 2)
    rwa [show 2 * (Real.log k / 2) = Real.log k by ring] at h
  have hinv_k : ((k : ℝ))⁻¹ ≤ 1 / Real.cosh (Real.log k / 2) :=
    (inv_natCast_le_inv_cosh_log hk1).trans (one_div_le_one_div_of_le hC2_pos hC2_le_C)
  have htail1 : |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k 1 ν v| ≤
      (3300 * ν.real univ / Real.cosh (Real.log k / 2)) *
        Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    have h := abs_arcLineInfiniteDyadicProfile_sub_succ_le_exp_quarter hk 0 hν v
    simp only [zero_add, pow_zero, pow_one] at h
    calc |arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k 1 ν v|
        ≤ ((k : ℝ))⁻¹ * (3300 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) := by
          linarith
      _ ≤ (1 / Real.cosh (Real.log k / 2)) *
            (3300 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul_of_nonneg_right hinv_k (by positivity)
      _ = (3300 * ν.real univ / Real.cosh (Real.log k / 2)) *
            Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring
  have hstep0 : |arcLineDyadicTowerProfile k 1 ν v - arcLineAtomicProfile (Real.log k) ν v| ≤
      (825 * ν.real univ / Real.cosh (Real.log k / 2)) *
        Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    have hid := arcLineDyadicTowerProfile_add_sub k 0 1 ν v
    simp only [zero_add, Finset.sum_range_one, pow_zero, pow_one] at hid
    change |arcLineDyadicTowerProfile k 1 ν v - arcLineDyadicTowerProfile k 0 ν v| ≤ _
    rw [hid, abs_neg, abs_mul, abs_of_pos (by positivity)]
    have hsym := abs_arcLineSymDyadicTowerProfile_le_exp_quarter_uniform hk 0 hν v
    simp only [pow_zero, pow_one] at hsym
    have hratio : Real.cosh ((1 / 4 : ℝ) * (2 * Real.log k)) / Real.cosh (Real.log k) ≤
        1 / Real.cosh (Real.log k / 2) := by
      have h := cosh_div_cosh_two_mul_le (Real.log k / 2)
      rw [show (1 / 4 : ℝ) * (2 * Real.log k) = Real.log k / 2 by ring]
      rwa [show 2 * (Real.log k / 2) = Real.log k by ring] at h
    calc (1 / Real.cosh (Real.log k)) * |arcLineSymDyadicTowerProfile k 0 ν v|
        ≤ (1 / Real.cosh (Real.log k)) *
            ((825 * ν.real univ) * Real.cosh ((1 / 4 : ℝ) * (2 * Real.log k)) *
              Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul_of_nonneg_left hsym (by positivity)
      _ = (Real.cosh ((1 / 4 : ℝ) * (2 * Real.log k)) / Real.cosh (Real.log k)) *
            (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
      _ ≤ (1 / Real.cosh (Real.log k / 2)) *
            (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = (825 * ν.real univ / Real.cosh (Real.log k / 2)) *
            Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring
  have hsplit : arcLineInfiniteDyadicProfile k ν v - arcLineAtomicProfile (Real.log k) ν v =
      (arcLineInfiniteDyadicProfile k ν v - arcLineDyadicTowerProfile k 1 ν v) +
        (arcLineDyadicTowerProfile k 1 ν v - arcLineAtomicProfile (Real.log k) ν v) := by ring
  rw [hsplit]
  have htri := (abs_add_le _ _).trans (add_le_add htail1 hstep0)
  have hgoal :
      (3300 * ν.real univ / Real.cosh (Real.log k / 2)) * Real.exp (-((1 / 4 : ℝ) * |v|)) +
        (825 * ν.real univ / Real.cosh (Real.log k / 2)) * Real.exp (-((1 / 4 : ℝ) * |v|)) =
      (4125 * ν.real univ / Real.cosh (Real.log k / 2)) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    ring
  linarith

/-- **Joint exponential `O(exp(−|v|/4) / cosh((log k)/4))` scale-limit bound for `arcLineInfiniteDyadicProfile k ν − arcPoissonProfile ν` (`k ≥ 2`):**
For every `k ≥ 2` and `v ∈ ℝ`,
`|arcLineInfiniteDyadicProfile k ν v − arcPoissonProfile ν v| ≤ (4140 · ν.real univ / cosh((log k)/4)) · exp(−|v|/4)`. -/
theorem abs_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_exp_quarter
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v| ≤
      (4140 * ν.real univ / Real.cosh (Real.log k / 4)) *
        Real.exp (-((1 / 4 : ℝ) * |v|)) := by
  have hC4_pos : 0 < Real.cosh (Real.log k / 4) := Real.cosh_pos _
  have hC4_le_C2 : Real.cosh (Real.log k / 4) ≤ Real.cosh (Real.log k / 2) := by
    have h := cosh_le_cosh_two_mul (Real.log k / 4)
    rwa [show 2 * (Real.log k / 4) = Real.log k / 2 by ring] at h
  have hinv : 1 / Real.cosh (Real.log k / 2) ≤ 1 / Real.cosh (Real.log k / 4) :=
    one_div_le_one_div_of_le hC4_pos hC4_le_C2
  have h1 : |arcLineInfiniteDyadicProfile k ν v - arcLineAtomicProfile (Real.log k) ν v| ≤
      (4125 * ν.real univ / Real.cosh (Real.log k / 4)) *
        Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    have h := abs_arcLineInfiniteDyadicProfile_sub_arcLineAtomicProfile_le_exp_quarter hk hν v
    have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
    calc |arcLineInfiniteDyadicProfile k ν v - arcLineAtomicProfile (Real.log k) ν v|
        ≤ (4125 * ν.real univ / Real.cosh (Real.log k / 2)) *
            Real.exp (-((1 / 4 : ℝ) * |v|)) := h
      _ = (1 / Real.cosh (Real.log k / 2)) *
            (4125 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
      _ ≤ (1 / Real.cosh (Real.log k / 4)) *
            (4125 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = (4125 * ν.real univ / Real.cosh (Real.log k / 4)) *
            Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring
  have h2 := abs_arcLineAtomicProfile_sub_arcPoissonProfile_le_exp_quarter (Real.log k) hν v
  have hsplit : arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v =
      (arcLineInfiniteDyadicProfile k ν v - arcLineAtomicProfile (Real.log k) ν v) +
        (arcLineAtomicProfile (Real.log k) ν v - arcPoissonProfile ν v) := by ring
  rw [hsplit]
  have htri := (abs_add_le _ _).trans (add_le_add h1 h2)
  have hgoal :
      (4125 * ν.real univ / Real.cosh (Real.log k / 4)) * Real.exp (-((1 / 4 : ℝ) * |v|)) +
        (15 * ν.real univ / Real.cosh (Real.log k / 4)) * Real.exp (-((1 / 4 : ℝ) * |v|)) =
      (4140 * ν.real univ / Real.cosh (Real.log k / 4)) * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    ring
  linarith

/-- **Squared exponential `O((√k)⁻¹ · exp(−|v|/2))` bound for `(Φ_k(v) − B_ν(v))²` (`k ≥ 2`):**
For every `k ≥ 2` and `v ∈ ℝ`,
`(arcLineInfiniteDyadicProfile k ν v − arcPoissonProfile ν v)² ≤ 68558400 · (ν.real univ)² · (√k)⁻¹ · exp(−|v|/2)`. -/
theorem sq_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_exp_half
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    (arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v) ^ 2 ≤
      68558400 * (ν.real univ) ^ 2 * (Real.sqrt k)⁻¹ * Real.exp (-((1 / 2 : ℝ) * |v|)) := by
  have hk1 : 1 ≤ k := by omega
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  have h1 := abs_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_exp_quarter hk hν v
  have hsq := mul_self_le_mul_self (abs_nonneg _) h1
  rw [← sq, sq_abs] at hsq
  have hexp : (Real.exp (-((1 / 4 : ℝ) * |v|))) ^ 2 = Real.exp (-((1 / 2 : ℝ) * |v|)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hinv := inv_cosh_quarter_log_sq_le_four_mul_inv_sqrt hk1
  calc (arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v) ^ 2
      ≤ ((4140 * ν.real univ / Real.cosh (Real.log k / 4)) *
          Real.exp (-((1 / 4 : ℝ) * |v|))) ^ 2 := by
        simpa [sq] using hsq
    _ = (1 / Real.cosh (Real.log k / 4) ^ 2) *
          (17139600 * (ν.real univ) ^ 2 * (Real.exp (-((1 / 4 : ℝ) * |v|))) ^ 2) := by ring
    _ = (1 / Real.cosh (Real.log k / 4) ^ 2) *
          (17139600 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|))) := by rw [hexp]
    _ ≤ (4 * (Real.sqrt k)⁻¹) *
          (17139600 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = 68558400 * (ν.real univ) ^ 2 * (Real.sqrt k)⁻¹ *
          Real.exp (-((1 / 2 : ℝ) * |v|)) := by ring

/-! ### Two-sided multiplicative power-law scale-limit bounds for `arcLineInfiniteDyadicVector k ν − arcLineVector ν` on `ℝ \ {0}` -/

/-- For `x ≠ 0` and an `arcNeg`-symmetric measure `ν`,
`arcLineVector ν x = exp(−(log |x|)/2) · arcPoissonProfile ν (log |x|)`. -/
theorem arcLineVector_eq_exp_neg_half_mul_profile
    {ν : Measure ArcParam} (hν : ν.map arcNeg = ν) {x : ℝ} (hx : x ≠ 0) :
    arcLineVector ν x =
      Real.exp (-(Real.log |x| / 2)) * arcPoissonProfile ν (Real.log |x|) := by
  have habs_pos : 0 < |x| := abs_pos.mpr hx
  have heven : arcLineVector ν x = arcLineVector ν |x| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, arcLineVector_neg_of_map_arcNeg hν]
  rw [heven, ← exp_half_mul_arcLineVector ν (Real.log |x|),
    Real.exp_log habs_pos, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- **Near-infinity `O(|x|^{−3/4} / cosh((log k)/4))` scale-limit bound on `|x| ≥ 1` (`k ≥ 2`):**
For every `k ≥ 2` and `|x| ≥ 1`,
`|arcLineInfiniteDyadicVector k ν x − arcLineVector ν x| ≤ (4140 · ν.real univ / cosh((log k)/4)) · |x|^{−3/4}`. -/
theorem abs_arcLineInfiniteDyadicVector_sub_arcLineVector_le_rpow_quarter_uniform
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {x : ℝ} (hx : 1 ≤ |x|) :
    |arcLineInfiniteDyadicVector k ν x - arcLineVector ν x| ≤
      (4140 * ν.real univ / Real.cosh (Real.log k / 4)) * |x| ^ (-(3 / 4 : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have habs_pos : 0 < |x| := lt_of_lt_of_le zero_lt_one hx
  have hx0 : x ≠ 0 := abs_pos.mp habs_pos
  have hlog_nonneg : 0 ≤ Real.log |x| := Real.log_nonneg hx
  rw [arcLineInfiniteDyadicVector_eq_exp_neg_half_mul_profile hk1 hν hx0,
    arcLineVector_eq_exp_neg_half_mul_profile hν hx0, ← mul_sub,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hprof := abs_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_exp_quarter
    hk hν (Real.log |x|)
  rw [abs_of_nonneg hlog_nonneg] at hprof
  calc Real.exp (-(Real.log |x| / 2)) *
        |arcLineInfiniteDyadicProfile k ν (Real.log |x|) - arcPoissonProfile ν (Real.log |x|)|
      ≤ Real.exp (-(Real.log |x| / 2)) *
          ((4140 * ν.real univ / Real.cosh (Real.log k / 4)) *
            Real.exp (-((1 / 4 : ℝ) * Real.log |x|))) :=
        mul_le_mul_of_nonneg_left hprof (Real.exp_pos _).le
    _ = (4140 * ν.real univ / Real.cosh (Real.log k / 4)) *
          (Real.exp (-(Real.log |x| / 2)) * Real.exp (-((1 / 4 : ℝ) * Real.log |x|))) := by ring
    _ = (4140 * ν.real univ / Real.cosh (Real.log k / 4)) *
          Real.exp (Real.log |x| * (-(3 / 4 : ℝ))) := by
        rw [← Real.exp_add]; congr 2; ring
    _ = (4140 * ν.real univ / Real.cosh (Real.log k / 4)) * |x| ^ (-(3 / 4 : ℝ)) := by
        rw [Real.rpow_def_of_pos habs_pos]

/-- **Near-origin `O(|x|^{−1/4} / cosh((log k)/4))` scale-limit bound on `0 < |x| ≤ 1` (`k ≥ 2`):**
For every `k ≥ 2` and `0 < |x| ≤ 1`,
`|arcLineInfiniteDyadicVector k ν x − arcLineVector ν x| ≤ (4140 · ν.real univ / cosh((log k)/4)) · |x|^{−1/4}`. -/
theorem abs_arcLineInfiniteDyadicVector_sub_arcLineVector_le_rpow_quarter_near_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {x : ℝ} (hx0 : x ≠ 0) (hx1 : |x| ≤ 1) :
    |arcLineInfiniteDyadicVector k ν x - arcLineVector ν x| ≤
      (4140 * ν.real univ / Real.cosh (Real.log k / 4)) * |x| ^ (-(1 / 4 : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have habs_pos : 0 < |x| := abs_pos.mpr hx0
  have hlog_nonpos : Real.log |x| ≤ 0 := Real.log_nonpos habs_pos.le hx1
  rw [arcLineInfiniteDyadicVector_eq_exp_neg_half_mul_profile hk1 hν hx0,
    arcLineVector_eq_exp_neg_half_mul_profile hν hx0, ← mul_sub,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hprof := abs_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_exp_quarter
    hk hν (Real.log |x|)
  rw [abs_of_nonpos hlog_nonpos] at hprof
  calc Real.exp (-(Real.log |x| / 2)) *
        |arcLineInfiniteDyadicProfile k ν (Real.log |x|) - arcPoissonProfile ν (Real.log |x|)|
      ≤ Real.exp (-(Real.log |x| / 2)) *
          ((4140 * ν.real univ / Real.cosh (Real.log k / 4)) *
            Real.exp (-((1 / 4 : ℝ) * -Real.log |x|))) :=
        mul_le_mul_of_nonneg_left hprof (Real.exp_pos _).le
    _ = (4140 * ν.real univ / Real.cosh (Real.log k / 4)) *
          (Real.exp (-(Real.log |x| / 2)) * Real.exp (-((1 / 4 : ℝ) * -Real.log |x|))) := by ring
    _ = (4140 * ν.real univ / Real.cosh (Real.log k / 4)) *
          Real.exp (Real.log |x| * (-(1 / 4 : ℝ))) := by
        rw [← Real.exp_add]; congr 2; ring
    _ = (4140 * ν.real univ / Real.cosh (Real.log k / 4)) * |x| ^ (-(1 / 4 : ℝ)) := by
        rw [Real.rpow_def_of_pos habs_pos]

/-! ### Strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert norm convergence to `arcLineVector ν` and cross-scale Cauchy bound across `|l| < 1/4` -/

/-- Exact strip-weighted `L²((0, ∞), x^{2l} dx) ≃ L²(ℝ, e^{2lv} dv)` energy identity for
`arcLineVector ν`. -/
theorem setIntegral_Ioi_rpow_two_mul_sq_arcLineVector_eq
    (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineVector ν x) ^ 2) =
      ∫ v : ℝ, Real.exp (2 * l * v) * (arcPoissonProfile ν v) ^ 2 := by
  rw [setIntegral_Ioi_rpow_two_mul_sq_eq_integral_exp_two_mul_sq]
  simp_rw [exp_half_mul_arcLineVector ν]

/-- Exact strip-weighted `L²((0, ∞), x^{2l} dx) ≃ L²(ℝ, e^{2lv} dv)` difference-energy identity
between `arcLineInfiniteDyadicVector k ν` and `arcLineVector ν` (`k ≥ 1`). -/
theorem setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_arcLineVector_eq
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x - arcLineVector ν x) ^ 2) =
      ∫ v : ℝ,
        Real.exp (2 * l * v) *
          (arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v) ^ 2 := by
  rw [setIntegral_Ioi_rpow_two_mul_sq_eq_integral_exp_two_mul_sq]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [mul_sub, exp_half_mul_arcLineInfiniteDyadicVector hk ν v, exp_half_mul_arcLineVector ν v]

/-- **Quantitative `O((√k)⁻¹ / (1/4 − |l|))` strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert norm
convergence of `arcLineInfiniteDyadicVector k ν` to `arcLineVector ν` across `|l| < 1/4` (`k ≥ 2`):**
`∫_{x > 0} x^{2l} (V_k(x) − arcLineVector ν x)² dx ≤ (68558400 · (ν.real univ)² / (1/4 − |l|)) · (√k)⁻¹`. -/
theorem setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_arcLineVector_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 4) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x - arcLineVector ν x) ^ 2) ≤
      (68558400 * (ν.real univ) ^ 2 / (1 / 4 - |l|)) * (Real.sqrt k)⁻¹ := by
  have hk1 : 1 ≤ k := by omega
  have hcl : 0 < 1 / 2 - 2 * |l| := by linarith
  rw [setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_arcLineVector_eq hk1 ν l]
  set B := 68558400 * (ν.real univ) ^ 2 * (Real.sqrt k)⁻¹
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 2 - 2 * |l|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hcl).const_mul B
  have hpoint : ∀ v : ℝ,
      Real.exp (2 * l * v) *
          (arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v) ^ 2 ≤
        B * Real.exp (-((1 / 2 - 2 * |l|) * |v|)) := fun v => by
    have hexp : Real.exp (2 * l * v) ≤ Real.exp (2 * |l| * |v|) := by
      rw [Real.exp_le_exp]
      have := le_abs_self (l * v)
      rw [abs_mul] at this
      linarith
    have hsq := sq_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_exp_half hk hν v
    calc Real.exp (2 * l * v) *
            (arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v) ^ 2
        ≤ Real.exp (2 * |l| * |v|) * (B * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
          mul_le_mul hexp hsq (sq_nonneg _) (Real.exp_pos _).le
      _ = B * (Real.exp (2 * |l| * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by ring
      _ = B * Real.exp (-((1 / 2 - 2 * |l|) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring
  have hcont : Continuous (fun v : ℝ =>
      Real.exp (2 * l * v) *
        (arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v) ^ 2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (((continuous_arcLineInfiniteDyadicProfile hk ν).sub (continuous_arcPoissonProfile ν)).pow 2)
  have hint : Integrable (fun v : ℝ =>
      Real.exp (2 * l * v) *
        (arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v) ^ 2) :=
    hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
      exact hpoint v)
  calc (∫ v : ℝ,
          Real.exp (2 * l * v) *
            (arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v) ^ 2)
      ≤ ∫ v : ℝ, B * Real.exp (-((1 / 2 - 2 * |l|) * |v|)) :=
        integral_mono hint hdom hpoint
    _ = B * (2 / (1 / 2 - 2 * |l|)) := by
        rw [integral_const_mul, integral_rexp_neg_mul_abs hcl]
    _ = (68558400 * (ν.real univ) ^ 2 / (1 / 4 - |l|)) * (Real.sqrt k)⁻¹ := by
        dsimp [B]
        have hne1 : 1 / 4 - |l| ≠ 0 := by linarith
        have hne2 : 1 / 2 - 2 * |l| ≠ 0 := by linarith
        field_simp
        ring

/-- **Asymptotic `k → ∞` convergence in strip-weighted `L²((0, ∞), x^{2l} dx)` norm across `|l| < 1/4`:**
`∫_{x > 0} x^{2l} (V_k(x) − arcLineVector ν x)² dx → 0` as `k → ∞`. -/
theorem tendsto_setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_arcLineVector_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl : |l| < 1 / 4) :
    Tendsto (fun k : ℕ =>
      ∫ x in Ioi (0 : ℝ),
        x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x - arcLineVector ν x) ^ 2)
      atTop (𝓝 0) := by
  set C := 68558400 * (ν.real univ) ^ 2 / (1 / 4 - |l|)
  have ht : Tendsto (fun k : ℕ => C * (Real.sqrt k)⁻¹) atTop (𝓝 0) := by
    simpa using
      ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop).const_mul C
  refine squeeze_zero' ?_ ?_ ht
  · filter_upwards [eventually_ge_atTop 2] with k _
    exact setIntegral_nonneg measurableSet_Ioi fun x hx =>
      mul_nonneg (Real.rpow_pos_of_pos hx _).le (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 2] with k hk
    exact setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_arcLineVector_le hk hν hl

/-- **Quantitative cross-scale Cauchy bound in strip-weighted `L²((0, ∞), x^{2l} dx)` between any
two scales `k₁, k₂ ≥ 2` across `|l| < 1/4`:**
`∫_{x > 0} x^{2l} (V_{k₁}(x) − V_{k₂}(x))² dx ≤ (137116800 · (ν.real univ)² / (1/4 − |l|)) · ((√k₁)⁻¹ + (√k₂)⁻¹)`. -/
theorem setIntegral_Ioi_rpow_two_mul_sq_sub_arcLineInfiniteDyadicVector_le_cauchy
    {k₁ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl : |l| < 1 / 4) :
    (∫ x in Ioi (0 : ℝ),
        x ^ (2 * l) *
          (arcLineInfiniteDyadicVector k₁ ν x - arcLineInfiniteDyadicVector k₂ ν x) ^ 2) ≤
      (137116800 * (ν.real univ) ^ 2 / (1 / 4 - |l|)) *
        ((Real.sqrt k₁)⁻¹ + (Real.sqrt k₂)⁻¹) := by
  have hk₁1 : 1 ≤ k₁ := by omega
  have hk₂1 : 1 ≤ k₂ := by omega
  have hcl : 0 < 1 / 2 - 2 * |l| := by linarith
  have hlhs : (∫ x in Ioi (0 : ℝ),
        x ^ (2 * l) *
          (arcLineInfiniteDyadicVector k₁ ν x - arcLineInfiniteDyadicVector k₂ ν x) ^ 2) =
      ∫ v : ℝ,
        Real.exp (2 * l * v) *
          (arcLineInfiniteDyadicProfile k₁ ν v - arcLineInfiniteDyadicProfile k₂ ν v) ^ 2 := by
    rw [setIntegral_Ioi_rpow_two_mul_sq_eq_integral_exp_two_mul_sq]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only
    rw [mul_sub, exp_half_mul_arcLineInfiniteDyadicVector hk₁1 ν v,
      exp_half_mul_arcLineInfiniteDyadicVector hk₂1 ν v]
  rw [hlhs]
  set B := 137116800 * (ν.real univ) ^ 2 * ((Real.sqrt k₁)⁻¹ + (Real.sqrt k₂)⁻¹)
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 2 - 2 * |l|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hcl).const_mul B
  have hpoint : ∀ v : ℝ,
      Real.exp (2 * l * v) *
          (arcLineInfiniteDyadicProfile k₁ ν v - arcLineInfiniteDyadicProfile k₂ ν v) ^ 2 ≤
        B * Real.exp (-((1 / 2 - 2 * |l|) * |v|)) := fun v => by
    have hexp : Real.exp (2 * l * v) ≤ Real.exp (2 * |l| * |v|) := by
      rw [Real.exp_le_exp]
      have := le_abs_self (l * v)
      rw [abs_mul] at this
      linarith
    have hsq1 := sq_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_exp_half hk₁ hν v
    have hsq2 := sq_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_exp_half hk₂ hν v
    have hquad : (arcLineInfiniteDyadicProfile k₁ ν v - arcLineInfiniteDyadicProfile k₂ ν v) ^ 2 ≤
        2 * (arcLineInfiniteDyadicProfile k₁ ν v - arcPoissonProfile ν v) ^ 2 +
          2 * (arcLineInfiniteDyadicProfile k₂ ν v - arcPoissonProfile ν v) ^ 2 := by
      have : 0 ≤ ((arcLineInfiniteDyadicProfile k₁ ν v - arcPoissonProfile ν v) +
          (arcLineInfiniteDyadicProfile k₂ ν v - arcPoissonProfile ν v)) ^ 2 := sq_nonneg _
      linarith
    have hsum : (arcLineInfiniteDyadicProfile k₁ ν v - arcLineInfiniteDyadicProfile k₂ ν v) ^ 2 ≤
        B * Real.exp (-((1 / 2 : ℝ) * |v|)) := by
      dsimp [B]
      linarith
    calc Real.exp (2 * l * v) *
            (arcLineInfiniteDyadicProfile k₁ ν v - arcLineInfiniteDyadicProfile k₂ ν v) ^ 2
        ≤ Real.exp (2 * |l| * |v|) * (B * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
          mul_le_mul hexp hsum (sq_nonneg _) (Real.exp_pos _).le
      _ = B * (Real.exp (2 * |l| * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by ring
      _ = B * Real.exp (-((1 / 2 - 2 * |l|) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring
  have hcont : Continuous (fun v : ℝ =>
      Real.exp (2 * l * v) *
        (arcLineInfiniteDyadicProfile k₁ ν v - arcLineInfiniteDyadicProfile k₂ ν v) ^ 2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (((continuous_arcLineInfiniteDyadicProfile hk₁ ν).sub
        (continuous_arcLineInfiniteDyadicProfile hk₂ ν)).pow 2)
  have hint : Integrable (fun v : ℝ =>
      Real.exp (2 * l * v) *
        (arcLineInfiniteDyadicProfile k₁ ν v - arcLineInfiniteDyadicProfile k₂ ν v) ^ 2) :=
    hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
      exact hpoint v)
  calc (∫ v : ℝ,
          Real.exp (2 * l * v) *
            (arcLineInfiniteDyadicProfile k₁ ν v - arcLineInfiniteDyadicProfile k₂ ν v) ^ 2)
      ≤ ∫ v : ℝ, B * Real.exp (-((1 / 2 - 2 * |l|) * |v|)) :=
        integral_mono hint hdom hpoint
    _ = B * (2 / (1 / 2 - 2 * |l|)) := by
        rw [integral_const_mul, integral_rexp_neg_mul_abs hcl]
    _ = (137116800 * (ν.real univ) ^ 2 / (1 / 4 - |l|)) *
          ((Real.sqrt k₁)⁻¹ + (Real.sqrt k₂)⁻¹) := by
        dsimp [B]
        have hne1 : 1 / 4 - |l| ≠ 0 := by linarith
        have hne2 : 1 / 2 - 2 * |l| ≠ 0 := by linarith
        field_simp
        ring

/-! ### Asymptotic `k → ∞` convergence of the strip-weighted Hilbert energy `E_k(l)` and all logarithmic energy moments `M_n(k, ν)` -/

/-- **Pointwise squared-profile difference bound with `O((√k)⁻¹ · exp(−|v|/4))` decay (`k ≥ 2`):**
`|(arcLineInfiniteDyadicProfile k ν v)² − (arcPoissonProfile ν v)²| ≤ 249000 · (ν.real univ)² · (√k)⁻¹ · exp(−|v|/4)`. -/
theorem abs_sq_arcLineInfiniteDyadicProfile_sub_sq_arcPoissonProfile_le_exp_quarter
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    |(arcLineInfiniteDyadicProfile k ν v) ^ 2 - (arcPoissonProfile ν v) ^ 2| ≤
      249000 * (ν.real univ) ^ 2 * (Real.sqrt k)⁻¹ * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
  have hdiff := abs_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_uniform hk ν v
  have h1 := abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v
  have h2 := abs_arcPoissonProfile_le_exp_mul hν (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) v
  have hsum : |arcLineInfiniteDyadicProfile k ν v + arcPoissonProfile ν v| ≤
      830 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    have := (abs_add_le _ _).trans (add_le_add h1 h2)
    linarith
  have hfac : (arcLineInfiniteDyadicProfile k ν v) ^ 2 - (arcPoissonProfile ν v) ^ 2 =
      (arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v) *
        (arcLineInfiniteDyadicProfile k ν v + arcPoissonProfile ν v) := by ring
  rw [hfac, abs_mul]
  calc |arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v| *
          |arcLineInfiniteDyadicProfile k ν v + arcPoissonProfile ν v|
      ≤ (300 * ν.real univ * (Real.sqrt k)⁻¹) *
          (830 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul hdiff hsum (abs_nonneg _) (by
          have := measureReal_nonneg (μ := ν) (s := univ); positivity)
    _ = 249000 * (ν.real univ) ^ 2 * (Real.sqrt k)⁻¹ *
          Real.exp (-((1 / 4 : ℝ) * |v|)) := by ring

/-- **Pointwise squared-profile difference bound with `O(exp(−|v|/2) / cosh((log k)/4))` decay (`k ≥ 2`):**
`|(arcLineInfiniteDyadicProfile k ν v)² − (arcPoissonProfile ν v)²| ≤ (3436200 · (ν.real univ)² / cosh((log k)/4)) · exp(−|v|/2)`. -/
theorem abs_sq_arcLineInfiniteDyadicProfile_sub_sq_arcPoissonProfile_le_exp_half
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (v : ℝ) :
    |(arcLineInfiniteDyadicProfile k ν v) ^ 2 - (arcPoissonProfile ν v) ^ 2| ≤
      (3436200 * (ν.real univ) ^ 2 / Real.cosh (Real.log k / 4)) *
        Real.exp (-((1 / 2 : ℝ) * |v|)) := by
  have hdiff := abs_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_exp_quarter hk hν v
  have h1 := abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v
  have h2 := abs_arcPoissonProfile_le_exp_mul hν (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) v
  have hsum : |arcLineInfiniteDyadicProfile k ν v + arcPoissonProfile ν v| ≤
      830 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
    have := (abs_add_le _ _).trans (add_le_add h1 h2)
    linarith
  have hfac : (arcLineInfiniteDyadicProfile k ν v) ^ 2 - (arcPoissonProfile ν v) ^ 2 =
      (arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v) *
        (arcLineInfiniteDyadicProfile k ν v + arcPoissonProfile ν v) := by ring
  rw [hfac, abs_mul]
  calc |arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v| *
          |arcLineInfiniteDyadicProfile k ν v + arcPoissonProfile ν v|
      ≤ ((4140 * ν.real univ / Real.cosh (Real.log k / 4)) *
            Real.exp (-((1 / 4 : ℝ) * |v|))) *
          (830 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
        mul_le_mul hdiff hsum (abs_nonneg _) (by
          have := measureReal_nonneg (μ := ν) (s := univ); positivity)
    _ = (3436200 * (ν.real univ) ^ 2 / Real.cosh (Real.log k / 4)) *
          (Real.exp (-((1 / 4 : ℝ) * |v|)) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
    _ = (3436200 * (ν.real univ) ^ 2 / Real.cosh (Real.log k / 4)) *
          Real.exp (-((1 / 2 : ℝ) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- Integrability of `e^{2lv} (arcPoissonProfile ν v)²` across `|l| < 1/4`. -/
theorem integrable_exp_two_mul_sq_arcPoissonProfile
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl : |l| < 1 / 4) :
    Integrable (fun v : ℝ => Real.exp (2 * l * v) * (arcPoissonProfile ν v) ^ 2) := by
  have hcl : 0 < 1 / 2 - 2 * |l| := by linarith
  set B := 25 * (ν.real univ) ^ 2
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 2 - 2 * |l|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hcl).const_mul B
  have hcont : Continuous (fun v : ℝ => Real.exp (2 * l * v) * (arcPoissonProfile ν v) ^ 2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((continuous_arcPoissonProfile ν).pow 2)
  refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  have hexp : Real.exp (2 * l * v) ≤ Real.exp (2 * |l| * |v|) := by
    rw [Real.exp_le_exp]
    have := le_abs_self (l * v)
    rw [abs_mul] at this
    linarith
  have hB := abs_arcPoissonProfile_le_exp_mul hν (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) v
  have hsq : (arcPoissonProfile ν v) ^ 2 ≤ B * Real.exp (-((1 / 2 : ℝ) * |v|)) := by
    have hmul := mul_self_le_mul_self (abs_nonneg _) hB
    rw [← sq, sq_abs] at hmul
    calc (arcPoissonProfile ν v) ^ 2
        ≤ (5 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) ^ 2 := by simpa [sq] using hmul
      _ = B * (Real.exp (-((1 / 4 : ℝ) * |v|)) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by
          dsimp [B]; ring
      _ = B * Real.exp (-((1 / 2 : ℝ) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring
  calc Real.exp (2 * l * v) * (arcPoissonProfile ν v) ^ 2
      ≤ Real.exp (2 * |l| * |v|) * (B * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
        mul_le_mul hexp hsq (sq_nonneg _) (Real.exp_pos _).le
    _ = B * (Real.exp (2 * |l| * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by ring
    _ = B * Real.exp (-((1 / 2 - 2 * |l|) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Quantitative strip-weighted Hilbert energy convergence bound across `|l| < 1/4` (`k ≥ 2`):**
`|∫_{x > 0} x^{2l} (V_k(x))² dx − ∫_{x > 0} x^{2l} (arcLineVector ν x)² dx| ≤ (3436200 · (ν.real univ)² / (1/4 − |l|)) / cosh((log k)/4)`. -/
theorem abs_setIntegral_Ioi_rpow_two_mul_sq_sub_arcLineVector_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 4) :
    |(∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineVector ν x) ^ 2)| ≤
      (3436200 * (ν.real univ) ^ 2 / (1 / 4 - |l|)) *
        (1 / Real.cosh (Real.log k / 4)) := by
  have hk1 : 1 ≤ k := by omega
  have hl2 : |l| < 1 / 2 := by linarith
  have hcl : 0 < 1 / 2 - 2 * |l| := by linarith
  rw [setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l,
    setIntegral_Ioi_rpow_two_mul_sq_arcLineVector_eq ν l,
    ← integral_sub
      (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl2)
      (integrable_exp_two_mul_sq_arcPoissonProfile hν hl)]
  set B := 3436200 * (ν.real univ) ^ 2 / Real.cosh (Real.log k / 4)
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 2 - 2 * |l|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hcl).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
        Real.exp (2 * l * v) * (arcPoissonProfile ν v) ^ 2)
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hcl] at h1
    calc |∫ v : ℝ,
            (Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
              Real.exp (2 * l * v) * (arcPoissonProfile ν v) ^ 2)|
        ≤ B * (2 / (1 / 2 - 2 * |l|)) := h1
      _ = (3436200 * (ν.real univ) ^ 2 / (1 / 4 - |l|)) *
            (1 / Real.cosh (Real.log k / 4)) := by
          dsimp [B]
          have hne1 : 1 / 4 - |l| ≠ 0 := by linarith
          have hne2 : 1 / 2 - 2 * |l| ≠ 0 := by linarith
          field_simp
          ring
  · rw [← mul_sub, Real.norm_eq_abs, abs_mul, Real.abs_exp]
    have hexp : Real.exp (2 * l * v) ≤ Real.exp (2 * |l| * |v|) := by
      rw [Real.exp_le_exp]
      have := le_abs_self (l * v)
      rw [abs_mul] at this
      linarith
    have hsq := abs_sq_arcLineInfiniteDyadicProfile_sub_sq_arcPoissonProfile_le_exp_half hk hν v
    calc Real.exp (2 * l * v) *
            |(arcLineInfiniteDyadicProfile k ν v) ^ 2 - (arcPoissonProfile ν v) ^ 2|
        ≤ Real.exp (2 * |l| * |v|) * (B * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
          mul_le_mul hexp hsq (abs_nonneg _) (Real.exp_pos _).le
      _ = B * (Real.exp (2 * |l| * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by ring
      _ = B * Real.exp (-((1 / 2 - 2 * |l|) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring

/-- **Asymptotic `k → ∞` convergence of the strip-weighted Hilbert energy `E_k(l)` across `|l| < 1/4`:**
`∫_{x > 0} x^{2l} (V_k(x))² dx → ∫_{x > 0} x^{2l} (arcLineVector ν x)² dx` as `k → ∞`. -/
theorem tendsto_setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl : |l| < 1 / 4) :
    Tendsto (fun k : ℕ =>
      ∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineVector ν x) ^ 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set C := 3436200 * (ν.real univ) ^ 2 / (1 / 4 - |l|)
  have ht : Tendsto (fun k : ℕ => C * (1 / Real.cosh (Real.log k / 4))) atTop (𝓝 0) := by
    simpa using tendsto_inv_cosh_quarter_log_atTop.const_mul C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
  filter_upwards [eventually_ge_atTop 2] with k hk
  rw [Real.norm_eq_abs]
  exact abs_setIntegral_Ioi_rpow_two_mul_sq_sub_arcLineVector_le hk hν hl

/-- Integrability of `|v|^n (arcPoissonProfile ν v)²` on `ℝ` for every `n ∈ ℕ`. -/
theorem integrable_abs_pow_mul_sq_arcPoissonProfile
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (n : ℕ) :
    Integrable (fun v : ℝ => |v| ^ n * (arcPoissonProfile ν v) ^ 2) := by
  set B := 25 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * 4 ^ n
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
    (integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 1 / 4)).const_mul B
  have hcont : Continuous (fun v : ℝ => |v| ^ n * (arcPoissonProfile ν v) ^ 2) :=
    (continuous_abs.pow n).mul ((continuous_arcPoissonProfile ν).pow 2)
  refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg v) n) (sq_nonneg _))]
  have h1 := abs_pow_le_factorial_mul_four_pow_mul_exp_quarter n v
  have hB := abs_arcPoissonProfile_le_exp_mul hν (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) v
  have hsq : (arcPoissonProfile ν v) ^ 2 ≤
      25 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|)) := by
    have hmul := mul_self_le_mul_self (abs_nonneg _) hB
    rw [← sq, sq_abs] at hmul
    calc (arcPoissonProfile ν v) ^ 2
        ≤ (5 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) ^ 2 := by simpa [sq] using hmul
      _ = 25 * (ν.real univ) ^ 2 *
            (Real.exp (-((1 / 4 : ℝ) * |v|)) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
      _ = 25 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring
  calc |v| ^ n * (arcPoissonProfile ν v) ^ 2
      ≤ ((n.factorial : ℝ) * 4 ^ n * Real.exp ((1 / 4 : ℝ) * |v|)) *
          (25 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|))) :=
        mul_le_mul h1 hsq (sq_nonneg _) (by positivity)
    _ = B * (Real.exp ((1 / 4 : ℝ) * |v|) * Real.exp (-((1 / 2 : ℝ) * |v|))) := by
        dsimp [B]; ring
    _ = B * Real.exp (-((1 / 4 : ℝ) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- Integrability of `v^n (arcPoissonProfile ν v)²` on `Ioi (0 : ℝ)` for every `n ∈ ℕ`. -/
theorem integrableOn_Ioi_zero_pow_mul_sq_arcPoissonProfile
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (n : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ n * (arcPoissonProfile ν v) ^ 2) (Ioi (0 : ℝ)) := by
  refine (integrable_abs_pow_mul_sq_arcPoissonProfile hν n).integrableOn.congr_fun
    (fun v hv => ?_) measurableSet_Ioi
  dsimp only
  rw [abs_of_pos hv]

/-- **Quantitative `O((√k)⁻¹)` convergence of the half-line logarithmic energy moment hierarchy
`M_n(k, ν) = ∫_{v > 0} v^n (Φ_k(v))² dv` (`k ≥ 2`, `n ∈ ℕ`):**
`|∫_{v > 0} v^n (Φ_k(v))² dv − ∫_{v > 0} v^n (B_ν(v))² dv| ≤ 3984000 · (ν.real univ)² · n! · 8^n · (√k)⁻¹`. -/
theorem abs_setIntegral_Ioi_zero_pow_mul_sq_sub_arcPoissonProfile_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) :
    |(∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) -
        (∫ v in Ioi (0 : ℝ), v ^ n * (arcPoissonProfile ν v) ^ 2)| ≤
      3984000 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * 8 ^ n * (Real.sqrt k)⁻¹ := by
  rw [← integral_sub
    (integrableOn_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν n)
    (integrableOn_Ioi_zero_pow_mul_sq_arcPoissonProfile hν n)]
  set B := 249000 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * 8 ^ n * (Real.sqrt k)⁻¹
  have hc8 : (0 : ℝ) < 1 / 8 := by norm_num
  have hdom : IntegrableOn (fun v : ℝ => B * Real.exp (-((1 / 8 : ℝ) * |v|))) (Ioi (0 : ℝ)) :=
    ((integrable_rexp_neg_mul_abs hc8).const_mul B).integrableOn
  have hdom_full : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 : ℝ) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc8).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
        v ^ n * (arcPoissonProfile ν v) ^ 2)
    hdom (ae_restrict_mem measurableSet_Ioi |>.mono fun v hv => ?_)
  · have hle_full : (∫ v in Ioi (0 : ℝ), B * Real.exp (-((1 / 8 : ℝ) * |v|))) ≤
        ∫ v : ℝ, B * Real.exp (-((1 / 8 : ℝ) * |v|)) := by
      refine setIntegral_le_integral hdom_full (Eventually.of_forall fun v => ?_)
      have := measureReal_nonneg (μ := ν) (s := univ)
      dsimp [B]; positivity
    have hfull_eq : (∫ v : ℝ, B * Real.exp (-((1 / 8 : ℝ) * |v|))) =
        3984000 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * 8 ^ n * (Real.sqrt k)⁻¹ := by
      rw [integral_const_mul, integral_rexp_neg_mul_abs hc8]
      dsimp [B]; ring
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hle_full.trans hfull_eq.le)
  · rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hv n)]
    have hpow : v ^ n ≤ (n.factorial : ℝ) * 8 ^ n * Real.exp ((1 / 8 : ℝ) * |v|) := by
      have h := pow_le_factorial_mul_exp_nonneg (by positivity : 0 ≤ (1 / 8 : ℝ) * |v|) n
      have hmul := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (8 : ℝ) ^ n)
      calc v ^ n
          = |v| ^ n := by rw [abs_of_pos hv]
        _ = ((1 / 8 : ℝ) * |v|) ^ n * (8 : ℝ) ^ n := by rw [← mul_pow]; ring
        _ ≤ ((n.factorial : ℝ) * Real.exp ((1 / 8 : ℝ) * |v|)) * (8 : ℝ) ^ n := hmul
        _ = (n.factorial : ℝ) * 8 ^ n * Real.exp ((1 / 8 : ℝ) * |v|) := by ring
    have hsq := abs_sq_arcLineInfiniteDyadicProfile_sub_sq_arcPoissonProfile_le_exp_quarter hk hν v
    calc v ^ n * |(arcLineInfiniteDyadicProfile k ν v) ^ 2 - (arcPoissonProfile ν v) ^ 2|
        ≤ ((n.factorial : ℝ) * 8 ^ n * Real.exp ((1 / 8 : ℝ) * |v|)) *
            (249000 * (ν.real univ) ^ 2 * (Real.sqrt k)⁻¹ *
              Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul hpow hsq (abs_nonneg _) (by positivity)
      _ = B * (Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp (-((1 / 4 : ℝ) * |v|))) := by
          dsimp [B]; ring
      _ = B * Real.exp (-((1 / 8 : ℝ) * |v|)) := by
          rw [← Real.exp_add]; congr 2; ring

/-- **Asymptotic `k → ∞` convergence of every logarithmic energy moment `M_n(k, ν)` (`n ∈ ℕ`):**
`∫_{v > 0} v^n (Φ_k(v))² dv → ∫_{v > 0} v^n (arcPoissonProfile ν v)² dv` as `k → ∞`. -/
theorem tendsto_setIntegral_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (n : ℕ) :
    Tendsto (fun k : ℕ =>
      ∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      atTop (𝓝 (∫ v in Ioi (0 : ℝ), v ^ n * (arcPoissonProfile ν v) ^ 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set C := 3984000 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * 8 ^ n
  have ht : Tendsto (fun k : ℕ => C * (Real.sqrt k)⁻¹) atTop (𝓝 0) := by
    simpa using
      ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
  filter_upwards [eventually_ge_atTop 2] with k hk
  rw [Real.norm_eq_abs]
  exact abs_setIntegral_Ioi_zero_pow_mul_sq_sub_arcPoissonProfile_le hk hν n

/-! ### Master unconditional theorem for the `k → ∞` scale-limit Hilbert and moment convergence -/

/-- **Master unconditional theorem for the quantitative `k → ∞` scale-limit convergence of the
dyadic modular arc tower to the Poisson line model.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for the infinite-horizon dyadic profile `Φ_k = arcLineInfiniteDyadicProfile k ν`, line vector
`V_k = arcLineInfiniteDyadicVector k ν`, Poisson profile `B_ν = arcPoissonProfile ν`, and Poisson
line vector `arcLineVector ν`:
1. **Uniform `O((√k)⁻¹)` `L^∞(ℝ)` and joint exponential `O(exp(−|v|/4) / cosh((log k)/4))` profile
   bounds (`k ≥ 2`, `v ∈ ℝ`):**
   `|Φ_k(v) − B_ν(v)| ≤ 300 · ν.real univ · (√k)⁻¹` and
   `|Φ_k(v) − B_ν(v)| ≤ (4140 · ν.real univ / cosh((log k)/4)) · exp(−|v|/4)`;
2. **Two-sided multiplicative power-law bounds on `ℝ \ {0}` (`k ≥ 2`):**
   `|V_k(x) − arcLineVector ν x| ≤ (4140 · ν.real univ / cosh((log k)/4)) · |x|^{−3/4}` on `|x| ≥ 1`
   and `|V_k(x) − arcLineVector ν x| ≤ (4140 · ν.real univ / cosh((log k)/4)) · |x|^{−1/4}` on `0 < |x| ≤ 1`;
3. **Strip-weighted `L²((0, ∞), x^{2l} dx)` Hilbert norm convergence (`k ≥ 2`, `|l| < 1/4`):**
   `∫_{x > 0} x^{2l} (V_k(x) − arcLineVector ν x)² dx ≤ (68558400 · (ν.real univ)² / (1/4 − |l|)) · (√k)⁻¹ → 0` as `k → ∞`;
4. **Cross-scale Cauchy inequality in strip-weighted `L²((0, ∞), x^{2l} dx)` (`k₁, k₂ ≥ 2`, `|l| < 1/4`):**
   `∫_{x > 0} x^{2l} (V_{k₁}(x) − V_{k₂}(x))² dx ≤ (137116800 · (ν.real univ)² / (1/4 − |l|)) · ((√k₁)⁻¹ + (√k₂)⁻¹)`;
5. **Asymptotic `k → ∞` convergence of the strip-weighted Hilbert energy across `|l| < 1/4`:**
   `∫_{x > 0} x^{2l} (V_k(x))² dx → ∫_{x > 0} x^{2l} (arcLineVector ν x)² dx` as `k → ∞`;
6. **Asymptotic `k → ∞` convergence of all logarithmic energy moments (`n ∈ ℕ`):**
   `∫_{v > 0} v^n (Φ_k(v))² dv → ∫_{v > 0} v^n (B_ν(v))² dv` at rate `O(n! · 8^n · (√k)⁻¹)`. -/
theorem exists_dyadic_scaleLimit_hilbertConvergence_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ v : ℝ,
          |arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v| ≤
            300 * ν.real univ * (Real.sqrt k)⁻¹ ∧
          |arcLineInfiniteDyadicProfile k ν v - arcPoissonProfile ν v| ≤
            (4140 * ν.real univ / Real.cosh (Real.log k / 4)) *
              Real.exp (-((1 / 4 : ℝ) * |v|))) ∧
        (∀ x : ℝ, 1 ≤ |x| →
          |arcLineInfiniteDyadicVector k ν x - arcLineVector ν x| ≤
            (4140 * ν.real univ / Real.cosh (Real.log k / 4)) * |x| ^ (-(3 / 4 : ℝ))) ∧
        (∀ x : ℝ, x ≠ 0 → |x| ≤ 1 →
          |arcLineInfiniteDyadicVector k ν x - arcLineVector ν x| ≤
            (4140 * ν.real univ / Real.cosh (Real.log k / 4)) * |x| ^ (-(1 / 4 : ℝ))) ∧
        (∀ l : ℝ, |l| < 1 / 4 →
          (∫ x in Ioi (0 : ℝ),
              x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x - arcLineVector ν x) ^ 2) ≤
            (68558400 * (ν.real univ) ^ 2 / (1 / 4 - |l|)) * (Real.sqrt k)⁻¹) ∧
        (∀ n : ℕ,
          |(∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) -
              (∫ v in Ioi (0 : ℝ), v ^ n * (arcPoissonProfile ν v) ^ 2)| ≤
            3984000 * (ν.real univ) ^ 2 * (n.factorial : ℝ) * 8 ^ n * (Real.sqrt k)⁻¹)) ∧
      (∀ k₁ k₂ : ℕ, 2 ≤ k₁ → 2 ≤ k₂ → ∀ l : ℝ, |l| < 1 / 4 →
        (∫ x in Ioi (0 : ℝ),
            x ^ (2 * l) *
              (arcLineInfiniteDyadicVector k₁ ν x - arcLineInfiniteDyadicVector k₂ ν x) ^ 2) ≤
          (137116800 * (ν.real univ) ^ 2 / (1 / 4 - |l|)) *
            ((Real.sqrt k₁)⁻¹ + (Real.sqrt k₂)⁻¹)) ∧
      (∀ l : ℝ, |l| < 1 / 4 →
        Tendsto (fun k : ℕ =>
          ∫ x in Ioi (0 : ℝ),
            x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x - arcLineVector ν x) ^ 2)
          atTop (𝓝 0) ∧
        Tendsto (fun k : ℕ =>
          ∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)
          atTop (𝓝 (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineVector ν x) ^ 2))) ∧
      (∀ n : ℕ,
        Tendsto (fun k : ℕ =>
          ∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
          atTop (𝓝 (∫ v in Ioi (0 : ℝ), v ^ n * (arcPoissonProfile ν v) ^ 2))) := by
  obtain ⟨ν, hfin, hne, hsym, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hne, hsym,
    fun k hk =>
      ⟨fun v =>
        ⟨abs_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_uniform hk ν v,
         abs_arcLineInfiniteDyadicProfile_sub_arcPoissonProfile_le_exp_quarter hk hsym v⟩,
       fun x hx =>
        abs_arcLineInfiniteDyadicVector_sub_arcLineVector_le_rpow_quarter_uniform hk hsym hx,
       fun x hx0 hx1 =>
        abs_arcLineInfiniteDyadicVector_sub_arcLineVector_le_rpow_quarter_near_zero hk hsym hx0 hx1,
       fun l hl =>
        setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_arcLineVector_le hk hsym hl,
       fun n =>
        abs_setIntegral_Ioi_zero_pow_mul_sq_sub_arcPoissonProfile_le hk hsym n⟩,
    fun k₁ k₂ hk₁ hk₂ l hl =>
      setIntegral_Ioi_rpow_two_mul_sq_sub_arcLineInfiniteDyadicVector_le_cauchy hk₁ hk₂ hsym hl,
    fun l hl =>
      ⟨tendsto_setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_sub_arcLineVector_atTop
        hsym hl,
       tendsto_setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_atTop hsym hl⟩,
    fun n =>
      tendsto_setIntegral_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile_atTop hsym n⟩

end

end RHTower
