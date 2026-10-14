import GaloisForLFunctions.RHTower.ModularArcAtomicSublatticeBlind

/-!
# Forward integer-dilation pole-filtered modular arc witnesses blind at all positive integers

In `ModularArcAtomicSublatticeBlind`, applying the symmetric 5-point atomic pole filter at
`b = log k` (`k ≥ 2`) to the continuous modular arc witness `ν` produced a self-reciprocal
(`h(1/x) = |x| h(x)`) function `arcLineAtomicVector (log k) ν` in the full `O(e^{−3|v|/2})` Weil
decay class with zero mean and strict positive definiteness on the critical line, whose derivative
is blind along the infinite arithmetic progression `2π k²(m+1)` (`m ∈ ℕ`).

In this module we apply the forward dilation `D_{2 log k}` (`x ↦ x / k²`, weighted by `k⁻¹`) to
`arcLineAtomicVector (log k) ν`, defining:

`G_{k,ν}(x) = k⁻¹ H_{log k, ν}(x / k²)`  (`arcLineForwardAtomicVector k ν`),

with derivative `G_{k,ν}'(x) = k⁻³ H_{log k, ν}'(x / k²)` (`arcLineForwardAtomicDeriv k ν`) and
log-scale profile `e^{v/2} G_{k,ν}(e^v) = arcLineAtomicProfile (log k) ν (v − 2 log k)`
(`arcLineForwardAtomicProfile k ν v`).

Because shifting the five dilation exponents `{−2 log k, −log k, 0, log k, 2 log k}` by `+2 log k`
turns all five shifts into **non-negative integer logarithms** `{0, log k, 2 log k, 3 log k, 4 log k}`,
every positive integer frequency `2π(n+1)` is scaled into `{2π(n+1)k^j : 0 ≤ j ≤ 4} ⊂ 2π ℕ⁺`.

## Main results

1. **Full two-sided `O(e^{−3|v|/2})` Weil decay class and zero mean:**
   - `hasDerivAt_arcLineForwardAtomicVector`: `HasDerivAt (arcLineForwardAtomicVector k ν) (arcLineForwardAtomicDeriv k ν x) x`.
   - `arcLineForwardAtomicVector_neg_of_map_arcNeg`, `arcLineForwardAtomicDeriv_neg_of_map_arcNeg`:
     `G_{k,ν}` is even and `G_{k,ν}'` is odd.
   - `abs_arcLineForwardAtomicProfile_le`: for `k ≥ 1` and symmetric `ν`,
     `|e^{v/2} G_{k,ν}(e^v)| ≤ 5 · ν.real univ · atomMass (log k) · k⁶ · e^{−3|v|/2}` for all `v ∈ ℝ`
     (both `v → +∞` and `v → −∞` logarithmic edges are canceled).
   - `integral_arcLineForwardAtomicVector_eq_zero`: `∫ G_{k,ν}(x) dx = 0`.
2. **Shifted inversion covariance and critical-line spectral positivity:**
   - `arcLineForwardAtomicVector_inv_scaled`: `G_{k,ν}(k⁴ / x) = (|x| / k²) G_{k,ν}(x)` for `x ≠ 0`.
   - `integral_cos_mul_arcLineForwardAtomicProfile_add` and
     `integral_cos_mul_arcLineForwardAtomicProfile_add_pos`: the `2 log k`-centered log-profile is
     even and strictly positive definite on the critical line (`∀ τ ∈ ℝ, 0 < ∫ cos(τv) P(v + 2 log k) dv`),
     while the unshifted cosine transform is `cos(2τ log k) (1 − cos(τ log k)/cosh(½ log k))² B̂_ν(τ)`.
3. **Simultaneous blindness at EVERY nonzero integer frequency (`∀ n ∈ ℕ`):**
   - `integral_arcLineForwardAtomicDeriv_mul_sin_eq_zero`: for any integer-blind measure `ν` and any
     `k ≥ 1`, `∫ G_{k,ν}'(x) sin(arcFreq n · x) dx = 0` for **all** `n ∈ ℕ`.
   - `integral_arcLineForwardAtomicDeriv_mul_cos_eq_zero`: for any symmetric `ν`,
     `∫ G_{k,ν}'(x) cos(cx) dx = 0` for **all** `c ∈ ℝ`.
   - `exists_forwardLogNat_decayClass_allInteger_blind_witness`: unconditional master existence
     theorem for every `k ≥ 2`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Definition and basic calculus of `arcLineForwardAtomicVector` -/

/-- The forward-dilated 5-point pole-filtered modular arc line vector:
`G_{k,ν}(x) = k⁻¹ · arcLineAtomicVector (log k) ν (x / k²)`. -/
def arcLineForwardAtomicVector (k : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  (k : ℝ)⁻¹ * arcLineAtomicVector (Real.log k) ν (x * ((k : ℝ) ^ 2)⁻¹)

/-- Its derivative `G_{k,ν}'(x) = k⁻³ · arcLineAtomicDeriv (log k) ν (x / k²)`. -/
def arcLineForwardAtomicDeriv (k : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  ((k : ℝ) ^ 3)⁻¹ * arcLineAtomicDeriv (Real.log k) ν (x * ((k : ℝ) ^ 2)⁻¹)

/-- Its log-scale profile `arcLineAtomicProfile (log k) ν (v − 2 log k)`. -/
def arcLineForwardAtomicProfile (k : ℕ) (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  arcLineAtomicProfile (Real.log k) ν (v - 2 * Real.log k)

theorem hasDerivAt_arcLineForwardAtomicVector (k : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (x : ℝ) :
    HasDerivAt (arcLineForwardAtomicVector k ν) (arcLineForwardAtomicDeriv k ν x) x := by
  have hc : HasDerivAt (fun x' : ℝ => x' * ((k : ℝ) ^ 2)⁻¹) (((k : ℝ) ^ 2)⁻¹) x := by
    simpa using (hasDerivAt_id x).mul_const (((k : ℝ) ^ 2)⁻¹)
  have h := ((hasDerivAt_arcLineAtomicVector (Real.log k) ν
    (x * ((k : ℝ) ^ 2)⁻¹)).comp x hc).const_mul ((k : ℝ)⁻¹)
  refine h.congr_deriv ?_
  unfold arcLineForwardAtomicDeriv
  ring

theorem continuous_arcLineForwardAtomicVector (k : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] :
    Continuous (arcLineForwardAtomicVector k ν) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_arcLineForwardAtomicVector k ν x).continuousAt

theorem arcLineForwardAtomicVector_neg_of_map_arcNeg (k : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineForwardAtomicVector k ν (-x) = arcLineForwardAtomicVector k ν x := by
  unfold arcLineForwardAtomicVector
  rw [neg_mul, arcLineAtomicVector_neg_of_map_arcNeg _ hν]

theorem arcLineForwardAtomicDeriv_neg_of_map_arcNeg (k : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineForwardAtomicDeriv k ν (-x) = -arcLineForwardAtomicDeriv k ν x := by
  unfold arcLineForwardAtomicDeriv
  rw [neg_mul, arcLineAtomicDeriv_neg_of_map_arcNeg _ hν, mul_neg]

/-- **`k²`-centered inversion covariance**: `G_{k,ν}(k⁴ / x) = (|x| / k²) G_{k,ν}(x)` for `x ≠ 0`. -/
theorem arcLineForwardAtomicVector_inv_scaled {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam)
    {x : ℝ} (hx : x ≠ 0) :
    arcLineForwardAtomicVector k ν ((k : ℝ) ^ 4 / x) =
      |x| / (k : ℝ) ^ 2 * arcLineForwardAtomicVector k ν x := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hxne : x * ((k : ℝ) ^ 2)⁻¹ ≠ 0 := mul_ne_zero hx (inv_ne_zero (pow_ne_zero 2 hkne))
  unfold arcLineForwardAtomicVector
  have e : (k : ℝ) ^ 4 / x * ((k : ℝ) ^ 2)⁻¹ = 1 / (x * ((k : ℝ) ^ 2)⁻¹) := by
    field_simp
  rw [e, arcLineAtomicVector_inv (Real.log k) ν hxne, abs_mul,
    abs_of_pos (inv_pos.mpr (pow_pos hkpos 2))]
  ring

theorem exp_half_mul_arcLineForwardAtomicVector {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) (v : ℝ) :
    Real.exp (v / 2) * arcLineForwardAtomicVector k ν (Real.exp v) =
      arcLineForwardAtomicProfile k ν v := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  unfold arcLineForwardAtomicVector arcLineForwardAtomicProfile
  have he2 : ((k : ℝ) ^ 2)⁻¹ = Real.exp (-(2 * Real.log k)) := by
    rw [Real.exp_neg, show (2 : ℝ) * Real.log k = ((2 : ℕ) : ℝ) * Real.log k by norm_num,
      Real.exp_nat_mul, Real.exp_log hkpos]
  have he1 : (k : ℝ)⁻¹ = Real.exp (-(Real.log k)) := by
    rw [Real.exp_neg, Real.exp_log hkpos]
  have e1 : Real.exp v * ((k : ℝ) ^ 2)⁻¹ = Real.exp (v - 2 * Real.log k) := by
    rw [he2, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (v / 2) * (k : ℝ)⁻¹ = Real.exp ((v - 2 * Real.log k) / 2) := by
    rw [he1, ← Real.exp_add]; congr 1; ring
  rw [e1, ← mul_assoc, e2, exp_half_mul_arcLineAtomicVector]

/-! ### Full two-sided `O(e^{−3|v|/2})` Weil decay class and zero mean -/

/-- **Two-sided `O(e^{−3|v|/2})` Weil decay-class bound for `arcLineForwardAtomicProfile`.** -/
theorem abs_arcLineForwardAtomicProfile_le {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineForwardAtomicProfile k ν v| ≤
      5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 * Real.exp (-(3 * |v| / 2)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  unfold arcLineForwardAtomicProfile
  have hprof := abs_arcLineAtomicProfile_le hb hν (v - 2 * Real.log k)
  have hexp3 : Real.exp (3 * Real.log k) = (k : ℝ) ^ 3 := by
    rw [show (3 : ℝ) * Real.log k = ((3 : ℕ) : ℝ) * Real.log k by norm_num,
      Real.exp_nat_mul, Real.exp_log hkpos]
  have hshift : Real.exp (-(3 * |v - 2 * Real.log k| / 2)) ≤
      (k : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2)) := by
    rw [← hexp3, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have habs : |v| - |2 * Real.log k| ≤ |v - 2 * Real.log k| := abs_sub_abs_le_abs_sub v _
    have hlog : |2 * Real.log k| = 2 * Real.log k := abs_of_nonneg (by positivity)
    linarith
  have hC0 : 0 ≤ 5 * ν.real univ * atomMass (Real.log k) * Real.exp (3 * Real.log k) := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    have := atomMass_nonneg (Real.log k)
    positivity
  calc |arcLineAtomicProfile (Real.log k) ν (v - 2 * Real.log k)|
      ≤ 5 * ν.real univ * atomMass (Real.log k) * Real.exp (3 * Real.log k) *
          Real.exp (-(3 * |v - 2 * Real.log k| / 2)) := hprof
    _ ≤ 5 * ν.real univ * atomMass (Real.log k) * Real.exp (3 * Real.log k) *
          ((k : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2))) :=
        mul_le_mul_of_nonneg_left hshift hC0
    _ = 5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 * Real.exp (-(3 * |v| / 2)) := by
        rw [hexp3]; ring

theorem integrable_arcLineForwardAtomicVector {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Integrable (arcLineForwardAtomicVector k ν) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  exact ((integrable_arcLineAtomicVector hb hν).comp_mul_right'
    (inv_ne_zero (pow_ne_zero 2 hkpos.ne'))).const_mul ((k : ℝ)⁻¹)

theorem integrable_arcLineForwardAtomicDeriv {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineForwardAtomicDeriv k ν) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  exact ((integrable_arcLineAtomicDeriv (Real.log k) ν).comp_mul_right'
    (inv_ne_zero (pow_ne_zero 2 hkpos.ne'))).const_mul (((k : ℝ) ^ 3)⁻¹)

/-- **Zero mean of `arcLineForwardAtomicVector`.** -/
theorem integral_arcLineForwardAtomicVector_eq_zero {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    ∫ x, arcLineForwardAtomicVector k ν x = 0 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  unfold arcLineForwardAtomicVector
  rw [integral_const_mul, Measure.integral_comp_mul_right
    (arcLineAtomicVector (Real.log k) ν) (((k : ℝ) ^ 2)⁻¹),
    integral_arcLineAtomicVector_eq_zero hb hν, smul_zero, mul_zero]

/-! ### Critical-line spectral transforms and centered strict positive definiteness -/

theorem arcLineForwardAtomicProfile_add_two_log (k : ℕ) (ν : Measure ArcParam) (v : ℝ) :
    arcLineForwardAtomicProfile k ν (v + 2 * Real.log k) =
      arcLineAtomicProfile (Real.log k) ν v := by
  unfold arcLineForwardAtomicProfile
  rw [add_sub_cancel_right]

/-- The `2 log k`-centered log-profile of `arcLineForwardAtomicVector k ν` is even. -/
theorem arcLineForwardAtomicProfile_add_neg (k : ℕ) (ν : Measure ArcParam) (v : ℝ) :
    arcLineForwardAtomicProfile k ν (-v + 2 * Real.log k) =
      arcLineForwardAtomicProfile k ν (v + 2 * Real.log k) := by
  rw [arcLineForwardAtomicProfile_add_two_log, arcLineForwardAtomicProfile_add_two_log,
    arcLineAtomicProfile_neg]

/-- **Strict positive definiteness of the `2 log k`-centered log-profile on the critical line.** -/
theorem integral_cos_mul_arcLineForwardAtomicProfile_add_pos {k : ℕ} (hk : 2 ≤ k)
    (ν : Measure ArcParam) [IsFiniteMeasure ν]
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * arcLineForwardAtomicProfile k ν (v + 2 * Real.log k) := by
  have hkgt1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le one_lt_two hk)
  have hb : 0 < Real.log k := Real.log_pos hkgt1
  simp_rw [arcLineForwardAtomicProfile_add_two_log]
  exact integral_cos_mul_arcLineAtomicProfile_pos hb ν hpd τ

/-! ### Simultaneous blindness at ALL positive integer frequencies `2π(n+1)` (`n ∈ ℕ`) -/

/-- For a symmetric measure `ν`, all cosine moments of `arcLineForwardAtomicDeriv k ν` vanish. -/
theorem integral_arcLineForwardAtomicDeriv_mul_cos_eq_zero (k : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (c : ℝ) :
    ∫ x, arcLineForwardAtomicDeriv k ν x * Real.cos (c * x) = 0 := by
  have h := integral_neg_eq_self
    (fun x : ℝ => arcLineForwardAtomicDeriv k ν x * Real.cos (c * x)) volume
  have e : (fun x : ℝ => arcLineForwardAtomicDeriv k ν (-x) * Real.cos (c * -x)) =
      fun x => -(arcLineForwardAtomicDeriv k ν x * Real.cos (c * x)) := by
    funext x
    rw [arcLineForwardAtomicDeriv_neg_of_map_arcNeg k hν, mul_neg, Real.cos_neg, neg_mul]
  rw [e, integral_neg] at h
  linarith

/-- **Simultaneous sine blindness at EVERY positive integer frequency `arcFreq n = 2π(n+1)`.**
Because `arcLineForwardAtomicDeriv k ν` rescales `arcLineAtomicDeriv (log k) ν` by `x ↦ x / k²`,
its sine moment at `arcFreq n` is `k⁻¹` times the sine moment of `arcLineAtomicDeriv (log k) ν` at
`arcFreq (k²(n+1) − 1)`, which vanishes identically for **all** `n ∈ ℕ`. -/
theorem integral_arcLineForwardAtomicDeriv_mul_sin_eq_zero {ν : Measure ArcParam}
    [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    ∫ x, arcLineForwardAtomicDeriv k ν x * Real.sin (arcFreq n * x) = 0 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hk2 : 1 ≤ k ^ 2 := by nlinarith
  have hfreq : arcFreq n * ((k : ℝ) ^ 2) = arcFreq (k ^ 2 * (n + 1) - 1) := by
    rw [Nat.mul_comm (k ^ 2) (n + 1), ← arcFreq_mul_nat hk2 n]
    push_cast; ring
  have e : (fun x => arcLineForwardAtomicDeriv k ν x * Real.sin (arcFreq n * x)) = fun x =>
      ((k : ℝ) ^ 3)⁻¹ * (arcLineAtomicDeriv (Real.log k) ν (x * ((k : ℝ) ^ 2)⁻¹) *
        Real.sin (arcFreq (k ^ 2 * (n + 1) - 1) * (x * ((k : ℝ) ^ 2)⁻¹))) := by
    funext x
    unfold arcLineForwardAtomicDeriv
    rw [← hfreq]
    have hx : arcFreq n * (k : ℝ) ^ 2 * (x * ((k : ℝ) ^ 2)⁻¹) = arcFreq n * x := by
      field_simp
    rw [hx]; ring
  rw [e, integral_const_mul, Measure.integral_comp_mul_right
    (fun t => arcLineAtomicDeriv (Real.log k) ν t *
      Real.sin (arcFreq (k ^ 2 * (n + 1) - 1) * t)) (((k : ℝ) ^ 2)⁻¹),
    integral_arcLineAtomicDeriv_log_mul_sin_sq_mul_eq_zero hblind hk n,
    smul_zero, mul_zero]

/-! ### The unconditional all-integer-blind decay-class witness theorem -/

/-- **Unconditional all-integer-blind witness in the `O(e^{−3|v|/2})` Weil decay class.**
For every integer `k ≥ 2`, the forward-dilated pole-filtered modular arc witness
`G = arcLineForwardAtomicVector k ν` is a single fixed function in the full two-sided
`O(e^{−3|v|/2})` Weil decay class (even, integrable with zero mean, `k²`-inversion-covariant, and
strictly positive definite on the critical line after centering at `2 log k`) whose derivative `G'`
is **simultaneously blind at EVERY nonzero integer frequency `2π(n+1)` (`n ∈ ℕ`)**, both sine and
cosine. -/
theorem exists_forwardLogNat_decayClass_allInteger_blind_witness {k : ℕ} (hk : 2 ≤ k) :
    ∃ G G' : ℝ → ℝ,
      (∀ x, HasDerivAt G (G' x) x) ∧ Integrable G ∧ Integrable G' ∧
      (∀ x, G (-x) = G x) ∧ (∀ x, G' (-x) = -G' x) ∧
      (∀ x, x ≠ 0 → G ((k : ℝ) ^ 4 / x) = |x| / (k : ℝ) ^ 2 * G x) ∧
      ∫ x, G x = 0 ∧
      (∃ C, 0 < C ∧ ∀ v, |Real.exp (v / 2) * G (Real.exp v)| ≤ C * Real.exp (-(3 * |v| / 2))) ∧
      (∀ n : ℕ, ∫ x, G' x * Real.sin (arcFreq n * x) = 0) ∧
      (∀ c : ℝ, ∫ x, G' x * Real.cos (c * x) = 0) ∧
      ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) *
        (Real.exp ((v + 2 * Real.log k) / 2) * G (Real.exp (v + 2 * Real.log k))) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hk1 : 1 ≤ k := by omega
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨arcLineForwardAtomicVector k ν, arcLineForwardAtomicDeriv k ν,
    hasDerivAt_arcLineForwardAtomicVector k ν,
    integrable_arcLineForwardAtomicVector hk1 hsym,
    integrable_arcLineForwardAtomicDeriv hk1 ν,
    arcLineForwardAtomicVector_neg_of_map_arcNeg k hsym,
    arcLineForwardAtomicDeriv_neg_of_map_arcNeg k hsym,
    fun x hx => arcLineForwardAtomicVector_inv_scaled hk1 ν hx,
    integral_arcLineForwardAtomicVector_eq_zero hk1 hsym,
    ⟨5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 + 1, ?_, fun v => ?_⟩,
    integral_arcLineForwardAtomicDeriv_mul_sin_eq_zero hblind hk1,
    integral_arcLineForwardAtomicDeriv_mul_cos_eq_zero k hsym,
    fun τ => ?_⟩
  · have := measureReal_nonneg (μ := ν) (s := univ)
    have := atomMass_nonneg (Real.log k)
    positivity
  · rw [exp_half_mul_arcLineForwardAtomicVector hk1]
    calc |arcLineForwardAtomicProfile k ν v|
        ≤ 5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 *
            Real.exp (-(3 * |v| / 2)) := abs_arcLineForwardAtomicProfile_le hk1 hsym v
      _ ≤ (5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 + 1) *
            Real.exp (-(3 * |v| / 2)) := by
          gcongr; linarith
  · simp_rw [exp_half_mul_arcLineForwardAtomicVector hk1]
    exact integral_cos_mul_arcLineForwardAtomicProfile_add_pos hk ν hpd τ

end

end RHTower
