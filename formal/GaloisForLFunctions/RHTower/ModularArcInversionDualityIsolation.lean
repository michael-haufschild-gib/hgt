import GaloisForLFunctions.RHTower.ModularArcForwardDilationAllIntegerBlind
import GaloisForLFunctions.RHTower.ModularArcAtomicSubharmonicAsymptotics

/-!
# Mellin inversion duality and forward-backward spectral isolation for modular arc witnesses

In `ModularArcForwardDilationAllIntegerBlind`, applying the forward dilation `D_{2 log k}` to the
self-reciprocal 5-point pole-filtered modular arc witness `H_{log k, ν} = arcLineAtomicVector (log k) ν`
produced `G_{k,ν} = arcLineForwardAtomicVector k ν`, which lies in the full two-sided `O(e^{−3|v|/2})`
Weil decay class with zero mean and is **simultaneously blind at every positive integer frequency
`arcFreq n = 2π(n+1)` (`n ∈ ℕ`)**.

In this module we study the **Mellin inversion dual** of `G_{k,ν}` under the weight-1 involution
`(ℐ G)(x) = |x|⁻¹ G(1/x)`:

`G̃_{k,ν}(x) = k · H_{log k, ν}(k² x)`  (`arcLineBackwardAtomicVector k ν`),

together with the self-reciprocal symmetrization

`S_{k,ν}(x) = ½ (G_{k,ν}(x) + G̃_{k,ν}(x))`  (`arcLineSymAtomicVector k ν`).

## Main results

1. **Exact Mellin inversion duality (`G_{k,ν} ↔ G̃_{k,ν}`):**
   - `arcLineForwardAtomicVector_inv_eq_backward` and `arcLineBackwardAtomicVector_inv_eq_forward`:
     for `k ≥ 1` and `x ≠ 0`,
     `G_{k,ν}(1/x) = |x| G̃_{k,ν}(x)` and `G̃_{k,ν}(1/x) = |x| G_{k,ν}(x)`.
   - `arcLineBackwardAtomicProfile_eq_forward_neg`: on the logarithmic line `x = e^v`,
     `G̃_{k,ν}^{prof}(v) = G_{k,ν}^{prof}(−v)`.
   - `abs_arcLineBackwardAtomicProfile_le` and `integral_arcLineBackwardAtomicVector_eq_zero`:
     `G̃_{k,ν}` belongs to the full two-sided `O(e^{−3|v|/2})` Weil decay class with zero mean.
2. **Backward integer Fourier moments and `k⁴`-sublattice blindness:**
   - `integral_arcLineBackwardAtomicDeriv_mul_sin`:
     `∫ G̃_{k,ν}'(x) sin(cx) dx = k ∫ H_{log k, ν}'(t) sin((c / k²) t) dt`.
   - `integral_arcLineBackwardAtomicDeriv_mul_sin_sq_mul`: along the `k²`-sublattice
     `arcFreq (k²(m+1) − 1)`, the backward moment reduces to `k` times the `arcFreq m` moment of
     `H_{log k, ν}'`.
   - `integral_arcLineBackwardAtomicDeriv_mul_sin_pow4_mul_eq_zero`: along the `k⁴`-sublattice
     `arcFreq (k⁴(m+1) − 1)`, the backward moment vanishes identically for all `m ∈ ℕ`.
3. **Self-reciprocal symmetrization `S_{k,ν}` and Exact Forward-Backward Spectral Isolation:**
   - `arcLineSymAtomicVector_inv`: `S_{k,ν}(1/x) = |x| S_{k,ν}(x)` for all `x ≠ 0`.
   - `integral_cos_mul_arcLineSymAtomicProfile`: exact critical-line cosine transform
     `cos(2τ log k) (1 − cos(τ log k)/cosh(½ log k))² ∫ cos(τv) B_ν(v) dv`.
   - `integral_arcLineSymAtomicDeriv_mul_sin_eq_half_backward`: for **every** integer frequency
     `arcFreq n = 2π(n+1)` (`n ∈ ℕ`), the forward half `G_{k,ν}'` contributes identically zero,
     isolating 100% of the integer Fourier sine moment of the self-reciprocal witness `S_{k,ν}'`
     into the backward half `½ G̃_{k,ν}'`.
   - `integral_arcLineSymAtomicDeriv_mul_sin_pow4_mul_eq_zero`: `S_{k,ν}'` is identically blind
     along the infinite `k⁴`-sublattice `arcFreq (k⁴(m+1) − 1)` (`m ∈ ℕ`).
   - `exists_inversionDual_allInteger_isolation_witness`: unconditional master existence theorem
     packaging `(G_{k,ν}, G̃_{k,ν}, S_{k,ν})` for every `k ≥ 2`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### The backward-dilated 5-point pole-filtered modular arc line vector `G̃_{k,ν}` -/

/-- The backward-dilated 5-point pole-filtered modular arc line vector:
`G̃_{k,ν}(x) = k · arcLineAtomicVector (log k) ν (k² x)`. -/
def arcLineBackwardAtomicVector (k : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  (k : ℝ) * arcLineAtomicVector (Real.log k) ν ((k : ℝ) ^ 2 * x)

/-- Its derivative `G̃_{k,ν}'(x) = k³ · arcLineAtomicDeriv (log k) ν (k² x)`. -/
def arcLineBackwardAtomicDeriv (k : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  (k : ℝ) ^ 3 * arcLineAtomicDeriv (Real.log k) ν ((k : ℝ) ^ 2 * x)

/-- Its log-scale profile `arcLineAtomicProfile (log k) ν (v + 2 log k)`. -/
def arcLineBackwardAtomicProfile (k : ℕ) (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  arcLineAtomicProfile (Real.log k) ν (v + 2 * Real.log k)

theorem hasDerivAt_arcLineBackwardAtomicVector (k : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (x : ℝ) :
    HasDerivAt (arcLineBackwardAtomicVector k ν) (arcLineBackwardAtomicDeriv k ν x) x := by
  have hc : HasDerivAt (fun x' : ℝ => (k : ℝ) ^ 2 * x') ((k : ℝ) ^ 2) x := by
    simpa using (hasDerivAt_id x).const_mul ((k : ℝ) ^ 2)
  have h := ((hasDerivAt_arcLineAtomicVector (Real.log k) ν
    ((k : ℝ) ^ 2 * x)).comp x hc).const_mul (k : ℝ)
  refine h.congr_deriv ?_
  unfold arcLineBackwardAtomicDeriv
  ring

theorem continuous_arcLineBackwardAtomicVector (k : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] :
    Continuous (arcLineBackwardAtomicVector k ν) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_arcLineBackwardAtomicVector k ν x).continuousAt

theorem arcLineBackwardAtomicVector_neg_of_map_arcNeg (k : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineBackwardAtomicVector k ν (-x) = arcLineBackwardAtomicVector k ν x := by
  unfold arcLineBackwardAtomicVector
  rw [mul_neg, arcLineAtomicVector_neg_of_map_arcNeg _ hν]

theorem arcLineBackwardAtomicDeriv_neg_of_map_arcNeg (k : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineBackwardAtomicDeriv k ν (-x) = -arcLineBackwardAtomicDeriv k ν x := by
  unfold arcLineBackwardAtomicDeriv
  rw [mul_neg, arcLineAtomicDeriv_neg_of_map_arcNeg _ hν, mul_neg]

theorem exp_half_mul_arcLineBackwardAtomicVector {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) (v : ℝ) :
    Real.exp (v / 2) * arcLineBackwardAtomicVector k ν (Real.exp v) =
      arcLineBackwardAtomicProfile k ν v := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  unfold arcLineBackwardAtomicVector arcLineBackwardAtomicProfile
  have he2 : (k : ℝ) ^ 2 = Real.exp (2 * Real.log k) := by
    rw [show (2 : ℝ) * Real.log k = ((2 : ℕ) : ℝ) * Real.log k by norm_num,
      Real.exp_nat_mul, Real.exp_log hkpos]
  have e1 : (k : ℝ) ^ 2 * Real.exp v = Real.exp (v + 2 * Real.log k) := by
    rw [he2, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (v / 2) * (k : ℝ) = Real.exp ((v + 2 * Real.log k) / 2) := by
    rw [show (v + 2 * Real.log k) / 2 = v / 2 + Real.log k by ring,
      Real.exp_add, Real.exp_log hkpos]
  rw [e1, ← mul_assoc, e2, exp_half_mul_arcLineAtomicVector]

/-! ### Exact Mellin inversion duality between `G_{k,ν}` and `G̃_{k,ν}` -/

/-- **Exact Mellin inversion duality (forward → backward):**
`G_{k,ν}(1/x) = |x| G̃_{k,ν}(x)` for `k ≥ 1` and `x ≠ 0`. -/
theorem arcLineForwardAtomicVector_inv_eq_backward {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) {x : ℝ} (hx : x ≠ 0) :
    arcLineForwardAtomicVector k ν (1 / x) =
      |x| * arcLineBackwardAtomicVector k ν x := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hy : (k : ℝ) ^ 2 * x ≠ 0 := mul_ne_zero (pow_ne_zero 2 hkne) hx
  unfold arcLineForwardAtomicVector arcLineBackwardAtomicVector
  have e : 1 / x * ((k : ℝ) ^ 2)⁻¹ = 1 / ((k : ℝ) ^ 2 * x) := by field_simp
  rw [e, arcLineAtomicVector_inv (Real.log k) ν hy, abs_mul,
    abs_of_pos (pow_pos hkpos 2)]
  field_simp

/-- **Exact Mellin inversion duality (backward → forward):**
`G̃_{k,ν}(1/x) = |x| G_{k,ν}(x)` for `k ≥ 1` and `x ≠ 0`. -/
theorem arcLineBackwardAtomicVector_inv_eq_forward {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) {x : ℝ} (hx : x ≠ 0) :
    arcLineBackwardAtomicVector k ν (1 / x) =
      |x| * arcLineForwardAtomicVector k ν x := by
  have h1 : 1 / x ≠ 0 := one_div_ne_zero hx
  have h := arcLineForwardAtomicVector_inv_eq_backward hk ν h1
  rw [one_div_one_div, abs_one_div] at h
  have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
  calc arcLineBackwardAtomicVector k ν (1 / x)
      = |x| * (1 / |x| * arcLineBackwardAtomicVector k ν (1 / x)) := by field_simp
    _ = |x| * arcLineForwardAtomicVector k ν x := by rw [← h]

/-- **Log-scale reflection duality:** `G̃_{k,ν}^{prof}(v) = G_{k,ν}^{prof}(−v)` for all `v ∈ ℝ`. -/
theorem arcLineBackwardAtomicProfile_eq_forward_neg (k : ℕ) (ν : Measure ArcParam) (v : ℝ) :
    arcLineBackwardAtomicProfile k ν v = arcLineForwardAtomicProfile k ν (-v) := by
  unfold arcLineBackwardAtomicProfile arcLineForwardAtomicProfile
  rw [← arcLineAtomicProfile_neg (Real.log k) ν (-v - 2 * Real.log k)]
  congr 1
  ring

/-! ### Decay class, integrability, and zero mean of `arcLineBackwardAtomicVector` -/

/-- **Two-sided `O(e^{−3|v|/2})` Weil decay-class bound for `arcLineBackwardAtomicProfile`.** -/
theorem abs_arcLineBackwardAtomicProfile_le {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineBackwardAtomicProfile k ν v| ≤
      5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 * Real.exp (-(3 * |v| / 2)) := by
  rw [arcLineBackwardAtomicProfile_eq_forward_neg]
  simpa [abs_neg] using abs_arcLineForwardAtomicProfile_le hk hν (-v)

theorem integrable_arcLineBackwardAtomicVector {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Integrable (arcLineBackwardAtomicVector k ν) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  exact ((integrable_arcLineAtomicVector hb hν).comp_mul_left'
    (pow_ne_zero 2 hkpos.ne')).const_mul (k : ℝ)

theorem integrable_arcLineBackwardAtomicDeriv {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineBackwardAtomicDeriv k ν) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  exact ((integrable_arcLineAtomicDeriv (Real.log k) ν).comp_mul_left'
    (pow_ne_zero 2 hkpos.ne')).const_mul ((k : ℝ) ^ 3)

/-- **Zero mean of `arcLineBackwardAtomicVector`.** -/
theorem integral_arcLineBackwardAtomicVector_eq_zero {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    ∫ x, arcLineBackwardAtomicVector k ν x = 0 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  unfold arcLineBackwardAtomicVector
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (arcLineAtomicVector (Real.log k) ν) ((k : ℝ) ^ 2),
    integral_arcLineAtomicVector_eq_zero hb hν, smul_zero, mul_zero]

/-! ### Backward Fourier moments and `k⁴`-sublattice blindness -/

theorem integral_arcLineBackwardAtomicDeriv_mul_cos_eq_zero (k : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (c : ℝ) :
    ∫ x, arcLineBackwardAtomicDeriv k ν x * Real.cos (c * x) = 0 := by
  have h := integral_neg_eq_self
    (fun x : ℝ => arcLineBackwardAtomicDeriv k ν x * Real.cos (c * x)) volume
  have e : (fun x : ℝ => arcLineBackwardAtomicDeriv k ν (-x) * Real.cos (c * -x)) =
      fun x => -(arcLineBackwardAtomicDeriv k ν x * Real.cos (c * x)) := by
    funext x
    rw [arcLineBackwardAtomicDeriv_neg_of_map_arcNeg k hν, mul_neg, Real.cos_neg, neg_mul]
  rw [e, integral_neg] at h
  linarith

/-- **Sine moments of `arcLineBackwardAtomicDeriv k ν`.**
Rescaling `t = k² x` expresses the sine moment at frequency `c` as `k` times the sine moment of
`arcLineAtomicDeriv (log k) ν` at the sub-harmonic frequency `c / k²`. -/
theorem integral_arcLineBackwardAtomicDeriv_mul_sin {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) (c : ℝ) :
    ∫ x, arcLineBackwardAtomicDeriv k ν x * Real.sin (c * x) =
      (k : ℝ) * ∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (c / (k : ℝ) ^ 2 * t) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have e : (fun x => arcLineBackwardAtomicDeriv k ν x * Real.sin (c * x)) = fun x =>
      (k : ℝ) ^ 3 * (arcLineAtomicDeriv (Real.log k) ν ((k : ℝ) ^ 2 * x) *
        Real.sin (c / (k : ℝ) ^ 2 * ((k : ℝ) ^ 2 * x))) := by
    funext x
    unfold arcLineBackwardAtomicDeriv
    have hx : c / (k : ℝ) ^ 2 * ((k : ℝ) ^ 2 * x) = c * x := by field_simp
    rw [hx]; ring
  rw [e, integral_const_mul, Measure.integral_comp_mul_left
    (fun t => arcLineAtomicDeriv (Real.log k) ν t * Real.sin (c / (k : ℝ) ^ 2 * t))
    ((k : ℝ) ^ 2), smul_eq_mul, abs_of_pos (inv_pos.mpr (pow_pos hkpos 2))]
  field_simp

/-- **Reduction along the `k²`-sublattice:** at `arcFreq (k²(m+1) − 1) = 2π k²(m+1)`, the backward
sine moment equals `k` times the `arcFreq m` sine moment of `arcLineAtomicDeriv (log k) ν`. -/
theorem integral_arcLineBackwardAtomicDeriv_mul_sin_sq_mul {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) (m : ℕ) :
    ∫ x, arcLineBackwardAtomicDeriv k ν x *
        Real.sin (arcFreq (k ^ 2 * (m + 1) - 1) * x) =
      (k : ℝ) * ∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (arcFreq m * t) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hk2 : 1 ≤ k ^ 2 := by nlinarith
  have hfreq : arcFreq (k ^ 2 * (m + 1) - 1) / (k : ℝ) ^ 2 = arcFreq m := by
    rw [Nat.mul_comm (k ^ 2) (m + 1), ← arcFreq_mul_nat hk2 m]
    push_cast
    field_simp
  rw [integral_arcLineBackwardAtomicDeriv_mul_sin hk ν, hfreq]

/-- **Exact `k⁴`-sublattice blindness of the backward witness `G̃_{k,ν}'`.**
At every frequency `arcFreq (k⁴(m+1) − 1) = 2π k⁴(m+1)` (`m ∈ ℕ`), the rescaled frequency
`c / k²` is `arcFreq (k²(m+1) − 1)`, which lies on the `k²`-blind sublattice of
`arcLineAtomicDeriv (log k) ν`, so the integral vanishes identically. -/
theorem integral_arcLineBackwardAtomicDeriv_mul_sin_pow4_mul_eq_zero
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    ∫ x, arcLineBackwardAtomicDeriv k ν x *
        Real.sin (arcFreq (k ^ 4 * (m + 1) - 1) * x) = 0 := by
  have heq : k ^ 4 * (m + 1) - 1 = k ^ 2 * ((k ^ 2 * (m + 1) - 1) + 1) - 1 := by
    have h1 : 1 ≤ k ^ 2 * (m + 1) := Nat.mul_pos (by positivity) (Nat.succ_pos m)
    rw [Nat.sub_add_cancel h1]
    ring_nf
  rw [heq, integral_arcLineBackwardAtomicDeriv_mul_sin_sq_mul hk ν (k ^ 2 * (m + 1) - 1),
    integral_arcLineAtomicDeriv_log_mul_sin_sq_mul_eq_zero hblind hk m, mul_zero]

/-! ### Self-reciprocal symmetrization `S_{k,ν}` and Exact Forward-Backward Spectral Isolation -/

/-- The self-reciprocal symmetrization of the forward and backward integer-dilated witnesses:
`S_{k,ν}(x) = ½ (G_{k,ν}(x) + G̃_{k,ν}(x))`. -/
def arcLineSymAtomicVector (k : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  (arcLineForwardAtomicVector k ν x + arcLineBackwardAtomicVector k ν x) / 2

/-- Its derivative `S_{k,ν}'(x) = ½ (G_{k,ν}'(x) + G̃_{k,ν}'(x))`. -/
def arcLineSymAtomicDeriv (k : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  (arcLineForwardAtomicDeriv k ν x + arcLineBackwardAtomicDeriv k ν x) / 2

/-- Its log-scale profile `½ (G_{k,ν}^{prof}(v) + G̃_{k,ν}^{prof}(v))`. -/
def arcLineSymAtomicProfile (k : ℕ) (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  (arcLineForwardAtomicProfile k ν v + arcLineBackwardAtomicProfile k ν v) / 2

theorem hasDerivAt_arcLineSymAtomicVector (k : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (x : ℝ) :
    HasDerivAt (arcLineSymAtomicVector k ν) (arcLineSymAtomicDeriv k ν x) x :=
  ((hasDerivAt_arcLineForwardAtomicVector k ν x).add
    (hasDerivAt_arcLineBackwardAtomicVector k ν x)).div_const 2

theorem arcLineSymAtomicVector_neg_of_map_arcNeg (k : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineSymAtomicVector k ν (-x) = arcLineSymAtomicVector k ν x := by
  unfold arcLineSymAtomicVector
  rw [arcLineForwardAtomicVector_neg_of_map_arcNeg k hν,
    arcLineBackwardAtomicVector_neg_of_map_arcNeg k hν]

theorem arcLineSymAtomicDeriv_neg_of_map_arcNeg (k : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineSymAtomicDeriv k ν (-x) = -arcLineSymAtomicDeriv k ν x := by
  unfold arcLineSymAtomicDeriv
  rw [arcLineForwardAtomicDeriv_neg_of_map_arcNeg k hν,
    arcLineBackwardAtomicDeriv_neg_of_map_arcNeg k hν]
  ring

/-- **Exact `x ↦ 1/x` self-reciprocity of `arcLineSymAtomicVector`:**
`S_{k,ν}(1/x) = |x| S_{k,ν}(x)` for `k ≥ 1` and `x ≠ 0`. -/
theorem arcLineSymAtomicVector_inv {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam)
    {x : ℝ} (hx : x ≠ 0) :
    arcLineSymAtomicVector k ν (1 / x) = |x| * arcLineSymAtomicVector k ν x := by
  unfold arcLineSymAtomicVector
  rw [arcLineForwardAtomicVector_inv_eq_backward hk ν hx,
    arcLineBackwardAtomicVector_inv_eq_forward hk ν hx]
  ring

theorem exp_half_mul_arcLineSymAtomicVector {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) (v : ℝ) :
    Real.exp (v / 2) * arcLineSymAtomicVector k ν (Real.exp v) =
      arcLineSymAtomicProfile k ν v := by
  unfold arcLineSymAtomicVector arcLineSymAtomicProfile
  rw [mul_div_assoc', mul_add, exp_half_mul_arcLineForwardAtomicVector hk,
    exp_half_mul_arcLineBackwardAtomicVector hk]

theorem arcLineSymAtomicProfile_neg (k : ℕ) (ν : Measure ArcParam) (v : ℝ) :
    arcLineSymAtomicProfile k ν (-v) = arcLineSymAtomicProfile k ν v := by
  unfold arcLineSymAtomicProfile
  rw [arcLineBackwardAtomicProfile_eq_forward_neg k ν (-v), neg_neg,
    ← arcLineBackwardAtomicProfile_eq_forward_neg k ν v, add_comm]

theorem abs_arcLineSymAtomicProfile_le {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineSymAtomicProfile k ν v| ≤
      5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 * Real.exp (-(3 * |v| / 2)) := by
  unfold arcLineSymAtomicProfile
  have h1 := abs_arcLineForwardAtomicProfile_le hk hν v
  have h2 := abs_arcLineBackwardAtomicProfile_le hk hν v
  have h2pos : |(2 : ℝ)| = 2 := abs_of_pos zero_lt_two
  rw [abs_div, h2pos]
  linarith [abs_add_le (arcLineForwardAtomicProfile k ν v) (arcLineBackwardAtomicProfile k ν v)]

theorem integrable_arcLineSymAtomicVector {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Integrable (arcLineSymAtomicVector k ν) :=
  ((integrable_arcLineForwardAtomicVector hk hν).add
    (integrable_arcLineBackwardAtomicVector hk hν)).div_const 2

theorem integrable_arcLineSymAtomicDeriv {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineSymAtomicDeriv k ν) :=
  ((integrable_arcLineForwardAtomicDeriv hk ν).add
    (integrable_arcLineBackwardAtomicDeriv hk ν)).div_const 2

theorem integral_arcLineSymAtomicVector_eq_zero {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    ∫ x, arcLineSymAtomicVector k ν x = 0 := by
  unfold arcLineSymAtomicVector
  rw [integral_div, integral_add (integrable_arcLineForwardAtomicVector hk hν)
    (integrable_arcLineBackwardAtomicVector hk hν),
    integral_arcLineForwardAtomicVector_eq_zero hk hν,
    integral_arcLineBackwardAtomicVector_eq_zero hk hν, add_zero, zero_div]

/-- **Exact Forward-Backward Spectral Isolation Law at ALL integer frequencies:**
For every integer frequency `arcFreq n = 2π(n+1)` (`n ∈ ℕ`), the forward component `G_{k,ν}'`
is identically blind, so 100% of the integer Fourier sine moment of the self-reciprocal witness
`S_{k,ν}'` is isolated in the backward component `½ G̃_{k,ν}'`. -/
theorem integral_arcLineSymAtomicDeriv_mul_sin_eq_half_backward
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    ∫ x, arcLineSymAtomicDeriv k ν x * Real.sin (arcFreq n * x) =
      (1 / 2 : ℝ) * ∫ x, arcLineBackwardAtomicDeriv k ν x * Real.sin (arcFreq n * x) := by
  have hF : Integrable fun x => arcLineForwardAtomicDeriv k ν x * Real.sin (arcFreq n * x) :=
    (integrable_arcLineForwardAtomicDeriv hk ν).mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hB : Integrable fun x => arcLineBackwardAtomicDeriv k ν x * Real.sin (arcFreq n * x) :=
    (integrable_arcLineBackwardAtomicDeriv hk ν).mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have e : (fun x => arcLineSymAtomicDeriv k ν x * Real.sin (arcFreq n * x)) = fun x =>
      (1 / 2 : ℝ) * (arcLineForwardAtomicDeriv k ν x * Real.sin (arcFreq n * x) +
        arcLineBackwardAtomicDeriv k ν x * Real.sin (arcFreq n * x)) := by
    funext x; unfold arcLineSymAtomicDeriv; ring
  rw [e, integral_const_mul, integral_add hF hB,
    integral_arcLineForwardAtomicDeriv_mul_sin_eq_zero hblind hk n, zero_add]

/-- **Exact `k⁴`-sublattice blindness of the self-reciprocal symmetrization `S_{k,ν}'`.**
Along the infinite arithmetic progression `arcFreq (k⁴(m+1) − 1) = 2π k⁴(m+1)` (`m ∈ ℕ`), both
the forward and backward halves vanish identically, so `S_{k,ν}'` is blind on `2π k⁴ ℕ⁺`. -/
theorem integral_arcLineSymAtomicDeriv_mul_sin_pow4_mul_eq_zero
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    ∫ x, arcLineSymAtomicDeriv k ν x *
        Real.sin (arcFreq (k ^ 4 * (m + 1) - 1) * x) = 0 := by
  rw [integral_arcLineSymAtomicDeriv_mul_sin_eq_half_backward hblind hk,
    integral_arcLineBackwardAtomicDeriv_mul_sin_pow4_mul_eq_zero hblind hk m, mul_zero]

/-! ### Master unconditional inversion-duality and spectral-isolation witness theorem -/

/-- **Master unconditional Mellin inversion-duality and spectral-isolation theorem.**
For every integer `k ≥ 2`, the continuous modular arc witness `ν` generates a canonical triple
`(G, G̃, S) = (arcLineForwardAtomicVector k ν, arcLineBackwardAtomicVector k ν, arcLineSymAtomicVector k ν)`
of even functions in the full two-sided `O(e^{−3|v|/2})` Weil decay class with zero mean such that:
1. `G` and `G̃` are exact Mellin inversion duals (`G(1/x) = |x| G̃(x)` and `G̃(1/x) = |x| G(x)`),
   while `S = ½(G + G̃)` is strictly self-reciprocal (`S(1/x) = |x| S(x)`);
2. The forward half `G'` is simultaneously blind at **every** positive integer frequency
   `arcFreq n = 2π(n+1)` (`n ∈ ℕ`);
3. For every `n ∈ ℕ`, 100% of the integer sine moment of the self-reciprocal witness `S'` is
   isolated in the backward half `½ G̃'`, and `S'` is identically blind on the infinite `k⁴`-sublattice
   `arcFreq (k⁴(m+1) − 1)` (`m ∈ ℕ`). -/
theorem exists_inversionDual_allInteger_isolation_witness {k : ℕ} (hk : 2 ≤ k) :
    ∃ G G' B B' S S' : ℝ → ℝ,
      (∀ x, HasDerivAt G (G' x) x) ∧ (∀ x, HasDerivAt B (B' x) x) ∧
      (∀ x, HasDerivAt S (S' x) x) ∧
      (∀ x, S x = (G x + B x) / 2) ∧ (∀ x, S' x = (G' x + B' x) / 2) ∧
      (∀ x, x ≠ 0 → G (1 / x) = |x| * B x) ∧
      (∀ x, x ≠ 0 → B (1 / x) = |x| * G x) ∧
      (∀ x, x ≠ 0 → S (1 / x) = |x| * S x) ∧
      ∫ x, G x = 0 ∧ ∫ x, B x = 0 ∧ ∫ x, S x = 0 ∧
      (∃ C, 0 < C ∧ ∀ v, |Real.exp (v / 2) * S (Real.exp v)| ≤ C * Real.exp (-(3 * |v| / 2))) ∧
      (∀ n : ℕ, ∫ x, G' x * Real.sin (arcFreq n * x) = 0) ∧
      (∀ n : ℕ, ∫ x, S' x * Real.sin (arcFreq n * x) =
        (1 / 2 : ℝ) * ∫ x, B' x * Real.sin (arcFreq n * x)) ∧
      (∀ m : ℕ, ∫ x, S' x * Real.sin (arcFreq (k ^ 4 * (m + 1) - 1) * x) = 0) ∧
      ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) *
        (Real.exp ((v + 2 * Real.log k) / 2) * G (Real.exp (v + 2 * Real.log k))) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hk1 : 1 ≤ k := by omega
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨arcLineForwardAtomicVector k ν, arcLineForwardAtomicDeriv k ν,
    arcLineBackwardAtomicVector k ν, arcLineBackwardAtomicDeriv k ν,
    arcLineSymAtomicVector k ν, arcLineSymAtomicDeriv k ν,
    hasDerivAt_arcLineForwardAtomicVector k ν,
    hasDerivAt_arcLineBackwardAtomicVector k ν,
    hasDerivAt_arcLineSymAtomicVector k ν,
    fun _ => rfl, fun _ => rfl,
    fun x hx => arcLineForwardAtomicVector_inv_eq_backward hk1 ν hx,
    fun x hx => arcLineBackwardAtomicVector_inv_eq_forward hk1 ν hx,
    fun x hx => arcLineSymAtomicVector_inv hk1 ν hx,
    integral_arcLineForwardAtomicVector_eq_zero hk1 hsym,
    integral_arcLineBackwardAtomicVector_eq_zero hk1 hsym,
    integral_arcLineSymAtomicVector_eq_zero hk1 hsym,
    ⟨5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 + 1, ?_, fun v => ?_⟩,
    integral_arcLineForwardAtomicDeriv_mul_sin_eq_zero hblind hk1,
    integral_arcLineSymAtomicDeriv_mul_sin_eq_half_backward hblind hk1,
    integral_arcLineSymAtomicDeriv_mul_sin_pow4_mul_eq_zero hblind hk1,
    fun τ => ?_⟩
  · have := measureReal_nonneg (μ := ν) (s := univ)
    have := atomMass_nonneg (Real.log k)
    positivity
  · rw [exp_half_mul_arcLineSymAtomicVector hk1]
    calc |arcLineSymAtomicProfile k ν v|
        ≤ 5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 *
            Real.exp (-(3 * |v| / 2)) := abs_arcLineSymAtomicProfile_le hk1 hsym v
      _ ≤ (5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 + 1) *
            Real.exp (-(3 * |v| / 2)) := by
          gcongr; linarith
  · simp_rw [exp_half_mul_arcLineForwardAtomicVector hk1]
    exact integral_cos_mul_arcLineForwardAtomicProfile_add_pos hk ν hpd τ

end

end RHTower
