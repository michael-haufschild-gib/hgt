import GaloisForLFunctions.RHTower.ModularArcInversionDualityIsolation

/-!
# Two-scale hyperbolic pole-filtered modular arc witnesses

In `ModularArcInversionDualityIsolation`, the self-reciprocal symmetrization
`S_{k,ν} = ½ (G_{k,ν} + G̃_{k,ν})` (`arcLineSymAtomicVector k ν`) isolated 100% of its integer
Fourier sine moments in the backward half `½ G̃_{k,ν}'` because the forward half `G_{k,ν}'` is
blind at all positive integers `2π(n+1)`. However, unweighted `S_{k,ν}` has two structural features
that need hyperbolic damping:
1. Its critical-line cosine multiplier `cos(2τ log k)` changes sign in `τ`;
2. Its backward half `G̃_{k,ν}(x) = k H_{log k, ν}(k² x)` carries an amplitude factor `k` that
   scales sub-harmonic moments by `k`.

In this module we form the **two-scale hyperbolic pole-filtered modular arc witness**:

`W_{k,ν}(x) = H_{log k, ν}(x) − (1 / cosh(log k)) · S_{k,ν}(x)`  (`arcLineTwoScaleVector k ν`).

The single hyperbolic weight `1 / cosh(log k) = 2 / (k + k⁻¹)` resolves both issues simultaneously:
1. Since `|cos(2τ log k)| ≤ 1 < cosh(log k)` for `k ≥ 2`, the critical-line cosine transform of
   `W_{k,ν}` factors with the strictly positive two-scale spectral filter
   `(1 − cos(2τ log k) / cosh(log k)) (1 − cos(τ log k) / cosh(½ log k))² > 0` for all `τ ∈ ℝ`.
2. Since `k / (2 cosh(log k)) = k / (k + k⁻¹) ≤ 1`, the hyperbolic weight absorbs the backward
   dilation factor `k` on the `k²`-sublattice `arcFreq (k²(m+1) − 1)` (where `H_{log k, ν}'` and
   `G_{k,ν}'` both vanish), contracting the `k²`-sublattice moment of `W_{k,ν}'` below the `m`-th
   moment of `H_{log k, ν}'` and forcing `O(k^{−1/2})` decay as `k → ∞`, while maintaining exact
   blindness (`= 0`) on the infinite `k⁴`-sublattice `arcFreq (k⁴(m+1) − 1)`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Shifted critical-line cosine transforms for `arcLineAtomicProfile` and `arcLineSymAtomicProfile` -/

theorem integrable_arcLineAtomicProfile (b : ℝ) (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineAtomicProfile b ν) := by
  unfold arcLineAtomicProfile
  exact integrable_finsetSum _ fun j _ =>
    (((integrable_arcPoissonProfile ν).comp_sub_right (atomShift b j)).const_mul (atomWeight b j))

theorem integrable_cos_mul_arcLineAtomicProfile_sub (b : ℝ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (τ w : ℝ) :
    Integrable fun v => Real.cos (τ * v) * arcLineAtomicProfile b ν (v - w) :=
  ((integrable_arcLineAtomicProfile b ν).comp_sub_right w).bdd_mul (by fun_prop)
    (Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

theorem integral_cos_mul_arcLineAtomicProfile_shift (b : ℝ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (τ w : ℝ) :
    ∫ v, Real.cos (τ * v) * arcLineAtomicProfile b ν (v - w) =
      Real.cos (τ * w) * ∫ v, Real.cos (τ * v) * arcLineAtomicProfile b ν v := by
  have hP := integrable_arcLineAtomicProfile b ν
  have hc : Integrable fun v => Real.cos (τ * v) * arcLineAtomicProfile b ν v :=
    hP.bdd_mul (by fun_prop) (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hs : Integrable fun v => Real.sin (τ * v) * arcLineAtomicProfile b ν v :=
    hP.bdd_mul (by fun_prop) (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hodd : ∫ v, Real.sin (τ * v) * arcLineAtomicProfile b ν v = 0 := by
    have h := integral_neg_eq_self
      (fun v => Real.sin (τ * v) * arcLineAtomicProfile b ν v) volume
    have e : (fun v => Real.sin (τ * -v) * arcLineAtomicProfile b ν (-v)) =
        fun v => -(Real.sin (τ * v) * arcLineAtomicProfile b ν v) := by
      funext v; rw [arcLineAtomicProfile_neg, mul_neg, Real.sin_neg]; ring
    rw [e, integral_neg] at h
    linarith
  rw [← integral_add_right_eq_self (μ := volume)
    (fun v => Real.cos (τ * v) * arcLineAtomicProfile b ν (v - w)) w]
  have e : ∀ v, Real.cos (τ * (v + w)) * arcLineAtomicProfile b ν (v + w - w) =
      Real.cos (τ * w) * (Real.cos (τ * v) * arcLineAtomicProfile b ν v) -
        Real.sin (τ * w) * (Real.sin (τ * v) * arcLineAtomicProfile b ν v) := by
    intro v
    rw [add_sub_cancel_right, mul_add, Real.cos_add]; ring
  simp_rw [e]
  rw [integral_sub (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul,
    hodd, mul_zero, sub_zero]

/-- **Critical-line cosine transform of `arcLineSymAtomicProfile k ν`.** -/
theorem integral_cos_mul_arcLineSymAtomicProfile (k : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * arcLineSymAtomicProfile k ν v =
      Real.cos (τ * (2 * Real.log k)) *
        ∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v := by
  have hF : Integrable fun v => Real.cos (τ * v) * arcLineForwardAtomicProfile k ν v :=
    integrable_cos_mul_arcLineAtomicProfile_sub (Real.log k) ν τ (2 * Real.log k)
  have hB : Integrable fun v => Real.cos (τ * v) * arcLineBackwardAtomicProfile k ν v := by
    have e : (fun v => Real.cos (τ * v) * arcLineBackwardAtomicProfile k ν v) =
        fun v => Real.cos (τ * v) *
          arcLineAtomicProfile (Real.log k) ν (v - (-(2 * Real.log k))) := by
      funext v; unfold arcLineBackwardAtomicProfile; rw [sub_neg_eq_add]
    rw [e]
    exact integrable_cos_mul_arcLineAtomicProfile_sub (Real.log k) ν τ (-(2 * Real.log k))
  have e : (fun v => Real.cos (τ * v) * arcLineSymAtomicProfile k ν v) = fun v =>
      (1 / 2 : ℝ) * (Real.cos (τ * v) * arcLineForwardAtomicProfile k ν v +
        Real.cos (τ * v) * arcLineBackwardAtomicProfile k ν v) := by
    funext v; unfold arcLineSymAtomicProfile; ring
  have eB : ∫ v, Real.cos (τ * v) * arcLineBackwardAtomicProfile k ν v =
      Real.cos (τ * (2 * Real.log k)) *
        ∫ v, Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v := by
    have e' : (fun v => Real.cos (τ * v) * arcLineBackwardAtomicProfile k ν v) =
        fun v => Real.cos (τ * v) *
          arcLineAtomicProfile (Real.log k) ν (v - (-(2 * Real.log k))) := by
      funext v; unfold arcLineBackwardAtomicProfile; rw [sub_neg_eq_add]
    rw [e', integral_cos_mul_arcLineAtomicProfile_shift, mul_neg, Real.cos_neg]
  rw [e, integral_const_mul, integral_add hF hB]
  unfold arcLineForwardAtomicProfile
  rw [integral_cos_mul_arcLineAtomicProfile_shift, eB]
  ring

/-! ### Definition and calculus of `arcLineTwoScaleVector` -/

/-- The two-scale hyperbolic pole-filtered modular arc witness:
`W_{k,ν}(x) = H_{log k, ν}(x) − (1 / cosh(log k)) · S_{k,ν}(x)`. -/
def arcLineTwoScaleVector (k : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  arcLineAtomicVector (Real.log k) ν x -
    (1 / Real.cosh (Real.log k)) * arcLineSymAtomicVector k ν x

/-- Its derivative `W_{k,ν}'(x) = H_{log k, ν}'(x) − (1 / cosh(log k)) · S_{k,ν}'(x)`. -/
def arcLineTwoScaleDeriv (k : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  arcLineAtomicDeriv (Real.log k) ν x -
    (1 / Real.cosh (Real.log k)) * arcLineSymAtomicDeriv k ν x

/-- Its log-scale profile `H_{log k, ν}^{prof}(v) − (1 / cosh(log k)) · S_{k,ν}^{prof}(v)`. -/
def arcLineTwoScaleProfile (k : ℕ) (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  arcLineAtomicProfile (Real.log k) ν v -
    (1 / Real.cosh (Real.log k)) * arcLineSymAtomicProfile k ν v

theorem hasDerivAt_arcLineTwoScaleVector (k : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (x : ℝ) :
    HasDerivAt (arcLineTwoScaleVector k ν) (arcLineTwoScaleDeriv k ν x) x :=
  (hasDerivAt_arcLineAtomicVector (Real.log k) ν x).sub
    ((hasDerivAt_arcLineSymAtomicVector k ν x).const_mul (1 / Real.cosh (Real.log k)))

theorem arcLineTwoScaleVector_neg_of_map_arcNeg (k : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineTwoScaleVector k ν (-x) = arcLineTwoScaleVector k ν x := by
  unfold arcLineTwoScaleVector
  rw [arcLineAtomicVector_neg_of_map_arcNeg _ hν,
    arcLineSymAtomicVector_neg_of_map_arcNeg k hν]

theorem arcLineTwoScaleDeriv_neg_of_map_arcNeg (k : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineTwoScaleDeriv k ν (-x) = -arcLineTwoScaleDeriv k ν x := by
  unfold arcLineTwoScaleDeriv
  rw [arcLineAtomicDeriv_neg_of_map_arcNeg _ hν,
    arcLineSymAtomicDeriv_neg_of_map_arcNeg k hν]
  ring

/-- **Exact `x ↦ 1/x` self-reciprocity of `arcLineTwoScaleVector`:**
`W_{k,ν}(1/x) = |x| W_{k,ν}(x)` for `k ≥ 1` and `x ≠ 0`. -/
theorem arcLineTwoScaleVector_inv {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam)
    {x : ℝ} (hx : x ≠ 0) :
    arcLineTwoScaleVector k ν (1 / x) = |x| * arcLineTwoScaleVector k ν x := by
  unfold arcLineTwoScaleVector
  rw [arcLineAtomicVector_inv (Real.log k) ν hx,
    arcLineSymAtomicVector_inv hk ν hx]
  ring

theorem exp_half_mul_arcLineTwoScaleVector {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) (v : ℝ) :
    Real.exp (v / 2) * arcLineTwoScaleVector k ν (Real.exp v) =
      arcLineTwoScaleProfile k ν v := by
  unfold arcLineTwoScaleVector arcLineTwoScaleProfile
  rw [mul_sub, exp_half_mul_arcLineAtomicVector, ← mul_left_comm,
    exp_half_mul_arcLineSymAtomicVector hk]

theorem arcLineTwoScaleProfile_neg (k : ℕ) (ν : Measure ArcParam) (v : ℝ) :
    arcLineTwoScaleProfile k ν (-v) = arcLineTwoScaleProfile k ν v := by
  unfold arcLineTwoScaleProfile
  rw [arcLineAtomicProfile_neg, arcLineSymAtomicProfile_neg]

/-! ### Full `O(e^{−3|v|/2})` Weil decay class, integrability, and zero mean -/

theorem abs_arcLineTwoScaleProfile_le {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineTwoScaleProfile k ν v| ≤
      10 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 * Real.exp (-(3 * |v| / 2)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hH := abs_arcLineAtomicProfile_le hb hν v
  have hexp3 : Real.exp (3 * Real.log k) = (k : ℝ) ^ 3 := by
    rw [show (3 : ℝ) * Real.log k = ((3 : ℕ) : ℝ) * Real.log k by norm_num,
      Real.exp_nat_mul, Real.exp_log hkpos]
  rw [hexp3] at hH
  have hk3_le_k6 : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 6 := by
    exact pow_le_pow_right₀ hk1 (by norm_num)
  have hH6 : |arcLineAtomicProfile (Real.log k) ν v| ≤
      5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 * Real.exp (-(3 * |v| / 2)) := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    have := atomMass_nonneg (Real.log k)
    calc |arcLineAtomicProfile (Real.log k) ν v|
        ≤ 5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 3 * Real.exp (-(3 * |v| / 2)) := hH
      _ ≤ 5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 * Real.exp (-(3 * |v| / 2)) := by
          gcongr
  have hS := abs_arcLineSymAtomicProfile_le hk hν v
  have hcosh : 1 / Real.cosh (Real.log k) ≤ 1 :=
    div_le_one_of_le₀ (Real.one_le_cosh _) (Real.cosh_pos _).le
  have hS_scaled : |(1 / Real.cosh (Real.log k)) * arcLineSymAtomicProfile k ν v| ≤
      5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 * Real.exp (-(3 * |v| / 2)) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / Real.cosh (Real.log k) * |arcLineSymAtomicProfile k ν v|
        ≤ 1 * |arcLineSymAtomicProfile k ν v| :=
          mul_le_mul_of_nonneg_right hcosh (abs_nonneg _)
      _ = |arcLineSymAtomicProfile k ν v| := one_mul _
      _ ≤ 5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 * Real.exp (-(3 * |v| / 2)) := hS
  unfold arcLineTwoScaleProfile
  linarith [abs_sub (arcLineAtomicProfile (Real.log k) ν v)
    ((1 / Real.cosh (Real.log k)) * arcLineSymAtomicProfile k ν v)]

theorem integrable_arcLineTwoScaleVector {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Integrable (arcLineTwoScaleVector k ν) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact (integrable_arcLineAtomicVector (Real.log_nonneg hk1) hν).sub
    ((integrable_arcLineSymAtomicVector hk hν).const_mul _)

theorem integrable_arcLineTwoScaleDeriv {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineTwoScaleDeriv k ν) :=
  (integrable_arcLineAtomicDeriv (Real.log k) ν).sub
    ((integrable_arcLineSymAtomicDeriv hk ν).const_mul _)

theorem integral_arcLineTwoScaleVector_eq_zero {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    ∫ x, arcLineTwoScaleVector k ν x = 0 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  unfold arcLineTwoScaleVector
  rw [integral_sub (integrable_arcLineAtomicVector hb hν)
    ((integrable_arcLineSymAtomicVector hk hν).const_mul _),
    integral_const_mul, integral_arcLineAtomicVector_eq_zero hb hν,
    integral_arcLineSymAtomicVector_eq_zero hk hν, mul_zero, sub_zero]

/-! ### Exact two-scale critical-line spectral factorization and strict positive definiteness -/

/-- **Exact two-scale critical-line cosine transform factorization.** -/
theorem integral_cos_mul_arcLineTwoScaleProfile (k : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * arcLineTwoScaleProfile k ν v =
      (1 - Real.cos (τ * (2 * Real.log k)) / Real.cosh (Real.log k)) *
        (1 - Real.cos (Real.log k * τ) / Real.cosh (Real.log k / 2)) ^ 2 *
        ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v := by
  have hH : Integrable fun v => Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v := by
    simpa using integrable_cos_mul_arcLineAtomicProfile_sub (Real.log k) ν τ 0
  have hS : Integrable fun v => Real.cos (τ * v) * arcLineSymAtomicProfile k ν v := by
    have hF := integrable_cos_mul_arcLineAtomicProfile_sub (Real.log k) ν τ (2 * Real.log k)
    have hB : Integrable fun v => Real.cos (τ * v) * arcLineBackwardAtomicProfile k ν v := by
      have e : (fun v => Real.cos (τ * v) * arcLineBackwardAtomicProfile k ν v) =
          fun v => Real.cos (τ * v) *
            arcLineAtomicProfile (Real.log k) ν (v - (-(2 * Real.log k))) := by
        funext v; unfold arcLineBackwardAtomicProfile; rw [sub_neg_eq_add]
      rw [e]
      exact integrable_cos_mul_arcLineAtomicProfile_sub (Real.log k) ν τ (-(2 * Real.log k))
    have e : (fun v => Real.cos (τ * v) * arcLineSymAtomicProfile k ν v) = fun v =>
        (1 / 2 : ℝ) * (Real.cos (τ * v) * arcLineForwardAtomicProfile k ν v +
          Real.cos (τ * v) * arcLineBackwardAtomicProfile k ν v) := by
      funext v; unfold arcLineSymAtomicProfile; ring
    rw [e]
    exact (hF.add hB).const_mul _
  have e : (fun v => Real.cos (τ * v) * arcLineTwoScaleProfile k ν v) = fun v =>
      Real.cos (τ * v) * arcLineAtomicProfile (Real.log k) ν v -
        (1 / Real.cosh (Real.log k)) * (Real.cos (τ * v) * arcLineSymAtomicProfile k ν v) := by
    funext v; unfold arcLineTwoScaleProfile; ring
  rw [e, integral_sub hH (hS.const_mul _), integral_const_mul,
    integral_cos_mul_arcLineSymAtomicProfile,
    integral_cos_mul_arcLineAtomicProfile]
  ring

/-- **Strict positive definiteness of `arcLineTwoScaleProfile` on the critical line (`k ≥ 2`).** -/
theorem integral_cos_mul_arcLineTwoScaleProfile_pos {k : ℕ} (hk : 2 ≤ k)
    (ν : Measure ArcParam) [IsFiniteMeasure ν]
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * arcLineTwoScaleProfile k ν v := by
  have hkgt1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le one_lt_two hk)
  have hb : 0 < Real.log k := Real.log_pos hkgt1
  rw [integral_cos_mul_arcLineTwoScaleProfile]
  have h1 : 0 < 1 - Real.cos (τ * (2 * Real.log k)) / Real.cosh (Real.log k) := by
    have hC : 1 < Real.cosh (Real.log k) := Real.one_lt_cosh.mpr hb.ne'
    have hlt : Real.cos (τ * (2 * Real.log k)) / Real.cosh (Real.log k) < 1 := by
      rw [div_lt_one (Real.cosh_pos _)]
      linarith [Real.cos_le_one (τ * (2 * Real.log k))]
    linarith
  have h2 : 0 < (1 - Real.cos (Real.log k * τ) / Real.cosh (Real.log k / 2)) ^ 2 := by
    have hC : 1 < Real.cosh (Real.log k / 2) := Real.one_lt_cosh.mpr (by positivity)
    have hlt : Real.cos (Real.log k * τ) / Real.cosh (Real.log k / 2) < 1 := by
      rw [div_lt_one (Real.cosh_pos _)]
      linarith [Real.cos_le_one (Real.log k * τ)]
    have := sub_pos.mpr hlt
    positivity
  exact mul_pos (mul_pos h1 h2) (hpd τ)

/-! ### Hyperbolic absorption of the backward factor on the `k²`-sublattice and `k⁴`-blindness -/

/-- For every `k ≥ 1`, `k ≤ 2 * cosh(log k) = k + k⁻¹`. -/
theorem nat_le_two_mul_cosh_log {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) ≤ 2 * Real.cosh (Real.log k) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  rw [Real.cosh_eq, Real.exp_log hkpos]
  linarith [Real.exp_pos (-Real.log k)]

/-- The hyperbolic backward-dilation contraction factor `k / (2 cosh(log k))` lies in `(0, 1]`. -/
theorem div_two_mul_cosh_log_le_one {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) / (2 * Real.cosh (Real.log k)) ≤ 1 := by
  rw [div_le_one (by positivity)]
  exact nat_le_two_mul_cosh_log hk

/-- **Exact `k²`-sublattice reduction for `arcLineTwoScaleDeriv k ν`.**
Along `arcFreq (k²(m+1) − 1)`, both `H_{log k, ν}'` and the forward half `G_{k,ν}'` vanish
identically, leaving `−(k / (2 cosh(log k)))` times the `arcFreq m` moment of `H_{log k, ν}'`. -/
theorem integral_arcLineTwoScaleDeriv_mul_sin_sq_mul
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    ∫ x, arcLineTwoScaleDeriv k ν x *
        Real.sin (arcFreq (k ^ 2 * (m + 1) - 1) * x) =
      -((k : ℝ) / (2 * Real.cosh (Real.log k))) *
        ∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (arcFreq m * t) := by
  set n := k ^ 2 * (m + 1) - 1
  have hH : Integrable fun x => arcLineAtomicDeriv (Real.log k) ν x * Real.sin (arcFreq n * x) :=
    (integrable_arcLineAtomicDeriv (Real.log k) ν).mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hS : Integrable fun x => arcLineSymAtomicDeriv k ν x * Real.sin (arcFreq n * x) :=
    (integrable_arcLineSymAtomicDeriv hk ν).mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have e : (fun x => arcLineTwoScaleDeriv k ν x * Real.sin (arcFreq n * x)) = fun x =>
      arcLineAtomicDeriv (Real.log k) ν x * Real.sin (arcFreq n * x) -
        (1 / Real.cosh (Real.log k)) * (arcLineSymAtomicDeriv k ν x * Real.sin (arcFreq n * x)) := by
    funext x; unfold arcLineTwoScaleDeriv; ring
  rw [e, integral_sub hH (hS.const_mul _), integral_const_mul,
    integral_arcLineAtomicDeriv_log_mul_sin_sq_mul_eq_zero hblind hk m,
    integral_arcLineSymAtomicDeriv_mul_sin_eq_half_backward hblind hk n,
    integral_arcLineBackwardAtomicDeriv_mul_sin_sq_mul hk ν m]
  ring

/-- **Hyperbolic contraction on the `k²`-sublattice:** the `k²`-sublattice sine moment of
`arcLineTwoScaleDeriv k ν` is bounded in absolute value by the `arcFreq m` sine moment of
`arcLineAtomicDeriv (log k) ν`, with no `k`-amplification. -/
theorem abs_integral_arcLineTwoScaleDeriv_mul_sin_sq_mul_le
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    |∫ x, arcLineTwoScaleDeriv k ν x *
        Real.sin (arcFreq (k ^ 2 * (m + 1) - 1) * x)| ≤
      |∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (arcFreq m * t)| := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  rw [integral_arcLineTwoScaleDeriv_mul_sin_sq_mul hblind hk m,
    abs_mul, abs_neg, abs_of_pos (by positivity)]
  calc (k : ℝ) / (2 * Real.cosh (Real.log k)) *
        |∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (arcFreq m * t)|
      ≤ 1 * |∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (arcFreq m * t)| :=
        mul_le_mul_of_nonneg_right (div_two_mul_cosh_log_le_one hk) (abs_nonneg _)
    _ = |∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (arcFreq m * t)| := one_mul _

/-- **Asymptotic vanishing on the `k²`-sublattice as `k → ∞`:** for every `m ∈ ℕ`,
`∫ W_{k,ν}'(x) sin(arcFreq (k²(m+1) − 1) x) dx → 0` as `k → ∞`. -/
theorem tendsto_integral_arcLineTwoScaleDeriv_mul_sin_sq_mul_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    (m : ℕ) :
    Tendsto (fun k : ℕ => ∫ x, arcLineTwoScaleDeriv k ν x *
      Real.sin (arcFreq (k ^ 2 * (m + 1) - 1) * x)) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun k : ℕ =>
      |∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (arcFreq m * t)|) atTop (𝓝 0) := by
    simpa using (tendsto_integral_arcLineAtomicDeriv_log_mul_sin_atTop hblind m).norm
  refine squeeze_zero_norm' ?_ hnorm
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [Real.norm_eq_abs]
  exact abs_integral_arcLineTwoScaleDeriv_mul_sin_sq_mul_le hblind hk m

/-- **Exact `k⁴`-sublattice blindness of `arcLineTwoScaleDeriv k ν`.** -/
theorem integral_arcLineTwoScaleDeriv_mul_sin_pow4_mul_eq_zero
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    ∫ x, arcLineTwoScaleDeriv k ν x *
        Real.sin (arcFreq (k ^ 4 * (m + 1) - 1) * x) = 0 := by
  have heq : k ^ 4 * (m + 1) - 1 = k ^ 2 * ((k ^ 2 * (m + 1) - 1) + 1) - 1 := by
    have h1 : 1 ≤ k ^ 2 * (m + 1) := Nat.mul_pos (by positivity) (Nat.succ_pos m)
    rw [Nat.sub_add_cancel h1]
    ring_nf
  rw [heq, integral_arcLineTwoScaleDeriv_mul_sin_sq_mul hblind hk (k ^ 2 * (m + 1) - 1),
    integral_arcLineAtomicDeriv_log_mul_sin_sq_mul_eq_zero hblind hk m, mul_zero]

/-! ### Master unconditional two-scale hyperbolic witness theorem -/

/-- **Master unconditional theorem for the two-scale hyperbolic modular arc witnesses.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2`, `W_k = arcLineTwoScaleVector k ν` is an even, strictly self-reciprocal
(`W_k(1/x) = |x| W_k(x)`), zero-mean, strictly positive definite function in the full
`O(e^{−3|v|/2})` Weil decay class satisfying:
1. Exact two-scale critical-line positivity `∀ τ ∈ ℝ, 0 < ∫ cos(τv) W_k^{prof}(v) dv`;
2. Exact blindness on the infinite `k⁴`-sublattice `arcFreq (k⁴(m+1) − 1)` (`m ∈ ℕ`);
3. Hyperbolic contraction on the `k²`-sublattice `arcFreq (k²(m+1) − 1)`, bounding its sine moment
   by the `m`-th moment of `arcLineAtomicDeriv (log k) ν` and forcing asymptotic vanishing as
   `k → ∞`. -/
theorem exists_twoScale_hyperbolic_decayClass_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ x, arcLineTwoScaleVector k ν (-x) = arcLineTwoScaleVector k ν x) ∧
        (∀ x, x ≠ 0 → arcLineTwoScaleVector k ν (1 / x) =
          |x| * arcLineTwoScaleVector k ν x) ∧
        ∫ x, arcLineTwoScaleVector k ν x = 0 ∧
        (∀ v, |arcLineTwoScaleProfile k ν v| ≤
          10 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 * Real.exp (-(3 * |v| / 2))) ∧
        (∀ m : ℕ, ∫ x, arcLineTwoScaleDeriv k ν x *
          Real.sin (arcFreq (k ^ 4 * (m + 1) - 1) * x) = 0) ∧
        (∀ m : ℕ, |∫ x, arcLineTwoScaleDeriv k ν x *
            Real.sin (arcFreq (k ^ 2 * (m + 1) - 1) * x)| ≤
          |∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (arcFreq m * t)|) ∧
        ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcLineTwoScaleProfile k ν v) ∧
      ∀ m : ℕ, Tendsto (fun k : ℕ =>
        ∫ x, arcLineTwoScaleDeriv k ν x *
          Real.sin (arcFreq (k ^ 2 * (m + 1) - 1) * x)) atTop (𝓝 0) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym, fun k hk => ?_,
    tendsto_integral_arcLineTwoScaleDeriv_mul_sin_sq_mul_atTop hblind⟩
  have hk1 : 1 ≤ k := by omega
  exact ⟨arcLineTwoScaleVector_neg_of_map_arcNeg k hsym,
    fun x hx => arcLineTwoScaleVector_inv hk1 ν hx,
    integral_arcLineTwoScaleVector_eq_zero hk1 hsym,
    abs_arcLineTwoScaleProfile_le hk1 hsym,
    integral_arcLineTwoScaleDeriv_mul_sin_pow4_mul_eq_zero hblind hk1,
    abs_integral_arcLineTwoScaleDeriv_mul_sin_sq_mul_le hblind hk1,
    integral_cos_mul_arcLineTwoScaleProfile_pos hk ν hpd⟩

end

end RHTower
