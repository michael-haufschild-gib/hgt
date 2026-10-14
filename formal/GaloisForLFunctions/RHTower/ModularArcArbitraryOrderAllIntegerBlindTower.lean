import GaloisForLFunctions.RHTower.ModularArcArbitraryOrderStripEdgeTower

/-!
# Arbitrary-order strip-edge vanishing and simultaneous all-integer blindness for modular arc witnesses

In `ModularArcArbitraryOrderStripEdgeTower`, we constructed the iterated hyperbolic pole-filtered
modular arc tower `arcLineTowerVector k d ν` (`d ∈ ℕ`), which is strictly self-reciprocal,
strictly positive definite on the critical line, vanishes to arbitrary order `O((1/2 − l)^{d+1})`
at the critical strip edge `l → (1/2)⁻`, and is identically blind along the `k^{2(d+1)}`-sublattice
`arcFreq (k^{2(d+1)}(n+1) − 1)` (`n ∈ ℕ`).

In this module we apply the forward dilation `D_{2(d+1) log k}` (`x ↦ x / k^{2(d+1)}`, weighted by
`k^{−(d+1)}`) to level `d` of the tower, defining:

* `arcLineForwardTowerVector k d ν x = k^{−(d+1)} · arcLineTowerVector k d ν (x / k^{2(d+1)})`,
* `arcLineForwardTowerDeriv k d ν x = k^{−3(d+1)} · arcLineTowerDeriv k d ν (x / k^{2(d+1)})`,
* `arcLineForwardTowerProfile k d ν v = arcLineTowerProfile k d ν (v − 2(d+1) log k)`.

Because rescaling `x ↦ x / k^{2(d+1)}` maps **every** positive integer frequency
`arcFreq n = 2π(n+1)` (`n ∈ ℕ`) onto `arcFreq (k^{2(d+1)}(n+1) − 1)` on the blind sublattice of
`arcLineTowerDeriv k d ν`, while shifting `v ↦ v − 2(d+1) log k` multiplies the strip Laplace/Mellin
transform by `e^{2(d+1) l log k} ≤ k^{d+1}` on `l ∈ [0, 1/2)`, we obtain at **every prescribed
order `d ∈ ℕ`** a single fixed function in the full two-sided `O(e^{−3|v|/2})` Weil decay class
that is simultaneously:
1. **Blind at EVERY positive integer frequency `arcFreq n = 2π(n+1)` (`∀ n ∈ ℕ`)**, both sine and
   cosine (`integral_arcLineForwardTowerDeriv_mul_sin_eq_zero`,
   `integral_arcLineForwardTowerDeriv_mul_cos_eq_zero`);
2. **Vanishing to order `(1/2 − l)^{d+1}` at the critical strip edge `l → (1/2)⁻`**, with vanishing
   `d`-th divided difference `(∫ e^{lv} P(v) dv) / (1/2 − l)^d → 0` on `𝓝[<] (1/2)`
   (`abs_integral_exp_mul_arcLineForwardTowerProfile_le`,
   `tendsto_div_pow_integral_exp_mul_arcLineForwardTowerProfile_nhdsWithin`);
3. **Even, integrable with zero mean, `k^{2(d+1)}`-centered inversion-covariant, and strictly
   positive definite on the critical line after centering at `2(d+1) log k`**
   (`exists_arbitraryOrder_allInteger_blind_arcWitness`).
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Definition and calculus of `arcLineForwardTowerVector` -/

/-- Level `d` of the forward `2(d+1) log k`-dilated arbitrary-order modular arc tower:
`F_{k,d,ν}(x) = k^{−(d+1)} · arcLineTowerVector k d ν (x / k^{2(d+1)})`. -/
def arcLineForwardTowerVector (k d : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  ((k : ℝ) ^ (d + 1))⁻¹ * arcLineTowerVector k d ν (x * ((k : ℝ) ^ (2 * (d + 1)))⁻¹)

/-- Its derivative `F_{k,d,ν}'(x) = k^{−3(d+1)} · arcLineTowerDeriv k d ν (x / k^{2(d+1)})`. -/
def arcLineForwardTowerDeriv (k d : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  ((k : ℝ) ^ (3 * (d + 1)))⁻¹ * arcLineTowerDeriv k d ν (x * ((k : ℝ) ^ (2 * (d + 1)))⁻¹)

/-- Its log-scale profile `arcLineTowerProfile k d ν (v − 2(d+1) log k)`. -/
def arcLineForwardTowerProfile (k d : ℕ) (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  arcLineTowerProfile k d ν (v - ((2 * (d + 1) : ℕ) : ℝ) * Real.log k)

theorem hasDerivAt_arcLineForwardTowerVector (k d : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (x : ℝ) :
    HasDerivAt (arcLineForwardTowerVector k d ν) (arcLineForwardTowerDeriv k d ν x) x := by
  have hc : HasDerivAt (fun x' : ℝ => x' * ((k : ℝ) ^ (2 * (d + 1)))⁻¹)
      (((k : ℝ) ^ (2 * (d + 1)))⁻¹) x := by
    simpa using (hasDerivAt_id x).mul_const (((k : ℝ) ^ (2 * (d + 1)))⁻¹)
  have h := ((hasDerivAt_arcLineTowerVector k d ν
    (x * ((k : ℝ) ^ (2 * (d + 1)))⁻¹)).comp x hc).const_mul (((k : ℝ) ^ (d + 1))⁻¹)
  refine h.congr_deriv ?_
  unfold arcLineForwardTowerDeriv
  have hpow : (k : ℝ) ^ (3 * (d + 1)) = (k : ℝ) ^ (d + 1) * (k : ℝ) ^ (2 * (d + 1)) := by
    rw [show 3 * (d + 1) = (d + 1) + 2 * (d + 1) by ring, pow_add]
  rw [hpow, mul_inv]
  ring

theorem arcLineForwardTowerVector_neg_of_map_arcNeg (k d : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineForwardTowerVector k d ν (-x) = arcLineForwardTowerVector k d ν x := by
  unfold arcLineForwardTowerVector
  rw [neg_mul, arcLineTowerVector_neg_of_map_arcNeg k d hν]

theorem arcLineTowerDeriv_neg_of_map_arcNeg (k d : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) :
    ∀ x, arcLineTowerDeriv k d ν (-x) = -arcLineTowerDeriv k d ν x := by
  induction d with
  | zero => exact arcLineAtomicDeriv_neg_of_map_arcNeg (Real.log k) hν
  | succ d ih => exact hyperbolicFilterDeriv_neg k ih

theorem abs_arcLineTowerProfile_le {k : ℕ} (hk : 1 ≤ k) (d : ℕ) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    ∀ v, |arcLineTowerProfile k d ν v| ≤
      5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 3 * (1 + (k : ℝ) ^ 3) ^ d *
        Real.exp (-(3 * |v| / 2)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  induction d with
  | zero =>
    intro v
    have h0 := abs_arcLineAtomicProfile_le hb hν v
    have hexp3 : Real.exp (3 * Real.log k) = (k : ℝ) ^ 3 := by
      rw [show (3 : ℝ) * Real.log k = ((3 : ℕ) : ℝ) * Real.log k by norm_num,
        Real.exp_nat_mul, Real.exp_log hkpos]
    rw [hexp3] at h0
    simpa [arcLineTowerProfile] using h0
  | succ d ih =>
    intro v
    have hC : 0 ≤ 5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 3 *
        (1 + (k : ℝ) ^ 3) ^ d := by
      have := measureReal_nonneg (μ := ν) (s := univ)
      have := atomMass_nonneg (Real.log k)
      positivity
    have hstep := abs_hyperbolicFilterProfile_le hk hC ih v
    calc |arcLineTowerProfile k (d + 1) ν v|
        ≤ 5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 3 * (1 + (k : ℝ) ^ 3) ^ d *
            (1 + (k : ℝ) ^ 3) * Real.exp (-(3 * |v| / 2)) := hstep
      _ = 5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 3 * (1 + (k : ℝ) ^ 3) ^ (d + 1) *
            Real.exp (-(3 * |v| / 2)) := by rw [pow_succ]; ring

theorem arcLineForwardTowerDeriv_neg_of_map_arcNeg (k d : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineForwardTowerDeriv k d ν (-x) = -arcLineForwardTowerDeriv k d ν x := by
  unfold arcLineForwardTowerDeriv
  rw [neg_mul, arcLineTowerDeriv_neg_of_map_arcNeg k d hν, mul_neg]

/-- **`k^{2(d+1)}`-centered inversion covariance**:
`F_{k,d,ν}(k^{4(d+1)} / x) = (|x| / k^{2(d+1)}) F_{k,d,ν}(x)` for `x ≠ 0`. -/
theorem arcLineForwardTowerVector_inv_scaled {k : ℕ} (hk : 1 ≤ k) (d : ℕ) (ν : Measure ArcParam)
    {x : ℝ} (hx : x ≠ 0) :
    arcLineForwardTowerVector k d ν ((k : ℝ) ^ (4 * (d + 1)) / x) =
      |x| / (k : ℝ) ^ (2 * (d + 1)) * arcLineForwardTowerVector k d ν x := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hxne : x * ((k : ℝ) ^ (2 * (d + 1)))⁻¹ ≠ 0 :=
    mul_ne_zero hx (inv_ne_zero (pow_ne_zero (2 * (d + 1)) hkne))
  unfold arcLineForwardTowerVector
  have hpow : (k : ℝ) ^ (4 * (d + 1)) = (k : ℝ) ^ (2 * (d + 1)) * (k : ℝ) ^ (2 * (d + 1)) := by
    rw [show 4 * (d + 1) = 2 * (d + 1) + 2 * (d + 1) by ring, pow_add]
  have e : (k : ℝ) ^ (4 * (d + 1)) / x * ((k : ℝ) ^ (2 * (d + 1)))⁻¹ =
      1 / (x * ((k : ℝ) ^ (2 * (d + 1)))⁻¹) := by
    rw [hpow]
    field_simp
  rw [e, arcLineTowerVector_inv hk d ν _ hxne, abs_mul,
    abs_of_pos (inv_pos.mpr (pow_pos hkpos (2 * (d + 1))))]
  ring

theorem exp_half_mul_arcLineForwardTowerVector {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    (ν : Measure ArcParam) (v : ℝ) :
    Real.exp (v / 2) * arcLineForwardTowerVector k d ν (Real.exp v) =
      arcLineForwardTowerProfile k d ν v := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  unfold arcLineForwardTowerVector arcLineForwardTowerProfile
  have he2 : ((k : ℝ) ^ (2 * (d + 1)))⁻¹ =
      Real.exp (-(((2 * (d + 1) : ℕ) : ℝ) * Real.log k)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hkpos]
  have he1 : ((k : ℝ) ^ (d + 1))⁻¹ =
      Real.exp (-(((d + 1 : ℕ) : ℝ) * Real.log k)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hkpos]
  have e1 : Real.exp v * ((k : ℝ) ^ (2 * (d + 1)))⁻¹ =
      Real.exp (v - ((2 * (d + 1) : ℕ) : ℝ) * Real.log k) := by
    rw [he2, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (v / 2) * ((k : ℝ) ^ (d + 1))⁻¹ =
      Real.exp ((v - ((2 * (d + 1) : ℕ) : ℝ) * Real.log k) / 2) := by
    rw [he1, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [e1, ← mul_assoc, e2, exp_half_mul_arcLineTowerVector hk d ν]

/-! ### Full two-sided `O(e^{−3|v|/2})` Weil decay class, integrability, and zero mean -/

theorem abs_arcLineForwardTowerProfile_le {k : ℕ} (hk : 1 ≤ k) (d : ℕ) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineForwardTowerProfile k d ν v| ≤
      5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 3 * (1 + (k : ℝ) ^ 3) ^ d *
        (k : ℝ) ^ (3 * (d + 1)) * Real.exp (-(3 * |v| / 2)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  unfold arcLineForwardTowerProfile
  set w := ((2 * (d + 1) : ℕ) : ℝ) * Real.log k
  have hprof := abs_arcLineTowerProfile_le hk d hν (v - w)
  have hexp : Real.exp (((3 * (d + 1) : ℕ) : ℝ) * Real.log k) = (k : ℝ) ^ (3 * (d + 1)) := by
    rw [Real.exp_nat_mul, Real.exp_log hkpos]
  have hshift : Real.exp (-(3 * |v - w| / 2)) ≤
      (k : ℝ) ^ (3 * (d + 1)) * Real.exp (-(3 * |v| / 2)) := by
    rw [← hexp, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have habs : |v| - |w| ≤ |v - w| := abs_sub_abs_le_abs_sub v w
    have hw0 : 0 ≤ w := by positivity
    have hw_abs : |w| = w := abs_of_nonneg hw0
    have hw3 : 3 * w / 2 = ((3 * (d + 1) : ℕ) : ℝ) * Real.log k := by
      dsimp [w]; push_cast; ring
    linarith
  have hC0 : 0 ≤ 5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 3 * (1 + (k : ℝ) ^ 3) ^ d := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    have := atomMass_nonneg (Real.log k)
    positivity
  calc |arcLineTowerProfile k d ν (v - w)|
      ≤ 5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 3 * (1 + (k : ℝ) ^ 3) ^ d *
          Real.exp (-(3 * |v - w| / 2)) := hprof
    _ ≤ 5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 3 * (1 + (k : ℝ) ^ 3) ^ d *
          ((k : ℝ) ^ (3 * (d + 1)) * Real.exp (-(3 * |v| / 2))) :=
        mul_le_mul_of_nonneg_left hshift hC0
    _ = 5 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 3 * (1 + (k : ℝ) ^ 3) ^ d *
          (k : ℝ) ^ (3 * (d + 1)) * Real.exp (-(3 * |v| / 2)) := by ring

theorem integrable_arcLineForwardTowerVector {k : ℕ} (hk : 1 ≤ k) (d : ℕ) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Integrable (arcLineForwardTowerVector k d ν) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  exact ((integrable_arcLineTowerVector hk d hν).comp_mul_right'
    (inv_ne_zero (pow_ne_zero (2 * (d + 1)) hkpos.ne'))).const_mul (((k : ℝ) ^ (d + 1))⁻¹)

theorem integrable_arcLineForwardTowerDeriv {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineForwardTowerDeriv k d ν) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  exact ((integrable_arcLineTowerDeriv hk d ν).comp_mul_right'
    (inv_ne_zero (pow_ne_zero (2 * (d + 1)) hkpos.ne'))).const_mul (((k : ℝ) ^ (3 * (d + 1)))⁻¹)

theorem integral_arcLineForwardTowerVector_eq_zero {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    ∫ x, arcLineForwardTowerVector k d ν x = 0 := by
  unfold arcLineForwardTowerVector
  rw [integral_const_mul, Measure.integral_comp_mul_right
    (arcLineTowerVector k d ν) (((k : ℝ) ^ (2 * (d + 1)))⁻¹),
    integral_arcLineTowerVector_eq_zero hk d hν, smul_zero, mul_zero]

theorem arcLineForwardTowerProfile_add_shift (k d : ℕ) (ν : Measure ArcParam) (v : ℝ) :
    arcLineForwardTowerProfile k d ν (v + ((2 * (d + 1) : ℕ) : ℝ) * Real.log k) =
      arcLineTowerProfile k d ν v := by
  unfold arcLineForwardTowerProfile
  rw [add_sub_cancel_right]

/-- **Strict positive definiteness of the `2(d+1) log k`-centered log-profile on the critical line.** -/
theorem integral_cos_mul_arcLineForwardTowerProfile_add_pos {k : ℕ} (hk : 2 ≤ k) (d : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν]
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) *
      arcLineForwardTowerProfile k d ν (v + ((2 * (d + 1) : ℕ) : ℝ) * Real.log k) := by
  simp_rw [arcLineForwardTowerProfile_add_shift]
  exact integral_cos_mul_arcLineTowerProfile_pos hk d ν hpd τ

/-! ### Simultaneous blindness at ALL positive integer frequencies `arcFreq n = 2π(n+1)` (`n ∈ ℕ`) -/

theorem integral_arcLineForwardTowerDeriv_mul_cos_eq_zero (k d : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (c : ℝ) :
    ∫ x, arcLineForwardTowerDeriv k d ν x * Real.cos (c * x) = 0 := by
  have h := integral_neg_eq_self
    (fun x : ℝ => arcLineForwardTowerDeriv k d ν x * Real.cos (c * x)) volume
  have e : (fun x : ℝ => arcLineForwardTowerDeriv k d ν (-x) * Real.cos (c * -x)) =
      fun x => -(arcLineForwardTowerDeriv k d ν x * Real.cos (c * x)) := by
    funext x
    rw [arcLineForwardTowerDeriv_neg_of_map_arcNeg k d hν, mul_neg, Real.cos_neg, neg_mul]
  rw [e, integral_neg] at h
  linarith

/-- **Simultaneous sine blindness at EVERY positive integer frequency `arcFreq n = 2π(n+1)` (`n ∈ ℕ`).**
Rescaling `t = x / k^{2(d+1)}` maps `arcFreq n` onto `arcFreq (k^{2(d+1)}(n+1) − 1)`, which lies on
the `k^{2(d+1)}`-blind sublattice of `arcLineTowerDeriv k d ν`. -/
theorem integral_arcLineForwardTowerDeriv_mul_sin_eq_zero {ν : Measure ArcParam}
    [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (d n : ℕ) :
    ∫ x, arcLineForwardTowerDeriv k d ν x * Real.sin (arcFreq n * x) = 0 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  set N := k ^ (2 * (d + 1))
  have hN : 1 ≤ N := Nat.one_le_pow (2 * (d + 1)) k hk
  have hNcast : (N : ℝ) = (k : ℝ) ^ (2 * (d + 1)) := by dsimp [N]; push_cast; rfl
  have hfreq : arcFreq n * ((k : ℝ) ^ (2 * (d + 1))) = arcFreq (N * (n + 1) - 1) := by
    rw [← hNcast, Nat.mul_comm N (n + 1), ← arcFreq_mul_nat hN n]
  have e : (fun x => arcLineForwardTowerDeriv k d ν x * Real.sin (arcFreq n * x)) = fun x =>
      ((k : ℝ) ^ (3 * (d + 1)))⁻¹ * (arcLineTowerDeriv k d ν (x * ((k : ℝ) ^ (2 * (d + 1)))⁻¹) *
        Real.sin (arcFreq (N * (n + 1) - 1) * (x * ((k : ℝ) ^ (2 * (d + 1)))⁻¹))) := by
    funext x
    unfold arcLineForwardTowerDeriv
    rw [← hfreq]
    have hx : arcFreq n * (k : ℝ) ^ (2 * (d + 1)) * (x * ((k : ℝ) ^ (2 * (d + 1)))⁻¹) =
        arcFreq n * x := by
      field_simp
    rw [hx]; ring
  rw [e, integral_const_mul, Measure.integral_comp_mul_right
    (fun t => arcLineTowerDeriv k d ν t *
      Real.sin (arcFreq (N * (n + 1) - 1) * t)) (((k : ℝ) ^ (2 * (d + 1)))⁻¹),
    integral_arcLineTowerDeriv_mul_sin_sublattice_eq_zero hblind hk d n,
    smul_zero, mul_zero]

/-! ### Arbitrary-order `(1/2 − l)^{d+1}` strip-edge vanishing for `arcLineForwardTowerProfile` -/

theorem integral_exp_mul_arcLineForwardTowerProfile (k d : ℕ) (ν : Measure ArcParam) (l : ℝ) :
    ∫ v, Real.exp (l * v) * arcLineForwardTowerProfile k d ν v =
      Real.exp (l * (((2 * (d + 1) : ℕ) : ℝ) * Real.log k)) *
        ∫ v, Real.exp (l * v) * arcLineTowerProfile k d ν v := by
  unfold arcLineForwardTowerProfile
  set w := ((2 * (d + 1) : ℕ) : ℝ) * Real.log k
  rw [← integral_add_right_eq_self (μ := volume)
    (fun v => Real.exp (l * v) * arcLineTowerProfile k d ν (v - w)) w, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [add_sub_cancel_right, show l * (v + w) = l * w + l * v by ring, Real.exp_add]
  ring

/-- **Arbitrary-order `O((1/2 − l)^{d+1})` strip-edge vanishing bound for `arcLineForwardTowerProfile`.** -/
theorem abs_integral_exp_mul_arcLineForwardTowerProfile_le {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |∫ v, Real.exp (l * v) * arcLineForwardTowerProfile k d ν v| ≤
      10 * ν.real univ * (k : ℝ) ^ (d + 1) * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
        (1 / 2 - l) ^ (d + 1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hexp : Real.exp (((d + 1 : ℕ) : ℝ) * Real.log k) = (k : ℝ) ^ (d + 1) := by
    rw [Real.exp_nat_mul, Real.exp_log hkpos]
  have hexp_le : Real.exp (l * (((2 * (d + 1) : ℕ) : ℝ) * Real.log k)) ≤ (k : ℝ) ^ (d + 1) := by
    rw [← hexp]
    refine Real.exp_le_exp.mpr ?_
    have h2 : (((2 * (d + 1) : ℕ) : ℝ) * Real.log k) = 2 * (((d + 1 : ℕ) : ℝ) * Real.log k) := by
      push_cast; ring
    have hd0 : 0 ≤ ((d + 1 : ℕ) : ℝ) * Real.log k := by positivity
    nlinarith
  rw [integral_exp_mul_arcLineForwardTowerProfile, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hT := abs_integral_exp_mul_arcLineTowerProfile_le hk d hν hl0 hl
  have hRHS0 : 0 ≤ 10 * ν.real univ * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
      (1 / 2 - l) ^ (d + 1) := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    have hκ : 0 ≤ 1 / 2 - l := by linarith
    positivity
  calc Real.exp (l * (((2 * (d + 1) : ℕ) : ℝ) * Real.log k)) *
        |∫ v, Real.exp (l * v) * arcLineTowerProfile k d ν v|
      ≤ (k : ℝ) ^ (d + 1) * (10 * ν.real univ * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
          (1 / 2 - l) ^ (d + 1)) :=
        mul_le_mul hexp_le hT (abs_nonneg _) (by positivity)
    _ = 10 * ν.real univ * (k : ℝ) ^ (d + 1) * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
          (1 / 2 - l) ^ (d + 1) := by ring

/-- **`d`-th divided-difference bound at the strip edge for `arcLineForwardTowerProfile`.** -/
theorem abs_div_pow_integral_exp_mul_arcLineForwardTowerProfile_le {k : ℕ} (hk : 1 ≤ k) (d : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |(∫ v, Real.exp (l * v) * arcLineForwardTowerProfile k d ν v) / (1 / 2 - l) ^ d| ≤
      10 * ν.real univ * (k : ℝ) ^ (d + 1) * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
        (1 / 2 - l) := by
  have hκ : 0 < 1 / 2 - l := by linarith
  have hpow : 0 < (1 / 2 - l) ^ d := pow_pos hκ d
  rw [abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
  calc |∫ v, Real.exp (l * v) * arcLineForwardTowerProfile k d ν v|
      ≤ 10 * ν.real univ * (k : ℝ) ^ (d + 1) * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
          (1 / 2 - l) ^ (d + 1) :=
        abs_integral_exp_mul_arcLineForwardTowerProfile_le hk d hν hl0 hl
    _ = 10 * ν.real univ * (k : ℝ) ^ (d + 1) * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
          (1 / 2 - l) * (1 / 2 - l) ^ d := by rw [pow_succ']; ring

/-- **`d`-th divided-difference vanishing as `l → (1/2)⁻` for `arcLineForwardTowerProfile`.** -/
theorem tendsto_div_pow_integral_exp_mul_arcLineForwardTowerProfile_nhdsWithin
    {k : ℕ} (hk : 1 ≤ k) (d : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      (∫ v, Real.exp (l * v) * arcLineForwardTowerProfile k d ν v) / (1 / 2 - l) ^ d)
      (𝓝[<] (1 / 2)) (𝓝 0) := by
  set D := 10 * ν.real univ * (k : ℝ) ^ (d + 1) * (Real.log k) ^ 2 * (2 * Real.log k) ^ d
  have hlin : Tendsto (fun l : ℝ => D * (1 / 2 - l)) (𝓝[<] (1 / 2)) (𝓝 0) := by
    have hcont : Continuous fun l : ℝ => D * (1 / 2 - l) := by fun_prop
    have h := (hcont.continuousAt (x := (1 / 2 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 / 2 : ℝ)))
    rwa [sub_self, mul_zero] at h
  refine squeeze_zero_norm' ?_ hlin
  have hmem : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[<] (1 / 2 : ℝ) :=
    Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hmem] with l hl
  rw [Real.norm_eq_abs]
  exact abs_div_pow_integral_exp_mul_arcLineForwardTowerProfile_le hk d hν hl.1.le hl.2

/-! ### Master unconditional arbitrary-order all-integer-blind tower theorem -/

/-- **Master unconditional theorem for arbitrary-order all-integer-blind modular arc witnesses.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2` and every prescribed order `d ∈ ℕ`, `arcLineForwardTowerVector k d ν` is a
single fixed function in the full two-sided `O(e^{−3|v|/2})` Weil decay class (even, integrable
with zero mean, `k^{2(d+1)}`-centered inversion-covariant, and strictly positive definite on the
critical line after centering at `2(d+1) log k`) whose derivative is **simultaneously blind at
EVERY positive integer frequency `arcFreq n = 2π(n+1)` (`n ∈ ℕ`)** AND whose strip Laplace/Mellin
transform vanishes to **arbitrary order `(1/2 − l)^{d+1}`** at the critical strip edge `l → (1/2)⁻`,
with vanishing `d`-th divided difference on `𝓝[<] (1/2)`. -/
theorem exists_arbitraryOrder_allInteger_blind_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      ∀ k : ℕ, 2 ≤ k → ∀ d : ℕ,
        (∀ x, HasDerivAt (arcLineForwardTowerVector k d ν)
          (arcLineForwardTowerDeriv k d ν x) x) ∧
        (∀ x, arcLineForwardTowerVector k d ν (-x) = arcLineForwardTowerVector k d ν x) ∧
        (∀ x, x ≠ 0 → arcLineForwardTowerVector k d ν ((k : ℝ) ^ (4 * (d + 1)) / x) =
          |x| / (k : ℝ) ^ (2 * (d + 1)) * arcLineForwardTowerVector k d ν x) ∧
        Integrable (arcLineForwardTowerVector k d ν) ∧
        Integrable (arcLineForwardTowerDeriv k d ν) ∧
        ∫ x, arcLineForwardTowerVector k d ν x = 0 ∧
        (∀ n : ℕ, ∫ x, arcLineForwardTowerDeriv k d ν x * Real.sin (arcFreq n * x) = 0 ∧
          ∫ x, arcLineForwardTowerDeriv k d ν x * Real.cos (arcFreq n * x) = 0) ∧
        (∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) *
          arcLineForwardTowerProfile k d ν (v + ((2 * (d + 1) : ℕ) : ℝ) * Real.log k)) ∧
        (∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
          |∫ v, Real.exp (l * v) * arcLineForwardTowerProfile k d ν v| ≤
            10 * ν.real univ * (k : ℝ) ^ (d + 1) * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
              (1 / 2 - l) ^ (d + 1)) ∧
        Tendsto (fun l : ℝ =>
          (∫ v, Real.exp (l * v) * arcLineForwardTowerProfile k d ν v) / (1 / 2 - l) ^ d)
          (𝓝[<] (1 / 2)) (𝓝 0) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym, fun k hk d => ?_⟩
  have hk1 : 1 ≤ k := by omega
  exact ⟨hasDerivAt_arcLineForwardTowerVector k d ν,
    arcLineForwardTowerVector_neg_of_map_arcNeg k d hsym,
    fun x hx => arcLineForwardTowerVector_inv_scaled hk1 d ν hx,
    integrable_arcLineForwardTowerVector hk1 d hsym,
    integrable_arcLineForwardTowerDeriv hk1 d ν,
    integral_arcLineForwardTowerVector_eq_zero hk1 d hsym,
    fun n => ⟨integral_arcLineForwardTowerDeriv_mul_sin_eq_zero hblind hk1 d n,
      integral_arcLineForwardTowerDeriv_mul_cos_eq_zero k d hsym (arcFreq n)⟩,
    integral_cos_mul_arcLineForwardTowerProfile_add_pos hk d ν hpd,
    fun l hl0 hl => abs_integral_exp_mul_arcLineForwardTowerProfile_le hk1 d hsym hl0 hl,
    tendsto_div_pow_integral_exp_mul_arcLineForwardTowerProfile_nhdsWithin hk1 d hsym⟩

end

end RHTower
