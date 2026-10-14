import GaloisForLFunctions.RHTower.ModularArcDyadicInversionDuality

/-!
# Telescoping decomposition and depth-and-scale-uniform `O(√c)` bounds for the dyadic modular arc tower

In `ModularArcDyadicHyperbolicTower` and `ModularArcDyadicInversionDuality`, we established that
at dyadic depth `r ∈ ℕ`, `arcLineDyadicTowerDeriv k r ν` and `arcLineSymDyadicTowerDeriv k r ν`
satisfy the `k`-independent square-root frequency bound
`2^r · (8 √(π/2) · ν.real univ) · √c` (and half that constant at integer frequencies `arcFreq n`
for `arcLineSymDyadicTowerDeriv`), while each dyadic step satisfies the exact identity
`arcLineDyadicTowerVector k (r + 1) ν x = arcLineDyadicTowerVector k r ν x − (1 / cosh(log(k^{2^r}))) · arcLineSymDyadicTowerVector k r ν x`.

In this module we combine this **exact telescoping decomposition** with the elementary inequality
`2 r ≤ 2^r + 1` (`r ∈ ℕ`), which shows that for every integer `k ≥ 2`, the doubly-exponential
denominator `cosh(log(k^{2^r})) ≥ k^{2^r} / 2 ≥ 2^{2r − 2} = 4^r / 4` crushes the `2^r` numerator:
`2^r / cosh(log(k^{2^r})) ≤ 4 · (1/2)^r`. Summing the geometric telescoping series eliminates the
`2^R` depth factor altogether, yielding **universal `O(√c)` frequency bounds that are simultaneously
independent of BOTH the integer scale `k ≥ 2` AND the pole-cancellation depth `R ∈ ℕ`**:

## Main results

1. **Exact finite-horizon telescoping decompositions (`arcLineDyadicTowerVector_eq_atomic_sub_sum`,
   `arcLineDyadicTowerDeriv_eq_atomic_sub_sum`, `arcLineDyadicTowerProfile_eq_atomic_sub_sum`,
   `integral_arcLineDyadicTowerDeriv_mul_sin_eq_atomic_sub_sum`):**
   Level `R` of the dyadic tower equals the base atomic witness minus the finite weighted sum of
   the self-reciprocal symmetrizations `arcLineSymDyadicTower* k r ν` (`0 ≤ r < R`) with weights
   `1 / cosh(log(k^{2^r}))`.
2. **Geometric Cauchy step bounds (`two_pow_div_cosh_log_pow_two_pow_le`,
   `abs_integral_arcLineDyadicTowerDeriv_succ_sub_le`,
   `abs_integral_arcLineDyadicTowerDeriv_succ_sub_arcFreq_le`):**
   For all `k ≥ 2`, `r ∈ ℕ`, and `c > 0`, the step increment between levels `r` and `r + 1` is
   bounded by `(32 √(π/2) · ν.real univ · √c) · (1/2)^r` (and by
   `(16 √(π/2) · ν.real univ · √(arcFreq n)) · (1/2)^r` at positive integer frequencies).
3. **Depth-and-scale-uniform `O(√c)` bounds across all `k ≥ 2` and all `R ∈ ℕ`
   (`abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_uniform`,
   `abs_integral_arcLineForwardDyadicTowerDeriv_mul_sin_le_uniform`,
   `abs_integral_arcLineBackwardDyadicTowerDeriv_mul_sin_le_uniform`,
   `abs_integral_arcLineSymDyadicTowerDeriv_mul_sin_le_uniform`,
   `abs_integral_arcLineSymDyadicTowerDeriv_mul_sin_arcFreq_le_uniform`):**
   For **every** `k ≥ 2`, **every** pole-cancellation depth `R ∈ ℕ`, and **every** `c > 0`, the
   sine moments of `arcLineDyadicTowerDeriv k R ν`, `arcLineForwardDyadicTowerDeriv k R ν`,
   `arcLineBackwardDyadicTowerDeriv k R ν`, and `arcLineSymDyadicTowerDeriv k R ν` are all bounded
   by `72 √(π/2) · ν.real univ · √c` (and by `36 √(π/2) · ν.real univ · √(arcFreq n)` at integer
   frequencies for `arcLineSymDyadicTowerDeriv k R ν`), with an absolute constant independent of
   both `k` and `R` (`exists_dyadic_depthAndScaleUniform_arcWitness`).
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Exponent-doubling domination and geometric partial-sum bounds -/

/-- For every `r ∈ ℕ`, `2 * r ≤ 2 ^ r + 1`. -/
theorem two_mul_le_two_pow_add_one : ∀ r : ℕ, 2 * r ≤ 2 ^ r + 1
  | 0 => by decide
  | 1 => by decide
  | r + 2 => by
    have ih := two_mul_le_two_pow_add_one (r + 1)
    have h2 : 2 ≤ 2 ^ (r + 1) := by
      rw [pow_succ]
      have := Nat.one_le_pow r 2 (by omega)
      omega
    have hpow : 2 ^ (r + 2) = 2 ^ (r + 1) + 2 ^ (r + 1) := by rw [pow_succ]; omega
    omega

/-- For every integer `k ≥ 2` and `r ∈ ℕ`, `(2 : ℝ)^r · (2 : ℝ)^r ≤ 2 · k^{2^r}`. -/
theorem two_pow_mul_two_pow_le_two_mul_pow_two_pow {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    (2 : ℝ) ^ r * (2 : ℝ) ^ r ≤ 2 * ((k ^ (2 ^ r) : ℕ) : ℝ) := by
  have hnat : 2 ^ r * 2 ^ r ≤ 2 * k ^ (2 ^ r) := by
    calc 2 ^ r * 2 ^ r = 2 ^ (r + r) := (pow_add 2 r r).symm
      _ = 2 ^ (2 * r) := by rw [two_mul]
      _ ≤ 2 ^ (2 ^ r + 1) := Nat.pow_le_pow_right (by omega) (two_mul_le_two_pow_add_one r)
      _ = 2 * 2 ^ (2 ^ r) := by rw [pow_succ']
      _ ≤ 2 * k ^ (2 ^ r) := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hk (2 ^ r))
  exact_mod_cast hnat

/-- **Doubly-exponential denominator crushes singly-exponential numerator:**
For every `k ≥ 2` and `r ∈ ℕ`, `(2 : ℝ)^r / cosh(log(k^{2^r})) ≤ 4 · (1/2)^r`. -/
theorem two_pow_div_cosh_log_pow_two_pow_le {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    (2 : ℝ) ^ r / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) ≤ 4 * (1 / 2 : ℝ) ^ r := by
  have hk1 : 1 ≤ k := by omega
  have hm : 1 ≤ k ^ (2 ^ r) := one_le_pow_two_pow hk1 r
  have hcosh_pos : 0 < Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) := Real.cosh_pos _
  have h1 := nat_le_two_mul_cosh_log hm
  have h2 := two_pow_mul_two_pow_le_two_mul_pow_two_pow hk r
  have hprod : (2 : ℝ) ^ r * (2 : ℝ) ^ r ≤
      4 * Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) := by linarith
  rw [div_le_iff₀ hcosh_pos]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hcancel : (4 * (1 / 2 : ℝ) ^ r * Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) * (2 : ℝ) ^ r =
      4 * Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) := by
    calc (4 * (1 / 2 : ℝ) ^ r * Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) * (2 : ℝ) ^ r
        = 4 * Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) * ((1 / 2 : ℝ) ^ r * (2 : ℝ) ^ r) := by ring
      _ = 4 * Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) * ((1 / 2 : ℝ) * 2) ^ r := by
          rw [← mul_pow]
      _ = 4 * Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) := by norm_num
  nlinarith

/-- Exact closed form for the geometric partial sum `∑_{r < R} (1/2)^r = 2 − 2 · (1/2)^R`. -/
theorem sum_range_half_pow (R : ℕ) :
    ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r = 2 - 2 * (1 / 2 : ℝ) ^ R := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

theorem sum_range_half_pow_le_two (R : ℕ) :
    ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r ≤ 2 := by
  rw [sum_range_half_pow R]
  have : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ R := by positivity
  linarith

/-! ### Exact finite-horizon telescoping decompositions of the dyadic tower -/

theorem arcLineDyadicTowerDeriv_succ_eq_sub_sym (k r : ℕ) (ν : Measure ArcParam) (x : ℝ) :
    arcLineDyadicTowerDeriv k (r + 1) ν x =
      arcLineDyadicTowerDeriv k r ν x -
        (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
          arcLineSymDyadicTowerDeriv k r ν x :=
  hyperbolicFilterDeriv_eq_sub_symScaleDeriv (k ^ (2 ^ r)) (arcLineDyadicTowerDeriv k r ν) x

theorem arcLineDyadicTowerProfile_succ_eq_sub_sym (k r : ℕ) (ν : Measure ArcParam) (v : ℝ) :
    arcLineDyadicTowerProfile k (r + 1) ν v =
      arcLineDyadicTowerProfile k r ν v -
        (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
          arcLineSymDyadicTowerProfile k r ν v :=
  hyperbolicFilterProfile_eq_sub_symScaleProfile (k ^ (2 ^ r)) (arcLineDyadicTowerProfile k r ν) v

/-- **Telescoping decomposition of `arcLineDyadicTowerVector k R ν`.** -/
theorem arcLineDyadicTowerVector_eq_atomic_sub_sum (k R : ℕ) (ν : Measure ArcParam) (x : ℝ) :
    arcLineDyadicTowerVector k R ν x =
      arcLineAtomicVector (Real.log k) ν x -
        ∑ r ∈ Finset.range R,
          (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
            arcLineSymDyadicTowerVector k r ν x := by
  induction R with
  | zero => simp [arcLineDyadicTowerVector]
  | succ R ih =>
    rw [arcLineDyadicTowerVector_succ_eq_sub_sym, ih, Finset.sum_range_succ]
    ring

/-- **Telescoping decomposition of `arcLineDyadicTowerDeriv k R ν`.** -/
theorem arcLineDyadicTowerDeriv_eq_atomic_sub_sum (k R : ℕ) (ν : Measure ArcParam) (x : ℝ) :
    arcLineDyadicTowerDeriv k R ν x =
      arcLineAtomicDeriv (Real.log k) ν x -
        ∑ r ∈ Finset.range R,
          (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
            arcLineSymDyadicTowerDeriv k r ν x := by
  induction R with
  | zero => simp [arcLineDyadicTowerDeriv]
  | succ R ih =>
    rw [arcLineDyadicTowerDeriv_succ_eq_sub_sym, ih, Finset.sum_range_succ]
    ring

/-- **Telescoping decomposition of `arcLineDyadicTowerProfile k R ν`.** -/
theorem arcLineDyadicTowerProfile_eq_atomic_sub_sum (k R : ℕ) (ν : Measure ArcParam) (v : ℝ) :
    arcLineDyadicTowerProfile k R ν v =
      arcLineAtomicProfile (Real.log k) ν v -
        ∑ r ∈ Finset.range R,
          (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
            arcLineSymDyadicTowerProfile k r ν v := by
  induction R with
  | zero => simp [arcLineDyadicTowerProfile]
  | succ R ih =>
    rw [arcLineDyadicTowerProfile_succ_eq_sub_sym, ih, Finset.sum_range_succ]
    ring

/-- **Exact sine-moment step identity for the dyadic tower:**
For every `k ≥ 1`, `r ∈ ℕ`, and `c ∈ ℝ`, the difference between the sine moments at levels
`r + 1` and `r` equals `−(1 / cosh(log(k^{2^r})))` times the sine moment of
`arcLineSymDyadicTowerDeriv k r ν`. -/
theorem integral_arcLineDyadicTowerDeriv_succ_mul_sin_sub
    {k : ℕ} (hk : 1 ≤ k) (r : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (c : ℝ) :
    (∫ x, arcLineDyadicTowerDeriv k (r + 1) ν x * Real.sin (c * x)) -
        (∫ x, arcLineDyadicTowerDeriv k r ν x * Real.sin (c * x)) =
      -(1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        ∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x) := by
  have hD : Integrable fun x => arcLineDyadicTowerDeriv k r ν x * Real.sin (c * x) :=
    (integrable_arcLineDyadicTowerDeriv hk r ν).mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hS : Integrable fun x => arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x) :=
    (integrable_symScaleDeriv (one_le_pow_two_pow hk r)
      (integrable_arcLineDyadicTowerDeriv hk r ν)).mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have e : (fun x => arcLineDyadicTowerDeriv k (r + 1) ν x * Real.sin (c * x)) = fun x =>
      arcLineDyadicTowerDeriv k r ν x * Real.sin (c * x) -
        (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
          (arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x)) := by
    funext x
    rw [arcLineDyadicTowerDeriv_succ_eq_sub_sym]
    ring
  rw [e, integral_sub hD (hS.const_mul _), integral_const_mul]
  ring

/-- **Exact telescoping sine-moment expansion across dyadic depth `R ∈ ℕ`.** -/
theorem integral_arcLineDyadicTowerDeriv_mul_sin_eq_atomic_sub_sum
    {k : ℕ} (hk : 1 ≤ k) (R : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (c : ℝ) :
    ∫ x, arcLineDyadicTowerDeriv k R ν x * Real.sin (c * x) =
      (∫ x, arcLineAtomicDeriv (Real.log k) ν x * Real.sin (c * x)) -
        ∑ r ∈ Finset.range R,
          (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
            ∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x) := by
  induction R with
  | zero => simp [arcLineDyadicTowerDeriv]
  | succ R ih =>
    have hstep := integral_arcLineDyadicTowerDeriv_succ_mul_sin_sub hk R ν c
    rw [Finset.sum_range_succ]
    linarith

/-! ### Geometric Cauchy step bounds and depth-and-scale-uniform `O(√c)` bounds -/

/-- **Geometric `(1/2)^r` Cauchy step bound at any real frequency `c > 0` (`k ≥ 2`).** -/
theorem abs_integral_arcLineDyadicTowerDeriv_succ_sub_le
    {k : ℕ} (hk : 2 ≤ k) (r : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {c : ℝ} (hc : 0 < c) :
    |(∫ x, arcLineDyadicTowerDeriv k (r + 1) ν x * Real.sin (c * x)) -
        (∫ x, arcLineDyadicTowerDeriv k r ν x * Real.sin (c * x))| ≤
      (32 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c) * (1 / 2 : ℝ) ^ r := by
  have hk1 : 1 ≤ k := by omega
  rw [integral_arcLineDyadicTowerDeriv_succ_mul_sin_sub hk1 r ν c,
    abs_mul, abs_neg, abs_of_pos (by positivity)]
  have hS : |∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x)| ≤
      2 ^ r * (8 * Real.sqrt (Real.pi / 2) * ν.real univ) * Real.sqrt c :=
    abs_integral_symScaleDeriv_mul_sin_le_sqrt (one_le_pow_two_pow hk1 r)
      (integrable_arcLineDyadicTowerDeriv hk1 r ν)
      (fun _ hω => abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_sqrt hk1 r ν hω) hc
  have hratio := two_pow_div_cosh_log_pow_two_pow_le hk r
  have hB0 : 0 ≤ 8 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  calc 1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) *
        |∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x)|
      ≤ 1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) *
          ((2 : ℝ) ^ r * (8 * Real.sqrt (Real.pi / 2) * ν.real univ) * Real.sqrt c) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = ((2 : ℝ) ^ r / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
          (8 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c) := by ring
    _ ≤ (4 * (1 / 2 : ℝ) ^ r) *
          (8 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c) :=
        mul_le_mul_of_nonneg_right hratio hB0
    _ = (32 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c) * (1 / 2 : ℝ) ^ r := by ring

/-- **Halved geometric `(1/2)^r` Cauchy step bound at all positive integer frequencies `arcFreq n`.** -/
theorem abs_integral_arcLineDyadicTowerDeriv_succ_sub_arcFreq_le
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 2 ≤ k) (r n : ℕ) :
    |(∫ x, arcLineDyadicTowerDeriv k (r + 1) ν x * Real.sin (arcFreq n * x)) -
        (∫ x, arcLineDyadicTowerDeriv k r ν x * Real.sin (arcFreq n * x))| ≤
      (16 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n)) * (1 / 2 : ℝ) ^ r := by
  have hk1 : 1 ≤ k := by omega
  rw [integral_arcLineDyadicTowerDeriv_succ_mul_sin_sub hk1 r ν (arcFreq n),
    abs_mul, abs_neg, abs_of_pos (by positivity)]
  have hS := abs_integral_arcLineSymDyadicTowerDeriv_mul_sin_arcFreq_le hblind hk1 r n
  have hratio := two_pow_div_cosh_log_pow_two_pow_le hk r
  have hB0 : 0 ≤ 4 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n) := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    have := arcFreq_pos n
    positivity
  calc 1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) *
        |∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (arcFreq n * x)|
      ≤ 1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) *
          ((2 : ℝ) ^ r * (4 * Real.sqrt (Real.pi / 2) * ν.real univ) * Real.sqrt (arcFreq n)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = ((2 : ℝ) ^ r / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
          (4 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n)) := by ring
    _ ≤ (4 * (1 / 2 : ℝ) ^ r) *
          (4 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n)) :=
        mul_le_mul_of_nonneg_right hratio hB0
    _ = (16 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n)) *
          (1 / 2 : ℝ) ^ r := by ring

/-- **Depth-and-scale-uniform `O(√c)` frequency bound for `arcLineDyadicTowerDeriv k R ν`:**
For **every** integer `k ≥ 2`, **every** dyadic depth `R ∈ ℕ`, and **every** `c > 0`,
`|∫ arcLineDyadicTowerDeriv k R ν x · sin(c x) dx| ≤ 72 √(π/2) · ν.real univ · √c`
(with an absolute constant completely independent of BOTH `k` and `R`). -/
theorem abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_uniform
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {c : ℝ} (hc : 0 < c) :
    |∫ x, arcLineDyadicTowerDeriv k R ν x * Real.sin (c * x)| ≤
      72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c := by
  have hk1 : 1 ≤ k := by omega
  rw [integral_arcLineDyadicTowerDeriv_mul_sin_eq_atomic_sub_sum hk1 R ν c]
  have h0 := abs_integral_arcLineAtomicDeriv_mul_sin_le_sqrt (Real.log k) ν hc
  set B := 8 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c
  have hB0 : 0 ≤ B := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  have hsum : |∑ r ∈ Finset.range R,
      (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        ∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x)| ≤
      (4 * B) * ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    have hr := abs_integral_arcLineDyadicTowerDeriv_succ_sub_le hk r ν hc
    rw [integral_arcLineDyadicTowerDeriv_succ_mul_sin_sub hk1 r ν c, abs_mul, abs_neg] at hr
    have hmul : |(1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        ∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x)| =
      |1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))| *
        |∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x)| := abs_mul _ _
    rw [hmul]
    refine hr.trans_eq ?_
    dsimp [B]; ring
  have hgeom : (4 * B) * ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r ≤ 8 * B := by
    have h2 := sum_range_half_pow_le_two R
    nlinarith
  have hsub := abs_sub (∫ x, arcLineAtomicDeriv (Real.log k) ν x * Real.sin (c * x))
    (∑ r ∈ Finset.range R,
      (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        ∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x))
  calc |(∫ x, arcLineAtomicDeriv (Real.log k) ν x * Real.sin (c * x)) -
        ∑ r ∈ Finset.range R,
          (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
            ∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x)|
      ≤ B + 8 * B := by linarith
    _ = 72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c := by dsimp [B]; ring

/-- **Depth-and-scale-uniform `O(√c)` bound for `arcLineForwardDyadicTowerDeriv k R ν`.** -/
theorem abs_integral_arcLineForwardDyadicTowerDeriv_mul_sin_le_uniform
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {c : ℝ} (hc : 0 < c) :
    |∫ x, arcLineForwardDyadicTowerDeriv k R ν x * Real.sin (c * x)| ≤
      72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c :=
  abs_integral_forwardScaleDeriv_mul_sin_le_sqrt (one_le_pow_two_pow (by omega) R)
    (fun _ hω => abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_uniform hk R ν hω) hc

/-- **Depth-and-scale-uniform `O(√c)` bound for `arcLineBackwardDyadicTowerDeriv k R ν`.** -/
theorem abs_integral_arcLineBackwardDyadicTowerDeriv_mul_sin_le_uniform
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {c : ℝ} (hc : 0 < c) :
    |∫ x, arcLineBackwardDyadicTowerDeriv k R ν x * Real.sin (c * x)| ≤
      72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c :=
  abs_integral_backwardScaleDeriv_mul_sin_le_sqrt (one_le_pow_two_pow (by omega) R)
    (fun _ hω => abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_uniform hk R ν hω) hc

/-- **Depth-and-scale-uniform `O(√c)` bound for `arcLineSymDyadicTowerDeriv k R ν`.** -/
theorem abs_integral_arcLineSymDyadicTowerDeriv_mul_sin_le_uniform
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {c : ℝ} (hc : 0 < c) :
    |∫ x, arcLineSymDyadicTowerDeriv k R ν x * Real.sin (c * x)| ≤
      72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c :=
  abs_integral_symScaleDeriv_mul_sin_le_sqrt (one_le_pow_two_pow (by omega) R)
    (integrable_arcLineDyadicTowerDeriv (by omega) R ν)
    (fun _ hω => abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_uniform hk R ν hω) hc

/-- **Halved depth-and-scale-uniform `O(√(arcFreq n))` bound at all integer frequencies for `arcLineSymDyadicTowerDeriv`.**
For every `k ≥ 2`, every pole-cancellation depth `R ∈ ℕ`, and every integer frequency `arcFreq n`,
`|∫ arcLineSymDyadicTowerDeriv k R ν x · sin(arcFreq n · x) dx| ≤ 36 √(π/2) · ν.real univ · √(arcFreq n)`
independently of both `k` and `R`. -/
theorem abs_integral_arcLineSymDyadicTowerDeriv_mul_sin_arcFreq_le_uniform
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 2 ≤ k) (R n : ℕ) :
    |∫ x, arcLineSymDyadicTowerDeriv k R ν x * Real.sin (arcFreq n * x)| ≤
      36 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n) := by
  have hk1 : 1 ≤ k := by omega
  have h := abs_integral_symScaleDeriv_mul_sin_arcFreq_le (one_le_pow_two_pow hk1 R)
    (integrable_arcLineDyadicTowerDeriv hk1 R ν)
    (fun j => by
      rw [pow_two_pow_sq]
      exact integral_arcLineDyadicTowerDeriv_mul_sin_sublattice_eq_zero hblind hk1 R j)
    (fun _ hω => abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_uniform hk R ν hω) n
  refine h.trans_eq ?_
  ring

/-! ### Master unconditional depth-and-scale-uniform dyadic tower theorem -/

/-- **Master unconditional theorem for the depth-and-scale-uniform dyadic modular arc tower.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for **every** integer `k ≥ 2` and **every** pole-cancellation depth `R ∈ ℕ`:
1. `arcLineDyadicTowerDeriv k R ν`, `arcLineForwardDyadicTowerDeriv k R ν`,
   `arcLineBackwardDyadicTowerDeriv k R ν`, and `arcLineSymDyadicTowerDeriv k R ν` all satisfy the
   **depth-and-scale-uniform square-root frequency bound**
   `|∫ f'(x) sin(c x) dx| ≤ 72 √(π/2) · ν.real univ · √c` for all `c > 0`, with constant
   completely independent of both `k` and `R`;
2. At every positive integer frequency `arcFreq n = 2π(n+1)` (`n ∈ ℕ`),
   `arcLineForwardDyadicTowerDeriv k R ν` vanishes identically and
   `arcLineSymDyadicTowerDeriv k R ν` satisfies the halved uniform bound
   `|∫ S'(x) sin(arcFreq n · x) dx| ≤ 36 √(π/2) · ν.real univ · √(arcFreq n)` while vanishing
   identically on the doubly-exponential `k^{2^{R+2}}`-sublattice;
3. Both `arcLineDyadicTowerProfile k R ν` and `arcLineSymDyadicTowerProfile k R ν` vanish to
   order `O((1/2 − l)^{R+1})` as `l → (1/2)⁻`, with vanishing `R`-th divided difference on
   `𝓝[<] (1/2)`. -/
theorem exists_dyadic_depthAndScaleUniform_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      ∀ k : ℕ, 2 ≤ k → ∀ R : ℕ,
        (∀ c : ℝ, 0 < c →
          |∫ x, arcLineDyadicTowerDeriv k R ν x * Real.sin (c * x)| ≤
            72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c) ∧
        (∀ c : ℝ, 0 < c →
          |∫ x, arcLineForwardDyadicTowerDeriv k R ν x * Real.sin (c * x)| ≤
            72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c) ∧
        (∀ c : ℝ, 0 < c →
          |∫ x, arcLineSymDyadicTowerDeriv k R ν x * Real.sin (c * x)| ≤
            72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c) ∧
        (∀ n : ℕ, ∫ x, arcLineForwardDyadicTowerDeriv k R ν x * Real.sin (arcFreq n * x) = 0) ∧
        (∀ n : ℕ, |∫ x, arcLineSymDyadicTowerDeriv k R ν x * Real.sin (arcFreq n * x)| ≤
          36 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n)) ∧
        (∀ j : ℕ, ∫ x, arcLineSymDyadicTowerDeriv k R ν x *
          Real.sin (arcFreq (k ^ (2 ^ (R + 2)) * (j + 1) - 1) * x) = 0) ∧
        Tendsto (fun l : ℝ =>
          (∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k R ν v) / (1 / 2 - l) ^ R)
          (𝓝[<] (1 / 2)) (𝓝 0) ∧
        Tendsto (fun l : ℝ =>
          (∫ v, Real.exp (l * v) * arcLineSymDyadicTowerProfile k R ν v) / (1 / 2 - l) ^ R)
          (𝓝[<] (1 / 2)) (𝓝 0) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, _⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym, fun k hk R => ?_⟩
  have hk1 : 1 ≤ k := by omega
  exact ⟨fun c hc => abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_uniform hk R ν hc,
    fun c hc => abs_integral_arcLineForwardDyadicTowerDeriv_mul_sin_le_uniform hk R ν hc,
    fun c hc => abs_integral_arcLineSymDyadicTowerDeriv_mul_sin_le_uniform hk R ν hc,
    integral_arcLineForwardDyadicTowerDeriv_mul_sin_eq_zero hblind hk1 R,
    abs_integral_arcLineSymDyadicTowerDeriv_mul_sin_arcFreq_le_uniform hblind hk R,
    integral_arcLineSymDyadicTowerDeriv_mul_sin_sublattice_eq_zero hblind hk1 R,
    tendsto_div_pow_integral_exp_mul_arcLineDyadicTowerProfile_nhdsWithin hk1 R hsym,
    tendsto_div_pow_integral_exp_mul_arcLineSymDyadicTowerProfile_nhdsWithin hk1 R hsym⟩

end

end RHTower
