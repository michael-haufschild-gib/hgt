import GaloisForLFunctions.RHTower.ModularArcDyadicTelescopingUniformBound

/-!
# Depth-and-scale-uniform `L^∞` profile bounds, pure doubly-exponential `O(k^{−2^r})` step decay, and the infinite-horizon dyadic modular arc limit

In `ModularArcDyadicTelescopingUniformBound`, we used the telescoping expansion of the dyadic
hyperbolic tower together with `2^r / cosh(log(k^{2^r})) ≤ 4 · (1/2)^r` to establish the
depth-and-scale-uniform square-root frequency bound
`|∫ arcLineDyadicTowerDeriv k R ν x · sin(c x) dx| ≤ 72 √(π/2) · ν.real univ · √c`
for all `k ≥ 2`, `R ∈ ℕ`, and `c > 0`.

In this module we complete the infinite-horizon (`R → ∞`) theory of the dyadic modular arc tower:

1. **Scale-independent `L^∞(ℝ)` profile bounds (`abs_arcPoissonProfile_le_two`,
   `abs_arcLineAtomicProfile_le_eight`, `abs_symScaleProfile_le_const`,
   `abs_hyperbolicFilterProfile_le_const`):**
   For every `b ∈ ℝ` and `v ∈ ℝ`, `|arcLineAtomicProfile b ν v| ≤ 8 · ν.real univ` (independent
   of `b`), and `symScaleProfile M` and `hyperbolicFilterProfile M` preserve uniform `L^∞(ℝ)`
   bounds with constants `C` and `2 C` independent of `M`.
2. **Depth-and-scale-uniform `L^∞(ℝ)` bound across all `k ≥ 2` and `R ∈ ℕ`
   (`abs_arcLineDyadicTowerProfile_le_uniform`, `abs_arcLineSymDyadicTowerProfile_le_uniform`):**
   Telescoping over `0 ≤ r < R` yields
   `|arcLineDyadicTowerProfile k R ν v| ≤ 72 · ν.real univ` and
   `|arcLineSymDyadicTowerProfile k R ν v| ≤ 72 · ν.real univ` for all `k ≥ 2`, `R ∈ ℕ`, and `v ∈ ℝ`.
3. **Pure doubly-exponential `O(k^{−2^r})` step decay (`abs_arcLineDyadicTowerProfile_succ_sub_le_inv_pow`,
   `abs_integral_arcLineDyadicTowerDeriv_succ_sub_le_inv_pow`,
   `abs_integral_arcLineDyadicTowerDeriv_succ_sub_arcFreq_le_inv_pow`):**
   Plugging the `r`-independent uniform bounds back into the dyadic step identity upgrades the
   step decay from `O((1/2)^r)` to pure doubly-exponential `O(k^{−2^r})` decay!
4. **Unconditional `R → ∞` convergence to the infinite-horizon limit profile and sine-moment
   functional (`tendsto_arcLineDyadicTowerProfile_atTop`,
   `tendsto_integral_arcLineDyadicTowerDeriv_mul_sin_atTop`,
   `abs_arcLineInfiniteDyadicProfile_le`, `abs_arcLineInfiniteDyadicSineMoment_le`,
   `exists_dyadic_infiniteHorizon_limit_arcWitness`):**
   For every `k ≥ 2`, the infinite dyadic telescoping series are absolutely summable, so as the
   pole-cancellation depth `R → ∞`, `arcLineDyadicTowerProfile k R ν v` and
   `∫ arcLineDyadicTowerDeriv k R ν x · sin(c x) dx` converge unconditionally to the even,
   uniformly bounded infinite-horizon limit profile `arcLineInfiniteDyadicProfile k ν` and
   sine-moment functional `arcLineInfiniteDyadicSineMoment k ν`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Scale-independent `L^∞(ℝ)` profile bounds -/

/-- For every `v ∈ ℝ`, `|arcPoissonProfile ν v| ≤ 2 · ν.real univ`. -/
theorem abs_arcPoissonProfile_le_two (ν : Measure ArcParam) [IsFiniteMeasure ν] (v : ℝ) :
    |arcPoissonProfile ν v| ≤ 2 * ν.real univ := by
  have h1 : Real.cosh v ^ (-(1 / 2) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_cosh v) (by norm_num)
  have h0 : 0 ≤ 2 * ν.real univ := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  calc |arcPoissonProfile ν v|
      ≤ 2 * ν.real univ * Real.cosh v ^ (-(1 / 2) : ℝ) := abs_arcPoissonProfile_le ν v
    _ ≤ 2 * ν.real univ * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = 2 * ν.real univ := mul_one _

/-- For every `b ∈ ℝ` and `v ∈ ℝ`, `|arcLineAtomicProfile b ν v| ≤ 8 · ν.real univ`
(completely independent of `b`). -/
theorem abs_arcLineAtomicProfile_le_eight (b : ℝ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (v : ℝ) :
    |arcLineAtomicProfile b ν v| ≤ 8 * ν.real univ := by
  unfold arcLineAtomicProfile
  have h0 : 0 ≤ 2 * ν.real univ := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  have hsum : |∑ j, atomWeight b j * arcPoissonProfile ν (v - atomShift b j)| ≤
      atomMass b * (2 * ν.real univ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [atomMass, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_arcPoissonProfile_le_two ν (v - atomShift b j)) (abs_nonneg _)
  calc |∑ j, atomWeight b j * arcPoissonProfile ν (v - atomShift b j)|
      ≤ atomMass b * (2 * ν.real univ) := hsum
    _ ≤ 4 * (2 * ν.real univ) := mul_le_mul_of_nonneg_right (atomMass_le_four b) h0
    _ = 8 * ν.real univ := by ring

/-- `symScaleProfile M` preserves any uniform `L^∞(ℝ)` bound `|P(v)| ≤ C` with zero loss. -/
theorem abs_symScaleProfile_le_const (M : ℕ) {P : ℝ → ℝ} {C : ℝ}
    (hP : ∀ v, |P v| ≤ C) (v : ℝ) :
    |symScaleProfile M P v| ≤ C := by
  unfold symScaleProfile forwardScaleProfile backwardScaleProfile
  rw [abs_mul, abs_of_pos (by positivity)]
  have h1 := hP (v - 2 * Real.log M)
  have h2 := hP (v + 2 * Real.log M)
  have habs := (abs_add_le _ _).trans (add_le_add h1 h2)
  linarith

/-- `hyperbolicFilterProfile M` preserves any uniform `L^∞(ℝ)` bound `|P(v)| ≤ C` with constant `2 C`. -/
theorem abs_hyperbolicFilterProfile_le_const (M : ℕ) {P : ℝ → ℝ} {C : ℝ}
    (hP : ∀ v, |P v| ≤ C) (v : ℝ) :
    |hyperbolicFilterProfile M P v| ≤ 2 * C := by
  rw [hyperbolicFilterProfile_eq_sub_symScaleProfile]
  have h0 := hP v
  have hC0 : 0 ≤ C := (abs_nonneg (P v)).trans h0
  have hS := abs_symScaleProfile_le_const M hP v
  have hcosh : 1 / Real.cosh (Real.log M) ≤ 1 := by
    rw [div_le_one (Real.cosh_pos _)]
    exact Real.one_le_cosh _
  have hmul : |(1 / Real.cosh (Real.log M)) * symScaleProfile M P v| ≤ C := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / Real.cosh (Real.log M) * |symScaleProfile M P v|
        ≤ 1 * C := mul_le_mul hcosh hS (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have hsub := abs_sub (P v) ((1 / Real.cosh (Real.log M)) * symScaleProfile M P v)
  linarith

/-- Scale-independent `L^∞(ℝ)` bound `2^r · (8 · ν.real univ)` at dyadic level `r`. -/
theorem abs_arcLineDyadicTowerProfile_le_two_pow (k r : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] :
    ∀ v : ℝ, |arcLineDyadicTowerProfile k r ν v| ≤ 2 ^ r * (8 * ν.real univ) := by
  induction r with
  | zero =>
    intro v
    simpa [arcLineDyadicTowerProfile] using abs_arcLineAtomicProfile_le_eight (Real.log k) ν v
  | succ r ih =>
    intro v
    have hstep := abs_hyperbolicFilterProfile_le_const (k ^ (2 ^ r)) ih v
    calc |arcLineDyadicTowerProfile k (r + 1) ν v|
        ≤ 2 * (2 ^ r * (8 * ν.real univ)) := hstep
      _ = 2 ^ (r + 1) * (8 * ν.real univ) := by rw [pow_succ']; ring

theorem abs_arcLineSymDyadicTowerProfile_le_two_pow (k r : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (v : ℝ) :
    |arcLineSymDyadicTowerProfile k r ν v| ≤ 2 ^ r * (8 * ν.real univ) :=
  abs_symScaleProfile_le_const (k ^ (2 ^ r))
    (abs_arcLineDyadicTowerProfile_le_two_pow k r ν) v

/-! ### Geometric `(1/2)^r` profile step bound and depth-and-scale-uniform `L^∞(ℝ)` bound -/

/-- **Geometric `(1/2)^r` pointwise Cauchy step bound for `arcLineDyadicTowerProfile` (`k ≥ 2`).** -/
theorem abs_arcLineDyadicTowerProfile_succ_sub_le {k : ℕ} (hk : 2 ≤ k) (r : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] (v : ℝ) :
    |(1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        arcLineSymDyadicTowerProfile k r ν v| ≤
      (32 * ν.real univ) * (1 / 2 : ℝ) ^ r := by
  rw [abs_mul, abs_of_pos (by positivity)]
  have hS := abs_arcLineSymDyadicTowerProfile_le_two_pow k r ν v
  have hratio := two_pow_div_cosh_log_pow_two_pow_le hk r
  have hB0 : 0 ≤ 8 * ν.real univ := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  calc 1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) *
        |arcLineSymDyadicTowerProfile k r ν v|
      ≤ 1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) * (2 ^ r * (8 * ν.real univ)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = ((2 : ℝ) ^ r / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) * (8 * ν.real univ) := by ring
    _ ≤ (4 * (1 / 2 : ℝ) ^ r) * (8 * ν.real univ) :=
        mul_le_mul_of_nonneg_right hratio hB0
    _ = (32 * ν.real univ) * (1 / 2 : ℝ) ^ r := by ring

/-- **Depth-and-scale-uniform `L^∞(ℝ)` bound for `arcLineDyadicTowerProfile k R ν`:**
For every `k ≥ 2`, every dyadic depth `R ∈ ℕ`, and every `v ∈ ℝ`,
`|arcLineDyadicTowerProfile k R ν v| ≤ 72 · ν.real univ` (independent of both `k` and `R`). -/
theorem abs_arcLineDyadicTowerProfile_le_uniform {k : ℕ} (hk : 2 ≤ k) (R : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] (v : ℝ) :
    |arcLineDyadicTowerProfile k R ν v| ≤ 72 * ν.real univ := by
  rw [arcLineDyadicTowerProfile_eq_atomic_sub_sum k R ν v]
  have h0 := abs_arcLineAtomicProfile_le_eight (Real.log k) ν v
  set B := 8 * ν.real univ
  have hB0 : 0 ≤ B := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  have hsum : |∑ r ∈ Finset.range R,
      (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        arcLineSymDyadicTowerProfile k r ν v| ≤
      (4 * B) * ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    refine (abs_arcLineDyadicTowerProfile_succ_sub_le hk r ν v).trans_eq ?_
    dsimp [B]; ring
  have hgeom : (4 * B) * ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r ≤ 8 * B := by
    have h2 := sum_range_half_pow_le_two R
    nlinarith
  have hsub := abs_sub (arcLineAtomicProfile (Real.log k) ν v)
    (∑ r ∈ Finset.range R,
      (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        arcLineSymDyadicTowerProfile k r ν v)
  calc |arcLineAtomicProfile (Real.log k) ν v -
        ∑ r ∈ Finset.range R,
          (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
            arcLineSymDyadicTowerProfile k r ν v|
      ≤ B + 8 * B := by linarith
    _ = 72 * ν.real univ := by dsimp [B]; ring

/-- **Depth-and-scale-uniform `L^∞(ℝ)` bound for `arcLineSymDyadicTowerProfile k R ν`.** -/
theorem abs_arcLineSymDyadicTowerProfile_le_uniform {k : ℕ} (hk : 2 ≤ k) (R : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] (v : ℝ) :
    |arcLineSymDyadicTowerProfile k R ν v| ≤ 72 * ν.real univ :=
  abs_symScaleProfile_le_const (k ^ (2 ^ R))
    (abs_arcLineDyadicTowerProfile_le_uniform hk R ν) v

/-! ### Pure doubly-exponential `O(k^{−2^r})` step bounds -/

/-- **Pure doubly-exponential `O(k^{−2^r})` pointwise profile step bound (`k ≥ 2`).** -/
theorem abs_arcLineDyadicTowerProfile_succ_sub_le_inv_pow {k : ℕ} (hk : 2 ≤ k) (r : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] (v : ℝ) :
    |arcLineDyadicTowerProfile k (r + 1) ν v - arcLineDyadicTowerProfile k r ν v| ≤
      144 * ν.real univ * (((k ^ (2 ^ r) : ℕ) : ℝ)⁻¹) := by
  have heq : arcLineDyadicTowerProfile k (r + 1) ν v - arcLineDyadicTowerProfile k r ν v =
      -(1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        arcLineSymDyadicTowerProfile k r ν v := by
    rw [arcLineDyadicTowerProfile_succ_eq_sub_sym]; ring
  rw [heq, abs_mul, abs_neg, abs_of_pos (by positivity)]
  have hm : 1 ≤ k ^ (2 ^ r) := one_le_pow_two_pow (by omega) r
  have hcosh := inv_cosh_log_le hm
  have hS := abs_arcLineSymDyadicTowerProfile_le_uniform hk r ν v
  have h0 : 0 ≤ 72 * ν.real univ := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  calc 1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) *
        |arcLineSymDyadicTowerProfile k r ν v|
      ≤ (2 * (((k ^ (2 ^ r) : ℕ) : ℝ)⁻¹)) * (72 * ν.real univ) :=
        mul_le_mul hcosh hS (abs_nonneg _) (by positivity)
    _ = 144 * ν.real univ * (((k ^ (2 ^ r) : ℕ) : ℝ)⁻¹) := by ring

/-- **Pure doubly-exponential `O(k^{−2^r})` sine-moment step bound at any frequency `c > 0`.** -/
theorem abs_integral_arcLineDyadicTowerDeriv_succ_sub_le_inv_pow
    {k : ℕ} (hk : 2 ≤ k) (r : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {c : ℝ} (hc : 0 < c) :
    |(∫ x, arcLineDyadicTowerDeriv k (r + 1) ν x * Real.sin (c * x)) -
        (∫ x, arcLineDyadicTowerDeriv k r ν x * Real.sin (c * x))| ≤
      144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c *
        (((k ^ (2 ^ r) : ℕ) : ℝ)⁻¹) := by
  have hk1 : 1 ≤ k := by omega
  rw [integral_arcLineDyadicTowerDeriv_succ_mul_sin_sub hk1 r ν c,
    abs_mul, abs_neg, abs_of_pos (by positivity)]
  have hm : 1 ≤ k ^ (2 ^ r) := one_le_pow_two_pow hk1 r
  have hcosh := inv_cosh_log_le hm
  have hS := abs_integral_arcLineSymDyadicTowerDeriv_mul_sin_le_uniform hk r ν hc
  calc 1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) *
        |∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x)|
      ≤ (2 * (((k ^ (2 ^ r) : ℕ) : ℝ)⁻¹)) *
          (72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c) :=
        mul_le_mul hcosh hS (abs_nonneg _) (by positivity)
    _ = 144 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c *
          (((k ^ (2 ^ r) : ℕ) : ℝ)⁻¹) := by ring

/-- **Halved doubly-exponential `O(k^{−2^r})` sine-moment step bound at all integer frequencies `arcFreq n`.** -/
theorem abs_integral_arcLineDyadicTowerDeriv_succ_sub_arcFreq_le_inv_pow
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 2 ≤ k) (r n : ℕ) :
    |(∫ x, arcLineDyadicTowerDeriv k (r + 1) ν x * Real.sin (arcFreq n * x)) -
        (∫ x, arcLineDyadicTowerDeriv k r ν x * Real.sin (arcFreq n * x))| ≤
      72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n) *
        (((k ^ (2 ^ r) : ℕ) : ℝ)⁻¹) := by
  have hk1 : 1 ≤ k := by omega
  rw [integral_arcLineDyadicTowerDeriv_succ_mul_sin_sub hk1 r ν (arcFreq n),
    abs_mul, abs_neg, abs_of_pos (by positivity)]
  have hm : 1 ≤ k ^ (2 ^ r) := one_le_pow_two_pow hk1 r
  have hcosh := inv_cosh_log_le hm
  have hS := abs_integral_arcLineSymDyadicTowerDeriv_mul_sin_arcFreq_le_uniform hblind hk r n
  calc 1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))) *
        |∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (arcFreq n * x)|
      ≤ (2 * (((k ^ (2 ^ r) : ℕ) : ℝ)⁻¹)) *
          (36 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n)) :=
        mul_le_mul hcosh hS (abs_nonneg _) (by positivity)
    _ = 72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n) *
          (((k ^ (2 ^ r) : ℕ) : ℝ)⁻¹) := by ring

/-! ### Unconditional `R → ∞` convergence to the infinite-horizon limit profile and sine-moment functional -/

/-- The infinite-horizon dyadic log-scale profile at integer scale `k`:
`P_{k,∞}(v) = arcLineAtomicProfile (log k) ν v − ∑'_{r=0}^∞ (1 / cosh(log(k^{2^r}))) · arcLineSymDyadicTowerProfile k r ν v`. -/
def arcLineInfiniteDyadicProfile (k : ℕ) (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  arcLineAtomicProfile (Real.log k) ν v -
    ∑' r : ℕ, (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
      arcLineSymDyadicTowerProfile k r ν v

/-- The infinite-horizon dyadic sine-moment functional at integer scale `k`:
`M_{k,∞}(c) = ∫ arcLineAtomicDeriv (log k) ν x · sin(c x) dx − ∑'_{r=0}^∞ (1 / cosh(log(k^{2^r}))) · ∫ arcLineSymDyadicTowerDeriv k r ν x · sin(c x) dx`. -/
def arcLineInfiniteDyadicSineMoment (k : ℕ) (ν : Measure ArcParam) (c : ℝ) : ℝ :=
  (∫ x, arcLineAtomicDeriv (Real.log k) ν x * Real.sin (c * x)) -
    ∑' r : ℕ, (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
      ∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x)

/-- Absolute summability of the dyadic profile telescoping series for `k ≥ 2`. -/
theorem summable_inv_cosh_mul_arcLineSymDyadicTowerProfile
    {k : ℕ} (hk : 2 ≤ k) (ν : Measure ArcParam) [IsFiniteMeasure ν] (v : ℝ) :
    Summable fun r : ℕ =>
      (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        arcLineSymDyadicTowerProfile k r ν v := by
  refine Summable.of_norm_bounded (summable_geometric_two.mul_left (32 * ν.real univ)) fun r => ?_
  rw [Real.norm_eq_abs]
  exact abs_arcLineDyadicTowerProfile_succ_sub_le hk r ν v

/-- **Unconditional `R → ∞` convergence of `arcLineDyadicTowerProfile k R ν v` to `arcLineInfiniteDyadicProfile k ν v`.** -/
theorem tendsto_arcLineDyadicTowerProfile_atTop
    {k : ℕ} (hk : 2 ≤ k) (ν : Measure ArcParam) [IsFiniteMeasure ν] (v : ℝ) :
    Tendsto (fun R : ℕ => arcLineDyadicTowerProfile k R ν v)
      atTop (𝓝 (arcLineInfiniteDyadicProfile k ν v)) := by
  simp_rw [arcLineDyadicTowerProfile_eq_atomic_sub_sum]
  exact tendsto_const_nhds.sub
    (summable_inv_cosh_mul_arcLineSymDyadicTowerProfile hk ν v).hasSum.tendsto_sum_nat

/-- Even symmetry (`v ↦ −v`) of the infinite-horizon dyadic profile `arcLineInfiniteDyadicProfile k ν`. -/
theorem arcLineInfiniteDyadicProfile_neg (k : ℕ) (ν : Measure ArcParam) (v : ℝ) :
    arcLineInfiniteDyadicProfile k ν (-v) = arcLineInfiniteDyadicProfile k ν v := by
  have hsym : ∀ r : ℕ, arcLineSymDyadicTowerProfile k r ν (-v) =
      arcLineSymDyadicTowerProfile k r ν v := fun r => by
    unfold arcLineSymDyadicTowerProfile symScaleProfile
      forwardScaleProfile backwardScaleProfile
    have h1 : arcLineDyadicTowerProfile k r ν (-v - 2 * Real.log ((k ^ (2 ^ r) : ℕ))) =
        arcLineDyadicTowerProfile k r ν (v + 2 * Real.log ((k ^ (2 ^ r) : ℕ))) := by
      rw [← arcLineDyadicTowerProfile_neg k r ν (v + 2 * Real.log ((k ^ (2 ^ r) : ℕ)))]
      congr 1; ring
    have h2 : arcLineDyadicTowerProfile k r ν (-v + 2 * Real.log ((k ^ (2 ^ r) : ℕ))) =
        arcLineDyadicTowerProfile k r ν (v - 2 * Real.log ((k ^ (2 ^ r) : ℕ))) := by
      rw [← arcLineDyadicTowerProfile_neg k r ν (v - 2 * Real.log ((k ^ (2 ^ r) : ℕ)))]
      congr 1; ring
    rw [h1, h2]
    ring
  unfold arcLineInfiniteDyadicProfile
  rw [arcLineAtomicProfile_neg]
  congr 1
  exact tsum_congr fun r => by rw [hsym r]

/-- **Uniform `L^∞(ℝ)` bound for the infinite-horizon limit profile (`k ≥ 2`).** -/
theorem abs_arcLineInfiniteDyadicProfile_le {k : ℕ} (hk : 2 ≤ k) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (v : ℝ) :
    |arcLineInfiniteDyadicProfile k ν v| ≤ 72 * ν.real univ :=
  le_of_tendsto (continuous_abs.tendsto _ |>.comp (tendsto_arcLineDyadicTowerProfile_atTop hk ν v))
    (Eventually.of_forall fun R => abs_arcLineDyadicTowerProfile_le_uniform hk R ν v)

/-- Absolute summability of the dyadic sine-moment telescoping series for `k ≥ 2` and `c > 0`. -/
theorem summable_inv_cosh_mul_integral_arcLineSymDyadicTowerDeriv_mul_sin
    {k : ℕ} (hk : 2 ≤ k) (ν : Measure ArcParam) [IsFiniteMeasure ν] {c : ℝ} (hc : 0 < c) :
    Summable fun r : ℕ =>
      (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
        ∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (c * x) := by
  have hk1 : 1 ≤ k := by omega
  refine Summable.of_norm_bounded
    (summable_geometric_two.mul_left (32 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c))
    fun r => ?_
  rw [Real.norm_eq_abs]
  have hr := abs_integral_arcLineDyadicTowerDeriv_succ_sub_le hk r ν hc
  rwa [integral_arcLineDyadicTowerDeriv_succ_mul_sin_sub hk1 r ν c, abs_mul, abs_neg,
    ← abs_mul] at hr

/-- **Unconditional `R → ∞` convergence of the dyadic sine moments to `arcLineInfiniteDyadicSineMoment k ν c`.** -/
theorem tendsto_integral_arcLineDyadicTowerDeriv_mul_sin_atTop
    {k : ℕ} (hk : 2 ≤ k) (ν : Measure ArcParam) [IsFiniteMeasure ν] {c : ℝ} (hc : 0 < c) :
    Tendsto (fun R : ℕ => ∫ x, arcLineDyadicTowerDeriv k R ν x * Real.sin (c * x))
      atTop (𝓝 (arcLineInfiniteDyadicSineMoment k ν c)) := by
  have hk1 : 1 ≤ k := by omega
  simp_rw [integral_arcLineDyadicTowerDeriv_mul_sin_eq_atomic_sub_sum hk1 _ ν c]
  exact tendsto_const_nhds.sub
    (summable_inv_cosh_mul_integral_arcLineSymDyadicTowerDeriv_mul_sin hk ν hc).hasSum.tendsto_sum_nat

/-- **Scale-independent `O(√c)` bound for the infinite-horizon sine-moment functional (`k ≥ 2`).** -/
theorem abs_arcLineInfiniteDyadicSineMoment_le
    {k : ℕ} (hk : 2 ≤ k) (ν : Measure ArcParam) [IsFiniteMeasure ν] {c : ℝ} (hc : 0 < c) :
    |arcLineInfiniteDyadicSineMoment k ν c| ≤
      72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c :=
  le_of_tendsto
    (continuous_abs.tendsto _ |>.comp (tendsto_integral_arcLineDyadicTowerDeriv_mul_sin_atTop hk ν hc))
    (Eventually.of_forall fun R => abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_uniform hk R ν hc)

/-! ### Master unconditional infinite-horizon dyadic modular arc limit theorem -/

/-- **Master unconditional theorem for the infinite-horizon dyadic modular arc limit.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2`:
1. Across all dyadic pole-cancellation depths `R ∈ ℕ` and all `v ∈ ℝ`,
   `|arcLineDyadicTowerProfile k R ν v| ≤ 72 · ν.real univ` and the step differences decay
   doubly-exponentially:
   `|arcLineDyadicTowerProfile k (R + 1) ν v − arcLineDyadicTowerProfile k R ν v| ≤ 144 · ν.real univ · (k^{2^R})⁻¹`;
2. As `R → ∞`, `arcLineDyadicTowerProfile k R ν v` converges unconditionally to the even,
   uniformly bounded infinite-horizon profile `arcLineInfiniteDyadicProfile k ν v`
   (`|arcLineInfiniteDyadicProfile k ν v| ≤ 72 · ν.real univ`);
3. For every `c > 0`, as `R → ∞`, the sine moments `∫ arcLineDyadicTowerDeriv k R ν x · sin(c x) dx`
   converge unconditionally with doubly-exponential step decay `O((k^{2^R})⁻¹)` to
   `arcLineInfiniteDyadicSineMoment k ν c`, which satisfies the `k`-independent bound
   `|arcLineInfiniteDyadicSineMoment k ν c| ≤ 72 √(π/2) · ν.real univ · √c`. -/
theorem exists_dyadic_infiniteHorizon_limit_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      ∀ k : ℕ, 2 ≤ k →
        (∀ R : ℕ, ∀ v : ℝ, |arcLineDyadicTowerProfile k R ν v| ≤ 72 * ν.real univ) ∧
        (∀ r : ℕ, ∀ v : ℝ,
          |arcLineDyadicTowerProfile k (r + 1) ν v - arcLineDyadicTowerProfile k r ν v| ≤
            144 * ν.real univ * (((k ^ (2 ^ r) : ℕ) : ℝ)⁻¹)) ∧
        (∀ v : ℝ, Tendsto (fun R : ℕ => arcLineDyadicTowerProfile k R ν v)
          atTop (𝓝 (arcLineInfiniteDyadicProfile k ν v))) ∧
        (∀ v : ℝ, arcLineInfiniteDyadicProfile k ν (-v) = arcLineInfiniteDyadicProfile k ν v) ∧
        (∀ v : ℝ, |arcLineInfiniteDyadicProfile k ν v| ≤ 72 * ν.real univ) ∧
        (∀ r n : ℕ,
          |(∫ x, arcLineDyadicTowerDeriv k (r + 1) ν x * Real.sin (arcFreq n * x)) -
              (∫ x, arcLineDyadicTowerDeriv k r ν x * Real.sin (arcFreq n * x))| ≤
            72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq n) *
              (((k ^ (2 ^ r) : ℕ) : ℝ)⁻¹)) ∧
        (∀ c : ℝ, 0 < c →
          Tendsto (fun R : ℕ => ∫ x, arcLineDyadicTowerDeriv k R ν x * Real.sin (c * x))
            atTop (𝓝 (arcLineInfiniteDyadicSineMoment k ν c))) ∧
        (∀ c : ℝ, 0 < c →
          |arcLineInfiniteDyadicSineMoment k ν c| ≤
            72 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt c) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, _⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym, fun k hk => ?_⟩
  exact ⟨fun R v => abs_arcLineDyadicTowerProfile_le_uniform hk R ν v,
    fun r v => abs_arcLineDyadicTowerProfile_succ_sub_le_inv_pow hk r ν v,
    fun v => tendsto_arcLineDyadicTowerProfile_atTop hk ν v,
    fun v => arcLineInfiniteDyadicProfile_neg k ν v,
    fun v => abs_arcLineInfiniteDyadicProfile_le hk ν v,
    fun r n => abs_integral_arcLineDyadicTowerDeriv_succ_sub_arcFreq_le_inv_pow hblind hk r n,
    fun c hc => tendsto_integral_arcLineDyadicTowerDeriv_mul_sin_atTop hk ν hc,
    fun c hc => abs_arcLineInfiniteDyadicSineMoment_le hk ν hc⟩

end

end RHTower
