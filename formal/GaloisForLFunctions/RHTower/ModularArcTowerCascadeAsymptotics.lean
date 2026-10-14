import GaloisForLFunctions.RHTower.ModularArcArbitraryOrderAllIntegerBlindTower

/-!
# Exact sublattice cascade reduction and critical-line spectral convergence for the arbitrary-order modular arc tower

In `ModularArcArbitraryOrderStripEdgeTower`, we constructed the iterated hyperbolic pole-filtered
modular arc tower `arcLineTowerVector k d ν` (`d ∈ ℕ`), proving that at level `d` its derivative
`arcLineTowerDeriv k d ν` is identically blind along the `k^{2(d+1)}`-sublattice
`arcFreq (k^{2(d+1)}(j+1) − 1)` while its strip Laplace/Mellin transform vanishes to order
`O((1/2 − l)^{d+1})` as `l → (1/2)⁻`.

In this module we establish the **exact `d`-step sublattice cascade law**, quantitative sub-harmonic
contraction bounds, and **`k → ∞` critical-line spectral convergence** across all levels `d ∈ ℕ`
of the tower:

1. **Universal one-step sublattice cascade (`integral_hyperbolicFilterDeriv_mul_sin_cascade`):**
   If `f'` is blind on the `(m² M)`-sublattice `arcFreq (m² M (j+1) − 1)`, then along that same
   `(m² M)`-sublattice both the central term and the forward-dilated term of
   `hyperbolicFilterDeriv m f'` vanish identically, reducing the sine moment of
   `hyperbolicFilterDeriv m f'` at `arcFreq (m² M (j+1) − 1)` to `−(m / (2 cosh(log m)))` times the
   sine moment of `f'` at the `m²`-contracted frequency `arcFreq (M (j+1) − 1)`.
2. **Exact `d`-step tower cascade (`integral_arcLineTowerDeriv_mul_sin_cascade`):**
   Iterating the one-step cascade `d` times from level `d` down to level `0` shows that along the
   `k^{2d}`-sublattice `arcFreq (k^{2d}(j+1) − 1)`,
   `∫ x, arcLineTowerDeriv k d ν x * sin(arcFreq (k^{2d}(j+1) − 1) x)`
   `= (−k / (2 cosh(log k)))^d * ∫ t, arcLineAtomicDeriv (log k) ν t * sin(arcFreq j · t)`.
3. **Uniform contraction and `k → ∞` asymptotic vanishing (`tendsto_integral_arcLineTowerDeriv_mul_sin_cascade_atTop`):**
   Because `k / (2 cosh(log k)) ≤ 1` for all `k ≥ 1`, the `k^{2d}`-sublattice moment at depth `d`
   is bounded by the base (`d = 0`) moment at the unscaled frequency `arcFreq j`, which is
   `O(k^{−1/2})` and converges to `0` as `k → ∞` (`abs_integral_arcLineTowerDeriv_mul_sin_cascade_le`).
   On the `k^{2d+1}`-sublattice `arcFreq (k^{2d+1}(m+1) − 1)`, the `−log k` sub-harmonic also
   cancels, giving the `1 / (4 cosh²(½ log k))` bound
   (`abs_integral_arcLineTowerDeriv_mul_sin_odd_sublattice_le`).
4. **Closed-form critical-line factorization and `k → ∞` convergence (`integral_cos_mul_arcLineTowerProfile`, `tendsto_integral_cos_mul_arcLineTowerProfile_atTop`):**
   At every level `d ∈ ℕ`, the cosine transform of `arcLineTowerProfile k d ν` factors as
   `(1 − cos(2τ log k) / cosh(log k))^d · (1 − cos(τ log k) / cosh(½ log k))² · ∫ cos(τv) arcPoissonProfile ν v`,
   and converges as `k → ∞` to the strictly positive Poisson transform `∫ cos(τv) arcPoissonProfile ν v`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Universal one-step sublattice cascade for `hyperbolicFilterDeriv` -/

/-- **Universal one-step sublattice cascade law:**
If `f'` is integrable and blind on the `(m² M)`-sublattice `arcFreq (m² M (j+1) − 1)`, then along
that same sublattice both the central term `f'(x)` and the forward-dilated term
`m⁻³ f'(x / m²)` vanish identically, isolating the backward-dilated term at the `m²`-contracted
frequency `arcFreq (M (j+1) − 1)` with hyperbolic contraction weight `−m / (2 cosh(log m))`. -/
theorem integral_hyperbolicFilterDeriv_mul_sin_cascade
    {m M : ℕ} (hm : 1 ≤ m) (hM : 1 ≤ M) {f' : ℝ → ℝ} (hf' : Integrable f')
    (hblind : ∀ j : ℕ, ∫ x, f' x * Real.sin (arcFreq (m ^ 2 * M * (j + 1) - 1) * x) = 0)
    (j : ℕ) :
    ∫ x, hyperbolicFilterDeriv m f' x *
        Real.sin (arcFreq (m ^ 2 * M * (j + 1) - 1) * x) =
      -((m : ℝ) / (2 * Real.cosh (Real.log m))) *
        ∫ t, f' t * Real.sin (arcFreq (M * (j + 1) - 1) * t) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  have hmne : (m : ℝ) ≠ 0 := hmpos.ne'
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow 2 m hm
  have hm2M : 1 ≤ m ^ 2 * M := Nat.mul_pos hm2 hM
  set c := arcFreq (m ^ 2 * M * (j + 1) - 1)
  have h0_int : Integrable fun x => f' x * Real.sin (c * x) :=
    hf'.mul_bdd (by fun_prop) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have h1_int : Integrable fun x =>
      ((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x) :=
    ((hf'.comp_mul_right' (inv_ne_zero (pow_ne_zero 2 hmne))).const_mul (((m : ℝ) ^ 3)⁻¹)).mul_bdd
      (by fun_prop) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have h2_int : Integrable fun x =>
      (m : ℝ) ^ 3 * f' ((m : ℝ) ^ 2 * x) * Real.sin (c * x) :=
    ((hf'.comp_mul_left' (pow_ne_zero 2 hmne)).const_mul ((m : ℝ) ^ 3)).mul_bdd
      (by fun_prop) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have h01_int : Integrable fun x =>
      f' x * Real.sin (c * x) -
        (1 / (2 * Real.cosh (Real.log m))) *
          (((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x)) :=
    h0_int.sub (h1_int.const_mul _)
  -- Central term vanishes by `hblind j`
  have h0_eq : ∫ x, f' x * Real.sin (c * x) = 0 := hblind j
  -- Forward term lands on `arcFreq (m² M (m²(j+1)) − 1)` and vanishes by `hblind`
  have h1_eq : ∫ x, ((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x) = 0 := by
    have hfreq : c * ((m : ℝ) ^ 2) =
        arcFreq (m ^ 2 * M * ((m ^ 2 * (j + 1) - 1) + 1) - 1) := by
      have h1 : 1 ≤ m ^ 2 * (j + 1) := Nat.mul_pos hm2 (Nat.succ_pos j)
      have heq : (m ^ 2 * M * (j + 1) - 1 + 1) * m ^ 2 - 1 =
          m ^ 2 * M * ((m ^ 2 * (j + 1) - 1) + 1) - 1 := by
        have h2 : 1 ≤ m ^ 2 * M * (j + 1) := Nat.mul_pos hm2M (Nat.succ_pos j)
        rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
        ring_nf
      change arcFreq (m ^ 2 * M * (j + 1) - 1) * ((m : ℝ) ^ 2) = _
      rw [← heq, ← arcFreq_mul_nat hm2 (m ^ 2 * M * (j + 1) - 1)]
      push_cast; ring
    have e : (fun x => ((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x)) =
        fun x => ((m : ℝ) ^ 3)⁻¹ * (f' (x * ((m : ℝ) ^ 2)⁻¹) *
          Real.sin (arcFreq (m ^ 2 * M * ((m ^ 2 * (j + 1) - 1) + 1) - 1) *
            (x * ((m : ℝ) ^ 2)⁻¹))) := by
      funext x
      rw [← hfreq]
      have hx : c * (m : ℝ) ^ 2 * (x * ((m : ℝ) ^ 2)⁻¹) = c * x := by field_simp
      rw [hx]; ring
    rw [e, integral_const_mul, Measure.integral_comp_mul_right
      (fun t => f' t * Real.sin
        (arcFreq (m ^ 2 * M * ((m ^ 2 * (j + 1) - 1) + 1) - 1) * t)) (((m : ℝ) ^ 2)⁻¹),
      hblind (m ^ 2 * (j + 1) - 1), smul_zero, mul_zero]
  -- Backward term rescales to `(m : ℝ) * ∫ t, f' t * sin(arcFreq (M(j+1) − 1) * t)`
  have h2_eq : ∫ x, (m : ℝ) ^ 3 * f' ((m : ℝ) ^ 2 * x) * Real.sin (c * x) =
      (m : ℝ) * ∫ t, f' t * Real.sin (arcFreq (M * (j + 1) - 1) * t) := by
    have hfreq : c / ((m : ℝ) ^ 2) = arcFreq (M * (j + 1) - 1) := by
      have h1 : 1 ≤ M * (j + 1) := Nat.mul_pos hM (Nat.succ_pos j)
      have heq : (m ^ 2 * M) * (j + 1) - 1 = (M * (j + 1) - 1 + 1) * m ^ 2 - 1 := by
        rw [Nat.sub_add_cancel h1]; ring_nf
      change arcFreq ((m ^ 2 * M) * (j + 1) - 1) / (m : ℝ) ^ 2 = _
      rw [heq, ← arcFreq_mul_nat hm2 (M * (j + 1) - 1)]
      push_cast; field_simp
    have e : (fun x => (m : ℝ) ^ 3 * f' ((m : ℝ) ^ 2 * x) * Real.sin (c * x)) =
        fun x => (m : ℝ) ^ 3 * (f' ((m : ℝ) ^ 2 * x) *
          Real.sin (arcFreq (M * (j + 1) - 1) * ((m : ℝ) ^ 2 * x))) := by
      funext x
      rw [← hfreq]
      have hx : c / (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 * x) = c * x := by field_simp
      rw [hx]; ring
    rw [e, integral_const_mul, Measure.integral_comp_mul_left
      (fun t => f' t * Real.sin (arcFreq (M * (j + 1) - 1) * t)) ((m : ℝ) ^ 2),
      smul_eq_mul, abs_of_pos (inv_pos.mpr (pow_pos hmpos 2))]
    field_simp
  have e : (fun x => hyperbolicFilterDeriv m f' x * Real.sin (c * x)) = fun x =>
      f' x * Real.sin (c * x) -
        (1 / (2 * Real.cosh (Real.log m))) *
          (((m : ℝ) ^ 3)⁻¹ * f' (x * ((m : ℝ) ^ 2)⁻¹) * Real.sin (c * x)) -
        (1 / (2 * Real.cosh (Real.log m))) *
          ((m : ℝ) ^ 3 * f' ((m : ℝ) ^ 2 * x) * Real.sin (c * x)) := by
    funext x; unfold hyperbolicFilterDeriv; ring
  rw [e, integral_sub h01_int (h2_int.const_mul _),
    integral_sub h0_int (h1_int.const_mul _),
    integral_const_mul, integral_const_mul, h0_eq, h1_eq, h2_eq]
  ring

/-! ### Exact `d`-step tower cascade on the `k^{2d}`-sublattice -/

/-- **Exact `d`-step sublattice cascade for `arcLineTowerDeriv k d ν`.**
Along the `k^{2d}`-sublattice `arcFreq (k^{2d}(j+1) − 1)`, iterating the one-step cascade `d`
times reduces the sine moment of `arcLineTowerDeriv k d ν` to `(−k / (2 cosh(log k)))^d` times the
base (`d = 0`) sine moment of `arcLineAtomicDeriv (log k) ν` at the unscaled frequency `arcFreq j`. -/
theorem integral_arcLineTowerDeriv_mul_sin_cascade
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (d j : ℕ) :
    ∫ x, arcLineTowerDeriv k d ν x *
        Real.sin (arcFreq (k ^ (2 * d) * (j + 1) - 1) * x) =
      (-((k : ℝ) / (2 * Real.cosh (Real.log k)))) ^ d *
        ∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (arcFreq j * t) := by
  induction d with
  | zero =>
    simp [arcLineTowerDeriv]
  | succ d ih =>
    have hpow : k ^ (2 * (d + 1)) = k ^ 2 * k ^ (2 * d) := by
      rw [show 2 * (d + 1) = 2 + 2 * d by ring, pow_add]
    have hstep : ∫ x, arcLineTowerDeriv k (d + 1) ν x *
        Real.sin (arcFreq (k ^ (2 * (d + 1)) * (j + 1) - 1) * x) =
      -((k : ℝ) / (2 * Real.cosh (Real.log k))) *
        ∫ t, arcLineTowerDeriv k d ν t *
          Real.sin (arcFreq (k ^ (2 * d) * (j + 1) - 1) * t) := by
      rw [hpow]
      exact integral_hyperbolicFilterDeriv_mul_sin_cascade hk
        (Nat.one_le_pow (2 * d) k hk) (integrable_arcLineTowerDeriv hk d ν)
        (fun m => by
          rw [← hpow]
          exact integral_arcLineTowerDeriv_mul_sin_sublattice_eq_zero hblind hk d m) j
    rw [hstep, ih, pow_succ]
    ring

/-- **Uniform hyperbolic contraction bound on the `k^{2d}`-sublattice.**
For every `k ≥ 1`, `d ∈ ℕ`, and `j ∈ ℕ`, the `k^{2d}`-sublattice moment of `arcLineTowerDeriv k d ν`
is bounded by `(k / (2 cosh(log k)))^d ≤ 1` times the base moment at `arcFreq j`, and hence by
`2 √(π/2) · ν.real univ · √(arcFreq j) · (1 / cosh(½ log k) + 1 / (4 cosh²(½ log k)))`. -/
theorem abs_integral_arcLineTowerDeriv_mul_sin_cascade_le
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (d j : ℕ) :
    |∫ x, arcLineTowerDeriv k d ν x *
        Real.sin (arcFreq (k ^ (2 * d) * (j + 1) - 1) * x)| ≤
      2 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq j) *
        (1 / Real.cosh (Real.log k / 2) + 1 / (4 * Real.cosh (Real.log k / 2) ^ 2)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hratio_le : |(-((k : ℝ) / (2 * Real.cosh (Real.log k)))) ^ d| ≤ 1 := by
    rw [abs_pow, abs_neg, abs_of_pos (by positivity)]
    exact pow_le_one₀ (by positivity) (div_two_mul_cosh_log_le_one hk)
  rw [integral_arcLineTowerDeriv_mul_sin_cascade hblind hk d j, abs_mul]
  calc |(-((k : ℝ) / (2 * Real.cosh (Real.log k)))) ^ d| *
        |∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (arcFreq j * t)|
      ≤ 1 * |∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (arcFreq j * t)| :=
        mul_le_mul_of_nonneg_right hratio_le (abs_nonneg _)
    _ = |∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (arcFreq j * t)| := one_mul _
    _ ≤ 2 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq j) *
          (1 / Real.cosh (Real.log k / 2) + 1 / (4 * Real.cosh (Real.log k / 2) ^ 2)) :=
        abs_integral_arcLineAtomicDeriv_log_mul_sin_le hblind hk j

/-- **Enhanced quadratic-cosh bound on the `k^{2d+1}`-sublattice.**
Along `arcFreq (k^{2d+1}(m+1) − 1)`, the `−log k` sub-harmonic of the base atom also vanishes,
leaving the `1 / (4 cosh²(½ log k))` bound. -/
theorem abs_integral_arcLineTowerDeriv_mul_sin_odd_sublattice_le
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (d m : ℕ) :
    |∫ x, arcLineTowerDeriv k d ν x *
        Real.sin (arcFreq (k ^ (2 * d + 1) * (m + 1) - 1) * x)| ≤
      2 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq (k * (m + 1) - 1)) *
        (1 / (4 * Real.cosh (Real.log k / 2) ^ 2)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hratio_le : |(-((k : ℝ) / (2 * Real.cosh (Real.log k)))) ^ d| ≤ 1 := by
    rw [abs_pow, abs_neg, abs_of_pos (by positivity)]
    exact pow_le_one₀ (by positivity) (div_two_mul_cosh_log_le_one hk)
  have h1 : 1 ≤ k * (m + 1) := Nat.mul_pos hk (Nat.succ_pos m)
  have hidx : k ^ (2 * d + 1) * (m + 1) - 1 =
      k ^ (2 * d) * (k * (m + 1) - 1 + 1) - 1 := by
    rw [Nat.sub_add_cancel h1, pow_succ]
    ring_nf
  rw [hidx, integral_arcLineTowerDeriv_mul_sin_cascade hblind hk d (k * (m + 1) - 1), abs_mul]
  calc |(-((k : ℝ) / (2 * Real.cosh (Real.log k)))) ^ d| *
        |∫ t, arcLineAtomicDeriv (Real.log k) ν t *
          Real.sin (arcFreq (k * (m + 1) - 1) * t)|
      ≤ 1 * |∫ t, arcLineAtomicDeriv (Real.log k) ν t *
          Real.sin (arcFreq (k * (m + 1) - 1) * t)| :=
        mul_le_mul_of_nonneg_right hratio_le (abs_nonneg _)
    _ = |∫ t, arcLineAtomicDeriv (Real.log k) ν t *
          Real.sin (arcFreq (k * (m + 1) - 1) * t)| := one_mul _
    _ ≤ 2 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq (k * (m + 1) - 1)) *
          (1 / (4 * Real.cosh (Real.log k / 2) ^ 2)) :=
        abs_integral_arcLineAtomicDeriv_log_mul_sin_mul_le hblind hk m

/-- **Asymptotic vanishing as `k → ∞` of the `k^{2d}`-sublattice cascade moments at every depth `d`.** -/
theorem tendsto_integral_arcLineTowerDeriv_mul_sin_cascade_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    (d j : ℕ) :
    Tendsto (fun k : ℕ =>
      ∫ x, arcLineTowerDeriv k d ν x *
        Real.sin (arcFreq (k ^ (2 * d) * (j + 1) - 1) * x))
      atTop (𝓝 0) := by
  set B := 2 * Real.sqrt (Real.pi / 2) * ν.real univ * Real.sqrt (arcFreq j)
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
  exact abs_integral_arcLineTowerDeriv_mul_sin_cascade_le hblind hk d j

/-! ### Closed-form critical-line spectral factorization and `k → ∞` convergence at depth `d` -/

/-- **Closed-form critical-line cosine transform factorization at arbitrary tower depth `d ∈ ℕ`.** -/
theorem integral_cos_mul_arcLineTowerProfile (k d : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * arcLineTowerProfile k d ν v =
      (1 - Real.cos (τ * (2 * Real.log k)) / Real.cosh (Real.log k)) ^ d *
        (1 - Real.cos (Real.log k * τ) / Real.cosh (Real.log k / 2)) ^ 2 *
        ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v := by
  induction d with
  | zero =>
    rw [pow_zero, one_mul]
    exact integral_cos_mul_arcLineAtomicProfile (Real.log k) ν τ
  | succ d ih =>
    change ∫ v, Real.cos (τ * v) * hyperbolicFilterProfile k (arcLineTowerProfile k d ν) v = _
    rw [integral_cos_mul_hyperbolicFilterProfile k (integrable_arcLineTowerProfile k d ν)
      (arcLineTowerProfile_neg k d ν) τ, ih, pow_succ]
    ring

theorem inv_cosh_log_le {k : ℕ} (hk : 1 ≤ k) :
    1 / Real.cosh (Real.log k) ≤ 2 * (k : ℝ)⁻¹ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hC := Real.cosh_pos (Real.log k)
  rw [div_le_iff₀ hC]
  have h1 := nat_le_two_mul_cosh_log hk
  have h2 : (k : ℝ)⁻¹ * (k : ℝ) ≤ (k : ℝ)⁻¹ * (2 * Real.cosh (Real.log k)) :=
    mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hkpos.le)
  rw [inv_mul_cancel₀ hkpos.ne'] at h2
  linarith

theorem tendsto_inv_cosh_log_atTop :
    Tendsto (fun k : ℕ => 1 / Real.cosh (Real.log k)) atTop (𝓝 0) := by
  have ht : Tendsto (fun k : ℕ => 2 * (k : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul 2
  refine squeeze_zero' (eventually_ge_atTop 1 |>.mono fun k _ => by positivity)
    (eventually_ge_atTop 1 |>.mono fun k hk => inv_cosh_log_le hk) ht

/-- **Critical-line spectral convergence as `k → ∞` at arbitrary tower depth `d ∈ ℕ`.**
For every fixed pole-cancellation order `d ∈ ℕ` and every `τ ∈ ℝ`, the cosine transform of
`arcLineTowerProfile k d ν` converges as `k → ∞` to the cosine transform of `arcPoissonProfile ν`. -/
theorem tendsto_integral_cos_mul_arcLineTowerProfile_atTop
    (d : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] (τ : ℝ) :
    Tendsto (fun k : ℕ => ∫ v, Real.cos (τ * v) * arcLineTowerProfile k d ν v)
      atTop (𝓝 (∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)) := by
  simp_rw [integral_cos_mul_arcLineTowerProfile]
  have hcos1 : Tendsto (fun k : ℕ =>
      Real.cos (τ * (2 * Real.log k)) / Real.cosh (Real.log k)) atTop (𝓝 0) := by
    refine squeeze_zero_norm'
      (Eventually.of_forall fun k => ?_) tendsto_inv_cosh_log_atTop
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.cosh_pos _)]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (Real.cosh_pos _).le
  have hcos2 : Tendsto (fun k : ℕ =>
      Real.cos (Real.log k * τ) / Real.cosh (Real.log k / 2)) atTop (𝓝 0) := by
    refine squeeze_zero_norm'
      (Eventually.of_forall fun k => ?_) tendsto_inv_cosh_half_log_atTop
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.cosh_pos _)]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (Real.cosh_pos _).le
  have hmult1 : Tendsto (fun k : ℕ =>
      (1 - Real.cos (τ * (2 * Real.log k)) / Real.cosh (Real.log k)) ^ d) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hcos1).pow d
    simpa using this
  have hmult2 : Tendsto (fun k : ℕ =>
      (1 - Real.cos (Real.log k * τ) / Real.cosh (Real.log k / 2)) ^ 2) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hcos2).pow 2
    simpa using this
  have hprod : Tendsto (fun k : ℕ =>
      (1 - Real.cos (τ * (2 * Real.log k)) / Real.cosh (Real.log k)) ^ d *
        (1 - Real.cos (Real.log k * τ) / Real.cosh (Real.log k / 2)) ^ 2) atTop (𝓝 1) := by
    simpa using hmult1.mul hmult2
  simpa using hprod.mul_const (∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)

/-! ### Master unconditional arbitrary-order cascade & spectral convergence theorem -/

/-- **Master unconditional theorem for the arbitrary-order cascade and critical-line convergence.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every pole-cancellation depth `d ∈ ℕ`:
1. For every integer `k ≥ 2`, `arcLineTowerVector k d ν` is an even, strictly self-reciprocal,
   zero-mean, strictly positive definite function in the `O(e^{−3|v|/2})` Weil decay class that
   vanishes to order `O((1/2 − l)^{d+1})` at the strip edge `l → (1/2)⁻` and is identically blind
   on the `k^{2(d+1)}`-sublattice;
2. Along the `k^{2d}`-sublattice `arcFreq (k^{2d}(j+1) − 1)`, its sine moments satisfy the exact
   cascade law `(−k / (2 cosh(log k)))^d * ∫ arcLineAtomicDeriv (log k) ν t * sin(arcFreq j · t)`
   and converge to `0` as `k → ∞` for every `j ∈ ℕ`;
3. For every `τ ∈ ℝ`, its critical-line cosine transform converges as `k → ∞` to the strictly
   positive transform `∫ cos(τv) arcPoissonProfile ν v > 0`. -/
theorem exists_arbitraryOrder_cascade_asymptotic_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) ∧
      ∀ d : ℕ,
        (∀ k : ℕ, 2 ≤ k →
          (∀ x, arcLineTowerVector k d ν (-x) = arcLineTowerVector k d ν x) ∧
          (∀ x, x ≠ 0 → arcLineTowerVector k d ν (1 / x) =
            |x| * arcLineTowerVector k d ν x) ∧
          ∫ x, arcLineTowerVector k d ν x = 0 ∧
          (∀ j : ℕ, ∫ x, arcLineTowerDeriv k d ν x *
            Real.sin (arcFreq (k ^ (2 * (d + 1)) * (j + 1) - 1) * x) = 0) ∧
          (∀ j : ℕ, ∫ x, arcLineTowerDeriv k d ν x *
              Real.sin (arcFreq (k ^ (2 * d) * (j + 1) - 1) * x) =
            (-((k : ℝ) / (2 * Real.cosh (Real.log k)))) ^ d *
              ∫ t, arcLineAtomicDeriv (Real.log k) ν t * Real.sin (arcFreq j * t)) ∧
          (∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcLineTowerProfile k d ν v) ∧
          (∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
            |∫ v, Real.exp (l * v) * arcLineTowerProfile k d ν v| ≤
              10 * ν.real univ * (Real.log k) ^ 2 * (2 * Real.log k) ^ d *
                (1 / 2 - l) ^ (d + 1))) ∧
        (∀ j : ℕ, Tendsto (fun k : ℕ =>
          ∫ x, arcLineTowerDeriv k d ν x *
            Real.sin (arcFreq (k ^ (2 * d) * (j + 1) - 1) * x)) atTop (𝓝 0)) ∧
        ∀ τ : ℝ, Tendsto (fun k : ℕ =>
          ∫ v, Real.cos (τ * v) * arcLineTowerProfile k d ν v)
          atTop (𝓝 (∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym, hpd, fun d => ⟨fun k hk => ?_, ?_, ?_⟩⟩
  · have hk1 : 1 ≤ k := by omega
    exact ⟨arcLineTowerVector_neg_of_map_arcNeg k d hsym,
      arcLineTowerVector_inv hk1 d ν,
      integral_arcLineTowerVector_eq_zero hk1 d hsym,
      integral_arcLineTowerDeriv_mul_sin_sublattice_eq_zero hblind hk1 d,
      integral_arcLineTowerDeriv_mul_sin_cascade hblind hk1 d,
      integral_cos_mul_arcLineTowerProfile_pos hk d ν hpd,
      fun l hl0 hl => abs_integral_exp_mul_arcLineTowerProfile_le hk1 d hsym hl0 hl⟩
  · exact tendsto_integral_arcLineTowerDeriv_mul_sin_cascade_atTop hblind d
  · exact tendsto_integral_cos_mul_arcLineTowerProfile_atTop d ν

end

end RHTower
