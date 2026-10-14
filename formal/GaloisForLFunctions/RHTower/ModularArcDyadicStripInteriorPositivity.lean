import GaloisForLFunctions.RHTower.ModularArcDyadicInfiniteOrderStripEdge

/-!
# Strict interior strip positivity and `k → ∞` Laplace/Mellin convergence for the infinite-horizon dyadic modular arc tower

In `ModularArcDyadicInfiniteOrderStripEdge`, we proved that on the strip `l ∈ [0, 1/2)`, the
dyadic hyperbolic tower `R ↦ ∫ e^{lv} arcLineDyadicTowerProfile k R ν v` is non-negative and
monotonically decreasing (`Antitone`), converging as `R → ∞` to
`arcLineInfiniteDyadicLaplaceTransform k ν l ≥ 0`, which vanishes to **infinite order
(`O((1/2 − l)^{N+1})` for every `N ∈ ℕ`)** as `l → (1/2)⁻`.

A critical question for any transform defined as an infimum over `R ∈ ℕ` that vanishes to infinite
order at the boundary `l → (1/2)⁻` is whether it collapses to `0` on the interior `(0, 1/2)`.
In this module we prove unconditionally that `arcLineInfiniteDyadicLaplaceTransform k ν l` is
**strictly positive (`> 0`) at EVERY point `l ∈ [0, 1/2)`** and converges as `k → ∞` to the
strictly positive Laplace/Mellin transform `∫ e^{lv} arcPoissonProfile ν v > 0`:

1. **Strict strip positivity at every finite dyadic level `r ∈ ℕ`
   (`integral_exp_mul_arcPoissonProfile_pos`,
   `integral_exp_mul_arcLineAtomicProfile_pos`,
   `integral_exp_mul_arcLineDyadicTowerProfile_pos`):**
   Using even symmetry (`arcPoissonProfile_neg`) and `cosh(lv) ≥ 1`, we show
   `∫ e^{lv} arcPoissonProfile ν v ≥ ∫ cos(0·v) arcPoissonProfile ν v > 0`, and by strict
   monotonicity of `cosh` on `[0, ∞)`, every finite level `r ∈ ℕ` satisfies
   `0 < ∫ e^{lv} arcLineDyadicTowerProfile k r ν v` on `[0, 1/2)`.
2. **Shifted strip Weierstrass lower bound (`cosh_two_mul_div_cosh_log_pow_two_pow_add_le`,
   `integral_exp_mul_arcLineDyadicTowerProfile_add_ge`,
   `arcLineInfiniteDyadicLaplaceTransform_ge`):**
   For every `k ≥ 2`, `r₀, s ∈ ℕ`, and `l ∈ [0, 1/2)`,
   `cosh(2l log(k^{2^{r₀+s}})) / cosh(log(k^{2^{r₀+s}})) ≤ (2 / (2^{r₀} (1 − 2l) log k)) · (1/2)^s`.
   Summing over `s` yields the infinite-horizon Weierstrass lower bound
   `(1 − 4 / (2^{r₀} (1 − 2l) log k)) · ∫ e^{lv} arcLineDyadicTowerProfile k r₀ ν v ≤ arcLineInfiniteDyadicLaplaceTransform k ν l`.
3. **Strict interior positivity across the entire strip `[0, 1/2)`
   (`arcLineInfiniteDyadicLaplaceTransform_pos`):**
   Choosing `r₀` with `2^{r₀} ≥ 8 / ((1 − 2l) log k)` proves
   `0 < arcLineInfiniteDyadicLaplaceTransform k ν l` for **every** `l ∈ [0, 1/2)` and `k ≥ 2`.
4. **Two-sided sandwich at `r₀ = 0` and `k → ∞` Laplace/Mellin convergence
   (`tendsto_arcLineInfiniteDyadicLaplaceTransform_atTop`,
   `exists_dyadic_stripInteriorPositivity_infiniteOrderEdge_arcWitness`):**
   At `r₀ = 0`, `arcLineInfiniteDyadicLaplaceTransform k ν l` is sandwiched between
   `(1 − 4 / ((1 − 2l) log k)) · ∫ e^{lv} arcLineAtomicProfile (log k) ν v` and
   `∫ e^{lv} arcLineAtomicProfile (log k) ν v`, forcing
   `arcLineInfiniteDyadicLaplaceTransform k ν l → ∫ e^{lv} arcPoissonProfile ν v > 0` as `k → ∞`
   for every `l ∈ [0, 1/2)`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Strict positivity on the strip `[0, 1/2)` at every finite dyadic depth `r ∈ ℕ` -/

/-- Even symmetry of `arcPoissonProfile ν` implies
`∫ e^{lv} arcPoissonProfile ν v = ∫ cosh(lv) arcPoissonProfile ν v ≥ ∫ cos(0·v) arcPoissonProfile ν v`. -/
theorem integral_cos_zero_le_integral_exp_mul_arcPoissonProfile
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    ∫ v, Real.cos (0 * v) * arcPoissonProfile ν v ≤
      ∫ v, Real.exp (l * v) * arcPoissonProfile ν v := by
  have hI0 : Integrable (arcPoissonProfile ν) := integrable_arcPoissonProfile ν
  have hIl : Integrable fun v => Real.exp (l * v) * arcPoissonProfile ν v :=
    integrable_exp_mul_arcPoissonProfile hν hl0 hl
  have hIneg : Integrable fun v => Real.exp (-(l * v)) * arcPoissonProfile ν v := by
    have e : (fun v => Real.exp (-(l * v)) * arcPoissonProfile ν v) =
        fun v => Real.exp (l * -v) * arcPoissonProfile ν (-v) := by
      funext v; rw [mul_neg, arcPoissonProfile_neg]
    rw [e]
    exact hIl.comp_neg
  have hneg_eq : ∫ v, Real.exp (-(l * v)) * arcPoissonProfile ν v =
      ∫ v, Real.exp (l * v) * arcPoissonProfile ν v := by
    have h := integral_neg_eq_self
      (fun v : ℝ => Real.exp (l * v) * arcPoissonProfile ν v) volume
    simpa [mul_neg, arcPoissonProfile_neg] using h
  have hcosh : ∫ v, Real.exp (l * v) * arcPoissonProfile ν v =
      ∫ v, Real.cosh (l * v) * arcPoissonProfile ν v := by
    have e : (fun v => Real.cosh (l * v) * arcPoissonProfile ν v) =
        fun v => (1 / 2 : ℝ) * (Real.exp (l * v) * arcPoissonProfile ν v +
          Real.exp (-(l * v)) * arcPoissonProfile ν v) := by
      funext v; rw [Real.cosh_eq]; ring
    rw [e, integral_const_mul, integral_add hIl hIneg, hneg_eq]
    ring
  rw [hcosh]
  refine integral_mono (by simpa using hI0) (hIl.add hIneg |>.const_mul (1 / 2 : ℝ) |>.congr
    (Eventually.of_forall fun v => by dsimp; rw [Real.cosh_eq]; ring)) fun v => ?_
  simp only [zero_mul, Real.cos_zero]
  exact mul_le_mul_of_nonneg_right (Real.one_le_cosh _) (arcPoissonProfile_nonneg ν v)

/-- **Strict strip positivity of `∫ e^{lv} arcPoissonProfile ν v` for all `l ∈ [0, 1/2)`.** -/
theorem integral_exp_mul_arcPoissonProfile_pos
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    0 < ∫ v, Real.exp (l * v) * arcPoissonProfile ν v :=
  (hpd 0).trans_le (integral_cos_zero_le_integral_exp_mul_arcPoissonProfile hν hl0 hl)

/-- Strict positivity of the hyperbolic strip multiplier `1 − cosh(l · 2 log m) / cosh(log m)`
when `m ≥ 2` and `l ∈ [0, 1/2)`. -/
theorem sub_cosh_div_cosh_log_pos
    {m : ℕ} (hm : 2 ≤ m) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    0 < 1 - Real.cosh (l * (2 * Real.log m)) / Real.cosh (Real.log m) := by
  have hmgt1 : (1 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le one_lt_two hm)
  have hlog : 0 < Real.log m := Real.log_pos hmgt1
  have hC := Real.cosh_pos (Real.log m)
  rw [sub_pos, div_lt_one hC, Real.cosh_lt_cosh]
  rw [abs_of_nonneg (by positivity), abs_of_pos hlog]
  nlinarith

/-- **Strict strip positivity of `arcLineAtomicProfile (log k) ν` for `k ≥ 2` and `l ∈ [0, 1/2)`.** -/
theorem integral_exp_mul_arcLineAtomicProfile_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    0 < ∫ v, Real.exp (l * v) * arcLineAtomicProfile (Real.log k) ν v := by
  have hkgt1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le one_lt_two hk)
  have hlog : 0 < Real.log k := Real.log_pos hkgt1
  have hC := Real.cosh_pos (Real.log k / 2)
  rw [integral_exp_mul_arcLineAtomicProfile (Real.log k) hν hl0 hl]
  refine mul_pos (sq_pos_of_pos ?_) (integral_exp_mul_arcPoissonProfile_pos hν hpd hl0 hl)
  rw [sub_pos, div_lt_one hC, Real.cosh_lt_cosh]
  rw [abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
  nlinarith

/-- **Strict strip positivity at every finite dyadic depth `r ∈ ℕ` (`k ≥ 2`, `l ∈ [0, 1/2)`).** -/
theorem integral_exp_mul_arcLineDyadicTowerProfile_pos
    {k : ℕ} (hk : 2 ≤ k) (r : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    0 < ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r ν v := by
  induction r with
  | zero => exact integral_exp_mul_arcLineAtomicProfile_pos hk hν hpd hl0 hl
  | succ r ih =>
    rw [integral_exp_mul_arcLineDyadicTowerProfile_succ k r hν hl0 hl]
    exact mul_pos (sub_cosh_div_cosh_log_pos (two_le_pow_two_pow hk r) hl0 hl) ih

/-! ### Shifted strip Weierstrass lower bound and strict interior positivity of the infinite-horizon limit -/

/-- For any `b ≥ 0` and `l ∈ [0, 1/2)`, `cosh(l · 2b) / cosh(b) ≤ 2 · exp(−(1 − 2l) b)`. -/
theorem cosh_two_mul_div_cosh_le_two_mul_exp_neg
    {b l : ℝ} (hb : 0 ≤ b) (hl0 : 0 ≤ l) :
    Real.cosh (l * (2 * b)) / Real.cosh b ≤ 2 * Real.exp (-((1 - 2 * l) * b)) := by
  have hC := Real.cosh_pos b
  have hnum : Real.cosh (l * (2 * b)) ≤ Real.exp (2 * l * b) := by
    rw [Real.cosh_eq]
    have hle : Real.exp (-(l * (2 * b))) ≤ Real.exp (2 * l * b) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have heq : Real.exp (l * (2 * b)) = Real.exp (2 * l * b) := by ring_nf
    linarith
  have hden : Real.exp b / 2 ≤ Real.cosh b := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-b)]
  have hexp_pos : 0 < Real.exp b / 2 := by positivity
  calc Real.cosh (l * (2 * b)) / Real.cosh b
      ≤ Real.exp (2 * l * b) / Real.cosh b :=
        div_le_div_of_nonneg_right hnum hC.le
    _ ≤ Real.exp (2 * l * b) / (Real.exp b / 2) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hexp_pos hden
    _ = 2 * (Real.exp (2 * l * b) / Real.exp b) := by ring
    _ = 2 * Real.exp (-((1 - 2 * l) * b)) := by
        rw [← Real.exp_sub]
        congr 2
        ring

/-- For any `y > 0`, `exp(−y) ≤ 1 / y`. -/
theorem exp_neg_le_one_div {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) ≤ 1 / y := by
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hy (by linarith [Real.add_one_le_exp y])

/-- **Shifted geometric `cosh` ratio bound on the strip `[0, 1/2)` (`k ≥ 2`):**
For every `r₀, s ∈ ℕ` and `l ∈ [0, 1/2)`,
`cosh(l · 2 log(k^{2^{r₀+s}})) / cosh(log(k^{2^{r₀+s}})) ≤ (2 / (2^{r₀} (1 − 2l) log k)) · (1/2)^s`. -/
theorem cosh_two_mul_div_cosh_log_pow_two_pow_add_le
    {k : ℕ} (hk : 2 ≤ k) (r₀ s : ℕ) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    Real.cosh (l * (2 * Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ))) ≤
      (2 / ((2 : ℝ) ^ r₀ * (1 - 2 * l) * Real.log k)) * (1 / 2 : ℝ) ^ s := by
  have hkgt1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le one_lt_two hk)
  have hlog : 0 < Real.log k := Real.log_pos hkgt1
  have h12l : 0 < 1 - 2 * l := by linarith
  set b := Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ))
  have hb_eq : b = ((2 : ℝ) ^ r₀ * Real.log k) * (2 : ℝ) ^ s := by
    dsimp [b]
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow, Nat.cast_ofNat, pow_add]
    ring
  have hb0 : 0 ≤ b := by rw [hb_eq]; positivity
  have hy : 0 < (1 - 2 * l) * b := by rw [hb_eq]; positivity
  calc Real.cosh (l * (2 * b)) / Real.cosh b
      ≤ 2 * Real.exp (-((1 - 2 * l) * b)) :=
        cosh_two_mul_div_cosh_le_two_mul_exp_neg hb0 hl0
    _ ≤ 2 * (1 / ((1 - 2 * l) * b)) :=
        mul_le_mul_of_nonneg_left (exp_neg_le_one_div hy) (by positivity)
    _ = (2 / ((2 : ℝ) ^ r₀ * (1 - 2 * l) * Real.log k)) * (1 / 2 : ℝ) ^ s := by
        rw [hb_eq, one_div_pow]
        field_simp

/-- **Shifted Weierstrass sum lower bound on the Laplace/Mellin strip transform.** -/
theorem integral_exp_mul_arcLineDyadicTowerProfile_add_ge_sub_sum
    {k : ℕ} (hk : 1 ≤ k) (r₀ S : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    (1 - ∑ s ∈ Finset.range S,
      Real.cosh (l * (2 * Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) *
      (∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r₀ ν v) ≤
    ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k (r₀ + S) ν v := by
  have hpos0 := integral_exp_mul_arcLineDyadicTowerProfile_nonneg hk r₀ hν hl0 hl
  induction S with
  | zero => simp
  | succ S ih =>
    rw [← Nat.add_assoc, integral_exp_mul_arcLineDyadicTowerProfile_succ k (r₀ + S) hν hl0 hl,
      Finset.sum_range_succ]
    set a := Real.cosh (l * (2 * Real.log ((k ^ (2 ^ (r₀ + S)) : ℕ)))) /
      Real.cosh (Real.log ((k ^ (2 ^ (r₀ + S)) : ℕ)))
    set Ssum := ∑ s ∈ Finset.range S,
      Real.cosh (l * (2 * Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))
    have ha0 : 0 ≤ a := by positivity
    have ha1 : 0 ≤ 1 - a :=
      (sub_cosh_div_cosh_log_mem_Icc (one_le_pow_two_pow hk (r₀ + S)) hl0 hl.le).1
    have hSsum0 : 0 ≤ Ssum := Finset.sum_nonneg fun s _ => by positivity
    have hweier : 1 - (Ssum + a) ≤ (1 - a) * (1 - Ssum) := by nlinarith
    calc (1 - (Ssum + a)) * (∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r₀ ν v)
        ≤ ((1 - a) * (1 - Ssum)) *
            (∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r₀ ν v) :=
          mul_le_mul_of_nonneg_right hweier hpos0
      _ = (1 - a) * ((1 - Ssum) *
            (∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r₀ ν v)) := by ring
      _ ≤ (1 - a) * (∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k (r₀ + S) ν v) :=
          mul_le_mul_of_nonneg_left ih ha1

/-- **Closed-form Weierstrass lower bound on the finite-depth Laplace/Mellin strip transform.** -/
theorem integral_exp_mul_arcLineDyadicTowerProfile_add_ge
    {k : ℕ} (hk : 2 ≤ k) (r₀ S : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    (1 - 4 / ((2 : ℝ) ^ r₀ * (1 - 2 * l) * Real.log k)) *
      (∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r₀ ν v) ≤
    ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k (r₀ + S) ν v := by
  have hk1 : 1 ≤ k := by omega
  have hkgt1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le one_lt_two hk)
  have hlog : 0 < Real.log k := Real.log_pos hkgt1
  have h12l : 0 < 1 - 2 * l := by linarith
  have hpos0 := integral_exp_mul_arcLineDyadicTowerProfile_nonneg hk1 r₀ hν hl0 hl
  have hsum : ∑ s ∈ Finset.range S,
      Real.cosh (l * (2 * Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) /
        Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ))) ≤
      4 / ((2 : ℝ) ^ r₀ * (1 - 2 * l) * Real.log k) := by
    calc ∑ s ∈ Finset.range S,
          Real.cosh (l * (2 * Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))) /
            Real.cosh (Real.log ((k ^ (2 ^ (r₀ + s)) : ℕ)))
        ≤ ∑ s ∈ Finset.range S,
            (2 / ((2 : ℝ) ^ r₀ * (1 - 2 * l) * Real.log k)) * (1 / 2 : ℝ) ^ s :=
          Finset.sum_le_sum fun s _ =>
            cosh_two_mul_div_cosh_log_pow_two_pow_add_le hk r₀ s hl0 hl
      _ = (2 / ((2 : ℝ) ^ r₀ * (1 - 2 * l) * Real.log k)) *
            ∑ s ∈ Finset.range S, (1 / 2 : ℝ) ^ s := by rw [Finset.mul_sum]
      _ ≤ (2 / ((2 : ℝ) ^ r₀ * (1 - 2 * l) * Real.log k)) * 2 :=
          mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two S) (by positivity)
      _ = 4 / ((2 : ℝ) ^ r₀ * (1 - 2 * l) * Real.log k) := by ring
  refine (mul_le_mul_of_nonneg_right (by linarith) hpos0).trans
    (integral_exp_mul_arcLineDyadicTowerProfile_add_ge_sub_sum hk1 r₀ S hν hl0 hl)

/-- **Closed-form Weierstrass lower bound on `arcLineInfiniteDyadicLaplaceTransform k ν l`.** -/
theorem arcLineInfiniteDyadicLaplaceTransform_ge
    {k : ℕ} (hk : 2 ≤ k) (r₀ : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    (1 - 4 / ((2 : ℝ) ^ r₀ * (1 - 2 * l) * Real.log k)) *
      (∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r₀ ν v) ≤
    arcLineInfiniteDyadicLaplaceTransform k ν l := by
  have hk1 : 1 ≤ k := by omega
  have ht : Tendsto (fun S : ℕ =>
      ∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k (S + r₀) ν v)
      atTop (𝓝 (arcLineInfiniteDyadicLaplaceTransform k ν l)) :=
    (tendsto_integral_exp_mul_arcLineDyadicTowerProfile_atTop hk1 hν hl0 hl).comp
      (tendsto_add_atTop_nat r₀)
  exact ge_of_tendsto ht
    (Eventually.of_forall fun S => by
      simpa [Nat.add_comm S r₀] using
        integral_exp_mul_arcLineDyadicTowerProfile_add_ge hk r₀ S hν hl0 hl)

/-- **Strict positivity of `arcLineInfiniteDyadicLaplaceTransform k ν l` across the ENTIRE strip `[0, 1/2)`.**
Even though `arcLineInfiniteDyadicLaplaceTransform k ν l` vanishes to infinite order
`O((1/2 − l)^{N+1})` for all `N ∈ ℕ` at the boundary `l → (1/2)⁻`, it is **strictly positive (`> 0`)**
at every interior strip point `l ∈ [0, 1/2)`. -/
theorem arcLineInfiniteDyadicLaplaceTransform_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    0 < arcLineInfiniteDyadicLaplaceTransform k ν l := by
  have hkgt1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le one_lt_two hk)
  have hlog : 0 < Real.log k := Real.log_pos hkgt1
  have h12l : 0 < 1 - 2 * l := by linarith
  have hδ : 0 < (1 - 2 * l) * Real.log k := mul_pos h12l hlog
  have ht : Tendsto (fun r₀ : ℕ => (2 : ℝ) ^ r₀) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  obtain ⟨r₀, hr₀⟩ := (ht.eventually_ge_atTop (8 / ((1 - 2 * l) * Real.log k))).exists
  have hdiv : 4 / ((2 : ℝ) ^ r₀ * (1 - 2 * l) * Real.log k) ≤ 1 / 2 := by
    have h1 : 8 ≤ (2 : ℝ) ^ r₀ * ((1 - 2 * l) * Real.log k) :=
      (div_le_iff₀ hδ).mp hr₀
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hpos_r0 := integral_exp_mul_arcLineDyadicTowerProfile_pos hk r₀ hν hpd hl0 hl
  have hge := arcLineInfiniteDyadicLaplaceTransform_ge hk r₀ hν hl0 hl
  have hhalf : (1 / 2 : ℝ) * (∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r₀ ν v) ≤
      (1 - 4 / ((2 : ℝ) ^ r₀ * (1 - 2 * l) * Real.log k)) *
        (∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r₀ ν v) :=
    mul_le_mul_of_nonneg_right (by linarith) hpos_r0.le
  linarith

/-! ### Asymptotic `k → ∞` convergence of `arcLineInfiniteDyadicLaplaceTransform` on `[0, 1/2)` -/

/-- For every `l ∈ [0, 1/2)`, as `k → ∞`, `∫ e^{lv} arcLineAtomicProfile (log k) ν v` converges to
`∫ e^{lv} arcPoissonProfile ν v`. -/
theorem tendsto_integral_exp_mul_arcLineAtomicProfile_log_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    Tendsto (fun k : ℕ => ∫ v, Real.exp (l * v) * arcLineAtomicProfile (Real.log k) ν v)
      atTop (𝓝 (∫ v, Real.exp (l * v) * arcPoissonProfile ν v)) := by
  simp_rw [integral_exp_mul_arcLineAtomicProfile _ hν hl0 hl]
  have h12l : 0 < 1 / 2 - l := by linarith
  have hratio : Tendsto (fun k : ℕ =>
      Real.cosh (l * Real.log k) / Real.cosh (Real.log k / 2)) atTop (𝓝 0) := by
    have hexp : Tendsto (fun k : ℕ =>
        2 * (1 / ((1 / 2 - l) * Real.log k))) atTop (𝓝 0) := by
      have hlog_top : Tendsto (fun k : ℕ => (1 / 2 - l) * Real.log k) atTop atTop :=
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop h12l
      simpa using (tendsto_inv_atTop_zero.comp hlog_top).const_mul 2
    refine squeeze_zero' (Eventually.of_forall fun k => by positivity) ?_ hexp
    filter_upwards [eventually_ge_atTop 2] with k hk
    have hkgt1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le one_lt_two hk)
    have hlog : 0 < Real.log k := Real.log_pos hkgt1
    have hb : 0 ≤ Real.log k / 2 := by positivity
    have h1 := cosh_two_mul_div_cosh_le_two_mul_exp_neg hb hl0
    have heq1 : l * (2 * (Real.log k / 2)) = l * Real.log k := by ring
    have heq2 : (1 - 2 * l) * (Real.log k / 2) = (1 / 2 - l) * Real.log k := by ring
    rw [heq1, heq2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left
      (exp_neg_le_one_div (mul_pos h12l hlog)) (by positivity))
  have hmult : Tendsto (fun k : ℕ =>
      (1 - Real.cosh (l * Real.log k) / Real.cosh (Real.log k / 2)) ^ 2) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hratio).pow 2
    simpa using this
  simpa using hmult.mul_const (∫ v, Real.exp (l * v) * arcPoissonProfile ν v)

/-- **Asymptotic `k → ∞` convergence of `arcLineInfiniteDyadicLaplaceTransform k ν l` on `[0, 1/2)`:**
For every `l ∈ [0, 1/2)`, as `k → ∞`,
`arcLineInfiniteDyadicLaplaceTransform k ν l → ∫ e^{lv} arcPoissonProfile ν v > 0`. -/
theorem tendsto_arcLineInfiniteDyadicLaplaceTransform_atTop
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    Tendsto (fun k : ℕ => arcLineInfiniteDyadicLaplaceTransform k ν l)
      atTop (𝓝 (∫ v, Real.exp (l * v) * arcPoissonProfile ν v)) := by
  have h0 := tendsto_integral_exp_mul_arcLineAtomicProfile_log_atTop hν hl0 hl
  have h12l : 0 < 1 - 2 * l := by linarith
  have hfactor : Tendsto (fun k : ℕ =>
      1 - 4 / ((2 : ℝ) ^ 0 * (1 - 2 * l) * Real.log k)) atTop (𝓝 1) := by
    have hlog_top : Tendsto (fun k : ℕ => (2 : ℝ) ^ 0 * (1 - 2 * l) * Real.log k) atTop atTop := by
      simpa using (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop h12l
    have hdiv : Tendsto (fun k : ℕ => 4 / ((2 : ℝ) ^ 0 * (1 - 2 * l) * Real.log k)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hlog_top).const_mul 4
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hdiv
  have hlow : Tendsto (fun k : ℕ =>
      (1 - 4 / ((2 : ℝ) ^ 0 * (1 - 2 * l) * Real.log k)) *
        ∫ v, Real.exp (l * v) * arcLineAtomicProfile (Real.log k) ν v)
      atTop (𝓝 (∫ v, Real.exp (l * v) * arcPoissonProfile ν v)) := by
    simpa using hfactor.mul h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow h0 ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with k hk
    simpa [arcLineDyadicTowerProfile] using
      arcLineInfiniteDyadicLaplaceTransform_ge hk 0 hν hl0 hl
  · filter_upwards [eventually_ge_atTop 1] with k hk
    simpa [arcLineDyadicTowerProfile] using
      arcLineInfiniteDyadicLaplaceTransform_le hk 0 hν hl0 hl

/-! ### Master unconditional interior strip positivity and infinite-order edge vanishing theorem -/

/-- **Master unconditional theorem for the infinite-horizon dyadic strip transform.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that:
1. For every integer `k ≥ 2`, the single infinite-horizon Laplace/Mellin transform
   `arcLineInfiniteDyadicLaplaceTransform k ν` is **strictly positive (`> 0`) at EVERY interior
   strip point `l ∈ [0, 1/2)`** AND **vanishes to infinite order (`O((1/2 − l)^{N+1})` for EVERY
   `N ∈ ℕ`)** at the strip edge `l → (1/2)⁻`;
2. At `l = 0` (`s = 1/2`), `arcLineInfiniteDyadicLaplaceTransform k ν 0 = arcLineInfiniteDyadicCosTransform k ν 0 > 0`,
   and `0 < arcLineInfiniteDyadicCosTransform k ν τ` across the entire critical line `τ ∈ ℝ`;
3. As `k → ∞`, simultaneously:
   - `arcLineInfiniteDyadicLaplaceTransform k ν l → ∫ e^{lv} arcPoissonProfile ν v > 0` for every `l ∈ [0, 1/2)`,
   - `arcLineInfiniteDyadicCosTransform k ν τ → ∫ cos(τv) arcPoissonProfile ν v > 0` for every `τ ∈ ℝ`, and
   - `arcLineInfiniteDyadicSineMoment k ν (arcFreq n) → 0` for every integer frequency `n ∈ ℕ`. -/
theorem exists_dyadic_stripInteriorPositivity_infiniteOrderEdge_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ l : ℝ, 0 ≤ l → l < 1 / 2 → 0 < ∫ v, Real.exp (l * v) * arcPoissonProfile ν v) ∧
      (∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ l : ℝ, 0 ≤ l → l < 1 / 2 → 0 < arcLineInfiniteDyadicLaplaceTransform k ν l) ∧
        (∀ τ : ℝ, 0 < arcLineInfiniteDyadicCosTransform k ν τ) ∧
        arcLineInfiniteDyadicLaplaceTransform k ν 0 = arcLineInfiniteDyadicCosTransform k ν 0 ∧
        (∀ N : ℕ, ∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
          |arcLineInfiniteDyadicLaplaceTransform k ν l| ≤
            (10 * ν.real univ * dyadicStripConst k N) * (1 / 2 - l) ^ (N + 1)) ∧
        (∀ N : ℕ, Tendsto (fun l : ℝ =>
          arcLineInfiniteDyadicLaplaceTransform k ν l / (1 / 2 - l) ^ N)
          (𝓝[<] (1 / 2)) (𝓝 0))) ∧
      (∀ l : ℝ, 0 ≤ l → l < 1 / 2 →
        Tendsto (fun k : ℕ => arcLineInfiniteDyadicLaplaceTransform k ν l)
          atTop (𝓝 (∫ v, Real.exp (l * v) * arcPoissonProfile ν v))) ∧
      (∀ τ : ℝ, Tendsto (fun k : ℕ => arcLineInfiniteDyadicCosTransform k ν τ)
        atTop (𝓝 (∫ v, Real.cos (τ * v) * arcPoissonProfile ν v))) ∧
      (∀ n : ℕ, Tendsto (fun k : ℕ => arcLineInfiniteDyadicSineMoment k ν (arcFreq n))
        atTop (𝓝 0)) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym,
    fun l hl0 hl => integral_exp_mul_arcPoissonProfile_pos hsym hpd hl0 hl,
    hpd,
    fun k hk => ?_,
    fun l hl0 hl => tendsto_arcLineInfiniteDyadicLaplaceTransform_atTop hsym hl0 hl,
    tendsto_arcLineInfiniteDyadicCosTransform_atTop ν,
    tendsto_arcLineInfiniteDyadicSineMoment_arcFreq_atTop hblind⟩
  have hk1 : 1 ≤ k := by omega
  exact ⟨fun l hl0 hl => arcLineInfiniteDyadicLaplaceTransform_pos hk hsym hpd hl0 hl,
    fun τ => arcLineInfiniteDyadicCosTransform_pos hk hpd τ,
    arcLineInfiniteDyadicLaplaceTransform_zero_eq_cosTransform hk hsym,
    fun N l hl0 hl => arcLineInfiniteDyadicLaplaceTransform_le_pow_sub_half hk1 N hsym hl0 hl,
    fun N => tendsto_div_pow_arcLineInfiniteDyadicLaplaceTransform_nhdsWithin hk1 N hsym⟩

end

end RHTower
