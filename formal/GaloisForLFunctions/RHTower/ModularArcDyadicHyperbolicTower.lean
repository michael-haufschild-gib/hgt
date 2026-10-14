import GaloisForLFunctions.RHTower.ModularArcUniversalSqrtMomentBound

/-!
# The dyadic (exponent-doubling) hyperbolic pole-filtered modular arc tower

In `ModularArcArbitraryOrderStripEdgeTower`, iterating `hyperbolicFilter` at the fixed integer scale
`k` produced `arcLineTowerVector k d ν`, which vanishes to order `O((1/2 − l)^{d+1})` at the critical
strip edge while annihilating the `k^{2(d+1)}`-sublattice (whose exponent grows linearly in `d`).

In this module we construct the **dyadic (exponent-doubling) hyperbolic tower**
`(arcLineDyadicTowerVector k r ν, arcLineDyadicTowerDeriv k r ν, arcLineDyadicTowerProfile k r ν)`
by applying `hyperbolicFilter` at scale `m_r = k^{2^r}` at step `r ↦ r + 1`. Because
`m_r² = (k^{2^r})² = k^{2^{r+1}}` equals the current blind sublattice modulus `N_r = k^{2^{r+1}}`,
each step squares the blind sublattice modulus `N_{r+1} = m_r² N_r = N_r² = k^{2^{r+2}}`.

## Main results

1. **Doubly-exponential `k^{2^{r+1}}`-sublattice blindness
   (`integral_arcLineDyadicTowerDeriv_mul_sin_sublattice_eq_zero`):**
   For every `k ≥ 1`, `r ∈ ℕ`, and `j ∈ ℕ`, `arcLineDyadicTowerDeriv k r ν` is identically blind
   on the `k^{2^{r+1}}`-sublattice `arcFreq (k^{2^{r+1}}(j+1) − 1)`.
2. **Universal `k`-independent `O(√c)` frequency bound across doubly-exponential scales
   (`abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_sqrt`):**
   Even though the filter scales `m_r = k^{2^r}` grow doubly-exponentially, the scale-invariant
   preservation law from `ModularArcUniversalSqrtMomentBound` ensures that for all `c > 0`,
   `|∫ arcLineDyadicTowerDeriv k r ν x · sin(c x) dx| ≤ 2^r · (8 √(π/2) · ν.real univ) · √c`,
   with constant **completely independent of `k`**.
3. **One-step exact reduction on the `k^{2^{r+1}}`-sublattice directly to `arcFreq j`
   (`integral_arcLineDyadicTowerDeriv_succ_mul_sin_sublattice`,
   `abs_integral_arcLineDyadicTowerDeriv_succ_mul_sin_sublattice_le`):**
   Because `m_r² = k^{2^{r+1}}`, along the `k^{2^{r+1}}`-sublattice `arcFreq (k^{2^{r+1}}(j+1) − 1)`
   the sine moment of level `r + 1` collapses in a **single step** to the unscaled integer frequency
   `arcFreq j` of level `r`, and is bounded by `2^r · (8 √(π/2) · ν.real univ) · √(arcFreq j)`
   independently of `k`.
4. **Arbitrary-order strip-edge vanishing and strict critical-line positive definiteness
   (`exists_dyadic_hyperbolic_tower_arcWitness`):**
   At every dyadic depth `r ∈ ℕ`, `arcLineDyadicTowerVector k r ν` is even, strictly self-reciprocal,
   zero-mean, strictly positive definite on the critical line (`k ≥ 2`), and vanishes to order
   `O((1/2 − l)^{r+1})` as `l → (1/2)⁻`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Exponent-doubling arithmetic identities -/

theorem pow_two_pow_sq (k r : ℕ) : (k ^ (2 ^ r)) ^ 2 = k ^ (2 ^ (r + 1)) := by
  rw [← pow_mul, pow_succ]

theorem pow_two_pow_sq_mul_self (k r : ℕ) :
    (k ^ (2 ^ r)) ^ 2 * k ^ (2 ^ (r + 1)) = k ^ (2 ^ (r + 2)) := by
  rw [pow_two_pow_sq, ← pow_add,
    show 2 ^ (r + 1) + 2 ^ (r + 1) = 2 ^ (r + 1) * 2 by ring, ← pow_succ]

theorem one_le_pow_two_pow {k : ℕ} (hk : 1 ≤ k) (r : ℕ) : 1 ≤ k ^ (2 ^ r) :=
  Nat.one_le_pow (2 ^ r) k hk

theorem two_le_pow_two_pow {k : ℕ} (hk : 2 ≤ k) (r : ℕ) : 2 ≤ k ^ (2 ^ r) := by
  have hpos : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
  calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (2 ^ r) := Nat.pow_le_pow_right (by omega) hpos
    _ ≤ k ^ (2 ^ r) := Nat.pow_le_pow_left hk (2 ^ r)

/-! ### Definition of the dyadic hyperbolic modular arc tower -/

/-- Level `r` of the dyadic (exponent-doubling) hyperbolic modular arc line vector tower,
obtained by applying `hyperbolicFilterVec (k^{2^r})` at step `r ↦ r + 1`. -/
def arcLineDyadicTowerVector (k : ℕ) : ℕ → Measure ArcParam → ℝ → ℝ
  | 0, ν => arcLineAtomicVector (Real.log k) ν
  | r + 1, ν => hyperbolicFilterVec (k ^ (2 ^ r)) (arcLineDyadicTowerVector k r ν)

/-- Level `r` derivative of the dyadic hyperbolic tower. -/
def arcLineDyadicTowerDeriv (k : ℕ) : ℕ → Measure ArcParam → ℝ → ℝ
  | 0, ν => arcLineAtomicDeriv (Real.log k) ν
  | r + 1, ν => hyperbolicFilterDeriv (k ^ (2 ^ r)) (arcLineDyadicTowerDeriv k r ν)

/-- Level `r` log-scale profile of the dyadic hyperbolic tower. -/
def arcLineDyadicTowerProfile (k : ℕ) : ℕ → Measure ArcParam → ℝ → ℝ
  | 0, ν => arcLineAtomicProfile (Real.log k) ν
  | r + 1, ν => hyperbolicFilterProfile (k ^ (2 ^ r)) (arcLineDyadicTowerProfile k r ν)

/-- Strip-edge constant at dyadic level `r`. -/
def dyadicStripConst (k : ℕ) : ℕ → ℝ
  | 0 => (Real.log k) ^ 2
  | r + 1 => 2 * Real.log ((k ^ (2 ^ r) : ℕ)) * dyadicStripConst k r

/-! ### Structural, symmetry, self-reciprocity, and spectral preservation -/

theorem hasDerivAt_arcLineDyadicTowerVector (k r : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    ∀ x, HasDerivAt (arcLineDyadicTowerVector k r ν) (arcLineDyadicTowerDeriv k r ν x) x := by
  induction r with
  | zero => exact hasDerivAt_arcLineAtomicVector (Real.log k) ν
  | succ r ih => exact hasDerivAt_hyperbolicFilterVec (k ^ (2 ^ r)) ih

theorem arcLineDyadicTowerVector_neg_of_map_arcNeg (k r : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) :
    ∀ x, arcLineDyadicTowerVector k r ν (-x) = arcLineDyadicTowerVector k r ν x := by
  induction r with
  | zero => exact arcLineAtomicVector_neg_of_map_arcNeg (Real.log k) hν
  | succ r ih => exact hyperbolicFilterVec_neg (k ^ (2 ^ r)) ih

theorem arcLineDyadicTowerDeriv_neg_of_map_arcNeg (k r : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) :
    ∀ x, arcLineDyadicTowerDeriv k r ν (-x) = -arcLineDyadicTowerDeriv k r ν x := by
  induction r with
  | zero => exact arcLineAtomicDeriv_neg_of_map_arcNeg (Real.log k) hν
  | succ r ih => exact hyperbolicFilterDeriv_neg (k ^ (2 ^ r)) ih

theorem arcLineDyadicTowerProfile_neg (k r : ℕ) (ν : Measure ArcParam) :
    ∀ v, arcLineDyadicTowerProfile k r ν (-v) = arcLineDyadicTowerProfile k r ν v := by
  induction r with
  | zero => exact arcLineAtomicProfile_neg (Real.log k) ν
  | succ r ih => exact hyperbolicFilterProfile_neg (k ^ (2 ^ r)) ih

theorem arcLineDyadicTowerVector_inv {k : ℕ} (hk : 1 ≤ k) (r : ℕ) (ν : Measure ArcParam) :
    ∀ x, x ≠ 0 →
      arcLineDyadicTowerVector k r ν (1 / x) = |x| * arcLineDyadicTowerVector k r ν x := by
  induction r with
  | zero => exact fun x hx => arcLineAtomicVector_inv (Real.log k) ν hx
  | succ r ih => exact fun x hx => hyperbolicFilterVec_inv (one_le_pow_two_pow hk r) ih hx

theorem exp_half_mul_arcLineDyadicTowerVector {k : ℕ} (hk : 1 ≤ k) (r : ℕ) (ν : Measure ArcParam) :
    ∀ v, Real.exp (v / 2) * arcLineDyadicTowerVector k r ν (Real.exp v) =
      arcLineDyadicTowerProfile k r ν v := by
  induction r with
  | zero => exact exp_half_mul_arcLineAtomicVector (Real.log k) ν
  | succ r ih => exact exp_half_mul_hyperbolicFilterVec (one_le_pow_two_pow hk r) ih

theorem integrable_arcLineDyadicTowerVector {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Integrable (arcLineDyadicTowerVector k r ν) := by
  induction r with
  | zero =>
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact integrable_arcLineAtomicVector (Real.log_nonneg hk1) hν
  | succ r ih => exact integrable_hyperbolicFilterVec (one_le_pow_two_pow hk r) ih

theorem integrable_arcLineDyadicTowerDeriv {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineDyadicTowerDeriv k r ν) := by
  induction r with
  | zero => exact integrable_arcLineAtomicDeriv (Real.log k) ν
  | succ r ih => exact integrable_hyperbolicFilterDeriv (one_le_pow_two_pow hk r) ih

theorem integrable_arcLineDyadicTowerProfile (k r : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineDyadicTowerProfile k r ν) := by
  induction r with
  | zero => exact integrable_arcLineAtomicProfile (Real.log k) ν
  | succ r ih => exact integrable_hyperbolicFilterProfile (k ^ (2 ^ r)) ih

theorem integral_arcLineDyadicTowerVector_eq_zero {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    ∫ x, arcLineDyadicTowerVector k r ν x = 0 := by
  induction r with
  | zero =>
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact integral_arcLineAtomicVector_eq_zero (Real.log_nonneg hk1) hν
  | succ r ih =>
    exact integral_hyperbolicFilterVec_eq_zero (one_le_pow_two_pow hk r)
      (integrable_arcLineDyadicTowerVector hk r hν) ih

/-- **Strict positive definiteness on the critical line at every dyadic depth `r ∈ ℕ`.** -/
theorem integral_cos_mul_arcLineDyadicTowerProfile_pos {k : ℕ} (hk : 2 ≤ k) (r : ℕ)
    (ν : Measure ArcParam) [IsFiniteMeasure ν]
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v := by
  induction r with
  | zero =>
    have hkgt1 : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le one_lt_two hk)
    exact integral_cos_mul_arcLineAtomicProfile_pos (Real.log_pos hkgt1) ν hpd τ
  | succ r ih =>
    exact integral_cos_mul_hyperbolicFilterProfile_pos (two_le_pow_two_pow hk r)
      (integrable_arcLineDyadicTowerProfile k r ν) (arcLineDyadicTowerProfile_neg k r ν) ih

theorem integrable_exp_mul_arcLineDyadicTowerProfile (k r : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    Integrable fun v => Real.exp (l * v) * arcLineDyadicTowerProfile k r ν v := by
  induction r with
  | zero => exact integrable_exp_mul_arcLineAtomicProfile (Real.log k) hν hl0 hl
  | succ r ih => exact integrable_exp_mul_hyperbolicFilterProfile (k ^ (2 ^ r)) ih

/-- **Order-`(r + 1)` strip-edge vanishing bound for the dyadic tower at level `r ∈ ℕ`.** -/
theorem abs_integral_exp_mul_arcLineDyadicTowerProfile_le {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r ν v| ≤
      (10 * ν.real univ * dyadicStripConst k r) * (1 / 2 - l) ^ (r + 1) := by
  induction r with
  | zero =>
    simpa [arcLineDyadicTowerProfile, arcLineTowerProfile, dyadicStripConst] using
      abs_integral_exp_mul_arcLineTowerProfile_le hk 0 hν hl0 hl
  | succ r ih =>
    have hstep := abs_integral_exp_mul_hyperbolicFilterProfile_le (one_le_pow_two_pow hk r)
      hl0 hl.le (integrable_exp_mul_arcLineDyadicTowerProfile k r hν hl0 hl) ih
    refine hstep.trans_eq ?_
    simp only [dyadicStripConst]
    ring

/-- **Order-`r` divided-difference vanishing at `l → (1/2)⁻` for the dyadic tower.** -/
theorem tendsto_div_pow_integral_exp_mul_arcLineDyadicTowerProfile_nhdsWithin
    {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      (∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r ν v) / (1 / 2 - l) ^ r)
      (𝓝[<] (1 / 2)) (𝓝 0) := by
  set D := 10 * ν.real univ * dyadicStripConst k r
  have hlin : Tendsto (fun l : ℝ => D * (1 / 2 - l)) (𝓝[<] (1 / 2)) (𝓝 0) := by
    have hcont : Continuous fun l : ℝ => D * (1 / 2 - l) := by fun_prop
    have h := (hcont.continuousAt (x := (1 / 2 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 / 2 : ℝ)))
    rwa [sub_self, mul_zero] at h
  refine squeeze_zero_norm' ?_ hlin
  have hmem : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[<] (1 / 2 : ℝ) :=
    Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hmem] with l hl
  have hκ : 0 < 1 / 2 - l := by linarith [hl.2]
  have hpow : 0 < (1 / 2 - l) ^ r := pow_pos hκ r
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
  calc |∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r ν v|
      ≤ D * (1 / 2 - l) ^ (r + 1) :=
        abs_integral_exp_mul_arcLineDyadicTowerProfile_le hk r hν hl.1.le hl.2
    _ = D * (1 / 2 - l) * (1 / 2 - l) ^ r := by rw [pow_succ']; ring

/-! ### Doubly-exponential `k^{2^{r+1}}`-sublattice blindness and `k`-independent `O(√c)` bounds -/

/-- **Doubly-exponential `k^{2^{r+1}}`-sublattice blindness:**
At dyadic depth `r ∈ ℕ`, `arcLineDyadicTowerDeriv k r ν` is identically blind along the
`k^{2^{r+1}}`-sublattice `arcFreq (k^{2^{r+1}}(j+1) − 1)` for all `j ∈ ℕ`. -/
theorem integral_arcLineDyadicTowerDeriv_mul_sin_sublattice_eq_zero
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (r j : ℕ) :
    ∫ x, arcLineDyadicTowerDeriv k r ν x *
      Real.sin (arcFreq (k ^ (2 ^ (r + 1)) * (j + 1) - 1) * x) = 0 := by
  induction r generalizing j with
  | zero =>
    simpa [arcLineDyadicTowerDeriv] using
      integral_arcLineAtomicDeriv_log_mul_sin_sq_mul_eq_zero hblind hk j
  | succ r ih =>
    rw [← pow_two_pow_sq_mul_self k r]
    exact integral_hyperbolicFilterDeriv_mul_sin_sublattice_eq_zero
      (one_le_pow_two_pow hk r) (Nat.one_le_pow (2 ^ (r + 1)) k hk)
      (integrable_arcLineDyadicTowerDeriv hk r ν) ih j

/-- **Scale-independent `O(√c)` bound across doubly-exponential dyadic scales:**
For every `k ≥ 1`, `r ∈ ℕ`, and `c > 0`, `|∫ arcLineDyadicTowerDeriv k r ν x · sin(c x) dx|` is
bounded by `2^r · (8 √(π/2) · ν.real univ) · √c`, with constant completely independent of `k`. -/
theorem abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_sqrt
    {k : ℕ} (hk : 1 ≤ k) (r : ℕ) (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    ∀ {c : ℝ}, 0 < c →
      |∫ x, arcLineDyadicTowerDeriv k r ν x * Real.sin (c * x)| ≤
        2 ^ r * (8 * Real.sqrt (Real.pi / 2) * ν.real univ) * Real.sqrt c := by
  induction r with
  | zero =>
    intro c hc
    simpa [arcLineDyadicTowerDeriv] using
      abs_integral_arcLineAtomicDeriv_mul_sin_le_sqrt (Real.log k) ν hc
  | succ r ih =>
    intro c hc
    have hstep := abs_integral_hyperbolicFilterDeriv_mul_sin_le_sqrt
      (one_le_pow_two_pow hk r) (integrable_arcLineDyadicTowerDeriv hk r ν)
      (fun _ hω => ih hω) hc
    calc |∫ x, arcLineDyadicTowerDeriv k (r + 1) ν x * Real.sin (c * x)|
        ≤ (2 * (2 ^ r * (8 * Real.sqrt (Real.pi / 2) * ν.real univ))) * Real.sqrt c := hstep
      _ = 2 ^ (r + 1) * (8 * Real.sqrt (Real.pi / 2) * ν.real univ) * Real.sqrt c := by
          rw [pow_succ']; ring

/-! ### Exact one-step reduction on the `k^{2^{r+1}}`-sublattice directly to `arcFreq j` -/

/-- **One-step exact reduction on the `k^{2^{r+1}}`-sublattice:**
Because `m_r² = (k^{2^r})² = k^{2^{r+1}}` matches the blind sublattice modulus of level `r`,
the sine moment of level `r + 1` (`arcLineDyadicTowerDeriv k (r + 1) ν`) along the
`k^{2^{r+1}}`-sublattice `arcFreq (k^{2^{r+1}}(j+1) − 1)` collapses in a **single step** to the
unscaled integer frequency `arcFreq j` of level `r`. -/
theorem integral_arcLineDyadicTowerDeriv_succ_mul_sin_sublattice
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (r j : ℕ) :
    ∫ x, arcLineDyadicTowerDeriv k (r + 1) ν x *
        Real.sin (arcFreq (k ^ (2 ^ (r + 1)) * (j + 1) - 1) * x) =
      -(((k ^ (2 ^ r) : ℕ) : ℝ) / (2 * Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))))) *
        ∫ t, arcLineDyadicTowerDeriv k r ν t * Real.sin (arcFreq j * t) := by
  have heq : k ^ (2 ^ (r + 1)) = (k ^ (2 ^ r)) ^ 2 * 1 := by
    rw [mul_one, pow_two_pow_sq]
  have hj : 1 * (j + 1) - 1 = j := by omega
  change ∫ x, hyperbolicFilterDeriv (k ^ (2 ^ r)) (arcLineDyadicTowerDeriv k r ν) x *
    Real.sin (arcFreq (k ^ (2 ^ (r + 1)) * (j + 1) - 1) * x) = _
  rw [heq]
  have h := integral_hyperbolicFilterDeriv_mul_sin_cascade
    (one_le_pow_two_pow hk r) le_rfl (integrable_arcLineDyadicTowerDeriv hk r ν)
    (fun m => by
      rw [← heq]
      exact integral_arcLineDyadicTowerDeriv_mul_sin_sublattice_eq_zero hblind hk r m) j
  rwa [hj] at h

/-- **Scale-uniform bound on the `k^{2^{r+1}}`-sublattice at dyadic level `r + 1`:**
Even though `arcFreq (k^{2^{r+1}}(j+1) − 1)` grows doubly-exponentially in `r` and polynomially
in `k`, the `1 / (2 cosh(log(k^{2^r})))` cancellation absorbs the `k^{2^r}` factor completely,
bounding the `k^{2^{r+1}}`-sublattice moment of level `r + 1` by
`2^r · (8 √(π/2) · ν.real univ) · √(arcFreq j)` (completely independent of `k`). -/
theorem abs_integral_arcLineDyadicTowerDeriv_succ_mul_sin_sublattice_le
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (r j : ℕ) :
    |∫ x, arcLineDyadicTowerDeriv k (r + 1) ν x *
        Real.sin (arcFreq (k ^ (2 ^ (r + 1)) * (j + 1) - 1) * x)| ≤
      2 ^ r * (8 * Real.sqrt (Real.pi / 2) * ν.real univ) * Real.sqrt (arcFreq j) := by
  rw [integral_arcLineDyadicTowerDeriv_succ_mul_sin_sublattice hblind hk r j,
    abs_mul, abs_neg]
  have hm : 1 ≤ k ^ (2 ^ r) := one_le_pow_two_pow hk r
  have hmpos : (0 : ℝ) < (k ^ (2 ^ r) : ℕ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  have hratio : |((k ^ (2 ^ r) : ℕ) : ℝ) / (2 * Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))))| ≤ 1 := by
    rw [abs_of_pos (by positivity)]
    exact div_two_mul_cosh_log_le_one hm
  calc |((k ^ (2 ^ r) : ℕ) : ℝ) / (2 * Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ))))| *
        |∫ t, arcLineDyadicTowerDeriv k r ν t * Real.sin (arcFreq j * t)|
      ≤ 1 * |∫ t, arcLineDyadicTowerDeriv k r ν t * Real.sin (arcFreq j * t)| :=
        mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
    _ = |∫ t, arcLineDyadicTowerDeriv k r ν t * Real.sin (arcFreq j * t)| := one_mul _
    _ ≤ 2 ^ r * (8 * Real.sqrt (Real.pi / 2) * ν.real univ) * Real.sqrt (arcFreq j) :=
        abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_sqrt hk r ν (arcFreq_pos j)

/-! ### Master unconditional dyadic hyperbolic tower theorem -/

/-- **Master unconditional theorem for the dyadic (exponent-doubling) hyperbolic modular arc tower.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2` and every dyadic depth `r ∈ ℕ`:
1. `arcLineDyadicTowerVector k r ν` is even, strictly self-reciprocal (`f(1/x) = |x| f(x)`),
   zero-mean, and strictly positive definite on the critical line;
2. Its derivative `arcLineDyadicTowerDeriv k r ν` is identically blind on the doubly-exponential
   `k^{2^{r+1}}`-sublattice `arcFreq (k^{2^{r+1}}(j+1) − 1)` and satisfies the `k`-independent
   universal square-root bound `2^r · (8 √(π/2) · ν.real univ) · √c` for all `c > 0`;
3. At level `r + 1`, its sine moments on the `k^{2^{r+1}}`-sublattice collapse in one step to
   the unscaled integer frequency `arcFreq j` of level `r` and are bounded by
   `2^r · (8 √(π/2) · ν.real univ) · √(arcFreq j)` independently of `k`;
4. Its strip Laplace/Mellin transform vanishes to order `O((1/2 − l)^{r+1})` as `l → (1/2)⁻`. -/
theorem exists_dyadic_hyperbolic_tower_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      ∀ k : ℕ, 2 ≤ k → ∀ r : ℕ,
        (∀ x, arcLineDyadicTowerVector k r ν (-x) = arcLineDyadicTowerVector k r ν x) ∧
        (∀ x, x ≠ 0 → arcLineDyadicTowerVector k r ν (1 / x) =
          |x| * arcLineDyadicTowerVector k r ν x) ∧
        ∫ x, arcLineDyadicTowerVector k r ν x = 0 ∧
        (∀ j : ℕ, ∫ x, arcLineDyadicTowerDeriv k r ν x *
          Real.sin (arcFreq (k ^ (2 ^ (r + 1)) * (j + 1) - 1) * x) = 0) ∧
        (∀ c : ℝ, 0 < c →
          |∫ x, arcLineDyadicTowerDeriv k r ν x * Real.sin (c * x)| ≤
            2 ^ r * (8 * Real.sqrt (Real.pi / 2) * ν.real univ) * Real.sqrt c) ∧
        (∀ j : ℕ,
          |∫ x, arcLineDyadicTowerDeriv k (r + 1) ν x *
              Real.sin (arcFreq (k ^ (2 ^ (r + 1)) * (j + 1) - 1) * x)| ≤
            2 ^ r * (8 * Real.sqrt (Real.pi / 2) * ν.real univ) * Real.sqrt (arcFreq j)) ∧
        (∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcLineDyadicTowerProfile k r ν v) ∧
        Tendsto (fun l : ℝ =>
          (∫ v, Real.exp (l * v) * arcLineDyadicTowerProfile k r ν v) / (1 / 2 - l) ^ r)
          (𝓝[<] (1 / 2)) (𝓝 0) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym, fun k hk r => ?_⟩
  have hk1 : 1 ≤ k := by omega
  exact ⟨arcLineDyadicTowerVector_neg_of_map_arcNeg k r hsym,
    arcLineDyadicTowerVector_inv hk1 r ν,
    integral_arcLineDyadicTowerVector_eq_zero hk1 r hsym,
    integral_arcLineDyadicTowerDeriv_mul_sin_sublattice_eq_zero hblind hk1 r,
    fun c hc => abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_sqrt hk1 r ν hc,
    abs_integral_arcLineDyadicTowerDeriv_succ_mul_sin_sublattice_le hblind hk1 r,
    integral_cos_mul_arcLineDyadicTowerProfile_pos hk r ν hpd,
    tendsto_div_pow_integral_exp_mul_arcLineDyadicTowerProfile_nhdsWithin hk1 r hsym⟩

end

end RHTower
