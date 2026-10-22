import GaloisForLFunctions.RHTower.PMPowerDampedMobiusDivisorHaar

/-!
# Positive divisor-weighted Haar prefixes of the power-damped Möbius source

Write `a_ε(n) = ∑_{d|n} μ(d) d^(−ε)` (nonnegative for `ε ≥ 0`), `A_ε(x) = ∑_{n≤x} a_ε(n)`, and
`h` for the dyadic Haar function supported on `(0,1]`. The prefix
`P_N(t) = ∑_{n≤N} a_ε(n) h(n t)` (`pmPowerDampedPositiveHaarPrefix`) equals
`A_ε(min(N,1/t)) − 2 A_ε(min(N,1/(2t)))`, coincides with the power-damped Möbius Fermi source
once `N ≥ 1/t`, is in `L²(0,∞)` with integral zero, and is constant `−A_ε(N)` on
`(0, 1/(2N)]`. Rescaling `u = (N+1)t` and dividing by `N+1`, the prefixes converge pointwise to
`(1/ζ(1+ε))` times the boundary profile `min(1,1/u) − 2 min(1,1/(2u))`, with the uniform
majorant `3 min(1,1/u)`.

## Main results

- `pmPowerDampedPositiveHaarPrefix_eq_clipped_counts`: `P_N(t) = A_ε(min(N,1/t)) − 2 A_ε(min(N,1/(2t)))` for `t > 0`.
- `pmPowerDampedPositiveHaarPrefix_eq_source`, `tendsto_pmPowerDampedPositiveHaarPrefix`: `P_N(t)` equals the Fermi source for `N ≥ 1/t`, hence converges to it pointwise.
- `tendsto_pmPowerDampedRescaledHaarPrefix`: for `ε > 0`, `u > 0`, `P_{N+1}(u/(N+1))/(N+1) → profile(u)/ζ(1+ε)`.
- `norm_pmPowerDampedRescaledHaarPrefix_le`: for `ε ≥ 0`, the rescaled prefix is bounded by `3 min(1,1/u)`.
- `pmPowerDampedPositiveHaarPrefix_plateau`: `P_N(t) = −A_ε(N)` for `0 < t ≤ 1/(2N)`.
- `pmPowerDampedPositiveHaarPrefix_energy_lower`: `|A_ε(N)|²/(2N) ≤ ∫₀^∞ |P_N|²`.
- `pmPowerDampedPositiveHaarPrefix_integral`: `∫₀^∞ P_N = 0`.

## Hypotheses

All results are unconditional. The damping enters only through `0 ≤ ε` (positivity and the
bound `A_ε(x) ≤ x`) or `0 < ε` (so that `ζ(1+ε) ≠ 0` and the mean value `A_ε(x)/x → 1/ζ(1+ε)` holds).
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
noncomputable section
namespace RHTower

/-- The divisor-weighted Haar prefix `P_N(t) = ∑_{n≤N} a_ε(n) h(n t)` with
`a_ε(n) = ∑_{d|n} μ(d) d^(−ε)`. -/
def pmPowerDampedPositiveHaarPrefix (ε : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (pmPowerDampedDivisorCoeff ε n : ℂ) * pmSupportedDyadicHaar ((n : ℝ) * t)

theorem measurable_pmPowerDampedPositiveHaarPrefix (ε : ℝ) (N : ℕ) :
    Measurable (pmPowerDampedPositiveHaarPrefix ε N) := by
  unfold pmPowerDampedPositiveHaarPrefix
  have hh := measurable_pmSupportedDyadicHaar
  fun_prop

/-- Each prefix `P_N` lies in `L²(0,∞)`. -/
theorem memLp_pmPowerDampedPositiveHaarPrefix (ε : ℝ) (N : ℕ) :
    MemLp (pmPowerDampedPositiveHaarPrefix ε N) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  unfold pmPowerDampedPositiveHaarPrefix
  apply memLp_finsetSum
  intro n hn
  exact (memLp_pmSupportedDyadicHaar_dilation
    (by exact_mod_cast (Finset.mem_Icc.mp hn).1)).const_mul _

theorem pm_floor_min_nat (N : ℕ) (x : ℝ) :
    ⌊min (N : ℝ) x⌋₊ = min N ⌊x⌋₊ := by
  rcases le_total (N : ℝ) x with h | h
  · rw [min_eq_left h, Nat.floor_natCast,
      min_eq_left (by simpa only [Nat.floor_natCast] using Nat.floor_mono h)]
  · rw [min_eq_right h,
      min_eq_right (by simpa only [Nat.floor_natCast] using Nat.floor_mono h)]

/-- For `t > 0`, `P_N(t) = A_ε(min(N,1/t)) − 2 A_ε(min(N,1/(2t)))`: the prefix is the Fermi
divisor-count difference with both counts clipped at `N`. -/
theorem pmPowerDampedPositiveHaarPrefix_eq_clipped_counts (ε : ℝ) (N : ℕ)
    {t : ℝ} (ht : 0 < t) :
    pmPowerDampedPositiveHaarPrefix ε N t =
      (pmPowerDampedDivisorSum ε (min (N : ℝ) (1 / t)) : ℂ) -
        2 * (pmPowerDampedDivisorSum ε (min (N : ℝ) (1 / (2 * t))) : ℂ) := by
  classical
  have hc (y : ℝ) (hy : 0 ≤ y) :
      (∑ n ∈ Finset.Icc 1 N, (pmPowerDampedDivisorCoeff ε n : ℂ) *
        (if (n : ℝ) ≤ y then 1 else 0)) =
          (pmPowerDampedDivisorSum ε (min (N : ℝ) y) : ℂ) := by
    have hfilter : (Finset.Icc 1 N).filter (fun n => n ≤ ⌊y⌋₊) =
        Finset.Icc 1 (min N ⌊y⌋₊) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
      omega
    simp only [← Nat.le_floor_iff hy, mul_ite, mul_one, mul_zero, ← Finset.sum_filter,
      hfilter, pmPowerDampedDivisorSum, pm_floor_min_nat, Complex.ofReal_sum]
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (pmPowerDampedDivisorCoeff ε n : ℂ) * pmSupportedDyadicHaar ((n : ℝ) * t) =
        (pmPowerDampedDivisorCoeff ε n : ℂ) * (if (n : ℝ) ≤ 1 / t then 1 else 0) -
        2 * ((pmPowerDampedDivisorCoeff ε n : ℂ) *
          (if (n : ℝ) ≤ 1 / (2 * t) then 1 else 0)) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hh : (n : ℝ) * t ≤ 1 / 2 ↔ (n : ℝ) ≤ 1 / (2 * t) := by
      rw [le_div_iff₀ (by positivity : 0 < 2 * t)]
      constructor <;> intro h <;> nlinarith
    have hfull : (n : ℝ) * t ≤ 1 ↔ (n : ℝ) ≤ 1 / t := (le_div_iff₀ ht).symm
    rw [pmSupportedDyadicHaar_eq_cutoffs (mul_pos hn0 ht)]
    simp only [hfull, hh]
    ring
  rw [pmPowerDampedPositiveHaarPrefix, Finset.sum_congr rfl hterm,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hc _ (by positivity), hc _ (by positivity)]

/-- For `ε ≥ 0`, the summatory function `A_ε(x)` is nonnegative. -/
theorem pmPowerDampedDivisorSum_nonneg {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ pmPowerDampedDivisorSum ε x :=
  Finset.sum_nonneg (fun n _ => pmPowerDampedDivisorCoeff_nonneg hε n)

/-- For `ε ≥ 0` and `x ≥ 0`, `A_ε(x) ≤ x`, since `0 ≤ a_ε(n) ≤ 1`. -/
theorem pmPowerDampedDivisorSum_le {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    pmPowerDampedDivisorSum ε x ≤ x := by
  calc
    pmPowerDampedDivisorSum ε x ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) :=
      Finset.sum_le_sum (fun n _ => pmPowerDampedDivisorCoeff_le_one hε n)
    _ = (⌊x⌋₊ : ℝ) := by simp
    _ ≤ x := Nat.floor_le hx

/-- For `ε > 0`, the density `1/ζ(1+ε)` is nonzero. -/
theorem pmPowerDampedDivisorDensity_ne_zero {ε : ℝ} (hε : 0 < ε) :
    pmPowerDampedDivisorDensity ε ≠ 0 := by
  unfold pmPowerDampedDivisorDensity
  exact one_div_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by simpa using hε))

/-- For `ε > 0` and `a > 0`, `A_ε((N+1)a)/(N+1) → a/ζ(1+ε)` as `N → ∞`. -/
theorem tendsto_pmPowerDampedDivisorSum_scaled {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    Tendsto (fun N : ℕ => (pmPowerDampedDivisorSum ε (((N : ℝ) + 1) * a) : ℂ) /
      ((N : ℂ) + 1)) atTop (𝓝 (pmPowerDampedDivisorDensity ε * (a : ℂ))) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h := ((tendsto_pmPowerDampedDivisorSum_div hε).comp
    (hN.atTop_mul_const ha)).mul_const (a : ℂ)
  convert h using 1
  funext N
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hNC : (N : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < (N : ℝ) + 1 by positivity))
  dsimp only [Function.comp_def]
  push_cast
  field_simp

/-- The boundary profile `min(1,1/u) − 2 min(1,1/(2u))`, the large-`N` shape of the rescaled
Haar prefix. -/
def pmPositiveHaarBoundaryProfile (u : ℝ) : ℝ :=
  min 1 (1 / u) - 2 * min 1 (1 / (2 * u))

/-- The rescaled prefix `P_{N+1}(u/(N+1))/(N+1)`. -/
def pmPowerDampedRescaledHaarPrefix (ε : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  pmPowerDampedPositiveHaarPrefix ε (N + 1) (u / ((N : ℝ) + 1)) / ((N : ℂ) + 1)

/-- For `u > 0`, the rescaled prefix equals
`A_ε((N+1) min(1,1/u))/(N+1) − 2 A_ε((N+1) min(1,1/(2u)))/(N+1)`. -/
theorem pmPowerDampedRescaledHaarPrefix_eq_counts (ε : ℝ) (N : ℕ)
    {u : ℝ} (hu : 0 < u) :
    pmPowerDampedRescaledHaarPrefix ε N u =
      (pmPowerDampedDivisorSum ε (((N : ℝ) + 1) * min 1 (1 / u)) : ℂ) / ((N : ℂ) + 1) -
        2 * ((pmPowerDampedDivisorSum ε (((N : ℝ) + 1) * min 1 (1 / (2 * u))) : ℂ) /
          ((N : ℂ) + 1)) := by
  have hNp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : 1 / (u / ((N : ℝ) + 1)) = ((N : ℝ) + 1) / u := by field_simp
  have h2 : 1 / (2 * (u / ((N : ℝ) + 1))) = ((N : ℝ) + 1) / (2 * u) := by field_simp
  rw [pmPowerDampedRescaledHaarPrefix,
    pmPowerDampedPositiveHaarPrefix_eq_clipped_counts ε (N + 1) (div_pos hu hNp), h1, h2]
  simp only [Nat.cast_add, Nat.cast_one, mul_min_of_nonneg _ _ hNp.le, mul_one, mul_one_div]
  ring

/-- For `ε > 0` and `u > 0`, the rescaled prefix converges to
`pmPositiveHaarBoundaryProfile u / ζ(1+ε)` as `N → ∞`. -/
theorem tendsto_pmPowerDampedRescaledHaarPrefix {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    Tendsto (fun N : ℕ => pmPowerDampedRescaledHaarPrefix ε N u) atTop
      (𝓝 (pmPowerDampedDivisorDensity ε * (pmPositiveHaarBoundaryProfile u : ℂ))) := by
  have ha : 0 < min (1 : ℝ) (1 / u) := lt_min one_pos (one_div_pos.mpr hu)
  have hb : 0 < min (1 : ℝ) (1 / (2 * u)) := lt_min one_pos (by positivity)
  have h := (tendsto_pmPowerDampedDivisorSum_scaled hε ha).sub
    ((tendsto_pmPowerDampedDivisorSum_scaled hε hb).const_mul 2)
  have hv : pmPowerDampedDivisorDensity ε * (min 1 (1 / u) : ℝ) -
      2 * (pmPowerDampedDivisorDensity ε * (min 1 (1 / (2 * u)) : ℝ)) =
        pmPowerDampedDivisorDensity ε * (pmPositiveHaarBoundaryProfile u : ℂ) := by
    simp only [pmPositiveHaarBoundaryProfile, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring
  simpa only [pmPowerDampedRescaledHaarPrefix_eq_counts ε _ hu, hv] using h

/-- For `ε ≥ 0` and `a ≥ 0`, `|A_ε((N+1)a)/(N+1)| ≤ a`. -/
theorem norm_pmPowerDampedDivisorSum_scaled_le {ε a : ℝ} (hε : 0 ≤ ε) (ha : 0 ≤ a)
    (N : ℕ) :
    ‖(pmPowerDampedDivisorSum ε (((N : ℝ) + 1) * a) : ℂ) / ((N : ℂ) + 1)‖ ≤ a := by
  have hNp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hcast : (N : ℂ) + 1 = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast]
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pmPowerDampedDivisorSum_nonneg hε _), abs_of_pos hNp, div_le_iff₀ hNp]
  simpa only [mul_comm] using pmPowerDampedDivisorSum_le hε (mul_nonneg hNp.le ha)

/-- For `ε ≥ 0` and `u > 0`, the rescaled prefix is bounded by `3 min(1,1/u)` uniformly in `N`. -/
theorem norm_pmPowerDampedRescaledHaarPrefix_le {ε u : ℝ} (hε : 0 ≤ ε) (hu : 0 < u)
    (N : ℕ) :
    ‖pmPowerDampedRescaledHaarPrefix ε N u‖ ≤ 3 * min 1 (1 / u) := by
  rw [pmPowerDampedRescaledHaarPrefix_eq_counts ε N hu]
  have ha : 0 ≤ min (1 : ℝ) (1 / u) := by positivity
  have hb : 0 ≤ min (1 : ℝ) (1 / (2 * u)) := by positivity
  have hba : min (1 : ℝ) (1 / (2 * u)) ≤ min 1 (1 / u) :=
    min_le_min_left 1 (one_div_le_one_div_of_le hu (by linarith))
  calc
    _ ≤ ‖(pmPowerDampedDivisorSum ε (((N : ℝ) + 1) * min 1 (1 / u)) : ℂ) / ((N : ℂ) + 1)‖ +
        2 * ‖(pmPowerDampedDivisorSum ε (((N : ℝ) + 1) * min 1 (1 / (2 * u))) : ℂ) /
          ((N : ℂ) + 1)‖ := by
      have hh := norm_sub_le
        ((pmPowerDampedDivisorSum ε (((N : ℝ) + 1) * min 1 (1 / u)) : ℂ) / ((N : ℂ) + 1))
        (2 * ((pmPowerDampedDivisorSum ε (((N : ℝ) + 1) * min 1 (1 / (2 * u))) : ℂ) /
          ((N : ℂ) + 1)))
      simpa only [norm_mul, norm_ofNat] using hh
    _ ≤ min 1 (1 / u) + 2 * min 1 (1 / (2 * u)) :=
      add_le_add (norm_pmPowerDampedDivisorSum_scaled_le hε ha N)
        (mul_le_mul_of_nonneg_left (norm_pmPowerDampedDivisorSum_scaled_le hε hb N) (by norm_num))
    _ ≤ 3 * min 1 (1 / u) := by linarith

/-- For `t > 0` and `1/t ≤ N`, the prefix `P_N(t)` equals the power-damped Möbius Fermi source. -/
theorem pmPowerDampedPositiveHaarPrefix_eq_source (ε : ℝ) (N : ℕ)
    {t : ℝ} (ht : 0 < t) (hN : 1 / t ≤ (N : ℝ)) :
    pmPowerDampedPositiveHaarPrefix ε N t = pmPowerDampedFermiSource ε t := by
  have hhalf : 1 / (2 * t) ≤ (N : ℝ) :=
    (one_div_le_one_div_of_le ht (by linarith)).trans hN
  rw [pmPowerDampedPositiveHaarPrefix_eq_clipped_counts ε N ht,
    min_eq_right hN, min_eq_right hhalf, pmPowerDampedFermiSource_eq_divisor_counts ε ht]

/-- At each `t > 0`, `P_N(t)` converges to the power-damped Fermi source (it is eventually equal). -/
theorem tendsto_pmPowerDampedPositiveHaarPrefix (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => pmPowerDampedPositiveHaarPrefix ε N t) atTop
      (𝓝 (pmPowerDampedFermiSource ε t)) := by
  have hn : ∀ᶠ N : ℕ in atTop, 1 / t ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 / t))
  apply tendsto_const_nhds.congr'
  filter_upwards [hn] with N hN
  exact (pmPowerDampedPositiveHaarPrefix_eq_source ε N ht hN).symm

/-- For `N ≥ 1` and `0 < t ≤ 1/(2N)`, the prefix is the constant `−A_ε(N)`. -/
theorem pmPowerDampedPositiveHaarPrefix_plateau (ε : ℝ) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) (1 / (2 * (N : ℝ)))) :
    pmPowerDampedPositiveHaarPrefix ε N t = -(pmPowerDampedDivisorSum ε (N : ℝ) : ℂ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have htp : 0 < t := ht.1
  have hNt : t * (2 * (N : ℝ)) ≤ 1 := (le_div_iff₀ (by positivity)).mp ht.2
  have hhalf : (N : ℝ) ≤ 1 / (2 * t) := (le_div_iff₀ (by positivity : 0 < 2 * t)).mpr (by nlinarith)
  have hwhole : (N : ℝ) ≤ 1 / t :=
    hhalf.trans (one_div_le_one_div_of_le ht.1 (by linarith [ht.1]))
  rw [pmPowerDampedPositiveHaarPrefix_eq_clipped_counts ε N ht.1,
    min_eq_left hwhole, min_eq_left hhalf]
  ring

/-- For `N ≥ 1`, the plateau gives the energy lower bound `|A_ε(N)|²/(2N) ≤ ∫₀^∞ |P_N(t)|² dt`. -/
theorem pmPowerDampedPositiveHaarPrefix_energy_lower (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ‖(pmPowerDampedDivisorSum ε (N : ℝ) : ℂ)‖ ^ 2 / (2 * (N : ℝ)) ≤
      ∫ t in Ioi (0 : ℝ), ‖pmPowerDampedPositiveHaarPrefix ε N t‖ ^ 2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : IntegrableOn (fun t => ‖pmPowerDampedPositiveHaarPrefix ε N t‖ ^ 2) (Ioi (0 : ℝ)) :=
    (memLp_pmPowerDampedPositiveHaarPrefix ε N).norm.integrable_sq
  have hlocal : (∫ t in Ioc (0 : ℝ) (1 / (2 * (N : ℝ))),
      ‖pmPowerDampedPositiveHaarPrefix ε N t‖ ^ 2) =
        ‖(pmPowerDampedDivisorSum ε (N : ℝ) : ℂ)‖ ^ 2 / (2 * (N : ℝ)) := by
    have he (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) (1 / (2 * (N : ℝ)))) :
        ‖pmPowerDampedPositiveHaarPrefix ε N t‖ ^ 2 =
          ‖(pmPowerDampedDivisorSum ε (N : ℝ) : ℂ)‖ ^ 2 := by
      rw [pmPowerDampedPositiveHaarPrefix_plateau ε hN ht, norm_neg]
    rw [setIntegral_congr_fun measurableSet_Ioc he,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 1 / (2 * (N : ℝ))),
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hh := setIntegral_mono_set (s := Ioc (0 : ℝ) (1 / (2 * (N : ℝ)))) hint
    (Eventually.of_forall fun t => sq_nonneg ‖pmPowerDampedPositiveHaarPrefix ε N t‖)
    (Eventually.of_forall fun t (ht : t ∈ Ioc (0 : ℝ) (1 / (2 * (N : ℝ)))) => ht.1)
  rw [hlocal] at hh
  exact hh

theorem integrable_pmPowerDampedPositiveHaarPrefix (ε : ℝ) (N : ℕ) :
    IntegrableOn (pmPowerDampedPositiveHaarPrefix ε N) (Ioi (0 : ℝ)) := by
  apply integrable_finsetSum
  intro n hn
  exact (integrable_pmSupportedDyadicHaar_dilation
    (by exact_mod_cast (Finset.mem_Icc.mp hn).1)).const_mul _

/-- Each prefix has integral zero over `(0,∞)`. -/
theorem pmPowerDampedPositiveHaarPrefix_integral (ε : ℝ) (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), pmPowerDampedPositiveHaarPrefix ε N t) = 0 := by
  unfold pmPowerDampedPositiveHaarPrefix
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro n hn
    rw [integral_const_mul, pmSupportedDyadicHaar_dilation_integral
      (by exact_mod_cast (Finset.mem_Icc.mp hn).1), mul_zero]
  · intro n hn
    exact (integrable_pmSupportedDyadicHaar_dilation
      (by exact_mod_cast (Finset.mem_Icc.mp hn).1)).const_mul _

end RHTower
