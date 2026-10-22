import GaloisForLFunctions.RHTower.PMPowerDampedMobiusSecondMoment
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPositiveHaarPrefix
import GaloisForLFunctions.RHTower.SummableDivisorHarmonicMean
import GaloisForLFunctions.HTGeometry.EtemadiWeightedAverage

/-!
# Diagonal growth and forced off-diagonal cancellation in the discrete divisor energy

The discrete divisor energy `E_ε(N) = ∑_{j,k ≤ N} c̃_j c̃_k (1/max(j,k) - 1/(N+1))` of the
centered coefficients `c̃_n = c_ε(n) - Re(1/ζ(1+ε))` splits into a diagonal part `D_ε(N)` and an
off-diagonal part `O_ε(N)`. Comparing the Euler products `Re(1/ζ(1+ε)) = ∏_p (1 - p^{-ε}/p)` and
the second-moment density, the variance `σ²_ε` of the coefficients is strictly positive for
`ε > 0`. A weighted-average (Etemadi) argument converts the Cesàro mean of `c̃_n²` into the
logarithmic mean, giving `D_ε(N)/log N → σ²_ε`; in particular the diagonal is unbounded. If the
Fermi source `F_ε` is square integrable, `E_ε(N)` is bounded, so the off-diagonal part must
cancel the diagonal exactly at logarithmic scale: `O_ε(N)/log N → -σ²_ε`.

## Main results

- `pmPowerDampedDivisorDensity_hasProd_real`: `Re(1/ζ(1+ε)) = ∏_p (1 - p^{-ε}/p)` for `ε > 0`.
- `pmPowerDampedDivisorVariance_pos`: `σ²_ε > 0` for `ε > 0`.
- `pm_tendsto_harmonic_average_of_mean`: Cesàro mean `→ L` implies logarithmic mean `→ L`.
- `tendsto_pmPowerDampedDivisorCovarianceDiagonal_div_log`: `D_ε(N)/log N → σ²_ε` for `ε > 0`.
- `not_bounded_pmPowerDampedDivisorCovarianceDiagonal`: `D_ε(N)` is not bounded above for `ε > 0`.
- `tendsto_pmPowerDampedDivisorCovarianceOffDiagonal_div_log`: if `F_ε ∈ L²(0, ∞)`, then
  `O_ε(N)/log N → -σ²_ε`.
- `tendsto_pmPowerDampedDivisorCovarianceOffDiagonal_div_log_of_half_le`: unconditionally
  `O_ε(N)/log N → -σ²_ε` for `ε ≥ 1/2`.

## Hypotheses

The positivity, diagonal asymptotics and the `ε ≥ 1/2` cancellation are unconditional, given the
range `0 < ε` or `1/2 ≤ ε`. `tendsto_pmPowerDampedDivisorDiscreteEnergy_div_log` and
`tendsto_pmPowerDampedDivisorCovarianceOffDiagonal_div_log` take as hypothesis that
`F_ε ∈ L²(0, ∞)` (square integrability of the power-damped Möbius Fermi source); they are
conditional on that input for `0 < ε < 1/2`.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
noncomputable section
namespace RHTower

/-- Strict comparison of infinite products: if `∏ f = a > 0`, `∏ g = b`, `0 ≤ f ≤ g` pointwise
and `f i < g i` at one index, then `a < b`. -/
theorem pm_hasProd_lt_real {ι : Type*} {f g : ι → ℝ} {a b : ℝ}
    (hf : HasProd f a) (hg : HasProd g b) (hf0 : ∀ i, 0 ≤ f i)
    (hfg : ∀ i, f i ≤ g i) (ha : 0 < a) {i : ι} (hi : f i < g i) : a < b := by
  classical
  have hf' : Tendsto (fun s : Finset ι => ∏ j ∈ s, f j) atTop (𝓝 a) := hf
  have hg' : Tendsto (fun s : Finset ι => ∏ j ∈ s, g j) atTop (𝓝 b) := hg
  have hbound : ∀ᶠ s : Finset ι in atTop,
      g i * (∏ j ∈ s, f j) ≤ f i * (∏ j ∈ s, g j) := by
    refine eventually_atTop.2 ⟨{i}, fun s hs => ?_⟩
    have his : i ∈ s := hs (Finset.mem_singleton_self i)
    rw [← Finset.mul_prod_erase s f his, ← Finset.mul_prod_erase s g his]
    have hp : (∏ j ∈ s.erase i, f j) ≤ ∏ j ∈ s.erase i, g j :=
      Finset.prod_le_prod (fun j hj => hf0 j) (fun j hj => hfg j)
    have h := mul_le_mul_of_nonneg_left hp (mul_nonneg (hf0 i) ((hf0 i).trans (hfg i)))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hlim : g i * a ≤ f i * b :=
    le_of_tendsto_of_tendsto (hf'.const_mul (g i)) (hg'.const_mul (f i)) hbound
  by_contra hn
  have hba : b ≤ a := le_of_not_gt hn
  have hmul := mul_le_mul_of_nonneg_left hba (hf0 i)
  have hgap := mul_pos (sub_pos.mpr hi) ha
  nlinarith

/-- Euler product of the mean density: for `ε > 0`, `Re(1/ζ(1+ε)) = ∏_p (1 - p^{-ε}/p)`. -/
theorem pmPowerDampedDivisorDensity_hasProd_real {ε : ℝ} (hε : 0 < ε) :
    HasProd (fun p : Nat.Primes => 1 - (p : ℝ)^(-ε)/(p : ℝ))
      (pmPowerDampedDivisorDensity ε).re := by
  let a := DampedMobius.dampedMobius (fun p : ℕ => (p : ℝ)^(-ε))
  have hm := DampedMobius.isMultiplicative_dampedMobius (fun p : ℕ => (p : ℝ)^(-ε))
  have hs : Summable (fun n : ℕ => a n / (n : ℝ)) := by
    apply (RCLike.summable_ofReal (𝕜 := ℂ)).mp
    change Summable (fun n : ℕ => ((a n / (n : ℝ) : ℝ) : ℂ))
    simpa only [a, pm_dampedMobius_rpow, pmPowerDampedMobiusCoeff,
      Complex.ofReal_div, Complex.ofReal_natCast] using
        summable_pmPowerDampedDivisorDensity_terms hε
  have he (n : ℕ) : (∑ d ∈ n.divisors, a d) = pmPowerDampedDivisorCoeff ε n := by
    rw [pmPowerDampedDivisorCoeff_eq_divisorSum]
    simpa only [coe_mul_zeta_apply, a] using congrArg (fun f : ArithmeticFunction ℝ => f n)
      (DampedMobius.dampedMobius_mul_zeta (fun p : ℕ => (p : ℝ)^(-ε)))
  have hav : Tendsto (fun x : ℝ => pmPowerDampedDivisorSum ε x / x) atTop
      (𝓝 (∑' n : ℕ, a n / (n : ℝ))) := by
    simpa only [he, pmPowerDampedDivisorSum] using pm_tendsto_divisor_average hs
  have hv := tendsto_nhds_unique hav (tendsto_pmPowerDampedDivisorSum_div_real hε)
  have h1 : a 1 / ((1 : ℕ) : ℝ) = 1 := by simpa [a] using hm.map_one
  have hmul {m n : ℕ} (h : m.Coprime n) :
      a (m*n) / ((m*n : ℕ) : ℝ) = (a m / (m : ℝ)) * (a n / (n : ℝ)) := by
    rw [show a (m*n) = a m * a n from hm.map_mul_of_coprime h, Nat.cast_mul]
    ring
  have hp := EulerProduct.eulerProduct_hasProd h1 (fun {_ _} h => hmul h) hs.norm (by simp)
  rw [hv] at hp
  apply hp.congr_fun
  intro p
  rw [tsum_eq_sum (s := {0, 1}) (fun k hk => ?_)]
  · simp [a, DampedMobius.dampedMobius_apply_prime_pow, p.property, sub_eq_add_neg, neg_div]
  · have hk0 : k ≠ 0 := fun h => hk (by simp [h])
    have hk1 : k ≠ 1 := fun h => hk (by simp [h])
    simp [a, DampedMobius.dampedMobius_apply_prime_pow, p.property, hk0, hk1]

/-- Local Euler-factor gap: with `w(p) = 2p^{-ε} - p^{-2ε}`,
`(1 - w(p)/p) - (1 - p^{-ε}/p)² = p^{-2ε} (p - 1)/p²`. -/
theorem pmPowerDampedSecondFactor_gap (ε : ℝ) {p : ℕ} (hp : 0 < p) :
    (1 - pmPowerDampedSecondWeight ε p / (p : ℝ)) -
      (1 - (p : ℝ)^(-ε)/(p : ℝ))^2 =
        ((p : ℝ)^(-ε))^2 * ((p : ℝ)-1)/(p : ℝ)^2 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  dsimp only [pmPowerDampedSecondWeight]
  field_simp [hpR]
  ring

/-- For `ε > 0` the coefficient variance `σ²_ε` (second-moment density minus squared mean
density) is strictly positive. -/
theorem pmPowerDampedDivisorVariance_pos {ε : ℝ} (hε : 0 < ε) :
    0 < pmPowerDampedDivisorVariance ε := by
  have hlocal (p : Nat.Primes) :
      (1 - (p : ℝ)^(-ε)/(p : ℝ))^2 <
        1 - pmPowerDampedSecondWeight ε p / (p : ℝ) := by
    apply sub_pos.mp
    rw [pmPowerDampedSecondFactor_gap ε p.property.pos]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
    exact div_pos (mul_pos (sq_pos_of_pos (Real.rpow_pos_of_pos (by linarith) _))
      (sub_pos.mpr hp1)) (sq_pos_of_pos (by linarith))
  have hα : (pmPowerDampedDivisorDensity ε).re ≠ 0 := by
    intro hz
    apply pmPowerDampedDivisorDensity_ne_zero hε
    rw [pmPowerDampedDivisorDensity_eq_ofReal_re hε, hz]
    simp
  have h := pm_hasProd_lt_real ((pmPowerDampedDivisorDensity_hasProd_real hε).pow 2)
    (pmPowerDampedSecondDensity_hasProd hε) (fun p => sq_nonneg _)
    (fun p => (hlocal p).le) (sq_pos_of_ne_zero hα)
    (hlocal ⟨2, Nat.prime_two⟩)
  exact sub_pos.mpr h

/-- Cesàro to logarithmic means: if `(1/N) ∑_{n ≤ N} a_n → L`, then
`(1/log N) ∑_{n ≤ N} a_n/n → L`. -/
theorem pm_tendsto_harmonic_average_of_mean {a : ℕ → ℝ} {L : ℝ}
    (ha : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, a n)/(N : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, a n/(n : ℝ))/Real.log N)
      atTop (𝓝 L) := by
  let w : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hw (n : ℕ) : 0 < w n := by dsimp only [w]; positivity
  have hanti : Antitone w := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (m : ℝ)+1)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hweight (N : ℕ) :
      GaloisForLFunctions.HTGeometry.Etemadi.totalWeight w N = (harmonic N : ℝ) := by
    simp [GaloisForLFunctions.HTGeometry.Etemadi.totalWeight, w, harmonic, one_div]
  have hHinf : Tendsto (fun N : ℕ => (harmonic N : ℝ)) atTop atTop := by
    exact tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall fun N => log_add_one_le_harmonic N)
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)))
  have hW := hHinf.congr (fun N => (hweight N).symm)
  have hendpoint (N : ℕ) : (N : ℝ)*w (N-1) ≤
      1*GaloisForLFunctions.HTGeometry.Etemadi.totalWeight w N := by
    change (N : ℝ)*w (N-1) ≤ 1*(∑ i ∈ Finset.range N, w i)
    rw [one_mul]
    calc
      _ = ∑ i ∈ Finset.range N, w (N-1) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => hanti (by
        have := Finset.mem_range.mp hi
        omega)
  have hx : Tendsto (fun N : ℕ =>
      GaloisForLFunctions.HTGeometry.Etemadi.partialSum (fun i => a (i+1)) N/(N : ℝ))
      atTop (𝓝 L) := by
    simpa only [GaloisForLFunctions.HTGeometry.Etemadi.partialSum,
      RegularizedDivisorHarmonic.sum_Icc_one_eq_sum_range] using ha
  have h := GaloisForLFunctions.HTGeometry.Etemadi.tendsto_weightedAverage_of_antitone
    hw hanti hW hendpoint hx
  have hm : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, a n/(n : ℝ))/(harmonic N : ℝ)) atTop (𝓝 L) := by
    apply h.congr
    intro N
    rw [hweight, RegularizedDivisorHarmonic.sum_Icc_one_eq_sum_range]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [w]
    push_cast
    ring
  have hp := hm.mul GaloisForLFunctions.tendsto_harmonic_div_log
  simpa only [mul_one] using hp.congr' (by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hH : (0 : ℝ) < harmonic N := lt_of_lt_of_le
      (by norm_num : (0 : ℝ) < harmonic 1) (harmonic_cast_mono (by omega : 1 ≤ N))
    have hlog : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
    field_simp)

/-- For `ε > 0`, `(1/N) ∑_{n ≤ N} c̃_ε(n)² → σ²_ε`. -/
theorem tendsto_pmPowerDampedCenteredDivisorCoeff_sq_nat_mean {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, pmPowerDampedCenteredDivisorCoeff ε n ^ 2)/(N : ℝ))
      atTop (𝓝 (pmPowerDampedDivisorVariance ε)) := by
  have h := (tendsto_pmPowerDampedCenteredDivisorCoeff_sq_mean hε).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  simpa only [Function.comp_def, Nat.floor_natCast] using h

/-- For `ε > 0`, `(1/log N) ∑_{n ≤ N} c̃_ε(n)²/n → σ²_ε`. -/
theorem tendsto_pmPowerDampedCenteredDivisorCoeff_sq_harmonic {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, pmPowerDampedCenteredDivisorCoeff ε n ^ 2/(n : ℝ))/Real.log N)
      atTop (𝓝 (pmPowerDampedDivisorVariance ε)) :=
  pm_tendsto_harmonic_average_of_mean (tendsto_pmPowerDampedCenteredDivisorCoeff_sq_nat_mean hε)

/-- Diagonal part `D_ε(N) = ∑_{n ≤ N} c̃_ε(n)² (1/n - 1/(N+1))` of the discrete energy. -/
def pmPowerDampedDivisorCovarianceDiagonal (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, pmPowerDampedCenteredDivisorCoeff ε n ^ 2 *
    (1/(n : ℝ) - 1/((N : ℝ)+1))

/-- Off-diagonal part `O_ε(N) = ∑_{j ≠ k ≤ N} c̃_ε(j) c̃_ε(k) (1/max(j,k) - 1/(N+1))`. -/
def pmPowerDampedDivisorCovarianceOffDiagonal (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ (Finset.Icc 1 N).erase j,
    pmPowerDampedCenteredDivisorCoeff ε j * pmPowerDampedCenteredDivisorCoeff ε k *
      (1/(max j k : ℕ) - 1/((N : ℝ)+1))

/-- The discrete energy splits as `E_ε(N) = D_ε(N) + O_ε(N)`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_split (ε : ℝ) (N : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy ε N = pmPowerDampedDivisorCovarianceDiagonal ε N +
      pmPowerDampedDivisorCovarianceOffDiagonal ε N := by
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_covariance]
  have he (j : ℕ) (hj : j ∈ Finset.Icc 1 N) :
      (∑ k ∈ Finset.Icc 1 N,
        pmPowerDampedCenteredDivisorCoeff ε j * pmPowerDampedCenteredDivisorCoeff ε k *
          (1/(max j k : ℕ) - 1/((N : ℝ)+1))) =
      pmPowerDampedCenteredDivisorCoeff ε j ^ 2 * (1/(j : ℝ)-1/((N : ℝ)+1)) +
        ∑ k ∈ (Finset.Icc 1 N).erase j,
          pmPowerDampedCenteredDivisorCoeff ε j * pmPowerDampedCenteredDivisorCoeff ε k *
            (1/(max j k : ℕ) - 1/((N : ℝ)+1)) := by
    simpa only [max_self, pow_two] using (Finset.add_sum_erase (Finset.Icc 1 N)
      (fun k => pmPowerDampedCenteredDivisorCoeff ε j * pmPowerDampedCenteredDivisorCoeff ε k *
        (1/(max j k : ℕ) - 1/((N : ℝ)+1))) hj).symm
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib]
  rfl

theorem pmPowerDampedDivisorCovarianceDiagonal_eq (ε : ℝ) (N : ℕ) :
    pmPowerDampedDivisorCovarianceDiagonal ε N =
      (∑ n ∈ Finset.Icc 1 N, pmPowerDampedCenteredDivisorCoeff ε n ^ 2/(n : ℝ)) -
        (∑ n ∈ Finset.Icc 1 N, pmPowerDampedCenteredDivisorCoeff ε n ^ 2)/((N : ℝ)+1) := by
  simp only [pmPowerDampedDivisorCovarianceDiagonal, mul_sub, mul_one_div,
    Finset.sum_sub_distrib, Finset.sum_div]

theorem tendsto_pmPowerDampedCenteredDivisorCoeff_sq_shift_mean {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, pmPowerDampedCenteredDivisorCoeff ε n ^ 2)/((N : ℝ)+1))
      atTop (𝓝 (pmPowerDampedDivisorVariance ε)) := by
  have h := (tendsto_pmPowerDampedCenteredDivisorCoeff_sq_nat_mean hε).mul
    (tendsto_natCast_div_add_atTop (1 : ℝ))
  simpa only [mul_one] using h.congr' (by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp)

/-- For `ε > 0` the diagonal grows logarithmically: `D_ε(N)/log N → σ²_ε`. -/
theorem tendsto_pmPowerDampedDivisorCovarianceDiagonal_div_log {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => pmPowerDampedDivisorCovarianceDiagonal ε N/Real.log N)
      atTop (𝓝 (pmPowerDampedDivisorVariance ε)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (tendsto_pmPowerDampedCenteredDivisorCoeff_sq_harmonic hε).sub
    ((tendsto_pmPowerDampedCenteredDivisorCoeff_sq_shift_mean hε).div_atTop hlog)
  simpa only [sub_zero] using h.congr (fun N => by
    rw [pmPowerDampedDivisorCovarianceDiagonal_eq]
    ring)

/-- For `ε > 0` the diagonal part `D_ε(N)` is not bounded above. -/
theorem not_bounded_pmPowerDampedDivisorCovarianceDiagonal {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ B : ℝ, ∀ N : ℕ, pmPowerDampedDivisorCovarianceDiagonal ε N ≤ B := by
  rintro ⟨B, hB⟩
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => B/Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have h := le_of_tendsto_of_tendsto
    (tendsto_pmPowerDampedDivisorCovarianceDiagonal_div_log hε) hlim (by
      filter_upwards [eventually_ge_atTop 2] with N hN
      exact div_le_div_of_nonneg_right (hB N) (Real.log_pos (by exact_mod_cast hN)).le)
  exact (not_le.mpr (pmPowerDampedDivisorVariance_pos hε)) h

/-- Assuming `hf : F_ε ∈ L²(0, ∞)` with `ε > 0`, the discrete energy is bounded, so
`E_ε(N)/log N → 0`. -/
theorem tendsto_pmPowerDampedDivisorDiscreteEnergy_div_log {ε : ℝ} (hε : 0 < ε)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    Tendsto (fun N : ℕ => pmPowerDampedDivisorDiscreteEnergy ε N/Real.log N)
      atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := (pmPowerDampedFermiSource_memLp_iff_discrete_budget hε).mp hf
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => B/Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 2] with N hN
    apply div_nonneg _ (Real.log_pos (by exact_mod_cast hN)).le
    exact Finset.sum_nonneg fun n hn => by
      apply div_nonneg (sq_nonneg _)
      positivity
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact div_le_div_of_nonneg_right (hB N) (Real.log_pos (by exact_mod_cast hN)).le

/-- Forced cancellation: assuming `hf : F_ε ∈ L²(0, ∞)` with `ε > 0`, the off-diagonal part
satisfies `O_ε(N)/log N → -σ²_ε`. -/
theorem tendsto_pmPowerDampedDivisorCovarianceOffDiagonal_div_log {ε : ℝ} (hε : 0 < ε)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    Tendsto (fun N : ℕ => pmPowerDampedDivisorCovarianceOffDiagonal ε N/Real.log N)
      atTop (𝓝 (-pmPowerDampedDivisorVariance ε)) := by
  have h := (tendsto_pmPowerDampedDivisorDiscreteEnergy_div_log hε hf).sub
    (tendsto_pmPowerDampedDivisorCovarianceDiagonal_div_log hε)
  simpa only [zero_sub] using h.congr (fun N => by
    rw [pmPowerDampedDivisorDiscreteEnergy_split]
    ring)

/-- Unconditionally, for `ε ≥ 1/2` the off-diagonal part satisfies `O_ε(N)/log N → -σ²_ε`. -/
theorem tendsto_pmPowerDampedDivisorCovarianceOffDiagonal_div_log_of_half_le
    {ε : ℝ} (hε : (1/2 : ℝ) ≤ ε) :
    Tendsto (fun N : ℕ => pmPowerDampedDivisorCovarianceOffDiagonal ε N/Real.log N)
      atTop (𝓝 (-pmPowerDampedDivisorVariance ε)) :=
  tendsto_pmPowerDampedDivisorCovarianceOffDiagonal_div_log (by linarith)
    (memLp_pmPowerDampedFermiSource_of_half_le hε)

end RHTower
