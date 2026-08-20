import GaloisForLFunctions.RHTower.PrimeEndpointJetTaylor
import GaloisForLFunctions.RHTower.PrimeSuperspaceDecompactification
import Mathlib

/-!
# The symmetric Wick expansion of the prime boundary layer

Applying the endpoint-jet theorem to the two axes of the finite Wick cumulant gives the card's
expansion `(17)`:

* radial axis, test function `2(cosh (c u) - 1)`: the finite radial prime-clock energy at
  boundary-layer scale differs from its Dickman limit by an even jet in `1/log N`;
* vertical axis, test function `2(1 - cos (c u))`: the same for the vertical clock energy.

The leading correction `(18)` is the second higher-order Mertens constant at scale `(log N)^2`,
every test function flat at the collapsed endpoint has defect beyond all algebraic orders `(19)`,
and every finite truncation is zero-free after exponentiation `(20)`.

The two derivative towers are built here: `coshTestTower` and `waveTower`, the latter written as a
single phase-shifted cosine so that one derivative computation covers all orders.
-/

set_option maxHeartbeats 1600000

open Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-! ## The hyperbolic and trigonometric boundary test towers -/

/-- The derivative tower of `u ↦ 2 (cosh (c u) - 1)`. -/
def coshTestTower (c : ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  if j = 0 then 2 * (Real.cosh (c * u) - 1)
  else if j % 2 = 0 then 2 * c ^ j * Real.cosh (c * u)
  else 2 * c ^ j * Real.sinh (c * u)

theorem coshTestTower_zero (c : ℝ) (u : ℝ) :
    coshTestTower c 0 u = 2 * (Real.cosh (c * u) - 1) := by
  rw [coshTestTower, if_pos rfl]

theorem hasDerivAt_coshTestTower (c : ℝ) (j : ℕ) (u : ℝ) :
    HasDerivAt (coshTestTower c j) (coshTestTower c (j + 1) u) u := by
  have hcu : HasDerivAt (fun v : ℝ => c * v) c u := by
    have h := (hasDerivAt_id u).const_mul c
    simpa using h
  have hcosh : HasDerivAt (fun v : ℝ => Real.cosh (c * v)) (Real.sinh (c * u) * c) u :=
    (Real.hasDerivAt_cosh (c * u)).comp u hcu
  have hsinh : HasDerivAt (fun v : ℝ => Real.sinh (c * v)) (Real.cosh (c * u) * c) u :=
    (Real.hasDerivAt_sinh (c * u)).comp u hcu
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have hfun : coshTestTower c 0 = fun v : ℝ => 2 * (Real.cosh (c * v) - 1) := by
      funext v
      exact coshTestTower_zero c v
    have hval : coshTestTower c 1 u = 2 * c * Real.sinh (c * u) := by
      rw [coshTestTower, if_neg (by omega), if_neg (by omega)]
      ring
    rw [hfun, hval]
    have h := (hcosh.sub_const 1).const_mul 2
    refine h.congr_deriv ?_
    ring
  · by_cases hpar : j % 2 = 0
    · have hfun : coshTestTower c j = fun v : ℝ => 2 * c ^ j * Real.cosh (c * v) := by
        funext v
        rw [coshTestTower, if_neg (by omega), if_pos hpar]
      have hval : coshTestTower c (j + 1) u = 2 * c ^ (j + 1) * Real.sinh (c * u) := by
        rw [coshTestTower, if_neg (by omega), if_neg (by omega)]
      rw [hfun, hval]
      have h := hcosh.const_mul (2 * c ^ j)
      refine h.congr_deriv ?_
      ring
    · have hfun : coshTestTower c j = fun v : ℝ => 2 * c ^ j * Real.sinh (c * v) := by
        funext v
        rw [coshTestTower, if_neg (by omega), if_neg hpar]
      have hval : coshTestTower c (j + 1) u = 2 * c ^ (j + 1) * Real.cosh (c * u) := by
        rw [coshTestTower, if_neg (by omega), if_pos (by omega)]
      rw [hfun, hval]
      have h := hsinh.const_mul (2 * c ^ j)
      refine h.congr_deriv ?_
      ring

theorem continuous_coshTestTower (c : ℝ) (j : ℕ) : Continuous (coshTestTower c j) := by
  by_cases hj : j = 0
  · subst hj
    have hfun : coshTestTower c 0 = fun v : ℝ => 2 * (Real.cosh (c * v) - 1) := by
      funext v
      exact coshTestTower_zero c v
    rw [hfun]
    exact (((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).sub
      continuous_const).const_mul 2)
  · by_cases hpar : j % 2 = 0
    · have hfun : coshTestTower c j = fun v : ℝ => 2 * c ^ j * Real.cosh (c * v) := by
        funext v
        rw [coshTestTower, if_neg hj, if_pos hpar]
      rw [hfun]
      exact (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).const_mul _
    · have hfun : coshTestTower c j = fun v : ℝ => 2 * c ^ j * Real.sinh (c * v) := by
        funext v
        rw [coshTestTower, if_neg hj, if_neg hpar]
      rw [hfun]
      exact (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).const_mul _

theorem coshTestTower_apply_zero (c : ℝ) (j : ℕ) (hj : j ≠ 0) :
    coshTestTower c j 0 = if j % 2 = 0 then 2 * c ^ j else 0 := by
  rw [coshTestTower, if_neg hj]
  by_cases hpar : j % 2 = 0
  · rw [if_pos hpar, if_pos hpar]
    simp
  · rw [if_neg hpar, if_neg hpar]
    simp

theorem abs_coshTestTower_le (c : ℝ) (j : ℕ) (hj : j ≠ 0) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |coshTestTower c j u| ≤ 2 * |c| ^ j * Real.cosh c := by
  have hcu : |c * u| ≤ |c| := by
    rw [abs_mul]
    have h1 : |u| ≤ 1 := by
      rw [abs_of_nonneg hu.1]
      exact hu.2
    calc |c| * |u| ≤ |c| * 1 := by
          exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
      _ = |c| := mul_one _
  have hcosh : |Real.cosh (c * u)| ≤ Real.cosh c := by
    rw [abs_of_nonneg (Real.cosh_pos _).le]
    have := Real.cosh_abs (c * u)
    calc Real.cosh (c * u) = Real.cosh |c * u| := (Real.cosh_abs _).symm
      _ ≤ Real.cosh |c| := by
          refine Real.cosh_le_cosh.mpr ?_
          rw [abs_abs, abs_abs]
          exact hcu
      _ = Real.cosh c := Real.cosh_abs c
  have hsinh : |Real.sinh (c * u)| ≤ Real.cosh c := by
    calc |Real.sinh (c * u)| = Real.sinh |c * u| := by
          rw [Real.abs_sinh]
      _ ≤ Real.cosh |c * u| := by
          nlinarith [Real.cosh_sq_sub_sinh_sq |c * u|, Real.cosh_pos |c * u|,
            Real.sinh_nonneg_iff.mpr (abs_nonneg (c * u))]
      _ ≤ Real.cosh |c| := by
          refine Real.cosh_le_cosh.mpr ?_
          rw [abs_abs, abs_abs]
          exact hcu
      _ = Real.cosh c := Real.cosh_abs c
  rw [coshTestTower, if_neg hj]
  by_cases hpar : j % 2 = 0
  · rw [if_pos hpar, abs_mul, abs_mul, abs_two, abs_pow]
    exact mul_le_mul_of_nonneg_left hcosh (by positivity)
  · rw [if_neg hpar, abs_mul, abs_mul, abs_two, abs_pow]
    exact mul_le_mul_of_nonneg_left hsinh (by positivity)

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory

/-! ## The boundary defect of the hyperbolic test function -/

theorem primeBoundaryDefect_cosh_eq (c : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    primeBoundaryDefect (coshTestTower c 0) (N : ℝ)
      = primeClockRadialEnergy N (c / Real.log N)
        - ∫ u in (0 : ℝ)..1, radialProfileTest c u := by
  classical
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
  have hsum : (∑ n ∈ Finset.Icc 0 ⌊(N : ℝ)⌋₊,
      (if n.Prime then coshTestTower c 0 (Real.log n / Real.log (N : ℝ)) / n else 0))
      = primeClockRadialEnergy N (c / Real.log (N : ℝ)) := by
    rw [hfloor, primeClockRadialEnergy, sum_primesLE_eq_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    by_cases hp : n.Prime
    · rw [if_pos hp, if_pos hp, coshTestTower_zero]
      have harg : c / Real.log (N : ℝ) * Real.log (n : ℝ)
          = c * (Real.log (n : ℝ) / Real.log (N : ℝ)) := by ring
      rw [harg]
    · rw [if_neg hp, if_neg hp]
  have hint : (∫ u in (0 : ℝ)..1, coshTestTower c 0 u / u)
      = ∫ u in (0 : ℝ)..1, radialProfileTest c u := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu _
    have hu0 : u ≠ 0 := hu
    rw [coshTestTower_zero, radialProfileTest, if_neg hu0]
  rw [primeBoundaryDefect, hsum, hint]

/-- **`(17)`: the symmetric Wick expansion on the radial axis.**  The finite radial prime-clock
energy at boundary-layer scale differs from its Dickman limit by the endpoint jet of the
hyperbolic test function, to every algebraic order. -/
theorem exists_abs_primeClockRadialEnergy_jet_le (N : ℕ) (c : ℝ) :
    ∃ B X₀ : ℝ, 0 ≤ B ∧ 4 ≤ X₀ ∧ ∀ n : ℕ, X₀ ≤ (n : ℝ) →
      |(primeClockRadialEnergy n (c / Real.log n)
          - ∫ u in (0 : ℝ)..1, radialProfileTest c u)
          - ∑ k ∈ Finset.range (N + 1),
              ((if (k + 1) % 2 = 0 then 2 * c ^ (k + 1) else 0)
                / (((k + 1).factorial : ℕ) : ℝ))
                * mertensLogPowConstantFull k / (Real.log n) ^ (k + 1)|
        ≤ B / (Real.log n) ^ (N + 2) := by
  obtain ⟨B, X₀, hB, hX₀, hmain⟩ := exists_abs_primeBoundaryDefect_taylor_jet_le N
    (coshTestTower c) (2 * |c| ^ (N + 2) * Real.cosh c) (by positivity)
    (fun j _ u => hasDerivAt_coshTestTower c j u)
    (fun j _ => continuous_coshTestTower c j)
    (fun u hu => abs_coshTestTower_le c (N + 2) (by omega) hu)
    (by rw [coshTestTower_zero]; simp)
  refine ⟨B, max X₀ 4, hB, le_max_right _ _, ?_⟩
  intro n hn
  have hX₀n : X₀ ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
  have h4n : (4 : ℝ) ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
  have hn2 : 2 ≤ n := by
    have : (2 : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  have h := hmain (n : ℝ) hX₀n
  rw [primeBoundaryDefect_cosh_eq c hn2] at h
  refine h.trans_eq' ?_
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coshTestTower_apply_zero c (k + 1) (by omega)]

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory

/-! ## The trigonometric boundary test tower -/

/-- The derivative tower of `u ↦ 2 (1 - cos (c u))`. -/
def waveTower (c : ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  if j = 0 then 2 * (1 - Real.cos (c * u))
  else -(2 * c ^ j * Real.cos (c * u + (j : ℝ) * (Real.pi / 2)))

theorem waveTower_zero (c : ℝ) (u : ℝ) : waveTower c 0 u = 2 * (1 - Real.cos (c * u)) := by
  rw [waveTower, if_pos rfl]

theorem hasDerivAt_waveTower (c : ℝ) (j : ℕ) (u : ℝ) :
    HasDerivAt (waveTower c j) (waveTower c (j + 1) u) u := by
  have hcu : HasDerivAt (fun v : ℝ => c * v) c u := by
    have h := (hasDerivAt_id u).const_mul c
    simpa using h
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have hfun : waveTower c 0 = fun v : ℝ => 2 * (1 - Real.cos (c * v)) := by
      funext v
      exact waveTower_zero c v
    have hval : waveTower c 1 u = 2 * c * Real.sin (c * u) := by
      rw [waveTower, if_neg (by omega)]
      push_cast
      rw [one_mul, Real.cos_add_pi_div_two]
      ring
    have hcos : HasDerivAt (fun v : ℝ => Real.cos (c * v)) (-Real.sin (c * u) * c) u :=
      (Real.hasDerivAt_cos (c * u)).comp u hcu
    rw [hfun, hval]
    have h := ((hcos.const_sub 1).const_mul 2)
    refine h.congr_deriv ?_
    ring
  · have hshift : ∀ v : ℝ,
        HasDerivAt (fun w : ℝ => Real.cos (c * w + (j : ℝ) * (Real.pi / 2)))
          (-Real.sin (c * v + (j : ℝ) * (Real.pi / 2)) * c) v := by
      intro v
      have hinner : HasDerivAt (fun w : ℝ => c * w + (j : ℝ) * (Real.pi / 2)) c v := by
        have h0 : HasDerivAt (fun w : ℝ => c * w) c v := by
          have h := (hasDerivAt_id v).const_mul c
          simpa using h
        exact h0.add_const _
      exact (Real.hasDerivAt_cos _).comp v hinner
    have hfun : waveTower c j
        = fun v : ℝ => -(2 * c ^ j * Real.cos (c * v + (j : ℝ) * (Real.pi / 2))) := by
      funext v
      rw [waveTower, if_neg (by omega)]
    have hval : waveTower c (j + 1) u
        = 2 * c ^ (j + 1) * Real.sin (c * u + (j : ℝ) * (Real.pi / 2)) := by
      rw [waveTower, if_neg (by omega)]
      have harg : c * u + ((j : ℕ) + 1 : ℝ) * (Real.pi / 2)
          = (c * u + (j : ℝ) * (Real.pi / 2)) + Real.pi / 2 := by
        ring
      push_cast
      rw [harg, Real.cos_add_pi_div_two]
      ring
    rw [hfun, hval]
    have h := ((hshift u).const_mul (2 * c ^ j)).neg
    refine h.congr_deriv ?_
    ring

theorem continuous_waveTower (c : ℝ) (j : ℕ) : Continuous (waveTower c j) := by
  by_cases hj : j = 0
  · subst hj
    have hfun : waveTower c 0 = fun v : ℝ => 2 * (1 - Real.cos (c * v)) := by
      funext v
      exact waveTower_zero c v
    rw [hfun]
    exact ((continuous_const.sub
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).const_mul 2)
  · have hfun : waveTower c j
        = fun v : ℝ => -(2 * c ^ j * Real.cos (c * v + (j : ℝ) * (Real.pi / 2))) := by
      funext v
      rw [waveTower, if_neg hj]
    rw [hfun]
    exact ((Real.continuous_cos.comp
      ((continuous_const.mul continuous_id).add continuous_const)).const_mul _).neg

theorem waveTower_apply_zero (c : ℝ) (j : ℕ) (hj : j ≠ 0) :
    waveTower c j 0 = -(2 * c ^ j * Real.cos ((j : ℝ) * (Real.pi / 2))) := by
  rw [waveTower, if_neg hj, mul_zero, zero_add]

theorem abs_waveTower_le (c : ℝ) (j : ℕ) (hj : j ≠ 0) (u : ℝ) :
    |waveTower c j u| ≤ 2 * |c| ^ j := by
  rw [waveTower, if_neg hj, abs_neg, abs_mul, abs_mul, abs_two, abs_pow]
  have hcos : |Real.cos (c * u + (j : ℝ) * (Real.pi / 2))| ≤ 1 := Real.abs_cos_le_one _
  calc 2 * |c| ^ j * |Real.cos (c * u + (j : ℝ) * (Real.pi / 2))|
      ≤ 2 * |c| ^ j * 1 := by
        refine mul_le_mul_of_nonneg_left hcos (by positivity)
    _ = 2 * |c| ^ j := mul_one _

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory

theorem primeBoundaryDefect_wave_eq (c : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    primeBoundaryDefect (waveTower c 0) (N : ℝ)
      = primeClockVerticalEnergy N (c / Real.log N)
        - ∫ u in (0 : ℝ)..1, verticalProfileTest c u := by
  classical
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
  have hsum : (∑ n ∈ Finset.Icc 0 ⌊(N : ℝ)⌋₊,
      (if n.Prime then waveTower c 0 (Real.log n / Real.log (N : ℝ)) / n else 0))
      = primeClockVerticalEnergy N (c / Real.log (N : ℝ)) := by
    rw [hfloor, primeClockVerticalEnergy_eq_cos, sum_primesLE_eq_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    by_cases hp : n.Prime
    · rw [if_pos hp, if_pos hp, waveTower_zero]
      have harg : c / Real.log (N : ℝ) * Real.log (n : ℝ)
          = c * (Real.log (n : ℝ) / Real.log (N : ℝ)) := by ring
      rw [harg]
    · rw [if_neg hp, if_neg hp]
  have hint : (∫ u in (0 : ℝ)..1, waveTower c 0 u / u)
      = ∫ u in (0 : ℝ)..1, verticalProfileTest c u := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu _
    have hu0 : u ≠ 0 := hu
    rw [waveTower_zero, verticalProfileTest, if_neg hu0]
  rw [primeBoundaryDefect, hsum, hint]

/-- **`(17)`: the symmetric Wick expansion on the vertical axis.** -/
theorem exists_abs_primeClockVerticalEnergy_jet_le (N : ℕ) (c : ℝ) :
    ∃ B X₀ : ℝ, 0 ≤ B ∧ 4 ≤ X₀ ∧ ∀ n : ℕ, X₀ ≤ (n : ℝ) →
      |(primeClockVerticalEnergy n (c / Real.log n)
          - ∫ u in (0 : ℝ)..1, verticalProfileTest c u)
          - ∑ k ∈ Finset.range (N + 1),
              (-(2 * c ^ (k + 1) * Real.cos (((k : ℝ) + 1) * (Real.pi / 2)))
                / (((k + 1).factorial : ℕ) : ℝ))
                * mertensLogPowConstantFull k / (Real.log n) ^ (k + 1)|
        ≤ B / (Real.log n) ^ (N + 2) := by
  obtain ⟨B, X₀, hB, hX₀, hmain⟩ := exists_abs_primeBoundaryDefect_taylor_jet_le N
    (waveTower c) (2 * |c| ^ (N + 2)) (by positivity)
    (fun j _ u => hasDerivAt_waveTower c j u)
    (fun j _ => continuous_waveTower c j)
    (fun u _ => abs_waveTower_le c (N + 2) (by omega) u)
    (by rw [waveTower_zero]; simp)
  refine ⟨B, max X₀ 4, hB, le_max_right _ _, ?_⟩
  intro n hn
  have hX₀n : X₀ ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
  have h4n : (4 : ℝ) ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
  have hn2 : 2 ≤ n := by
    have : (2 : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  have h := hmain (n : ℝ) hX₀n
  rw [primeBoundaryDefect_wave_eq c hn2] at h
  refine h.trans_eq' ?_
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [waveTower_apply_zero c (k + 1) (by omega)]
  push_cast
  ring

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology Set MeasureTheory

/-! ## The leading correction and the beyond-all-orders statement -/

/-- **`(18)`: the first symmetric normalization is `(log N)^2` and its coefficient is the second
higher-order Mertens constant.** -/
theorem tendsto_logSq_mul_primeClockRadialEnergy_sub (c : ℝ) :
    Tendsto (fun n : ℕ => (Real.log n) ^ 2 *
        (primeClockRadialEnergy n (c / Real.log n)
          - ∫ u in (0 : ℝ)..1, radialProfileTest c u))
      atTop (𝓝 (c ^ 2 * mertensLogPowConstantFull 1)) := by
  obtain ⟨B, X₀, hB, hX₀, hmain⟩ := exists_abs_primeClockRadialEnergy_jet_le 1 c
  have hX₀nat : ∀ᶠ n : ℕ in atTop, X₀ ≤ (n : ℝ) := by
    have h := tendsto_natCast_atTop_atTop (R := ℝ)
    exact h.eventually_ge_atTop X₀
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' (a := fun n : ℕ => B / Real.log n) ?_ ?_
  · filter_upwards [hX₀nat, Filter.eventually_ge_atTop 4] with n hn hn4
    have hn4' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have h := hmain n hn
    have hjet : ∑ k ∈ Finset.range 2,
        ((if (k + 1) % 2 = 0 then 2 * c ^ (k + 1) else 0) / (((k + 1).factorial : ℕ) : ℝ))
          * mertensLogPowConstantFull k / (Real.log (n : ℝ)) ^ (k + 1)
        = c ^ 2 * mertensLogPowConstantFull 1 / (Real.log (n : ℝ)) ^ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    rw [hjet] at h
    have hkey : |(Real.log (n : ℝ)) ^ 2 *
        (primeClockRadialEnergy n (c / Real.log (n : ℝ))
          - ∫ u in (0 : ℝ)..1, radialProfileTest c u)
        - c ^ 2 * mertensLogPowConstantFull 1|
        ≤ (Real.log (n : ℝ)) ^ 2 * (B / (Real.log (n : ℝ)) ^ 3) := by
      have hfac : (Real.log (n : ℝ)) ^ 2 *
          (primeClockRadialEnergy n (c / Real.log (n : ℝ))
            - ∫ u in (0 : ℝ)..1, radialProfileTest c u)
          - c ^ 2 * mertensLogPowConstantFull 1
          = (Real.log (n : ℝ)) ^ 2 *
            ((primeClockRadialEnergy n (c / Real.log (n : ℝ))
              - ∫ u in (0 : ℝ)..1, radialProfileTest c u)
              - c ^ 2 * mertensLogPowConstantFull 1 / (Real.log (n : ℝ)) ^ 2) := by
        field_simp
      rw [hfac, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2)]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    rw [Real.norm_eq_abs]
    refine hkey.trans_eq ?_
    field_simp
  · have hlogTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop)
    exact Filter.Tendsto.div_atTop tendsto_const_nhds hlogTop

/-- **`(19)`: the bulk defect is beyond every algebraic order.**  A boundary test function whose
whole derivative tower vanishes at the collapsed endpoint — in particular any test function
supported in `[δ,1]` — has boundary defect `O(L^{-M})` for every `M`. -/
theorem exists_abs_primeBoundaryDefect_flat_le (N : ℕ) (f : ℕ → ℝ → ℝ) (A : ℝ)
    (hA : 0 ≤ A)
    (hderiv : ∀ j ≤ N + 1, ∀ u : ℝ, HasDerivAt (f j) (f (j + 1) u) u)
    (hcont : ∀ j ≤ N + 2, Continuous (f j))
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, |f (N + 2) u| ≤ A)
    (hflat : ∀ j ≤ N + 1, f j 0 = 0) :
    ∃ B X₀ : ℝ, 0 ≤ B ∧ 4 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
      |primeBoundaryDefect (f 0) x| ≤ B / (Real.log x) ^ (N + 2) := by
  obtain ⟨B, X₀, hB, hX₀, hmain⟩ := exists_abs_primeBoundaryDefect_taylor_jet_le N f A hA
    hderiv hcont hbound (hflat 0 (by omega))
  refine ⟨B, X₀, hB, hX₀, ?_⟩
  intro x hx
  have h := hmain x hx
  have hzero : ∑ k ∈ Finset.range (N + 1),
      (f (k + 1) 0 / (((k + 1).factorial : ℕ) : ℝ))
        * mertensLogPowConstantFull k / (Real.log x) ^ (k + 1) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k + 1 ≤ N + 1 := by
      have := Finset.mem_range.mp hk
      omega
    rw [hflat (k + 1) hk']
    ring
  rwa [hzero, sub_zero] at h

/-- **`(20)`: every finite truncation of the boundary expansion is zero-free.**  The exponential
of any finite Lévy exponent is nonvanishing, so no finite set of boundary coefficients can create
a node. -/
theorem exp_wickProfile_add_poly_ne_zero (z w : ℂ) : Complex.exp (wickProfile z + w) ≠ 0 :=
  Complex.exp_ne_zero _

end

end RHTower
