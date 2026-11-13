import GaloisForLFunctions.RHTower.BeurlingOverRegularIntegersOffLineZeros
import GaloisForLFunctions.RHTower.CCM.CCMFirstClockTailLowerBoundCompleteness

/-!
# Möbius inversion of the over-regular prime density

Let `1/3 < μ < 1/2`, `0 < ν < 3μ - 1`, and let `w = primeDensity μ ν γ` be the logarithmic prime
density of the rational zeta function `ζ_c = overRegularZeta μ ν γ` (zeros at `1 - μ ± iγ`, a
simple pole at `1`).  Cut `w` at `u₀ = 10/μ` (`cutDensity`, `w̃ = 1_{[u₀,∞)} w`) and invert the
prime-power sum by Möbius:

`π₀(y) = Σ_{d ≥ 1} μ(d) d⁻² w̃(y/d)`  (`invertedDensity`).

* `π₀` vanishes below `u₀` and `e^y/(2y) ≤ π₀(y) ≤ 3e^y/(2y)` above it: the term `d = 1` dominates
  (`invertedDensity_bounds`).
* Möbius inversion: `Σ_{r ≥ 1} r⁻² π₀(v/r) = w̃(v)` (`tsum_invertedDensity_div`), hence for
  `Re s > 1` the prime-power Laplace sum of `π₀` is the Laplace transform of `w̃`:
  `Σ_{r ≥ 1} r⁻¹ ∫ e^{-rsy} π₀(y) dy = ∫ e^{-sv} w̃(v) dv` (`laplace_cutDensity_eq_tsum`).
* `exp (∫ e^{-sv} w̃(v) dv) = ζ_c(s) e^{-I₀(s)}` with `I₀(s) = ∫_0^{u₀} e^{-sv} w(v) dv` entire
  (`cexp_laplace_cutDensity`, `differentiable_headLaplace`).
-/

open Complex MeasureTheory Filter Topology Set
open RHTower.BeurlingOverRegularIntegers

noncomputable section

namespace GaloisForLFunctions.EulerFETransportTheory.MobiusInverted

/-! ## The cut density -/

/-- The cut point `u₀ = 10/μ`. -/
def cutPoint (μ : ℝ) : ℝ := 10 / μ

theorem twenty_lt_cutPoint {μ : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2) : 20 < cutPoint μ := by
  rw [cutPoint, lt_div_iff₀ hμ0]; linarith

theorem thirty_six_le_exp_ten : (36 : ℝ) ≤ Real.exp 10 := by
  have h := Real.add_one_le_exp 5
  have h' : Real.exp 10 = Real.exp 5 * Real.exp 5 := by rw [← Real.exp_add]; norm_num
  rw [h']; nlinarith

/-- Above `u₀` the numerator of the prime density is within `e^v/4` of `e^v`. -/
theorem abs_primeNumerator_sub_exp_le {μ ν γ v : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2)
    (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1)
    (hv : cutPoint μ ≤ v) : |primeNumerator μ ν γ v - Real.exp v| ≤ Real.exp v / 4 := by
  have hu := twenty_lt_cutPoint hμ0 hμ2
  have hv0 : 0 < v := by linarith
  have hμv : 10 ≤ μ * v := by
    rw [cutPoint, div_le_iff₀ hμ0] at hv; linarith
  have hE := thirty_six_le_exp_ten
  have hev : 36 ≤ Real.exp v := hE.trans (Real.exp_le_exp.mpr (by linarith))
  have h1 : Real.exp ((1 - μ) * v) * 36 ≤ Real.exp v := by
    have : Real.exp ((1 - μ) * v) * Real.exp (μ * v) = Real.exp v := by
      rw [← Real.exp_add]; ring_nf
    have h10 : 36 ≤ Real.exp (μ * v) := hE.trans (Real.exp_le_exp.mpr hμv)
    nlinarith [Real.exp_pos ((1 - μ) * v)]
  have e1 : Real.exp (-((3 * μ - 1 - ν) * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e2 : Real.exp (-((3 * μ - 1 + ν) * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have e3 : Real.exp (-((4 * μ - 1) * v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_pos h4 hv0])
  have p1 := Real.exp_pos (-((3 * μ - 1 - ν) * v))
  have p2 := Real.exp_pos (-((3 * μ - 1 + ν) * v))
  have p3 := Real.exp_pos (-((4 * μ - 1) * v))
  have hE1 := Real.exp_pos ((1 - μ) * v)
  have hc1 := Real.cos_le_one (γ * v)
  have hc2 := Real.neg_one_le_cos (γ * v)
  have hcos1 : Real.exp ((1 - μ) * v) * Real.cos (γ * v) ≤ Real.exp ((1 - μ) * v) := by
    nlinarith
  have hcos2 : -Real.exp ((1 - μ) * v) ≤ Real.exp ((1 - μ) * v) * Real.cos (γ * v) := by
    nlinarith
  rw [primeNumerator, abs_le]
  constructor <;> nlinarith

/-- `(3/4) e^v/v ≤ w(v) ≤ (5/4) e^v/v` above `u₀`. -/
theorem primeDensity_bounds {μ ν γ v : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2)
    (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1)
    (hv : cutPoint μ ≤ v) :
    3 / 4 * (Real.exp v / v) ≤ primeDensity μ ν γ v ∧
      primeDensity μ ν γ v ≤ 5 / 4 * (Real.exp v / v) := by
  have hv0 : 0 < v := by linarith [twenty_lt_cutPoint hμ0 hμ2]
  have h := abs_le.mp (abs_primeNumerator_sub_exp_le (γ := γ) hμ0 hμ2 hp₁ hp₂ h4 hv)
  rw [primeDensity, mul_div_assoc', mul_div_assoc']
  exact ⟨div_le_div_of_nonneg_right (by linarith) hv0.le,
    div_le_div_of_nonneg_right (by linarith) hv0.le⟩

/-- The prime density cut at `u₀`: `w̃ = 1_{[u₀,∞)} w`. -/
def cutDensity (μ ν γ : ℝ) : ℝ → ℝ := (Ici (cutPoint μ)).indicator (primeDensity μ ν γ)

theorem measurable_primeDensity (μ ν γ : ℝ) : Measurable (primeDensity μ ν γ) := by
  unfold primeDensity primeNumerator
  fun_prop

theorem measurable_cutDensity (μ ν γ : ℝ) : Measurable (cutDensity μ ν γ) :=
  (measurable_primeDensity μ ν γ).indicator measurableSet_Ici

theorem cutDensity_nonneg {μ ν γ : ℝ} (hμ0 : 0 < μ) (v : ℝ) : 0 ≤ cutDensity μ ν γ v := by
  unfold cutDensity
  by_cases hv : v ∈ Ici (cutPoint μ)
  · rw [indicator_of_mem hv]
    exact primeDensity_nonneg hμ0.le (lt_of_lt_of_le (div_pos (by norm_num) hμ0) hv)
  · rw [indicator_of_notMem hv]

theorem cutDensity_eq_zero {μ ν γ v : ℝ} (hv : v < cutPoint μ) : cutDensity μ ν γ v = 0 := by
  unfold cutDensity
  rw [indicator_of_notMem (by simpa using hv)]

theorem cutDensity_le {μ ν γ : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2)
    (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1) {v : ℝ}
    (hv : cutPoint μ ≤ v) : cutDensity μ ν γ v ≤ 5 / 4 * (Real.exp v / v) := by
  unfold cutDensity
  rw [indicator_of_mem (show v ∈ Ici (cutPoint μ) from hv)]
  exact (primeDensity_bounds hμ0 hμ2 hp₁ hp₂ h4 hv).2

/-! ## The Möbius-inverted density -/

/-- The `d`-th term `μ(d+1) (d+1)⁻² w̃(y/(d+1))`. -/
def invTerm (μ ν γ : ℝ) (d : ℕ) (y : ℝ) : ℝ :=
  (ArithmeticFunction.moebius (d + 1) : ℝ) / ((d : ℝ) + 1) ^ 2 * cutDensity μ ν γ (y / ((d : ℝ) + 1))

/-- The Möbius-inverted density `π₀(y) = Σ_{d ≥ 1} μ(d) d⁻² w̃(y/d)`. -/
def invertedDensity (μ ν γ y : ℝ) : ℝ := ∑' d : ℕ, invTerm μ ν γ d y

theorem invTerm_eq_zero {μ ν γ y : ℝ} {d : ℕ}
    (hd : y < ((d : ℝ) + 1) * cutPoint μ) : invTerm μ ν γ d y = 0 := by
  rw [invTerm, cutDensity_eq_zero, mul_zero]
  rw [div_lt_iff₀ (by positivity)]; linarith

/-- Only the terms `d < ⌊y/u₀⌋` survive. -/
theorem invertedDensity_eq_sum {μ ν γ : ℝ} (hμ0 : 0 < μ) (y : ℝ) :
    invertedDensity μ ν γ y = ∑ d ∈ Finset.range ⌊y / cutPoint μ⌋₊, invTerm μ ν γ d y := by
  have hu : 0 < cutPoint μ := div_pos (by norm_num) hμ0
  refine tsum_eq_sum fun d hd => invTerm_eq_zero ?_
  rw [Finset.mem_range, not_lt] at hd
  have h1 := Nat.lt_floor_add_one (y / cutPoint μ)
  have h2 : (⌊y / cutPoint μ⌋₊ : ℝ) ≤ d := by exact_mod_cast hd
  have := (div_lt_iff₀ hu).mp
    (lt_of_lt_of_le h1 (show (⌊y / cutPoint μ⌋₊ : ℝ) + 1 ≤ d + 1 by linarith))
  linarith

theorem summable_invTerm {μ ν γ : ℝ} (hμ0 : 0 < μ) (y : ℝ) :
    Summable fun d => invTerm μ ν γ d y := by
  have hu : 0 < cutPoint μ := div_pos (by norm_num) hμ0
  refine summable_of_ne_finset_zero (s := Finset.range ⌊y / cutPoint μ⌋₊) fun d hd => ?_
  refine invTerm_eq_zero ?_
  rw [Finset.mem_range, not_lt] at hd
  have h1 := Nat.lt_floor_add_one (y / cutPoint μ)
  have h2 : (⌊y / cutPoint μ⌋₊ : ℝ) ≤ d := by exact_mod_cast hd
  have := (div_lt_iff₀ hu).mp
    (lt_of_lt_of_le h1 (show (⌊y / cutPoint μ⌋₊ : ℝ) + 1 ≤ d + 1 by linarith))
  linarith

theorem invertedDensity_eq_zero {μ ν γ y : ℝ} (hμ0 : 0 < μ) (hy : y < cutPoint μ) :
    invertedDensity μ ν γ y = 0 := by
  rw [invertedDensity]
  refine (tsum_congr fun d => invTerm_eq_zero ?_).trans tsum_zero
  have hu : 0 < cutPoint μ := div_pos (by norm_num) hμ0
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

theorem measurable_invertedDensity (μ ν γ : ℝ) (hμ0 : 0 < μ) :
    Measurable (invertedDensity μ ν γ) := by
  refine measurable_of_tendsto_metrizable (f := fun N y => ∑ d ∈ Finset.range N, invTerm μ ν γ d y)
    (fun N => Finset.measurable_sum _ fun d _ => ?_) (tendsto_pi_nhds.mpr fun y =>
      (summable_invTerm hμ0 y).hasSum.tendsto_sum_nat)
  exact measurable_const.mul ((measurable_cutDensity μ ν γ).comp (measurable_id.div_const _))

/-- `y ≤ e^{y/2}` for `y ≥ 0`. -/
theorem le_exp_half {y : ℝ} (hy : 0 ≤ y) : y ≤ Real.exp (y / 2) := by
  have h := Real.add_one_le_exp (y / 4)
  have h' : Real.exp (y / 2) = Real.exp (y / 4) * Real.exp (y / 4) := by
    rw [← Real.exp_add]; ring_nf
  rw [h']
  nlinarith [sq_nonneg (y / 4 - 1)]

/-- The terms `d ≥ 1` are at most `(5/4) e^{y/2}/y`. -/
theorem abs_invTerm_succ_le {μ ν γ : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2)
    (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1) {y : ℝ}
    (hy : cutPoint μ ≤ y) (d : ℕ) :
    |invTerm μ ν γ (d + 1) y| ≤ 5 / 4 * (Real.exp (y / 2) / y) := by
  have hu := twenty_lt_cutPoint hμ0 hμ2
  have hy0 : 0 < y := by linarith
  have hd2 : (2 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith [(d.cast_nonneg : (0 : ℝ) ≤ d)]
  set D : ℝ := ((d + 1 : ℕ) : ℝ) + 1 with hD
  have hD0 : 0 < D := by linarith
  rw [invTerm, ← hD, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < D ^ 2)]
  have hμ1 : |(ArithmeticFunction.moebius (d + 1 + 1) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rcases lt_or_ge (y / D) (cutPoint μ) with hlt | hge
  · rw [cutDensity_eq_zero hlt, abs_zero, mul_zero]; positivity
  · rw [abs_of_nonneg (cutDensity_nonneg hμ0 _)]
    have hc := cutDensity_le (γ := γ) hμ0 hμ2 hp₁ hp₂ h4 hge
    have hexp : Real.exp (y / D) ≤ Real.exp (y / 2) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hy0.le (by norm_num) hd2)
    have e : Real.exp (y / D) / (y / D) = D * (Real.exp (y / D) / y) := by
      field_simp
    rw [e] at hc
    calc |(ArithmeticFunction.moebius (d + 1 + 1) : ℝ)| / D ^ 2 * cutDensity μ ν γ (y / D)
        ≤ 1 / D ^ 2 * (5 / 4 * (D * (Real.exp (y / D) / y))) := by
          gcongr
          exact cutDensity_nonneg hμ0 _
      _ = 5 / 4 * (Real.exp (y / D) / y) / D := by field_simp
      _ ≤ 5 / 4 * (Real.exp (y / 2) / y) / 1 := by
          gcongr
          linarith
      _ = 5 / 4 * (Real.exp (y / 2) / y) := by rw [div_one]

/-- **The inverted density is comparable to `e^y/y` above `u₀`.** -/
theorem invertedDensity_bounds {μ ν γ : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2)
    (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1) {y : ℝ}
    (hy : cutPoint μ ≤ y) :
    1 / 2 * (Real.exp y / y) ≤ invertedDensity μ ν γ y ∧
      invertedDensity μ ν γ y ≤ 3 / 2 * (Real.exp y / y) := by
  have hu := twenty_lt_cutPoint hμ0 hμ2
  have hu0 : 0 < cutPoint μ := by linarith
  have hy0 : 0 < y := by linarith
  set N := ⌊y / cutPoint μ⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by rw [Nat.cast_one, one_le_div hu0]; exact hy)
  have hNy : (N : ℝ) ≤ y / cutPoint μ := Nat.floor_le (div_nonneg hy0.le hu0.le)
  obtain ⟨K, hK⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  rw [invertedDensity_eq_sum hμ0, ← hN, hK, Finset.sum_range_succ']
  -- the leading term `d = 1` is `w(y)`
  have h0 : invTerm μ ν γ 0 y = primeDensity μ ν γ y := by
    simp only [invTerm, Nat.cast_zero, zero_add, ArithmeticFunction.moebius_apply_one,
      Int.cast_one, one_pow, div_one, one_mul]
    unfold cutDensity
    rw [indicator_of_mem (show y ∈ Ici (cutPoint μ) from hy)]
  rw [h0]
  have hw := primeDensity_bounds (γ := γ) hμ0 hμ2 hp₁ hp₂ h4 hy
  -- the tail `d ≥ 2` is at most `(5/4) e^{y/2}/u₀ ≤ (1/4) e^y/y`
  have htail : |∑ d ∈ Finset.range K, invTerm μ ν γ (d + 1) y| ≤ 1 / 4 * (Real.exp y / y) := by
    have hK' : (K : ℝ) ≤ y / cutPoint μ := by
      have : (K : ℝ) + 1 = N := by rw [hK]; push_cast; ring
      linarith
    calc |∑ d ∈ Finset.range K, invTerm μ ν γ (d + 1) y|
        ≤ ∑ d ∈ Finset.range K, |invTerm μ ν γ (d + 1) y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Finset.range K, 5 / 4 * (Real.exp (y / 2) / y) :=
          Finset.sum_le_sum fun d _ => abs_invTerm_succ_le hμ0 hμ2 hp₁ hp₂ h4 hy d
      _ = K * (5 / 4 * (Real.exp (y / 2) / y)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ y / cutPoint μ * (5 / 4 * (Real.exp (y / 2) / y)) := by gcongr
      _ = 5 / 4 * Real.exp (y / 2) / cutPoint μ := by field_simp
      _ ≤ 1 / 4 * (Real.exp y / y) := by
          have hhalf : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
            rw [← Real.exp_add]; ring_nf
          have hle := le_exp_half hy0.le
          have hpos := Real.exp_pos (y / 2)
          rw [div_le_iff₀ hu0, hhalf]
          rw [show 1 / 4 * (Real.exp (y / 2) * Real.exp (y / 2) / y) * cutPoint μ =
            Real.exp (y / 2) * (Real.exp (y / 2) * cutPoint μ / (4 * y)) by field_simp]
          rw [show 5 / 4 * Real.exp (y / 2) = Real.exp (y / 2) * (5 / 4) by ring]
          refine mul_le_mul_of_nonneg_left ?_ hpos.le
          rw [le_div_iff₀ (by positivity)]
          nlinarith
  have := abs_le.mp htail
  constructor <;> linarith [this.1, this.2]

theorem invertedDensity_nonneg {μ ν γ : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2)
    (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1) (y : ℝ) :
    0 ≤ invertedDensity μ ν γ y := by
  rcases lt_or_ge y (cutPoint μ) with hy | hy
  · rw [invertedDensity_eq_zero hμ0 hy]
  · have hy0 : 0 < y := by linarith [twenty_lt_cutPoint hμ0 hμ2]
    exact le_trans (by positivity) (invertedDensity_bounds hμ0 hμ2 hp₁ hp₂ h4 hy).1

theorem invertedDensity_pos {μ ν γ : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2)
    (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1) {y : ℝ}
    (hy : cutPoint μ ≤ y) : 0 < invertedDensity μ ν γ y := by
  have hy0 : 0 < y := by linarith [twenty_lt_cutPoint hμ0 hμ2]
  exact lt_of_lt_of_le (by positivity) (invertedDensity_bounds hμ0 hμ2 hp₁ hp₂ h4 hy).1

theorem invertedDensity_le_exp {μ ν γ : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2)
    (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1) (y : ℝ) :
    invertedDensity μ ν γ y ≤ (Ici (cutPoint μ)).indicator Real.exp y := by
  rcases lt_or_ge y (cutPoint μ) with hy | hy
  · rw [invertedDensity_eq_zero hμ0 hy, indicator_of_notMem (by simpa using hy)]
  · have hu := twenty_lt_cutPoint hμ0 hμ2
    have hy0 : 0 < y := by linarith
    rw [indicator_of_mem (show y ∈ Ici (cutPoint μ) from hy)]
    refine (invertedDensity_bounds hμ0 hμ2 hp₁ hp₂ h4 hy).2.trans ?_
    rw [mul_div_assoc', div_le_iff₀ hy0]
    nlinarith [Real.exp_pos y]

/-! ## Möbius inversion -/

/-- Divisor regrouping of a summable real double series vanishing on the axes. -/
theorem hasSum_divisorsAntidiagonal_regroup {f : ℕ × ℕ → ℝ} (hf : Summable f)
    (h0 : ∀ p : ℕ × ℕ, (p.1 = 0 ∨ p.2 = 0) → f p = 0) :
    HasSum (fun N : ℕ => ∑ p ∈ N.divisorsAntidiagonal, f p) (∑' p, f p) := by
  refine (hf.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)).congr_fun fun N => ?_
  rw [tsum_subtype]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.divisorsAntidiagonal_zero, Finset.sum_empty]
    have hz : ∀ p : ℕ × ℕ, ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}).indicator f p = 0 := by
      intro p
      by_cases hp : p ∈ (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}
      · rw [Set.indicator_of_mem hp]; exact h0 p (mul_eq_zero.mp hp)
      · rw [Set.indicator_of_notMem hp]
    simp only [hz, tsum_zero]
  · rw [tsum_eq_sum (s := N.divisorsAntidiagonal)]
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [Set.indicator_of_mem]
      exact (Nat.mem_divisorsAntidiagonal.mp hp).1
    · intro p hp
      rw [Set.indicator_of_notMem]
      intro h
      exact hp (Nat.mem_divisorsAntidiagonal.mpr ⟨h, hN.ne'⟩)

theorem sum_divisors_moebius_real (N : ℕ) :
    ∑ i ∈ N.divisors, (ArithmeticFunction.moebius i : ℝ) = if N = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f N) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← Int.cast_sum, h]
  split_ifs <;> simp

/-- **Möbius inversion**: `Σ_{r ≥ 1} r⁻² π₀(v/r) = w̃(v)`. -/
theorem tsum_invertedDensity_div {μ ν γ : ℝ} (hμ0 : 0 < μ) (v : ℝ) :
    ∑' r : ℕ, invertedDensity μ ν γ (v / ((r : ℝ) + 1)) / ((r : ℝ) + 1) ^ 2 =
      cutDensity μ ν γ v := by
  have hu : 0 < cutPoint μ := div_pos (by norm_num) hμ0
  -- `a(n) = w̃(v/n)/n²`
  set a : ℕ → ℝ := fun n => if n = 0 then 0 else cutDensity μ ν γ (v / n) / (n : ℝ) ^ 2 with ha
  set f : ℕ × ℕ → ℝ := fun p => (ArithmeticFunction.moebius p.2 : ℝ) * a (p.1 * p.2) with hf
  have hf0 : ∀ p : ℕ × ℕ, (p.1 = 0 ∨ p.2 = 0) → f p = 0 := by
    rintro ⟨r, d⟩ h
    rcases h with h | h
    · simp only [hf, ha] at h ⊢; simp [h]
    · simp only [hf] at h ⊢; simp [h]
  -- finite support
  set K := ⌊|v| / cutPoint μ⌋₊ + 1 with hK
  have hsupp : ∀ p : ℕ × ℕ, p ∉ Finset.range K ×ˢ Finset.range K → f p = 0 := by
    rintro ⟨r, d⟩ hp
    by_cases hz : r = 0 ∨ d = 0
    · exact hf0 _ hz
    rw [not_or] at hz
    simp only [hf, ha]
    have hrd : r * d ≠ 0 := Nat.mul_ne_zero hz.1 hz.2
    rw [if_neg hrd]
    have hbig : (K : ℝ) ≤ r * d := by
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range, not_and_or, not_lt,
        not_lt] at hp
      rcases hp with h | h
      · have h1 : (K : ℝ) ≤ r := by exact_mod_cast h
        have h2 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz.2
        calc (K : ℝ) = K * 1 := (mul_one _).symm
          _ ≤ r * d := mul_le_mul h1 h2 zero_le_one (Nat.cast_nonneg r)
      · have h1 : (K : ℝ) ≤ d := by exact_mod_cast h
        have h2 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz.1
        calc (K : ℝ) = 1 * K := (one_mul _).symm
          _ ≤ r * d := mul_le_mul h2 h1 (Nat.cast_nonneg _) (Nat.cast_nonneg r)
    have hlt : v / ((r * d : ℕ) : ℝ) < cutPoint μ := by
      have hpos : (0 : ℝ) < ((r * d : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hrd
      rw [div_lt_iff₀ hpos]
      have h1 := Nat.lt_floor_add_one (|v| / cutPoint μ)
      rw [div_lt_iff₀ hu] at h1
      have hKc : (K : ℝ) = (⌊|v| / cutPoint μ⌋₊ : ℝ) + 1 := by rw [hK]; push_cast; ring
      have h2 := mul_le_mul_of_nonneg_right hbig hu.le
      push_cast
      have : v ≤ |v| := le_abs_self v
      nlinarith
    rw [cutDensity_eq_zero hlt]; simp
  have hsum : Summable f := summable_of_ne_finset_zero fun p hp => hsupp p hp
  -- regroup by `N = r d`
  have hreg := hasSum_divisorsAntidiagonal_regroup hsum hf0
  have hblock : ∀ N : ℕ, ∑ p ∈ N.divisorsAntidiagonal, f p = if N = 1 then a 1 else 0 := by
    intro N
    have e : ∀ p ∈ N.divisorsAntidiagonal, f p = (ArithmeticFunction.moebius p.2 : ℝ) * a N := by
      intro p hp
      simp only [hf]; rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
    rw [Finset.sum_congr rfl e, ← Finset.sum_mul,
      Nat.sum_divisorsAntidiagonal' (fun _ d => (ArithmeticFunction.moebius d : ℝ)),
      sum_divisors_moebius_real]
    split_ifs with h
    · rw [h, one_mul]
    · rw [zero_mul]
  have hval : ∑' p, f p = a 1 := by
    rw [← hreg.tsum_eq, tsum_congr hblock, tsum_eq_single 1 (fun N hN => if_neg hN), if_pos rfl]
  -- iterate: `Σ' p f = Σ'_r Σ'_d f (r+1, d+1)`
  have hiter : ∑' p, f p = ∑' r : ℕ, ∑' d : ℕ, f (r + 1, d + 1) := by
    rw [hsum.tsum_prod' fun r => hsum.prod_factor r]
    rw [hsum.prod.tsum_eq_zero_add]
    have hz : ∑' d : ℕ, f (0, d) = 0 := (tsum_congr fun d => hf0 _ (Or.inl rfl)).trans tsum_zero
    rw [hz, zero_add]
    refine tsum_congr fun r => ?_
    rw [(hsum.prod_factor (r + 1)).tsum_eq_zero_add, hf0 _ (Or.inr rfl), zero_add]
  have h1 : a 1 = cutDensity μ ν γ v := by simp [ha]
  rw [← h1, ← hval, hiter]
  refine tsum_congr fun r => ?_
  rw [invertedDensity, div_eq_mul_inv, ← tsum_mul_right]
  refine tsum_congr fun d => ?_
  simp only [hf, ha, invTerm]
  rw [if_neg (Nat.mul_ne_zero (Nat.succ_ne_zero r) (Nat.succ_ne_zero d))]
  push_cast
  rw [div_div]
  field_simp

/-! ## Laplace transforms -/

/-- The dominating function `1_{[u₀,∞)}(y) e^{-(a-1) y}` of `e^{-ay} π₀(y)`. -/
theorem integrable_indicator_exp_neg {u₀ b : ℝ} (hb : 0 < b) :
    Integrable ((Ici u₀).indicator fun y => Real.exp (-b * y)) := by
  refine IntegrableOn.integrable_indicator ?_ measurableSet_Ici
  exact (integrableOn_Ici_iff_integrableOn_Ioi enorm_ne_top).2 (exp_neg_integrableOn_Ioi u₀ hb)

theorem integral_indicator_exp_neg {u₀ b : ℝ} (hb : 0 < b) :
    ∫ y, (Ici u₀).indicator (fun y => Real.exp (-b * y)) y = Real.exp (-b * u₀) / b := by
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (by linarith)]
  field_simp

theorem exp_mul_invertedDensity_le {μ ν γ : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2)
    (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1) (a y : ℝ) :
    Real.exp (-a * y) * invertedDensity μ ν γ y ≤
      (Ici (cutPoint μ)).indicator (fun y => Real.exp (-(a - 1) * y)) y := by
  have h := mul_le_mul_of_nonneg_left (invertedDensity_le_exp (γ := γ) hμ0 hμ2 hp₁ hp₂ h4 y)
    (Real.exp_pos (-a * y)).le
  refine h.trans (le_of_eq ?_)
  by_cases hy : y ∈ Ici (cutPoint μ)
  · rw [indicator_of_mem hy, indicator_of_mem hy, ← Real.exp_add]; ring_nf
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]

theorem integrable_exp_mul_invertedDensity {μ ν γ : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2)
    (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1) {a : ℝ}
    (ha : 1 < a) : Integrable fun y => Real.exp (-a * y) * invertedDensity μ ν γ y := by
  refine (integrable_indicator_exp_neg (u₀ := cutPoint μ) (by linarith : 0 < a - 1)).mono'
    ((by fun_prop : Measurable fun y => Real.exp (-a * y)).mul
      (measurable_invertedDensity μ ν γ hμ0)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
    (invertedDensity_nonneg hμ0 hμ2 hp₁ hp₂ h4 y))]
  exact exp_mul_invertedDensity_le hμ0 hμ2 hp₁ hp₂ h4 a y

/-- `∫ e^{-ay} π₀(y) dy ≤ e^{-(a-1)u₀}/(a - 1)` for `a > 1`. -/
theorem integral_exp_mul_invertedDensity_le {μ ν γ : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2)
    (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1) {a : ℝ}
    (ha : 1 < a) :
    ∫ y, Real.exp (-a * y) * invertedDensity μ ν γ y ≤
      Real.exp (-(a - 1) * cutPoint μ) / (a - 1) := by
  rw [← integral_indicator_exp_neg (by linarith : 0 < a - 1)]
  exact integral_mono (integrable_exp_mul_invertedDensity hμ0 hμ2 hp₁ hp₂ h4 ha)
    (integrable_indicator_exp_neg (by linarith)) fun y =>
      exp_mul_invertedDensity_le hμ0 hμ2 hp₁ hp₂ h4 a y

theorem norm_cexp_mul_ofReal (z : ℂ) (y c : ℝ) :
    ‖cexp (-(z * y)) * (c : ℂ)‖ = Real.exp (-z.re * y) * |c| := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  congr 2
  simp

theorem integrable_cexp_mul_invertedDensity {μ ν γ : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2)
    (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1) {z : ℂ}
    (hz : 1 < z.re) :
    Integrable fun y : ℝ => cexp (-(z * y)) * (invertedDensity μ ν γ y : ℂ) := by
  refine (integrable_exp_mul_invertedDensity (γ := γ) hμ0 hμ2 hp₁ hp₂ h4 hz).mono'
    ((by fun_prop : Continuous fun y : ℝ => cexp (-(z * y))).aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp
        (measurable_invertedDensity μ ν γ hμ0)).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [norm_cexp_mul_ofReal, abs_of_nonneg (invertedDensity_nonneg hμ0 hμ2 hp₁ hp₂ h4 y)]

/-- **The prime-power Laplace sum of `π₀` is the Laplace transform of `w̃`.** -/
theorem laplace_cutDensity_eq_tsum {μ ν γ : ℝ} (hμ0 : 0 < μ) (hμ2 : μ < 1 / 2)
    (hp₁ : 0 < 3 * μ - 1 - ν) (hp₂ : 0 < 3 * μ - 1 + ν) (h4 : 0 < 4 * μ - 1) {s : ℂ}
    (hs : 1 < s.re) :
    ∫ v : ℝ, cexp (-(s * v)) * (cutDensity μ ν γ v : ℂ) =
      ∑' r : ℕ, 1 / ((r : ℂ) + 1) *
        ∫ y : ℝ, cexp (-(((r : ℂ) + 1) * s * y)) * (invertedDensity μ ν γ y : ℂ) := by
  have hu := twenty_lt_cutPoint hμ0 hμ2
  -- `H_r(y) = e^{-(r+1)sy} π₀(y)/(r+1)²`
  set H : ℕ → ℝ → ℂ := fun r y => cexp (-(((r : ℂ) + 1) * s * y)) *
    (invertedDensity μ ν γ y : ℂ) / ((r : ℂ) + 1) ^ 2 with hH
  have hr0 : ∀ r : ℕ, ((r : ℝ) + 1) ≠ 0 := fun r => by positivity
  have hrc : ∀ r : ℕ, ((r : ℂ) + 1) ≠ 0 := fun r => by exact_mod_cast hr0 r
  have hre : ∀ r : ℕ, 1 < (((r : ℂ) + 1) * s).re := fun r => by
    have : (((r : ℂ) + 1) * s).re = ((r : ℝ) + 1) * s.re := by simp
    rw [this]; nlinarith [(r.cast_nonneg : (0 : ℝ) ≤ r)]
  -- pointwise Möbius inversion
  have hpt : ∀ v : ℝ, cexp (-(s * v)) * (cutDensity μ ν γ v : ℂ) =
      ∑' r : ℕ, H r (v / ((r : ℝ) + 1)) := by
    intro v
    rw [← tsum_invertedDensity_div hμ0 v, Complex.ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr fun r => ?_
    simp only [hH]
    have e : ((r : ℂ) + 1) * s * ((v / ((r : ℝ) + 1) : ℝ) : ℂ) = s * v := by
      push_cast; field_simp [hrc r]
    rw [e]
    push_cast
    ring
  -- integrability of each term and summability of the norms
  have hint : ∀ r : ℕ, Integrable fun y : ℝ => H r y := fun r =>
    (integrable_cexp_mul_invertedDensity hμ0 hμ2 hp₁ hp₂ h4 (hre r)).div_const _
  have hnorm : ∀ r : ℕ, ∫ v : ℝ, ‖H r (v / ((r : ℝ) + 1))‖ =
      (1 / ((r : ℝ) + 1)) * ∫ y : ℝ, Real.exp (-(((r : ℝ) + 1) * s.re) * y) *
        invertedDensity μ ν γ y := by
    intro r
    rw [Measure.integral_comp_div (fun y => ‖H r y‖), abs_of_pos (by positivity), smul_eq_mul,
      ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hH]
    rw [norm_div, norm_cexp_mul_ofReal, abs_of_nonneg (invertedDensity_nonneg hμ0 hμ2 hp₁ hp₂ h4 y),
      norm_pow, show ‖((r : ℂ) + 1)‖ = (r : ℝ) + 1 by exact_mod_cast Complex.norm_natCast (r + 1)]
    have : (((r : ℂ) + 1) * s).re = ((r : ℝ) + 1) * s.re := by simp
    rw [this]
    field_simp
  have hsum : Summable fun r : ℕ => ∫ v : ℝ, ‖H r (v / ((r : ℝ) + 1))‖ := by
    set q := Real.exp (-(s.re * cutPoint μ)) with hq
    have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    refine Summable.of_nonneg_of_le (fun r => integral_nonneg fun v => norm_nonneg _)
      (fun r => ?_) ((summable_geometric_of_lt_one (Real.exp_pos _).le hq1).mul_left
        (Real.exp (cutPoint μ) / (s.re - 1)))
    rw [hnorm r]
    have hσ : 1 < ((r : ℝ) + 1) * s.re := by
      nlinarith [(r.cast_nonneg : (0 : ℝ) ≤ r)]
    have hb := integral_exp_mul_invertedDensity_le (γ := γ) hμ0 hμ2 hp₁ hp₂ h4 hσ
    have hden : s.re - 1 ≤ ((r : ℝ) + 1) * s.re - 1 := by
      nlinarith [(r.cast_nonneg : (0 : ℝ) ≤ r)]
    have hexp : Real.exp (-(((r : ℝ) + 1) * s.re - 1) * cutPoint μ) =
        Real.exp (cutPoint μ) * q ^ (r + 1) := by
      rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
    calc 1 / ((r : ℝ) + 1) * ∫ y, Real.exp (-(((r : ℝ) + 1) * s.re) * y) *
          invertedDensity μ ν γ y
        ≤ 1 * (Real.exp (-(((r : ℝ) + 1) * s.re - 1) * cutPoint μ) /
            (((r : ℝ) + 1) * s.re - 1)) := by
          refine mul_le_mul ?_ hb (integral_nonneg fun y => mul_nonneg (Real.exp_pos _).le
            (invertedDensity_nonneg hμ0 hμ2 hp₁ hp₂ h4 y)) zero_le_one
          rw [div_le_one (by positivity)]; linarith [(r.cast_nonneg : (0 : ℝ) ≤ r)]
      _ ≤ Real.exp (cutPoint μ) * q ^ (r + 1) / (s.re - 1) := by
          rw [one_mul, hexp]
          exact div_le_div_of_nonneg_left (by positivity) (by linarith) hden
      _ = Real.exp (cutPoint μ) / (s.re - 1) * q ^ r * q := by ring
      _ ≤ Real.exp (cutPoint μ) / (s.re - 1) * q ^ r * 1 :=
          mul_le_mul_of_nonneg_left hq1.le (mul_nonneg (div_nonneg (Real.exp_pos _).le
            (by linarith)) (pow_nonneg (Real.exp_pos _).le r))
      _ = Real.exp (cutPoint μ) / (s.re - 1) * q ^ r := mul_one _
  rw [integral_congr_ae (Eventually.of_forall hpt), ← integral_tsum_of_summable_integral_norm
    (fun r => (hint r).comp_div (hr0 r)) hsum]
  refine tsum_congr fun r => ?_
  rw [Measure.integral_comp_div (H r), abs_of_pos (by positivity), Complex.real_smul]
  simp only [hH]
  rw [integral_div]
  push_cast
  field_simp

/-! ## The head `I₀` and the zeta function of `w̃` -/

/-- The head `I₀(s) = ∫_0^{u₀} e^{-sv} w(v) dv`. -/
def headLaplace (μ ν γ : ℝ) (s : ℂ) : ℂ :=
  ∫ v in Ioc 0 (cutPoint μ), cexp (-s * v) * (primeDensity μ ν γ v : ℂ)

theorem integrableOn_laplace_primeDensity {μ ν γ : ℝ} (hlow : 0 ≤ 3 * μ - 1 - ν)
    (hhigh : 0 ≤ 3 * μ - 1 + ν) (h4 : 0 ≤ 4 * μ - 1) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun v : ℝ => cexp (-(s * v)) * (primeDensity μ ν γ v : ℂ)) (Ioi 0) := by
  have hb : 0 < (s - (1 - μ)).re := by
    simpa using re_sub_pos (a := 1 - μ) (by linarith) hs
  have h1 : 0 < (s - 1).re := by simpa using re_sub_pos (a := 1) le_rfl hs
  have hm : 0 < (s - (1 - μ) - γ * I).re := by simpa using hb
  have hp : 0 < (s - (1 - μ) + γ * I).re := by simpa using hb
  have hl : 0 < (s + (3 * μ - 1 - ν)).re := by
    simpa using re_add_pos (a := 3 * μ - 1 - ν) hlow hs
  have hh : 0 < (s + (3 * μ - 1 + ν)).re := by
    simpa using re_add_pos (a := 3 * μ - 1 + ν) hhigh hs
  have hq : 0 < (s + (4 * μ - 1)).re := by
    simpa using re_add_pos (a := 4 * μ - 1) h4 hs
  refine ((GaloisForLFunctions.HTGeometry.integrableOn_frullani h1 hm).add
    ((GaloisForLFunctions.HTGeometry.integrableOn_frullani hl hp).add
      (GaloisForLFunctions.HTGeometry.integrableOn_frullani hh hq))).congr_fun
    (fun t ht => (cexp_mul_primeDensity μ ν γ s ht).symm) measurableSet_Ioi

theorem integrableOn_primeDensity_head {μ ν γ : ℝ} (hlow : 0 ≤ 3 * μ - 1 - ν)
    (hhigh : 0 ≤ 3 * μ - 1 + ν) (h4 : 0 ≤ 4 * μ - 1) :
    IntegrableOn (fun v : ℝ => (primeDensity μ ν γ v : ℂ)) (Ioc 0 (cutPoint μ)) := by
  have h2 := (integrableOn_laplace_primeDensity (γ := γ) hlow hhigh h4
    (s := 2) (by norm_num)).mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) (cutPoint μ) ⊆ Ioi 0)
  have hb : IntegrableOn (fun v : ℝ => cexp (2 * v) * (cexp (-(2 * v)) *
      (primeDensity μ ν γ v : ℂ))) (Ioc 0 (cutPoint μ)) :=
    h2.bdd_mul (f := fun v : ℝ => cexp (2 * v)) (c := Real.exp (2 * cutPoint μ))
    (by fun_prop : Continuous fun v : ℝ => cexp (2 * v)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun v hv => by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      norm_num
      exact hv.2))
  refine IntegrableOn.congr_fun hb (fun v _ => ?_) measurableSet_Ioc
  rw [← mul_assoc, ← Complex.exp_add]
  ring_nf
  simp

/-- `I₀` is entire. -/
theorem differentiable_headLaplace {μ ν γ : ℝ} (hμ0 : 0 < μ) (hlow : 0 ≤ 3 * μ - 1 - ν)
    (hhigh : 0 ≤ 3 * μ - 1 + ν) (h4 : 0 ≤ 4 * μ - 1) :
    Differentiable ℂ (headLaplace μ ν γ) :=
  RHTower.differentiable_compactLaplaceIntegral le_rfl (div_pos (by norm_num) hμ0).le
    (integrableOn_primeDensity_head hlow hhigh h4)

/-- The mass `∫_0^{u₀} w` of the head. -/
def headMass (μ ν γ : ℝ) : ℝ := ∫ v in Ioc 0 (cutPoint μ), primeDensity μ ν γ v

/-- `‖I₀(s)‖ ≤ ∫_0^{u₀} w` on `Re s ≥ 0`. -/
theorem norm_headLaplace_le {μ ν γ : ℝ} (hμ0 : 0 < μ) (hlow : 0 ≤ 3 * μ - 1 - ν)
    (hhigh : 0 ≤ 3 * μ - 1 + ν) (h4 : 0 ≤ 4 * μ - 1) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖headLaplace μ ν γ s‖ ≤ headMass μ ν γ := by
  have hi : IntegrableOn (fun v => ‖(primeDensity μ ν γ v : ℂ)‖) (Ioc 0 (cutPoint μ)) :=
    (integrableOn_primeDensity_head (γ := γ) hlow hhigh h4).norm
  have hpos : ∀ v ∈ Ioc 0 (cutPoint μ), ‖(primeDensity μ ν γ v : ℂ)‖ = primeDensity μ ν γ v :=
    fun v hv => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (primeDensity_nonneg hμ0.le hv.1)]
  have hi' : IntegrableOn (primeDensity μ ν γ) (Ioc 0 (cutPoint μ)) :=
    IntegrableOn.congr_fun hi hpos measurableSet_Ioc
  refine norm_integral_le_of_norm_le hi' ((ae_restrict_iff' measurableSet_Ioc).mpr
    (Eventually.of_forall fun v hv => ?_))
  rw [norm_mul, Complex.norm_exp, hpos v hv]
  have : (-s * (v : ℂ)).re = -(s.re * v) := by simp
  rw [this]
  exact mul_le_of_le_one_left (primeDensity_nonneg hμ0.le hv.1)
    (Real.exp_le_one_iff.mpr (by nlinarith [hv.1]))

/-- **The zeta function of the cut density**: `exp (∫ e^{-sv} w̃) = ζ_c(s) e^{-I₀(s)}`. -/
theorem cexp_laplace_cutDensity {μ ν γ : ℝ} (hμ0 : 0 < μ) (hlow : 0 ≤ 3 * μ - 1 - ν)
    (hhigh : 0 ≤ 3 * μ - 1 + ν) (h4 : 0 ≤ 4 * μ - 1) {s : ℂ} (hs : 1 < s.re) :
    cexp (∫ v : ℝ, cexp (-(s * v)) * (cutDensity μ ν γ v : ℂ)) =
      overRegularZeta μ ν γ s * cexp (-headLaplace μ ν γ s) := by
  have hu0 : 0 ≤ cutPoint μ := (div_pos (by norm_num) hμ0).le
  have hint := integrableOn_laplace_primeDensity (γ := γ) hlow hhigh h4 hs
  have hsplit : ∫ v in Ioi (0 : ℝ), cexp (-(s * v)) * (primeDensity μ ν γ v : ℂ) =
      headLaplace μ ν γ s + ∫ v : ℝ, cexp (-(s * v)) * (cutDensity μ ν γ v : ℂ) := by
    rw [← Ioc_union_Ioi_eq_Ioi hu0, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hu0))]
    congr 1
    · unfold headLaplace
      exact setIntegral_congr_fun measurableSet_Ioc fun v _ => by rw [neg_mul]
    · rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      dsimp only
      unfold cutDensity
      by_cases hv : v ∈ Ici (cutPoint μ)
      · rw [indicator_of_mem hv, indicator_of_mem hv]
      · rw [indicator_of_notMem hv, indicator_of_notMem hv]; simp
  have h := cexp_integral_primeDensity (γ := γ) hlow hhigh h4 hs
  rw [hsplit, Complex.exp_add] at h
  rw [← h, mul_comm (cexp (headLaplace μ ν γ s)), mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, mul_one]

end GaloisForLFunctions.EulerFETransportTheory.MobiusInverted
