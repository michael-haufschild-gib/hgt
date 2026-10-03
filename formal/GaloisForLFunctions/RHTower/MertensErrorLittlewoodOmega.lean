import GaloisForLFunctions.RHTower.MertensProductLaplace
import GaloisForLFunctions.RHTower.VonKochChebyshevBound
import GaloisForLFunctions.RHTower.PrimeCountingLogIntegralSignChange

/-!
# Littlewood's theorem for the Mertens error

Let `R(x) = Σ_{n ≤ x} Λ(n)/(n log n) - log log x - γ`.  Abel summation against `ψ` and the change
of variables `t = e^s` give, for `T ≥ log 2`,

```text
R(e^T) = (ψ(e^T) - e^T)/(e^T T) + c₀ - ∫_{log 2}^T (e^s - ψ(e^s)) w(s) ds,   w(s) = (1+s)e^{-s}/s²,
```

with `c₀ = 1/log 2 - log log 2 - γ`.  Under the Riemann hypothesis the primitive
`P(s) = ∫_0^s (e^r - ψ(e^r)) dr` is `O(e^{s/2})`, and integration by parts against `w` bounds every
`∫_T^U (e^s - ψ(e^s)) w(s) ds` by `8B e^{-T/2}/T`.  Since `R` changes sign infinitely often
(`frequently_rpow_lt_mertensError`, `frequently_mertensError_lt_neg_rpow`) and
`(ψ(x) - x)/(x log x) → 0`, the remainder itself is `O(1/(√x log x))`:

```text
|R(x) - (ψ(x) - x)/(x log x)| ≤ C/(√x log x)        (RH).
```

Littlewood's theorem for `ψ` then gives `R(x) = Ω±(logloglog x/(√x log x))` under the Riemann
hypothesis, and Landau's theorem (`riemannHypothesis_of_mertensError_le_sqrt`) gives it otherwise.
-/

open MeasureTheory Set Filter Topology
open ArithmeticFunction (vonMangoldt)
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Abel summation -/

theorem mertensPowerSum_eq_sum_Icc_zero (x : ℝ) :
    mertensPowerSum x
      = ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, 1 / ((k : ℝ) * Real.log k) * vonMangoldt k := by
  have hsub : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.Icc 0 ⌊x⌋₊ := Finset.Icc_subset_Icc_left (by norm_num)
  have hzero : ∀ k ∈ Finset.Icc 0 ⌊x⌋₊, k ∉ Finset.Icc 1 ⌊x⌋₊ →
      1 / ((k : ℝ) * Real.log k) * vonMangoldt k = 0 := by
    intro k hk hk'
    have : k = 0 := by simp only [Finset.mem_Icc] at hk hk'; omega
    subst this; simp
  rw [← Finset.sum_subset hsub hzero]
  unfold mertensPowerSum
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold eulerLogCoeffReal
  rw [div_div]; ring

/-- The weight `1/(t log t)` and its derivative `-(1 + log t)/(t log t)²` for `t > 1`. -/
theorem hasDerivAt_inv_mul_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ => 1 / (t * Real.log t))
      (-((1 + Real.log t) / (t ^ 2 * Real.log t ^ 2))) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h1 : HasDerivAt (fun t : ℝ => t * Real.log t) (1 * Real.log t + t * t⁻¹) t :=
    (hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)
  have h2 := h1.inv (mul_ne_zero ht0 hl)
  simp only [one_div]
  refine h2.congr_deriv ?_
  field_simp
  ring

theorem continuousOn_weight_deriv {x : ℝ} :
    ContinuousOn (fun t : ℝ => -((1 + Real.log t) / (t ^ 2 * Real.log t ^ 2))) (Icc 2 x) := by
  refine ((continuousOn_const.add (Real.continuousOn_log.mono ?_)).div
    ((continuousOn_id.pow 2).mul ((Real.continuousOn_log.mono ?_).pow 2)) ?_).neg
  · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [ht.1]
  · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [ht.1]
  · intro t ht
    have h1 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have h2 : 0 < t := by linarith [ht.1]
    exact mul_ne_zero (pow_ne_zero 2 h2.ne') (pow_ne_zero 2 h1.ne')

/-- **Abel summation.**  `A(x) = ψ(x)/(x log x) + ∫_2^x ψ(t)(1 + log t)/(t log t)² dt`. -/
theorem mertensPowerSum_eq_abel (x : ℝ) :
    mertensPowerSum x = Chebyshev.psi x / (x * Real.log x)
      + ∫ t in Ioc 2 x, Chebyshev.psi t * ((1 + Real.log t) / (t ^ 2 * Real.log t ^ 2)) := by
  have hd : ∀ t ∈ Icc (2 : ℝ) x, HasDerivAt (fun t : ℝ => 1 / (t * Real.log t))
      (-((1 + Real.log t) / (t ^ 2 * Real.log t ^ 2))) t :=
    fun t ht => hasDerivAt_inv_mul_log (by linarith [ht.1])
  have hint : IntegrableOn (deriv fun t : ℝ => 1 / (t * Real.log t)) (Icc 2 x) :=
    (continuousOn_weight_deriv.integrableOn_Icc).congr_fun
      (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₁ (c := fun k => vonMangoldt k)
    (f := fun t : ℝ => 1 / (t * Real.log t)) (by simp) (by simp) x
    (fun t ht => (hd t ht).differentiableAt) hint
  rw [mertensPowerSum_eq_sum_Icc_zero, h, ← Chebyshev.psi_eq_sum_Icc]
  have hcongr : ∫ t in Ioc 2 x, deriv (fun t : ℝ => 1 / (t * Real.log t)) t
        * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, vonMangoldt k
      = ∫ t in Ioc 2 x, -(Chebyshev.psi t * ((1 + Real.log t) / (t ^ 2 * Real.log t ^ 2))) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv, ← Chebyshev.psi_eq_sum_Icc]
    ring
  rw [hcongr, integral_neg]
  ring

/-! ## The logarithmic variable -/

/-- The weight `w(s) = (1 + s) e^{-s}/s²`. -/
def mertensAbelWeight (s : ℝ) : ℝ := (1 + s) * Real.exp (-s) / s ^ 2

theorem integral_psi_weight_eq_log_variable {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in Ioc 2 x, Chebyshev.psi t * ((1 + Real.log t) / (t ^ 2 * Real.log t ^ 2))
      = ∫ s in (Real.log 2)..(Real.log x), Chebyshev.psi (Real.exp s) * mertensAbelWeight s := by
  have hl : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  rw [intervalIntegral.integral_of_le hl, ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc]
  have himg : Icc (2 : ℝ) x = Real.exp '' Icc (Real.log 2) (Real.log x) := by
    rw [Real.image_exp_Icc, Real.exp_log (by norm_num), Real.exp_log (by linarith)]
  rw [himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun s _ => (Real.hasDerivAt_exp s).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  have hs0 : 0 < s := lt_of_lt_of_le (Real.log_pos (by norm_num)) hs.1
  rw [abs_of_pos (Real.exp_pos s), smul_eq_mul, Real.log_exp, mertensAbelWeight, Real.exp_neg]
  have he := (Real.exp_pos s).ne'
  field_simp

theorem continuousOn_mertensAbelWeight {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn mertensAbelWeight (uIcc a b) := by
  rw [uIcc_of_le hab]
  unfold mertensAbelWeight
  exact ((continuousOn_const.add continuousOn_id).mul
    (Real.continuous_exp.comp continuous_neg).continuousOn).div (continuousOn_id.pow 2)
    fun s hs => pow_ne_zero 2 (lt_of_lt_of_le ha hs.1).ne'

/-- `∫_a^T (1 + s)/s² ds = log T - 1/T - log a + 1/a`. -/
theorem integral_one_add_div_sq {a T : ℝ} (ha : 0 < a) (haT : a ≤ T) :
    ∫ s in a..T, (1 + s) / s ^ 2 = Real.log T - 1 / T - (Real.log a - 1 / a) := by
  have hpos : ∀ s ∈ uIcc a T, 0 < s := fun s hs => by
    rw [uIcc_of_le haT] at hs; linarith [hs.1]
  have hd : ∀ s ∈ uIcc a T, HasDerivAt (fun s : ℝ => Real.log s - 1 / s) ((1 + s) / s ^ 2) s := by
    intro s hs
    have hs0 := (hpos s hs).ne'
    have h := (Real.hasDerivAt_log hs0).sub (hasDerivAt_inv hs0)
    simp only [one_div]
    refine h.congr_deriv ?_
    field_simp
    ring
  have hc : ContinuousOn (fun s : ℝ => (1 + s) / s ^ 2) (uIcc a T) :=
    (continuousOn_const.add continuousOn_id).div (continuousOn_id.pow 2)
      fun s hs => pow_ne_zero 2 (hpos s hs).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]

/-- **The exact Mertens remainder.**  For `T ≥ log 2`,
`R(e^T) = (ψ(e^T) - e^T)/(e^T T) + c₀ - ∫_{log 2}^T (e^s - ψ(e^s)) w(s) ds`. -/
theorem mertensError_exp_eq {T : ℝ} (hT : Real.log 2 ≤ T) :
    mertensError (Real.exp T) = (Chebyshev.psi (Real.exp T) - Real.exp T) / (Real.exp T * T)
      + (1 / Real.log 2 - Real.log (Real.log 2) - Real.eulerMascheroniConstant)
      - ∫ s in (Real.log 2)..T,
          (Real.exp s - Chebyshev.psi (Real.exp s)) * mertensAbelWeight s := by
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hT0 : 0 < T := lt_of_lt_of_le ha hT
  have hx2 : 2 ≤ Real.exp T := by
    rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num)]; exact Real.exp_le_exp.mpr hT
  have hw := continuousOn_mertensAbelWeight ha hT
  have hi1 : IntervalIntegrable (fun s => (1 + s) / s ^ 2) volume (Real.log 2) T := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (continuousOn_const.add continuousOn_id).div (continuousOn_id.pow 2) fun s hs => ?_
    rw [uIcc_of_le hT] at hs
    exact pow_ne_zero 2 (lt_of_lt_of_le ha hs.1).ne'
  have hi2 : IntervalIntegrable (fun s => (Real.exp s - Chebyshev.psi (Real.exp s))
      * mertensAbelWeight s) volume (Real.log 2) T :=
    (intervalIntegrable_chebyshevDeficit _ _).mul_continuousOn hw
  have hsplit : ∫ s in (Real.log 2)..T, Chebyshev.psi (Real.exp s) * mertensAbelWeight s
      = (∫ s in (Real.log 2)..T, (1 + s) / s ^ 2)
        - ∫ s in (Real.log 2)..T,
            (Real.exp s - Chebyshev.psi (Real.exp s)) * mertensAbelWeight s := by
    rw [← intervalIntegral.integral_sub hi1 hi2]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hT] at hs
    have hs0 : s ≠ 0 := (lt_of_lt_of_le ha hs.1).ne'
    simp only [mertensAbelWeight, Real.exp_neg]
    have he := (Real.exp_pos s).ne'
    field_simp
    ring
  unfold mertensError
  rw [mertensPowerSum_eq_abel, integral_psi_weight_eq_log_variable hx2, Real.log_exp, hsplit,
    integral_one_add_div_sq ha hT]
  have he := (Real.exp_pos T).ne'
  field_simp
  ring

/-! ## The tail under a primitive bound -/

theorem hasDerivAt_mertensAbelWeight {s : ℝ} (hs : 0 < s) :
    HasDerivAt mertensAbelWeight (-(Real.exp (-s) * (s ^ 2 + 2 * s + 2) / s ^ 3)) s := by
  have hs0 := hs.ne'
  have h1 : HasDerivAt (fun s : ℝ => (1 + s) * Real.exp (-s))
      (1 * Real.exp (-s) + (1 + s) * (Real.exp (-s) * (-1))) s := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-s) * (-1)) s :=
      (hasDerivAt_neg s).exp
    exact ((hasDerivAt_id s).const_add 1).mul he
  have h := h1.div (hasDerivAt_pow 2 s) (pow_ne_zero 2 hs0)
  unfold mertensAbelWeight
  refine h.congr_deriv ?_
  field_simp
  ring

theorem exp_neg_half_div_antitone {T U : ℝ} (hT : 2 ≤ T) (hTU : T ≤ U) :
    Real.exp (-U / 2) / U ≤ Real.exp (-T / 2) / T := by
  have hT0 : 0 < T := by linarith
  rw [div_le_div_iff₀ (by linarith) hT0]
  have h1 : Real.exp (-U / 2) ≤ Real.exp (-T / 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 := Real.exp_pos (-U / 2)
  nlinarith

/-- A primitive bound `|P(t)| ≤ B e^{t/2}` bounds the tail weight integral. -/
theorem abs_integral_deficit_mertensAbelWeight_le {B T U : ℝ} (hT : 4 ≤ T) (hTU : T ≤ U)
    (hB : ∀ t : ℝ, 0 ≤ t → |ccmLogChebyshevDeficitPrimitive t| ≤ B * Real.exp (t / 2)) :
    |∫ s in T..U, (Real.exp s - Chebyshev.psi (Real.exp s)) * mertensAbelWeight s|
      ≤ 12 * B * (Real.exp (-T / 2) / T) := by
  have hT0 : 0 < T := by linarith
  have hB0 : 0 ≤ B := by
    have := (abs_nonneg _).trans (hB 0 le_rfl)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  set f : ℝ → ℝ := fun r => Real.exp r - Chebyshev.psi (Real.exp r) with hf
  set Q : ℝ → ℝ := fun s => ∫ r in T..s, f r with hQ
  have hi : IntervalIntegrable f volume T U := intervalIntegrable_chebyshevDeficit T U
  have hQac : AbsolutelyContinuousOnInterval Q T U :=
    hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  -- `Q(s) = P(s) - P(T)` and `|Q(s)| ≤ 2B e^{s/2}`
  have hQb : ∀ s, T ≤ s → |Q s| ≤ 2 * B * Real.exp (s / 2) := by
    intro s hs
    have hQP : Q s = ccmLogChebyshevDeficitPrimitive s - ccmLogChebyshevDeficitPrimitive T := by
      simp only [hQ, ccmLogChebyshevDeficitPrimitive]
      rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_chebyshevDeficit 0 s)
        (intervalIntegrable_chebyshevDeficit 0 T)]
    have h1 := hB s (by linarith)
    have h2 := hB T hT0.le
    have h3 : Real.exp (T / 2) ≤ Real.exp (s / 2) := Real.exp_le_exp.mpr (by linarith)
    rw [hQP]
    calc |ccmLogChebyshevDeficitPrimitive s - ccmLogChebyshevDeficitPrimitive T|
        ≤ |ccmLogChebyshevDeficitPrimitive s| + |ccmLogChebyshevDeficitPrimitive T| := abs_sub _ _
      _ ≤ B * Real.exp (s / 2) + B * Real.exp (T / 2) := add_le_add h1 h2
      _ ≤ 2 * B * Real.exp (s / 2) := by nlinarith
  have hwd : ∀ s ∈ uIcc T U, HasDerivAt mertensAbelWeight
      (-(Real.exp (-s) * (s ^ 2 + 2 * s + 2) / s ^ 3)) s := fun s hs =>
    hasDerivAt_mertensAbelWeight (by rw [uIcc_of_le hTU] at hs; linarith [hs.1])
  have hwcd : ContDiffOn ℝ 1 mertensAbelWeight (uIcc T U) := by
    rw [uIcc_of_le hTU]
    unfold mertensAbelWeight
    refine ContDiffOn.div ?_ (contDiffOn_id.pow 2) fun s hs => pow_ne_zero 2 (by
      simp; linarith [hs.1])
    exact (contDiffOn_const.add contDiffOn_id).mul (Real.contDiff_exp.comp contDiff_neg).contDiffOn
  have hparts := hwcd.absolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hQac
  have hleft : (∫ s in T..U, mertensAbelWeight s * deriv Q s)
      = ∫ s in T..U, f s * mertensAbelWeight s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hi.ae_hasDerivAt_integral] with s hs hmem
    have hd : HasDerivAt Q (f s) s := hs (uIoc_subset_uIcc hmem) T left_mem_uIcc
    rw [hd.deriv, mul_comm]
  have hright : (∫ s in T..U, deriv mertensAbelWeight s * Q s)
      = ∫ s in T..U, -(Real.exp (-s) * (s ^ 2 + 2 * s + 2) / s ^ 3) * Q s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [(hwd s hs).deriv]
  have hQT : Q T = 0 := by simp [hQ]
  rw [hleft, hright, hQT, mul_zero, sub_zero] at hparts
  rw [hparts]
  -- the boundary term at `U`
  have hU0 : 0 < U := by linarith
  have hexpU : Real.exp (-U) * Real.exp (U / 2) = Real.exp (-U / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hwU : |mertensAbelWeight U * Q U| ≤ 4 * B * (Real.exp (-T / 2) / T) := by
    have hw0 : 0 ≤ mertensAbelWeight U := by unfold mertensAbelWeight; positivity
    rw [abs_mul, abs_of_nonneg hw0]
    have h1 := hQb U hTU
    have h3 : (1 + U) / U ≤ 2 := by rw [div_le_iff₀ hU0]; linarith
    have hmono := exp_neg_half_div_antitone (by linarith) hTU
    calc mertensAbelWeight U * |Q U| ≤ mertensAbelWeight U * (2 * B * Real.exp (U / 2)) :=
          mul_le_mul_of_nonneg_left h1 hw0
      _ = 2 * B * ((1 + U) / U) * (Real.exp (-U) * Real.exp (U / 2) / U) := by
          unfold mertensAbelWeight; field_simp
      _ = 2 * B * ((1 + U) / U) * (Real.exp (-U / 2) / U) := by rw [hexpU]
      _ ≤ 2 * B * 2 * (Real.exp (-U / 2) / U) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ 2 * B * 2 * (Real.exp (-T / 2) / T) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = 4 * B * (Real.exp (-T / 2) / T) := by ring
  -- the interior integral
  have hint : |∫ s in T..U, -(Real.exp (-s) * (s ^ 2 + 2 * s + 2) / s ^ 3) * Q s|
      ≤ 8 * B * (Real.exp (-T / 2) / T) := by
    have hg : IntervalIntegrable (fun s => 4 * B / T * Real.exp (-s / 2)) volume T U :=
      ((Real.continuous_exp.comp (continuous_neg.div_const 2)).intervalIntegrable _ _).const_mul _
    have hpt : ∀ᵐ s ∂volume, s ∈ Ioc T U →
        ‖-(Real.exp (-s) * (s ^ 2 + 2 * s + 2) / s ^ 3) * Q s‖
          ≤ 4 * B / T * Real.exp (-s / 2) := by
      refine Filter.Eventually.of_forall fun s hs => ?_
      have hs0 : 0 < s := by linarith [hs.1]
      have hsT : T ≤ s := hs.1.le
      have hs4 : 4 ≤ s := le_trans hT hsT
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
      have h1 := hQb s hsT
      have hq : (s ^ 2 + 2 * s + 2) / s ^ 3 ≤ 2 / s := by
        rw [div_le_div_iff₀ (by positivity) hs0]
        nlinarith
      have hexp : Real.exp (-s) * Real.exp (s / 2) = Real.exp (-s / 2) := by
        rw [← Real.exp_add]; ring_nf
      have h2s : 2 / s ≤ 2 / T := div_le_div_of_nonneg_left (by norm_num) hT0 hsT
      calc Real.exp (-s) * (s ^ 2 + 2 * s + 2) / s ^ 3 * |Q s|
          ≤ Real.exp (-s) * (s ^ 2 + 2 * s + 2) / s ^ 3 * (2 * B * Real.exp (s / 2)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * B * (Real.exp (-s) * Real.exp (s / 2)) * ((s ^ 2 + 2 * s + 2) / s ^ 3) := by ring
        _ = 2 * B * Real.exp (-s / 2) * ((s ^ 2 + 2 * s + 2) / s ^ 3) := by rw [hexp]
        _ ≤ 2 * B * Real.exp (-s / 2) * (2 / T) :=
            mul_le_mul_of_nonneg_left (hq.trans h2s) (by positivity)
        _ = 4 * B / T * Real.exp (-s / 2) := by ring
    have hle := intervalIntegral.norm_integral_le_of_norm_le hTU hpt hg
    rw [Real.norm_eq_abs] at hle
    refine hle.trans ?_
    have hFTC : ∫ s in T..U, 4 * B / T * Real.exp (-s / 2)
        = 4 * B / T * (2 * (Real.exp (-T / 2) - Real.exp (-U / 2))) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hd : ∀ s ∈ uIcc T U, HasDerivAt (fun s : ℝ => -2 * Real.exp (-s / 2))
          (Real.exp (-s / 2)) s := by
        intro s _
        have := ((hasDerivAt_neg s).div_const 2).exp.const_mul (-2)
        refine this.congr_deriv ?_
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((Real.continuous_exp.comp (continuous_neg.div_const 2)).intervalIntegrable _ _)]
      ring
    rw [hFTC]
    have hEU := Real.exp_pos (-U / 2)
    have : 4 * B / T * (2 * (Real.exp (-T / 2) - Real.exp (-U / 2)))
        ≤ 4 * B / T * (2 * Real.exp (-T / 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc _ ≤ 4 * B / T * (2 * Real.exp (-T / 2)) := this
      _ = 8 * B * (Real.exp (-T / 2) / T) := by ring
  calc |mertensAbelWeight U * Q U
        - ∫ s in T..U, -(Real.exp (-s) * (s ^ 2 + 2 * s + 2) / s ^ 3) * Q s|
      ≤ |mertensAbelWeight U * Q U|
        + |∫ s in T..U, -(Real.exp (-s) * (s ^ 2 + 2 * s + 2) / s ^ 3) * Q s| := abs_sub _ _
    _ ≤ 4 * B * (Real.exp (-T / 2) / T) + 8 * B * (Real.exp (-T / 2) / T) := add_le_add hwU hint
    _ = 12 * B * (Real.exp (-T / 2) / T) := by ring


/-! ## The remainder under the Riemann hypothesis -/

/-- The remainder `G(T) = R(e^T) - (ψ(e^T) - e^T)/(e^T T)`. -/
def mertensErrorRemainder (T : ℝ) : ℝ :=
  mertensError (Real.exp T) - (Chebyshev.psi (Real.exp T) - Real.exp T) / (Real.exp T * T)

theorem mertensErrorRemainder_sub_eq {T U : ℝ} (hT : Real.log 2 ≤ T) (hTU : T ≤ U) :
    mertensErrorRemainder T - mertensErrorRemainder U
      = ∫ s in T..U, (Real.exp s - Chebyshev.psi (Real.exp s)) * mertensAbelWeight s := by
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hU : Real.log 2 ≤ U := le_trans hT hTU
  have hiT := (intervalIntegrable_chebyshevDeficit (Real.log 2) T).mul_continuousOn
    (continuousOn_mertensAbelWeight ha hT)
  have hiU := (intervalIntegrable_chebyshevDeficit (Real.log 2) U).mul_continuousOn
    (continuousOn_mertensAbelWeight ha hU)
  unfold mertensErrorRemainder
  rw [mertensError_exp_eq hT, mertensError_exp_eq hU, ← intervalIntegral.integral_interval_sub_left
    hiU hiT]
  ring

/-- `(ψ(x) - x)/(x log x) → 0` under the Riemann hypothesis. -/
theorem eventually_abs_chebyshevError_div_lt_of_riemannHypothesis (hRH : RiemannHypothesis)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, |(Chebyshev.psi x - x) / (x * Real.log x)| < η := by
  set K : ℝ := 200 * (xiLineTwoLogDerivConstant + 2) with hK
  have hK0 : 0 ≤ K := by
    have := (abs_nonneg _).trans (abs_chebyshevPsi_sub_le_of_riemannHypothesis hRH
      (le_refl (16 : ℝ)))
    have h16 : 0 < Real.sqrt 16 * Real.log 16 ^ 2 := by
      have : 0 < Real.log 16 := Real.log_pos (by norm_num)
      positivity
    rw [mul_assoc] at this
    exact nonneg_of_mul_nonneg_left this h16
  have hε : 0 < η / (K + 1) := by positivity
  filter_upwards [(isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound hε,
    eventually_ge_atTop (16 : ℝ)] with x hx hx16
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlx,
    abs_of_nonneg (Real.rpow_nonneg hx0.le _), ← Real.sqrt_eq_rpow] at hx
  have hE := abs_chebyshevPsi_sub_le_of_riemannHypothesis hRH hx16
  rw [← hK] at hE
  rw [abs_div, abs_of_pos (mul_pos hx0 hlx), div_lt_iff₀ (mul_pos hx0 hlx)]
  calc |Chebyshev.psi x - x| ≤ K * Real.sqrt x * Real.log x ^ 2 := hE
    _ = K * Real.log x * (Real.log x * Real.sqrt x) := by ring
    _ ≤ K * Real.log x * (η / (K + 1) * Real.sqrt x * Real.sqrt x) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith
    _ = K / (K + 1) * η * (Real.sqrt x * Real.sqrt x * Real.log x) := by field_simp
    _ = K / (K + 1) * η * (x * Real.log x) := by rw [Real.mul_self_sqrt hx0.le]
    _ < η * (x * Real.log x) := by
        have h1 : K / (K + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
        have h2 : 0 < η * (x * Real.log x) := by positivity
        nlinarith

/-- **Under the Riemann hypothesis the Mertens error is the Chebyshev error.**
`|R(x) - (ψ(x) - x)/(x log x)| ≤ C/(√x log x)` for `x ≥ e⁴`. -/
theorem exists_abs_mertensError_sub_le_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, Real.exp 4 ≤ x →
      |mertensError x - (Chebyshev.psi x - x) / (x * Real.log x)|
        ≤ C / (Real.sqrt x * Real.log x) := by
  obtain ⟨B, hB0, hB⟩ := riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound.mp hRH
  refine ⟨12 * B, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 4) hx
  set T : ℝ := Real.log x with hTdef
  have hT4 : 4 ≤ T := by rw [hTdef, Real.le_log_iff_exp_le hx0]; exact hx
  have hT0 : 0 < T := by linarith
  have hl2 : Real.log 2 ≤ T := by have := Real.log_two_lt_d9; linarith
  have hxT : Real.exp T = x := Real.exp_log hx0
  have hGT : mertensErrorRemainder T
      = mertensError x - (Chebyshev.psi x - x) / (x * Real.log x) := by
    rw [mertensErrorRemainder, hxT]
  -- the Cauchy bound
  have hcauchy : ∀ U, T ≤ U → |mertensErrorRemainder T - mertensErrorRemainder U|
      ≤ 12 * B * (Real.exp (-T / 2) / T) := fun U hU => by
    rw [mertensErrorRemainder_sub_eq hl2 hU]
    exact abs_integral_deficit_mertensAbelWeight_le hT4 hU hB
  have hval : 12 * B * (Real.exp (-T / 2) / T) = 12 * B / (Real.sqrt x * Real.log x) := by
    have hs : Real.exp (-T / 2) = (Real.sqrt x)⁻¹ := by
      rw [show -T / 2 = -(1 / 2 * T) by ring, Real.exp_neg, ← sqrt_exp_eq_exp_half_mul, hxT]
    rw [hs, ← hTdef]; field_simp
  rw [← hGT, ← hval]
  -- sign changes of `R`
  have hb : (1 / 4 : ℝ) < zeroReSup := by linarith [half_le_zeroReSup]
  have hpos : ∃ᶠ y : ℝ in atTop, 0 < mertensError y :=
    ((frequently_rpow_lt_mertensError hb).and_eventually (eventually_gt_atTop 0)).mono
      fun y ⟨h, hy⟩ => lt_of_le_of_lt (Real.rpow_nonneg hy.le _) h
  have hneg : ∃ᶠ y : ℝ in atTop, mertensError y < 0 :=
    ((frequently_mertensError_lt_neg_rpow hb).and_eventually (eventually_gt_atTop 0)).mono
      fun y ⟨h, hy⟩ => by have := Real.rpow_nonneg hy.le (1 / 4 - 1); linarith
  have hfar : ∀ η > 0, ∀ᶠ y : ℝ in atTop,
      |(Chebyshev.psi y - y) / (y * Real.log y)| < η ∧ x ≤ y :=
    fun η hη => (eventually_abs_chebyshevError_div_lt_of_riemannHypothesis hRH hη).and
      (eventually_ge_atTop x)
  have hGy : ∀ y, x ≤ y → mertensErrorRemainder (Real.log y)
      = mertensError y - (Chebyshev.psi y - y) / (y * Real.log y) := fun y hy => by
    rw [mertensErrorRemainder, Real.exp_log (lt_of_lt_of_le hx0 hy)]
  have hlogy : ∀ y, x ≤ y → T ≤ Real.log y := fun y hy => Real.log_le_log hx0 hy
  rw [abs_le]
  constructor
  · -- lower bound: compare with a point where `R > 0`
    refine neg_le.mpr (le_of_forall_pos_lt_add fun η hη => ?_)
    obtain ⟨y, ⟨hRy, hsm, hxy⟩⟩ := ((hpos.and_eventually (hfar η hη)).exists)
    have h1 := hcauchy (Real.log y) (hlogy y hxy)
    rw [hGy y hxy, abs_le] at h1
    have h2 := (abs_lt.mp hsm).2
    linarith [h1.2]
  · refine le_of_forall_pos_lt_add fun η hη => ?_
    obtain ⟨y, ⟨hRy, hsm, hxy⟩⟩ := ((hneg.and_eventually (hfar η hη)).exists)
    have h1 := hcauchy (Real.log y) (hlogy y hxy)
    rw [hGy y hxy, abs_le] at h1
    have h2 := (abs_lt.mp hsm).1
    linarith [h1.1]

/-! ## Littlewood's theorem for `R` -/

theorem eventually_littlewood_div_le_rpow :
    ∀ᶠ x : ℝ in atTop, littlewoodConst / 28 * Real.log (Real.log (Real.log x))
        / (Real.sqrt x * Real.log x) ≤ 1 * x ^ (-(1 / 2) : ℝ) := by
  have hc := littlewoodConst_le_one
  have hc0 := littlewoodConst_pos
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 1))] with x hx
  have hee : (1 : ℝ) < Real.exp (Real.exp 1) := Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
  have hx1 : 1 < x := lt_of_lt_of_le hee hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hll : 1 ≤ Real.log (Real.log x) := by
    rw [Real.le_log_iff_exp_le hlx, Real.le_log_iff_exp_le hx0]; exact hx
  have hL3 : Real.log (Real.log (Real.log x)) ≤ Real.log x := by
    have h1 : Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x) := by
      have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hll); linarith
    have h2 : Real.log (Real.log x) ≤ Real.log x := by
      have := Real.log_le_sub_one_of_pos hlx; linarith
    linarith
  have hL30 : 0 ≤ Real.log (Real.log (Real.log x)) := Real.log_nonneg hll
  rw [one_mul, Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, div_le_iff₀ (mul_pos hsx hlx)]
  rw [show (Real.sqrt x)⁻¹ * (Real.sqrt x * Real.log x) = Real.log x by field_simp]
  have : littlewoodConst / 28 ≤ 1 := by linarith
  nlinarith

/-- **Littlewood's theorem for the Mertens error, upper side.**  Unconditionally,
`R(x) > (c/28) logloglog x/(√x log x)` for arbitrarily large `x`, `c = 1/(70π³)`. -/
theorem frequently_littlewood_lt_mertensError :
    ∃ᶠ x : ℝ in atTop, littlewoodConst / 28 * Real.log (Real.log (Real.log x))
      / (Real.sqrt x * Real.log x) < mertensError x := by
  have hc0 := littlewoodConst_pos
  by_cases hRH : RiemannHypothesis
  · obtain ⟨C, hC0, hC⟩ := exists_abs_mertensError_sub_le_of_riemannHypothesis hRH
    refine (frequently_littlewood_lt_chebyshevPsi_sub.and_eventually
      ((eventually_ge_atTop (Real.exp 4)).and (tendsto_logLogLog_atTop.eventually_ge_atTop
        (28 * C / littlewoodConst)))).mono fun x ⟨hψ, hx4, hL⟩ => ?_
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 4) hx4
    have hlx : 0 < Real.log x := by
      rw [Real.log_pos_iff hx0.le]; linarith [Real.add_one_le_exp 4]
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hD : 0 < Real.sqrt x * Real.log x := mul_pos hsx hlx
    have hR := (abs_le.mp (hC x hx4)).1
    have hxx : x * Real.log x = Real.sqrt x * (Real.sqrt x * Real.log x) := by
      rw [← mul_assoc, Real.mul_self_sqrt hx0.le]
    have hE : littlewoodConst / 14 * Real.log (Real.log (Real.log x)) / (Real.sqrt x * Real.log x)
        < (Chebyshev.psi x - x) / (x * Real.log x) := by
      rw [hxx, div_lt_div_iff₀ hD (mul_pos hsx hD)]
      nlinarith
    have hCL : C ≤ littlewoodConst / 28 * Real.log (Real.log (Real.log x)) := by
      rw [div_le_iff₀ hc0] at hL; linarith
    have hsplit : littlewoodConst / 14 * Real.log (Real.log (Real.log x))
          / (Real.sqrt x * Real.log x) - C / (Real.sqrt x * Real.log x)
        ≥ littlewoodConst / 28 * Real.log (Real.log (Real.log x)) / (Real.sqrt x * Real.log x) := by
      rw [ge_iff_le, ← sub_div, div_le_div_iff_of_pos_right hD]
      linarith
    linarith
  · by_contra hno
    rw [Filter.not_frequently] at hno
    exact hRH (riemannHypothesis_of_mertensError_le_sqrt (K := 1) (Or.inl
      ((hno.and eventually_littlewood_div_le_rpow).mono fun x ⟨h1, h2⟩ =>
        le_trans (not_lt.mp h1) h2)))

/-- **Littlewood's theorem for the Mertens error, lower side.**  Unconditionally,
`R(x) < -(c/28) logloglog x/(√x log x)` for arbitrarily large `x`. -/
theorem frequently_mertensError_lt_neg_littlewood :
    ∃ᶠ x : ℝ in atTop, mertensError x
      < -(littlewoodConst / 28 * Real.log (Real.log (Real.log x))
        / (Real.sqrt x * Real.log x)) := by
  have hc0 := littlewoodConst_pos
  by_cases hRH : RiemannHypothesis
  · obtain ⟨C, hC0, hC⟩ := exists_abs_mertensError_sub_le_of_riemannHypothesis hRH
    refine (frequently_chebyshevPsi_sub_lt_littlewood.and_eventually
      ((eventually_ge_atTop (Real.exp 4)).and (tendsto_logLogLog_atTop.eventually_ge_atTop
        (28 * C / littlewoodConst)))).mono fun x ⟨hψ, hx4, hL⟩ => ?_
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 4) hx4
    have hlx : 0 < Real.log x := by
      rw [Real.log_pos_iff hx0.le]; linarith [Real.add_one_le_exp 4]
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hD : 0 < Real.sqrt x * Real.log x := mul_pos hsx hlx
    have hR := (abs_le.mp (hC x hx4)).2
    have hxx : x * Real.log x = Real.sqrt x * (Real.sqrt x * Real.log x) := by
      rw [← mul_assoc, Real.mul_self_sqrt hx0.le]
    have hE : (Chebyshev.psi x - x) / (x * Real.log x)
        < -(littlewoodConst / 14 * Real.log (Real.log (Real.log x))
          / (Real.sqrt x * Real.log x)) := by
      rw [hxx, ← neg_div, div_lt_div_iff₀ (mul_pos hsx hD) hD]
      nlinarith
    have hCL : C ≤ littlewoodConst / 28 * Real.log (Real.log (Real.log x)) := by
      rw [div_le_iff₀ hc0] at hL; linarith
    have hsplit : -(littlewoodConst / 14 * Real.log (Real.log (Real.log x))
          / (Real.sqrt x * Real.log x)) + C / (Real.sqrt x * Real.log x)
        ≤ -(littlewoodConst / 28 * Real.log (Real.log (Real.log x))
          / (Real.sqrt x * Real.log x)) := by
      rw [← neg_div, ← neg_div, ← add_div, div_le_div_iff_of_pos_right hD]
      linarith
    linarith
  · by_contra hno
    rw [Filter.not_frequently] at hno
    exact hRH (riemannHypothesis_of_mertensError_le_sqrt (K := 1) (Or.inr
      ((hno.and eventually_littlewood_div_le_rpow).mono fun x ⟨h1, h2⟩ => by
        have := not_lt.mp h1; linarith)))

/-- **Littlewood's theorem for the Mertens error.**  `R(x) = Ω±(logloglog x/(√x log x))`. -/
theorem mertensError_omega_pm_littlewood :
    (∃ᶠ x : ℝ in atTop, littlewoodConst / 28 * Real.log (Real.log (Real.log x))
      / (Real.sqrt x * Real.log x) < mertensError x) ∧
    ∃ᶠ x : ℝ in atTop, mertensError x
      < -(littlewoodConst / 28 * Real.log (Real.log (Real.log x))
        / (Real.sqrt x * Real.log x)) :=
  ⟨frequently_littlewood_lt_mertensError, frequently_mertensError_lt_neg_littlewood⟩

end

end RHTower
