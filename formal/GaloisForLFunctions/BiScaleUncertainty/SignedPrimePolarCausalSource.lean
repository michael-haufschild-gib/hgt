import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarRampCore
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceParameters
import GaloisForLFunctions.BiScaleUncertainty.ExponentialTentMoments

/-!
# A causal smoothing of the factorial bi-null prime test

For `N ≥ 1` the factorial bi-null test `factorialBiNull N = (L_(4N) - 4 L_(2N) + 4 L_N) / sqrt N`
is built from the rectangle sums `L_K(x) = Σ_(j ≤ K) e^(x/2) 1_[0, log(K/j)](x)`. This module replaces
each rectangle by a clamped linear ramp of collar `ε_N = e^(δ_N) - 1`, `δ_N = log(1 + 1/(4N)) / 3`
(`sourceFactorialRamp`), and then averages the shifted ramp `e^(t/2) R(x - t)` against the exponential
tent probability density on `[0, 2 δ_N]` (`sourceFactorialCausal`). The result is continuous, supported
in `[0, log(4N + 1)]`, agrees with `factorialBiNull N` at every `log n` with `n ≥ 1`, and equals
`e^(x/2) / sqrt N` on the band `[log(2N + 1), log(4N)]`.

## Main results

- `sourceFactorialCausal_at_log`: `sourceFactorialCausal N (log n) = factorialBiNull N (log n)` for all
  `N, n ≥ 1`.
- `sourceFactorialCausal_on_band`: `sourceFactorialCausal N x = e^(x/2) / sqrt N` for
  `log(2N + 1) ≤ x ≤ log(4N)`.
- `hasCompactSupport_sourceFactorialCausal`: the causal source has compact support in
  `[0, log(4N + 1)]`.
- `continuous_sourceFactorialCausal`: the causal source is continuous.

## Hypotheses

All results are unconditional. The only side conditions are `1 ≤ N`, `1 ≤ n`, and the explicit ranges
of the shift `t ∈ [0, 2 δ_N]` and of `x` in the band and tail lemmas.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

/-- Continuous ramp version of the factorial bi-null test: the `(1, -4, 4) / sqrt N` combination of
the smooth factorial lifts at levels `4N, 2N, N` with collar `sourceFactorialCollar N`. -/
def sourceFactorialRamp (N : ℕ) : ℝ → ℝ := rampBiNull (sourceFactorialCollar N) N

/-- Causal source: the average of `e^(t/2) · sourceFactorialRamp N (x - t)` over shifts `t ∈ [0, 2 δ_N]`
against the exponential tent density of width `δ_N = sourceFactorialWidth N`. -/
def sourceFactorialCausal (N : ℕ) (x : ℝ) : ℝ :=
  ∫ t in Icc 0 (2*sourceFactorialWidth N),
    exponentialTentDensity (sourceFactorialWidth N) t *
      (Real.exp (t/2)*sourceFactorialRamp N (x-t))

/-- Collar budget: for `N ≥ 1`, `sourceFactorialCollar N · 4N ≤ 1`. -/
theorem sourceFactorialCollar_budget {N : ℕ} (hN : 1 ≤ N) :
    sourceFactorialCollar N*(4*(N : ℝ)) ≤ 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hd := sourceFactorialWidth_pos hN
  have hb := sourceFactorial_dilated_collar_le (N := N) (t := 0) (by linarith)
  simp only [Real.exp_zero, mul_one] at hb
  have he : sourceFactorialCollar N ≤ 1/(4*(N : ℝ)) := by linarith
  calc
    _ ≤ (1/(4*(N : ℝ)))*(4*(N : ℝ)) := mul_le_mul_of_nonneg_right he (by positivity)
    _ = 1 := by field_simp

theorem sourceFactorialCollar_small_budget {N K : ℕ} (hN : 1 ≤ N) (hK : K ≤ 4*N) :
    sourceFactorialCollar N*(K : ℝ) ≤ 1 := by
  have hk : (K : ℝ) ≤ 4*(N : ℝ) := by exact_mod_cast hK
  exact (mul_le_mul_of_nonneg_left hk (sourceFactorialCollar_pos hN).le).trans
    (sourceFactorialCollar_budget hN)

/-- Shift budget: for `N ≥ 1`, `K ≤ 4N` and `t ≤ 2 δ_N`, `K (1 + ε_N) e^t ≤ K + 1`, so a collar plus a
causal shift never reaches the next integer. -/
theorem sourceFactorial_shift_budget {N K : ℕ} {t : ℝ} (hN : 1 ≤ N) (hK : K ≤ 4*N)
    (ht : t ≤ 2*sourceFactorialWidth N) :
    (K : ℝ)*(1+sourceFactorialCollar N)*Real.exp t ≤ (K : ℝ)+1 := by
  have hb := sourceFactorial_dilated_collar_le (N := N) ht
  have hk := factorialCollar_mul_le_one hN hK
  unfold factorialCollar at hk
  calc
    _ = (K : ℝ)*((1+sourceFactorialCollar N)*Real.exp t) := by ring
    _ ≤ (K : ℝ)*(1+1/(4*(N : ℝ))) := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg K)
    _ ≤ _ := by nlinarith

theorem continuous_sourceFactorialRamp (N : ℕ) : Continuous (sourceFactorialRamp N) :=
  continuous_rampBiNull _ _

theorem hasCompactSupport_sourceFactorialRamp {N : ℕ} (hN : 1 ≤ N) :
    HasCompactSupport (sourceFactorialRamp N) :=
  hasCompactSupport_rampBiNull (sourceFactorialCollar_pos hN) hN (sourceFactorialCollar_budget hN)

theorem sourceFactorialRamp_zero_of_nonpos {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : x ≤ 0) :
    sourceFactorialRamp N x = 0 := rampBiNull_zero_of_nonpos (sourceFactorialCollar_pos hN) N hx

/-- At every integer point `log n` (`n ≥ 1`), each causal shift `t ∈ [0, 2 δ_N]` of the ramp reproduces
the factorial bi-null test exactly: `e^(t/2) R_N(log n - t) = factorialBiNull N (log n)`. -/
theorem sourceFactorialRamp_shift_at_log {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) {t : ℝ}
    (ht : t ∈ Icc 0 (2*sourceFactorialWidth N)) :
    Real.exp (t/2)*sourceFactorialRamp N (Real.log n-t) = factorialBiNull N (Real.log n) := by
  have hl (K : ℕ) (hK : K ≤ 4*N) :
      Real.exp (t/2)*smoothFactorialLift (sourceFactorialCollar N) K (Real.log n-t) =
        factorialLift K (Real.log n) :=
    smoothFactorialLift_shift_at_log (sourceFactorialCollar_pos hN)
      (sourceFactorialCollar_small_budget hN hK) hn ht.1 (sourceFactorial_shift_budget hN hK ht.2)
  have he : Real.exp (t/2)*sourceFactorialRamp N (Real.log n-t) =
      (Real.exp (t/2)*smoothFactorialLift (sourceFactorialCollar N) (4*N) (Real.log n-t)-
        4*(Real.exp (t/2)*smoothFactorialLift (sourceFactorialCollar N) (2*N) (Real.log n-t))+
        4*(Real.exp (t/2)*smoothFactorialLift (sourceFactorialCollar N) N (Real.log n-t)))/Real.sqrt N := by
    unfold sourceFactorialRamp rampBiNull
    ring
  rw [he, hl (4*N) (by omega), hl (2*N) (by omega), hl N (by omega)]
  rfl

/-- For `x ≥ log(4N + 1)` and `t ∈ [0, 2 δ_N]`, the shifted ramp vanishes: `R_N(x - t) = 0`. -/
theorem sourceFactorialRamp_shift_tail {N : ℕ} (hN : 1 ≤ N) {x t : ℝ}
    (ht : t ∈ Icc 0 (2*sourceFactorialWidth N)) (hx : Real.log (4*(N : ℝ)+1) ≤ x) :
    sourceFactorialRamp N (x-t) = 0 := by
  apply rampBiNull_tail_exp (sourceFactorialCollar_pos hN) hN
  have hb := sourceFactorial_shift_budget hN (by omega : 4*N ≤ 4*N) ht.2
  push_cast at hb
  have he := Real.exp_le_exp.mpr hx
  rw [Real.exp_log (by positivity : 0 < 4*(N : ℝ)+1)] at he
  apply (mul_le_mul_iff_left₀ (Real.exp_pos t)).mp
  calc
    _ ≤ 4*(N : ℝ)+1 := hb
    _ ≤ Real.exp x := he
    _ = _ := by rw [← Real.exp_add, sub_add_cancel]

/-- On the top band `log(2N + 1) ≤ x ≤ log(4N)`, every causal shift gives
`e^(t/2) R_N(x - t) = e^(x/2) / sqrt N`. -/
theorem sourceFactorialRamp_shift_band {N : ℕ} (hN : 1 ≤ N) {x t : ℝ}
    (ht : t ∈ Icc 0 (2*sourceFactorialWidth N))
    (hx : x ∈ Icc (Real.log (2*(N : ℝ)+1)) (Real.log (4*(N : ℝ)))) :
    Real.exp (t/2)*sourceFactorialRamp N (x-t) = Real.exp (x/2)/Real.sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := sourceFactorial_shift_budget hN (by omega : 2*N ≤ 4*N) ht.2
  push_cast at hb
  have hlo := Real.exp_le_exp.mpr hx.1
  have hhi := Real.exp_le_exp.mpr hx.2
  rw [Real.exp_log (by positivity : 0 < 2*(N : ℝ)+1)] at hlo
  rw [Real.exp_log (by positivity : 0 < 4*(N : ℝ))] at hhi
  have hlow : 2*(N : ℝ)*(1+sourceFactorialCollar N) ≤ Real.exp (x-t) := by
    apply (mul_le_mul_iff_left₀ (Real.exp_pos t)).mp
    calc
      _ ≤ 2*(N : ℝ)+1 := hb
      _ ≤ Real.exp x := hlo
      _ = _ := by rw [← Real.exp_add, sub_add_cancel]
  have hhigh : Real.exp (x-t) ≤ 4*(N : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith [ht.1])).trans hhi
  change Real.exp (t/2)*rampBiNull _ _ _ = _
  rw [rampBiNull_on_top_band (sourceFactorialCollar_pos hN) hN hlow hhigh]
  rw [← mul_div_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The causal source is continuous, as a parametric integral of a continuous integrand over a
compact shift interval. -/
theorem continuous_sourceFactorialCausal (N : ℕ) : Continuous (sourceFactorialCausal N) := by
  unfold sourceFactorialCausal
  apply continuous_parametric_integral_of_continuous _ isCompact_Icc
  exact ((continuous_exponentialTentDensity _).comp continuous_snd).mul
    ((Real.continuous_exp.comp (continuous_snd.div_const 2)).mul
      ((continuous_sourceFactorialRamp N).comp (continuous_fst.sub continuous_snd)))

theorem sourceFactorialCausal_zero_of_nonpos {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : x ≤ 0) :
    sourceFactorialCausal N x = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  rw [sourceFactorialRamp_zero_of_nonpos hN (by linarith [ht.1]), mul_zero, mul_zero]

theorem sourceFactorialCausal_tail {N : ℕ} (hN : 1 ≤ N) {x : ℝ}
    (hx : Real.log (4*(N : ℝ)+1) ≤ x) : sourceFactorialCausal N x = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  rw [sourceFactorialRamp_shift_tail hN ht hx, mul_zero, mul_zero]

/-- For `N ≥ 1`, the causal source has compact support, contained in `[0, log(4N + 1)]`. -/
theorem hasCompactSupport_sourceFactorialCausal {N : ℕ} (hN : 1 ≤ N) :
    HasCompactSupport (sourceFactorialCausal N) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc 0 (Real.log (4*(N : ℝ)+1))) isCompact_Icc
  intro x hx
  constructor
  · by_contra! h
    exact hx (sourceFactorialCausal_zero_of_nonpos hN h.le)
  · by_contra! h
    exact hx (sourceFactorialCausal_tail hN h.le)

/-- The causal source agrees with the factorial bi-null test on the logarithms of positive integers:
`sourceFactorialCausal N (log n) = factorialBiNull N (log n)` for `N, n ≥ 1`. -/
theorem sourceFactorialCausal_at_log {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) :
    sourceFactorialCausal N (Real.log n) = factorialBiNull N (Real.log n) := by
  have he : sourceFactorialCausal N (Real.log n) =
      ∫ t in Icc 0 (2*sourceFactorialWidth N), exponentialTentDensity (sourceFactorialWidth N) t*
        factorialBiNull N (Real.log n) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [sourceFactorialRamp_shift_at_log hN hn ht]
  rw [he, integral_mul_const, integral_Icc_exponentialTentDensity (sourceFactorialWidth_pos hN), one_mul]

/-- On the band `log(2N + 1) ≤ x ≤ log(4N)` the causal source equals `e^(x/2) / sqrt N`. -/
theorem sourceFactorialCausal_on_band {N : ℕ} (hN : 1 ≤ N) {x : ℝ}
    (hx : x ∈ Icc (Real.log (2*(N : ℝ)+1)) (Real.log (4*(N : ℝ)))) :
    sourceFactorialCausal N x = Real.exp (x/2)/Real.sqrt N := by
  have he : sourceFactorialCausal N x =
      ∫ t in Icc 0 (2*sourceFactorialWidth N), exponentialTentDensity (sourceFactorialWidth N) t*
        (Real.exp (x/2)/Real.sqrt N) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [sourceFactorialRamp_shift_band hN ht hx]
  rw [he, integral_mul_const, integral_Icc_exponentialTentDensity (sourceFactorialWidth_pos hN), one_mul]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
