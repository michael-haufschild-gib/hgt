import GaloisForLFunctions.RHTower.InfiniteMobiusCausalShift
import GaloisForLFunctions.RHTower.MobiusCriticalClockMoments
import GaloisForLFunctions.RHTower.VectorSignedChannelCoisometry

/-!
# The coupled floor--Möbius feature and its exact norm

`mobius-signed-channel-coisometry-incidence-law.md`, equations `(11)`--`(17)` and `(20)`--`(23)`.

For a causal vector `k` of `L²(R)` (the normalized floor remainder of the card) and the truncated
constant boundary mode `(I - P_d) 1 = 1_{[0, log d)}`, the coupled feature at the divisor channel `d`
is

```text
B_{omega,d} = V_{log d} k - c_omega (I - P_d) 1 .
```

Its two terms have disjoint supports, so

```text
||B_{omega,d}||^2 = ||k||^2 + c_omega^2 log d ,                              (15)
||Y_omega||^2     = ||k||^2 + c_omega^2 E_{P_omega}[log d] ,                 (17)
```

and the exact logarithmic moment is the squarefree fixed current
`-zeta'/zeta(sigma) + 2 zeta'/zeta(2 sigma)`, already formalized as
`squarefreeMobiusLogMoment 1`.

Feeding `Y_omega` through the signed coisometry recovers the coupled error and gives the exact
cancellation law `(23)`.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

noncomputable section
namespace RHTower

/-! ### The truncated constant boundary mode -/

private theorem volume_Ico_ne_top (a : ℝ) : (volume (Ico (0 : ℝ) a)) ≠ ⊤ := by
  rw [Real.volume_Ico]
  exact ENNReal.ofReal_ne_top

/-- Card `(13)`: the truncated constant boundary mode `(I - P_d) 1 = 1_{[0, a)}`. -/
def truncatedConstant (a : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 measurableSet_Ico (volume_Ico_ne_top a) (1 : ℂ)

theorem norm_truncatedConstant_sq {a : ℝ} (ha : 0 ≤ a) :
    ‖truncatedConstant a‖ ^ 2 = a := by
  have hnorm : ‖truncatedConstant a‖ =
      ‖(1 : ℂ)‖ * (volume.real (Ico (0 : ℝ) a)) ^ (1 / (2 : ℝ≥0∞).toReal) :=
    norm_indicatorConstLp (by norm_num) (by norm_num)
  have hmeas : volume.real (Ico (0 : ℝ) a) = a := by
    rw [measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hnorm, hmeas, norm_one, one_mul, show (1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) by norm_num]
  rw [← Real.rpow_natCast (a ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul ha]
  norm_num

/-- The truncated constant vanishes above its cutoff. -/
theorem truncatedConstant_ae_eq_zero_of_le {a : ℝ} :
    ∀ᵐ t : ℝ, a ≤ t → (truncatedConstant a) t = 0 := by
  filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := (volume : Measure ℝ))
    (hs := measurableSet_Ico (a := (0 : ℝ)) (b := a)) (hμs := volume_Ico_ne_top a)
    (c := (1 : ℂ))] with t ht hta
  rw [truncatedConstant] at *
  rw [ht, Set.indicator_of_notMem (by simp; intro _; exact hta)]

/-! ### The coupled feature at one divisor channel -/

/-- Card `(13)`: the coupled floor--tail feature at the divisor channel `d`. -/
def coupledFeature (omega : ℝ) (k : Lp ℂ 2 (volume : Measure ℝ)) (d : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  MellinL2.additiveTranslationUnitary (-Real.log d) k -
    ((1 / (1 + omega) : ℝ) : ℂ) • truncatedConstant (Real.log d)

/-- The two components of the coupled feature are orthogonal. -/
theorem inner_shift_truncatedConstant_eq_zero
    {a : ℝ} (ha : 0 ≤ a) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    inner ℂ (MellinL2.additiveTranslationUnitary (-a) k) (truncatedConstant a) = 0 := by
  rw [L2.inner_def]
  have hshift := additiveTranslationUnitary_hasAELowerSupport_zero ha k hk
  have htrunc := truncatedConstant_ae_eq_zero_of_le (a := a)
  have hzero : ∀ᵐ t : ℝ,
      inner ℂ ((MellinL2.additiveTranslationUnitary (-a) k) t) ((truncatedConstant a) t)
        = (0 : ℂ) := by
    filter_upwards [hshift, htrunc] with t hs htz
    rcases lt_or_ge t a with h | h
    · rw [hs (by linarith)]
      simp
    · rw [htz h]
      simp
  rw [integral_congr_ae hzero, integral_zero]

/-- **Card `(15)`.**  Exact norm of the coupled feature at one divisor channel. -/
theorem norm_coupledFeature_sq
    {omega : ℝ} {d : ℕ} (hd : 0 < d) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    ‖coupledFeature omega k d‖ ^ 2 =
      ‖k‖ ^ 2 + (1 / (1 + omega)) ^ 2 * Real.log d := by
  have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
  have hinner : inner ℂ (MellinL2.additiveTranslationUnitary (-Real.log d) k)
      (((1 / (1 + omega) : ℝ) : ℂ) • truncatedConstant (Real.log d)) = 0 := by
    rw [inner_smul_right, inner_shift_truncatedConstant_eq_zero hlog k hk, mul_zero]
  rw [coupledFeature, norm_sub_sq (𝕜 := ℂ), hinner]
  rw [LinearIsometryEquiv.norm_map, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    norm_truncatedConstant_sq hlog, sq_abs]
  simp

end RHTower
