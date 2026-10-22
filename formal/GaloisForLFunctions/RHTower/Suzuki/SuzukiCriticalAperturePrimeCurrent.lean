import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalApertureQuarterShiftCurrent

/-!
# Absolute prime summability of the critical aperture quarter-shift current

The critical Gamma--Euler boundary is not an `ell^(2 : ℕ)` vector, but its pairing with the cubically
normalized true-aperture innovation closes in valuation depth to the geometric resolvent

`atom(p,0) / (1 - ratio(p))`.

Here that closed current is summed over primes.  The depth-zero atom has norm
`sqrt(log p) * p^{-1/4}` times an innovation bounded by `(h sqrt h)^{-1} p^{-1}`, and the depth
ratio has norm at most `2^{-1/4}`, so the current is `O(sqrt(log p) p^{-5/4})`.  The elementary
bound `log p ≤ 4 p^{1/4}` turns this into `O(p^{-9/8})`, which is summable.  Consequently the
finite Euler-boundary currents have an exhaustion-independent cofinal value at critical
displacement, although the critical boundary alone has no Hilbert vector.
-/

namespace RHTower

noncomputable section

open scoped ComplexConjugate

/-! ## The closed current at one prime -/

/-- The critical quarter-shift current carried by a single prime: the depth-completed pairing of
the critical Gamma--Euler boundary with the true-aperture innovation. -/
def suzukiCriticalApertureQuarterShiftCurrent (h a t : ℝ) (p : Nat.Primes) : ℂ :=
  ∑' e : ℕ, suzukiCriticalApertureBoundaryAtom h a t p e

theorem suzukiCriticalApertureQuarterShiftCurrent_eq
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    suzukiCriticalApertureQuarterShiftCurrent h a t p =
      suzukiCriticalApertureBoundaryAtom h a t p 0 *
        (1 - suzukiCriticalApertureDepthRatio h a t p)⁻¹ :=
  tsum_suzukiCriticalApertureBoundaryAtom_eq_resolvent hh ha t p

/-! ## The depth-zero atom -/

private theorem valuationNat_zero (p : Nat.Primes) :
    ((xiGammaEulerValuationNat (p, 0) : ℕ) : ℝ) = (p : ℝ) := by
  simp [xiGammaEulerValuationNat]

private theorem normSq_criticalBoundary_zero (t : ℝ) (p : Nat.Primes) :
    Complex.normSq (xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, 0)) =
      Real.log (p : ℝ) * ((p : ℝ) ^ (-(1 : ℝ) / 2)) := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  have hpow : (p : ℝ) ^ (-(1 : ℝ) / 2) * (p : ℝ) = (p : ℝ) ^ ((1 : ℝ) / 2) := by
    nth_rewrite 2 [show ((p : ℕ) : ℝ) = ((p : ℕ) : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_add hp]
    norm_num
  rw [normSq_xiGammaEulerHeightBoundaryFeature, valuationNat_zero,
    show -(-1 / 2 : ℝ) * Real.log (p : ℝ) = Real.log ((p : ℝ) ^ ((1 : ℝ) / 2)) by
      rw [Real.log_rpow hp]; ring,
    Real.exp_log (Real.rpow_pos_of_pos hp _), div_mul_eq_mul_div,
    div_eq_iff hp.ne', mul_assoc, hpow]

private theorem norm_criticalBoundary_zero (t : ℝ) (p : Nat.Primes) :
    ‖xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, 0)‖ =
      Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(1 : ℝ) / 4)) := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.prop.one_le)
  have hrhs : 0 ≤ Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(1 : ℝ) / 4)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hp.le _)
  have hsq : ‖xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, 0)‖ ^ 2 =
      (Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(1 : ℝ) / 4))) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, normSq_criticalBoundary_zero, mul_pow,
      Real.sq_sqrt hlog, ← Real.rpow_natCast ((p : ℝ) ^ (-(1 : ℝ) / 4)) 2,
      ← Real.rpow_mul hp.le]
    norm_num
  have := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hrhs] at this

private theorem innovation_zero_eq (h a : ℝ) (p : Nat.Primes) :
    xiMobiusCubicNormalizedInnovationFeature h a (p, 0) =
      (h * Real.sqrt h)⁻¹ *
        (((p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹)) *
          (1 - xiMobiusContinuousApertureDiskNode ((h / 2) * a) p) ^ 2) := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  have hq : xiTransversePrimeApertureDiskNode 1 p = ((p : ℝ))⁻¹ := by
    rw [xiTransversePrimeApertureDiskNode]
    rw [show -((1 : ℕ) : ℝ) * Real.log (p : ℝ) = -Real.log (p : ℝ) by push_cast; ring,
      Real.exp_neg, Real.exp_log hp]
  simp only [xiMobiusCubicNormalizedInnovationFeature,
    xiMobiusContinuousApertureDyadicInnovationFeature,
    xiMobiusPrimeContinuousApertureDyadicInnovationFeature, hq]
  norm_num

private theorem innovation_zero_nonneg {h a : ℝ} (hh : 0 < h) (p : Nat.Primes) :
    0 ≤ xiMobiusCubicNormalizedInnovationFeature h a (p, 0) := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  rw [innovation_zero_eq]
  have h1 : (0 : ℝ) ≤ (h * Real.sqrt h)⁻¹ := by positivity
  have h2 : (0 : ℝ) ≤ (p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹) := by positivity
  positivity

private theorem innovation_zero_le {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (p : Nat.Primes) :
    xiMobiusCubicNormalizedInnovationFeature h a (p, 0) ≤
      (h * Real.sqrt h)⁻¹ * ((p : ℝ) ^ (-(1 : ℝ))) := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  have hra : 0 < (h / 2) * a := mul_pos (half_pos hh) ha
  have hr0 := xiMobiusContinuousApertureDiskNode_pos ((h / 2) * a) p
  have hr1 := xiMobiusContinuousApertureDiskNode_lt_one hra p
  have hcube : (0 : ℝ) < (h * Real.sqrt h)⁻¹ := by positivity
  rw [innovation_zero_eq, Real.rpow_neg_one]
  refine mul_le_mul_of_nonneg_left ?_ hcube.le
  have hfac : ((p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹)) ≤ (p : ℝ)⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [inv_pos.mpr hp]
  have hsq : (1 - xiMobiusContinuousApertureDiskNode ((h / 2) * a) p) ^ 2 ≤ 1 := by
    nlinarith
  have hfac0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹) := by positivity
  calc ((p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹)) *
        (1 - xiMobiusContinuousApertureDiskNode ((h / 2) * a) p) ^ 2
      ≤ ((p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹)) * 1 := by
        exact mul_le_mul_of_nonneg_left hsq hfac0
    _ = (p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹) := by ring
    _ ≤ (p : ℝ)⁻¹ := hfac

/-- The depth-zero critical atom has the exact power scale `sqrt(log p) * p^{-5/4}`. -/
theorem norm_suzukiCriticalApertureBoundaryAtom_zero_le
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    ‖suzukiCriticalApertureBoundaryAtom h a t p 0‖ ≤
      (h * Real.sqrt h)⁻¹ * (Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(5 : ℝ) / 4))) := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  have hcube : (0 : ℝ) < (h * Real.sqrt h)⁻¹ := by positivity
  rw [suzukiCriticalApertureBoundaryAtom, norm_mul, norm_star,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (innovation_zero_nonneg hh p), norm_criticalBoundary_zero]
  have hbound := innovation_zero_le hh ha p
  have hnn : (0 : ℝ) ≤ Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(1 : ℝ) / 4)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hp.le _)
  calc Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(1 : ℝ) / 4)) *
        xiMobiusCubicNormalizedInnovationFeature h a (p, 0)
      ≤ Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(1 : ℝ) / 4)) *
          ((h * Real.sqrt h)⁻¹ * ((p : ℝ) ^ (-(1 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hbound hnn
    _ = (h * Real.sqrt h)⁻¹ *
          (Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(1 : ℝ) / 4) * (p : ℝ) ^ (-(1 : ℝ)))) := by
        ring
    _ = (h * Real.sqrt h)⁻¹ *
          (Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(5 : ℝ) / 4))) := by
        rw [← Real.rpow_add hp]
        norm_num

/-! ## The depth resolvent factor -/

/-- The quarter shift alone already contracts the depth ratio below `2^{-1/4}`. -/
theorem norm_suzukiCriticalApertureDepthRatio_le_quarter
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    ‖suzukiCriticalApertureDepthRatio h a t p‖ ≤ Real.exp (-(Real.log 2) / 4) := by
  have hL : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast p.prop.two_le)
  have hra : 0 < (h / 2) * a := mul_pos (half_pos hh) ha
  have hr0 := xiMobiusContinuousApertureDiskNode_pos ((h / 2) * a) p
  have hr1 := xiMobiusContinuousApertureDiskNode_lt_one hra p
  rw [suzukiCriticalApertureDepthRatio, suzukiCriticalGammaDepthRatio,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp_ofReal_mul_I,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hexp : Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) ≤ Real.exp (-(Real.log 2) / 4) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hsq : xiMobiusContinuousApertureDiskNode ((h / 2) * a) p ^ 2 ≤ 1 := by nlinarith
  calc Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) * 1 *
        xiMobiusContinuousApertureDiskNode ((h / 2) * a) p ^ 2
      ≤ Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) * 1 * 1 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = Real.exp (-(1 / 4 : ℝ) * Real.log (p : ℝ)) := by ring
    _ ≤ Real.exp (-(Real.log 2) / 4) := hexp

private theorem quarter_lt_one : Real.exp (-(Real.log 2) / 4) < 1 := by
  rw [Real.exp_lt_one_iff]
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- The depth resolvent is uniformly bounded over all primes and all heights. -/
theorem norm_suzukiCriticalApertureDepthResolvent_le
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    ‖(1 - suzukiCriticalApertureDepthRatio h a t p)⁻¹‖ ≤
      (1 - Real.exp (-(Real.log 2) / 4))⁻¹ := by
  have hq := quarter_lt_one
  have hpos : 0 < 1 - Real.exp (-(Real.log 2) / 4) := by linarith
  have hle := norm_suzukiCriticalApertureDepthRatio_le_quarter hh ha t p
  have hlow : 1 - Real.exp (-(Real.log 2) / 4) ≤
      ‖1 - suzukiCriticalApertureDepthRatio h a t p‖ := by
    have := norm_sub_norm_le (1 : ℂ) (suzukiCriticalApertureDepthRatio h a t p)
    simp only [norm_one] at this
    linarith
  rw [norm_inv]
  exact inv_anti₀ hpos hlow

/-! ## The prime-summable current -/

/-- Absolute size of the closed current: `O(sqrt(log p) p^{-5/4})`, uniformly in the height. -/
theorem norm_suzukiCriticalApertureQuarterShiftCurrent_le
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    ‖suzukiCriticalApertureQuarterShiftCurrent h a t p‖ ≤
      ((h * Real.sqrt h)⁻¹ * (1 - Real.exp (-(Real.log 2) / 4))⁻¹) *
        (Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(5 : ℝ) / 4))) := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  have hq := quarter_lt_one
  have hpos : 0 < 1 - Real.exp (-(Real.log 2) / 4) := by linarith
  rw [suzukiCriticalApertureQuarterShiftCurrent_eq hh ha, norm_mul]
  have hA := norm_suzukiCriticalApertureBoundaryAtom_zero_le hh ha t p
  have hB := norm_suzukiCriticalApertureDepthResolvent_le hh ha t p
  have hA0 : (0 : ℝ) ≤ ‖suzukiCriticalApertureBoundaryAtom h a t p 0‖ := norm_nonneg _
  have hRHS0 : (0 : ℝ) ≤ (h * Real.sqrt h)⁻¹ *
      (Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(5 : ℝ) / 4))) := by
    have : (0 : ℝ) ≤ (p : ℝ) ^ (-(5 : ℝ) / 4) := Real.rpow_nonneg hp.le _
    have h1 : (0 : ℝ) ≤ (h * Real.sqrt h)⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ Real.sqrt (Real.log (p : ℝ)) := Real.sqrt_nonneg _
    positivity
  calc ‖suzukiCriticalApertureBoundaryAtom h a t p 0‖ *
        ‖(1 - suzukiCriticalApertureDepthRatio h a t p)⁻¹‖
      ≤ ((h * Real.sqrt h)⁻¹ *
          (Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(5 : ℝ) / 4)))) *
            (1 - Real.exp (-(Real.log 2) / 4))⁻¹ :=
        mul_le_mul hA hB (norm_nonneg _) hRHS0
    _ = ((h * Real.sqrt h)⁻¹ * (1 - Real.exp (-(Real.log 2) / 4))⁻¹) *
          (Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(5 : ℝ) / 4))) := by ring

/-- Elementary logarithm bound: `sqrt (log x) ≤ 2 x^{1/8}` for `x ≥ 1`. -/
theorem sqrt_log_le_two_mul_rpow {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt (Real.log x) ≤ 2 * (x ^ ((1 : ℝ) / 8)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hquarter : Real.log x ≤ 4 * (x ^ ((1 : ℝ) / 4)) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 ((1 : ℝ) / 4))
    rw [Real.log_rpow hx0] at h
    have hxp : (0 : ℝ) ≤ x ^ ((1 : ℝ) / 4) := (Real.rpow_pos_of_pos hx0 _).le
    linarith
  have hsq : (2 * (x ^ ((1 : ℝ) / 8))) ^ 2 = 4 * (x ^ ((1 : ℝ) / 4)) := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 8)) 2, ← Real.rpow_mul hx0.le]
    norm_num
  have hnn : (0 : ℝ) ≤ 2 * (x ^ ((1 : ℝ) / 8)) := by positivity
  nlinarith [Real.sq_sqrt (Real.log_nonneg hx), Real.sqrt_nonneg (Real.log x)]

/-- The closed current is dominated by a convergent `p`-series. -/
theorem norm_suzukiCriticalApertureQuarterShiftCurrent_le_rpow
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) (p : Nat.Primes) :
    ‖suzukiCriticalApertureQuarterShiftCurrent h a t p‖ ≤
      (2 * ((h * Real.sqrt h)⁻¹ * (1 - Real.exp (-(Real.log 2) / 4))⁻¹)) *
        ((p : ℝ) ^ (-(9 : ℝ) / 8)) := by
  have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.one_le
  have hp : (0 : ℝ) < (p : ℕ) := lt_of_lt_of_le one_pos hp1
  have hq := quarter_lt_one
  have hK : (0 : ℝ) ≤ (h * Real.sqrt h)⁻¹ * (1 - Real.exp (-(Real.log 2) / 4))⁻¹ := by
    have h1 : (0 : ℝ) ≤ (h * Real.sqrt h)⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ (1 - Real.exp (-(Real.log 2) / 4))⁻¹ := by
      apply inv_nonneg.mpr; linarith
    exact mul_nonneg h1 h2
  refine le_trans (norm_suzukiCriticalApertureQuarterShiftCurrent_le hh ha t p) ?_
  have hlog := sqrt_log_le_two_mul_rpow hp1
  have hrp : (0 : ℝ) < (p : ℝ) ^ (-(5 : ℝ) / 4) := Real.rpow_pos_of_pos hp _
  have hstep : Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(5 : ℝ) / 4)) ≤
      2 * ((p : ℝ) ^ (-(9 : ℝ) / 8)) := by
    calc Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(5 : ℝ) / 4))
        ≤ (2 * ((p : ℝ) ^ ((1 : ℝ) / 8))) * ((p : ℝ) ^ (-(5 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_right hlog hrp.le
      _ = 2 * ((p : ℝ) ^ (-(9 : ℝ) / 8)) := by
          rw [mul_assoc, ← Real.rpow_add hp]
          norm_num
  calc ((h * Real.sqrt h)⁻¹ * (1 - Real.exp (-(Real.log 2) / 4))⁻¹) *
        (Real.sqrt (Real.log (p : ℝ)) * ((p : ℝ) ^ (-(5 : ℝ) / 4)))
      ≤ ((h * Real.sqrt h)⁻¹ * (1 - Real.exp (-(Real.log 2) / 4))⁻¹) *
          (2 * ((p : ℝ) ^ (-(9 : ℝ) / 8))) := mul_le_mul_of_nonneg_left hstep hK
    _ = (2 * ((h * Real.sqrt h)⁻¹ * (1 - Real.exp (-(Real.log 2) / 4))⁻¹)) *
          ((p : ℝ) ^ (-(9 : ℝ) / 8)) := by ring

private theorem summable_prime_rpow_neg_nine_eighths :
    Summable (fun p : Nat.Primes => ((p : ℝ) ^ (-(9 : ℝ) / 8))) := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ (-(9 : ℝ) / 8))) :=
    (Real.summable_nat_rpow (p := -(9 : ℝ) / 8)).mpr (by norm_num)
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := fun _ _ h => Subtype.ext h
  exact hnat.comp_injective hinj

/-- **Absolute prime summability of the critical current.**  The depth-completed critical
Gamma-boundary/aperture-innovation pairing is absolutely summable over primes, for every positive
observer aperture and every real height. -/
theorem summable_norm_suzukiCriticalApertureQuarterShiftCurrent
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) :
    Summable (fun p : Nat.Primes => ‖suzukiCriticalApertureQuarterShiftCurrent h a t p‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => norm_suzukiCriticalApertureQuarterShiftCurrent_le_rpow hh ha t p) ?_
  exact summable_prime_rpow_neg_nine_eighths.mul_left _

theorem summable_suzukiCriticalApertureQuarterShiftCurrent
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) :
    Summable (suzukiCriticalApertureQuarterShiftCurrent h a t) :=
  Summable.of_norm (summable_norm_suzukiCriticalApertureQuarterShiftCurrent hh ha t)

/-- The cofinal critical aperture current: the exhaustion-independent value of the finite
Euler-boundary currents at critical displacement. -/
def suzukiCriticalApertureCofinalCurrent (h a t : ℝ) : ℂ :=
  ∑' p : Nat.Primes, suzukiCriticalApertureQuarterShiftCurrent h a t p

/-- **Exhaustion independence.**  The cofinal current is an unconditional sum, so every exhaustion
of the primes converges to it. -/
theorem hasSum_suzukiCriticalApertureCofinalCurrent
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) :
    HasSum (suzukiCriticalApertureQuarterShiftCurrent h a t)
      (suzukiCriticalApertureCofinalCurrent h a t) :=
  (summable_suzukiCriticalApertureQuarterShiftCurrent hh ha t).hasSum

/-- The cofinal current obeys the same absolute bound term by term. -/
theorem norm_suzukiCriticalApertureCofinalCurrent_le
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ) :
    ‖suzukiCriticalApertureCofinalCurrent h a t‖ ≤
      ∑' p : Nat.Primes, ‖suzukiCriticalApertureQuarterShiftCurrent h a t p‖ :=
  norm_tsum_le_tsum_norm (summable_norm_suzukiCriticalApertureQuarterShiftCurrent hh ha t)

end

end RHTower
