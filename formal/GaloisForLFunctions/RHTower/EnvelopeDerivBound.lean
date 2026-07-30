/-
Explicit sup for the envelope derivative on the critical line.

The canonical derivative `archFactorDeriv = (2s−1)/2·Γ_ℝ + s(s−1)/2·Γ_ℝ·Ψ` is bounded on the
line by combining the Euler-integral bound for `‖Γ_ℝ‖` with the two vertical digamma bounds
for `‖Ψ‖`: `‖archFactorDeriv(linePt u)‖ ≤ π^{−1/4}Γ(¼)·(u + (¼+u²)/2·(‖ψ‖-bound/2 + log√π))`,
a closed-form function of the height.  With this the last non-theorem face of the completed
carrier's first-moment bound — the derivative sup `M₁` — is discharged, so the first-moment
cancellation face of the sign-bracket certificates is elementary segment arithmetic.
-/
import GaloisForLFunctions.RHTower.ResonanceClosedForm

open Complex Metric

namespace RHTower

/-- Explicit `Γ_ℝ` sup on the critical line. -/
theorem norm_Gammaℝ_line_le (u : ℝ) :
    ‖Complex.Gammaℝ (linePt u)‖ ≤ Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4) := by
  rw [Complex.Gammaℝ_def, norm_mul]
  have hpow : ‖((Real.pi : ℝ) : ℂ) ^ (-(linePt u) / 2)‖ = Real.pi ^ (-(1 / 4 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    rw [show (-(linePt u) / 2 : ℂ) = -(linePt u / 2) from by ring, Complex.neg_re,
      re_div_two, linePt_re]
    norm_num
  have hre : ((linePt u) / 2).re = 1 / 4 := by
    rw [re_div_two, linePt_re]
    norm_num
  have hGnorm : ‖Complex.Gamma ((linePt u) / 2)‖ ≤ Real.Gamma (1 / 4) := by
    have h := norm_Gamma_le_Gamma_re (z := (linePt u) / 2) (by rw [hre]; norm_num)
    rwa [hre] at h
  rw [hpow]
  exact mul_le_mul_of_nonneg_left hGnorm (Real.rpow_nonneg Real.pi_pos.le _)

/-- Explicit digamma sup at the quarter point of the line. -/
theorem norm_digamma_quarter_le {u : ℝ} (hu : 0 < u) :
    ‖Complex.digamma ((linePt u) / 2)‖ ≤
      |Real.log (1 / 16 + u ^ 2 / 4)| / 2 + 4 / u ^ 2 + Real.pi / u +
        (2 / u + Real.pi / 2) := by
  have harg : (linePt u) / 2 = ((1 / 4 : ℝ) : ℂ) + ((u / 2 : ℝ) : ℂ) * Complex.I := by
    unfold linePt
    push_cast
    ring
  refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
  rw [harg]
  have hre := re_digamma_vertical_bound_uncond (σ := 1 / 4) (t := u / 2)
    (by norm_num) (by positivity)
  have him := im_digamma_vertical_bound (σ := 1 / 4) (t := u / 2)
    (by norm_num) (by positivity)
  have hre' : |(Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((u / 2 : ℝ) : ℂ) * Complex.I)).re| ≤
      |Real.log ((1 / 4 : ℝ) ^ 2 + (u / 2) ^ 2)| / 2 +
        (1 / (u / 2) ^ 2 + Real.pi / (2 * (u / 2))) := by
    set a : ℝ := (Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((u / 2 : ℝ) : ℂ) * Complex.I)).re
    set b : ℝ := (1 / 2) * Real.log ((1 / 4 : ℝ) ^ 2 + (u / 2) ^ 2)
    have htri : |a| ≤ |a - b| + |b| := by
      calc |a| = |(a - b) + b| := by ring_nf
        _ ≤ |a - b| + |b| := abs_add_le _ _
    have hb : |b| = |Real.log ((1 / 4 : ℝ) ^ 2 + (u / 2) ^ 2)| / 2 := by
      rw [abs_mul]
      norm_num
      ring
    calc |a| ≤ |a - b| + |b| := htri
      _ ≤ (1 / (u / 2) ^ 2 + Real.pi / (2 * (u / 2))) + |b| := by
          have := hre
          gcongr
      _ = |Real.log ((1 / 4 : ℝ) ^ 2 + (u / 2) ^ 2)| / 2 +
          (1 / (u / 2) ^ 2 + Real.pi / (2 * (u / 2))) := by
          rw [hb]
          ring
  have him' : |(Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((u / 2 : ℝ) : ℂ) * Complex.I)).im| ≤
      1 / (u / 2) + Real.pi / 2 := by
    rw [abs_of_nonneg him.1]
    exact him.2
  have e0 : ((1 / 4 : ℝ)) ^ 2 + (u / 2) ^ 2 = 1 / 16 + u ^ 2 / 4 := by ring
  have e1 : 1 / ((u / 2 : ℝ)) ^ 2 = 4 / u ^ 2 := by
    rw [show ((u : ℝ) / 2) ^ 2 = u ^ 2 / 4 from by ring, one_div_div]
  have e2 : Real.pi / (2 * (u / 2)) = Real.pi / u := by
    rw [show 2 * (u / 2) = u from by ring]
  have e3 : 1 / ((u : ℝ) / 2) = 2 / u := one_div_div u 2
  rw [e0] at hre'
  rw [e1, e2] at hre'
  rw [e3] at him'
  linarith

/-- **Explicit envelope-derivative sup on the critical line.**  Every transcendental
ingredient is one of the banked vertical bounds, so the `M₁` face of the carrier's
first-moment cancellation is a closed-form function of the height. -/
theorem norm_archFactorDeriv_line_le {u : ℝ} (hu : 0 < u) :
    ‖archFactorDeriv (linePt u)‖ ≤
      Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4) *
        (u + (1 / 4 + u ^ 2) / 2 *
          ((|Real.log (1 / 16 + u ^ 2 / 4)| / 2 + 4 / u ^ 2 + Real.pi / u +
            (2 / u + Real.pi / 2)) / 2 + Real.log Real.pi / 2)) := by
  have hCγ : (0 : ℝ) ≤ Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4) :=
    mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.Gamma_pos_of_pos (by norm_num)).le
  have h1 : 2 * linePt u - 1 = ((2 * u : ℝ) : ℂ) * Complex.I := by
    unfold linePt
    push_cast
    ring
  have h2 : linePt u * (linePt u - 1) = ((-(1 / 4 + u ^ 2) : ℝ) : ℂ) := by
    unfold linePt
    push_cast
    linear_combination ((u : ℂ)) ^ 2 * Complex.I_sq
  have hA : ‖(2 * linePt u - 1) / 2‖ = u := by
    rw [norm_div, h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, abs_of_pos (by positivity : (0 : ℝ) < 2 * u),
      show ‖(2 : ℂ)‖ = 2 from by norm_num]
    ring
  have hP : ‖linePt u * (linePt u - 1) / 2‖ = (1 / 4 + u ^ 2) / 2 := by
    rw [norm_div, h2, Complex.norm_real, Real.norm_eq_abs,
      show |(-(1 / 4 + u ^ 2) : ℝ)| = 1 / 4 + u ^ 2 from by
        rw [abs_neg]; exact abs_of_pos (by positivity)]
    norm_num
  have hGR := norm_Gammaℝ_line_le u
  have hlogπ : (0 : ℝ) ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hΨ : ‖Complex.digamma ((linePt u) / 2) / 2 - (Real.log Real.pi : ℂ) / 2‖ ≤
      (|Real.log (1 / 16 + u ^ 2 / 4)| / 2 + 4 / u ^ 2 + Real.pi / u +
        (2 / u + Real.pi / 2)) / 2 + Real.log Real.pi / 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlogπ, show ‖(2 : ℂ)‖ = 2 from by norm_num]
    have := norm_digamma_quarter_le hu
    gcongr
  unfold archFactorDeriv
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mul, norm_mul, hA, hP]
  have hterm1 : u * ‖Complex.Gammaℝ (linePt u)‖ ≤
      u * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) :=
    mul_le_mul_of_nonneg_left hGR hu.le
  have hterm2 : (1 / 4 + u ^ 2) / 2 * (‖Complex.Gammaℝ (linePt u)‖ *
      ‖Complex.digamma ((linePt u) / 2) / 2 - (Real.log Real.pi : ℂ) / 2‖) ≤
      (1 / 4 + u ^ 2) / 2 * ((Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) *
        ((|Real.log (1 / 16 + u ^ 2 / 4)| / 2 + 4 / u ^ 2 + Real.pi / u +
          (2 / u + Real.pi / 2)) / 2 + Real.log Real.pi / 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul hGR hΨ (norm_nonneg _) hCγ
  calc u * ‖Complex.Gammaℝ (linePt u)‖ + (1 / 4 + u ^ 2) / 2 *
        (‖Complex.Gammaℝ (linePt u)‖ *
          ‖Complex.digamma ((linePt u) / 2) / 2 - (Real.log Real.pi : ℂ) / 2‖)
      ≤ u * (Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) +
        (1 / 4 + u ^ 2) / 2 * ((Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) *
          ((|Real.log (1 / 16 + u ^ 2 / 4)| / 2 + 4 / u ^ 2 + Real.pi / u +
            (2 / u + Real.pi / 2)) / 2 + Real.log Real.pi / 2)) :=
        add_le_add hterm1 hterm2
    _ = Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4) *
        (u + (1 / 4 + u ^ 2) / 2 *
          ((|Real.log (1 / 16 + u ^ 2 / 4)| / 2 + 4 / u ^ 2 + Real.pi / u +
            (2 / u + Real.pi / 2)) / 2 + Real.log Real.pi / 2)) := by ring

/-- Pointwise closed-form derivative-envelope budget on the critical line. -/
noncomputable def archDerivLineBudget (u : ℝ) : ℝ :=
  Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4) *
    (u + (1 / 4 + u ^ 2) / 2 *
      ((|Real.log (1 / 16 + u ^ 2 / 4)| / 2 + 4 / u ^ 2 + Real.pi / u +
        (2 / u + Real.pi / 2)) / 2 + Real.log Real.pi / 2))

/-- Segment-level closed derivative-envelope budget.  The right endpoint controls polynomial
growth, the left endpoint controls reciprocal decay, and the logarithm is bounded by the larger
endpoint log modulus. -/
noncomputable def archDerivSegmentBudget (α β : ℝ) : ℝ :=
  Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4) *
    (β + (1 / 4 + β ^ 2) / 2 *
      ((max |Real.log (1 / 16 + α ^ 2 / 4)| |Real.log (1 / 16 + β ^ 2 / 4)| / 2 +
        4 / α ^ 2 + Real.pi / α + (2 / α + Real.pi / 2)) / 2 +
        Real.log Real.pi / 2))

/-- Real absolute value is bounded by the larger endpoint absolute value on an interval. -/
theorem abs_le_max_abs_of_bounds {a x b : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    |x| ≤ max |a| |b| := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hma : |a| ≤ max |a| |b| := le_max_left _ _
    exact le_trans (neg_le_neg hma) (le_trans (neg_abs_le a) hax)
  · exact le_trans hxb (le_trans (le_abs_self b) (le_max_right _ _))

/-- Named-budget form of the pointwise derivative-envelope bound. -/
theorem norm_archFactorDeriv_line_le_budget {u : ℝ} (hu : 0 < u) :
    ‖archFactorDeriv (linePt u)‖ ≤ archDerivLineBudget u := by
  simpa [archDerivLineBudget] using norm_archFactorDeriv_line_le hu

/-- The segment derivative budget controls `‖archFactorDeriv(linePt u)‖` throughout a positive
segment `[α, β]`. -/
theorem norm_archFactorDeriv_line_le_segmentBudget {α β u : ℝ}
    (hα : 0 < α) (hu : u ∈ Set.Icc α β) :
    ‖archFactorDeriv (linePt u)‖ ≤ archDerivSegmentBudget α β := by
  have hu0 : 0 < u := lt_of_lt_of_le hα hu.1
  have hβ0 : 0 < β := lt_of_lt_of_le hu0 hu.2
  have hCγ : (0 : ℝ) ≤ Real.pi ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4) :=
    mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.Gamma_pos_of_pos (by norm_num)).le
  have hu2lo : α ^ 2 ≤ u ^ 2 := by nlinarith [hu.1, hα, hu0]
  have hu2hi : u ^ 2 ≤ β ^ 2 := by nlinarith [hu.2, hu0, hβ0]
  have hlogarg_lo_pos : 0 < 1 / 16 + α ^ 2 / 4 := by positivity
  have hlogarg_u_pos : 0 < 1 / 16 + u ^ 2 / 4 := by positivity
  have hloglo : Real.log (1 / 16 + α ^ 2 / 4) ≤ Real.log (1 / 16 + u ^ 2 / 4) :=
    Real.log_le_log hlogarg_lo_pos (by nlinarith)
  have hloghi : Real.log (1 / 16 + u ^ 2 / 4) ≤ Real.log (1 / 16 + β ^ 2 / 4) :=
    Real.log_le_log hlogarg_u_pos (by nlinarith)
  have hlogabs : |Real.log (1 / 16 + u ^ 2 / 4)| ≤
      max |Real.log (1 / 16 + α ^ 2 / 4)| |Real.log (1 / 16 + β ^ 2 / 4)| :=
    abs_le_max_abs_of_bounds hloglo hloghi
  have hinv : 1 / u ≤ 1 / α := one_div_le_one_div_of_le hα hu.1
  have hinv2 : 1 / u ^ 2 ≤ 1 / α ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hα) hu2lo
  have h4 : 4 / u ^ 2 ≤ 4 / α ^ 2 := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv2 (by norm_num : (0 : ℝ) ≤ 4)
  have hpi : Real.pi / u ≤ Real.pi / α := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv Real.pi_pos.le
  have h2 : 2 / u ≤ 2 / α := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
  have hpoint_piece_nonneg :
      0 ≤ (|Real.log (1 / 16 + u ^ 2 / 4)| / 2 + 4 / u ^ 2 + Real.pi / u +
        (2 / u + Real.pi / 2)) / 2 + Real.log Real.pi / 2 := by
    have hlogπ : 0 ≤ Real.log Real.pi :=
      Real.log_nonneg (by linarith [Real.pi_gt_three])
    positivity
  have hpiece : (|Real.log (1 / 16 + u ^ 2 / 4)| / 2 + 4 / u ^ 2 + Real.pi / u +
        (2 / u + Real.pi / 2)) / 2 + Real.log Real.pi / 2 ≤
      (max |Real.log (1 / 16 + α ^ 2 / 4)| |Real.log (1 / 16 + β ^ 2 / 4)| / 2 +
        4 / α ^ 2 + Real.pi / α + (2 / α + Real.pi / 2)) / 2 +
        Real.log Real.pi / 2 := by
    nlinarith [hlogabs, h4, hpi, h2]
  have hquad : (1 / 4 + u ^ 2) / 2 ≤ (1 / 4 + β ^ 2) / 2 := by nlinarith
  have hquad_nonneg : 0 ≤ (1 / 4 + β ^ 2) / 2 := by positivity
  have hprod : (1 / 4 + u ^ 2) / 2 *
        ((|Real.log (1 / 16 + u ^ 2 / 4)| / 2 + 4 / u ^ 2 + Real.pi / u +
          (2 / u + Real.pi / 2)) / 2 + Real.log Real.pi / 2) ≤
      (1 / 4 + β ^ 2) / 2 *
        ((max |Real.log (1 / 16 + α ^ 2 / 4)| |Real.log (1 / 16 + β ^ 2 / 4)| / 2 +
          4 / α ^ 2 + Real.pi / α + (2 / α + Real.pi / 2)) / 2 +
          Real.log Real.pi / 2) :=
    mul_le_mul hquad hpiece hpoint_piece_nonneg hquad_nonneg
  have hinside : u + (1 / 4 + u ^ 2) / 2 *
        ((|Real.log (1 / 16 + u ^ 2 / 4)| / 2 + 4 / u ^ 2 + Real.pi / u +
          (2 / u + Real.pi / 2)) / 2 + Real.log Real.pi / 2) ≤
      β + (1 / 4 + β ^ 2) / 2 *
        ((max |Real.log (1 / 16 + α ^ 2 / 4)| |Real.log (1 / 16 + β ^ 2 / 4)| / 2 +
          4 / α ^ 2 + Real.pi / α + (2 / α + Real.pi / 2)) / 2 +
          Real.log Real.pi / 2) :=
    add_le_add hu.2 hprod
  exact le_trans (norm_archFactorDeriv_line_le hu0) (by
    dsimp [archDerivSegmentBudget]
    exact mul_le_mul_of_nonneg_left hinside hCγ)

/-- The closed segment derivative-envelope budget is nonnegative on positive segments. -/
theorem archDerivSegmentBudget_nonneg {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    0 ≤ archDerivSegmentBudget α β := by
  exact le_trans (norm_nonneg (archFactorDeriv (linePt α)))
    (norm_archFactorDeriv_line_le_segmentBudget (α := α) (β := β) (u := α)
      hα ⟨le_rfl, hαβ⟩)

/-- The reflected critical-line derivative has the same norm as the direct derivative. -/
theorem norm_archFactorDeriv_reflected_line_eq (u : ℝ) :
    ‖archFactorDeriv (1 - linePt u)‖ = ‖archFactorDeriv (linePt u)‖ := by
  have heqfun : (fun v : ℝ => archFactor (1 - linePt v)) =
      fun v : ℝ => (starRingEnd ℂ) (archFactor (linePt v)) := by
    funext v
    rw [← conj_linePt v]
    exact archFactor_conj (linePt v)
  have hleft := hasDerivAt_archFactor_line_reflected u
  have hright0 := hasDerivAt_archFactor_line u
  have hconj : HasDerivAt (fun v : ℝ => (starRingEnd ℂ) (archFactor (linePt v)))
      ((starRingEnd ℂ) (archFactorDeriv (linePt u) * Complex.I)) u := by
    simpa using!
      ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
        u hright0)
  have hright : HasDerivAt (fun v : ℝ => archFactor (1 - linePt v))
      ((starRingEnd ℂ) (archFactorDeriv (linePt u) * Complex.I)) u := by
    simpa [heqfun] using hconj
  have huniq := HasDerivAt.unique hleft hright
  have hnorm := congrArg norm huniq
  simp [map_mul] at hnorm
  exact hnorm

end RHTower
