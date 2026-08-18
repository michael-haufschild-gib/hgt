import GaloisForLFunctions.RHTower.CCMUnitRieszFUCurvatureTransport

/-!
# The finite-aperture FU-to-UR curvature reporter

The exact FU-to-UR curvature transport identifies the shifted completed-error unit-Riesz response
with an endpoint term plus a pairing of the CCM-FU Cesàro primitive against the second derivative
of the cubically renormalized source test.  Normalizing that pairing by `exp(t/2)/t^3` and passing
to the lag variable `u = t - s` produces the *finite-aperture reporter kernel*

```text
K_t(u) = (3/32) (exp(-u) R(t-u) - exp(-u/2) P(t-u)) / t^3
```

with `P` the slow and `R` the fast polynomial of the second derivative.  This file proves:

* the exact reporter form of the transport, with its boundary atom `-(3/64)`;
* the strict monotonicity of `R/P` from `1` to `4` and the resulting unique moving sign wall,
  located strictly inside `(0, log 16)` and converging to `log 16`;
* the fixed-lag convergence `K_t → K_∞` to the limiting two-channel curvature kernel;
* exact affine blindness: mass `3/64`, vanishing first moment, strictly negative second moment;
* the two-unit loss of origin monotonicity of the literal test, in iff form.

Everything is unconditional and source-side.  No arithmetic estimate and no RH claim is made.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-! ## The finite-aperture reporter kernel -/

/-- Finite-aperture FU-to-UR curvature reporter at lag `u`, normalized by `exp(t/2)/t^3`. -/
def unitRieszCesaroApertureKernel (t u : ℝ) : ℝ :=
  (3 / 32) *
      (Real.exp (-u) * unitRieszCesaroFastPolynomial (t - u) -
        Real.exp (-u / 2) * unitRieszCesaroSlowPolynomial (t - u)) / t ^ 3

/-- The reporter numerator is the negated second derivative of the renormalized source test at
the reflected point, weighted by `exp(t/2)`. -/
theorem unitRieszCesaroApertureNumerator (t u : ℝ) :
    (3 / 32) *
        (Real.exp (-u) * unitRieszCesaroFastPolynomial (t - u) -
          Real.exp (-u / 2) * unitRieszCesaroSlowPolynomial (t - u)) =
      -(Real.exp (t / 2)) * unitRieszCesaroTestSecondDeriv t (t - u) := by
  have h1 : Real.exp (t / 2) * Real.exp (-t + (t - u) / 2) = Real.exp (-u / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (t / 2) * Real.exp (-3 * t / 2 + (t - u)) = Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [unitRieszCesaroTestSecondDeriv_eq_polynomials]
  linear_combination (-(3 / 32 : ℝ) * unitRieszCesaroFastPolynomial (t - u)) * h2 +
    ((3 / 32 : ℝ) * unitRieszCesaroSlowPolynomial (t - u)) * h1

/-- **Equation (10).**  Exact reflected form of the finite-aperture reporter. -/
theorem unitRieszCesaroApertureKernel_eq_secondDeriv (t u : ℝ) :
    unitRieszCesaroApertureKernel t u =
      -(Real.exp (t / 2) / t ^ 3) * unitRieszCesaroTestSecondDeriv t (t - u) := by
  rw [unitRieszCesaroApertureKernel, unitRieszCesaroApertureNumerator]
  ring

theorem continuous_unitRieszCesaroTest (t : ℝ) :
    Continuous (unitRieszCesaroTest t) := by
  unfold unitRieszCesaroTest; fun_prop

theorem continuous_unitRieszCesaroTestDeriv (t : ℝ) :
    Continuous (unitRieszCesaroTestDeriv t) := by
  unfold unitRieszCesaroTestDeriv; fun_prop

theorem continuous_unitRieszCesaroTestSecondDeriv (t : ℝ) :
    Continuous (unitRieszCesaroTestSecondDeriv t) := by
  unfold unitRieszCesaroTestSecondDeriv; fun_prop

theorem continuous_unitRieszCesaroApertureKernel (t : ℝ) :
    Continuous (unitRieszCesaroApertureKernel t) := by
  simp only [funext (unitRieszCesaroApertureKernel_eq_secondDeriv t)]
  exact continuous_const.mul
    ((continuous_unitRieszCesaroTestSecondDeriv t).comp (continuous_const.sub continuous_id))

/-! ## Exact normalized transport -/

/-- **Equation (9).**  The exact finite-aperture FU-to-UR reporter law: after normalizing the
literal shifted completed-error response by `exp(t/2)/t^3`, the whole answer is a boundary atom
`-(3/64)` on the Cesàro primitive plus its lag pairing against the reporter kernel. -/
theorem unitRieszCesaro_normalizedTransport {b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) :
    Real.exp (t / 2) / t ^ 3 *
        (-criticalMellinCompletedError b * unitRieszCompletedSourceTestReal t b -
          ∫ s in b..t,
            criticalMellinCompletedError s * unitRieszCompletedSourceTestDerivReal t s) =
      -(3 / 64) *
          ccmCesaroPrimitive (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b t +
        ∫ u in (0 : ℝ)..(t - b),
          ccmCesaroPrimitive (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b (t - u) *
            unitRieszCesaroApertureKernel t u := by
  have ht : (0 : ℝ) < t := lt_of_lt_of_le hb hbt
  have ht3 : (t : ℝ) ^ 3 ≠ 0 := by positivity
  have hexp : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
    rw [← Real.exp_add, show t / 2 + -t / 2 = (0 : ℝ) by ring, Real.exp_zero]
  have hsub :
      (∫ u in (0 : ℝ)..(t - b),
          ccmCesaroPrimitive (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b (t - u) *
            unitRieszCesaroApertureKernel t u) =
        -(Real.exp (t / 2) / t ^ 3) *
          ∫ s in b..t,
            ccmCesaroPrimitive (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b s *
              unitRieszCesaroTestSecondDeriv t s := by
    have hpt : ∀ u : ℝ,
        ccmCesaroPrimitive (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b (t - u) *
            unitRieszCesaroApertureKernel t u =
          (-(Real.exp (t / 2) / t ^ 3)) *
            (ccmCesaroPrimitive (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b (t - u) *
              unitRieszCesaroTestSecondDeriv t (t - u)) := by
      intro u
      rw [unitRieszCesaroApertureKernel_eq_secondDeriv]
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hcs := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := t - b)
      (f := fun s => ccmCesaroPrimitive (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b s *
        unitRieszCesaroTestSecondDeriv t s) t
    simpa using hcs
  rw [unitRieszCompletedSource_eq_FUCesaroCurvature_explicitEndpoint hb hbt, hsub]
  have hcollapse :
      Real.exp (t / 2) / t ^ 3 * (-(3 / 64) * t ^ 3 * Real.exp (-t / 2)) = -(3 / 64) := by
    have hrw : Real.exp (t / 2) / t ^ 3 * (-(3 / 64) * t ^ 3 * Real.exp (-t / 2)) =
        -(3 / 64 : ℝ) * (Real.exp (t / 2) * Real.exp (-t / 2)) * (t ^ 3 / t ^ 3) := by
      ring
    rw [hrw, hexp, div_self ht3]
    ring
  linear_combination
    (ccmCesaroPrimitive (ccmGuinandWeilThirdGradeCumulativeMeasurable b) b t) * hcollapse

/-! ## Fixed-lag limit of the reporter -/

/-- Profile of the finite-aperture reporter in the reciprocal aperture `x = 1/t`. -/
def unitRieszCesaroApertureProfile (u x : ℝ) : ℝ :=
  (3 / 32) *
    (Real.exp (-u) *
        ((1 - u * x) ^ 3 + 6 * x * (1 - u * x) ^ 2 + 6 * x ^ 2 * (1 - u * x)) -
      Real.exp (-u / 2) *
        ((1 / 4) * (1 - u * x) ^ 3 + 3 * x * (1 - u * x) ^ 2 + 6 * x ^ 2 * (1 - u * x)))

theorem unitRieszCesaroApertureKernel_eq_profile {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    unitRieszCesaroApertureKernel t u = unitRieszCesaroApertureProfile u (1 / t) := by
  rw [unitRieszCesaroApertureKernel, unitRieszCesaroApertureProfile,
    unitRieszCesaroFastPolynomial, unitRieszCesaroSlowPolynomial]
  field_simp
  ring

theorem unitRieszCesaroApertureProfile_zero (u : ℝ) :
    unitRieszCesaroApertureProfile u 0 = unitRieszCesaroCurvatureKernel u := by
  rw [unitRieszCesaroApertureProfile, unitRieszCesaroCurvatureKernel]
  ring

theorem continuous_unitRieszCesaroApertureProfile (u : ℝ) :
    Continuous (unitRieszCesaroApertureProfile u) := by
  unfold unitRieszCesaroApertureProfile; fun_prop

/-- **Equation (14).**  At every fixed lag the finite-aperture reporter converges to the limiting
signed two-channel curvature kernel. -/
theorem tendsto_unitRieszCesaroApertureKernel (u : ℝ) :
    Tendsto (fun t : ℝ => unitRieszCesaroApertureKernel t u) atTop
      (nhds (unitRieszCesaroCurvatureKernel u)) := by
  have hx : Tendsto (fun t : ℝ => 1 / t) atTop (nhds 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0))
  have hcomp :
      Tendsto (fun t : ℝ => unitRieszCesaroApertureProfile u (1 / t)) atTop
        (nhds (unitRieszCesaroApertureProfile u 0)) :=
    ((continuous_unitRieszCesaroApertureProfile u).tendsto 0).comp hx
  rw [unitRieszCesaroApertureProfile_zero] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (unitRieszCesaroApertureKernel_eq_profile (ne_of_gt ht) u).symm

/-! ## Two-unit loss of origin monotonicity -/

/-- **Equations (20)–(21), iff form.**  The literal completed-source test has positive derivative
at the origin exactly past the two-unit scale `log 4 = 2 log 2`; the cofinal unit-Riesz test is
therefore not a differentiable real autocorrelation. -/
theorem unitRieszCompletedSourceTestDeriv_zero_re_pos_iff (t : ℝ) :
    0 < (unitRieszCompletedSourceTestDeriv t 0).re ↔ 2 * Real.log 2 < t := by
  rw [unitRieszCompletedSourceTestDeriv_zero_eq]
  simp only [Complex.ofReal_re]
  have hfront : (0 : ℝ) < 3 * Real.exp (-3 * t / 2) := by positivity
  have hequiv : (2 : ℝ) < Real.exp (t / 2) ↔ Real.log 2 < t / 2 := by
    constructor
    · intro hx
      calc Real.log 2 < Real.log (Real.exp (t / 2)) :=
            Real.log_lt_log (by norm_num) hx
        _ = t / 2 := Real.log_exp _
    · intro hx
      have hlt := Real.exp_lt_exp.mpr hx
      rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hlt
  have hkey : 0 < Real.exp (t / 2) / 2 - 1 ↔ 2 * Real.log 2 < t := by
    constructor
    · intro h
      have hx : (2 : ℝ) < Real.exp (t / 2) := by linarith
      have := hequiv.mp hx
      linarith
    · intro h
      have hx : Real.log 2 < t / 2 := by linarith
      have := hequiv.mpr hx
      linarith
  constructor
  · intro h
    refine hkey.mp ?_
    by_contra hc
    push_neg at hc
    nlinarith [h, hfront]
  · intro h
    exact mul_pos hfront (hkey.mpr h)

/-! ## The fast/slow ratio and its strict monotonicity -/

/-- Reduced fast/slow polynomial ratio of the renormalized second derivative. -/
def unitRieszCesaroRatio (s : ℝ) : ℝ :=
  4 * (s ^ 2 + 6 * s + 6) / (s ^ 2 + 12 * s + 24)

theorem unitRieszCesaroRatio_denom_pos {s : ℝ} (hs : 0 ≤ s) :
    (0 : ℝ) < s ^ 2 + 12 * s + 24 := by nlinarith

/-- **Equation (11).**  The fast/slow ratio in reduced form. -/
theorem unitRieszCesaroFast_div_slow_eq_ratio {s : ℝ} (hs : 0 < s) :
    unitRieszCesaroFastPolynomial s / unitRieszCesaroSlowPolynomial s =
      unitRieszCesaroRatio s :=
  unitRieszCesaroFast_div_slow hs

theorem unitRieszCesaroRatio_zero : unitRieszCesaroRatio 0 = 1 := by
  norm_num [unitRieszCesaroRatio]

theorem unitRieszCesaroRatio_pos {s : ℝ} (hs : 0 ≤ s) : 0 < unitRieszCesaroRatio s := by
  have hd := unitRieszCesaroRatio_denom_pos hs
  rw [unitRieszCesaroRatio]
  exact div_pos (by nlinarith) hd

/-- The ratio never reaches the four-unit ceiling. -/
theorem unitRieszCesaroRatio_lt_four {s : ℝ} (hs : 0 ≤ s) : unitRieszCesaroRatio s < 4 := by
  have hd := unitRieszCesaroRatio_denom_pos hs
  rw [unitRieszCesaroRatio, div_lt_iff₀ hd]
  nlinarith

/-- **Equation (12).**  The fast/slow ratio is strictly increasing on the closed positive ray;
this is exactly positivity of the derivative numerator `24(s^2+6s+12)`. -/
theorem unitRieszCesaroRatio_strictMonoOn :
    StrictMonoOn unitRieszCesaroRatio (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) ≤ x := hx
  have hy0 : (0 : ℝ) ≤ y := hy
  have hdx := unitRieszCesaroRatio_denom_pos hx0
  have hdy := unitRieszCesaroRatio_denom_pos hy0
  rw [unitRieszCesaroRatio, unitRieszCesaroRatio, div_lt_div_iff₀ hdx hdy]
  have key : 4 * (y ^ 2 + 6 * y + 6) * (x ^ 2 + 12 * x + 24) -
      4 * (x ^ 2 + 6 * x + 6) * (y ^ 2 + 12 * y + 24) =
      24 * (y - x) * (x * y + 3 * (x + y) + 12) := by ring
  nlinarith [key, mul_pos (sub_pos.mpr hxy)
    (show (0 : ℝ) < x * y + 3 * (x + y) + 12 by nlinarith)]

theorem one_lt_unitRieszCesaroRatio {s : ℝ} (hs : 0 < s) : 1 < unitRieszCesaroRatio s := by
  have h := unitRieszCesaroRatio_strictMonoOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs.le) hs
  rwa [unitRieszCesaroRatio_zero] at h

theorem continuousOn_unitRieszCesaroRatio :
    ContinuousOn unitRieszCesaroRatio (Ici (0 : ℝ)) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro s hs
  exact (unitRieszCesaroRatio_denom_pos hs).ne'

/-- The ratio saturates the four-unit ceiling asymptotically. -/
theorem tendsto_unitRieszCesaroRatio_atTop :
    Tendsto unitRieszCesaroRatio atTop (nhds 4) := by
  have hshape : ∀ s : ℝ, 0 ≤ s →
      unitRieszCesaroRatio s = 4 - (24 * s + 72) / (s ^ 2 + 12 * s + 24) := by
    intro s hs
    have hd := unitRieszCesaroRatio_denom_pos hs
    rw [unitRieszCesaroRatio]
    field_simp
    ring
  have hzero : Tendsto (fun s : ℝ => (24 * s + 72) / (s ^ 2 + 12 * s + 24)) atTop (nhds 0) := by
    refine squeeze_zero' (g := fun s : ℝ => 96 * s⁻¹) ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
      have hd := unitRieszCesaroRatio_denom_pos (by linarith : (0 : ℝ) ≤ s)
      have hnum : (0 : ℝ) ≤ 24 * s + 72 := by linarith
      exact div_nonneg hnum hd.le
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
      have hs0 : (0 : ℝ) < s := by linarith
      have hd := unitRieszCesaroRatio_denom_pos (by linarith : (0 : ℝ) ≤ s)
      rw [div_le_iff₀ hd]
      have e1 : 96 * s⁻¹ * (s ^ 2 + 12 * s + 24) = 96 * s + 1152 + 2304 * s⁻¹ := by
        field_simp; ring
      rw [e1]
      have hinv : (0 : ℝ) < s⁻¹ := inv_pos.mpr hs0
      linarith
    · have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (96 : ℝ)
      simpa using h
  have hlim : Tendsto (fun s : ℝ => 4 - (24 * s + 72) / (s ^ 2 + 12 * s + 24)) atTop
      (nhds (4 - 0)) := tendsto_const_nhds.sub hzero
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  exact (hshape s hs).symm

/-! ## The unique moving sign wall -/

/-- Zero set of this function is the moving sign wall of the finite-aperture reporter:
`u = 2 log (R(t-u)/P(t-u))`. -/
def unitRieszCesaroWallEquation (t u : ℝ) : ℝ :=
  u - 2 * Real.log (unitRieszCesaroRatio (t - u))

theorem unitRieszCesaroApertureScale_pos {t u : ℝ} (ht : 0 < t) (hu : u < t) :
    0 < (3 / 32) * Real.exp (-u) * unitRieszCesaroSlowPolynomial (t - u) / t ^ 3 := by
  have hs : (0 : ℝ) < t - u := by linarith
  have hP : (0 : ℝ) < unitRieszCesaroSlowPolynomial (t - u) := by
    unfold unitRieszCesaroSlowPolynomial; nlinarith
  exact div_pos (mul_pos (by positivity) hP) (by positivity)

/-- The reporter is a strictly positive scale times the signed ratio defect. -/
theorem unitRieszCesaroApertureKernel_eq_scaled {t u : ℝ} (ht : 0 < t) (hu : u < t) :
    unitRieszCesaroApertureKernel t u =
      ((3 / 32) * Real.exp (-u) * unitRieszCesaroSlowPolynomial (t - u) / t ^ 3) *
        (unitRieszCesaroRatio (t - u) - Real.exp (u / 2)) := by
  have hs : (0 : ℝ) < t - u := by linarith
  have hP : unitRieszCesaroSlowPolynomial (t - u) ≠ 0 := by
    unfold unitRieszCesaroSlowPolynomial; nlinarith
  have hratio : unitRieszCesaroRatio (t - u) =
      unitRieszCesaroFastPolynomial (t - u) / unitRieszCesaroSlowPolynomial (t - u) := by
    rw [unitRieszCesaroRatio, unitRieszCesaroFast_div_slow hs]
  have he : Real.exp (-u / 2) = Real.exp (-u) * Real.exp (u / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [unitRieszCesaroApertureKernel, hratio, he]
  field_simp

theorem unitRieszCesaroWallEquation_neg_iff {t u : ℝ} (hu : u < t) :
    unitRieszCesaroWallEquation t u < 0 ↔
      Real.exp (u / 2) < unitRieszCesaroRatio (t - u) := by
  have hs : (0 : ℝ) ≤ t - u := by linarith
  have hpos := unitRieszCesaroRatio_pos hs
  rw [unitRieszCesaroWallEquation, sub_neg,
    show (u < 2 * Real.log (unitRieszCesaroRatio (t - u))) ↔
        (u / 2 < Real.log (unitRieszCesaroRatio (t - u))) from
      ⟨fun h => by linarith, fun h => by linarith⟩]
  exact Real.lt_log_iff_exp_lt hpos

theorem unitRieszCesaroWallEquation_pos_iff {t u : ℝ} (hu : u < t) :
    0 < unitRieszCesaroWallEquation t u ↔
      unitRieszCesaroRatio (t - u) < Real.exp (u / 2) := by
  have hs : (0 : ℝ) ≤ t - u := by linarith
  have hpos := unitRieszCesaroRatio_pos hs
  rw [unitRieszCesaroWallEquation, sub_pos,
    show (2 * Real.log (unitRieszCesaroRatio (t - u)) < u) ↔
        (Real.log (unitRieszCesaroRatio (t - u)) < u / 2) from
      ⟨fun h => by linarith, fun h => by linarith⟩]
  exact Real.log_lt_iff_lt_exp hpos

theorem unitRieszCesaroWallEquation_eq_zero_iff {t u : ℝ} (hu : u < t) :
    unitRieszCesaroWallEquation t u = 0 ↔
      Real.exp (u / 2) = unitRieszCesaroRatio (t - u) := by
  have hs : (0 : ℝ) ≤ t - u := by linarith
  have hpos := unitRieszCesaroRatio_pos hs
  rw [unitRieszCesaroWallEquation, sub_eq_zero]
  constructor
  · intro h
    have hhalf : u / 2 = Real.log (unitRieszCesaroRatio (t - u)) := by linarith
    rw [hhalf, Real.exp_log hpos]
  · intro h
    have hlog : Real.log (Real.exp (u / 2)) =
        Real.log (unitRieszCesaroRatio (t - u)) := by rw [h]
    rw [Real.log_exp] at hlog
    linarith

/-- **Equation (13), positive side.** -/
theorem unitRieszCesaroApertureKernel_pos_iff {t u : ℝ} (ht : 0 < t) (hu : u < t) :
    0 < unitRieszCesaroApertureKernel t u ↔ unitRieszCesaroWallEquation t u < 0 := by
  have hscale := unitRieszCesaroApertureScale_pos ht hu
  rw [unitRieszCesaroApertureKernel_eq_scaled ht hu, unitRieszCesaroWallEquation_neg_iff hu]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith [h, hscale]
  · intro h
    exact mul_pos hscale (by linarith)

/-- **Equation (13), negative side.** -/
theorem unitRieszCesaroApertureKernel_neg_iff {t u : ℝ} (ht : 0 < t) (hu : u < t) :
    unitRieszCesaroApertureKernel t u < 0 ↔ 0 < unitRieszCesaroWallEquation t u := by
  have hscale := unitRieszCesaroApertureScale_pos ht hu
  rw [unitRieszCesaroApertureKernel_eq_scaled ht hu, unitRieszCesaroWallEquation_pos_iff hu]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith [h, hscale]
  · intro h
    have hneg : unitRieszCesaroRatio (t - u) - Real.exp (u / 2) < 0 := by linarith
    exact mul_neg_of_pos_of_neg hscale hneg

theorem unitRieszCesaroApertureKernel_eq_zero_iff {t u : ℝ} (ht : 0 < t) (hu : u < t) :
    unitRieszCesaroApertureKernel t u = 0 ↔ unitRieszCesaroWallEquation t u = 0 := by
  have hscale := unitRieszCesaroApertureScale_pos ht hu
  rw [unitRieszCesaroApertureKernel_eq_scaled ht hu, unitRieszCesaroWallEquation_eq_zero_iff hu]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hscale.ne'
    · linarith
  · intro h
    have : unitRieszCesaroRatio (t - u) - Real.exp (u / 2) = 0 := by linarith
    rw [this, mul_zero]

theorem continuousOn_unitRieszCesaroWallEquation (t : ℝ) :
    ContinuousOn (unitRieszCesaroWallEquation t) (Icc 0 t) := by
  have hmap : MapsTo (fun u : ℝ => t - u) (Icc 0 t) (Ici (0 : ℝ)) := by
    intro u hu
    simp only [mem_Ici]
    linarith [hu.2]
  have hcomp : ContinuousOn (fun u : ℝ => unitRieszCesaroRatio (t - u)) (Icc 0 t) :=
    continuousOn_unitRieszCesaroRatio.comp (by fun_prop) hmap
  have hlog : ContinuousOn (fun u : ℝ => Real.log (unitRieszCesaroRatio (t - u))) (Icc 0 t) := by
    refine hcomp.log ?_
    intro u hu
    exact (unitRieszCesaroRatio_pos (by linarith [hu.2] : (0 : ℝ) ≤ t - u)).ne'
  exact ContinuousOn.sub (by fun_prop) (continuousOn_const.mul hlog)

theorem unitRieszCesaroWallEquation_strictMonoOn (t : ℝ) :
    StrictMonoOn (unitRieszCesaroWallEquation t) (Icc 0 t) := by
  intro x hx y hy hxy
  have hxr : (0 : ℝ) ≤ t - x := by linarith [hx.2]
  have hyr : (0 : ℝ) ≤ t - y := by linarith [hy.2]
  have hlt : unitRieszCesaroRatio (t - y) < unitRieszCesaroRatio (t - x) :=
    unitRieszCesaroRatio_strictMonoOn (mem_Ici.mpr hyr) (mem_Ici.mpr hxr) (by linarith)
  have hlog : Real.log (unitRieszCesaroRatio (t - y)) <
      Real.log (unitRieszCesaroRatio (t - x)) :=
    Real.log_lt_log (unitRieszCesaroRatio_pos hyr) hlt
  unfold unitRieszCesaroWallEquation
  linarith

theorem unitRieszCesaroWallEquation_zero_neg {t : ℝ} (ht : 0 < t) :
    unitRieszCesaroWallEquation t 0 < 0 := by
  have h1 : 1 < unitRieszCesaroRatio t := one_lt_unitRieszCesaroRatio ht
  have hlog : 0 < Real.log (unitRieszCesaroRatio t) := Real.log_pos h1
  unfold unitRieszCesaroWallEquation
  rw [sub_zero]
  linarith

theorem unitRieszCesaroWallEquation_self_pos {t : ℝ} (ht : 0 < t) :
    0 < unitRieszCesaroWallEquation t t := by
  unfold unitRieszCesaroWallEquation
  rw [sub_self, unitRieszCesaroRatio_zero, Real.log_one]
  linarith

/-- **Equation (13).**  The finite-aperture reporter changes sign exactly once inside the
aperture. -/
theorem exists_unique_unitRieszCesaroWall {t : ℝ} (ht : 0 < t) :
    ∃! u : ℝ, u ∈ Icc (0 : ℝ) t ∧ unitRieszCesaroWallEquation t u = 0 := by
  have hcont := continuousOn_unitRieszCesaroWallEquation t
  have h0 := unitRieszCesaroWallEquation_zero_neg ht
  have h1 := unitRieszCesaroWallEquation_self_pos ht
  have hmem : (0 : ℝ) ∈
      Icc (unitRieszCesaroWallEquation t 0) (unitRieszCesaroWallEquation t t) := ⟨h0.le, h1.le⟩
  obtain ⟨u, hu, hval⟩ := intermediate_value_Icc ht.le hcont hmem
  refine ⟨u, ⟨hu, hval⟩, ?_⟩
  rintro y ⟨hy, hyval⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hmono := unitRieszCesaroWallEquation_strictMonoOn t hy hu h
    rw [hyval, hval] at hmono
    exact lt_irrefl _ hmono
  · have hmono := unitRieszCesaroWallEquation_strictMonoOn t hu hy h
    rw [hyval, hval] at hmono
    exact lt_irrefl _ hmono

/-- The moving sign wall of the finite-aperture reporter. -/
def unitRieszCesaroWall (t : ℝ) : ℝ :=
  if h : 0 < t then (exists_unique_unitRieszCesaroWall h).choose else 0

theorem unitRieszCesaroWall_spec {t : ℝ} (ht : 0 < t) :
    unitRieszCesaroWall t ∈ Icc (0 : ℝ) t ∧
      unitRieszCesaroWallEquation t (unitRieszCesaroWall t) = 0 := by
  rw [unitRieszCesaroWall, dif_pos ht]
  exact (exists_unique_unitRieszCesaroWall ht).choose_spec.1

theorem unitRieszCesaroWall_pos {t : ℝ} (ht : 0 < t) : 0 < unitRieszCesaroWall t := by
  rcases lt_or_eq_of_le (unitRieszCesaroWall_spec ht).1.1 with h | h
  · exact h
  · exfalso
    have hval := (unitRieszCesaroWall_spec ht).2
    rw [← h] at hval
    have h0 := unitRieszCesaroWallEquation_zero_neg ht
    linarith

theorem unitRieszCesaroWall_lt {t : ℝ} (ht : 0 < t) : unitRieszCesaroWall t < t := by
  rcases lt_or_eq_of_le (unitRieszCesaroWall_spec ht).1.2 with h | h
  · exact h
  · exfalso
    have hval := (unitRieszCesaroWall_spec ht).2
    rw [h] at hval
    have h1 := unitRieszCesaroWallEquation_self_pos ht
    linarith

/-- The wall is the exact implicit root `u = 2 log (R(t-u)/P(t-u))`. -/
theorem unitRieszCesaroWall_eq {t : ℝ} (ht : 0 < t) :
    unitRieszCesaroWall t =
      2 * Real.log (unitRieszCesaroRatio (t - unitRieszCesaroWall t)) := by
  have h := (unitRieszCesaroWall_spec ht).2
  unfold unitRieszCesaroWallEquation at h
  linarith

theorem log_sixteen_eq : Real.log 16 = 2 * Real.log 4 := by
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- The moving wall lies strictly below the four-unit limit at every finite aperture. -/
theorem unitRieszCesaroWall_lt_log_sixteen {t : ℝ} (ht : 0 < t) :
    unitRieszCesaroWall t < Real.log 16 := by
  have hw := unitRieszCesaroWall_eq ht
  have hlt := unitRieszCesaroWall_lt ht
  have hs : (0 : ℝ) ≤ t - unitRieszCesaroWall t := by linarith
  have hlog : Real.log (unitRieszCesaroRatio (t - unitRieszCesaroWall t)) < Real.log 4 :=
    Real.log_lt_log (unitRieszCesaroRatio_pos hs) (unitRieszCesaroRatio_lt_four hs)
  rw [log_sixteen_eq]
  linarith

theorem unitRieszCesaroApertureKernel_wall {t : ℝ} (ht : 0 < t) :
    unitRieszCesaroApertureKernel t (unitRieszCesaroWall t) = 0 :=
  (unitRieszCesaroApertureKernel_eq_zero_iff ht (unitRieszCesaroWall_lt ht)).mpr
    (unitRieszCesaroWall_spec ht).2

theorem unitRieszCesaroApertureKernel_pos_of_lt_wall
    {t u : ℝ} (ht : 0 < t) (hu0 : 0 ≤ u) (hu : u < unitRieszCesaroWall t) :
    0 < unitRieszCesaroApertureKernel t u := by
  have hwlt := unitRieszCesaroWall_lt ht
  have hut : u < t := lt_trans hu hwlt
  refine (unitRieszCesaroApertureKernel_pos_iff ht hut).mpr ?_
  have hmono := unitRieszCesaroWallEquation_strictMonoOn t
    (mem_Icc.mpr ⟨hu0, hut.le⟩)
    (mem_Icc.mpr ⟨(unitRieszCesaroWall_pos ht).le, hwlt.le⟩) hu
  rw [(unitRieszCesaroWall_spec ht).2] at hmono
  exact hmono

theorem unitRieszCesaroApertureKernel_neg_of_wall_lt
    {t u : ℝ} (ht : 0 < t) (hu : unitRieszCesaroWall t < u) (hut : u < t) :
    unitRieszCesaroApertureKernel t u < 0 := by
  refine (unitRieszCesaroApertureKernel_neg_iff ht hut).mpr ?_
  have hmono := unitRieszCesaroWallEquation_strictMonoOn t
    (mem_Icc.mpr ⟨(unitRieszCesaroWall_pos ht).le, (unitRieszCesaroWall_lt ht).le⟩)
    (mem_Icc.mpr ⟨le_trans (unitRieszCesaroWall_pos ht).le hu.le, hut.le⟩) hu
  rw [(unitRieszCesaroWall_spec ht).2] at hmono
  exact hmono

/-- **Equation (13), asymptotic form.**  The moving sign wall converges to the four-unit scale
`log 16 = 4 log 2`. -/
theorem tendsto_unitRieszCesaroWall :
    Tendsto unitRieszCesaroWall atTop (nhds (Real.log 16)) := by
  have hshift : Tendsto (fun t : ℝ => t - Real.log 16) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-Real.log 16) (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)
  have h1 : Tendsto (fun t : ℝ => unitRieszCesaroRatio (t - Real.log 16)) atTop (nhds 4) :=
    tendsto_unitRieszCesaroRatio_atTop.comp hshift
  have h2 : Tendsto (fun t : ℝ => Real.log (unitRieszCesaroRatio (t - Real.log 16))) atTop
      (nhds (Real.log 4)) :=
    ((Real.continuousAt_log (by norm_num : (4 : ℝ) ≠ 0)).tendsto).comp h1
  have h3 : Tendsto (fun t : ℝ => 2 * Real.log (unitRieszCesaroRatio (t - Real.log 16))) atTop
      (nhds (2 * Real.log 4)) := h2.const_mul 2
  rw [log_sixteen_eq]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h3 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (Real.log 16)] with t htt
    have hlog16 : (0 : ℝ) < Real.log 16 := Real.log_pos (by norm_num)
    have ht : 0 < t := lt_trans hlog16 htt
    have hw := unitRieszCesaroWall_eq ht
    have hwlt := unitRieszCesaroWall_lt_log_sixteen ht
    have h0 : (0 : ℝ) ≤ t - Real.log 16 := by linarith
    have hle : t - Real.log 16 ≤ t - unitRieszCesaroWall t := by linarith
    have hmono := unitRieszCesaroRatio_strictMonoOn.monotoneOn
      (mem_Ici.mpr h0) (mem_Ici.mpr (le_trans h0 hle)) hle
    have hlogmono := Real.log_le_log (unitRieszCesaroRatio_pos h0) hmono
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← log_sixteen_eq]
    exact (unitRieszCesaroWall_lt_log_sixteen ht).le

/-! ## Exact affine blindness of the reporter -/

theorem unitRieszCesaroTest_zero (t : ℝ) : unitRieszCesaroTest t 0 = 0 := by
  simp [unitRieszCesaroTest]

theorem unitRieszCesaroTestDeriv_zero (t : ℝ) : unitRieszCesaroTestDeriv t 0 = 0 := by
  simp [unitRieszCesaroTestDeriv]

theorem unitRieszCesaroTest_self (t : ℝ) : unitRieszCesaroTest t t = 0 := by
  unfold unitRieszCesaroTest
  rw [show -t + t / 2 = -t / 2 by ring, show -3 * t / 2 + t = -t / 2 by ring]
  ring

theorem unitRieszCesaroTest_pos {t s : ℝ} (hs : 0 < s) (hst : s < t) :
    0 < unitRieszCesaroTest t s := by
  have hexp : Real.exp (-3 * t / 2 + s) < Real.exp (-t + s / 2) := by
    rw [Real.exp_lt_exp]; linarith
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  unfold unitRieszCesaroTest
  nlinarith [hexp, hs3]

theorem integral_unitRieszCesaroTest_pos {t : ℝ} (ht : 0 < t) :
    0 < ∫ s in (0 : ℝ)..t, unitRieszCesaroTest t s := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_unitRieszCesaroTest t).intervalIntegrable _ _) ?_ ht
  intro s hs
  exact unitRieszCesaroTest_pos hs.1 hs.2

private theorem exp_half_mul_exp_neg_half (t : ℝ) :
    Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
  rw [← Real.exp_add, show t / 2 + -t / 2 = (0 : ℝ) by ring, Real.exp_zero]

/-- **Equation (15).**  The interior reporter has exact mass `3/64`, cancelled by the boundary
atom `-(3/64) δ₀` of the transport law. -/
theorem integral_unitRieszCesaroApertureKernel {t : ℝ} (ht : 0 < t) :
    (∫ u in (0 : ℝ)..t, unitRieszCesaroApertureKernel t u) = 3 / 64 := by
  have ht3 : (t : ℝ) ^ 3 ≠ 0 := by positivity
  have hpt : ∀ u : ℝ, unitRieszCesaroApertureKernel t u =
      (-(Real.exp (t / 2) / t ^ 3)) * unitRieszCesaroTestSecondDeriv t (t - u) :=
    fun u => unitRieszCesaroApertureKernel_eq_secondDeriv t u
  have hcv : (∫ u in (0 : ℝ)..t, unitRieszCesaroTestSecondDeriv t (t - u)) =
      ∫ s in (0 : ℝ)..t, unitRieszCesaroTestSecondDeriv t s := by
    simpa using intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := t) (fun s => unitRieszCesaroTestSecondDeriv t s) t
  have hftc : (∫ s in (0 : ℝ)..t, unitRieszCesaroTestSecondDeriv t s) =
      unitRieszCesaroTestDeriv t t - unitRieszCesaroTestDeriv t 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_unitRieszCesaroTestDeriv t x)
      ((continuous_unitRieszCesaroTestSecondDeriv t).intervalIntegrable _ _)
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, hcv, hftc, unitRieszCesaroTestDeriv_zero,
    unitRieszCesaroTestDeriv_endpoint]
  have hrw : -(Real.exp (t / 2) / t ^ 3) * (-(3 / 64) * t ^ 3 * Real.exp (-t / 2) - 0) =
      (3 / 64 : ℝ) * (Real.exp (t / 2) * Real.exp (-t / 2)) * (t ^ 3 / t ^ 3) := by ring
  rw [hrw, exp_half_mul_exp_neg_half, div_self ht3]
  ring

/-- **Equation (16).**  The interior reporter has vanishing first moment: the complete reporter
measure annihilates every affine function of the Cesàro coordinate. -/
theorem integral_mul_unitRieszCesaroApertureKernel {t : ℝ} (ht : 0 < t) :
    (∫ u in (0 : ℝ)..t, u * unitRieszCesaroApertureKernel t u) = 0 := by
  have hΦ : ∀ s : ℝ, HasDerivAt
      (fun x : ℝ => (t - x) * unitRieszCesaroTestDeriv t x + unitRieszCesaroTest t x)
      ((t - s) * unitRieszCesaroTestSecondDeriv t s) s := by
    intro s
    have hlin : HasDerivAt (fun x : ℝ => t - x) (-1) s := by
      simpa using (hasDerivAt_const s t).sub (hasDerivAt_id s)
    have h := (hlin.mul (hasDerivAt_unitRieszCesaroTestDeriv t s)).add
      (hasDerivAt_unitRieszCesaroTest t s)
    convert h using 1
    ring
  have hint : (∫ s in (0 : ℝ)..t, (t - s) * unitRieszCesaroTestSecondDeriv t s) = 0 := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := t)
      (fun x _ => hΦ x)
      (((continuous_const.sub continuous_id).mul
        (continuous_unitRieszCesaroTestSecondDeriv t)).intervalIntegrable _ _)
    rw [hftc, unitRieszCesaroTest_self, unitRieszCesaroTest_zero, unitRieszCesaroTestDeriv_zero]
    ring
  have hpt : ∀ u : ℝ, u * unitRieszCesaroApertureKernel t u =
      (-(Real.exp (t / 2) / t ^ 3)) *
        ((t - (t - u)) * unitRieszCesaroTestSecondDeriv t (t - u)) := by
    intro u
    rw [unitRieszCesaroApertureKernel_eq_secondDeriv]
    ring
  have hcv : (∫ u in (0 : ℝ)..t, (t - (t - u)) * unitRieszCesaroTestSecondDeriv t (t - u)) =
      ∫ s in (0 : ℝ)..t, (t - s) * unitRieszCesaroTestSecondDeriv t s := by
    simpa using intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := t) (fun s => (t - s) * unitRieszCesaroTestSecondDeriv t s) t
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, hcv, hint, mul_zero]

/-- **Equation (17).**  The exact second moment of the interior reporter is a strictly negative
multiple of the Cesàro test mass: the reporter measures oriented curvature. -/
theorem integral_sq_mul_unitRieszCesaroApertureKernel {t : ℝ} (ht : 0 < t) :
    (∫ u in (0 : ℝ)..t, u ^ 2 * unitRieszCesaroApertureKernel t u) =
      -(2 * Real.exp (t / 2) / t ^ 3) * ∫ s in (0 : ℝ)..t, unitRieszCesaroTest t s := by
  have hΦ : ∀ s : ℝ, HasDerivAt
      (fun x : ℝ => (t - x) ^ 2 * unitRieszCesaroTestDeriv t x +
        2 * (t - x) * unitRieszCesaroTest t x)
      ((t - s) ^ 2 * unitRieszCesaroTestSecondDeriv t s - 2 * unitRieszCesaroTest t s) s := by
    intro s
    have hlin : HasDerivAt (fun x : ℝ => t - x) (-1) s := by
      simpa using (hasDerivAt_const s t).sub (hasDerivAt_id s)
    have hsq : HasDerivAt (fun x : ℝ => (t - x) ^ 2) (2 * (t - s) * (-1)) s := by
      have h := hlin.pow 2
      convert h using 1
      push_cast
      ring
    have htwo : HasDerivAt (fun x : ℝ => 2 * (t - x)) (2 * (-1)) s := hlin.const_mul 2
    have h := (hsq.mul (hasDerivAt_unitRieszCesaroTestDeriv t s)).add
      (htwo.mul (hasDerivAt_unitRieszCesaroTest t s))
    convert h using 1
    ring
  have hsplit : (∫ s in (0 : ℝ)..t,
        ((t - s) ^ 2 * unitRieszCesaroTestSecondDeriv t s - 2 * unitRieszCesaroTest t s)) = 0 := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := t)
      (fun x _ => hΦ x)
      (((((continuous_const.sub continuous_id).pow 2).mul
        (continuous_unitRieszCesaroTestSecondDeriv t)).sub
        (continuous_const.mul (continuous_unitRieszCesaroTest t))).intervalIntegrable _ _)
    rw [hftc, unitRieszCesaroTest_self, unitRieszCesaroTest_zero, unitRieszCesaroTestDeriv_zero]
    ring
  have hint : (∫ s in (0 : ℝ)..t, (t - s) ^ 2 * unitRieszCesaroTestSecondDeriv t s) =
      2 * ∫ s in (0 : ℝ)..t, unitRieszCesaroTest t s := by
    have hi1 : IntervalIntegrable
        (fun s : ℝ => (t - s) ^ 2 * unitRieszCesaroTestSecondDeriv t s) volume 0 t :=
      (((continuous_const.sub continuous_id).pow 2).mul
        (continuous_unitRieszCesaroTestSecondDeriv t)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable
        (fun s : ℝ => 2 * unitRieszCesaroTest t s) volume 0 t :=
      (continuous_const.mul (continuous_unitRieszCesaroTest t)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul] at hsplit
    linarith
  have hpt : ∀ u : ℝ, u ^ 2 * unitRieszCesaroApertureKernel t u =
      (-(Real.exp (t / 2) / t ^ 3)) *
        ((t - (t - u)) ^ 2 * unitRieszCesaroTestSecondDeriv t (t - u)) := by
    intro u
    rw [unitRieszCesaroApertureKernel_eq_secondDeriv]
    ring
  have hcv : (∫ u in (0 : ℝ)..t, (t - (t - u)) ^ 2 * unitRieszCesaroTestSecondDeriv t (t - u)) =
      ∫ s in (0 : ℝ)..t, (t - s) ^ 2 * unitRieszCesaroTestSecondDeriv t s := by
    simpa using intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := t) (fun s => (t - s) ^ 2 * unitRieszCesaroTestSecondDeriv t s) t
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, hcv, hint]
  ring

theorem integral_sq_mul_unitRieszCesaroApertureKernel_neg {t : ℝ} (ht : 0 < t) :
    (∫ u in (0 : ℝ)..t, u ^ 2 * unitRieszCesaroApertureKernel t u) < 0 := by
  rw [integral_sq_mul_unitRieszCesaroApertureKernel ht]
  have hpos := integral_unitRieszCesaroTest_pos ht
  have hscale : (0 : ℝ) < 2 * Real.exp (t / 2) / t ^ 3 := by positivity
  nlinarith [hpos, hscale]

end GaloisForLFunctions.RHTower
