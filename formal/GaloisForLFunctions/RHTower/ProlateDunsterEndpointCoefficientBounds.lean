import GaloisForLFunctions.RHTower.ProlateRadialEndpointBounds

/-!
# Quantitative endpoint Wronskian coefficients for actual radial prolate modes

Endpoint-anchored transport identifies both Dunster coefficients as improper defect integrals.
The zero-free collar gives `|U| <= 2`; the weighted defect is at most `40`; and the logarithmic
Bessel branch is controlled by an integrable `1/sqrt(x^2-1)` envelope.  At the deterministic
matching point this yields the unconditional coefficient bounds

```text
|F_regular| <= 18/c,
|F_log - pi/4| <= 141/c.
```
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter MeasureTheory Set Topology intervalIntegral

private def radialEndpointRegularIntegrand (s c : ℝ) (R : ℝ → ℝ) (x : ℝ) : ℝ :=
  lgWeight s x * lgNormalFormDefect s c (radialProlateQ s c) x *
    (comparisonSol (prolateNormalFormSol R) s x * lgBesselModel s c x)

private def radialEndpointLogIntegrand (s c : ℝ) (R : ℝ → ℝ) (x : ℝ) : ℝ :=
  lgWeight s x * lgNormalFormDefect s c (radialProlateQ s c) x *
    (comparisonSol (prolateNormalFormSol R) s x * lgBesselModel2 s c x)

private def radialEndpointLogMajorant (c x : ℝ) : ℝ :=
  320 + (120 / c) * (1 / Real.sqrt (x ^ 2 - 1))

private theorem abs_radialEndpointRegularIntegrand_le {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hx1 : 1 < x) (hx2 : x ≤ dunsterEndpointCrossing c) :
    |radialEndpointRegularIntegrand s c R x| ≤ 80 := by
  have hU := abs_comparisonSol_prolateNormalForm_le_two_to_crossing
    hs0 hs1 hc hR1 hR hDR hode hx1 hx2
  have hV : |lgBesselModel s c x| ≤ 1 := by
    rw [lgBesselModel]
    exact abs_besselJ0_le_one _
  have hm := lgWeight_mul_abs_defect_le (c := c) hs0 hs1 hx1
  have hm0 := (lgWeight_pos hs0 hs1 hx1).le
  simp only [radialEndpointRegularIntegrand, abs_mul, abs_of_nonneg hm0]
  have hUV : |comparisonSol (prolateNormalFormSol R) s x| * |lgBesselModel s c x|
      ≤ 2 := by
    have := mul_le_mul hU hV (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hmul := mul_le_mul hm hUV (by positivity : (0 : ℝ) ≤
    |comparisonSol (prolateNormalFormSol R) s x| * |lgBesselModel s c x|) (by norm_num)
  norm_num at hmul ⊢
  simpa only [abs_mul] using hmul

private theorem abs_radialEndpointLogIntegrand_le {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hx1 : 1 < x) (hx2 : x ≤ dunsterEndpointCrossing c) :
    |radialEndpointLogIntegrand s c R x| ≤ radialEndpointLogMajorant c x := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hd0 : 0 < x ^ 2 - 1 := by nlinarith
  have hsqrt0 : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr hd0
  have hU := abs_comparisonSol_prolateNormalForm_le_two_to_crossing
    hs0 hs1 hc hR1 hR hDR hode hx1 hx2
  have hV := abs_lgBesselModel2_le_endpoint_envelope hs0 hs1 hc hx1 hx2
  have hm := lgWeight_mul_abs_defect_le (c := c) hs0 hs1 hx1
  have hm0 := (lgWeight_pos hs0 hs1 hx1).le
  simp only [radialEndpointLogIntegrand, abs_mul, abs_of_nonneg hm0]
  have hEnv0 : 0 ≤ 4 + 3 / (2 * c * Real.sqrt (x ^ 2 - 1)) := by positivity
  have hUV : |comparisonSol (prolateNormalFormSol R) s x| * |lgBesselModel2 s c x|
      ≤ 2 * (4 + 3 / (2 * c * Real.sqrt (x ^ 2 - 1))) :=
    mul_le_mul hU hV (abs_nonneg _) (by norm_num)
  have hmul := mul_le_mul hm hUV (by positivity : (0 : ℝ) ≤
    |comparisonSol (prolateNormalFormSol R) s x| * |lgBesselModel2 s c x|) (by norm_num)
  have hmajorant : 40 * (2 * (4 + 3 / (2 * c * Real.sqrt (x ^ 2 - 1))))
      = radialEndpointLogMajorant c x := by
    rw [radialEndpointLogMajorant]
    field_simp [hc0.ne', hsqrt0.ne']
    ring
  rw [← hmajorant]
  simpa only [abs_mul] using hmul

private theorem continuousOn_radialEndpointRegularIntegrand {s c A B : ℝ}
    {R DR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hA : 1 < A) (_hAB : A ≤ B)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) :
    ContinuousOn (radialEndpointRegularIntegrand s c R) (Icc A B) := by
  have hsub : Icc A B ⊆ Ioi (1 : ℝ) := fun t ht => lt_of_lt_of_le hA ht.1
  have hU : ContinuousOn (comparisonSol (prolateNormalFormSol R) s) (Icc A B) :=
    fun t ht => (hasDerivAt_radialComparison hs0 hs1 (hsub ht) (hR t)).continuousAt.continuousWithinAt
  exact ((((continuousOn_lgWeight hs0 hs1).mono hsub).mul
    ((continuousOn_lgNormalFormDefect_radialProlate hs0 hs1).mono hsub)).mul
      (hU.mul ((continuousOn_lgBesselModel hs0).mono hsub)))

private theorem continuousOn_radialEndpointLogIntegrand {s c A B : ℝ}
    {R DR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hA : 1 < A) (_hAB : A ≤ B)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t) :
    ContinuousOn (radialEndpointLogIntegrand s c R) (Icc A B) := by
  have hsub : Icc A B ⊆ Ioi (1 : ℝ) := fun t ht => lt_of_lt_of_le hA ht.1
  have hU : ContinuousOn (comparisonSol (prolateNormalFormSol R) s) (Icc A B) :=
    fun t ht => (hasDerivAt_radialComparison hs0 hs1 (hsub ht) (hR t)).continuousAt.continuousWithinAt
  exact ((((continuousOn_lgWeight hs0 hs1).mono hsub).mul
    ((continuousOn_lgNormalFormDefect_radialProlate hs0 hs1).mono hsub)).mul
      (hU.mul ((continuousOn_lgBesselModel2 hs0 hs1 hc).mono hsub)))

private theorem abs_integral_radialEndpointRegularIntegrand_le {s c A B : ℝ}
    {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hA : 1 < A) (hAB : A ≤ B) (hB : B ≤ dunsterEndpointCrossing c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |∫ t in A..B, radialEndpointRegularIntegrand s c R t| ≤ 80 * (B - A) := by
  have hfcont := continuousOn_radialEndpointRegularIntegrand (c := c) hs0 hs1 hA hAB hR
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := radialEndpointRegularIntegrand s c R) hAB
  have hfcontU : ContinuousOn (fun t => |radialEndpointRegularIntegrand s c R t|)
      (uIcc A B) := by
    rw [uIcc_of_le hAB]
    exact hfcont.abs
  have hmono : (∫ t in A..B, |radialEndpointRegularIntegrand s c R t|)
      ≤ ∫ _t in A..B, (80 : ℝ) := by
    refine intervalIntegral.integral_mono_on hAB hfcontU.intervalIntegrable
      intervalIntegrable_const fun t ht => ?_
    exact abs_radialEndpointRegularIntegrand_le hs0 hs1 hc hR1 hR hDR hode
      (lt_of_lt_of_le hA ht.1) (le_trans ht.2 hB)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hfinal := hnorm.trans hmono
  simpa only [Real.norm_eq_abs, mul_comm] using hfinal

private theorem continuousOn_radialEndpointLogMajorant {c : ℝ} (_hc : 0 < c) :
    ContinuousOn (radialEndpointLogMajorant c) (Ioi (1 : ℝ)) := by
  have hsqrt : ContinuousOn (fun t : ℝ => Real.sqrt (t ^ 2 - 1)) (Ioi (1 : ℝ)) :=
    Real.continuous_sqrt.comp_continuousOn (by fun_prop)
  have hsqrtne : ∀ t ∈ Ioi (1 : ℝ), Real.sqrt (t ^ 2 - 1) ≠ 0 := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    exact (Real.sqrt_pos.mpr (by nlinarith)).ne'
  change ContinuousOn (fun x : ℝ => 320 + (120 / c) *
    (1 / Real.sqrt (x ^ 2 - 1))) (Ioi (1 : ℝ))
  exact continuousOn_const.add (continuousOn_const.mul
    (continuousOn_const.div hsqrt hsqrtne))

private theorem abs_integral_radialEndpointLogIntegrand_le {s c A B : ℝ}
    {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hA : 1 < A) (hAB : A ≤ B) (hB : B ≤ dunsterEndpointCrossing c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |∫ t in A..B, radialEndpointLogIntegrand s c R t|
      ≤ 320 * (B - A) + (120 / c) *
        (GaloisForLFunctions.HTGeometry.endpointLog B -
          GaloisForLFunctions.HTGeometry.endpointLog A) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hsub : uIcc A B ⊆ Ioi (1 : ℝ) := by
    rw [uIcc_of_le hAB]
    exact fun t ht => lt_of_lt_of_le hA ht.1
  have hfcont := continuousOn_radialEndpointLogIntegrand (c := c) hs0 hs1 hc0 hA hAB hR
  have hgcont := (continuousOn_radialEndpointLogMajorant hc0).mono hsub
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := radialEndpointLogIntegrand s c R) hAB
  have hfcontU : ContinuousOn (fun t => |radialEndpointLogIntegrand s c R t|)
      (uIcc A B) := by
    rw [uIcc_of_le hAB]
    exact hfcont.abs
  have hmono : (∫ t in A..B, |radialEndpointLogIntegrand s c R t|)
      ≤ ∫ t in A..B, radialEndpointLogMajorant c t := by
    refine intervalIntegral.integral_mono_on hAB hfcontU.intervalIntegrable
      hgcont.intervalIntegrable fun t ht => ?_
    exact abs_radialEndpointLogIntegrand_le hs0 hs1 hc hR1 hR hDR hode
      (lt_of_lt_of_le hA ht.1) (le_trans ht.2 hB)
  have hFTC : (∫ t in A..B, radialEndpointLogMajorant c t)
      = 320 * (B - A) + (120 / c) *
        (GaloisForLFunctions.HTGeometry.endpointLog B -
          GaloisForLFunctions.HTGeometry.endpointLog A) := by
    have hprimitive := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => 320 * t + (120 / c) *
        GaloisForLFunctions.HTGeometry.endpointLog t)
      (fun t ht => by
        have ht1 : 1 < t := hsub ht
        have hder := (hasDerivAt_id t).const_mul 320 |>.add
          ((GaloisForLFunctions.HTGeometry.hasDerivAt_endpointLog ht1).const_mul (120 / c))
        convert hder using 1
        · funext y
          simp only [Pi.add_apply, id_eq]
          ring
        · change 320 + (120 / c) * (1 / Real.sqrt (t ^ 2 - 1)) =
            320 + (120 / c) * (1 / Real.sqrt (t ^ 2 - 1))
          rfl)
      hgcont.intervalIntegrable
    calc
      (∫ t in A..B, radialEndpointLogMajorant c t) =
          (320 * B + (120 / c) * GaloisForLFunctions.HTGeometry.endpointLog B) -
            (320 * A + (120 / c) * GaloisForLFunctions.HTGeometry.endpointLog A) := hprimitive
      _ = 320 * (B - A) + (120 / c) *
          (GaloisForLFunctions.HTGeometry.endpointLog B -
            GaloisForLFunctions.HTGeometry.endpointLog A) := by ring
  rw [hFTC] at hmono
  simpa only [Real.norm_eq_abs] using hnorm.trans hmono

private theorem endpointLog_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ GaloisForLFunctions.HTGeometry.endpointLog x := by
  rw [GaloisForLFunctions.HTGeometry.endpointLog]
  exact Real.log_nonneg (by nlinarith [Real.sqrt_nonneg (x ^ 2 - 1)])

/-- Regular-branch endpoint coefficient at the matching point is `O(c^-1)`. -/
theorem abs_radialProlate_regularCoefficient_crossing_le {s c : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |lgEndpointRegularIntegral s c
      (comparisonSol (prolateNormalFormSol R) s)
      (comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s)
      (dunsterEndpointCrossing c)| ≤ 18 / c := by
  let B := dunsterEndpointCrossing c
  let U := comparisonSol (prolateNormalFormSol R) s
  let DU := comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hB1 : 1 < B := dunsterEndpointCrossing_gt_one hc0
  have hlim := radialProlate_tendsto_integral_lgBesselWronskian_at_endpoint
    hs0 hs1 hc0 hB1 (hR 1).continuousAt (hDR 1).continuousAt hR1
    (fun x _ => hR x) (fun x _ => hDR x) (fun x _ => hode x)
  change Tendsto (fun A : ℝ => ∫ t in A..B, radialEndpointRegularIntegrand s c R t)
      (nhdsWithin 1 (Ioi 1))
      (nhds (lgEndpointRegularIntegral s c U DU B)) at hlim
  have hAB : ∀ᶠ A : ℝ in nhdsWithin 1 (Ioi 1), A ≤ B := by
    have hid : Tendsto (fun A : ℝ => A) (nhdsWithin 1 (Ioi 1)) (nhds 1) :=
      tendsto_id.mono_left inf_le_left
    exact (hid.eventually (Iio_mem_nhds hB1)).mono fun _ h => h.le
  have hevent : ∀ᶠ A : ℝ in nhdsWithin 1 (Ioi 1),
      (∫ t in A..B, radialEndpointRegularIntegrand s c R t) ∈ Icc (-(18 / c)) (18 / c) := by
    filter_upwards [self_mem_nhdsWithin, hAB] with A hA hAle
    have hraw := abs_integral_radialEndpointRegularIntegrand_le hs0 hs1 hc hA hAle le_rfl
      hR1 hR hDR hode
    have hBsub : B - 1 = 9 / (8 * c ^ 2) := dunsterEndpointCrossing_sub_one
    have hfinal : |∫ t in A..B, radialEndpointRegularIntegrand s c R t| ≤ 18 / c := by
      have hA1 : (1 : ℝ) < A := hA
      have hstep : 80 * (B - A) ≤ 80 * (B - 1) :=
        mul_le_mul_of_nonneg_left (by linarith [hA1]) (by norm_num)
      have hconst : 80 * (B - 1) ≤ 18 / c := by
        rw [hBsub]
        have heq : 80 * (9 / (8 * c ^ 2)) = 90 / c ^ 2 := by ring
        have hrhs : 18 / c = (18 * c) / c ^ 2 := by field_simp [hc0.ne']
        rw [heq, hrhs, div_le_div_iff₀ (sq_pos_of_pos hc0) (sq_pos_of_pos hc0)]
        nlinarith
      exact hraw.trans (hstep.trans hconst)
    exact (abs_le.mp hfinal)
  exact abs_le.mpr (isClosed_Icc.mem_of_tendsto hlim hevent)

/-- Logarithmic-branch coefficient differs from its exact endpoint value `pi/4` by `O(c^-1)`. -/
theorem abs_radialProlate_logCoefficient_sub_pi_div_four_crossing_le
    {s c : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    |lgEndpointLogIntegral s c
      (comparisonSol (prolateNormalFormSol R) s)
      (comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s)
      (dunsterEndpointCrossing c)| ≤ 141 / c := by
  let B := dunsterEndpointCrossing c
  let U := comparisonSol (prolateNormalFormSol R) s
  let DU := comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hB1 : 1 < B := dunsterEndpointCrossing_gt_one hc0
  have hlim := radialProlate_tendsto_integral_lgBessel2Wronskian_at_endpoint
    hs0 hs1 hc0 hB1 (hR 1).continuousAt (hDR 1).continuousAt hR1
    (fun x _ => hR x) (fun x _ => hDR x) (fun x _ => hode x)
  change Tendsto (fun A : ℝ => ∫ t in A..B, radialEndpointLogIntegrand s c R t)
      (nhdsWithin 1 (Ioi 1))
      (nhds (lgEndpointLogIntegral s c U DU B)) at hlim
  have hAB : ∀ᶠ A : ℝ in nhdsWithin 1 (Ioi 1), A ≤ B := by
    have hid : Tendsto (fun A : ℝ => A) (nhdsWithin 1 (Ioi 1)) (nhds 1) :=
      tendsto_id.mono_left inf_le_left
    exact (hid.eventually (Iio_mem_nhds hB1)).mono fun _ h => h.le
  have hevent : ∀ᶠ A : ℝ in nhdsWithin 1 (Ioi 1),
      (∫ t in A..B, radialEndpointLogIntegrand s c R t) ∈ Icc (-(141 / c)) (141 / c) := by
    filter_upwards [self_mem_nhdsWithin, hAB] with A hA hAle
    have hraw := abs_integral_radialEndpointLogIntegrand_le hs0 hs1 hc hA hAle le_rfl
      hR1 hR hDR hode
    have hlogA := endpointLog_nonneg hA.le
    have hlogB := endpointLog_crossing_le_twenty_div_seven_c hs0 hs1 hc
    have hBsub : B - 1 = 9 / (8 * c ^ 2) := dunsterEndpointCrossing_sub_one
    have hfirst : 320 * (B - A) ≤ 360 / c ^ 2 := by
      have hA1 : (1 : ℝ) < A := hA
      have hstep : 320 * (B - A) ≤ 320 * (B - 1) :=
        mul_le_mul_of_nonneg_left (by linarith [hA1]) (by norm_num)
      calc
        320 * (B - A) ≤ 320 * (B - 1) := hstep
        _ = 360 / c ^ 2 := by rw [hBsub]; ring
    have hsecond : (120 / c) *
        (GaloisForLFunctions.HTGeometry.endpointLog B -
          GaloisForLFunctions.HTGeometry.endpointLog A) ≤ 2400 / (7 * c ^ 2) := by
      have hdiff : GaloisForLFunctions.HTGeometry.endpointLog B -
          GaloisForLFunctions.HTGeometry.endpointLog A ≤ 20 / (7 * c) := by linarith
      calc
        (120 / c) * (GaloisForLFunctions.HTGeometry.endpointLog B -
            GaloisForLFunctions.HTGeometry.endpointLog A)
            ≤ (120 / c) * (20 / (7 * c)) :=
              mul_le_mul_of_nonneg_left hdiff (by positivity)
        _ = 2400 / (7 * c ^ 2) := by field_simp [hc0.ne']; ring
    have hconstant : 360 / c ^ 2 + 2400 / (7 * c ^ 2) ≤ 141 / c := by
      have hleft : 360 / c ^ 2 + 2400 / (7 * c ^ 2) = (4920 / 7) / c ^ 2 := by ring
      have hright : 141 / c = (141 * c) / c ^ 2 := by field_simp [hc0.ne']
      rw [hleft, hright, div_le_div_iff₀ (sq_pos_of_pos hc0) (sq_pos_of_pos hc0)]
      nlinarith
    have hfinal : |∫ t in A..B, radialEndpointLogIntegrand s c R t| ≤ 141 / c :=
      hraw.trans ((add_le_add hfirst hsecond).trans hconstant)
    exact abs_le.mp hfinal
  exact abs_le.mpr (isClosed_Icc.mem_of_tendsto hlim hevent)

end GaloisForLFunctions.RHTower

end
