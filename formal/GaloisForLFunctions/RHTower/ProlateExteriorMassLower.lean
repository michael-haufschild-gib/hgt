import GaloisForLFunctions.RHTower.BesselEnergyFloor
import GaloisForLFunctions.RHTower.ProlateExteriorMassBound

/-!
# The exterior mass from below

The exterior density of an endpoint-normalised radial mode is `c R²`, and the corpus transfers it to
the Bessel density `B = (√c · A_s · J₀(cΞ))²` with `L¹` error `O(1/c)`.  What was missing was a lower
bound for `∫ B`, which no envelope can give because `J₀` vanishes at its zeros.

The route here is exact rather than asymptotic.  Pointwise,

```text
A_s(x)² / Ξ'(x) = Ξ_s(x) / (x²−s) ,
```

an identity, not an estimate — so on a window bounded away from the endpoint the density dominates a
constant multiple of `Ξ'(x)·J₀(cΞ(x))²`, which is exactly the shape a change of variables consumes.
Under `u = cΞ(x)` that integral becomes `∫ J₀(u)² du = ∫ (√u J₀(u))²/u du`, and the normal form's
mass grows linearly by `besselMass_lower_tiled`.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

section

variable {s c x : ℝ}

/-- The square of the exterior amplitude. -/
theorem xiAmplitude_sq (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiAmplitude s x ^ 2
      = xiEndpointPhase s x / Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have h1 : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hz : (0 : ℝ) < (x ^ 2 - 1) * (x ^ 2 - s) := mul_pos h1 h2
  have hsz : (0 : ℝ) < Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) := Real.sqrt_pos.2 hz
  have hphase : 0 ≤ xiEndpointPhase s x := by
    have := (xiEndpointPhase_bounds hs0 (by linarith) hx.le).1
    have hnn : (0 : ℝ) ≤ Real.sqrt (1 - s) * Real.sqrt (x ^ 2 - 1) := by positivity
    linarith
  rw [xiAmplitude, div_pow, Real.sq_sqrt hphase, Real.sq_sqrt hsz.le]

/-- **The amplitude-to-speed identity.**  `A² / Ξ' = Ξ/(x²−s)`, exactly. -/
theorem xiAmplitude_sq_eq_mul_xiSpeed (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    xiAmplitude s x ^ 2 = xiEndpointPhase s x / (x ^ 2 - s) * xiSpeed s x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have h1 : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hsq : Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s))
      = Real.sqrt (x ^ 2 - 1) * Real.sqrt (x ^ 2 - s) := Real.sqrt_mul h1.le _
  have hs1' : Real.sqrt (x ^ 2 - 1) > 0 := Real.sqrt_pos.2 h1
  have hs2' : Real.sqrt (x ^ 2 - s) > 0 := Real.sqrt_pos.2 h2
  have hspeed : xiSpeed s x = Real.sqrt (x ^ 2 - s) / Real.sqrt (x ^ 2 - 1) := by
    rw [xiSpeed, Real.sqrt_div h2.le]
  have hsq1 : Real.sqrt (x ^ 2 - 1) * Real.sqrt (x ^ 2 - 1) = x ^ 2 - 1 :=
    Real.mul_self_sqrt h1.le
  have hsq2 : Real.sqrt (x ^ 2 - s) * Real.sqrt (x ^ 2 - s) = x ^ 2 - s :=
    Real.mul_self_sqrt h2.le
  have hsqsq : Real.sqrt (x ^ 2 - s) ^ 2 = x ^ 2 - s := Real.sq_sqrt h2.le
  rw [xiAmplitude_sq hs0 hs1 hx, hsq, hspeed]
  field_simp
  rw [hsqsq]

/-- The Bessel density in amplitude form. -/
theorem radialProlateBesselDensity_eq (hc : 0 ≤ c) :
    radialProlateBesselDensity s c x
      = c * xiAmplitude s x ^ 2 * besselJ0 (c * xiEndpointPhase s x) ^ 2 := by
  rw [radialProlateBesselDensity, mul_pow, mul_pow, Real.sq_sqrt hc]

/-- The phase on the window `[2,3]` is bounded below by `61/50`. -/
theorem xiEndpointPhase_ge_window (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx2 : 2 ≤ x) :
    (61 : ℝ) / 50 ≤ xiEndpointPhase s x := by
  have hx : (1 : ℝ) < x := by linarith
  have hlow := (xiEndpointPhase_bounds hs0 (by linarith) hx.le).1
  have h1 : Real.sqrt (1 / 2 : ℝ) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt 3 ≤ Real.sqrt (x ^ 2 - 1) := Real.sqrt_le_sqrt (by nlinarith)
  have h3 : (0 : ℝ) ≤ Real.sqrt (1 / 2 : ℝ) := Real.sqrt_nonneg _
  have h4 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hprod : Real.sqrt (1 / 2 : ℝ) * Real.sqrt 3 ≤ Real.sqrt (1 - s) * Real.sqrt (x ^ 2 - 1) :=
    mul_le_mul h1 h2 h4 (le_trans h3 h1)
  have hmul : Real.sqrt (1 / 2 : ℝ) * Real.sqrt 3 = Real.sqrt (3 / 2) := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  have hge : (61 : ℝ) / 50 ≤ Real.sqrt (3 / 2) := by
    rw [show (61 : ℝ) / 50 = Real.sqrt ((61 / 50) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  rw [hmul] at hprod
  linarith [hlow, hprod, hge]

/-- **The density dominates the speed on the window.**  The exact amplitude identity turns the
density into the shape a change of variables consumes. -/
theorem besselDensity_ge_speed (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hx2 : 2 ≤ x) (hx3 : x ≤ 3) :
    1 / 8 * ((c * xiSpeed s x) * besselJ0 (c * xiEndpointPhase s x) ^ 2)
      ≤ radialProlateBesselDensity s c x := by
  have hx : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have h2 : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hxi := xiEndpointPhase_ge_window hs0 hs1 hx2
  have hratio : (1 : ℝ) / 8 ≤ xiEndpointPhase s x / (x ^ 2 - s) := by
    rw [le_div_iff₀ h2]
    nlinarith [hxi, hx3, hs0, hx2]
  have hspeed : 0 ≤ xiSpeed s x := Real.sqrt_nonneg _
  have hJ : (0 : ℝ) ≤ besselJ0 (c * xiEndpointPhase s x) ^ 2 := sq_nonneg _
  rw [radialProlateBesselDensity_eq hc.le, xiAmplitude_sq_eq_mul_xiSpeed hs0 hs1 hx]
  have hstep : 1 / 8 * (c * xiSpeed s x)
      ≤ c * (xiEndpointPhase s x / (x ^ 2 - s) * xiSpeed s x) := by
    have h := mul_le_mul_of_nonneg_right hratio (mul_nonneg hc.le hspeed)
    nlinarith [h]
  nlinarith [hstep, hJ]

/-- **The change of variables.**  Under `u = cΞ(x)` the dominating integral becomes `∫ J₀(u)² du`. -/
theorem integral_speed_besselJ0_sq (hs0 : 0 ≤ s) :
    (∫ x in (2 : ℝ)..3, (c * xiSpeed s x) * besselJ0 (c * xiEndpointPhase s x) ^ 2)
      = ∫ u in (c * xiEndpointPhase s 2)..(c * xiEndpointPhase s 3), besselJ0 u ^ 2 := by
  have huIcc : uIcc (2 : ℝ) 3 = Icc (2 : ℝ) 3 := uIcc_of_le (by norm_num)
  have hderiv : ∀ x ∈ uIcc (2 : ℝ) 3,
      HasDerivAt (fun t : ℝ => c * xiEndpointPhase s t) (c * xiSpeed s x) x := by
    intro x hx
    rw [huIcc] at hx
    exact (hasDerivAt_xiEndpointPhase hs0 (by linarith [hx.1])).const_mul c
  have hcont : ContinuousOn (fun x : ℝ => c * xiSpeed s x) (uIcc (2 : ℝ) 3) := by
    rw [huIcc]
    exact continuousOn_const.mul ((continuousOn_xiSpeed s).mono
      (fun t ht => by exact lt_of_lt_of_le (by norm_num) ht.1))
  exact intervalIntegral.integral_deriv_smul_comp hderiv hcont
    (continuous_besselJ0.pow 2)

theorem besselJ0_sq_eq_normalForm {u : ℝ} (hu : 0 < u) :
    besselJ0 u ^ 2 = besselNormalForm u ^ 2 / u := by
  rw [besselNormalForm, mul_pow, Real.sq_sqrt hu.le]
  field_simp

/-- **The `u`-integral from below**, by tiling the normal-form mass. -/
theorem integral_besselJ0_sq_ge {u₁ u₂ : ℝ} (h1 : 1 ≤ u₁) (n : ℕ)
    (hn : u₁ + 4 * (n : ℝ) ≤ u₂) :
    (n : ℝ) * (4 / 9 * besselEnergyFloor) / u₂ ≤ ∫ u in u₁..u₂, besselJ0 u ^ 2 := by
  have hu1 : (0 : ℝ) < u₁ := lt_of_lt_of_le zero_lt_one h1
  have hn0 : (0 : ℝ) ≤ 4 * (n : ℝ) := by positivity
  have h12 : u₁ ≤ u₂ := by linarith
  have hu2 : (0 : ℝ) < u₂ := lt_of_lt_of_le hu1 h12
  have hwc : Continuous fun u : ℝ => besselNormalForm u ^ 2 :=
    continuous_besselNormalForm.pow 2
  have hJc : Continuous fun u : ℝ => besselJ0 u ^ 2 := continuous_besselJ0.pow 2
  -- pointwise: J₀² ≥ w²/u₂
  have hpt : (∫ u in u₁..u₂, besselNormalForm u ^ 2 / u₂)
      ≤ ∫ u in u₁..u₂, besselJ0 u ^ 2 := by
    refine intervalIntegral.integral_mono_on h12 ((hwc.div_const u₂).intervalIntegrable _ _)
      (hJc.intervalIntegrable _ _) fun u hu => ?_
    have hupos : (0 : ℝ) < u := lt_of_lt_of_le hu1 hu.1
    rw [besselJ0_sq_eq_normalForm hupos]
    refine div_le_div_of_nonneg_left (sq_nonneg _) hupos ?_
    exact hu.2
  have hdiv : (∫ u in u₁..u₂, besselNormalForm u ^ 2 / u₂)
      = (∫ u in u₁..u₂, besselNormalForm u ^ 2) / u₂ := by
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const]
  -- tiling on the left part
  have htile := besselMass_lower_tiled h1 n
  have hrest : (∫ u in u₁..(u₁ + 4 * (n : ℝ)), besselNormalForm u ^ 2)
      ≤ ∫ u in u₁..u₂, besselNormalForm u ^ 2 := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (f := fun u : ℝ => besselNormalForm u ^ 2) (μ := MeasureTheory.volume)
      (a := u₁) (b := u₁ + 4 * (n : ℝ)) (c := u₂)
      (hwc.intervalIntegrable _ _) (hwc.intervalIntegrable _ _)
    have hnn : (0 : ℝ) ≤ ∫ u in (u₁ + 4 * (n : ℝ))..u₂, besselNormalForm u ^ 2 :=
      intervalIntegral.integral_nonneg hn fun _ _ => sq_nonneg _
    linarith [hadd, hnn]
  rw [div_le_iff₀ hu2]
  have hkey : (n : ℝ) * (4 / 9 * besselEnergyFloor)
      ≤ ∫ u in u₁..u₂, besselNormalForm u ^ 2 := le_trans htile hrest
  have hfin : (∫ u in u₁..u₂, besselNormalForm u ^ 2) / u₂ ≤ ∫ u in u₁..u₂, besselJ0 u ^ 2 := by
    rw [← hdiv]
    exact hpt
  have hfin' : (∫ u in u₁..u₂, besselNormalForm u ^ 2)
      ≤ (∫ u in u₁..u₂, besselJ0 u ^ 2) * u₂ := (div_le_iff₀ hu2).mp hfin
  linarith [hkey, hfin']

/-- The phase increases by at least one across the window. -/
theorem one_le_xiEndpointPhase_gap (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    1 ≤ xiEndpointPhase s 3 - xiEndpointPhase s 2 := by
  have hcont : ContinuousOn (xiSpeed s) (uIcc (2 : ℝ) 3) := by
    rw [uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)]
    exact (continuousOn_xiSpeed s).mono fun t ht => lt_of_lt_of_le (by norm_num) ht.1
  have hint : IntervalIntegrable (xiSpeed s) MeasureTheory.volume 2 3 := hcont.intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (f := xiSpeed s) (μ := MeasureTheory.volume) (a := (1 : ℝ)) (b := (2 : ℝ)) (c := (3 : ℝ))
    (intervalIntegrable_xiSpeed hs0 (by norm_num : (1:ℝ) ≤ 2)) hint
  have hmono : (∫ _t in (2:ℝ)..3, (1:ℝ)) ≤ ∫ t in (2:ℝ)..3, xiSpeed s t := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_const : Continuous fun _ : ℝ => (1:ℝ)).intervalIntegrable _ _) hint
      fun t ht => ?_
    exact one_le_xiSpeed hs1 (by linarith [ht.1])
  have hconst : (∫ _t in (2:ℝ)..3, (1:ℝ)) = 1 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  rw [hconst] at hmono
  rw [xiEndpointPhase, xiEndpointPhase]
  linarith [hadd, hmono]

/-- **The Bessel density carries absolute mass on the window `[2,3]`.**  Every constant is explicit
and none depends on the aperture. -/
theorem integral_window_besselDensity_ge (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 8 ≤ c) :
    besselEnergyFloor / 432 ≤ ∫ x in (2 : ℝ)..3, radialProlateBesselDensity s c x := by
  have hc0 : (0 : ℝ) < c := by linarith
  set n : ℕ := ⌊c / 4⌋₊ with hndef
  have hn4 : 4 * (n : ℝ) ≤ c := by
    have h := Nat.floor_le (by positivity : (0:ℝ) ≤ c / 4)
    rw [← hndef] at h
    linarith
  have hnlow : c / 8 ≤ (n : ℝ) := by
    have h := Nat.lt_floor_add_one (c / 4)
    rw [← hndef] at h
    linarith
  -- the endpoints of the substituted integral
  have hxi2 : (61 : ℝ) / 50 ≤ xiEndpointPhase s 2 :=
    xiEndpointPhase_ge_window hs0 hs1 le_rfl
  have hxi3 : xiEndpointPhase s 3 ≤ 3 := by
    have h := (xiEndpointPhase_bounds hs0 (by linarith) (by norm_num : (1:ℝ) ≤ 3)).2
    have h8 : Real.sqrt ((3:ℝ) ^ 2 - 1) ≤ 3 := by
      rw [show ((3:ℝ) ^ 2 - 1) = 8 by norm_num,
        show (3:ℝ) = Real.sqrt 9 from (by rw [show (9:ℝ) = 3 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)])]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have hu1 : (1 : ℝ) ≤ c * xiEndpointPhase s 2 := by nlinarith [hxi2, hc]
  have hgap : c * xiEndpointPhase s 2 + 4 * (n : ℝ) ≤ c * xiEndpointPhase s 3 := by
    have h := one_le_xiEndpointPhase_gap hs0 (by linarith)
    nlinarith [h, hn4, hc0]
  have hu2 : c * xiEndpointPhase s 3 ≤ 3 * c := by nlinarith [hxi3, hc0]
  have hu2pos : (0 : ℝ) < c * xiEndpointPhase s 3 := by
    have : (1 : ℝ) ≤ c * xiEndpointPhase s 2 := hu1
    have hn0 : (0 : ℝ) ≤ 4 * (n : ℝ) := by positivity
    linarith [hgap]
  -- the u-integral
  have hInt := integral_besselJ0_sq_ge hu1 n hgap
  have hlow : besselEnergyFloor / 54
      ≤ ∫ u in (c * xiEndpointPhase s 2)..(c * xiEndpointPhase s 3), besselJ0 u ^ 2 := by
    refine le_trans ?_ hInt
    rw [div_le_div_iff₀ (by norm_num) hu2pos]
    have hκ : 0 < besselEnergyFloor := besselEnergyFloor_pos
    nlinarith [hnlow, hu2, hκ, hc0]
  -- back to the x-integral
  rw [← integral_speed_besselJ0_sq (c := c) hs0] at hlow
  -- the pointwise density comparison
  have ha1 : (1 : ℝ) < 2 := by norm_num
  have hca : dunsterEndpointCrossing c ≤ 2 := by
    rw [dunsterEndpointCrossing]
    have h9 : 9 / (8 * c ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hc]
    linarith
  have hcaxi : 1 ≤ c * xiEndpointPhase s 2 := hu1
  have hBint : IntegrableOn (radialProlateBesselDensity s c) (Ioi (2:ℝ)) :=
    integrableOn_radialProlateBesselDensity hs0 (by linarith) hc0 ha1 hcaxi
  have hBii : IntervalIntegrable (radialProlateBesselDensity s c) MeasureTheory.volume 2 3 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact hBint.mono_set (fun t ht => ht.1)
  have hSint : IntervalIntegrable
      (fun x : ℝ => 1 / 8 * ((c * xiSpeed s x) * besselJ0 (c * xiEndpointPhase s x) ^ 2))
      MeasureTheory.volume 2 3 := by
    have hcont : ContinuousOn
        (fun x : ℝ => 1 / 8 * ((c * xiSpeed s x) * besselJ0 (c * xiEndpointPhase s x) ^ 2))
        (uIcc (2:ℝ) 3) := by
      rw [uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)]
      refine continuousOn_const.mul ((continuousOn_const.mul
        ((continuousOn_xiSpeed s).mono fun t ht => lt_of_lt_of_le (by norm_num) ht.1)).mul ?_)
      exact ((continuous_besselJ0.pow 2).comp_continuousOn
        (continuousOn_const.mul ((continuousOn_xiEndpointPhase' hs0).mono
          fun t ht => lt_of_lt_of_le (by norm_num) ht.1)))
    exact hcont.intervalIntegrable
  have hcmp : (∫ x in (2:ℝ)..3,
        1 / 8 * ((c * xiSpeed s x) * besselJ0 (c * xiEndpointPhase s x) ^ 2))
      ≤ ∫ x in (2:ℝ)..3, radialProlateBesselDensity s c x := by
    refine intervalIntegral.integral_mono_on (by norm_num) hSint hBii fun x hx => ?_
    exact besselDensity_ge_speed hs0 hs1 hc0 hx.1 hx.2
  have hscale : (∫ x in (2:ℝ)..3,
      1 / 8 * ((c * xiSpeed s x) * besselJ0 (c * xiEndpointPhase s x) ^ 2))
      = 1 / 8 * ∫ x in (2:ℝ)..3, (c * xiSpeed s x) * besselJ0 (c * xiEndpointPhase s x) ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  rw [hscale] at hcmp
  have hfin : besselEnergyFloor / 432
      ≤ 1 / 8 * ∫ x in (2:ℝ)..3, (c * xiSpeed s x) * besselJ0 (c * xiEndpointPhase s x) ^ 2 := by
    linarith [hlow]
  linarith [hcmp, hfin]

/-- **The exterior mass from below.**  For an endpoint-normalised radial mode the exterior mass is at
least a fixed multiple of `1/c`, minus the `O(1/c²)` transfer error.  This is the companion of
`integral_Ioi_one_radialProlate_sq_le` and matches its order. -/
theorem integral_Ioi_radialProlate_sq_ge {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 8 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    besselEnergyFloor / 432 / c - 2 * radialProlateDensityTransferConstant / c ^ 2
      ≤ ∫ x in Ioi (2 : ℝ), R x ^ 2 := by
  have hc0 : (0 : ℝ) < c := by linarith
  have ha1 : (1 : ℝ) < 2 := by norm_num
  have hxi2 : (61 : ℝ) / 50 ≤ xiEndpointPhase s 2 := xiEndpointPhase_ge_window hs0 hs1 le_rfl
  have hcaxi : (1 : ℝ) ≤ c * xiEndpointPhase s 2 := by nlinarith [hxi2, hc]
  have hca : dunsterEndpointCrossing c ≤ 2 := by
    rw [dunsterEndpointCrossing]
    have h9 : 9 / (8 * c ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [hc]
    linarith
  have hBint : IntegrableOn (radialProlateBesselDensity s c) (Ioi (2:ℝ)) :=
    integrableOn_radialProlateBesselDensity hs0 hs1 hc0 ha1 hcaxi
  have hDint : IntegrableOn (radialProlateDensity c R) (Ioi (2:ℝ)) :=
    integrableOn_Ioi_radialProlateDensity hs0 hs1 (by linarith) ha1 hca hR1 hR hDR hode
  have hdiff : (∫ x in Ioi (2:ℝ),
      |radialProlateDensity c R x - radialProlateBesselDensity s c x|)
      ≤ 2 * radialProlateDensityTransferConstant / c :=
    integral_Ioi_abs_radialProlateDensity_sub_besselDensity_le hs0 hs1 (by linarith) hca
      hR1 hR hDR hode
  -- the window mass is retained by the full ray
  have hBnn : ∀ x, 0 ≤ radialProlateBesselDensity s c x := fun x => by
    rw [radialProlateBesselDensity]; positivity
  have hwindow : (∫ x in (2:ℝ)..3, radialProlateBesselDensity s c x)
      ≤ ∫ x in Ioi (2:ℝ), radialProlateBesselDensity s c x := by
    rw [intervalIntegral.integral_of_le (by norm_num : (2:ℝ) ≤ 3)]
    refine setIntegral_mono_set hBint ?_ ?_
    · filter_upwards with x using hBnn x
    · exact ((show Ioc (2:ℝ) 3 ≤ Ioi (2:ℝ) from fun t ht => ht.1)).eventuallyLE
  have hwin := integral_window_besselDensity_ge (s := s) (c := c) hs0 hs1 hc
  -- the exact density from below
  have habsint : IntegrableOn
      (fun x => |radialProlateDensity c R x - radialProlateBesselDensity s c x|)
      (Ioi (2:ℝ)) := (hDint.sub hBint).abs
  have hsplit : (∫ x in Ioi (2:ℝ), radialProlateBesselDensity s c x)
      ≤ (∫ x in Ioi (2:ℝ), radialProlateDensity c R x)
        + ∫ x in Ioi (2:ℝ), |radialProlateDensity c R x - radialProlateBesselDensity s c x| := by
    have hle : ∀ᵐ x ∂(volume.restrict (Ioi (2:ℝ))), radialProlateBesselDensity s c x
        ≤ radialProlateDensity c R x
          + |radialProlateDensity c R x - radialProlateBesselDensity s c x| := by
      filter_upwards with x
      have := neg_abs_le (radialProlateDensity c R x - radialProlateBesselDensity s c x)
      linarith
    have hmono : (∫ x in Ioi (2:ℝ), radialProlateBesselDensity s c x)
        ≤ ∫ x in Ioi (2:ℝ), (radialProlateDensity c R x
            + |radialProlateDensity c R x - radialProlateBesselDensity s c x|) :=
      integral_mono_ae hBint (hDint.add habsint) hle
    rwa [integral_add hDint habsint] at hmono
  -- rescale
  have hscale : (∫ x in Ioi (2:ℝ), radialProlateDensity c R x)
      = c * ∫ x in Ioi (2:ℝ), R x ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by rw [radialProlateDensity]
  rw [hscale] at hsplit
  have hkey : besselEnergyFloor / 432 - 2 * radialProlateDensityTransferConstant / c
      ≤ c * ∫ x in Ioi (2:ℝ), R x ^ 2 := by
    linarith [hwin, hwindow, hsplit, hdiff]
  have hfin : (besselEnergyFloor / 432 - 2 * radialProlateDensityTransferConstant / c) / c
      ≤ ∫ x in Ioi (2:ℝ), R x ^ 2 := by
    rw [div_le_iff₀ hc0]
    linarith [hkey]
  have heq : (besselEnergyFloor / 432 - 2 * radialProlateDensityTransferConstant / c) / c
      = besselEnergyFloor / 432 / c - 2 * radialProlateDensityTransferConstant / c ^ 2 := by
    field_simp
  linarith [hfin, heq.le, heq.ge]

end

end GaloisForLFunctions.RHTower

end
