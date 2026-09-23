import GaloisForLFunctions.RHTower.ProlateDunsterEndpointVolterra

/-!
# Exact endpoint flux and a zero-free exterior collar for radial prolate modes

For a radial prolate solution

```text
((x^(2 : ℕ) - 1) R')' = c^(2 : ℕ) (s - x^(2 : ℕ)) R,
```

the singular endpoint sets the flux to zero without an extra boundary condition.  Integrating from
`1` gives an exact flux representation.  In the forbidden-endpoint regime `0 <= s <= 1`, a
nonnegative endpoint-normalized solution is decreasing.  A quantitative integration of the same
identity then proves that the solution has no zero in an explicit `O(c^-2)` collar.  This is the
endpoint continuation input for the pole-uniform Dunster comparison.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral

/-- Exterior Sturm--Liouville flux for a radial prolate profile. -/
def radialProlateFlux (DR : ℝ → ℝ) (x : ℝ) : ℝ := (x ^ (2 : ℕ) - 1) * DR x

@[simp]
theorem radialProlateFlux_one (DR : ℝ → ℝ) : radialProlateFlux DR 1 = 0 := by
  simp [radialProlateFlux]

/-- The radial equation is exactly the derivative law for the exterior flux. -/
theorem hasDerivAt_radialProlateFlux {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hDR : HasDerivAt DR (DDR x) x)
    (hode : (x ^ (2 : ℕ) - 1) * DDR x + 2 * x * DR x
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * R x = 0) :
    HasDerivAt (radialProlateFlux DR) (c ^ (2 : ℕ) * (s - x ^ (2 : ℕ)) * R x) x := by
  have hw : HasDerivAt (fun t : ℝ => t ^ (2 : ℕ) - 1) (2 * x) x := by
    simpa [pow_two, mul_comm] using ((hasDerivAt_id x).pow 2).sub_const 1
  have hflux := hw.mul hDR
  rw [show radialProlateFlux DR = fun t : ℝ => (t ^ (2 : ℕ) - 1) * DR t by rfl]
  refine hflux.congr_deriv ?_
  nlinarith [hode]

/-- Exact endpoint flux representation.  The endpoint term vanishes algebraically. -/
theorem radialProlateFlux_eq_integral {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (_hx : 1 ≤ x)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    radialProlateFlux DR x = ∫ t in 1..x, c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * R t := by
  have hderiv : ∀ t ∈ uIcc (1 : ℝ) x,
      HasDerivAt (radialProlateFlux DR) (c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * R t) t :=
    fun t _ => hasDerivAt_radialProlateFlux (hDR t) (hode t)
  have hint : IntervalIntegrable (fun t : ℝ => c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * R t) volume 1 x := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.mul (continuous_const.sub (continuous_id.pow 2))).mul
      (continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa using hFTC.symm

/-- A nonnegative radial profile with `s ≤ 1` has nonpositive exterior flux. -/
theorem radialProlateFlux_nonpos_of_nonnegative {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs : s ≤ 1) (hx : 1 ≤ x)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hpos : ∀ t ∈ Icc (1 : ℝ) x, 0 ≤ R t) :
    radialProlateFlux DR x ≤ 0 := by
  rw [radialProlateFlux_eq_integral hx hR hDR hode]
  have hnonneg : 0 ≤ ∫ t in 1..x, -(c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * R t) := by
    refine intervalIntegral.integral_nonneg hx fun t ht => ?_
    have hcoef : s - t ^ (2 : ℕ) ≤ 0 := by nlinarith [ht.1]
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) hcoef) (hpos t ht))
  rw [intervalIntegral.integral_neg] at hnonneg
  linarith

/-- While an `s ≤ 1` profile remains nonnegative, its derivative is nonpositive outside the
singular endpoint. -/
theorem radialProlate_deriv_nonpos_of_nonnegative {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs : s ≤ 1) (hx : 1 < x)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hpos : ∀ t ∈ Icc (1 : ℝ) x, 0 ≤ R t) :
    DR x ≤ 0 := by
  have hflux := radialProlateFlux_nonpos_of_nonnegative hs hx.le hR hDR hode hpos
  rw [radialProlateFlux] at hflux
  have hweight : 0 < x ^ (2 : ℕ) - 1 := by nlinarith
  nlinarith

/-- Nonnegative radial profiles with `s ≤ 1` are antitone on every exterior interval. -/
theorem radialProlate_antitoneOn_of_nonnegative {s c B : ℝ} {R DR DDR : ℝ → ℝ}
    (hs : s ≤ 1) (_hB : 1 ≤ B)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hpos : ∀ t ∈ Icc (1 : ℝ) B, 0 ≤ R t) :
    AntitoneOn R (Icc (1 : ℝ) B) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (continuous_iff_continuousAt.mpr (fun t => (hR t).continuousAt)).continuousOn
    ((show DifferentiableOn ℝ R (Icc (1 : ℝ) B) from
      (show Differentiable ℝ R from fun t => (hR t).differentiableAt).differentiableOn).mono
        interior_subset)
    fun x hx => ?_
  rw [interior_Icc] at hx
  have hposx : ∀ t ∈ Icc (1 : ℝ) x, 0 ≤ R t := fun t ht =>
    hpos t ⟨ht.1, le_trans ht.2 hx.2.le⟩
  rw [(hR x).deriv]
  exact radialProlate_deriv_nonpos_of_nonnegative hs hx.1 hR hDR hode hposx

/-- Quantitative derivative bound in the endpoint collar.  The constant `3/5` is uniform in
`0 <= s <= 1`. -/
theorem radialProlate_deriv_lower_bound_endpoint_collar {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx1 : 1 < x) (hx2 : x ≤ 11 / 10)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hpos : ∀ t ∈ Icc (1 : ℝ) x, 0 ≤ R t) :
    -(3 / 5 : ℝ) * c ^ (2 : ℕ) ≤ DR x := by
  have hanti := radialProlate_antitoneOn_of_nonnegative hs1 hx1.le hR hDR hode hpos
  have hflux := radialProlateFlux_eq_integral hx1.le hR hDR hode
  have hint : IntervalIntegrable (fun t : ℝ => c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * R t) volume 1 x := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.mul (continuous_const.sub (continuous_id.pow 2))).mul
      (continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt)
  have hconst : IntervalIntegrable (fun _t : ℝ => -(c ^ (2 : ℕ) * x ^ (2 : ℕ))) volume 1 x :=
    intervalIntegrable_const
  have hintegral : (∫ _t in 1..x, -(c ^ (2 : ℕ) * x ^ (2 : ℕ)))
      ≤ ∫ t in 1..x, c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * R t := by
    refine intervalIntegral.integral_mono_on hx1.le hconst hint fun t ht => ?_
    have hRt_le : R t ≤ 1 := by
      simpa only [hR1] using hanti ⟨le_rfl, hx1.le⟩ ht ht.1
    have hcoef : s - t ^ (2 : ℕ) ≤ 0 := by nlinarith [ht.1]
    have hmul : s - t ^ (2 : ℕ) ≤ (s - t ^ (2 : ℕ)) * R t := by
      simpa only [mul_one] using mul_le_mul_of_nonpos_left hRt_le hcoef
    have htsq : t ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by nlinarith [ht.1, ht.2]
    have hc2 : 0 ≤ c ^ (2 : ℕ) := sq_nonneg c
    calc
      -(c ^ (2 : ℕ) * x ^ (2 : ℕ)) ≤ -(c ^ (2 : ℕ) * t ^ (2 : ℕ)) := by nlinarith
      _ ≤ c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) := by nlinarith
      _ ≤ c ^ (2 : ℕ) * ((s - t ^ (2 : ℕ)) * R t) := mul_le_mul_of_nonneg_left hmul hc2
      _ = c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * R t := by ring
  rw [intervalIntegral.integral_const, smul_eq_mul] at hintegral
  rw [radialProlateFlux] at hflux
  have hdrop : -(c ^ (2 : ℕ) * x ^ (2 : ℕ)) * (x - 1) ≤ (x ^ (2 : ℕ) - 1) * DR x := by
    linarith [hintegral]
  have hfactor : x ^ (2 : ℕ) - 1 = (x - 1) * (x + 1) := by ring
  rw [hfactor] at hdrop
  have hxsub : 0 < x - 1 := by linarith
  have hcancel : -(c ^ (2 : ℕ) * x ^ (2 : ℕ)) ≤ (x + 1) * DR x := by
    apply le_of_mul_le_mul_left (a := x - 1) _ hxsub
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hdrop
  have hratio : x ^ (2 : ℕ) ≤ (3 / 5 : ℝ) * (x + 1) := by nlinarith
  have hxplus : 0 < x + 1 := by linarith
  have hratio_c := mul_le_mul_of_nonneg_left hratio (sq_nonneg c)
  nlinarith

/-- Integrating the collar derivative bound gives an explicit lower bound for every nonnegative
endpoint-normalized solution. -/
theorem radialProlate_value_lower_bound_endpoint_collar {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hx1 : 1 ≤ x) (hx2 : x ≤ 11 / 10)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hpos : ∀ t ∈ Icc (1 : ℝ) x, 0 ≤ R t) :
    1 - (3 / 5 : ℝ) * c ^ (2 : ℕ) * (x - 1) ≤ R x := by
  have hderiv : ∀ t ∈ uIcc (1 : ℝ) x, HasDerivAt R (DR t) t := fun t _ => hR t
  have hint : IntervalIntegrable DR volume 1 x := by
    apply Continuous.intervalIntegrable
    exact continuous_iff_continuousAt.mpr fun t => (hDR t).continuousAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hlower : ∀ t ∈ Icc (1 : ℝ) x, -(3 / 5 : ℝ) * c ^ (2 : ℕ) ≤ DR t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht1
    · have hone := hode 1
      rw [hR1] at hone
      norm_num only [one_pow, sub_self, zero_mul, zero_add, mul_one] at hone
      nlinarith [sq_nonneg c]
    · exact radialProlate_deriv_lower_bound_endpoint_collar hs0 hs1 ht1
        (le_trans ht.2 hx2) hR1 hR hDR hode
        (fun u hu => hpos u ⟨hu.1, le_trans hu.2 ht.2⟩)
  have hconst : IntervalIntegrable (fun _t : ℝ => -(3 / 5 : ℝ) * c ^ (2 : ℕ)) volume 1 x :=
    intervalIntegrable_const
  have hintegral : (∫ _t in 1..x, -(3 / 5 : ℝ) * c ^ (2 : ℕ)) ≤ ∫ t in 1..x, DR t :=
    intervalIntegral.integral_mono_on hx1 hconst hint hlower
  rw [intervalIntegral.integral_const, smul_eq_mul] at hintegral
  rw [hR1] at hFTC
  linarith

/-- **Explicit zero-free collar.**  If `3 c^(2 : ℕ) (B-1) < 5`, an endpoint-normalized `s ≤ 1`
radial solution is strictly positive on `[1,B]`. -/
theorem radialProlate_pos_endpoint_collar {s c B : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (_hB1 : 1 ≤ B) (hB2 : B ≤ 11 / 10)
    (hshort : 3 * c ^ (2 : ℕ) * (B - 1) < 5)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ∀ x ∈ Icc (1 : ℝ) B, 0 < R x := by
  intro x hx
  by_contra hnot
  push Not at hnot
  have hcont : Continuous R := continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt
  have hzero_exists : ∃ z ∈ Icc (1 : ℝ) x, R z = 0 := by
    have hzero_mem : (0 : ℝ) ∈ uIcc (R 1) (R x) := by
      rw [hR1, uIcc_of_ge (by linarith : R x ≤ (1 : ℝ))]
      exact ⟨hnot, zero_le_one⟩
    obtain ⟨z, hz, hzeq⟩ :=
      (intermediate_value_uIcc hcont.continuousOn) hzero_mem
    refine ⟨z, ?_, hzeq⟩
    simpa only [uIcc_of_le hx.1] using hz
  let H : Set ℝ := Icc (1 : ℝ) B ∩ {t : ℝ | R t = 0}
  have hHclosed : IsClosed H := isClosed_Icc.inter (isClosed_eq hcont continuous_const)
  have hHcompact : IsCompact H := isCompact_Icc.inter_right (isClosed_eq hcont continuous_const)
  have hHne : H.Nonempty := by
    obtain ⟨z, hz, hzeq⟩ := hzero_exists
    exact ⟨z, ⟨⟨hz.1, le_trans hz.2 hx.2⟩, hzeq⟩⟩
  obtain ⟨y, hyH, hyleast⟩ := hHcompact.exists_isLeast hHne
  have hyIcc : y ∈ Icc (1 : ℝ) B := hyH.1
  have hyzero : R y = 0 := hyH.2
  have hpos : ∀ t ∈ Icc (1 : ℝ) y, 0 ≤ R t := by
    intro t ht
    by_contra htneg
    push Not at htneg
    have hzero_mem : (0 : ℝ) ∈ uIcc (R 1) (R t) := by
      rw [hR1, uIcc_of_ge (by linarith : R t ≤ (1 : ℝ))]
      exact ⟨htneg.le, zero_le_one⟩
    obtain ⟨z, hz, hzeq⟩ :=
      (intermediate_value_uIcc hcont.continuousOn) hzero_mem
    have hzIcc : z ∈ Icc (1 : ℝ) t := by
      simpa only [uIcc_of_le ht.1] using hz
    have hzH : z ∈ H := ⟨⟨hzIcc.1, le_trans (le_trans hzIcc.2 ht.2) hyIcc.2⟩, hzeq⟩
    have hyz := hyleast hzH
    have hzt : z ≤ t := hzIcc.2
    have hty : t ≤ y := ht.2
    have hall : z = y := le_antisymm (le_trans hzt hty) hyz
    subst z
    have : t = y := le_antisymm hty hzt
    subst t
    linarith [hyzero]
  have hlower := radialProlate_value_lower_bound_endpoint_collar hs0 hs1 hyIcc.1
    (le_trans hyIcc.2 hB2) hR1 hR hDR hode hpos
  have hyshort : 3 * c ^ (2 : ℕ) * (y - 1) < 5 := by
    have hc2 : 0 ≤ 3 * c ^ (2 : ℕ) := by positivity
    have : y - 1 ≤ B - 1 := by linarith [hyIcc.2]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left this hc2) hshort
  rw [hyzero] at hlower
  nlinarith

/-- A short inverse-square collar used only for exterior-mass extraction. -/
def radialExteriorCollarEnd (c : ℝ) : ℝ := 1 + 1 / (2 * c ^ (2 : ℕ))

/-- Endpoint-normalized solutions with `s ≥ 1` are also positive on the inverse-square exterior
collar.  If the potential remains positive they are increasing.  Otherwise a maximum-principle
estimate bounds their entire relative variation on the collar by less than one quarter. -/
theorem radialProlate_pos_endpoint_collar_of_one_le
    {s c : ℝ} {R DR DDR : ℝ → ℝ}
    (hs1 : 1 ≤ s) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    ∀ x ∈ Icc (1 : ℝ) (radialExteriorCollarEnd c), 1 / 2 ≤ R x := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hB1 : 1 ≤ radialExteriorCollarEnd c := by
    rw [radialExteriorCollarEnd]
    exact le_add_of_nonneg_right (div_nonneg zero_le_one (by positivity))
  have hB2 : radialExteriorCollarEnd c ≤ 11 / 10 := by
    rw [radialExteriorCollarEnd]
    have hcSq : (5 : ℝ) ^ (2 : ℕ) ≤ c ^ (2 : ℕ) :=
      (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 5) hc0.le).2 hc
    have hfrac : 1 / (2 * c ^ (2 : ℕ)) ≤ (1 : ℝ) / 10 := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * c ^ (2 : ℕ)) (by norm_num : (0 : ℝ) < 10)]
      nlinarith
    nlinarith
  intro x hx
  by_contra hnot
  push Not at hnot
  have hcont : Continuous R := continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt
  have hzeroExists : ∃ z ∈ Icc (1 : ℝ) x, R z = 1 / 2 := by
    have hzeroMem : (1 / 2 : ℝ) ∈ uIcc (R 1) (R x) := by
      rw [hR1, uIcc_of_ge (by linarith : R x ≤ (1 : ℝ))]
      exact ⟨hnot.le, by norm_num⟩
    obtain ⟨z, hz, hzeq⟩ :=
      (intermediate_value_uIcc hcont.continuousOn) hzeroMem
    refine ⟨z, ?_, hzeq⟩
    simpa only [uIcc_of_le hx.1] using hz
  let H : Set ℝ := Icc (1 : ℝ) (radialExteriorCollarEnd c) ∩ {t : ℝ | R t = 1 / 2}
  have hHcompact : IsCompact H :=
    isCompact_Icc.inter_right (isClosed_eq hcont continuous_const)
  have hHne : H.Nonempty := by
    obtain ⟨z, hz, hzeq⟩ := hzeroExists
    exact ⟨z, ⟨⟨hz.1, hz.2.trans hx.2⟩, hzeq⟩⟩
  obtain ⟨y, hyH, hyleast⟩ := hHcompact.exists_isLeast hHne
  have hyIcc : y ∈ Icc (1 : ℝ) (radialExteriorCollarEnd c) := hyH.1
  have hyzero : R y = 1 / 2 := hyH.2
  have hpos : ∀ t ∈ Icc (1 : ℝ) y, 1 / 2 ≤ R t := by
    intro t ht
    by_contra htneg
    push Not at htneg
    have hzeroMem : (1 / 2 : ℝ) ∈ uIcc (R 1) (R t) := by
      rw [hR1, uIcc_of_ge (by linarith : R t ≤ (1 : ℝ))]
      exact ⟨htneg.le, by norm_num⟩
    obtain ⟨z, hz, hzeq⟩ :=
      (intermediate_value_uIcc hcont.continuousOn) hzeroMem
    have hzIcc : z ∈ Icc (1 : ℝ) t := by
      simpa only [uIcc_of_le ht.1] using hz
    have hzH : z ∈ H :=
      ⟨⟨hzIcc.1, (hzIcc.2.trans ht.2).trans hyIcc.2⟩, hzeq⟩
    have hyz := hyleast hzH
    have : z = y := le_antisymm (hzIcc.2.trans ht.2) hyz
    subst z
    have : t = y := le_antisymm ht.2 hzIcc.2
    subst t
    linarith [hyzero]
  have hsy : s < y ^ (2 : ℕ) := by
    by_contra hnotSy
    have hys : y ^ (2 : ℕ) ≤ s := le_of_not_gt hnotSy
    have hderiv0 : ∀ t ∈ Icc (1 : ℝ) y, 0 ≤ DR t := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with rfl | ht1
      · have hone := hode 1
        rw [hR1] at hone
        norm_num only [one_pow, sub_self, zero_mul, zero_add, mul_one] at hone
        nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sq_nonneg c)]
      · have hflux := radialProlateFlux_eq_integral ht1.le hR hDR hode
        have hint0 : 0 ≤ ∫ u in 1..t, c ^ (2 : ℕ) * (s - u ^ (2 : ℕ)) * R u := by
          refine intervalIntegral.integral_nonneg ht1.le fun u hu => ?_
          have hu0 : 0 ≤ u := by linarith [hu.1]
          have huy : u ≤ y := hu.2.trans ht.2
          have husq : u ^ (2 : ℕ) ≤ y ^ (2 : ℕ) :=
            (sq_le_sq₀ hu0 (by linarith [hyIcc.1])).2 huy
          exact mul_nonneg
            (mul_nonneg (sq_nonneg c) (sub_nonneg.2 (husq.trans hys)))
            (by linarith [hpos u ⟨hu.1, huy⟩])
        rw [radialProlateFlux] at hflux
        have hweight : 0 < t ^ (2 : ℕ) - 1 := by nlinarith
        nlinarith
    have hderivInt : 0 ≤ ∫ t in 1..y, DR t :=
      intervalIntegral.integral_nonneg hyIcc.1 hderiv0
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := R) (f' := DR) (fun t _ => hR t)
      ((continuous_iff_continuousAt.mpr fun t => (hDR t).continuousAt).intervalIntegrable 1 y)
    rw [hFTC, hR1, hyzero] at hderivInt
    linarith
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hyIcc.1) hcont.abs.continuousOn
  let M : ℝ := |R m|
  have hM0 : 0 ≤ M := abs_nonneg _
  have hbound : ∀ t ∈ Icc (1 : ℝ) y, |R t| ≤ M := by
    intro t ht
    exact isMaxOn_iff.mp hmax t ht
  have hM1 : 1 ≤ M := by
    have := hbound 1 ⟨le_rfl, hyIcc.1⟩
    rw [hR1, abs_one] at this
    exact this
  let B : ℝ := radialExteriorCollarEnd c
  let K : ℝ := c ^ (2 : ℕ) * (B ^ (2 : ℕ) - 1)
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB1
  have hy0 : 0 ≤ y := le_trans (by norm_num) hyIcc.1
  have hySqB : y ^ (2 : ℕ) ≤ B ^ (2 : ℕ) :=
    (sq_le_sq₀ hy0 hB0).2 hyIcc.2
  have hsB : s ≤ B ^ (2 : ℕ) := (le_of_lt hsy).trans hySqB
  have hK0 : 0 ≤ K := by
    dsimp only [K, B]
    have : 1 ≤ radialExteriorCollarEnd c ^ (2 : ℕ) :=
      by nlinarith [sq_nonneg (radialExteriorCollarEnd c - 1)]
    positivity
  have hcoeff : ∀ t ∈ Icc (1 : ℝ) y, |c ^ (2 : ℕ) * (s - t ^ (2 : ℕ))| ≤ K := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have htB : t ≤ B := ht.2.trans hyIcc.2
    have htSqB : t ^ (2 : ℕ) ≤ B ^ (2 : ℕ) := (sq_le_sq₀ ht0 hB0).2 htB
    have htSq1 : 1 ≤ t ^ (2 : ℕ) := by nlinarith [ht.1]
    have habs : |s - t ^ (2 : ℕ)| ≤ B ^ (2 : ℕ) - 1 := (abs_le).2 ⟨by linarith, by linarith⟩
    rw [abs_mul, abs_of_nonneg (sq_nonneg c)]
    exact mul_le_mul_of_nonneg_left habs (sq_nonneg c)
  have hderivBound : ∀ t ∈ Icc (1 : ℝ) y, |DR t| ≤ K * M := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht1
    · have hone := hode 1
      rw [hR1] at hone
      norm_num only [one_pow, sub_self, zero_mul, zero_add, mul_one] at hone
      have hsDiff : s - 1 ≤ B ^ (2 : ℕ) - 1 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hsDiff (sq_nonneg c)
      have hDR0 : 0 ≤ DR 1 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sq_nonneg c)]
      rw [abs_of_nonneg hDR0]
      dsimp only [K]
      nlinarith [hM1]
    · have hflux := radialProlateFlux_eq_integral ht1.le hR hDR hode
      have hintegrand : ∀ u ∈ Icc (1 : ℝ) t,
          |c ^ (2 : ℕ) * (s - u ^ (2 : ℕ)) * R u| ≤ K * M := by
        intro u hu
        rw [abs_mul]
        exact mul_le_mul (hcoeff u ⟨hu.1, hu.2.trans ht.2⟩)
          (hbound u ⟨hu.1, hu.2.trans ht.2⟩) (abs_nonneg _) hK0
      have hintBound :
          |∫ u in 1..t, c ^ (2 : ℕ) * (s - u ^ (2 : ℕ)) * R u| ≤
            (t - 1) * (K * M) := by
        have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun u : ℝ => c ^ (2 : ℕ) * (s - u ^ (2 : ℕ)) * R u) (C := K * M)
          (fun u hu => hintegrand u (by
            rw [← uIcc_of_le ht1.le]
            exact uIoc_subset_uIcc hu))
        simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 ht1.le), mul_comm] using hnorm
      rw [radialProlateFlux] at hflux
      have hweight : 0 ≤ t ^ (2 : ℕ) - 1 := by nlinarith
      have hfluxBound : |(t ^ (2 : ℕ) - 1) * DR t| ≤ (t - 1) * (K * M) := by
        rw [hflux]
        exact hintBound
      rw [abs_mul, abs_of_nonneg hweight] at hfluxBound
      have hfactor : t ^ (2 : ℕ) - 1 = (t - 1) * (t + 1) := by ring
      rw [hfactor] at hfluxBound
      have hcancel : (t + 1) * |DR t| ≤ K * M := by
        have htSub : 0 < t - 1 := by linarith
        apply le_of_mul_le_mul_left (a := t - 1) _ htSub
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hfluxBound
      exact le_trans (by nlinarith [abs_nonneg (DR t)]) hcancel
  have hpointBound : ∀ t ∈ Icc (1 : ℝ) y,
      |R t - 1| ≤ (t - 1) * (K * M) := by
    intro t ht
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := R) (f' := DR) (fun u _ => hR u)
      ((continuous_iff_continuousAt.mpr fun u => (hDR u).continuousAt).intervalIntegrable 1 t)
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := DR) (C := K * M) (fun u hu => by
        simpa only [Real.norm_eq_abs] using hderivBound u (by
          have hu' : u ∈ Icc (1 : ℝ) t := by
            rw [← uIcc_of_le ht.1]
            exact uIoc_subset_uIcc hu
          exact ⟨hu'.1, hu'.2.trans ht.2⟩))
    rw [hFTC, hR1] at hnorm
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 ht.1), mul_comm] using hnorm
  have hBsq : B ^ (2 : ℕ) - 1 ≤ 21 / 100 := by
    have := (sq_le_sq₀ hB0 (by norm_num : (0 : ℝ) ≤ 11 / 10)).2 hB2
    nlinarith
  have hwidth : B - 1 = 1 / (2 * c ^ (2 : ℕ)) := by
    dsimp only [B, radialExteriorCollarEnd]
    ring
  have halpha : (B - 1) * K ≤ 1 / 4 := by
    have hposden : 0 < 2 * c ^ (2 : ℕ) := by positivity
    have hidentity : (B - 1) * K = (B ^ (2 : ℕ) - 1) / 2 := by
      dsimp only [K]
      rw [hwidth]
      field_simp [hc0.ne']
    rw [hidentity]
    nlinarith
  have hmIcc : m ∈ Icc (1 : ℝ) y := hm
  have hmWidth : m - 1 ≤ B - 1 := by linarith [hm.2, hyIcc.2]
  have hmScale : (m - 1) * (K * M) ≤ (1 / 4) * M := by
    have hKM0 : 0 ≤ K * M := mul_nonneg hK0 hM0
    have hfirst := mul_le_mul_of_nonneg_right hmWidth hKM0
    have hsecond := mul_le_mul_of_nonneg_right halpha hM0
    nlinarith
  have hmPoint := (hpointBound m hmIcc).trans hmScale
  have hRm0 : 0 ≤ R m := by linarith [hpos m hmIcc]
  have hMeq : M = R m := by dsimp only [M]; rw [abs_of_nonneg hRm0]
  have hMupper : M ≤ 4 / 3 := by
    rw [hMeq] at hmPoint ⊢
    nlinarith [le_abs_self (R m - 1)]
  have hyWidth : y - 1 ≤ B - 1 := by linarith [hyIcc.2]
  have hyScale : (y - 1) * (K * M) ≤ (1 / 4) * M := by
    have hKM0 : 0 ≤ K * M := mul_nonneg hK0 hM0
    have hfirst := mul_le_mul_of_nonneg_right hyWidth hKM0
    have hsecond := mul_le_mul_of_nonneg_right halpha hM0
    nlinarith
  have hyPoint := (hpointBound y ⟨hyIcc.1, le_rfl⟩).trans hyScale
  rw [hyzero] at hyPoint
  norm_num at hyPoint
  nlinarith

/-- Endpoint-normalized radial profiles stay above `13/40` throughout a fixed
inverse-square collar, uniformly for `0 ≤ s ≤ 1`. -/
theorem radialProlate_value_ge_thirteen_fortieth_to_crossing
    {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hx : x ∈ Icc (1 : ℝ) (radialExteriorCollarEnd c)) :
    13 / 40 ≤ R x := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hB1 : 1 ≤ radialExteriorCollarEnd c := by
    rw [radialExteriorCollarEnd]
    exact le_add_of_nonneg_right (div_nonneg zero_le_one (by positivity))
  have hB2 : radialExteriorCollarEnd c ≤ 11 / 10 := by
    rw [radialExteriorCollarEnd]
    have hcSq : (5 : ℝ) ^ (2 : ℕ) ≤ c ^ (2 : ℕ) :=
      (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 5) hc0.le).2 hc
    have hfrac : 1 / (2 * c ^ (2 : ℕ)) ≤ (1 : ℝ) / 10 := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * c ^ (2 : ℕ)) (by norm_num : (0 : ℝ) < 10)]
      nlinarith
    nlinarith
  have hshort : 3 * c ^ (2 : ℕ) * (radialExteriorCollarEnd c - 1) < 5 := by
    rw [radialExteriorCollarEnd]
    field_simp [hc0.ne']
    norm_num
  have hpos := radialProlate_pos_endpoint_collar hs0 hs1 hB1 hB2
    hshort hR1 hR hDR hode
  have hlower := radialProlate_value_lower_bound_endpoint_collar hs0 hs1 hx.1
    (hx.2.trans hB2) hR1 hR hDR hode
    (fun t ht => (hpos t ⟨ht.1, ht.2.trans hx.2⟩).le)
  have hxsub : x - 1 ≤ 1 / (2 * c ^ (2 : ℕ)) := by
    rw [radialExteriorCollarEnd] at hx
    linarith [hx.2]
  have hscaled := mul_le_mul_of_nonneg_left hxsub
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 5) (sq_nonneg c))
  have hconst : (3 / 5 : ℝ) * c ^ (2 : ℕ) * (1 / (2 * c ^ (2 : ℕ))) = 3 / 10 := by
    field_simp [hc0.ne']
    ring
  rw [hconst] at hscaled
  nlinarith

/-- The positive exterior collar carries an explicit polynomial amount of squared mass. -/
theorem one_div_thirty_two_c_sq_le_integral_sq_endpoint_collar
    {s c : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0) :
    1 / (32 * c ^ (2 : ℕ)) ≤
      ∫ x in (1 : ℝ)..radialExteriorCollarEnd c, R x ^ (2 : ℕ) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hB1 : 1 ≤ radialExteriorCollarEnd c := by
    rw [radialExteriorCollarEnd]
    exact le_add_of_nonneg_right (div_nonneg zero_le_one (by positivity))
  have hint : IntervalIntegrable (fun x : ℝ => R x ^ (2 : ℕ)) volume 1
      (radialExteriorCollarEnd c) :=
    ((continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt).pow 2).intervalIntegrable _ _
  have hpoint : ∀ x ∈ Icc (1 : ℝ) (radialExteriorCollarEnd c),
      (1 / 16 : ℝ) ≤ R x ^ (2 : ℕ) := by
    intro x hx
    have hRlower := radialProlate_value_ge_thirteen_fortieth_to_crossing
      hs0 hs1 hc hR1 hR hDR hode hx
    have hquarter : (1 / 4 : ℝ) ≤ R x := by linarith
    have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hquarter 2
    norm_num at hsquare ⊢
    exact hsquare
  have hmono := intervalIntegral.integral_mono_on hB1 intervalIntegrable_const hint hpoint
  have hleft : (∫ _x in (1 : ℝ)..radialExteriorCollarEnd c, (1 / 16 : ℝ)) =
      1 / (32 * c ^ (2 : ℕ)) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, radialExteriorCollarEnd]
    field_simp [hc0.ne']
    ring
  rw [hleft] at hmono
  exact hmono

/-- The positive endpoint collar is contained, up to its null left endpoint, in the exterior of
the aperture. -/
theorem integral_sq_endpoint_collar_le_integral_outside
    {c : ℝ} {R : ℝ → ℝ} (hc : 0 < c)
    (hint : IntegrableOn (fun x : ℝ => R x ^ (2 : ℕ)) (Icc (-1 : ℝ) 1)ᶜ) :
    (∫ x in (1 : ℝ)..radialExteriorCollarEnd c, R x ^ (2 : ℕ)) ≤
      ∫ x in (Icc (-1 : ℝ) 1)ᶜ, R x ^ (2 : ℕ) := by
  have hB1 : 1 ≤ radialExteriorCollarEnd c := by
    rw [radialExteriorCollarEnd]
    exact le_add_of_nonneg_right (div_nonneg zero_le_one (by positivity))
  rw [intervalIntegral.integral_of_le hB1]
  apply integral_mono_measure
    (Measure.restrict_mono (show Ioc (1 : ℝ) (radialExteriorCollarEnd c) ⊆
        (Icc (-1 : ℝ) 1)ᶜ by
      intro x hx
      simp only [mem_compl_iff, mem_Icc, not_and, not_le]
      intro _
      exact hx.1) le_rfl)
  · filter_upwards with x
    exact sq_nonneg (R x)
  · exact hint

/-- **Polynomial exterior-mass floor.**  Every endpoint-normalized radial solution with
`0 ≤ s ≤ 1` carries at least `1/(32c²)` mass outside the aperture. -/
theorem one_div_thirty_two_c_sq_le_integral_outside_sq_radialProlate
    {s c : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hint : IntegrableOn (fun x : ℝ => R x ^ (2 : ℕ)) (Icc (-1 : ℝ) 1)ᶜ) :
    1 / (32 * c ^ (2 : ℕ)) ≤ ∫ x in (Icc (-1 : ℝ) 1)ᶜ, R x ^ (2 : ℕ) := by
  exact (one_div_thirty_two_c_sq_le_integral_sq_endpoint_collar
    hs0 hs1 hc hR1 hR hDR hode).trans
      (integral_sq_endpoint_collar_le_integral_outside
        (lt_of_lt_of_le (by norm_num) hc) hint)

/-- **High-separation exterior-mass floor.**  When `s ≥ 1`, endpoint growth gives the stronger
collar bound `1/(8c²)`. -/
theorem one_div_eight_c_sq_le_integral_outside_sq_radialProlate_of_one_le
    {s c : ℝ} {R DR DDR : ℝ → ℝ}
    (hs1 : 1 ≤ s) (hc : 5 ≤ c)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hint : IntegrableOn (fun x : ℝ => R x ^ (2 : ℕ)) (Icc (-1 : ℝ) 1)ᶜ) :
    1 / (8 * c ^ (2 : ℕ)) ≤ ∫ x in (Icc (-1 : ℝ) 1)ᶜ, R x ^ (2 : ℕ) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hB1 : 1 ≤ radialExteriorCollarEnd c := by
    rw [radialExteriorCollarEnd]
    exact le_add_of_nonneg_right (div_nonneg zero_le_one (by positivity))
  have hRint : IntervalIntegrable (fun x : ℝ => R x ^ (2 : ℕ)) volume 1
      (radialExteriorCollarEnd c) :=
    ((continuous_iff_continuousAt.mpr fun x => (hR x).continuousAt).pow 2).intervalIntegrable _ _
  have hpos := radialProlate_pos_endpoint_collar_of_one_le hs1 hc hR1 hR hDR hode
  have hpoint : ∀ x ∈ Icc (1 : ℝ) (radialExteriorCollarEnd c),
      (1 / 4 : ℝ) ≤ R x ^ (2 : ℕ) := by
    intro x hx
    have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (hpos x hx) 2
    norm_num at hsquare ⊢
    exact hsquare
  have hmono := intervalIntegral.integral_mono_on hB1 intervalIntegrable_const hRint hpoint
  have hleft : (∫ _x in (1 : ℝ)..radialExteriorCollarEnd c, (1 / 4 : ℝ)) =
      1 / (8 * c ^ (2 : ℕ)) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, radialExteriorCollarEnd]
    field_simp [hc0.ne']
    ring
  rw [hleft] at hmono
  exact hmono.trans (integral_sq_endpoint_collar_le_integral_outside hc0 hint)

end GaloisForLFunctions.RHTower

end
