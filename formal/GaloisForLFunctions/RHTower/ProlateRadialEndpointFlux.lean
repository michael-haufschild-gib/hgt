import GaloisForLFunctions.RHTower.ProlateDunsterEndpointVolterra

/-!
# Exact endpoint flux and a zero-free exterior collar for radial prolate modes

For a radial prolate solution

```text
((x^2 - 1) R')' = c^2 (s - x^2) R,
```

the singular endpoint sets the flux to zero without an extra boundary condition.  Integrating from
`1` gives an exact flux representation.  In the low-separation regime `0 <= s <= 1/2`, a
nonnegative endpoint-normalized solution is decreasing.  A quantitative integration of the same
identity then proves that the solution has no zero in an explicit `O(c^-2)` collar.  This is the
endpoint continuation input for the pole-uniform Dunster comparison.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral

/-- Exterior Sturm--Liouville flux for a radial prolate profile. -/
def radialProlateFlux (DR : ℝ → ℝ) (x : ℝ) : ℝ := (x ^ 2 - 1) * DR x

@[simp]
theorem radialProlateFlux_one (DR : ℝ → ℝ) : radialProlateFlux DR 1 = 0 := by
  simp [radialProlateFlux]

/-- The radial equation is exactly the derivative law for the exterior flux. -/
theorem hasDerivAt_radialProlateFlux {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hDR : HasDerivAt DR (DDR x) x)
    (hode : (x ^ 2 - 1) * DDR x + 2 * x * DR x
      - (s * c ^ 2 - c ^ 2 * x ^ 2) * R x = 0) :
    HasDerivAt (radialProlateFlux DR) (c ^ 2 * (s - x ^ 2) * R x) x := by
  have hw : HasDerivAt (fun t : ℝ => t ^ 2 - 1) (2 * x) x := by
    simpa [pow_two, mul_comm] using ((hasDerivAt_id x).pow 2).sub_const 1
  have hflux := hw.mul hDR
  rw [show radialProlateFlux DR = fun t : ℝ => (t ^ 2 - 1) * DR t by rfl]
  refine hflux.congr_deriv ?_
  nlinarith [hode]

/-- Exact endpoint flux representation.  The endpoint term vanishes algebraically. -/
theorem radialProlateFlux_eq_integral {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (_hx : 1 ≤ x)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
    radialProlateFlux DR x = ∫ t in 1..x, c ^ 2 * (s - t ^ 2) * R t := by
  have hderiv : ∀ t ∈ uIcc (1 : ℝ) x,
      HasDerivAt (radialProlateFlux DR) (c ^ 2 * (s - t ^ 2) * R t) t :=
    fun t _ => hasDerivAt_radialProlateFlux (hDR t) (hode t)
  have hint : IntervalIntegrable (fun t : ℝ => c ^ 2 * (s - t ^ 2) * R t) volume 1 x := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.mul (continuous_const.sub (continuous_id.pow 2))).mul
      (continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa using hFTC.symm

/-- A nonnegative low-separation radial profile has nonpositive exterior flux. -/
theorem radialProlateFlux_nonpos_of_nonnegative {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs : s ≤ 1 / 2) (hx : 1 ≤ x)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hpos : ∀ t ∈ Icc (1 : ℝ) x, 0 ≤ R t) :
    radialProlateFlux DR x ≤ 0 := by
  rw [radialProlateFlux_eq_integral hx hR hDR hode]
  have hnonneg : 0 ≤ ∫ t in 1..x, -(c ^ 2 * (s - t ^ 2) * R t) := by
    refine intervalIntegral.integral_nonneg hx fun t ht => ?_
    have hcoef : s - t ^ 2 ≤ 0 := by nlinarith [ht.1]
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) hcoef) (hpos t ht))
  rw [intervalIntegral.integral_neg] at hnonneg
  linarith

/-- While a low-separation profile remains nonnegative, its derivative is nonpositive outside the
singular endpoint. -/
theorem radialProlate_deriv_nonpos_of_nonnegative {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs : s ≤ 1 / 2) (hx : 1 < x)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hpos : ∀ t ∈ Icc (1 : ℝ) x, 0 ≤ R t) :
    DR x ≤ 0 := by
  have hflux := radialProlateFlux_nonpos_of_nonnegative hs hx.le hR hDR hode hpos
  rw [radialProlateFlux] at hflux
  have hweight : 0 < x ^ 2 - 1 := by nlinarith
  nlinarith

/-- Nonnegative low-separation radial profiles are antitone on every exterior interval. -/
theorem radialProlate_antitoneOn_of_nonnegative {s c B : ℝ} {R DR DDR : ℝ → ℝ}
    (hs : s ≤ 1 / 2) (_hB : 1 ≤ B)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
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
`0 <= s <= 1/2`. -/
theorem radialProlate_deriv_lower_bound_endpoint_collar {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx1 : 1 < x) (hx2 : x ≤ 11 / 10)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hpos : ∀ t ∈ Icc (1 : ℝ) x, 0 ≤ R t) :
    -(3 / 5 : ℝ) * c ^ 2 ≤ DR x := by
  have hanti := radialProlate_antitoneOn_of_nonnegative hs1 hx1.le hR hDR hode hpos
  have hflux := radialProlateFlux_eq_integral hx1.le hR hDR hode
  have hint : IntervalIntegrable (fun t : ℝ => c ^ 2 * (s - t ^ 2) * R t) volume 1 x := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.mul (continuous_const.sub (continuous_id.pow 2))).mul
      (continuous_iff_continuousAt.mpr fun t => (hR t).continuousAt)
  have hconst : IntervalIntegrable (fun _t : ℝ => -(c ^ 2 * x ^ 2)) volume 1 x :=
    intervalIntegrable_const
  have hintegral : (∫ _t in 1..x, -(c ^ 2 * x ^ 2))
      ≤ ∫ t in 1..x, c ^ 2 * (s - t ^ 2) * R t := by
    refine intervalIntegral.integral_mono_on hx1.le hconst hint fun t ht => ?_
    have hRt_le : R t ≤ 1 := by
      simpa only [hR1] using hanti ⟨le_rfl, hx1.le⟩ ht ht.1
    have hcoef : s - t ^ 2 ≤ 0 := by nlinarith [ht.1]
    have hmul : s - t ^ 2 ≤ (s - t ^ 2) * R t := by
      simpa only [mul_one] using mul_le_mul_of_nonpos_left hRt_le hcoef
    have htsq : t ^ 2 ≤ x ^ 2 := by nlinarith [ht.1, ht.2]
    have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
    calc
      -(c ^ 2 * x ^ 2) ≤ -(c ^ 2 * t ^ 2) := by nlinarith
      _ ≤ c ^ 2 * (s - t ^ 2) := by nlinarith
      _ ≤ c ^ 2 * ((s - t ^ 2) * R t) := mul_le_mul_of_nonneg_left hmul hc2
      _ = c ^ 2 * (s - t ^ 2) * R t := by ring
  rw [intervalIntegral.integral_const, smul_eq_mul] at hintegral
  rw [radialProlateFlux] at hflux
  have hdrop : -(c ^ 2 * x ^ 2) * (x - 1) ≤ (x ^ 2 - 1) * DR x := by
    linarith [hintegral]
  have hfactor : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
  rw [hfactor] at hdrop
  have hxsub : 0 < x - 1 := by linarith
  have hcancel : -(c ^ 2 * x ^ 2) ≤ (x + 1) * DR x := by
    apply le_of_mul_le_mul_left (a := x - 1) _ hxsub
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hdrop
  have hratio : x ^ 2 ≤ (3 / 5 : ℝ) * (x + 1) := by nlinarith
  have hxplus : 0 < x + 1 := by linarith
  have hratio_c := mul_le_mul_of_nonneg_left hratio (sq_nonneg c)
  nlinarith

/-- Integrating the collar derivative bound gives an explicit lower bound for every nonnegative
endpoint-normalized solution. -/
theorem radialProlate_value_lower_bound_endpoint_collar {s c x : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx1 : 1 ≤ x) (hx2 : x ≤ 11 / 10)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0)
    (hpos : ∀ t ∈ Icc (1 : ℝ) x, 0 ≤ R t) :
    1 - (3 / 5 : ℝ) * c ^ 2 * (x - 1) ≤ R x := by
  have hderiv : ∀ t ∈ uIcc (1 : ℝ) x, HasDerivAt R (DR t) t := fun t _ => hR t
  have hint : IntervalIntegrable DR volume 1 x := by
    apply Continuous.intervalIntegrable
    exact continuous_iff_continuousAt.mpr fun t => (hDR t).continuousAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hlower : ∀ t ∈ Icc (1 : ℝ) x, -(3 / 5 : ℝ) * c ^ 2 ≤ DR t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht1
    · have hone := hode 1
      rw [hR1] at hone
      norm_num only [one_pow, sub_self, zero_mul, zero_add, mul_one] at hone
      nlinarith [sq_nonneg c]
    · exact radialProlate_deriv_lower_bound_endpoint_collar hs0 hs1 ht1
        (le_trans ht.2 hx2) hR1 hR hDR hode
        (fun u hu => hpos u ⟨hu.1, le_trans hu.2 ht.2⟩)
  have hconst : IntervalIntegrable (fun _t : ℝ => -(3 / 5 : ℝ) * c ^ 2) volume 1 x :=
    intervalIntegrable_const
  have hintegral : (∫ _t in 1..x, -(3 / 5 : ℝ) * c ^ 2) ≤ ∫ t in 1..x, DR t :=
    intervalIntegral.integral_mono_on hx1 hconst hint hlower
  rw [intervalIntegral.integral_const, smul_eq_mul] at hintegral
  rw [hR1] at hFTC
  linarith

/-- **Explicit zero-free collar.**  If `3 c^2 (B-1) < 5`, an endpoint-normalized low-separation
radial solution is strictly positive on `[1,B]`. -/
theorem radialProlate_pos_endpoint_collar {s c B : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (_hB1 : 1 ≤ B) (hB2 : B ≤ 11 / 10)
    (hshort : 3 * c ^ 2 * (B - 1) < 5)
    (hR1 : R 1 = 1)
    (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ 2 - 1) * DDR t + 2 * t * DR t
      - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) :
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
  have hyshort : 3 * c ^ 2 * (y - 1) < 5 := by
    have hc2 : 0 ≤ 3 * c ^ 2 := by positivity
    have : y - 1 ≤ B - 1 := by linarith [hyIcc.2]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left this hc2) hshort
  rw [hyzero] at hlower
  nlinarith

end GaloisForLFunctions.RHTower

end
