import GaloisForLFunctions.HTGeometry.SectorPowerMassLower

/-!
# The Hausdorff CDD phase kernel

A paired CDD shell of radius `r ∈ (0,1)` contributes the rapidity phase
`4 arctan(sinh θ / B)` with `B = (1+r²)/(2r)`.  Written against the Hausdorff source variable
`y = r²` this is `r · K(y,θ)` for the kernel

```
K(y,θ) = 4 (arctan(√y e^θ) − arctan(√y e^{−θ})) / √y,      K(0,θ) = 8 sinh θ.
```

This module builds the kernel and its two analytic properties: the exact single-arctangent form of
the difference, and the explicit modulus

```
|K(y,θ) − 8 sinh θ| ≤ (8/3) |y| cosh 3θ,
```

which makes `K` continuous at the zero shell.  The modulus rests on cubic Taylor control of the
arctangent, `|arctan t − t| ≤ |t|³/3`, proved here by monotonicity of `w ↦ w³/3 − w + arctan w`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Cubic control of the arctangent -/

/-- On the nonnegative half-line the arctangent lies below the identity. -/
theorem arctan_le_self {t : ℝ} (ht : 0 ≤ t) : Real.arctan t ≤ t := by
  have h := abs_arctan_le_abs t
  rwa [abs_of_nonneg ht, abs_of_nonneg (Real.arctan_nonneg.mpr ht)] at h

/-- **Cubic Taylor control of the arctangent.**  For `t ≥ 0` the defect `t - arctan t` is at most
`t³/3`.  The proof is monotonicity of `w ↦ w³/3 - w + arctan w`, whose derivative is
`w⁴/(1+w²) ≥ 0`. -/
theorem sub_arctan_le_cube_div_three {t : ℝ} (ht : 0 ≤ t) :
    t - Real.arctan t ≤ t ^ 3 / 3 := by
  have hmono : MonotoneOn (fun w : ℝ => w ^ 3 / 3 - w + Real.arctan w) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (((continuous_pow 3).div_const 3).sub continuous_id).add
        Real.continuous_arctan |>.continuousOn
    · intro u _
      exact ((((differentiable_pow 3).div_const 3).sub differentiable_id).add
        Real.differentiable_arctan u).differentiableWithinAt
    · intro u _
      have h1 : HasDerivAt (fun w : ℝ => w ^ 3 / 3) (u ^ 2) u := by
        have h := (hasDerivAt_pow 3 u).div_const 3
        simpa only [Pi.div_apply] using! h.congr_deriv (by
          push_cast
          ring)
      have h2 : HasDerivAt (fun w : ℝ => w) 1 u := hasDerivAt_id u
      have h3 := Real.hasDerivAt_arctan u
      have hd : deriv (fun w : ℝ => w ^ 3 / 3 - w + Real.arctan w) u
          = u ^ 2 - 1 + 1 / (1 + u ^ 2) := ((h1.sub h2).add h3).deriv
      rw [hd]
      have hkey : u ^ 2 - 1 + 1 / (1 + u ^ 2) = u ^ 4 / (1 + u ^ 2) := by
        have hpos : (1 : ℝ) + u ^ 2 ≠ 0 := by positivity
        field_simp
        ring
      rw [hkey]
      positivity
  have h0 := hmono Set.self_mem_Ici (Set.mem_Ici.mpr ht) ht
  simp only [Real.arctan_zero] at h0
  norm_num at h0
  linarith

/-- Two-sided cubic Taylor control of the arctangent. -/
theorem abs_arctan_sub_self_le_cube (t : ℝ) : |Real.arctan t - t| ≤ |t| ^ 3 / 3 := by
  rcases le_total 0 t with ht | ht
  · have h1 : Real.arctan t - t ≤ 0 := by linarith [arctan_le_self ht]
    have h2 := sub_arctan_le_cube_div_three ht
    rw [abs_of_nonpos h1, abs_of_nonneg ht]
    linarith
  · have ht' : 0 ≤ -t := by linarith
    have h1 : Real.arctan (-t) ≤ -t := arctan_le_self ht'
    have h2 := sub_arctan_le_cube_div_three ht'
    rw [Real.arctan_neg] at h1 h2
    have habs : |t| = -t := abs_of_nonpos ht
    rw [habs]
    have hge : 0 ≤ Real.arctan t - t := by linarith
    rw [abs_of_nonneg hge]
    linarith

/-- The hyperbolic cosine is dominated by the exponential of the absolute value. -/
theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-! ## The kernel -/

/-- The Hausdorff phase kernel `K(y,θ) = 4(arctan(√y e^θ) − arctan(√y e^{−θ}))/√y`, extended by its
limiting value `K(0,θ) = 8 sinh θ` at the zero shell. -/
def cddPhaseKernel (y θ : ℝ) : ℝ :=
  if 0 < y then
    4 * (Real.arctan (Real.sqrt y * Real.exp θ)
      - Real.arctan (Real.sqrt y * Real.exp (-θ))) / Real.sqrt y
  else 8 * Real.sinh θ

@[simp]
theorem cddPhaseKernel_zero (θ : ℝ) : cddPhaseKernel 0 θ = 8 * Real.sinh θ := by
  simp [cddPhaseKernel]

/-- The arctangent difference of a reciprocal exponential pair is a single arctangent. -/
theorem arctan_sub_arctan_exp (u θ : ℝ) :
    Real.arctan (u * Real.exp θ) - Real.arctan (u * Real.exp (-θ))
      = Real.arctan (2 * u * Real.sinh θ / (1 + u ^ 2)) := by
  have hexp : Real.exp θ * Real.exp (-θ) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hprod : (u * Real.exp θ) * (-(u * Real.exp (-θ))) = -u ^ 2 := by
    have hmul : (u * Real.exp θ) * (u * Real.exp (-θ))
        = u ^ 2 * (Real.exp θ * Real.exp (-θ)) := by ring
    nlinarith [hmul, hexp]
  have hlt : (u * Real.exp θ) * (-(u * Real.exp (-θ))) < 1 := by
    rw [hprod]; nlinarith [sq_nonneg u]
  have h := Real.arctan_add hlt
  rw [Real.arctan_neg] at h
  have hden : 1 - (u * Real.exp θ) * (-(u * Real.exp (-θ))) = 1 + u ^ 2 := by
    rw [hprod]; ring
  have hnum : u * Real.exp θ + -(u * Real.exp (-θ)) = 2 * u * Real.sinh θ := by
    rw [Real.sinh_eq]; ring
  rw [hden, hnum] at h
  linarith [h]

/-- Closed form of the kernel at a positive shell radius. -/
theorem cddPhaseKernel_sq {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    r * cddPhaseKernel (r ^ 2) θ = 4 * Real.arctan (2 * r * Real.sinh θ / (1 + r ^ 2)) := by
  have hpos : 0 < r ^ 2 := by positivity
  have hsqrt : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
  rw [cddPhaseKernel, if_pos hpos, hsqrt, arctan_sub_arctan_exp]
  field_simp

/-- **Uniform kernel estimate.**  `|K(y,θ) − 8 sinh θ| ≤ (8/3)|y| cosh 3θ`, so the kernel is
continuous at the zero shell with an explicit modulus. -/
theorem abs_cddPhaseKernel_sub_flat_le (y θ : ℝ) :
    |cddPhaseKernel y θ - 8 * Real.sinh θ| ≤ 8 / 3 * |y| * Real.cosh (3 * θ) := by
  rcases le_or_gt y 0 with hy | hy
  · rw [cddPhaseKernel, if_neg (not_lt.mpr hy), sub_self, abs_zero]
    have := Real.cosh_pos (3 * θ)
    positivity
  · have hu : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have hu2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    have hsinh : 8 * Real.sinh θ = 4 * (Real.exp θ - Real.exp (-θ)) := by
      rw [Real.sinh_eq]; ring
    have hsplit : cddPhaseKernel y θ - 8 * Real.sinh θ
        = 4 / Real.sqrt y *
          ((Real.arctan (Real.sqrt y * Real.exp θ) - Real.sqrt y * Real.exp θ)
            - (Real.arctan (Real.sqrt y * Real.exp (-θ)) - Real.sqrt y * Real.exp (-θ))) := by
      rw [cddPhaseKernel, if_pos hy, hsinh]
      field_simp
      ring
    have hA := abs_arctan_sub_self_le_cube (Real.sqrt y * Real.exp θ)
    have hB := abs_arctan_sub_self_le_cube (Real.sqrt y * Real.exp (-θ))
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt y * Real.exp θ)] at hA
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt y * Real.exp (-θ))] at hB
    have htri :
        |(Real.arctan (Real.sqrt y * Real.exp θ) - Real.sqrt y * Real.exp θ)
          - (Real.arctan (Real.sqrt y * Real.exp (-θ)) - Real.sqrt y * Real.exp (-θ))|
        ≤ (Real.sqrt y * Real.exp θ) ^ 3 / 3 + (Real.sqrt y * Real.exp (-θ)) ^ 3 / 3 := by
      calc _ ≤ |Real.arctan (Real.sqrt y * Real.exp θ) - Real.sqrt y * Real.exp θ|
              + |Real.arctan (Real.sqrt y * Real.exp (-θ)) - Real.sqrt y * Real.exp (-θ)| :=
            abs_sub _ _
        _ ≤ _ := by linarith
    have hcube : (Real.sqrt y * Real.exp θ) ^ 3 / 3 + (Real.sqrt y * Real.exp (-θ)) ^ 3 / 3
        = Real.sqrt y ^ 3 / 3 * (Real.exp (3 * θ) + Real.exp (-(3 * θ))) := by
      have h1 : Real.exp θ ^ 3 = Real.exp (3 * θ) := by
        rw [show (3 : ℝ) * θ = θ + θ + θ by ring, Real.exp_add, Real.exp_add]
        ring
      have h2 : Real.exp (-θ) ^ 3 = Real.exp (-(3 * θ)) := by
        rw [show -((3 : ℝ) * θ) = -θ + -θ + -θ by ring, Real.exp_add, Real.exp_add]
        ring
      rw [mul_pow, mul_pow, h1, h2]
      ring
    have hcosh : Real.exp (3 * θ) + Real.exp (-(3 * θ)) = 2 * Real.cosh (3 * θ) := by
      rw [Real.cosh_eq]; ring
    rw [hsplit, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 / Real.sqrt y)]
    have hfinal : 4 / Real.sqrt y * (Real.sqrt y ^ 3 / 3 * (2 * Real.cosh (3 * θ)))
        = 8 / 3 * y * Real.cosh (3 * θ) := by
      field_simp
      nlinarith [hu2, hu.le, Real.cosh_pos (3 * θ)]
    calc 4 / Real.sqrt y *
        |(Real.arctan (Real.sqrt y * Real.exp θ) - Real.sqrt y * Real.exp θ)
          - (Real.arctan (Real.sqrt y * Real.exp (-θ)) - Real.sqrt y * Real.exp (-θ))|
        ≤ 4 / Real.sqrt y * (Real.sqrt y ^ 3 / 3 * (2 * Real.cosh (3 * θ))) := by
          have hstep := htri
          rw [hcube, hcosh] at hstep
          exact mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 8 / 3 * y * Real.cosh (3 * θ) := hfinal
      _ = 8 / 3 * |y| * Real.cosh (3 * θ) := by rw [abs_of_pos hy]

/-- The phase kernel is continuous in the shell variable, including at the zero shell. -/
theorem continuous_cddPhaseKernel (θ : ℝ) : Continuous fun y => cddPhaseKernel y θ := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases lt_trichotomy y 0 with h | h | h
  · have heq : (fun _ : ℝ => 8 * Real.sinh θ) =ᶠ[𝓝 y] fun z => cddPhaseKernel z θ := by
      filter_upwards [Iio_mem_nhds h] with z hz
      rw [cddPhaseKernel, if_neg (not_lt.mpr (le_of_lt hz))]
    exact continuousAt_const.congr heq
  · subst h
    have hbound : ∀ z : ℝ, ‖cddPhaseKernel z θ - 8 * Real.sinh θ‖
        ≤ 8 / 3 * |z| * Real.cosh (3 * θ) := fun z =>
      abs_cddPhaseKernel_sub_flat_le z θ
    have hg : Tendsto (fun z : ℝ => 8 / 3 * |z| * Real.cosh (3 * θ)) (𝓝 0) (𝓝 0) := by
      have hcont : Continuous fun z : ℝ => 8 / 3 * |z| * Real.cosh (3 * θ) :=
        (continuous_const.mul continuous_abs).mul continuous_const
      simpa using hcont.tendsto 0
    have hlim : Tendsto (fun z : ℝ => cddPhaseKernel z θ - 8 * Real.sinh θ) (𝓝 0) (𝓝 0) :=
      squeeze_zero_norm hbound hg
    have hshift := hlim.add_const (8 * Real.sinh θ)
    simp only [sub_add_cancel, zero_add] at hshift
    rw [ContinuousAt, cddPhaseKernel_zero]
    exact hshift
  · have hg : ContinuousAt (fun z : ℝ =>
        4 * (Real.arctan (Real.sqrt z * Real.exp θ)
          - Real.arctan (Real.sqrt z * Real.exp (-θ))) / Real.sqrt z) y := by
      refine ContinuousAt.div ?_ (Real.continuous_sqrt.continuousAt)
        (ne_of_gt (Real.sqrt_pos.mpr h))
      exact continuousAt_const.mul
        (((Real.continuous_arctan.comp
            (Real.continuous_sqrt.mul continuous_const)).continuousAt).sub
          ((Real.continuous_arctan.comp
            (Real.continuous_sqrt.mul continuous_const)).continuousAt))
    refine hg.congr ?_
    filter_upwards [Ioi_mem_nhds h] with z hz
    rw [cddPhaseKernel, if_pos (Set.mem_Ioi.mp hz)]

/-- The kernel is bounded on the Hausdorff source interval `[0,1]` at every fixed rapidity. -/
theorem exists_bound_cddPhaseKernel (θ : ℝ) :
    ∃ K : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1, |cddPhaseKernel y θ| ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_cddPhaseKernel θ).continuousOn
  exact ⟨K, fun y hy => by simpa [Real.norm_eq_abs] using hK y hy⟩

end

end GaloisForLFunctions.HTGeometry
