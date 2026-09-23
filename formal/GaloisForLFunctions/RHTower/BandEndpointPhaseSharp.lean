import GaloisForLFunctions.RHTower.BandEndpointPhase
import GaloisForLFunctions.HTGeometry.EnvelopeFromLogDerivative

/-!
# Sharp endpoint behaviour of the band phase

The band phase `Xi_s(y) = int_y^(1 : ℕ) sqrt((t²-s)/(1-t²)) dt` is squeezed between two elementary
multiples of `sqrt(1-y)`:

```text
sqrt(y²-s) sqrt(2(1-y))  ≤  Xi_s(y)  ≤  sqrt(1-s) · 2 sqrt(1-y)/sqrt(1+y) .
```

Both sides agree to relative order `1-y` at the endpoint, which is exactly the accuracy at which the
logarithmic derivative `Xi'/Xi` can be separated from its explicit singular part `-y/(1-y²)`.  The
intermediate step is the same squeeze for `arccos`, proved by comparing derivatives on the open
interval — the derivatives blow up at `y = 1`, so the comparison is carried to the endpoint by
continuity alone.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-! ## The elementary squeeze for `arccos` -/

/-- **Lower squeeze.**  `sqrt(2(1-y)) ≤ arccos y`, from `1-t² ≤ 2(1-t)`. -/
theorem sqrt_two_mul_one_sub_le_arccos {y : ℝ} (hy1 : -1 ≤ y) (hy2 : y ≤ 1) :
    Real.sqrt (2 * (1 - y)) ≤ Real.arccos y := by
  set G : ℝ → ℝ := fun t => Real.sqrt (2 * (1 - t)) - Real.arccos t with hG
  have hcont : ContinuousOn G (Icc y 1) := by
    refine ContinuousOn.sub ?_ Real.continuous_arccos.continuousOn
    exact (Real.continuous_sqrt.comp
      (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  have hderiv : ∀ t ∈ Ioo y 1, HasDerivAt G
      (-(1 / Real.sqrt (2 * (1 - t))) + 1 / Real.sqrt (1 - t ^ (2 : ℕ))) t := by
    intro t ht
    have ht1 : t < 1 := ht.2
    have htm1 : -1 < t := lt_of_le_of_lt hy1 ht.1
    have hpos : (0 : ℝ) < 2 * (1 - t) := by linarith
    have hin : HasDerivAt (fun u : ℝ => 2 * (1 - u)) (-2) t := by
      have h := ((hasDerivAt_id t).const_sub 1).const_mul (2 : ℝ)
      exact h.congr_deriv (by ring)
    have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (2 * (1 - t)))) (2 * (1 - t)) :=
      Real.hasDerivAt_sqrt hpos.ne'
    have h1 : HasDerivAt (fun u : ℝ => Real.sqrt (2 * (1 - u)))
        (-(1 / Real.sqrt (2 * (1 - t)))) t := by
      refine (hsq.comp t hin).congr_deriv ?_
      have hs : (0 : ℝ) < Real.sqrt (2 * (1 - t)) := Real.sqrt_pos.2 hpos
      field_simp
    have h2 : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - t ^ (2 : ℕ)))) t :=
      Real.hasDerivAt_arccos (by linarith) (by linarith)
    exact (h1.sub h2).congr_deriv (by ring)
  have hnn : ∀ t ∈ Ioo y 1, 0 ≤ -(1 / Real.sqrt (2 * (1 - t))) + 1 / Real.sqrt (1 - t ^ (2 : ℕ)) := by
    intro t ht
    have ht1 : t < 1 := ht.2
    have htm1 : -1 < t := lt_of_le_of_lt hy1 ht.1
    have h1 : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith
    have h2 : (0 : ℝ) < 2 * (1 - t) := by linarith
    have hle : Real.sqrt (1 - t ^ (2 : ℕ)) ≤ Real.sqrt (2 * (1 - t)) := by
      refine Real.sqrt_le_sqrt ?_
      nlinarith
    have hp1 : (0 : ℝ) < Real.sqrt (1 - t ^ (2 : ℕ)) := Real.sqrt_pos.2 h1
    have hp2 : (0 : ℝ) < Real.sqrt (2 * (1 - t)) := Real.sqrt_pos.2 h2
    have := one_div_le_one_div_of_le hp1 hle
    linarith
  have h := le_of_continuousOn_of_deriv_nonneg hy2 hcont hderiv hnn
  have hG1 : G 1 = 0 := by simp [hG]
  have hGy : G y = Real.sqrt (2 * (1 - y)) - Real.arccos y := rfl
  rw [hG1, hGy] at h
  linarith

/-- **Upper squeeze.**  `arccos y ≤ 2 sqrt(1-y)/sqrt(1+y)`, from `1+t ≤ 2`. -/
theorem arccos_le_two_mul_sqrt_div {y : ℝ} (hy1 : -1 < y) (hy2 : y ≤ 1) :
    Real.arccos y ≤ 2 * Real.sqrt (1 - y) / Real.sqrt (1 + y) := by
  set H : ℝ → ℝ := fun t => Real.arccos t - 2 * Real.sqrt (1 - t) / Real.sqrt (1 + t) with hH
  have hnum : Continuous fun t : ℝ => 2 * Real.sqrt (1 - t) :=
    continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub continuous_id))
  have hden : Continuous fun t : ℝ => Real.sqrt (1 + t) :=
    Real.continuous_sqrt.comp (continuous_const.add continuous_id)
  have hcont : ContinuousOn H (Icc y 1) := by
    refine Real.continuous_arccos.continuousOn.sub
      (ContinuousOn.div hnum.continuousOn hden.continuousOn ?_)
    intro t ht
    have hty : y ≤ t := ht.1
    have : (0 : ℝ) < 1 + t := by linarith
    exact (Real.sqrt_pos.2 this).ne'
  have hderiv : ∀ t ∈ Ioo y 1, HasDerivAt H
      (-(1 / Real.sqrt (1 - t ^ (2 : ℕ)))
        + 2 / (Real.sqrt (1 - t) * Real.sqrt (1 + t) * Real.sqrt (1 + t) ^ (2 : ℕ))) t := by
    intro t ht
    have ht1 : t < 1 := ht.2
    have htm1 : -1 < t := lt_trans hy1 ht.1
    have hp : (0 : ℝ) < 1 - t := by linarith
    have hq : (0 : ℝ) < 1 + t := by linarith
    have hsp : (0 : ℝ) < Real.sqrt (1 - t) := Real.sqrt_pos.2 hp
    have hsq : (0 : ℝ) < Real.sqrt (1 + t) := Real.sqrt_pos.2 hq
    have hp2 : Real.sqrt (1 - t) ^ (2 : ℕ) = 1 - t := Real.sq_sqrt hp.le
    have hq2 : Real.sqrt (1 + t) ^ (2 : ℕ) = 1 + t := Real.sq_sqrt hq.le
    have h1 : HasDerivAt (fun u : ℝ => Real.sqrt (1 - u)) (-(1 / (2 * Real.sqrt (1 - t)))) t := by
      have hin : HasDerivAt (fun u : ℝ => 1 - u) (-1) t := (hasDerivAt_id t).const_sub 1
      refine ((Real.hasDerivAt_sqrt hp.ne').comp t hin).congr_deriv ?_
      field_simp
    have h2 : HasDerivAt (fun u : ℝ => Real.sqrt (1 + u)) (1 / (2 * Real.sqrt (1 + t))) t := by
      have hin : HasDerivAt (fun u : ℝ => 1 + u) 1 t := (hasDerivAt_id t).const_add 1
      refine ((Real.hasDerivAt_sqrt hq.ne').comp t hin).congr_deriv ?_
      field_simp
    have h3 : HasDerivAt (fun u : ℝ => 2 * Real.sqrt (1 - u) / Real.sqrt (1 + u))
        (-(2 / (Real.sqrt (1 - t) * Real.sqrt (1 + t) * Real.sqrt (1 + t) ^ (2 : ℕ)))) t := by
      refine ((h1.const_mul (2 : ℝ)).fun_div h2 hsq.ne').congr_deriv ?_
      field_simp
      nlinarith [hp2, hq2, hsp, hsq]
    have h4 : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - t ^ (2 : ℕ)))) t :=
      Real.hasDerivAt_arccos (by linarith) (by linarith)
    exact (h4.sub h3).congr_deriv (by ring)
  have hnn : ∀ t ∈ Ioo y 1, 0 ≤ -(1 / Real.sqrt (1 - t ^ (2 : ℕ)))
      + 2 / (Real.sqrt (1 - t) * Real.sqrt (1 + t) * Real.sqrt (1 + t) ^ (2 : ℕ)) := by
    intro t ht
    have ht1 : t < 1 := ht.2
    have htm1 : -1 < t := lt_trans hy1 ht.1
    have hp : (0 : ℝ) < 1 - t := by linarith
    have hq : (0 : ℝ) < 1 + t := by linarith
    have hsp : (0 : ℝ) < Real.sqrt (1 - t) := Real.sqrt_pos.2 hp
    have hsq : (0 : ℝ) < Real.sqrt (1 + t) := Real.sqrt_pos.2 hq
    have hq2 : Real.sqrt (1 + t) ^ (2 : ℕ) = 1 + t := Real.sq_sqrt hq.le
    have hfac : Real.sqrt (1 - t ^ (2 : ℕ)) = Real.sqrt (1 - t) * Real.sqrt (1 + t) := by
      rw [← Real.sqrt_mul hp.le]
      ring_nf
    rw [hfac]
    have hkey : 1 / (Real.sqrt (1 - t) * Real.sqrt (1 + t))
        ≤ 2 / (Real.sqrt (1 - t) * Real.sqrt (1 + t) * Real.sqrt (1 + t) ^ (2 : ℕ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), hq2]
      nlinarith [mul_pos hsp hsq, ht1.le]
    linarith
  have h := le_of_continuousOn_of_deriv_nonneg hy2 hcont hderiv hnn
  have hH1 : H 1 = 0 := by simp [hH]
  have hHy : H y = Real.arccos y - 2 * Real.sqrt (1 - y) / Real.sqrt (1 + y) := rfl
  rw [hH1, hHy] at h
  linarith

/-! ## The sharp squeeze for the band phase -/

/-- **The phase from above at the endpoint rate.** -/
theorem bandEndpointPhase_le_sharp {s y : ℝ} (hy0 : 0 ≤ y) (hy2 : y ≤ 1) :
    bandEndpointPhase s y
      ≤ Real.sqrt (1 - s) * (2 * Real.sqrt (1 - y) / Real.sqrt (1 + y)) := by
  refine (bandEndpointPhase_le_sqrt_mul_arccos hy0 hy2).trans ?_
  refine mul_le_mul_of_nonneg_left (arccos_le_two_mul_sqrt_div (by linarith) hy2)
    (Real.sqrt_nonneg _)

/-- **The phase from below at the endpoint rate.** -/
theorem sharp_le_bandEndpointPhase {s y : ℝ} (hy0 : 0 ≤ y) (hy2 : y ≤ 1) :
    Real.sqrt (y ^ (2 : ℕ) - s) * Real.sqrt (2 * (1 - y)) ≤ bandEndpointPhase s y := by
  refine le_trans ?_ (sqrt_mul_arccos_le_bandEndpointPhase hy0 hy2)
  exact mul_le_mul_of_nonneg_left (sqrt_two_mul_one_sub_le_arccos (by linarith) hy2)
    (Real.sqrt_nonneg _)

end GaloisForLFunctions.RHTower

end
