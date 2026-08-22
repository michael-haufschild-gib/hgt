import Mathlib

/-!
# The dipolar-chain realization of the long-range lattice

Zhong--Malomed--Yan, arXiv:2407.12441, Section II C, equation (31).

Two parallel one-dimensional chains of dipoles at separation `L`, with dipolar densities `m₁, m₂`
and with the dipoles of chain `i` making a fixed angle `θᵢ` with the chain direction, interact with
energy

`E = -m₁ m₂ sin θ₁ sin θ₂ / (2π L²)`,

an inverse square in the separation.  That inverse square is exactly the `α = 2` coupling
`D_ℓ^{(2)} = 2(-1)^ℓ/ℓ²` of the quasi-Riesz lattice, which is why an array of parallel dipolar
condensates realises the model.

The computation is the integral along the chain of the dipole--dipole potential
`(m₁·m₂ - 3(m₁·r̂)(m₂·r̂))/r³` with unit permeability, i.e. with the prefactor `1/(4π)`.  It is
carried out here as a genuine limit of symmetric truncations, through the explicit primitive of the
kernel `A r^{-3} + (Bx² + Cx + D) r^{-5}`.

## Main results

* `invDist`, `hasDerivAt_invDist` — the reciprocal distance and its derivative.
* `hasDerivAt_dipolePrimitive` — the primitive of the kernel.
* `tendsto_integral_dipoleKernel` — the truncated integral of the kernel and its limit.
* `tendsto_integral_dipoleChainEnergy` — **equation (31)**.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.HTGeometry.FDNLS

/-! ## The reciprocal distance -/

/-- The reciprocal distance `(x² + L²)^{-1/2}` from a point of one chain to a point of the other. -/
noncomputable def invDist (L x : ℝ) : ℝ := (x ^ 2 + L ^ 2) ^ (-(1/2) : ℝ)

theorem sq_add_sq_pos {L : ℝ} (hL : 0 < L) (x : ℝ) : 0 < x ^ 2 + L ^ 2 := by positivity

theorem invDist_pos {L : ℝ} (hL : 0 < L) (x : ℝ) : 0 < invDist L x :=
  Real.rpow_pos_of_pos (sq_add_sq_pos hL x) _

theorem invDist_neg (L x : ℝ) : invDist L (-x) = invDist L x := by
  simp [invDist]

/-- The defining relation `v² (x² + L²) = 1`. -/
theorem invDist_sq_mul {L : ℝ} (hL : 0 < L) (x : ℝ) :
    invDist L x ^ 2 * (x ^ 2 + L ^ 2) = 1 := by
  have hw : (0:ℝ) < x ^ 2 + L ^ 2 := sq_add_sq_pos hL x
  have h : invDist L x ^ 2 = (x ^ 2 + L ^ 2) ^ (-1 : ℝ) := by
    rw [invDist, ← Real.rpow_natCast ((x ^ 2 + L ^ 2) ^ (-(1/2) : ℝ)) 2, ← Real.rpow_mul hw.le]
    norm_num
  rw [h, Real.rpow_neg_one, inv_mul_cancel₀ (ne_of_gt hw)]

theorem invDist_pow_three {L : ℝ} (hL : 0 < L) (x : ℝ) :
    invDist L x ^ 3 = (x ^ 2 + L ^ 2) ^ (-(3/2) : ℝ) := by
  have hw : (0:ℝ) < x ^ 2 + L ^ 2 := sq_add_sq_pos hL x
  rw [invDist, ← Real.rpow_natCast ((x ^ 2 + L ^ 2) ^ (-(1/2) : ℝ)) 3, ← Real.rpow_mul hw.le]
  norm_num

theorem hasDerivAt_invDist {L : ℝ} (hL : 0 < L) (x : ℝ) :
    HasDerivAt (invDist L) (-(x * invDist L x ^ 3)) x := by
  have hw : (0:ℝ) < x ^ 2 + L ^ 2 := sq_add_sq_pos hL x
  have hinner : HasDerivAt (fun y : ℝ => y ^ 2 + L ^ 2) (2 * x) x := by
    simpa using ((hasDerivAt_pow 2 x).add_const (L ^ 2))
  have h := hinner.rpow_const (p := -(1/2 : ℝ)) (Or.inl (ne_of_gt hw))
  refine h.congr_deriv ?_
  rw [invDist_pow_three hL]
  rw [show -(1/2 : ℝ) - 1 = -(3/2 : ℝ) by ring]
  ring

/-! ## The kernel and its primitive -/

/-- The dipolar kernel `A r^{-3} + (Bx² + Cx + D) r^{-5}`. -/
noncomputable def dipoleKernel (A B C D L x : ℝ) : ℝ :=
  A * invDist L x ^ 3 + (B * x ^ 2 + C * x + D) * invDist L x ^ 5

/-- Its primitive. -/
noncomputable def dipolePrimitive (A B C D L x : ℝ) : ℝ :=
  A * x * invDist L x / L ^ 2 + B * x ^ 3 * invDist L x ^ 3 / (3 * L ^ 2)
    - C * invDist L x ^ 3 / 3
    + D * x * (2 * x ^ 2 + 3 * L ^ 2) * invDist L x ^ 3 / (3 * L ^ 4)

theorem hasDerivAt_dipolePrimitive (A B C D : ℝ) {L : ℝ} (hL : 0 < L) (x : ℝ) :
    HasDerivAt (dipolePrimitive A B C D L) (dipoleKernel A B C D L x) x := by
  have hL2 : (L : ℝ) ^ 2 ≠ 0 := by positivity
  have hL4 : (L : ℝ) ^ 4 ≠ 0 := by positivity
  have hv := hasDerivAt_invDist hL x
  have hv3 : HasDerivAt (fun y : ℝ => invDist L y ^ 3)
      (3 * invDist L x ^ 2 * -(x * invDist L x ^ 3)) x := by
    have h := hv.pow 3
    have hfun : ((invDist L) ^ (3:ℕ) : ℝ → ℝ) = fun y => invDist L y ^ 3 := by
      funext y
      simp only [Pi.pow_apply]
    rw [hfun] at h
    exact h.congr_deriv (by push_cast; ring)
  have h1 : HasDerivAt (fun y : ℝ => A * y * invDist L y / L ^ 2)
      ((A * invDist L x + A * x * -(x * invDist L x ^ 3)) / L ^ 2) x := by
    have hx : HasDerivAt (fun y : ℝ => A * y) A x := by
      simpa using (hasDerivAt_id x).const_mul A
    have h := (hx.mul hv).div_const (L ^ 2)
    simp only [Pi.mul_def] at h
    exact h
  have h2 : HasDerivAt (fun y : ℝ => B * y ^ 3 * invDist L y ^ 3 / (3 * L ^ 2))
      ((B * (3 * x ^ 2) * invDist L x ^ 3
        + B * x ^ 3 * (3 * invDist L x ^ 2 * -(x * invDist L x ^ 3))) / (3 * L ^ 2)) x := by
    have hx : HasDerivAt (fun y : ℝ => B * y ^ 3) (B * (3 * x ^ 2)) x := by
      simpa using (hasDerivAt_pow 3 x).const_mul B
    have h := (hx.mul hv3).div_const (3 * L ^ 2)
    simp only [Pi.mul_def] at h
    exact h
  have h3 : HasDerivAt (fun y : ℝ => C * invDist L y ^ 3 / 3)
      (C * (3 * invDist L x ^ 2 * -(x * invDist L x ^ 3)) / 3) x :=
    (hv3.const_mul C).div_const 3
  have h4 : HasDerivAt (fun y : ℝ => D * y * (2 * y ^ 2 + 3 * L ^ 2) * invDist L y ^ 3 / (3 * L ^ 4))
      ((D * (6 * x ^ 2 + 3 * L ^ 2) * invDist L x ^ 3
        + D * x * (2 * x ^ 2 + 3 * L ^ 2)
          * (3 * invDist L x ^ 2 * -(x * invDist L x ^ 3))) / (3 * L ^ 4)) x := by
    have hx : HasDerivAt (fun y : ℝ => D * y * (2 * y ^ 2 + 3 * L ^ 2))
        (D * (6 * x ^ 2 + 3 * L ^ 2)) x := by
      have hp : HasDerivAt (fun y : ℝ => D * y * (2 * y ^ 2 + 3 * L ^ 2))
          (D * (2 * x ^ 2 + 3 * L ^ 2) + (D * x) * (2 * (2 * x))) x := by
        have ha : HasDerivAt (fun y : ℝ => D * y) D x := by
          simpa using (hasDerivAt_id x).const_mul D
        have hb : HasDerivAt (fun y : ℝ => 2 * y ^ 2 + 3 * L ^ 2) (2 * (2 * x)) x := by
          simpa using (((hasDerivAt_pow 2 x).const_mul (2:ℝ)).add_const (3 * L ^ 2))
        have h := ha.mul hb
        simp only [Pi.mul_def] at h
        exact h.congr_deriv (by ring)
      exact hp.congr_deriv (by ring)
    have h := (hx.mul hv3).div_const (3 * L ^ 4)
    simp only [Pi.mul_def] at h
    exact h
  have hsum := ((h1.add h2).sub h3).add h4
  refine hsum.congr_deriv ?_
  rw [dipoleKernel]
  have hrel := invDist_sq_mul hL x
  have ht : (x ^ 2 + L ^ 2) ≠ 0 := ne_of_gt (sq_add_sq_pos hL x)
  have hpow2 : invDist L x ^ 2 = (x ^ 2 + L ^ 2)⁻¹ := by
    field_simp
    linear_combination hrel
  have hpow3 : invDist L x ^ 3 = invDist L x * (x ^ 2 + L ^ 2)⁻¹ := by
    rw [show invDist L x ^ 3 = invDist L x * invDist L x ^ 2 by ring, hpow2]
  have hpow5 : invDist L x ^ 5 = invDist L x * ((x ^ 2 + L ^ 2)⁻¹) ^ 2 := by
    rw [show invDist L x ^ 5 = invDist L x * (invDist L x ^ 2) ^ 2 by ring, hpow2]
  rw [hpow5, hpow3, hpow2]
  field_simp
  ring

/-! ## The truncated integral and its limit -/

theorem continuous_invDist {L : ℝ} (hL : 0 < L) : Continuous (invDist L) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_invDist hL x).continuousAt

theorem integral_dipoleKernel (A B C D : ℝ) {L : ℝ} (hL : 0 < L) (R : ℝ) :
    (∫ x in (-R)..R, dipoleKernel A B C D L x)
      = dipolePrimitive A B C D L R - dipolePrimitive A B C D L (-R) := by
  have hcont : Continuous (fun x : ℝ => dipoleKernel A B C D L x) := by
    have hv := continuous_invDist hL
    exact (continuous_const.mul (hv.pow 3)).add
      ((((continuous_const.mul (continuous_pow 2)).add
        (continuous_const.mul continuous_id)).add continuous_const).mul (hv.pow 5))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_dipolePrimitive A B C D hL x) (hcont.intervalIntegrable _ _)

theorem tendsto_mul_invDist {L : ℝ} (hL : 0 < L) :
    Tendsto (fun R : ℝ => R * invDist L R) atTop (𝓝 1) := by
  have hsq : ∀ R : ℝ, (R * invDist L R) ^ 2 = R ^ 2 / (R ^ 2 + L ^ 2) := by
    intro R
    have hw : (0:ℝ) < R ^ 2 + L ^ 2 := sq_add_sq_pos hL R
    have h := invDist_sq_mul hL R
    field_simp
    linear_combination R ^ 2 * h
  have hden : Tendsto (fun R : ℝ => R ^ 2 + L ^ 2) atTop atTop :=
    tendsto_atTop_add_const_right _ (L ^ 2) (tendsto_pow_atTop two_ne_zero)
  have hfrac : Tendsto (fun R : ℝ => L ^ 2 / (R ^ 2 + L ^ 2)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hden
  have hone : Tendsto (fun R : ℝ => R ^ 2 / (R ^ 2 + L ^ 2)) atTop (𝓝 1) := by
    have hconst : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h : Tendsto (fun R : ℝ => 1 - L ^ 2 / (R ^ 2 + L ^ 2)) atTop (𝓝 1) := by
      simpa using hconst.sub hfrac
    refine h.congr fun R => ?_
    have hw : (0:ℝ) < R ^ 2 + L ^ 2 := sq_add_sq_pos hL R
    field_simp
    ring
  have hs2 : Tendsto (fun R : ℝ => (R * invDist L R) ^ 2) atTop (𝓝 1) :=
    hone.congr fun R => (hsq R).symm
  have hsqrt := (Real.continuous_sqrt.tendsto 1).comp hs2
  rw [Real.sqrt_one] at hsqrt
  refine hsqrt.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  exact Real.sqrt_sq (mul_nonneg hR.le (invDist_pos hL R).le)

theorem tendsto_invDist_sq {L : ℝ} (hL : 0 < L) :
    Tendsto (fun R : ℝ => invDist L R ^ 2) atTop (𝓝 0) := by
  have hden : Tendsto (fun R : ℝ => R ^ 2 + L ^ 2) atTop atTop :=
    tendsto_atTop_add_const_right _ (L ^ 2) (tendsto_pow_atTop two_ne_zero)
  have hfrac : Tendsto (fun R : ℝ => 1 / (R ^ 2 + L ^ 2)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hden
  refine hfrac.congr fun R => ?_
  have hw : (0:ℝ) < R ^ 2 + L ^ 2 := sq_add_sq_pos hL R
  rw [eq_comm, eq_div_iff (ne_of_gt hw)]
  exact invDist_sq_mul hL R

/-- **The truncated dipolar integral converges.** -/
theorem tendsto_integral_dipoleKernel (A B C D : ℝ) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, dipoleKernel A B C D L x) atTop
      (𝓝 (2 * A / L ^ 2 + 2 * B / (3 * L ^ 2) + 4 * D / (3 * L ^ 4))) := by
  have hL2 : (L : ℝ) ^ 2 ≠ 0 := by positivity
  have hL4 : (L : ℝ) ^ 4 ≠ 0 := by positivity
  have hval : ∀ R : ℝ,
      dipolePrimitive A B C D L R - dipolePrimitive A B C D L (-R)
        = 2 * A * (R * invDist L R) / L ^ 2
          + 2 * B * (R * invDist L R) ^ 3 / (3 * L ^ 2)
          + D * (4 * (R * invDist L R) ^ 3
            + 6 * L ^ 2 * ((R * invDist L R) * invDist L R ^ 2)) / (3 * L ^ 4) := by
    intro R
    rw [dipolePrimitive, dipolePrimitive, invDist_neg]
    field_simp
    ring
  have hs := tendsto_mul_invDist hL
  have hv2 := tendsto_invDist_sq hL
  have h1 : Tendsto (fun R : ℝ => 2 * A * (R * invDist L R) / L ^ 2) atTop
      (𝓝 (2 * A / L ^ 2)) := by
    simpa using (hs.const_mul (2 * A)).div_const (L ^ 2)
  have h2 : Tendsto (fun R : ℝ => 2 * B * (R * invDist L R) ^ 3 / (3 * L ^ 2)) atTop
      (𝓝 (2 * B / (3 * L ^ 2))) := by
    simpa using ((hs.pow 3).const_mul (2 * B)).div_const (3 * L ^ 2)
  have ha : Tendsto (fun R : ℝ => 4 * (R * invDist L R) ^ 3) atTop (𝓝 4) := by
    simpa using (hs.pow 3).const_mul (4:ℝ)
  have hb : Tendsto (fun R : ℝ => 6 * L ^ 2 * ((R * invDist L R) * invDist L R ^ 2)) atTop
      (𝓝 0) := by
    simpa using (hs.mul hv2).const_mul (6 * L ^ 2)
  have hinner : Tendsto (fun R : ℝ => 4 * (R * invDist L R) ^ 3
      + 6 * L ^ 2 * ((R * invDist L R) * invDist L R ^ 2)) atTop (𝓝 4) := by
    simpa using ha.add hb
  have h3 : Tendsto (fun R : ℝ => D * (4 * (R * invDist L R) ^ 3
      + 6 * L ^ 2 * ((R * invDist L R) * invDist L R ^ 2)) / (3 * L ^ 4)) atTop
      (𝓝 (4 * D / (3 * L ^ 4))) := by
    have h := (hinner.const_mul D).div_const (3 * L ^ 4)
    rw [show D * 4 / (3 * L ^ 4) = 4 * D / (3 * L ^ 4) by ring] at h
    exact h
  have hlim := (h1.add h2).add h3
  refine hlim.congr fun R => ?_
  rw [integral_dipoleKernel A B C D hL R, hval R]

/-! ## Equation (31) -/

/-- The dipole--dipole energy density between a dipole of chain one at the origin and a dipole of
chain two at horizontal displacement `x`, at chain separation `L`, with unit permeability. -/
noncomputable def dipoleChainIntegrand (m₁ m₂ θ₁ θ₂ L x : ℝ) : ℝ :=
  (m₁ * m₂ / (4 * Real.pi)) *
    dipoleKernel (Real.cos (θ₁ - θ₂)) (-3 * (Real.cos θ₁ * Real.cos θ₂))
      (-3 * (L * (Real.cos θ₁ * Real.sin θ₂ + Real.sin θ₁ * Real.cos θ₂)))
      (-3 * (L ^ 2 * (Real.sin θ₁ * Real.sin θ₂))) L x

/-- **Equation (31).**  The interaction energy of two parallel dipolar chains at separation `L` is
`-m₁ m₂ sin θ₁ sin θ₂ / (2π L²)`: an inverse square in the separation, with a prefactor that
vanishes when either chain is polarised along its own axis. -/
theorem tendsto_integral_dipoleChainEnergy (m₁ m₂ θ₁ θ₂ : ℝ) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, dipoleChainIntegrand m₁ m₂ θ₁ θ₂ L x) atTop
      (𝓝 (-(m₁ * m₂ * Real.sin θ₁ * Real.sin θ₂) / (2 * Real.pi * L ^ 2))) := by
  have hL2 : (L : ℝ) ^ 2 ≠ 0 := by positivity
  have hL4 : (L : ℝ) ^ 4 ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hbase := (tendsto_integral_dipoleKernel (Real.cos (θ₁ - θ₂))
    (-3 * (Real.cos θ₁ * Real.cos θ₂))
    (-3 * (L * (Real.cos θ₁ * Real.sin θ₂ + Real.sin θ₁ * Real.cos θ₂)))
    (-3 * (L ^ 2 * (Real.sin θ₁ * Real.sin θ₂))) hL).const_mul (m₁ * m₂ / (4 * Real.pi))
  have hvalue : (m₁ * m₂ / (4 * Real.pi)) * (2 * Real.cos (θ₁ - θ₂) / L ^ 2
      + 2 * (-3 * (Real.cos θ₁ * Real.cos θ₂)) / (3 * L ^ 2)
      + 4 * (-3 * (L ^ 2 * (Real.sin θ₁ * Real.sin θ₂))) / (3 * L ^ 4))
      = -(m₁ * m₂ * Real.sin θ₁ * Real.sin θ₂) / (2 * Real.pi * L ^ 2) := by
    rw [Real.cos_sub]
    field_simp
    ring
  rw [← hvalue]
  refine hbase.congr fun R => ?_
  rw [← intervalIntegral.integral_const_mul]
  rfl

end GaloisForLFunctions.HTGeometry.FDNLS
