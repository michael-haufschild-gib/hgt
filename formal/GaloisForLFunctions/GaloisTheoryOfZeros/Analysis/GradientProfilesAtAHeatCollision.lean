import GaloisForLFunctions.GaloisTheoryOfZeros.TheHermiteMonodromyOfACollision

/-!
# Gradient and reciprocal-residue profiles of the heat sheets

Du, Yang and Zhang (arXiv:2611.24046, §§3, 6) use the squared complex
gradient and its homogeneous rescaling to distinguish blow-up profiles.
For the real part of a holomorphic heat slice this square is `(H')²`.
At an order-`n+1` collision it has scale `s^(2n)`. The limiting
coefficient on each sheet is determined by the derivative of the Hermite
profile. Its inverse determines the residue of the reciprocal heat slice.
-/

noncomputable section
open Complex Filter Topology
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Derivative of the Hermite tangent polynomial with the physical jet normalization. -/
def collisionGradientProfile (τ z : ℂ) (m : ℕ) (y : ℂ) : ℂ :=
  iteratedDeriv m (complexHeat τ) z / (m.factorial : ℂ) * deriv (heatModelFwd m) y

private def scaledGradient (τ z : ℂ) (m : ℕ) (p : ℂ × ℂ) : ℂ :=
  fderiv ℂ (collisionBlowup τ z m) p (0, 1)

private theorem scaledGradient_slice (τ z : ℂ) (m : ℕ) (s y : ℂ) :
    HasDerivAt (fun w : ℂ => collisionBlowup τ z m (s,w))
      (scaledGradient τ z m (s,y)) y :=
  (analyticAt_collisionBlowup τ z m (s,y)).differentiableAt.hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y s).prodMk (hasDerivAt_id y))

private theorem scaledGradient_zero {τ z : ℂ} {m : ℕ} (hc : IsCollision τ z m) (y : ℂ) :
    scaledGradient τ z m (0,y) = collisionGradientProfile τ z m y := by
  have h := scaledGradient_slice τ z m 0 y
  simp_rw [collisionBlowup_zero hc.vanish] at h
  exact h.unique (((differentiable_heatModelFwd m y).hasDerivAt).const_mul _)

private theorem scaledGradient_continuousAt (τ z : ℂ) (m : ℕ) (p : ℂ × ℂ) :
    ContinuousAt (scaledGradient τ z m) p :=
  (analyticAt_collisionBlowup τ z m p).fderiv.continuousAt.clm_apply continuousAt_const

/-- Differentiation in the blown-up spatial coordinate removes one power of scale. -/
private theorem spatial_gradient_factor {τ z s : ℂ} {n : ℕ} (hc : IsCollision τ z (n+1))
    (hs : s ≠ 0) (y : ℂ) :
    deriv (complexHeat (τ+s^2)) (z+s*y) = s^n * scaledGradient τ z (n+1) (s,y) := by
  have h1 := (differentiable_complexHeat (τ+s^2) (z+s*y)).hasDerivAt.comp y
    (((hasDerivAt_id y).const_mul s).const_add z)
  change HasDerivAt (fun w : ℂ => complexHeat (τ+s^2) (z+s*w))
    (deriv (complexHeat (τ+s^2)) (z+s*y) * (s*1)) y at h1
  simp_rw [complexHeat_blowup hc.vanish] at h1
  have he := h1.unique ((scaledGradient_slice τ z (n+1) s y).const_mul (s^(n+1)))
  rw [mul_one, pow_succ] at he
  exact mul_right_cancel₀ hs (he.trans (by ring))

/-- The normalized gradient has a joint limit along *every* path of spatial
coordinates approaching the chosen point on the exceptional fibre. -/
theorem IsCollision.tendsto_scaled_gradient {τ z y : ℂ} {n : ℕ} (hc : IsCollision τ z (n+1))
    {u : ℂ → ℂ} (hu : Tendsto u (𝓝[≠] 0) (𝓝 y)) :
    Tendsto (fun s => deriv (complexHeat (τ+s^2)) (z+s*u s) / s^n)
      (𝓝[≠] 0) (𝓝 (collisionGradientProfile τ z (n+1) y)) := by
  have hp := (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto id (𝓝[≠] (0:ℂ)) (𝓝 0)).prodMk_nhds hu
  have hh := (scaledGradient_continuousAt τ z (n+1) (0,y)).tendsto.comp hp
  rw [scaledGradient_zero hc] at hh
  refine hh.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  change scaledGradient τ z (n+1) (s,u s) = _
  rw [spatial_gradient_factor hc hs0, mul_div_cancel_left₀ _ (pow_ne_zero _ hs0)]

/-- The Hopf differential of the real part of a heat slice has the square
of the Hermite gradient as its tangent on every sheet. -/
theorem IsCollision.sheet_hopf_limit {τ z ρ : ℂ} {n : ℕ} (hc : IsCollision τ z (n+1))
    (hρ : heatModelFwd (n+1) ρ = 0) :
    Tendsto (fun s => (deriv (complexHeat (τ+s^2)) (collisionZero τ z (n+1) ρ s))^2 /
      s^(2*n)) (𝓝[≠] 0) (𝓝 ((collisionGradientProfile τ z (n+1) ρ)^2)) := by
  obtain ⟨ha, h0, _, _⟩ := collisionBranch_spec hc hρ
  have hb := ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [h0] at hb
  simpa only [collisionZero, div_pow, ← pow_mul, Nat.mul_comm n 2] using
    (hc.tendsto_scaled_gradient hb).pow 2

/-- The tangent weight never vanishes at a Hermite root. -/
theorem IsCollision.gradientProfile_ne_zero {τ z ρ : ℂ} {m : ℕ} (hc : IsCollision τ z m)
    (hρ : heatModelFwd m ρ = 0) : collisionGradientProfile τ z m ρ ≠ 0 :=
  mul_ne_zero (div_ne_zero hc.top_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m))
    (deriv_heatModelFwd_ne_zero hρ)

/-- Leading coefficient of the pole residue of `1/H` at a separating sheet. -/
theorem IsCollision.sheet_reciprocal_residue_limit {τ z ρ : ℂ} {n : ℕ}
    (hc : IsCollision τ z (n+1)) (hρ : heatModelFwd (n+1) ρ = 0) :
    Tendsto (fun s => s^n / deriv (complexHeat (τ+s^2)) (collisionZero τ z (n+1) ρ s))
      (𝓝[≠] 0) (𝓝 (collisionGradientProfile τ z (n+1) ρ)⁻¹) := by
  obtain ⟨ha, h0, _, _⟩ := collisionBranch_spec hc hρ
  have hb := ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [h0] at hb
  simpa only [inv_div, collisionZero] using
    (hc.tendsto_scaled_gradient hb).inv₀ (hc.gradientProfile_ne_zero hρ)

/-- Away from a Hermite root the scaled logarithmic derivative has a
universal limit. The first nonzero spatial jet cancels from the quotient. -/
theorem IsCollision.logDeriv_profile {τ z y : ℂ} {n : ℕ} (hc : IsCollision τ z (n+1))
    (hy : heatModelFwd (n+1) y ≠ 0) {u : ℂ → ℂ} (hu : Tendsto u (𝓝[≠] 0) (𝓝 y)) :
    Tendsto (fun s => s * logDeriv (complexHeat (τ+s^2)) (z+s*u s)) (𝓝[≠] 0)
      (𝓝 (logDeriv (heatModelFwd (n+1)) y)) := by
  let c := iteratedDeriv (n+1) (complexHeat τ) z / ((n+1).factorial : ℂ)
  have hc0 : c ≠ 0 := div_ne_zero hc.top_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _)
  have hp := (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto id (𝓝[≠] (0:ℂ)) (𝓝 0)).prodMk_nhds hu
  have hg := (continuous_collisionBlowup τ z (n+1)).continuousAt.tendsto.comp hp
  rw [collisionBlowup_zero hc.vanish] at hg
  have hh := (hc.tendsto_scaled_gradient hu).div hg (mul_ne_zero hc0 hy)
  have hcanc : collisionGradientProfile τ z (n+1) y / (c*heatModelFwd (n+1) y) =
      logDeriv (heatModelFwd (n+1)) y := by
    change (c * _)/(c * _) = _ / _
    rw [mul_div_mul_left _ _ hc0]
  rw [hcanc] at hh
  refine hh.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  change (_ / s^n) / collisionBlowup τ z (n+1) (s,u s) = s * (_ / _)
  rw [complexHeat_blowup hc.vanish, pow_succ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf
  simp [hs0]

/-- The gradient asymptotics force simplicity of every emerging sheet
throughout a punctured neighborhood of the collision time parameter. -/
theorem IsCollision.eventually_sheet_deriv_ne_zero {τ z ρ : ℂ} {n : ℕ}
    (hc : IsCollision τ z (n+1)) (hρ : heatModelFwd (n+1) ρ = 0) :
    ∀ᶠ s in 𝓝[≠] (0 : ℂ), deriv (complexHeat (τ+s^2)) (collisionZero τ z (n+1) ρ s) ≠ 0 := by
  obtain ⟨ha, h0, _, _⟩ := collisionBranch_spec hc hρ
  have hb := ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [h0] at hb
  filter_upwards [(hc.tendsto_scaled_gradient hb).eventually_ne (hc.gradientProfile_ne_zero hρ)]
    with s hs
  exact fun h => hs (by rw [← collisionZero, h, zero_div])

/-- At a separating sheet the inverse spatial derivative is the actual
residue of the reciprocal. This gives its local pole interpretation before
the sheets meet. -/
theorem IsCollision.sheet_pole_limit {τ z ρ : ℂ} {n : ℕ}
    (hc : IsCollision τ z (n+1)) (hρ : heatModelFwd (n+1) ρ = 0) :
    ∀ᶠ s in 𝓝[≠] (0 : ℂ), let w := collisionZero τ z (n+1) ρ s
      Tendsto (fun u => (u-w)/complexHeat (τ+s^2) u) (𝓝[≠] w)
        (𝓝 (deriv (complexHeat (τ+s^2)) w)⁻¹) := by
  filter_upwards [hc.eventually_sheet_deriv_ne_zero hρ,
    (complexHeat_collisionZero hc hρ).filter_mono nhdsWithin_le_nhds] with s hd hz
  let w := collisionZero τ z (n+1) ρ s
  have hh := ((differentiable_complexHeat (τ+s^2) w).hasDerivAt.tendsto_slope).inv₀ hd
  simpa only [slope_def_field, w, hz, sub_zero, inv_div] using hh

#print axioms IsCollision.tendsto_scaled_gradient
#print axioms IsCollision.sheet_hopf_limit
#print axioms IsCollision.gradientProfile_ne_zero
#print axioms IsCollision.sheet_reciprocal_residue_limit
#print axioms IsCollision.logDeriv_profile
#print axioms IsCollision.eventually_sheet_deriv_ne_zero
#print axioms IsCollision.sheet_pole_limit
end GaloisForLFunctions.GaloisTheoryOfZeros
