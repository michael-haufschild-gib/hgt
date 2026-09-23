import GaloisForLFunctions.RHTower.SlepianSincCommutation
import GaloisForLFunctions.RHTower.ProlateBandSymmetric

/-!
# Exterior Slepian transfer: moving the prolate action through the time–band integral

For an evaluation point `x` outside the band `[−1,1]` the sinc kernel slice `K_c(x,·)` is smooth
on a neighborhood of the band (its singular point `y = x` lies outside), so the local band
self-adjointness applies with `g = K_c(x,·)` and combines with the off-diagonal kernel
commutation `P_x K = P_y K` into the **exterior Slepian transfer**
(`slepian_exterior_transfer`):

`∫_{−1}^{1} K_c(x,y)·(P_c f)(y) dy = ∫_{−1}^{1} (P_c K_c(·,y))(x)·f(y) dy`.

The prolate action on the input of the time–band transform reappears as the prolate action on
the output variable of the kernel: the differential operator passes through the integral
operator.  This is the commutation mechanism in its integrated (exterior) form, obtained with
no differentiation under the integral sign.

Supporting layer: the explicit second derivative of the sinc profile
`g''(u) = (−c²u²·sin(cu) − 2(cu·cos(cu) − sin(cu)))/(πu³)` off the origin, and the global
translation identities for the second kernel slot.
-/

open Filter MeasureTheory

namespace RHTower

/-- Second derivative of the sinc profile off the origin. -/
noncomputable def sincScalarDD (c u : ℝ) : ℝ :=
  (-(c ^ (2 : ℕ)) * u ^ (2 : ℕ) * Real.sin (c * u) - 2 * (c * u * Real.cos (c * u) - Real.sin (c * u)))
    / (Real.pi * u ^ (3 : ℕ))

theorem hasDerivAt_sincScalarD {c u : ℝ} (h : u ≠ 0) :
    HasDerivAt (sincScalarD c) (sincScalarDD c u) u := by
  have hcu : HasDerivAt (fun v : ℝ => c * v) c u := by
    simpa using (hasDerivAt_id u).const_mul c
  have hcv : HasDerivAt (fun v : ℝ => c * v * Real.cos (c * v))
      (c * Real.cos (c * u) + c * u * (-Real.sin (c * u) * c)) u := hcu.mul hcu.cos
  have hnum : HasDerivAt (fun v : ℝ => c * v * Real.cos (c * v) - Real.sin (c * v))
      (c * Real.cos (c * u) + c * u * (-Real.sin (c * u) * c) - Real.cos (c * u) * c) u :=
    hcv.sub hcu.sin
  have hden : HasDerivAt (fun v : ℝ => Real.pi * v ^ (2 : ℕ)) (Real.pi * (2 * u)) u := by
    have h2 : HasDerivAt (fun v : ℝ => v ^ (2 : ℕ)) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    simpa using h2.const_mul Real.pi
  have hden0 : Real.pi * u ^ (2 : ℕ) ≠ 0 := mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 h)
  have hdiv := hnum.div hden hden0
  have hval : ((c * Real.cos (c * u) + c * u * (-Real.sin (c * u) * c) - Real.cos (c * u) * c)
          * (Real.pi * u ^ (2 : ℕ))
        - (c * u * Real.cos (c * u) - Real.sin (c * u)) * (Real.pi * (2 * u)))
        / (Real.pi * u ^ (2 : ℕ)) ^ (2 : ℕ) = sincScalarDD c u := by
    unfold sincScalarDD
    field_simp
    ring
  rw [hval] at hdiv
  exact hdiv

/-- On the punctured line the derivative of the sinc profile agrees with its closed formula in
a neighborhood. -/
theorem eventuallyEq_deriv_sincScalar {c u : ℝ} (h : u ≠ 0) :
    deriv (sincScalar c) =ᶠ[nhds u] sincScalarD c := by
  filter_upwards [isOpen_compl_singleton.mem_nhds
    (by simpa using h : u ∈ ({0}ᶜ : Set ℝ))] with v hv
  exact deriv_sincScalar (by simpa using hv)

theorem hasDerivAt_deriv_sincScalar {c u : ℝ} (h : u ≠ 0) :
    HasDerivAt (deriv (sincScalar c)) (sincScalarDD c u) u :=
  (hasDerivAt_sincScalarD h).congr_of_eventuallyEq (eventuallyEq_deriv_sincScalar h)

theorem deriv_deriv_sincScalar {c u : ℝ} (h : u ≠ 0) :
    deriv (deriv (sincScalar c)) u = sincScalarDD c u :=
  (hasDerivAt_deriv_sincScalar h).deriv

/-- Global translation identity for the second kernel slot. -/
theorem deriv_sincKernel_snd (c x : ℝ) :
    deriv (fun s => sincKernel c x s) = fun s => -deriv (sincScalar c) (x - s) :=
  funext fun s => deriv_comp_const_sub (sincScalar c) x s

/-- Global translation identity for the second derivative in the second kernel slot. -/
theorem deriv2_sincKernel_snd (c x s : ℝ) :
    deriv (deriv (fun s' => sincKernel c x s')) s = deriv (deriv (sincScalar c)) (x - s) := by
  rw [deriv_sincKernel_snd]
  have hneg : deriv (fun s' : ℝ => -deriv (sincScalar c) (x - s')) s
      = -deriv (fun s' : ℝ => deriv (sincScalar c) (x - s')) s := deriv.neg
  rw [hneg, deriv_comp_const_sub (deriv (sincScalar c)) x s, neg_neg]

theorem differentiableAt_sincKernel_snd {c x s : ℝ} (h : s ≠ x) :
    DifferentiableAt ℝ (fun s' => sincKernel c x s') s := by
  have hin : HasDerivAt (fun s' : ℝ => x - s') (-1 : ℝ) s := (hasDerivAt_id s).const_sub x
  have hu : x - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  exact ((hasDerivAt_sincScalar hu).comp s hin).differentiableAt

theorem differentiableAt_deriv_sincKernel_snd {c x s : ℝ} (h : s ≠ x) :
    DifferentiableAt ℝ (deriv (fun s' => sincKernel c x s')) s := by
  rw [deriv_sincKernel_snd]
  have hin : HasDerivAt (fun s' : ℝ => x - s') (-1 : ℝ) s := (hasDerivAt_id s).const_sub x
  have hu : x - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  exact (((hasDerivAt_deriv_sincScalar hu).comp s hin).neg).differentiableAt

theorem continuousOn_deriv2_sincKernel_snd (c x : ℝ) :
    ContinuousOn (deriv (deriv (fun s' => sincKernel c x s'))) ({x}ᶜ : Set ℝ) := by
  have hcont : ContinuousOn (fun s => sincScalarDD c (x - s)) ({x}ᶜ : Set ℝ) := by
    intro s hs
    have hu : x - s ≠ 0 := sub_ne_zero.mpr (Ne.symm (by simpa using hs))
    apply ContinuousAt.continuousWithinAt
    simp only [sincScalarDD]
    exact ContinuousAt.div (by fun_prop) (by fun_prop)
      (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 3 hu))
  refine hcont.congr fun s hs => ?_
  have hu : x - s ≠ 0 := sub_ne_zero.mpr (Ne.symm (by simpa using hs))
  rw [deriv2_sincKernel_snd, deriv_deriv_sincScalar hu]

/-- **Exterior Slepian transfer.**  For an evaluation point `x` outside the band, the prolate
action moves through the time–band integral: applied to the input function it reappears as the
prolate action on the kernel's outer variable.  Band self-adjointness (with the smooth-on-band
slice `K_c(x,·)`) supplies the transfer to the kernel's inner variable, and the off-diagonal
kernel commutation swaps it to the outer one. -/
theorem slepian_exterior_transfer {c x : ℝ} (hx : x ∉ Set.uIcc (-1 : ℝ) 1) {f : ℝ → ℝ}
    (hf1 : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hf2c : Continuous (deriv (deriv f))) :
    ∫ y in (-1 : ℝ)..1, sincKernel c x y * prolateSLAction c f y
      = ∫ y in (-1 : ℝ)..1, prolateSLAction c (fun t => sincKernel c t y) x * f y := by
  have hUI : Set.uIcc (-1 : ℝ) 1 ⊆ ({x}ᶜ : Set ℝ) :=
    fun y hy (h : y = x) => hx (h ▸ hy)
  have hsym := prolateSLAction_band_symmetric_on hUI
    (fun y _ => hf1 y) (fun y _ => hf2 y) hf2c.continuousOn
    (fun y hy => differentiableAt_sincKernel_snd hy)
    (fun y hy => differentiableAt_deriv_sincKernel_snd hy)
    (continuousOn_deriv2_sincKernel_snd c x) c
  calc ∫ y in (-1 : ℝ)..1, sincKernel c x y * prolateSLAction c f y
      = ∫ y in (-1 : ℝ)..1, f y * prolateSLAction c (fun s => sincKernel c x s) y := hsym
    _ = ∫ y in (-1 : ℝ)..1, prolateSLAction c (fun t => sincKernel c t y) x * f y := by
        refine intervalIntegral.integral_congr fun y hy => ?_
        have hxy : x ≠ y := by rintro rfl; exact hx hy
        rw [prolateSLAction_sincKernel hxy]
        ring

end RHTower
