import GaloisForLFunctions.HTGeometry.IntegrableDerivLimit
import GaloisForLFunctions.RHTower.RadialInteractionBound

/-!
# Radial interaction terminal-amplitude universality

The exact interaction-picture transport laws and the generic integrable-derivative limit mechanism
close a gap left between the Riemann-tower and hypertranscendental-geometry libraries.

For a bounded solution of

```text
W'' + c² W = ψ W
```

on a ray, with `c ≠ 0` and integrable `ψ`, both transported amplitudes have integrable derivative.
Consequently each amplitude converges to its exact initial value plus total transport.  The same
proof retains an endpoint-uniform, phase-free displacement bound and the exact finite-point
reconstruction of `W`.
-/

open MeasureTheory Filter Set
open Complex

noncomputable section

namespace RHTower

/-- The positive-frequency transport source is integrable when the potential is integrable and the
solution is bounded on the ray. -/
theorem integrableOn_radialInteractionPlusTransport
    {c a B : ℝ} (hc : c ≠ 0) {W V psi : ℝ → ℂ}
    (hW : ∀ x ∈ Ici a, HasDerivAt W (V x) x)
    (hWbound : ∀ x ∈ Ici a, ‖W x‖ ≤ B)
    (hpsi : IntegrableOn psi (Ioi a) volume) :
    IntegrableOn
      (fun x : ℝ =>
        Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
          (2 * Complex.I * (c : ℂ)))
      (Ioi a) volume := by
  have hcabs : 0 < |c| := abs_pos.mpr hc
  have hWcont : ContinuousOn W (Ioi a) := by
    intro x hx
    exact (hW x (mem_Ici.mpr (mem_Ioi.mp hx).le)).continuousAt.continuousWithinAt
  have hfacCont : ContinuousOn
      (fun x : ℝ =>
        Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * W x /
          (2 * Complex.I * (c : ℂ)))
      (Ioi a) := by
    apply ContinuousOn.div_const
    exact (by
      fun_prop : Continuous
        (fun x : ℝ => Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)))).continuousOn.mul hWcont
  have hfacBound :
      ∀ᵐ x : ℝ ∂(volume.restrict (Ioi a)),
        ‖Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * W x /
          (2 * Complex.I * (c : ℂ))‖ ≤ B / (2 * |c|) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_div, norm_mul, norm_exp_neg_I_mul_ofReal, one_mul]
    rw [norm_mul, norm_mul]
    simp only [norm_ofNat, Complex.norm_I, mul_one, norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right
      (hWbound x (mem_Ici.mpr (mem_Ioi.mp hx).le)) (by positivity)
  have hraw :=
    hpsi.bdd_mul (hfacCont.aestronglyMeasurable measurableSet_Ioi) hfacBound
  have heq :
      (fun x : ℝ =>
          (Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * W x /
            (2 * Complex.I * (c : ℂ))) * psi x) =
        (fun x : ℝ =>
          Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
            (2 * Complex.I * (c : ℂ))) := by
    funext x
    ring
  rw [← heq]
  exact hraw

/-- The negative-frequency transport source is integrable under the same hypotheses. -/
theorem integrableOn_radialInteractionMinusTransport
    {c a B : ℝ} (hc : c ≠ 0) {W V psi : ℝ → ℂ}
    (hW : ∀ x ∈ Ici a, HasDerivAt W (V x) x)
    (hWbound : ∀ x ∈ Ici a, ‖W x‖ ≤ B)
    (hpsi : IntegrableOn psi (Ioi a) volume) :
    IntegrableOn
      (fun x : ℝ =>
        -Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
          (2 * Complex.I * (c : ℂ)))
      (Ioi a) volume := by
  have hcabs : 0 < |c| := abs_pos.mpr hc
  have hWcont : ContinuousOn W (Ioi a) := by
    intro x hx
    exact (hW x (mem_Ici.mpr (mem_Ioi.mp hx).le)).continuousAt.continuousWithinAt
  have hfacCont : ContinuousOn
      (fun x : ℝ =>
        -Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * W x /
          (2 * Complex.I * (c : ℂ)))
      (Ioi a) := by
    apply ContinuousOn.div_const
    exact (by
      fun_prop : Continuous
        (fun x : ℝ => -Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)))).continuousOn.mul hWcont
  have hfacBound :
      ∀ᵐ x : ℝ ∂(volume.restrict (Ioi a)),
        ‖-Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * W x /
          (2 * Complex.I * (c : ℂ))‖ ≤ B / (2 * |c|) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_div, norm_mul, norm_neg, norm_exp_I_mul_ofReal, one_mul]
    rw [norm_mul, norm_mul]
    simp only [norm_ofNat, Complex.norm_I, mul_one, norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right
      (hWbound x (mem_Ici.mpr (mem_Ioi.mp hx).le)) (by positivity)
  have hraw :=
    hpsi.bdd_mul (hfacCont.aestronglyMeasurable measurableSet_Ioi) hfacBound
  have heq :
      (fun x : ℝ =>
          (-Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * W x /
            (2 * Complex.I * (c : ℂ))) * psi x) =
        (fun x : ℝ =>
          -Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
            (2 * Complex.I * (c : ℂ))) := by
    funext x
    ring
  rw [← heq]
  exact hraw

/-- Uniform phase-free displacement bound for the positive-frequency amplitude. -/
theorem norm_radialInteractionPlus_sub_le_totalTransport
    {c a B b : ℝ} (hc : c ≠ 0) (hab : a ≤ b) {W V psi : ℝ → ℂ}
    (hW : ∀ x ∈ Ici a, HasDerivAt W (V x) x)
    (hV : ∀ x ∈ Ici a,
      HasDerivAt V ((psi x - (c : ℂ) ^ 2) * W x) x)
    (hWbound : ∀ x ∈ Ici a, ‖W x‖ ≤ B)
    (hpsi : IntegrableOn psi (Ioi a) volume) :
    ‖radialInteractionPlus c W V b - radialInteractionPlus c W V a‖ ≤
      ∫ x in Ioi a, ‖psi x‖ * (B / (2 * |c|)) := by
  have hsource := integrableOn_radialInteractionPlusTransport hc hW hWbound hpsi
  have hderiv : ∀ x ∈ Ici a, HasDerivAt (radialInteractionPlus c W V)
      (Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
        (2 * Complex.I * (c : ℂ))) x := by
    intro x hx
    exact hasDerivAt_radialInteractionPlus hc (hW x hx) (hV x hx)
  calc
    ‖radialInteractionPlus c W V b - radialInteractionPlus c W V a‖
        ≤ ∫ x in Ioi a,
            ‖Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
              (2 * Complex.I * (c : ℂ))‖ :=
      GaloisForLFunctions.norm_sub_le_integral_norm_of_hasDerivAt hab hderiv hsource
    _ ≤ ∫ x in Ioi a, ‖psi x‖ * (B / (2 * |c|)) := by
      apply integral_mono_ae hsource.norm (hpsi.norm.mul_const (B / (2 * |c|)))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_deriv_radialInteractionPlus]
      exact div_le_iff₀ (by positivity : 0 < 2 * |c|) |>.mpr (by
        calc
          ‖psi x‖ * ‖W x‖
              ≤ ‖psi x‖ * B :=
            mul_le_mul_of_nonneg_left
              (hWbound x (mem_Ici.mpr (mem_Ioi.mp hx).le)) (norm_nonneg _)
          _ = ‖psi x‖ * (B / (2 * |c|)) * (2 * |c|) := by field_simp)

/-- Uniform phase-free displacement bound for the negative-frequency amplitude. -/
theorem norm_radialInteractionMinus_sub_le_totalTransport
    {c a B b : ℝ} (hc : c ≠ 0) (hab : a ≤ b) {W V psi : ℝ → ℂ}
    (hW : ∀ x ∈ Ici a, HasDerivAt W (V x) x)
    (hV : ∀ x ∈ Ici a,
      HasDerivAt V ((psi x - (c : ℂ) ^ 2) * W x) x)
    (hWbound : ∀ x ∈ Ici a, ‖W x‖ ≤ B)
    (hpsi : IntegrableOn psi (Ioi a) volume) :
    ‖radialInteractionMinus c W V b - radialInteractionMinus c W V a‖ ≤
      ∫ x in Ioi a, ‖psi x‖ * (B / (2 * |c|)) := by
  have hsource := integrableOn_radialInteractionMinusTransport hc hW hWbound hpsi
  have hderiv : ∀ x ∈ Ici a, HasDerivAt (radialInteractionMinus c W V)
      (-Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
        (2 * Complex.I * (c : ℂ))) x := by
    intro x hx
    exact hasDerivAt_radialInteractionMinus hc (hW x hx) (hV x hx)
  calc
    ‖radialInteractionMinus c W V b - radialInteractionMinus c W V a‖
        ≤ ∫ x in Ioi a,
            ‖-Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
              (2 * Complex.I * (c : ℂ))‖ :=
      GaloisForLFunctions.norm_sub_le_integral_norm_of_hasDerivAt hab hderiv hsource
    _ ≤ ∫ x in Ioi a, ‖psi x‖ * (B / (2 * |c|)) := by
      apply integral_mono_ae hsource.norm (hpsi.norm.mul_const (B / (2 * |c|)))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_deriv_radialInteractionMinus]
      exact div_le_iff₀ (by positivity : 0 < 2 * |c|) |>.mpr (by
        calc
          ‖psi x‖ * ‖W x‖
              ≤ ‖psi x‖ * B :=
            mul_le_mul_of_nonneg_left
              (hWbound x (mem_Ici.mpr (mem_Ioi.mp hx).le)) (norm_nonneg _)
          _ = ‖psi x‖ * (B / (2 * |c|)) * (2 * |c|) := by field_simp)

/-- **Radial interaction terminal-amplitude universality.**

A bounded solution of the perturbed oscillator equation on a ray has exact terminal positive- and
negative-frequency amplitudes whenever the perturbing potential is integrable.  The result packages
finite-point reconstruction, both explicit terminal values, and uniform phase-free displacement
bounds. -/
theorem radialInteractionTerminalAmplitudeUniversality
    {c a B : ℝ} (hc : c ≠ 0) {W V psi : ℝ → ℂ}
    (hW : ∀ x ∈ Ici a, HasDerivAt W (V x) x)
    (hV : ∀ x ∈ Ici a,
      HasDerivAt V ((psi x - (c : ℂ) ^ 2) * W x) x)
    (hWbound : ∀ x ∈ Ici a, ‖W x‖ ≤ B)
    (hpsi : IntegrableOn psi (Ioi a) volume) :
    (∀ x : ℝ,
      radialInteractionPlus c W V x *
          Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) +
        radialInteractionMinus c W V x *
          Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) = W x) ∧
    Tendsto (radialInteractionPlus c W V) atTop
      (nhds
        (radialInteractionPlus c W V a +
          ∫ x in Ioi a,
            Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
              (2 * Complex.I * (c : ℂ)))) ∧
    Tendsto (radialInteractionMinus c W V) atTop
      (nhds
        (radialInteractionMinus c W V a +
          ∫ x in Ioi a,
            -Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
              (2 * Complex.I * (c : ℂ)))) ∧
    ∀ b : ℝ, a ≤ b →
      ‖radialInteractionPlus c W V b - radialInteractionPlus c W V a‖ ≤
          ∫ x in Ioi a, ‖psi x‖ * (B / (2 * |c|)) ∧
        ‖radialInteractionMinus c W V b - radialInteractionMinus c W V a‖ ≤
          ∫ x in Ioi a, ‖psi x‖ * (B / (2 * |c|)) := by
  have hplusSource := integrableOn_radialInteractionPlusTransport hc hW hWbound hpsi
  have hminusSource := integrableOn_radialInteractionMinusTransport hc hW hWbound hpsi
  have hplusDeriv : ∀ x ∈ Ici a, HasDerivAt (radialInteractionPlus c W V)
      (Complex.exp (-Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
        (2 * Complex.I * (c : ℂ))) x := by
    intro x hx
    exact hasDerivAt_radialInteractionPlus hc (hW x hx) (hV x hx)
  have hminusDeriv : ∀ x ∈ Ici a, HasDerivAt (radialInteractionMinus c W V)
      (-Complex.exp (Complex.I * (c : ℂ) * (x : ℂ)) * psi x * W x /
        (2 * Complex.I * (c : ℂ))) x := by
    intro x hx
    exact hasDerivAt_radialInteractionMinus hc (hW x hx) (hV x hx)
  refine ⟨fun x => radialInteraction_reconstruct hc W V, ?_, ?_, ?_⟩
  · exact GaloisForLFunctions.tendsto_of_hasDerivAt_of_integrableOn_Ioi
      hplusDeriv hplusSource
  · exact GaloisForLFunctions.tendsto_of_hasDerivAt_of_integrableOn_Ioi
      hminusDeriv hminusSource
  · intro b hab
    exact
      ⟨norm_radialInteractionPlus_sub_le_totalTransport hc hab hW hV hWbound hpsi,
        norm_radialInteractionMinus_sub_le_totalTransport hc hab hW hV hWbound hpsi⟩

end RHTower
