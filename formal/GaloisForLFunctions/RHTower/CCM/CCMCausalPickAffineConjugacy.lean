import GaloisForLFunctions.RHTower.CCM.CCMEulerRayLoewner

/-!
# The causal Möbius quotient is the Euler-region restriction of the shifted-Xi Pick carrier

The affine embedding `j_omega (z) = i (1/2 + omega + z)` satisfies `-i j_omega (z) = 1/2 + omega + z`,
so it carries the causal half-plane onto the Euler-convergent region and turns the shifted-Xi
quotient into the causal quotient:

```text
Theta_omega (j_omega z) = Phi_omega z = Xi (1 + z)/Xi (1 + 2 omega + z),
i /(j_omega z - conj (j_omega v)) = 1/(1 + 2 omega + z + conj v).
```

The completed-zeta formula then makes the explicit scalar conjugacy `(5)` a pure algebraic
identity, and at `omega = 0` the whole Pick carrier degenerates to the zero kernel.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The affine embedding -/

/-- The affine embedding `(9)`. -/
def affineEmbed (ω : ℝ) (z : ℂ) : ℂ := Complex.I * (1 / 2 + (ω : ℂ) + z)

theorem neg_I_mul_affineEmbed (ω : ℝ) (z : ℂ) :
    -Complex.I * affineEmbed ω z = 1 / 2 + (ω : ℂ) + z := by
  unfold affineEmbed
  rw [← mul_assoc]
  have : -Complex.I * Complex.I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  rw [this, one_mul]

/-- The shifted-Xi quotient `(8)`. -/
def shiftedXiQuotient (Xi : ℂ → ℂ) (ω : ℝ) (w : ℂ) : ℂ :=
  Xi (1 / 2 - (ω : ℂ) - Complex.I * w) / Xi (1 / 2 + (ω : ℂ) - Complex.I * w)

/-- The causal quotient `(1)`. -/
def causalPhi (Xi : ℂ → ℂ) (ω : ℝ) (z : ℂ) : ℂ := Xi (1 + z) / Xi (1 + 2 * (ω : ℂ) + z)

/-- **Equation (11).**  The affine embedding identifies the two quotients. -/
theorem shiftedTheta_comp_affineEmbed (Xi : ℂ → ℂ) (ω : ℝ) (z : ℂ) :
    shiftedXiQuotient Xi ω (affineEmbed ω z) = causalPhi Xi ω z := by
  unfold shiftedXiQuotient causalPhi
  have hI : Complex.I * affineEmbed ω z = -(1 / 2 + (ω : ℂ) + z) := by
    have h := neg_I_mul_affineEmbed ω z
    have : Complex.I * affineEmbed ω z = -(-Complex.I * affineEmbed ω z) := by ring
    rw [this, h]
  rw [hI]
  congr 2 <;> ring

/-- **Equation (12).**  The pulled-back Cauchy denominator. -/
theorem affineEmbed_cauchy_denominator (ω : ℝ) (z v : ℂ) :
    Complex.I / (affineEmbed ω z - (starRingEnd ℂ) (affineEmbed ω v))
      = 1 / (1 + 2 * (ω : ℂ) + z + (starRingEnd ℂ) v) := by
  have hconj : (starRingEnd ℂ) (affineEmbed ω v)
      = -(Complex.I * (1 / 2 + (ω : ℂ) + (starRingEnd ℂ) v)) := by
    unfold affineEmbed
    simp [Complex.conj_I, map_add, Complex.conj_ofReal, map_ofNat]
  rw [hconj, sub_neg_eq_add]
  have hfac : affineEmbed ω z + Complex.I * (1 / 2 + (ω : ℂ) + (starRingEnd ℂ) v)
      = Complex.I * (1 + 2 * (ω : ℂ) + z + (starRingEnd ℂ) v) := by
    unfold affineEmbed
    ring
  rw [hfac]
  rw [mul_comm, div_mul_eq_div_div_swap]
  rw [div_self Complex.I_ne_zero]

/-- The pulled-back Pick kernel `(13)`. -/
def causalPickKernel (Xi : ℂ → ℂ) (ω : ℝ) (z v : ℂ) : ℂ :=
  (1 - causalPhi Xi ω z * (starRingEnd ℂ) (causalPhi Xi ω v))
    / (1 + 2 * (ω : ℂ) + z + (starRingEnd ℂ) v)

/-- **Equation (13).**  The Schur kernel pulled back by the affine embedding is the causal Pick
kernel. -/
theorem schur_pullback_eq_causalPickKernel (Xi : ℂ → ℂ) (ω : ℝ) (z v : ℂ) :
    Complex.I * (1 - shiftedXiQuotient Xi ω (affineEmbed ω z)
        * (starRingEnd ℂ) (shiftedXiQuotient Xi ω (affineEmbed ω v)))
        / (affineEmbed ω z - (starRingEnd ℂ) (affineEmbed ω v))
      = causalPickKernel Xi ω z v := by
  rw [shiftedTheta_comp_affineEmbed, shiftedTheta_comp_affineEmbed]
  unfold causalPickKernel
  have hsplit : Complex.I * (1 - causalPhi Xi ω z * (starRingEnd ℂ) (causalPhi Xi ω v))
      / (affineEmbed ω z - (starRingEnd ℂ) (affineEmbed ω v))
      = (1 - causalPhi Xi ω z * (starRingEnd ℂ) (causalPhi Xi ω v))
        * (Complex.I / (affineEmbed ω z - (starRingEnd ℂ) (affineEmbed ω v))) := by
    ring
  rw [hsplit, affineEmbed_cauchy_denominator]
  ring

/-! ## The explicit completed formula -/

/-- **Equation (7).**  The causal quotient in explicit archimedean and Euler factors. -/
theorem causalPhi_eq_explicit {Xi : ℂ → ℂ}
    (hXi : ∀ s : ℂ, Xi s = 1 / 2 * s * (s - 1) * ((Real.pi : ℝ) : ℂ) ^ (-s / 2)
      * Complex.Gamma (s / 2) * riemannZeta s)
    {ω : ℝ} {z : ℂ}
    (h1 : (1 : ℂ) + 2 * (ω : ℂ) + z ≠ 0) (h2 : 2 * (ω : ℂ) + z ≠ 0)
    (h3 : Complex.Gamma ((1 + 2 * (ω : ℂ) + z) / 2) ≠ 0)
    (h4 : riemannZeta (1 + 2 * (ω : ℂ) + z) ≠ 0) :
    causalPhi Xi ω z
      = ((Real.pi : ℝ) : ℂ) ^ (ω : ℂ) * (((1 + z) * z) / ((1 + 2 * (ω : ℂ) + z) * (2 * (ω : ℂ) + z)))
        * (Complex.Gamma ((1 + z) / 2) / Complex.Gamma ((1 + 2 * (ω : ℂ) + z) / 2))
        * (riemannZeta (1 + z) / riemannZeta (1 + 2 * (ω : ℂ) + z)) := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcpow : ((Real.pi : ℝ) : ℂ) ^ (-(1 + z) / 2)
      = ((Real.pi : ℝ) : ℂ) ^ (ω : ℂ)
        * ((Real.pi : ℝ) : ℂ) ^ (-(1 + 2 * (ω : ℂ) + z) / 2) := by
    rw [← Complex.cpow_add _ _ hpi]
    congr 1
    ring
  have hpipos : ((Real.pi : ℝ) : ℂ) ^ (-(1 + 2 * (ω : ℂ) + z) / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpi]
    exact Complex.exp_ne_zero _
  have h2' : z + (ω : ℂ) * 2 ≠ 0 := by
    intro hc
    exact h2 (by linear_combination hc)
  have h1' : (1 : ℂ) + z + (ω : ℂ) * 2 ≠ 0 := by
    intro hc
    exact h1 (by linear_combination hc)
  have hcommon : (1 : ℂ) / 2 * ((Real.pi : ℝ) : ℂ) ^ (-(1 + 2 * (ω : ℂ) + z) / 2) ≠ 0 := by
    refine mul_ne_zero ?_ hpipos
    norm_num
  unfold causalPhi
  rw [hXi (1 + z), hXi (1 + 2 * (ω : ℂ) + z)]
  have hnum : (1 : ℂ) / 2 * (1 + z) * (1 + z - 1) * ((Real.pi : ℝ) : ℂ) ^ (-(1 + z) / 2)
        * Complex.Gamma ((1 + z) / 2) * riemannZeta (1 + z)
      = (((Real.pi : ℝ) : ℂ) ^ (ω : ℂ) * ((1 + z) * z) * Complex.Gamma ((1 + z) / 2)
          * riemannZeta (1 + z))
        * ((1 : ℂ) / 2 * ((Real.pi : ℝ) : ℂ) ^ (-(1 + 2 * (ω : ℂ) + z) / 2)) := by
    rw [hcpow]
    ring
  have hden : (1 : ℂ) / 2 * (1 + 2 * (ω : ℂ) + z) * (1 + 2 * (ω : ℂ) + z - 1)
        * ((Real.pi : ℝ) : ℂ) ^ (-(1 + 2 * (ω : ℂ) + z) / 2)
        * Complex.Gamma ((1 + 2 * (ω : ℂ) + z) / 2) * riemannZeta (1 + 2 * (ω : ℂ) + z)
      = (((1 + 2 * (ω : ℂ) + z) * (2 * (ω : ℂ) + z))
          * Complex.Gamma ((1 + 2 * (ω : ℂ) + z) / 2) * riemannZeta (1 + 2 * (ω : ℂ) + z))
        * ((1 : ℂ) / 2 * ((Real.pi : ℝ) : ℂ) ^ (-(1 + 2 * (ω : ℂ) + z) / 2)) := by
    ring
  rw [hnum, hden, mul_div_mul_right _ _ hcommon]
  field_simp

/-- The explicit scalar conjugacy factor `(3)`. -/
def conjugacyScalar (ω : ℝ) (z : ℂ) : ℂ :=
  ((Real.pi : ℝ) : ℂ) ^ (-(ω : ℂ)) * (Complex.Gamma ((1 + 2 * (ω : ℂ) + z) / 2)
      / Complex.Gamma ((1 + z) / 2))
    * (((1 + 2 * (ω : ℂ) + z) * (2 * (ω : ℂ) + z)) / ((1 + z) * z * (1 + (ω : ℂ) + z)))

/-- **Equation (5).**  The scalar conjugacy turns the causal quotient into the first term of the
signed-Möbius causal transform. -/
theorem conjugacyScalar_mul_causalPhi {Xi : ℂ → ℂ}
    (hXi : ∀ s : ℂ, Xi s = 1 / 2 * s * (s - 1) * ((Real.pi : ℝ) : ℂ) ^ (-s / 2)
      * Complex.Gamma (s / 2) * riemannZeta s)
    {ω : ℝ} {z : ℂ}
    (h1 : (1 : ℂ) + 2 * (ω : ℂ) + z ≠ 0) (h2 : 2 * (ω : ℂ) + z ≠ 0)
    (h3 : Complex.Gamma ((1 + 2 * (ω : ℂ) + z) / 2) ≠ 0)
    (h4 : riemannZeta (1 + 2 * (ω : ℂ) + z) ≠ 0)
    (h5 : (1 : ℂ) + z ≠ 0) (h6 : z ≠ 0) (h7 : (1 : ℂ) + (ω : ℂ) + z ≠ 0)
    (h8 : Complex.Gamma ((1 + z) / 2) ≠ 0) :
    conjugacyScalar ω z * causalPhi Xi ω z
      = riemannZeta (1 + z) / ((1 + (ω : ℂ) + z) * riemannZeta (1 + 2 * (ω : ℂ) + z)) := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hP : ((Real.pi : ℝ) : ℂ) ^ (ω : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpi]
    exact Complex.exp_ne_zero _
  rw [causalPhi_eq_explicit hXi h1 h2 h3 h4, conjugacyScalar, Complex.cpow_neg]
  field_simp

/-! ## The critical degeneration -/

/-- **Equation (20).**  At the critical shift the causal quotient is constant. -/
theorem causalPhi_zero_shift {Xi : ℂ → ℂ} {z : ℂ} (h : Xi (1 + z) ≠ 0) :
    causalPhi Xi 0 z = 1 := by
  unfold causalPhi
  norm_num
  exact h

/-- **Equation (20).**  Hence the whole Pick carrier degenerates to the zero kernel. -/
theorem causalPickKernel_zero_shift {Xi : ℂ → ℂ} {z v : ℂ}
    (hz : Xi (1 + z) ≠ 0) (hv : Xi (1 + v) ≠ 0) :
    causalPickKernel Xi 0 z v = 0 := by
  unfold causalPickKernel
  rw [causalPhi_zero_shift hz, causalPhi_zero_shift hv]
  simp

/-- **Equation (20).**  The scalar conjugacy factor degenerates to the Cauchy factor. -/
theorem conjugacyScalar_zero_shift {z : ℂ} (h5 : (1 : ℂ) + z ≠ 0) (h6 : z ≠ 0)
    (h8 : Complex.Gamma ((1 + z) / 2) ≠ 0) :
    conjugacyScalar 0 z = 1 / (1 + z) := by
  unfold conjugacyScalar
  norm_num
  field_simp

end GaloisForLFunctions.RHTower

end
