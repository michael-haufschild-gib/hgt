import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# The completed packet connection and its normal derivative

The Suzuki shift applied to the completed xi gives the completed packet connection
`Θ_α(z) = Ξ(z - α) / Ξ(z + α)`.  Its normal derivative at the unshifted point is exactly minus twice
the logarithmic derivative of the completed xi:

```text
∂_α Θ_α(z)|_(α = 0) = -2 Ξ'(z) / Ξ(z) ,
```

wherever the completed xi does not vanish.  This is the completed counterpart of the prime-power
identity `∂_α ζ(s-α)/ζ(s+α)|_0 = -2 ζ'(s)/ζ(s)`: the same normal differentiation before any
specialization of the shift, now carried out after Gamma completion.
-/

open Complex

namespace RHTower

noncomputable section

/-- The completed packet connection: the Suzuki shift applied to the completed xi. -/
def completedSuzukiPacket (a : ℝ) (z : ℂ) : ℂ := XiC (z - (a : ℂ)) / XiC (z + (a : ℂ))

theorem completedSuzukiPacket_zero (z : ℂ) (hz : XiC z ≠ 0) :
    completedSuzukiPacket 0 z = 1 := by
  simp [completedSuzukiPacket, div_self hz]

/-- **`(23)`: the normal derivative of the completed packet connection.**  Off the completed
divisor, differentiating the completed packet in the shift returns minus twice the logarithmic
derivative of the completed xi. -/
theorem hasDerivAt_completedSuzukiPacket {z : ℂ} (hz : XiC z ≠ 0) :
    HasDerivAt (fun a : ℝ => completedSuzukiPacket a z) (-2 * logDeriv XiC z) 0 := by
  have hXi : HasDerivAt XiC (deriv XiC z) z := (XiC_differentiable z).hasDerivAt
  have hlin1 : HasDerivAt (fun a : ℝ => z - (a : ℂ)) (-1) 0 := by
    have h : HasDerivAt (fun a : ℝ => ((a : ℝ) : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
    simpa using h.const_sub z
  have hlin2 : HasDerivAt (fun a : ℝ => z + (a : ℂ)) 1 0 := by
    have h : HasDerivAt (fun a : ℝ => ((a : ℝ) : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
    simpa using h.const_add z
  have hnum : HasDerivAt (fun a : ℝ => XiC (z - (a : ℂ))) (-deriv XiC z) 0 := by
    have hXi' : HasDerivAt XiC (deriv XiC (z - ((0 : ℝ) : ℂ))) (z - ((0 : ℝ) : ℂ)) := by
      have h0 : z - ((0 : ℝ) : ℂ) = z := by push_cast; ring
      rw [h0]
      exact hXi
    have h := HasDerivAt.scomp (h := fun a : ℝ => z - (a : ℂ)) 0 hXi' hlin1
    have h0 : z - ((0 : ℝ) : ℂ) = z := by push_cast; ring
    simpa [Function.comp, smul_eq_mul, h0] using! h
  have hden : HasDerivAt (fun a : ℝ => XiC (z + (a : ℂ))) (deriv XiC z) 0 := by
    have hXi' : HasDerivAt XiC (deriv XiC (z + ((0 : ℝ) : ℂ))) (z + ((0 : ℝ) : ℂ)) := by
      have h0 : z + ((0 : ℝ) : ℂ) = z := by push_cast; ring
      rw [h0]
      exact hXi
    have h := HasDerivAt.scomp (h := fun a : ℝ => z + (a : ℂ)) 0 hXi' hlin2
    have h0 : z + ((0 : ℝ) : ℂ) = z := by push_cast; ring
    simpa [Function.comp, smul_eq_mul, h0] using! h
  have hzero : XiC (z + ((0 : ℝ) : ℂ)) ≠ 0 := by
    have h0 : z + ((0 : ℝ) : ℂ) = z := by push_cast; ring
    rw [h0]
    exact hz
  have h := hnum.div hden hzero
  have h0 : z + ((0 : ℝ) : ℂ) = z := by push_cast; ring
  have h0' : z - ((0 : ℝ) : ℂ) = z := by push_cast; ring
  rw [h0, h0'] at h
  have hvalue : (-deriv XiC z * XiC z - XiC z * deriv XiC z) / XiC z ^ 2
      = -2 * logDeriv XiC z := by
    rw [logDeriv_apply]
    field_simp
    ring
  rw [hvalue] at h
  exact h

/-- The normal derivative in the form the fixed-current weld uses: the completed source is minus
twice the completed logarithmic current. -/
theorem deriv_completedSuzukiPacket {z : ℂ} (hz : XiC z ≠ 0) :
    deriv (fun a : ℝ => completedSuzukiPacket a z) 0 = -2 * logDeriv XiC z :=
  (hasDerivAt_completedSuzukiPacket hz).deriv

/-! ### The archimedean factor and the prime-power leg -/

/-- The archimedean completion factor of `ξ`: the polynomial prefactor times `Γ_ℝ`. -/
def archimedeanXiFactor (s : ℂ) : ℂ := s * (s - 1) / 2 * Complex.Gammaℝ s

/-- **`ξ` is its archimedean factor times `ζ`**, wherever the archimedean factor is nonzero.  The
hypothesis is not cosmetic: at the trivial-zero points `Γ_ℝ` vanishes in mathlib's convention and
the identity genuinely fails there. -/
theorem xi_eq_archimedean_mul_zeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hΓ : Complex.Gammaℝ s ≠ 0) :
    xi s = archimedeanXiFactor s * riemannZeta s := by
  have hz := riemannZeta_def_of_ne_zero h0
  have hcompleted : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    rw [hz]
    field_simp
  rw [xi_eq_half_mul h0 h1, hcompleted, archimedeanXiFactor]
  ring

/-- On the critical rotation the base point is neither `0` nor `1`. -/
theorem criticalPoint_ne_zero (w : ℝ) : (1 / 2 + (w : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have hre : ((1 : ℂ) / 2 + (w : ℂ) * Complex.I).re = 0 := by rw [h]; simp
  simp at hre

theorem criticalPoint_ne_one (w : ℝ) : (1 / 2 + (w : ℂ) * Complex.I) ≠ 1 := by
  intro h
  have hre : ((1 : ℂ) / 2 + (w : ℂ) * Complex.I).re = 1 := by rw [h]; simp
  simp at hre

/-- On the critical rotation the archimedean factor does not vanish. -/
theorem criticalPoint_Gammaℝ_ne_zero (w : ℝ) :
    Complex.Gammaℝ (1 / 2 + (w : ℂ) * Complex.I) ≠ 0 := by
  refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
  simp

/-- **The completed packet is the archimedean factor ratio times the prime-power leg.**  This is the
precise sense in which the packet Dirichlet series `(7)` is the uncompleted leg of the completed
source `(23)`: on the critical rotation the two differ exactly by the ratio of archimedean
factors. -/
theorem completedSuzukiPacket_eq_archimedean_mul_zeta (a z : ℝ) :
    completedSuzukiPacket a (z : ℂ)
      = (archimedeanXiFactor (1 / 2 + ((z : ℂ) - (a : ℂ)) * Complex.I) *
            riemannZeta (1 / 2 + ((z : ℂ) - (a : ℂ)) * Complex.I))
        / (archimedeanXiFactor (1 / 2 + ((z : ℂ) + (a : ℂ)) * Complex.I) *
            riemannZeta (1 / 2 + ((z : ℂ) + (a : ℂ)) * Complex.I)) := by
  have hminus : ((z : ℂ) - (a : ℂ)) = ((z - a : ℝ) : ℂ) := by push_cast; ring
  have hplus : ((z : ℂ) + (a : ℂ)) = ((z + a : ℝ) : ℂ) := by push_cast; ring
  rw [completedSuzukiPacket, XiC, XiC, hminus, hplus,
    xi_eq_archimedean_mul_zeta (criticalPoint_ne_zero (z - a)) (criticalPoint_ne_one (z - a))
      (criticalPoint_Gammaℝ_ne_zero (z - a)),
    xi_eq_archimedean_mul_zeta (criticalPoint_ne_zero (z + a)) (criticalPoint_ne_one (z + a))
      (criticalPoint_Gammaℝ_ne_zero (z + a))]

end

end RHTower
