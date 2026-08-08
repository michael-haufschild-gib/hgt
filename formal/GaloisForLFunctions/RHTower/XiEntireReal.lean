/-
The completed Riemann ξ, rotated to the critical line as an entire function of a single
variable: `ΞC z := ξ(½ + z·i)`.  On the real axis this is real-valued and agrees with the
detector function `Ξ` of the Laguerre theory; as a function of the complex variable `z` it is
entire, even, and of growth order at most one.  These are the structural facts a Hadamard
factorization of `Ξ` consumes: entire + order ≤ 1 feeds the canonical-product / exponential-type
argument, and evenness (from the functional equation `ξ(1−s)=ξ(s)`) forces the linear term of the
Hadamard exponential to vanish, so the factorization is a pure product over the zeros.
-/
import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.LaguerreInequality
import GaloisForLFunctions.RHTower.CompletedZetaGrowth

open Complex

namespace RHTower

/-- The critical-line rotation of the completed ξ as an entire function of one variable:
`ΞC z = ξ(½ + z·i)`.  The affine substitution `s = ½ + z·i` maps the real `z`-axis onto the
critical line `Re s = ½` and rotates the functional-equation reflection `s ↦ 1 − s` into
`z ↦ −z`. -/
noncomputable def XiC (z : ℂ) : ℂ := xi (1 / 2 + z * Complex.I)

/-- **Schwarz reality in the centered coordinate.**  `ΞC(conj z) = conj (ΞC z)`, from the
functional equation and the Schwarz reflection of `ξ`. -/
theorem XiC_conj (z : ℂ) :
    XiC ((starRingEnd ℂ) z) = (starRingEnd ℂ) (XiC z) := by
  rw [XiC, XiC]
  have harg : 1 / 2 + (starRingEnd ℂ) z * Complex.I =
      1 - (starRingEnd ℂ) (1 / 2 + z * Complex.I) := by
    apply Complex.ext
    · simp
      ring
    · simp
  rw [harg, xi_one_sub, xi_conj]

/-- `ΞC` is entire: it is `ξ` precomposed with the affine (hence entire) map `z ↦ ½ + z·i`. -/
theorem XiC_differentiable : Differentiable ℂ XiC := by
  have haff : Differentiable ℂ (fun z : ℂ => 1 / 2 + z * Complex.I) := by fun_prop
  exact xi_differentiable.comp haff

/-- **`ΞC` is even.**  `ΞC(−z) = ξ(½ − z·i) = ξ(1 − (½ + z·i)) = ξ(½ + z·i) = ΞC z`, the middle
step being the functional equation `ξ(1 − s) = ξ(s)`. -/
theorem XiC_even (z : ℂ) : XiC (-z) = XiC z := by
  have hrw : (1 : ℂ) / 2 + (-z) * Complex.I = 1 - (1 / 2 + z * Complex.I) := by ring
  rw [XiC, hrw, xi_one_sub, XiC]

/-- **`ΞC` restricts to `Ξ` on the real axis.**  For real `t`, `ΞC t = ξ(½ + t·i)`, which is real
and equals the detector value `Ξ t` (`xiHalfLine_real`). -/
theorem XiC_ofReal (t : ℝ) : XiC (t : ℂ) = (Xi t : ℂ) := by
  rw [XiC]; exact xiHalfLine_real t

/-- **`ΞC` has growth order at most one.**  There is `C > 0` with
`‖ΞC z‖ ≤ exp (C · (1 + ‖z‖) · log (2 + ‖z‖))` for all `z`.  Immediate from the unconditional
order-one envelope for `ξ` (`xi_growth_order_le_one`) together with `‖½ + z·i‖ ≤ 1 + ‖z‖` and the
monotonicity estimates `1 + ‖s‖ ≤ 2(1 + ‖z‖)` and `log(2 + ‖s‖) ≤ 2 log(2 + ‖z‖)`. -/
theorem XiC_order :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖XiC z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  obtain ⟨C₀, hC₀, hgrow⟩ := xi_growth_order_le_one
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro z
  set a : ℝ := ‖z‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg z
  -- The argument norm is controlled by `1 + ‖z‖`.
  have hsnorm : ‖(1 : ℂ) / 2 + z * Complex.I‖ ≤ 1 + a := by
    have htri : ‖(1 : ℂ) / 2 + z * Complex.I‖ ≤ ‖(1 : ℂ) / 2‖ + ‖z * Complex.I‖ :=
      norm_add_le _ _
    have h12 : ‖(1 : ℂ) / 2‖ = 1 / 2 := by
      rw [norm_div, norm_one, Complex.norm_ofNat]
    have hzI : ‖z * Complex.I‖ = a := by rw [norm_mul, Complex.norm_I, mul_one, ha]
    rw [h12, hzI] at htri; linarith
  set s : ℂ := 1 / 2 + z * Complex.I with hs
  have hsnn : 0 ≤ ‖s‖ := norm_nonneg s
  -- Envelope monotonicity in the argument norm.
  have hfac1 : 1 + ‖s‖ ≤ 2 * (1 + a) := by rw [hs] at hsnorm ⊢; linarith
  have hlog_s : Real.log (2 + ‖s‖) ≤ 2 * Real.log (2 + a) := by
    have hmono : Real.log (2 + ‖s‖) ≤ Real.log (3 + a) := by
      apply Real.log_le_log (by linarith)
      rw [hs] at hsnorm ⊢; linarith
    have hsq : Real.log (3 + a) ≤ 2 * Real.log (2 + a) := by
      have hpow : Real.log ((2 + a) ^ 2) = 2 * Real.log (2 + a) := by
        rw [Real.log_pow]; push_cast; ring
      rw [← hpow]
      apply Real.log_le_log (by linarith)
      nlinarith [ha0]
    linarith
  have hlog2a_nn : 0 ≤ Real.log (2 + a) := Real.log_nonneg (by linarith)
  have hlogs_nn : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith)
  -- Assemble the exponent bound.
  have hexp : C₀ * (1 + ‖s‖) * Real.log (2 + ‖s‖) ≤ 4 * C₀ * (1 + a) * Real.log (2 + a) := by
    have hprod : (1 + ‖s‖) * Real.log (2 + ‖s‖) ≤ 2 * (1 + a) * (2 * Real.log (2 + a)) :=
      mul_le_mul hfac1 hlog_s hlogs_nn (by linarith)
    nlinarith [hprod, hC₀, hlog2a_nn, ha0]
  calc ‖XiC z‖ = ‖xi s‖ := by rw [XiC, hs]
    _ ≤ Real.exp (C₀ * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := hgrow s
    _ ≤ Real.exp (4 * C₀ * (1 + a) * Real.log (2 + a)) := Real.exp_le_exp.mpr hexp

end RHTower
