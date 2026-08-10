import Mathlib
import GaloisForLFunctions.HTGeometry.QGammaAnalytic

/-!
# The q-digamma function and its shift law

`ψ_q = Γ_q'/Γ_q` on the right half-plane, with the differentiated form of Jackson's translation
law: every jet of `ψ_q` picks up exactly the corresponding jet of the logarithmic derivative of
the multiplier `(1 − qᶻ)/(1 − q)`.  This is the q-analogue of the digamma recurrence
`ψ⁽ʲ⁾(z+1) = ψ⁽ʲ⁾(z) + (−1)ʲ j!/z^{j+1}` which drives Hölder's theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Filter Topology

noncomputable section

theorem analyticOnNhd_qGammaOn (q : RealEulerNome) :
    AnalyticOnNhd ℂ (qGammaOn q) qHalfPlane :=
  (differentiableOn_qGammaOn q).analyticOnNhd isOpen_qHalfPlane

theorem qcpow_ne_one (q : RealEulerNome) {z : ℂ} (hz : z ∈ qHalfPlane) :
    (1 : ℂ) - (q.val : ℂ) ^ z ≠ 0 := by
  intro h0
  have hnorm : ‖(q.val : ℂ) ^ z‖ = q.val ^ z.re := norm_qcpow q z
  have hone : (q.val : ℂ) ^ z = 1 := by linear_combination -h0
  rw [hone, norm_one] at hnorm
  have hlt : q.val ^ z.re < 1 := Real.rpow_lt_one q.pos.le q.lt_one hz
  rw [← hnorm] at hlt
  exact absurd hlt (lt_irrefl 1)

/-- **The q-digamma function** `ψ_q = Γ_q'/Γ_q`. -/
def qDigamma (q : RealEulerNome) (z : ℂ) : ℂ := deriv (qGammaOn q) z / qGammaOn q z

/-- The logarithmic derivative of Jackson's multiplier. -/
def qShiftIncrement (q : RealEulerNome) (z : ℂ) : ℂ :=
  -((Real.log q.val : ℂ) * (q.val : ℂ) ^ z) / (1 - (q.val : ℂ) ^ z)

theorem hasDerivAt_qcpow (q : RealEulerNome) (z : ℂ) :
    HasDerivAt (fun w : ℂ => (q.val : ℂ) ^ w)
      ((q.val : ℂ) ^ z * (Real.log q.val : ℂ)) z := by
  have h := (Complex.hasStrictDerivAt_const_cpow (x := (q.val : ℂ)) (y := z)
    (Or.inl q.complex_ne_zero)).hasDerivAt
  rw [Complex.ofReal_log q.pos.le]
  simpa [mul_comm] using h

/-- **The q-digamma shift law.** -/
theorem qDigamma_shift (q : RealEulerNome) {z : ℂ} (hz : z ∈ qHalfPlane) :
    qDigamma q (z + 1) = qDigamma q z + qShiftIncrement q z := by
  set L : ℂ := (Real.log q.val : ℂ) with hL
  set b : ℂ := ((1 - q.val : ℝ) : ℂ) with hb
  have hb0 : b ≠ 0 := q.one_sub_complex_ne_zero
  have hM : ∀ w ∈ qHalfPlane, qGammaOn q (w + 1) = ((1 - (q.val : ℂ) ^ w) / b) * qGammaOn q w :=
    fun w hw => qGammaOn_shift q hw
  -- derivative of the multiplier
  have hMder : HasDerivAt (fun w : ℂ => (1 - (q.val : ℂ) ^ w) / b)
      (-((q.val : ℂ) ^ z * L) / b) z := by
    have h1 : HasDerivAt (fun w : ℂ => 1 - (q.val : ℂ) ^ w)
        (-((q.val : ℂ) ^ z * L)) z := by
      simpa using (hasDerivAt_qcpow q z).const_sub 1
    simpa using h1.div_const b
  -- derivative of the q-Gamma at the shifted point
  have hz1 : z + 1 ∈ qHalfPlane := by
    have hzre : (0 : ℝ) < z.re := hz
    have : (z + 1).re = z.re + 1 := by simp
    show (0 : ℝ) < (z + 1).re
    rw [this]
    linarith
  have hΓz : DifferentiableAt ℂ (qGammaOn q) z :=
    ((analyticOnNhd_qGammaOn q) z hz).differentiableAt
  have hΓz1 : DifferentiableAt ℂ (qGammaOn q) (z + 1) :=
    ((analyticOnNhd_qGammaOn q) (z + 1) hz1).differentiableAt
  have hshiftDeriv : HasDerivAt (fun w : ℂ => qGammaOn q (w + 1))
      (deriv (qGammaOn q) (z + 1)) z := by
    exact HasDerivAt.comp_add_const z 1 hΓz1.hasDerivAt
  have hprodDeriv : HasDerivAt (fun w : ℂ => ((1 - (q.val : ℂ) ^ w) / b) * qGammaOn q w)
      ((-((q.val : ℂ) ^ z * L) / b) * qGammaOn q z
        + ((1 - (q.val : ℂ) ^ z) / b) * deriv (qGammaOn q) z) z :=
    hMder.mul hΓz.hasDerivAt
  have hev : (fun w : ℂ => qGammaOn q (w + 1))
      =ᶠ[𝓝 z] fun w : ℂ => ((1 - (q.val : ℂ) ^ w) / b) * qGammaOn q w := by
    filter_upwards [isOpen_qHalfPlane.mem_nhds hz] with w hw using hM w hw
  have hderiv : deriv (qGammaOn q) (z + 1)
      = (-((q.val : ℂ) ^ z * L) / b) * qGammaOn q z
        + ((1 - (q.val : ℂ) ^ z) / b) * deriv (qGammaOn q) z := by
    rw [← hshiftDeriv.deriv, hev.deriv_eq, hprodDeriv.deriv]
  -- divide by the shifted value
  have hΓ0 : qGammaOn q z ≠ 0 := qGammaOn_ne_zero q hz
  have hone : (1 : ℂ) - (q.val : ℂ) ^ z ≠ 0 := qcpow_ne_one q hz
  have hval : qGammaOn q (z + 1) = ((1 - (q.val : ℂ) ^ z) / b) * qGammaOn q z := hM z hz
  rw [qDigamma, qDigamma, qShiftIncrement, hderiv, hval, ← hL]
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
