import GaloisForLFunctions.RHTower.MonodromyStripUniformization
import GaloisForLFunctions.RHTower.XiRealAnchorPositive
import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.XiCanonicalProduct

/-!
# The monodromy image of the Xi divisor

Under `mu(s) = exp(-2 π i s)` the nontrivial zeros of zeta land in the plane slit along the positive
real axis.  Two unconditional constraints hold on that image: it never meets the **unit circle**, and
it is stable under **complex conjugation**.  The first is the statement that zeta has no real zero in
the critical strip, transported to the modulus; the second is the functional equation, transported
by `monoScalar_lineConj`.

Together with `monoScalar_im_eq_zero_iff_re_eq_half`, this places the Riemann Hypothesis as the
assertion that a conjugation-stable, unit-circle-avoiding discrete set is contained in the negative
real axis.
-/

open Complex

namespace RHTower

noncomputable section

open HurwitzOrbit

theorem norm_monoScalar (s : ℂ) : ‖monoScalar s‖ = Real.exp (2 * Real.pi * s.im) := by
  rw [monoScalar, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **The monodromy image of the Xi divisor avoids the unit circle.**  Equivalently: no nontrivial
zero of zeta is real.  The modulus `‖mu(rho)‖ = exp(2 π Im rho)` equals one exactly on the real axis,
where `xi` is strictly positive. -/
theorem norm_monoScalar_ne_one_of_xiDivisor (ρ : XiDivisorSupport) :
    ‖monoScalar (ρ : ℂ)‖ ≠ 1 := by
  intro hone
  rw [norm_monoScalar] at hone
  have him : (ρ : ℂ).im = 0 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp, Real.exp_eq_exp] at hone
    have h : 2 * Real.pi * (ρ : ℂ).im = 0 := hone
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    rcases mul_eq_zero.mp h with h2 | h2
    · linarith
    · exact h2
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit ρ
  have hreal : (ρ : ℂ) = (((ρ : ℂ).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hzero : xi (((ρ : ℂ).re : ℝ) : ℂ) = 0 := by
    rw [← hreal]
    exact xi_eq_zero_of_mem_divisor_support ρ
  have hpos := xi_pos_on_real_anchor h0 h1
  rw [hzero] at hpos
  simp at hpos

/-- **The monodromy image of the Xi divisor is conjugation stable.**  This is the functional equation
in the uniformizing coordinate: `mu(1 - conj rho) = conj (mu rho)`, and `1 - conj rho` is again a
zero. -/
theorem monoScalar_conj_mem_image (ρ : XiDivisorSupport) :
    (starRingEnd ℂ) (monoScalar (ρ : ℂ))
      = monoScalar (1 - (starRingEnd ℂ) (ρ : ℂ)) :=
  (monoScalar_lineConj (ρ : ℂ)).symm

end

end RHTower
