import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.HTGeometry.ParaorthogonalInteriorRootExclusion

/-!
# OPUC paraorthogonal logarithmic-phase gate for RH

If a source-defined stable polynomial has a unimodular paraorthogonal terminal whose value at the
dyadic logarithmic phase is a multiple of `XiC`, then every Xi zero lies on the centered real
axis.  An off-line zero would otherwise become a strict open-disk root of a paraorthogonal
terminal, contradicting finite OPUC root location.
-/

open Complex Polynomial Set

namespace RHTower

noncomputable section

/-- The dyadic logarithmic phase of the centered Xi coordinate. -/
def xiDyadicLogPhase (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (Real.log 2 : ℂ) * z)

theorem norm_xiDyadicLogPhase (z : ℂ) :
    ‖xiDyadicLogPhase z‖ = Real.exp (-Real.log 2 * z.im) := by
  rw [xiDyadicLogPhase, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero,
    sub_zero, zero_sub]
  ring

/-- Unit modulus of the dyadic phase is equivalent to lying on the centered real axis. -/
theorem im_eq_zero_of_norm_xiDyadicLogPhase_eq_one
    {z : ℂ} (hz : ‖xiDyadicLogPhase z‖ = 1) : z.im = 0 := by
  rw [norm_xiDyadicLogPhase, Real.exp_eq_one_iff] at hz
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- A stable paraorthogonal terminal whose dyadic-phase value is a source multiple of `XiC`
forces every Xi zero onto the centered real axis, and therefore proves RH. -/
theorem riemannHypothesis_of_paraorthogonal_dyadic_phase_XiC_value
    (p : ℂ → Polynomial ℂ) (terminal amplitude : ℂ → ℂ)
    (hp : ∀ z, p z ≠ 0)
    (hroots : ∀ z a, a ∈ (p z).roots → ‖a‖ < 1)
    (hterminal : ∀ z, ‖terminal z‖ = 1)
    (hvalue : ∀ z,
      (GaloisForLFunctions.HTGeometry.finiteParaorthogonalPolynomial
          (p z) (terminal z)).eval (xiDyadicLogPhase z) =
        amplitude z * XiC z) :
    RiemannHypothesis := by
  have hXiCZeroReal : ∀ z : ℂ, XiC z = 0 → z.im = 0 := by
    intro z hz
    have hphaseRoot :
        (GaloisForLFunctions.HTGeometry.finiteParaorthogonalPolynomial
          (p z) (terminal z)).IsRoot (xiDyadicLogPhase z) := by
      rw [Polynomial.IsRoot, hvalue z, hz, mul_zero]
    have hphaseUnit :=
      GaloisForLFunctions.HTGeometry.finiteParaorthogonalPolynomial_isRoot_norm_eq_one
        (hp z) (hroots z) (hterminal z) hphaseRoot
    exact im_eq_zero_of_norm_xiDyadicLogPhase_eq_one hphaseUnit
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  let z : ℂ := (rho - 1 / 2) * (-Complex.I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * Complex.I = rho := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-Complex.I) * Complex.I = (1 : ℂ) := by
        rw [neg_mul, Complex.I_mul_I]
        ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have him : z.im = 0 := hXiCZeroReal z hXiC
  have hzIm : z.im = 1 / 2 - rho.re := by simp [z]
  have hre : rho.re = 1 / 2 := by linarith [him, hzIm]
  exact (ne_of_gt (mem_rightHalf.mp hrho)) hre

end

end RHTower
