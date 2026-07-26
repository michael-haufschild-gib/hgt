import GaloisForLFunctions.RHTower.DeningerArithmeticThreeTermCupDescent
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Source three-term Hodge purity

A positive flow-natural anti-linear Hodge operator on the middle cohomology of
an arbitrary three-term arithmetic complex forces every genuine Frobenius
eigenvalue onto the weight-one line.  This statement is source-independent:
the complex, cup product, flow, and Hodge operator are not defined from Xi.

The final corollary isolates the separate comparison required for the Riemann
zeta function.  It assumes only that every nontrivial Xi-divisor point occurs
as a genuine eigenvalue of the source middle flow.  Exact spectral equality,
multiplicity, determinants, and Lefschetz formulas are stronger obligations.
-/

open Complex

namespace RHTower

noncomputable section

section ThreeTermHodgePurity

variable {A0 A1 A2 : Type*}
variable [AddCommGroup A0] [Module ℂ A0]
variable [AddCommGroup A1] [Module ℂ A1]
variable [AddCommGroup A2] [Module ℂ A2]

/--
Source Hodge data on the middle cohomology of a three-term arithmetic flow.

The square-minus-one law records the intended odd Hodge structure.  The
critical-line argument itself uses flow naturality and positivity.
-/
structure DeningerArithmeticThreeTermHodge
    (F : DeningerArithmeticThreeTermFlow ℂ A0 A1 A2)
    (P : DeningerArithmeticThreeTermCupPairing F.complex) where
  star : F.complex.H1 →ₗ⋆[ℂ] F.complex.H1
  square_neg : ∀ x, star (star x) = -x
  theta_star :
    ∀ x, F.thetaH1 (star x) = star (F.thetaH1 x)
  positive :
    ∀ {x : F.complex.H1}, x ≠ 0 →
      0 < (P.pairH11 F.complex x (star x)).re

namespace DeningerArithmeticThreeTermHodge

variable
  (F : DeningerArithmeticThreeTermFlow ℂ A0 A1 A2)
  (P : DeningerArithmeticThreeTermCupPairing F.complex)
  (W : DeningerArithmeticThreeTermWeightOneCup F P)
  (Hodge : DeningerArithmeticThreeTermHodge F P)

/--
Source Hodge compatibility forces every genuine middle Frobenius eigenvalue
to have real part `1 / 2`.
-/
theorem eigenvalue_re_eq_half
    {rho : ℂ} {x : F.complex.H1}
    (hx0 : x ≠ 0)
    (hx : F.thetaH1 x = rho • x) :
    rho.re = 1 / 2 := by
  have hcup :=
    W.middle_weight_on_cohomology F P x (Hodge.star x)
  rw [hx, Hodge.theta_star, hx] at hcup
  have hstar :
      Hodge.star (rho • x) =
        (starRingEnd ℂ) rho • Hodge.star x :=
    map_smulₛₗ Hodge.star rho x
  rw [hstar] at hcup
  simp only [map_smul, LinearMap.smul_apply] at hcup
  have hmetric0 :
      P.pairH11 F.complex x (Hodge.star x) ≠ 0 := by
    intro hzero
    have hpos := Hodge.positive hx0
    rw [hzero, zero_re] at hpos
    linarith
  have hweight :
      rho + (starRingEnd ℂ) rho = 1 := by
    apply mul_right_cancel₀ hmetric0
    linear_combination hcup
  have hre := congrArg Complex.re hweight
  simp only [add_re, conj_re, one_re] at hre
  linarith

/--
One-way source spectral comparison: every nontrivial Xi-divisor point occurs
as a genuine eigenvalue of the source middle Frobenius.

This is weaker than exact spectrum, multiplicity, or determinant comparison,
but it is the exact spectral input needed for the RH implication.
-/
structure XiPointSpectrum where
  eigenvector :
    ∀ rho : XiDivisorSupport,
      ∃ x : F.complex.H1,
        x ≠ 0 ∧
          F.thetaH1 x =
            (1 / 2 + Complex.I * xiSpectralPointSupport rho) • x

/--
A positive source Hodge structure plus one-way inclusion of every nontrivial
zeta zero in the source point spectrum proves the Riemann hypothesis.
-/
theorem riemannHypothesis
    (Spectrum : XiPointSpectrum F) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro z hz hzero
  let rho : XiDivisorSupport :=
    ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
  obtain ⟨x, hx0, hx⟩ := Spectrum.eigenvector rho
  have hhalf :=
    Hodge.eigenvalue_re_eq_half F P W hx0 hx
  have hzhalf : z.re = 1 / 2 := by
    dsimp only [rho, xiSpectralPointSupport] at hhalf
    norm_num [Complex.mul_re] at hhalf
    linarith
  exact (ne_of_gt (mem_rightHalf.mp hz)) hzhalf

end DeningerArithmeticThreeTermHodge

end ThreeTermHodgePurity

end

end RHTower
