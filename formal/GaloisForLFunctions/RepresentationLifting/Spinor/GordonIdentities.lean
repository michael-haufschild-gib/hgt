import GaloisForLFunctions.HTGeometry.Arxiv2607NondegenerateDirac


/-!
# Gordon identities for the Weyl gamma matrices

Contracting the Clifford relation gives the momentum-square identity.
The vector and axial Gordon decompositions follow algebraically, with
explicit mass-shell residuals before restriction to Lorentz orbits.
-/

open scoped BigOperators
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.RepresentationLifting.Spinor
noncomputable section
abbrev DiracMatrix := Matrix HLSDiracSpinor HLSDiracSpinor ℂ

/-- Clifford contraction with the covariant momentum coordinates. -/
def momentumSlash (p : HLSMinkowskiVector) : DiracMatrix :=
  ∑ μ, (p μ : ℂ) • hlsWeylGamma μ

theorem gamma_slash_anticommutator (p : HLSMinkowskiVector) (μ : Fin 4) :
    hlsWeylGamma μ * momentumSlash p + momentumSlash p * hlsWeylGamma μ =
      (2 * (hlsMinkowskiCoordinateSign μ * p μ : ℝ) : ℂ) • 1 := by
  simp only [momentumSlash, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc, ← Finset.sum_add_distrib, ← smul_add, hlsWeylGamma_clifford,
    smul_smul]
  fin_cases μ <;>
    simp [Fin.sum_univ_four, hlsComplexMinkowskiMetric, hlsMinkowskiMetric,
      hlsMinkowskiCoordinateSign, mul_comm]

/-- The Clifford contraction squares to the Minkowski quadratic form. -/
theorem momentumSlash_square (p : HLSMinkowskiVector) :
    momentumSlash p * momentumSlash p = (hlsMinkowskiForm p : ℂ) • 1 := by
  have h : (2 : ℂ) • (momentumSlash p * momentumSlash p) =
      (2 : ℂ) • ((hlsMinkowskiForm p : ℂ) • (1 : DiracMatrix)) := by
    calc
      _ = ∑ μ, (p μ : ℂ) •
          (hlsWeylGamma μ * momentumSlash p + momentumSlash p * hlsWeylGamma μ) := by
        rw [two_smul]
        conv_lhs => lhs; lhs; unfold momentumSlash
        conv_lhs => rhs; rhs; unfold momentumSlash
        simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
          smul_add, Finset.sum_add_distrib]
      _ = _ := by
        simp only [gamma_slash_anticommutator, Fin.sum_univ_four,
          show hlsMinkowskiCoordinateSign 0 = 1 from rfl,
          show hlsMinkowskiCoordinateSign 1 = -1 from rfl,
          show hlsMinkowskiCoordinateSign 2 = -1 from rfl,
          show hlsMinkowskiCoordinateSign 3 = -1 from rfl, hlsMinkowskiForm_apply]
        push_cast
        module
  exact (smul_right_injective DiracMatrix (by norm_num : (2 : ℂ) ≠ 0)) h

theorem momentumSlash_sub (p q : HLSMinkowskiVector) :
    momentumSlash (p - q) = momentumSlash p - momentumSlash q := by
  simp only [momentumSlash, Pi.sub_apply, Complex.ofReal_sub, sub_smul,
    Finset.sum_sub_distrib]

/-- Chirality anticommutes with the entire momentum contraction. -/
theorem gammaFive_slash_anticommutator (p : HLSMinkowskiVector) :
    hlsWeylGammaFive * momentumSlash p + momentumSlash p * hlsWeylGammaFive = 0 := by
  simp only [momentumSlash, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc, ← Finset.sum_add_distrib, ← smul_add,
    hlsWeylGammaFive_anticommutes, smul_zero, Finset.sum_const_zero]

/-- Contraction of the existing antisymmetric Dirac generators. -/
def bivectorContract (p : HLSMinkowskiVector) (μ : Fin 4) : DiracMatrix :=
  ∑ ν, (p ν : ℂ) • hlsDiracBivector μ ν

theorem bivectorContract_eq (p : HLSMinkowskiVector) (μ : Fin 4) :
    bivectorContract p μ = (Complex.I / 2) •
      (hlsWeylGamma μ * momentumSlash p - momentumSlash p * hlsWeylGamma μ) := by
  simp only [bivectorContract, momentumSlash, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc, ← Finset.sum_sub_distrib, ← smul_sub,
    Finset.smul_sum, hlsDiracBivector, smul_smul]
  apply Finset.sum_congr rfl
  intro ν _
  rw [mul_comm (p ν : ℂ)]

/-- Twice the mean momentum plus the spin transfer, with raised free index. -/
def gordonCurrent (p q : HLSMinkowskiVector) (μ : Fin 4) : DiracMatrix :=
  (hlsMinkowskiCoordinateSign μ * (q μ + p μ) : ℂ) • 1 +
    Complex.I • bivectorContract (q - p) μ

theorem gordonCurrent_eq (p q : HLSMinkowskiVector) (μ : Fin 4) :
    gordonCurrent p q μ =
      momentumSlash q * hlsWeylGamma μ + hlsWeylGamma μ * momentumSlash p := by
  have hp := gamma_slash_anticommutator p μ
  have hq := gamma_slash_anticommutator q μ
  have hI : Complex.I * (Complex.I / 2) = -(1 / 2 : ℂ) := by
    rw [← mul_div_assoc, Complex.I_mul_I]
    ring
  unfold gordonCurrent
  rw [bivectorContract_eq, momentumSlash_sub, smul_smul, hI]
  have hc : (hlsMinkowskiCoordinateSign μ * (q μ + p μ) : ℂ) • (1 : DiracMatrix) =
      (1 / 2 : ℂ) • ((2 * (hlsMinkowskiCoordinateSign μ * q μ : ℝ) : ℂ) • 1 +
        (2 * (hlsMinkowskiCoordinateSign μ * p μ : ℝ) : ℂ) • 1) := by
    push_cast
    module
  rw [hc, ← hp, ← hq]
  simp only [mul_sub, sub_mul]
  module

/-- The Dirac numerator remains meaningful at zero mass. -/
def diracNumerator (m : ℝ) (p : HLSMinkowskiVector) : DiracMatrix :=
  momentumSlash p + (m : ℂ) • 1

/-- Exact vector Gordon defect for arbitrary, possibly off-shell, momenta. -/
theorem vectorGordon_residual (m : ℝ) (p q : HLSMinkowskiVector) (μ : Fin 4) :
    diracNumerator m q * ((2 * m : ℂ) • hlsWeylGamma μ - gordonCurrent p q μ) *
      diracNumerator m p =
    (m ^ 2 - hlsMinkowskiForm q : ℂ) •
      (hlsWeylGamma μ * diracNumerator m p) +
    (m ^ 2 - hlsMinkowskiForm p : ℂ) •
      (diracNumerator m q * hlsWeylGamma μ) := by
  have h : ∀ x y g : DiracMatrix,
      (y + (m : ℂ) • 1) * ((2 * m : ℂ) • g - (y * g + g * x)) *
        (x + (m : ℂ) • 1) =
      ((m : ℂ) ^ 2 • 1 - y * y) * g * (x + (m : ℂ) • 1) +
        (y + (m : ℂ) • 1) * g * ((m : ℂ) ^ 2 • 1 - x * x) := by
    intro x y g
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, mul_assoc]
    module
  rw [gordonCurrent_eq, diracNumerator, diracNumerator, h,
    momentumSlash_square, momentumSlash_square]
  simp only [← sub_smul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- Exact axial Gordon defect; chirality cancels the two mass terms. -/
theorem axialGordon_residual (m : ℝ) (p q : HLSMinkowskiVector) (μ : Fin 4) :
    diracNumerator m q * hlsWeylGammaFive * gordonCurrent p q μ * diracNumerator m p =
    (m ^ 2 - hlsMinkowskiForm q : ℂ) •
      (hlsWeylGammaFive * hlsWeylGamma μ * diracNumerator m p) -
    (m ^ 2 - hlsMinkowskiForm p : ℂ) •
      (diracNumerator m q * hlsWeylGammaFive * hlsWeylGamma μ) := by
  have h : ∀ x y c g : DiracMatrix,
      (y + (m : ℂ) • 1) * c * (y * g + g * x) * (x + (m : ℂ) • 1) =
      ((m : ℂ) ^ 2 • 1 - y * y) * c * g * (x + (m : ℂ) • 1) -
        (y + (m : ℂ) • 1) * c * g * ((m : ℂ) ^ 2 • 1 - x * x) +
        (y + (m : ℂ) • 1) * (c * y + y * c) * g * (x + (m : ℂ) • 1) := by
    intro x y c g
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, mul_assoc]
    module
  rw [gordonCurrent_eq, diracNumerator, diracNumerator, h,
    gammaFive_slash_anticommutator, mul_zero, zero_mul, zero_mul, add_zero,
    momentumSlash_square, momentumSlash_square]
  simp only [← sub_smul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

private theorem orbit_mass (m : ℝ) (g : hlsLorentzGroup) :
    hlsMinkowskiForm (g.1 (hlsRestMomentum m)) = m ^ 2 := by
  rw [hlsLorentz_preserves_minkowski]
  exact hlsRestMomentum_mass_shell m

/-- Vector Gordon identity on Lorentz transforms of rest momenta, including zero mass. -/
theorem vectorGordon_lorentzOrbit (m : ℝ) (g h : hlsLorentzGroup) (μ : Fin 4) :
    diracNumerator m (h.1 (hlsRestMomentum m)) *
      gordonCurrent (g.1 (hlsRestMomentum m)) (h.1 (hlsRestMomentum m)) μ *
      diracNumerator m (g.1 (hlsRestMomentum m)) =
    (2 * m : ℂ) • (diracNumerator m (h.1 (hlsRestMomentum m)) * hlsWeylGamma μ *
      diracNumerator m (g.1 (hlsRestMomentum m))) := by
  have hs := vectorGordon_residual m (g.1 (hlsRestMomentum m))
    (h.1 (hlsRestMomentum m)) μ
  simp only [orbit_mass, Complex.ofReal_pow, sub_self, zero_smul, add_zero,
    mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc] at hs
  exact (sub_eq_zero.mp hs).symm

/-- Axial Gordon cancellation on the same explicitly constructed mass shell. -/
theorem axialGordon_lorentzOrbit (m : ℝ) (g h : hlsLorentzGroup) (μ : Fin 4) :
    diracNumerator m (h.1 (hlsRestMomentum m)) * hlsWeylGammaFive *
      gordonCurrent (g.1 (hlsRestMomentum m)) (h.1 (hlsRestMomentum m)) μ *
      diracNumerator m (g.1 (hlsRestMomentum m)) = 0 := by
  have hs := axialGordon_residual m (g.1 (hlsRestMomentum m))
    (h.1 (hlsRestMomentum m)) μ
  simpa only [orbit_mass, Complex.ofReal_pow, sub_self, zero_smul] using hs

#print axioms momentumSlash_square
#print axioms gordonCurrent_eq
#print axioms vectorGordon_residual
#print axioms axialGordon_residual
#print axioms vectorGordon_lorentzOrbit
#print axioms axialGordon_lorentzOrbit

end
end GaloisForLFunctions.RepresentationLifting.Spinor
