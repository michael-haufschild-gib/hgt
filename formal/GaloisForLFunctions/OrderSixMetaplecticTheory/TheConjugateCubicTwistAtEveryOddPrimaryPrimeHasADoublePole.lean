import GaloisForLFunctions.OrderSixMetaplecticTheory.TheThetaSquareFactorsThroughTheCoprimeSquaresAndTheConjugateTwist
import GaloisForLFunctions.OrderSixMetaplecticTheory.ThePrimaryGeneratorEvaluatesTheFractionalJacobiPhase

/-!
# The conjugate cubic twist at every odd primary prime has a double pole

For an odd primary prime q (ρ = |q|, N = N(q) = ρ², J = −χ(4)q the cubic–quadratic Jacobi sum, g₁, g₂ the Gauss sums
of χ and χ²), substituting the Euler identity (1 − ρ²ρ^{−3s})D = D_{cop} + ρ^{−s}D_q and g₁D_q = ρ⁻²χ(9)⁻¹g₂²D_g into the
fractional-trace relation gives

M(s)A(s)D_g(s) = [simple pole] + NJ(1 − ρ^{2−3s}) M(s)D(s),
A(s) = N²χ(−4)χ(9)⁻¹N^{s−2} + NJρ^{−s}χ(9)⁻¹g₂²ρ⁻²g₁⁻¹   (`conjFactor`).

The two summands of A have absolute values ρ^{2Re s} and ρ^{2−Re s}, so A does not vanish on Re s > 2/3
(`conjFactor_ne_zero`). Hence (`conjugateTwist_double_pole`) the Gauss-weighted conjugate twist D_g has the double
pole with leading coefficient A(4/3)⁻¹ NJ(1 − N⁻¹)·108π³r³ ≠ 0, and since g(k) = χ(k)⁻¹g₁ (`conjugateCubicTwist_double_pole`):

**the conjugate cubic twist L_{χ̄_q}(s) = Σ_k χ_q(k)⁻¹T(k)²(4π|ξ_k|)^{−s} keeps the double pole at every odd primary prime.**

Together with `cubicTwistAtPrime_double_pole` (the twist by χ_q) both cubic twists at q carry the double pole of the theta
square; the leading coefficient of the conjugate twist involves the Jacobi sum J of the cubic and the quadratic character
of O/q.
-/

noncomputable section

open Filter Function Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- c₂ = χ(9)⁻¹g₂²ρ⁻². -/
def eulerGauss : ℂ := (P.chi 9)⁻¹ * P.gaussAt2 1 ^ 2 * ((‖ringComplex P.p‖ : ℂ) ^ 2)⁻¹

/-- A(s) = N²χ(−4)χ(9)⁻¹N^{s−2} + NJρ^{−s}c₂g₁⁻¹. -/
def conjFactor (s : ℂ) : ℂ :=
  P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) * ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 2) +
    P.normC * P.fracJacobi * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * (P.gaussAt 1)⁻¹

theorem conjFactor_differentiableAt (s : ℂ) : DifferentiableAt ℂ P.conjFactor s := by
  have hρ := P.rho_ne_zero
  have hρρ : ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos P.norm_pos P.norm_pos).ne'
  have hQ : DifferentiableAt ℂ (fun s : ℂ => ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 2)) s :=
    DifferentiableAt.const_cpow (f := fun s : ℂ => s - 2) (differentiableAt_id.sub_const 2) (Or.inl hρρ)
  have ht : DifferentiableAt ℂ (fun s : ℂ => ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) s :=
    DifferentiableAt.const_cpow (f := fun s : ℂ => -s) differentiableAt_id.neg (Or.inl hρ)
  unfold conjFactor
  exact ((differentiableAt_const _).mul hQ).add
    ((((differentiableAt_const _).mul ht).mul (differentiableAt_const _)).mul (differentiableAt_const _))

theorem one_lt_rho : 1 < ‖ringComplex P.p‖ := by
  have h1 := P.one_le_norm
  refine lt_of_le_of_ne h1 fun h => P.rho_sq_ne_one ?_
  rw [← h]
  norm_num

theorem norm_normC : ‖P.normC‖ = ‖ringComplex P.p‖ ^ 2 := by
  rw [normC, Complex.norm_natCast, P.card_res_eq]

theorem four_ne_zero' (h2 : (2 : P.Res) ≠ 0) : (4 : P.Res) ≠ 0 := by
  have := mul_ne_zero h2 h2
  norm_num at this
  exact this

theorem norm_fracJacobi (h2 : (2 : P.Res) ≠ 0) : ‖P.fracJacobi‖ = ‖ringComplex P.p‖ := by
  rw [P.fracJacobi_eq_primary, norm_neg, norm_mul, P.norm_chi_eq_one _ (P.four_ne_zero' h2), one_mul]

theorem norm_eulerGauss : ‖P.eulerGauss‖ = 1 := by
  have hn := P.norm_pos
  rw [eulerGauss, norm_mul, norm_mul, norm_inv, norm_inv, P.norm_chi_eq_one _ P.nine_ne_zero', norm_pow, norm_pow,
    P.norm_gaussAt2_one, Complex.norm_real, Real.norm_of_nonneg hn.le]
  field_simp

/-- **A(s) does not vanish on Re s > 2/3.** -/
theorem conjFactor_ne_zero (h2 : (2 : P.Res) ≠ 0) (s : ℂ) (hs : 2 / 3 < s.re) : P.conjFactor s ≠ 0 := by
  have hρ0 := P.norm_pos
  have hρ1 := P.one_lt_rho
  set ρ := ‖ringComplex P.p‖ with hρdef
  set σ := s.re
  have h4 : P.chi (-4) ≠ 0 := P.chi_ne_zero_of_ne _ (neg_ne_zero.mpr (P.four_ne_zero' h2))
  have hQn : ‖((ρ * ρ : ℝ) : ℂ) ^ (s - 2)‖ = ρ ^ (σ - 2) * ρ ^ (σ - 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hρ0 hρ0), Real.mul_rpow hρ0.le hρ0.le]
    simp [σ]
  have htn : ‖((ρ : ℝ) : ℂ) ^ (-s)‖ = ρ ^ (-σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hρ0, Complex.neg_re]
  have n1 : ‖P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) * ((ρ * ρ : ℝ) : ℂ) ^ (s - 2)‖ =
      ρ ^ (2 : ℝ) * ρ ^ (2 : ℝ) * ρ ^ (σ - 2) * ρ ^ (σ - 2) := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_inv, P.norm_normC, P.norm_chi_eq_one _ (neg_ne_zero.mpr
      (P.four_ne_zero' h2)), P.norm_chi_eq_one _ P.nine_ne_zero', hQn, Real.rpow_two]
    ring
  have n2 : ‖P.normC * P.fracJacobi * ((ρ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * (P.gaussAt 1)⁻¹‖ =
      ρ ^ (2 : ℝ) * ρ ^ (-σ) := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, P.norm_normC, P.norm_fracJacobi h2, htn, P.norm_eulerGauss,
      P.norm_gaussAt_one, Real.rpow_two, ← hρdef]
    field_simp
  have hlt : ρ ^ (2 : ℝ) * ρ ^ (-σ) < ρ ^ (2 : ℝ) * ρ ^ (2 : ℝ) * ρ ^ (σ - 2) * ρ ^ (σ - 2) := by
    rw [← Real.rpow_add hρ0, ← Real.rpow_add hρ0, ← Real.rpow_add hρ0, ← Real.rpow_add hρ0]
    exact Real.rpow_lt_rpow_of_exponent_lt hρ1 (by linarith)
  intro h0
  have heq := congrArg norm (eq_neg_of_add_eq_zero_left h0)
  rw [norm_neg] at heq
  unfold conjFactor at h0
  have : ‖P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) * ((ρ * ρ : ℝ) : ℂ) ^ (s - 2)‖ =
      ‖P.normC * P.fracJacobi * ((ρ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * (P.gaussAt 1)⁻¹‖ := by
    have e := eq_neg_of_add_eq_zero_left h0
    rw [e, norm_neg]
  rw [n1, n2] at this
  linarith

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
