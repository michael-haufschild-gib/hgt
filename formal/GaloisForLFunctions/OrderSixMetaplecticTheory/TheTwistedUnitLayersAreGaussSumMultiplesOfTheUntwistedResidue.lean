import GaloisForLFunctions.OrderSixMetaplecticTheory.TheUnitLayerOfTheCubicTwistHasASimplePole

/-!
# The twisted unit layers are Gauss-sum multiples of the untwisted residue

The residues at `w = 2/3` of the twisted unit layers `S^{χ_p}_1`, `S^{χ̄_q}_1` (`cubicUnitLayer_simple_pole`,
`conjugateUnitLayer_simple_pole`) and of `S₁` (STCC, a positive real number) share the factor `C̄²Z̃(4/3)(4π|ξ₁|)^{−4/3}`;
their ratios are local at `p`:

* the cubic twist (`twistUnitResidue_closed`):
  `Res S^{χ_p}_1 = 2N(p)^{5/6}/(N(p) + 1) · \overline{(9/p)₃} G̃(p) · Res S₁`,
  a normalized cubic Gauss sum at `p` times a factor of size `2N(p)^{−1/6}`;
* the conjugate twist (`conjUnitResidue_eq_mul`): `Res S^{χ̄_q}_1 = N(q)J_q/(g(χ_q)A_q(4/3)) · Res S₁`, with the
  Jacobi sum `J_q = −χ_q(4)q` and `A_q(4/3) = N²χ(−4)χ(9)⁻¹N^{−2/3} + NJ_qN(q)^{−2/3}c₂g(χ_q)⁻¹`.

So the `S₁`-reweighted family at the columns `p⁴` (twist `χ_p`) has a main term whose phase is the cubic Gauss sum
at `p`: the main terms across these columns are as incoherent as the Gauss sums at primes.
-/

noncomputable section

open Filter Topology
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `E_p(4/3) = 1 − N(p)⁻¹ = (ρ² − 1)/ρ²`, `ρ = |p|`. -/
theorem eulerFactorQ_four_thirds_rho :
    P.eulerFactorQ (4 / 3) = ((‖ringComplex P.p‖ : ℂ) ^ 2 - 1) / (‖ringComplex P.p‖ : ℂ) ^ 2 := by
  have hρ : (‖ringComplex P.p‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr P.norm_pos.ne'
  have h := ringComplex_norm_sq_eq_absNorm_span P.p
  have h' : ((Ideal.absNorm (Ideal.span {P.p} : Ideal O) : ℕ) : ℂ) = (‖ringComplex P.p‖ : ℂ) ^ 2 := by
    rw [← Complex.ofReal_natCast, ← h]
    push_cast
    ring
  rw [P.eulerFactorQ_four_thirds, h']
  field_simp

/-- The cubic-twist factor `κ_p = (9/p)₃\overline{G̃(p)}` has modulus one: `κ_p⁻¹ = \overline{(9/p)₃}G̃(p)`. -/
theorem twistFactor_inv :
    (ringComplex (symbol 9 P.p) * star (normalizedCubicUnitGauss P.p))⁻¹ =
      star (ringComplex (symbol 9 P.p)) * normalizedCubicUnitGauss P.p := by
  have h9 : IsCoprime (9 : O) P.p := by
    have := P.isCoprime_three.pow_left (m := 2)
    norm_num at this
    exact this
  have hs := cubicSymbol_star_mul 9 P.p P.primary h9
  have hG : ‖normalizedCubicUnitGauss P.p‖ = 1 := normalizedCubicUnitGauss_prime_norm P.p P.prime P.primary
  have hGG : star (normalizedCubicUnitGauss P.p) * normalizedCubicUnitGauss P.p = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hG]
    norm_num
  refine inv_eq_of_mul_eq_one_right ?_
  linear_combination (star (normalizedCubicUnitGauss P.p) * normalizedCubicUnitGauss P.p) * hs + hGG

/-- `Res S₁` over the common denominator `2(4π|ξ₁|)^{−4/3}C̄²(2/3)Z̃(4/3)`. -/
theorem untwistedSResidue_eq_denom :
    untwistedSResidue = 54 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3 /
      (2 * unitFrequencyWeight (4 / 3) * (star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta (4 / 3))) := by
  have hW := unitFrequencyWeight_ne_zero (4 / 3)
  have hC := scalar_star_ne_zero
  have hL := LFunction_chi3D_one_ne_zero
  rw [clearedCubeZeta_four_thirds]
  field_simp
  ring

/-- **The cubic twist multiplies the unit-layer residue by `2/(c_p(4/3)E_p(4/3)κ_p)`.** -/
theorem twistUnitResidue_eq_mul :
    P.twistUnitResidue = 2 / (P.dilateFactor (4 / 3) * P.eulerFactorQ (4 / 3) *
      (ringComplex (symbol 9 P.p) * star (normalizedCubicUnitGauss P.p))) * untwistedSResidue := by
  have hW := unitFrequencyWeight_ne_zero (4 / 3)
  have hC := scalar_star_ne_zero
  have hL := LFunction_chi3D_one_ne_zero
  have hc := P.dilateFactor_ne_zero (4 / 3) (by norm_num)
  have hE := P.eulerFactorQ_ne_zero (s := 4 / 3) (by norm_num)
  have hκ := P.twistFactor_ne_zero
  rw [untwistedSResidue_eq_denom]
  unfold twistUnitResidue twistLimit combinationDenom
  rw [clearedCubeZeta_four_thirds]
  field_simp
  ring

/-- **The residue of the cubic-twisted unit layer in closed form.** For every primary prime `p` (`ρ = |p|`,
`ρ² = N(p)`): `Res S^{χ_p}_1 = 2ρ^{5/3}/(ρ² + 1) · \overline{(9/p)₃}G̃(p) · Res S₁`. -/
theorem twistUnitResidue_closed :
    P.twistUnitResidue = 2 * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (5 / 3 : ℂ) / ((‖ringComplex P.p‖ : ℂ) ^ 2 + 1) *
      (star (ringComplex (symbol 9 P.p)) * normalizedCubicUnitGauss P.p) * untwistedSResidue := by
  have hρ := P.rho_ne_zero
  have hρ1 := P.rho_sq_ne_one
  set u : ℂ := ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (1 / 3 : ℂ) with hudef
  have hu3 : u ^ 3 = ((‖ringComplex P.p‖ : ℝ) : ℂ) := by
    rw [hudef, ← Complex.cpow_nat_mul]
    norm_num
  have hu5 : ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (5 / 3 : ℂ) = u ^ 5 := by
    rw [hudef, ← Complex.cpow_nat_mul]
    norm_num
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hu3
    exact hρ hu3.symm
  have hρu : (‖ringComplex P.p‖ : ℂ) = u ^ 3 := hu3.symm
  have hκ := P.twistFactor_ne_zero
  rw [P.twistUnitResidue_eq_mul, P.dilateFactor_four_thirds, P.eulerFactorQ_four_thirds_rho, hu5, ← P.twistFactor_inv,
    ← hudef, hρu]
  rw [hρu] at hρ1
  clear_value u
  generalize ringComplex (symbol 9 P.p) * star (normalizedCubicUnitGauss P.p) = κ at hκ ⊢
  generalize untwistedSResidue = R
  have h6 : (u ^ 3) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have h6' : (u ^ 3) ^ 2 + 1 ≠ 0 := by
    intro h
    have h1 : (u ^ 3) ^ 2 = -1 := by linear_combination h
    have hn := congrArg (fun z : ℂ => ‖z‖) h1
    simp only [norm_pow, norm_neg, norm_one] at hn
    have hu : ‖u‖ ^ 3 = ‖ringComplex P.p‖ := by
      rw [← norm_pow, hu3, Complex.norm_real, Real.norm_eq_abs, abs_of_pos P.norm_pos]
    rw [hu] at hn
    nlinarith [P.one_lt_rho]
  have h10 : -1 + u ^ 6 ≠ 0 := by
    rw [show -1 + u ^ 6 = (u ^ 3) ^ 2 - 1 by ring]
    exact h6
  have h11 : u ^ 6 - 1 ≠ 0 := by
    rw [show u ^ 6 - 1 = (u ^ 3) ^ 2 - 1 by ring]
    exact h6
  field_simp

/-- **The conjugate twist multiplies the unit-layer residue by `NJ/(gA(4/3))`.** For every odd primary prime `q`:
`Res S^{χ̄_q}_1 = N(q)J_q/(g(χ_q)A_q(4/3)) · Res S₁`. -/
theorem conjUnitResidue_eq_mul (h2 : (2 : P.Res) ≠ 0) :
    P.conjUnitResidue = P.normC * P.fracJacobi / (P.gaussAt 1 * P.conjFactor (4 / 3)) * untwistedSResidue := by
  have hW := unitFrequencyWeight_ne_zero (4 / 3)
  have hC := scalar_star_ne_zero
  have hL := LFunction_chi3D_one_ne_zero
  have hE := P.eulerFactorQ_ne_zero (s := 4 / 3) (by norm_num)
  have hA := P.conjFactor_ne_zero h2 (4 / 3) (by norm_num)
  have hg := P.gaussAt_one_ne_zero
  have hρ := P.rho_ne_zero
  have hEq : 1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-(4 / 3 : ℂ))) ^ 3 =
      P.eulerFactorQ (4 / 3) := by
    set u : ℂ := ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (1 / 3 : ℂ) with hudef
    have hu3 : u ^ 3 = ((‖ringComplex P.p‖ : ℝ) : ℂ) := by
      rw [hudef, ← Complex.cpow_nat_mul]
      norm_num
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num)] at hu3
      exact hρ hu3.symm
    have ht : ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-(4 / 3 : ℂ)) = (u ^ 4)⁻¹ := by
      rw [Complex.cpow_neg, hudef, ← Complex.cpow_nat_mul]
      norm_num
    rw [ht, P.eulerFactorQ_four_thirds_rho, ← hu3]
    field_simp
  rw [untwistedSResidue_eq_denom]
  unfold conjUnitResidue conjLimit combinationDenom
  rw [hEq]
  field_simp
  ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
