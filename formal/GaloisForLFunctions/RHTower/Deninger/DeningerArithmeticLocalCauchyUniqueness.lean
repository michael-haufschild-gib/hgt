import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticUnitaryBRSTHodge

/-!
# Fourier-mode Cauchy uniqueness on arithmetic Hodge charts

The Kummer half-cylinder and finite-prime cylindrical models reduce
each nonconstant harmonic packet to

`u(r) = c₊ exp(m r) + c₋ exp(-m r)`, with `m ≠ 0`.

This file formalizes the exact coefficient elimination used by local
full-Cauchy uniqueness.  It is source-local and assumes no zeta-zero
or Riemann-hypothesis statement.
-/

namespace RHTower

/--
`DAC_LOCAL_FULL_CAUCHY_MODE_UNIQUENESS`.

Zero value and zero normal value determine both integration
constants of a nonzero cylindrical Fourier mode.
-/
theorem deningerSecondOrderMode_coefficients_eq_zero
    {m cPlus cMinus : ℂ}
    (hm : m ≠ 0)
    (hvalue : cPlus + cMinus = 0)
    (hnormal : m * cPlus - m * cMinus = 0) :
    cPlus = 0 ∧ cMinus = 0 := by
  have hfactor : m * (cPlus - cMinus) = 0 := by
    linear_combination hnormal
  have hdiff : cPlus - cMinus = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hm
  constructor
  · linear_combination
      (1 / 2 : ℂ) * hvalue + (1 / 2 : ℂ) * hdiff
  · linear_combination
      (1 / 2 : ℂ) * hvalue - (1 / 2 : ℂ) * hdiff

/--
Finite-energy half-cylinder form: exclusion of the growing
coefficient and zero Dirichlet trace kill the mode.
-/
theorem deningerFiniteEnergyMode_coefficients_eq_zero
    {cPlus cMinus : ℂ}
    (hgrowing : cPlus = 0)
    (hvalue : cPlus + cMinus = 0) :
    cPlus = 0 ∧ cMinus = 0 := by
  constructor
  · exact hgrowing
  · linear_combination hvalue - hgrowing

end RHTower
