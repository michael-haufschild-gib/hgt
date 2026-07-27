import GaloisForLFunctions.RHTower.DeningerClosedOperatorPolarization

/-!
# Riesz-eigenfunctional purity for Deninger cohomology

Meyer's literal zeta-zero eigenvectors occur in the strong dual of
the nuclear quotient.  A positive Hodge completion constrains such an
eigenfunctional only after it is bounded for the Hodge norm and its
Riesz representative belongs to the closed generator domain.

This file supplies the missing abstract bridge.  The weight-one
adjoint law applied to that Riesz representative forces the
transpose eigencharacter to have real part `1 / 2`.
-/

open Complex

namespace RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/--
`DAC_RIESZ_EIGENFUNCTIONAL_HODGE_PURITY`.

If a nonzero vector in the domain of a closed weight-one polarized
generator represents a transpose eigenfunctional with character
`rho`, then `rho` lies on the weight-one line.
-/
theorem deningerClosedWeightOne_rieszEigenfunctional_re_eq_half
    (P : DeningerClosedWeightOnePolarization H)
    {rho : ℂ}
    (y : P.theta.domain)
    (hy : (y : H) ≠ 0)
    (heigen :
      ∀ x : P.theta.domain,
        inner ℂ (y : H) (P.theta x) =
          rho * inner ℂ (y : H) (x : H)) :
    rho.re = 1 / 2 := by
  have hweight := P.theta_inner_sum y y
  have hright := heigen y
  have hleft :
      inner ℂ (P.theta y) (y : H) =
        (starRingEnd ℂ) rho *
          inner ℂ (y : H) (y : H) := by
    rw [← inner_conj_symm, hright, map_mul]
    simp
  rw [hleft, hright] at hweight
  have hmetric0 :
      inner ℂ (y : H) (y : H) ≠ 0 :=
    inner_self_ne_zero.mpr hy
  have hconj :
      (starRingEnd ℂ) rho + rho = 1 := by
    apply mul_right_cancel₀ hmetric0
    linear_combination hweight
  have hre := congrArg Complex.re hconj
  simp only [add_re, conj_re, one_re] at hre
  linarith

end

end RHTower
