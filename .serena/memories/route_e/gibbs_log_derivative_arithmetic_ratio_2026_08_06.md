# Cycle 19: the zero potential IS an arithmetic ratio (2026-08-06)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-19).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsLogDerivative.lean`, wired, built, no sorry,
axioms clean.

## THE TWO-WAY BRIDGE
`gibbs_coulomb_sum_eq` (division-free): for gibbsDiagC S x (−1) ≠ 0,
  gibbsDiagC S x (−1) · ∑_ζ (1+ζ)⁻¹ = −eval(−1)(derivative (gibbsPoly S x))
i.e.  ∑_ζ 1/(1+ζ) = (∑_{T⊆S} |T|(−1)^{|T|}e^{−x·e(T)}) / J_S(x)
                  = (∑_{d∣m} μ(d)ω(d)e^{−dx}) / (∑_{d∣m} μ(d)e^{−dx})   [cycle-15 anchor,
                    ω(d) = |T| on squarefree divisors].
AT THE PARITY POINT THE ZERO POTENTIAL *IS* AN ARITHMETIC RATIO (not merely bounded by
arithmetic). With cycle 17 (log‖Z‖−log‖J‖ ≤ ∑2/‖1+ζ‖) and ∑1/‖1+ζ‖ ≥ |∑1/(1+ζ)|, the
Coulomb sum is squeezed between explicit Möbius data below and the cancellation above.

Supporting: `eval_derivative_multiset_prod` (log-derivative of ∏(X−ζ) = Coulomb sum, by
Multiset.induction_on; `field_simp` closes the cons step), `gibbsPoly_eq_prod_roots`,
`gibbsPoly_derivative_eval` (derivative in the configuration basis).

## Lean traps
- `Polynomial.derivative_sum` for Finset.sum (NOT `derivative_finsetSum`; that name does
  not exist). `Polynomial.eval_finsetSum` IS the eval name.
- `rw [...] at *` is dangerous: it rewrote `hJ` (which mentions gibbsDiagC) and destroyed
  the goal shape. Use an explicit `calc` chain instead.
- `Polynomial.derivative_X_pow : derivative (X^n) = C n * X^(n-1)` is fine at n = 0
  (ℕ-subtraction gives C 0 * X^0 = 0).
