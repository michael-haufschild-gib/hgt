# Rational orbit preservers are Laurent Adams operations

- **ID:** alst-rational-orbit-preservers-are-laurent-adams
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For a finite prime set containing two distinct primes, every rational self-map defined on the entire prime orbit and preserving it has coordinates `p^(−ib)X_p^n`, with unique `n∈ℤ`, `b∈ℝ`. Real or integer coefficients force `b=0`.

## Research consequence
Arbitrary rational denominators permit time reversal but no nonlinear clock.
Fixed orbit points satisfy `(n−1)t+b=0`; fixing two distinct orbit points
forces the identity rational map. This exhausts rational replacements for
Adams within the globally orbit-preserving category.

## Proof
Represent each coordinate by polynomial numerator and denominator `N_p/D_p`,
with denominator nonzero on the orbit. Substitution `X_p=p^(−iz)` gives entire
finite exponential sums, still denoted `N_p,D_p`. Both are nonzero on the
real axis by orbit preservation.

Locally normalized logarithms have defect
`log(q) log(F_p(t)/F_p(t₀)) − log(p) log(F_q(t)/F_q(t₀))`
in a countable image of `ℤ²`. Continuity on a small interval forces this
defect constant. Thus
`log(q)(N_p'/N_p−D_p'/D_p)=log(p)(N_q'/N_q−D_q'/D_q)`.
Clearing denominators and the identity principle extend the identity across
all complex points. Residues are integer orders. Irrational prime-log ratios
force both numerator-minus-denominator orders to vanish at every point.

The equal-divisor quotient is entire and nonvanishing. Finite exponential
sums have order-one growth; fixed-divisor rigidity makes the quotient
`exp(a_p z+d_p)`. Unit modulus on the real axis forces
`Re(a_p)=Re(d_p)=0`, giving `c_p exp(iγ_p t)`.
Choose any denominator monomial `α_p`. Its nonzero Bohr coefficient, shifted
by `γ_p`, must occur at a numerator monomial `β_p`. Hence
`γ_p=frequency(α_p)−frequency(β_p)`.

At time zero, `c_p=p^(−ib)`. Two-prime character-clock rigidity gives
`γ_p=−a log(p)` with one common slope `a`, without assuming clock regularity.
Multiplication by `a` therefore preserves the finite integer span of prime
logarithms. The determinant trick makes `a` integral over `ℤ`; Baker
independence makes the integer exponent matrix scalar. Thus `a=n∈ℤ`.
Injectivity of polynomial restriction, proved by Bohr coefficient extraction,
gives the exact polynomial identity
`N_p X_p^{(-n).toNat}=C(p^(−ib)) D_p X_p^{n.toNat}`.
This also proves the converse and handles arbitrary common factors.

Two-prime orbit injectivity gives uniqueness and the fixed-point equation.
For real coefficients, evaluation at the all-one point makes every `c_p`
real and unimodular. Squaring gives a common torsion return; two-prime torsion
rigidity forces `b=0`.

## Formalization
| Mathematical component | Lean declaration |
|---|---|
| No clock regularity needed | `common_exponential_clock_log_deriv` |
| Global cleared differential identity | `common_exponential_clock_cross_identity` |
| Equal complex zero divisors | `equal_divisors_of_common_exponential_clock` |
| Entire orbit extension and subquadratic proximity | `entirePrimeOrbitValue_proximity` |
| Entire quotients of unit modulus are characters | `entire_quotient_eq_character` |
| Integer scalar endomorphisms of the prime-logarithm lattice | `prime_log_lattice_dilation_is_int` |
| Polynomial quotient characters have signed prime frequencies | `polynomial_quotient_character_frequency` |
| Complete rational classification and converse | `rationalPreservesPrimeOrbit_iff`, `rationalPreservesPrimeOrbit_laurentAdams` |
| Unique exponent and translation | `laurentAdamsRelation_parameters_unique` |
| Two fixed orbit points force the identity | `rational_preserver_two_fixed_points` |
| Real and integer coefficients remove translation | `real_rational_preserver_is_laurentAdams`, `integer_rational_preserver_is_laurentAdams` |

These components and the corpus inputs
`logDeriv_residue_of_meromorphicOrder`,
`EntireQuotient.exists_entire_nonvanishing_quotient`,
`OrderOneRigidity.exists_expAffine_of_entire_quotient`
have only `propext`, `Classical.choice`, `Quot.sound` as transitive axioms.
All eight modules passed final plain `lake --old env lean` checks. The
[complex classification](../../../../formal/GaloisForLFunctions/ArithmeticLefschetzStepanovTheory/RationalOrbitPreserversAreLaurentAdams.lean)
and [real/integer descent](../../../../formal/GaloisForLFunctions/ArithmeticLefschetzStepanovTheory/RealRationalOrbitPreservers.lean)
are complete and wired into the programme umbrella. No placeholders or
raised proof limits occur in the eight modules.
