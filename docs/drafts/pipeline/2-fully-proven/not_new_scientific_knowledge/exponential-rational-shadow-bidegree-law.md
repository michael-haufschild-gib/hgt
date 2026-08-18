# Exponential--rational shadow bidegree law

- **ID:** `exponential-rational-shadow-bidegree-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) — `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** For a finite sum of distinct nonzero exponential modes plus a nonzero rational
  divisor correction, the minimal homogeneous linear differential order is one more than the
  mode count.  At that minimal order, the least possible degree of the leading polynomial
  coefficient is exactly the finite divisor-support size of the rational shadow obtained by
  applying the exponential annihilator to the correction.

## Goal

Find a genuinely coupled source--divisor complexity law.  Separate statements

`differential order >= number of independent source frequencies`

and

`leading coefficient degree >= number of captured poles`

are classical bridges.  The target here is different: the source annihilator acts on the
divisor correction, and the complete zero--pole support of that *shadow* determines the exact
minimal leading degree.  This would provide a sharp finite-model law for mixed prime/spectral
approximants to completed logarithmic carriers.

## Setup

Let `lambda_1,...,lambda_r` be distinct nonzero complex numbers, let every `a_i` be nonzero,
and put

`g(s)=sum_(i=1)^r a_i exp(lambda_i s)`.

Let `q in C(s)` be nonzero and set `f=g+q`.  Define the monic constant-coefficient
annihilator

`L_0(D)=product_(i=1)^r (D-lambda_i)`

and its rational divisor shadow

`h=L_0(D)q`.

Write `h=N/M` in lowest terms and let

`rad(h)=rad(NM)`,

the squarefree polynomial whose roots are the distinct finite zeros and poles of `h`.

## Candidate theorem

1. `[PROVED HERE]` `h` is nonzero.
2. `[PROVED HERE]` The least order of a nonzero homogeneous linear
   differential equation over `C(s)` satisfied by `f` is exactly `r+1`.
3. `[PROVED HERE]` Among order-`r+1` homogeneous linear equations with
   polynomial coefficients annihilating `f`, every leading coefficient is divisible by
   `rad(h)`, and one exists with leading coefficient exactly `rad(h)` up to a nonzero scalar.
   Hence the exact minimal leading degree is

   `deg rad(h) = card(support(div h) intersect C)`.
4. If the `lambda_i` are `Q`-linearly independent, the least algebraic-differential order
   over `C(s)` is exactly `r`.  Thus adding a nonzero rational constraint costs exactly one
   homogeneous linear state but no nonlinear differential state.

## Proof attack

### Lemma 1: the rational shadow is nonzero

Suppose `L_0(D)q=0`.  A rational solution of a constant-coefficient ODE with nonzero
characteristic roots has no finite pole: at a pole, the highest derivative has strictly larger
pole order than every lower derivative and cannot cancel.  Hence `q` is a polynomial.  Since

`L_0(0)=(-1)^r product_i lambda_i != 0`,

the top-degree term of a nonzero polynomial survives under `L_0(D)`.  Therefore `q=0`, a
contradiction.  So `h!=0`.

### Lemma 2: exponential modes plus a rational function are linearly independent

For distinct `lambda_i`, the functions

`1, exp(lambda_1 s),...,exp(lambda_r s)`

are linearly independent over `C(s)`.  This is the standard exponential-polynomial
independence theorem, obtainable by a Wronskian/minimal-relation argument.

Let

`A=sum_(j=0)^n c_j(s)D^j`, `c_n!=0`,

annihilate `f`.  Put `C_s(X)=sum_j c_j(s)X^j`.  Expanding `Af=0` gives

`Aq + sum_i a_i C_s(lambda_i)exp(lambda_i s)=0`.

Lemma 2 forces `Aq=0` and `C_s(lambda_i)=0` for every `i`.  Thus `L_0(X)` divides
`C_s(X)` in `C(s)[X]`.

If `n<r`, this forces `A=0`.  If `n=r`, then `A=c_r(s)L_0(D)`, and

`Aq=c_r(s)h!=0`.

Therefore every homogeneous annihilator has order at least `r+1`.

### Lemma 3: order `r+1` exists

Because `h` is nonzero rational, `h'/h` is rational.  Write

`h'/h=B/A`

with coprime polynomials `A,B`, `A!=0`.  Then

`(A D-B)L_0(D) f = (A D-B)h = 0`.

This is a homogeneous order-`r+1` equation.

### Lemma 4: exact leading polynomial

At order `r+1`, divisibility by `L_0` forces every symbol to have the form

`C_s(X)=L_0(X)(a(s)X+b(s))`.

The equation on the rational part is

`a h'+b h=0`,

so `-b/a=h'/h`.  In characteristic zero, if `h=N/M` is reduced, the reduced denominator
of `h'/h` is exactly `rad(NM)`: at every zero or pole of multiplicity `m!=0`, the logarithmic
derivative has residue `m` and therefore a genuine simple pole.  Hence every possible `a` is
divisible by `rad(h)`.

Conversely, `a=rad(h)` makes `b=-a h'/h` polynomial, producing an order-`r+1` equation whose
leading coefficient is exactly `rad(h)`.  This proves the exact degree statement.

### Lemma 5: exact nonlinear differential order

Assume the `lambda_i` are `Q`-linearly independent.  Then the exponentials
`exp(lambda_i s)` are algebraically independent over `C(s)`.  The Vandermonde matrix
recovers them from `g,g',...,g^(r-1)`, so these `r` jets are algebraically independent.
The next jet obeys `L_0(D)g=0`.  Subtracting the known rational jets of `q` transfers both
facts to `f`.  Thus the exact algebraic-differential order is `r`.

## Prime--divisor specialization

For distinct primes `p in P`, take `lambda_p=-log p`; unique factorization makes these
frequencies `Q`-linearly independent.  For a nonzero finite spectral correction

`q_Z(s)=sum_(rho in Z) m_rho/(s-rho)`,

the mixed carrier

`f_(P,Z)(s)=sum_(p in P) a_p p^(-s)+q_Z(s)`

has exact algebraic-differential order `|P|`, exact homogeneous linear order `|P|+1`, and
minimal leading degree at that order equal to the number of distinct finite zeros and poles of

`product_(p in P)(D+log p) q_Z`.

For packets `Z` of actual xi zeros, this is a source--divisor complexity law for finite
prime/spectral models.  It rules out stabilization of differential order along an unbounded
prime exhaustion and gives an exact divisor-derived leading-degree invariant at every finite
stage.  It does not rule out infinite-dimensional RH routes.

## Attack list

- [x] Check the exponential-plus-rational linear-independence lemma against exact hypotheses.
- [x] Check whether polynomial coefficients, rather than rational coefficients, change the
  order-`r+1` factorization or attainability argument.
- [x] Check cancellation in the reduced denominator of `h'/h`; prove `rad(NM)` exactly.
- [x] Check degenerate cases: `r=0`, `q` polynomial, zero residues, repeated modes, and zeros of
  `h` at infinity.
- [x] Search exact and parent literature only after the proof survives.
- [x] Apply the severe parent-theory gate: a short consequence of exponential-polynomial
  independence and rational logarithmic derivatives is a bridge even if exact wording is absent.
- [x] Inspect existing Lean exponential-sum/Vandermonde and meromorphic-divisor infrastructure.
- [x] Complete the Lean formalization (2026-08-18)

## Scientific-novelty verdict

The theorem is correct and its exact shadow-divisor formula is useful, but it fails the
parent-theory gate.  In Ore-algebra language, the minimal annihilator is the least common left
multiple of the constant-coefficient exponential annihilator with the first-order annihilator of
the nonzero rational shadow.  The factor `rad(h)` is the primitive polynomial denominator of the
rational logarithmic derivative `h'/h`.  Classical annihilator/LCLM and desingularization theory
therefore generate the proof directly; absence of the exact wording is not scientific novelty.

Retain the theorem as a sharp bridge for finite mixed prime/spectral models.  A genuinely new
successor must constrain how the shadow divisor evolves under an infinite prime/divisor exhaustion,
not merely calculate one finite LCLM.

## Parent sources

- Ore's differential-operator/LCLM theory (1933), the direct algebraic parent.
- Chen, Jaroschek, Kauers, and Singer, *Desingularization Explains Order-Degree Curves for Ore
  Operators* (2013), arXiv:1301.0917.
- Chen, Kauers, and Singer, *Desingularization of Ore Operators* (2015),
  arXiv:1408.5512; leading-coefficient factors, removable singularities, and LCLM construction.
- Classical exponential-polynomial linear independence and Vandermonde recovery.

## Log

- 2026-07-11 -- Opened after rejecting the uncoupled pair of prime-order and pole-degree bounds.
  Candidate exact invariant is the finite divisor of the rational shadow `L_0(D)q`.
- 2026-07-11 -- Proof attack passed, including `r=0`, polynomial/constant shadows, infinity, and
  primitive polynomial coefficients.  Novelty failed: the result is an explicit Ore-algebra LCLM
  and rational-logarithmic-derivative calculation.  Promoted the complete proof to stage 2 as a
  bridge, not new scientific knowledge.
- 2026-08-18 -- All four items formalized unconditionally in Lean 4 across six modules
  (`RationalExponentialShadow`, `DerivEigenIndependence`, `LinearDifferentialOperatorSeparation`,
  `ExponentialRationalMinimalOrder`, `RadicalDerivativeDivisibility` +
  `RationalLogarithmicDerivativeRadical`, `ExponentialRationalLeadingDegree`,
  `ExponentialModeAlgebraicIndependence`), all wired into the `HTGeometry` umbrella and
  axiom-clean.  Two corrections to the paper proof were forced: the rigidity hypothesis must be
  restricted to *constant* multipliers (the unrestricted form is false over `C(s)`), and Lemma 5
  needs no transcendence theory — algebraic independence of the modes is linear independence of
  their monomials, and each monomial is itself an eigenvector.  Promoted to stage 3.

## Formalization (complete, 2026-08-18)

`formal/GaloisForLFunctions/HTGeometry/RationalExponentialShadow.lean`
(namespace `GaloisForLFunctions.RationalShadow`, wired into the `HTGeometry` umbrella, builds
green, axiom-clean) closes **Lemma 1**.

| Card step | Lean name |
|---|---|
| no nonzero rational function has a nonzero constant logarithmic derivative | `ratFuncCoordinateDerivation_ne_smul` |
| its cross-multiplied form | `ratFuncCoordinateDerivation_smul_cross` |
| one factor `D - λ` and its kernel | `shiftedDeriv`, `shiftedDeriv_eq_zero_iff` |
| the monic annihilator `L_0(D) = ∏ (D - λ_i)` | `shiftedDerivProd` |
| **Lemma 1**: `L_0(D) q = 0 ⟹ q = 0` | `eq_zero_of_shiftedDerivProd_eq_zero` |
| **Lemma 1, contrapositive**: the shadow `h = L_0(D) q` is nonzero | `shiftedDerivProd_ne_zero` |

The card's pole-order argument for Lemma 1 is replaced by a degree argument that also covers the
polynomial case in one step: cross-multiplying `z' = μ z` gives
`denom · num' - num · denom' = μ · num · denom`, and `Polynomial.degree_derivative_lt` makes the
left side of strictly smaller degree than the right whenever `μ ≠ 0` and `z ≠ 0`.  The separate
"rational solutions have no finite pole, hence are polynomials, hence vanish because `L_0(0) ≠ 0`"
case split is then unnecessary.

`formal/GaloisForLFunctions/HTGeometry/DerivEigenIndependence.lean`
(namespace `GaloisForLFunctions.DerivEigen`) closes **Lemma 2**.

| Card step | Lean name |
|---|---|
| eigenvectors with distinct eigenvalues are independent over the base | `linearIndependent_of_deriv_eigen` |
| the minimal-relation induction | `eigen_sum_eq_zero_aux` |
| **Lemma 2** over `C(s)`: `1, exp(λ_1 s), …, exp(λ_r s)` independent | `linearIndependent_expEigen_over_ratFunc` |

`formal/GaloisForLFunctions/HTGeometry/LinearDifferentialOperatorSeparation.lean`
(namespace `GaloisForLFunctions.LinDiffOp`) closes the step the card calls "Expanding `Af=0`".

| Card step | Lean name |
|---|---|
| the operator `A = ∑_j c_j D^j` and its base and symbol versions | `linOp`, `linOpBase`, `symbolEval` |
| `A E = (symbol at λ) · E` for an eigenvector | `linOp_eigen` (via `differentialJet_eigen`) |
| `A` on a base element | `linOp_algebraMap` |
| **`Af = 0 ⟹ Aq = 0` and `C_s(λ_i) = 0`** | `linOp_eq_zero_separation` |

The formal route makes one structural simplification: since each `a_i` is a nonzero constant, the
mode `a_i exp(λ_i s)` is itself an eigenvector with the same eigenvalue, so the coefficients `a_i`
never need to be carried — the theorem is stated for the modes already scaled.

The same module now also carries the operator/symbol dictionary that Lemma 4 needs:

| Card step | Lean name |
|---|---|
| one linear factor of the symbol is one factor `a·D - b` of the operator | `linOpBase_linear_mul` |
| the annihilator `L_0(D) = ∏_i (D - λ_i)` | `opList` |
| its monic symbol `L_0(X) = ∏_i (X - λ_i)`, monic of degree `r`, with constant coefficients | `factorPoly`, `factorPoly_monic`, `factorPoly_natDegree`, `factorPoly_coeff_deriv` |
| **the operator identity `∑_j (L_0)_j D^j = ∏_i (D - λ_i)`** | `linOpBase_factorPoly` |

`formal/GaloisForLFunctions/HTGeometry/ExponentialRationalMinimalOrder.lean` (same namespace)
closes **item 2**, the exact minimal homogeneous order.

| Card step | Lean name |
|---|---|
| the symbol as a polynomial, its degree, value and coefficients | `symbolPoly`, `symbolPoly_natDegree_le`, `symbolPoly_eval`, `symbolPoly_coeff` |
| a monic divisor of matching degree is the whole polynomial up to its leading scalar | `eq_C_leadingCoeff_mul_of_monic_dvd` |
| **lower bound**: every annihilator of order `≤ r` is zero | `coeff_eq_zero_of_annihilates` |
| **upper bound**: an explicit annihilator of order `r+1` | `exists_annihilator_succ` |

Together with Lemma 1 this is the card's statement that the least homogeneous order is exactly
`r + 1`.

Two notes on the formal route.

* The card builds the order-`r+1` annihilator from the reduced fraction `h′/h = B/A`.  That is not
  needed for existence: `A = h`, `B = h′` already gives `A·h′ - B·h = 0`, so the symbol
  `(h·X - h′)·L_0(X)` annihilates the carrier.  The reduced form is needed only for the *exact
  leading coefficient* claim.
* The lower bound is proved through the roots of the symbol rather than through polynomial
  division: `Multiset.prod_X_sub_C_dvd_iff_le_roots` turns "the symbol vanishes at the `r` distinct
  eigenvalues" directly into divisibility by the monic `∏_i (X - λ_i)`, and matching degrees then
  force a scalar multiple.

`formal/GaloisForLFunctions/HTGeometry/RadicalDerivativeDivisibility.lean`
(namespace `GaloisForLFunctions.RadicalDeriv`) and
`formal/GaloisForLFunctions/HTGeometry/RationalLogarithmicDerivativeRadical.lean`
(namespace `GaloisForLFunctions.RationalShadow`) close **item 3** at the level of the rational
shadow itself.

| Card step | Lean name |
|---|---|
| a prime is never a factor of its own derivative, nor of a nonzero constant | `not_dvd_derivative_self`, `not_dvd_C` |
| every prime factor of `N` divides `a` once `N ∣ a·N′` | `prime_dvd_of_dvd_mul_derivative` |
| hence `radical N ∣ a` | `radical_dvd_of_dvd_mul_derivative` |
| divisibility is tested on prime factors | `radical_dvd_of_forall_prime` |
| `rad(N·M)` clears the logarithmic derivative | `dvd_radical_mul_wronskian` |
| every clearing polynomial is a multiple of `rad(N·M)` | `radical_dvd_of_dvd_mul_wronskian` |
| the shadow radical `rad(h) = rad(denom h · num h)` | `shadowRadical` |
| cross-multiplied form of `a·h′ = b·h` | `cross_iff` |
| **minimality**: every admissible `a` is divisible by `rad(h)` | `shadowRadical_dvd` |
| **attainment**: `rad(h)` itself is admissible | `exists_cross_shadowRadical` |
| `deg rad(h)` is a lower bound for `deg a` | `natDegree_shadowRadical_le` |
| **`deg rad(h) = card(support(div h) ∩ C)`** | `natDegree_radical_eq_card_roots`, `natDegree_shadowRadical_eq_card_roots` |

The card's residue argument ("at every zero or pole of multiplicity `m ≠ 0` the logarithmic
derivative has a genuine simple pole") is replaced by an exact multiplicity computation valid over
any field of characteristic zero: at a prime `p` of multiplicity `e ≥ 1`, writing `N = p^e·N₁` with
`p ∤ N₁` gives `N′ = p^{e-1}·(e·p′·N₁ + p·N₁′)`, and the bracket is prime to `p` because `p ∤ e`
(characteristic zero), `p ∤ p′` (degree), and `p ∤ N₁`.  Cancelling `p^{e-1}` leaves `p ∣ a·u` with
`p ∤ u`.  The converse half is mathlib's `divRadical_dvd_wronskian_left`/`_right` together with
`divRadical_mul` for the coprime pair `(denom h, num h)`.

`formal/GaloisForLFunctions/HTGeometry/ExponentialRationalLeadingDegree.lean` (namespace
`GaloisForLFunctions.LinDiffOp`) transports item 3 to the operator level, which is what the card
actually asserts.

| Card step | Lean name |
|---|---|
| the symbol of an annihilator is divisible by `L_0` | `factorPoly_dvd_symbolPoly` |
| **Lemma 4's factorization** `C_s(X) = (c_{r+1}·X + t)·L_0(X)` | `symbolPoly_eq_linear_mul`, `linearTail` |
| the resulting first-order relation `c_{r+1}·h′ = -t·h` | `leadingCoeff_mul_deriv_shadow` |
| the leading coefficient of `(a·X - b)·L_0` is `a` | `coeff_linear_mul_factorPoly_top` |
| any realisation of `h′/h` gives an order-`r+1` annihilator | `linOp_linear_mul_factorPoly_eq_zero` |
| constants of `C(s)` are exactly `C` | `ratFunc_hconst` (via `ratFuncCoordinateDerivation_eq_zero_iff`) |
| the abstract annihilator is the shifted-derivative product | `opList_map_algebraMap` |
| polynomial coefficients stay polynomial under the factorization | `coeff_mem_range`, `symbolPoly_mem_range`, `factorPoly_mem_range` |
| **every order-`r+1` polynomial-coefficient annihilator has `rad(h) ∣ c_{r+1}`** | `shadowRadical_dvd_leadingCoeff` |
| **one exists with leading coefficient exactly `rad(h)`** | `exists_polynomial_annihilator_shadowRadical` |
| **exact minimal leading degree** | `natDegree_shadowRadical_le_of_annihilates` |

Two notes on this half.

* The card's blanket rigidity hypothesis ("no nonzero rational function has a nonzero constant
  logarithmic derivative") had to be *weakened* in `linOp_eq_zero_separation` and
  `coeff_eq_zero_of_annihilates` before it could be instantiated over `C(s)`: the unrestricted form
  `∀ μ ≠ 0, ∀ c ≠ 0, c′ ≠ μ·c` is false over `C(s)` (take `c = s`, `μ = 1/s`).  Only *constant* `μ`
  is rigid, and only constant `μ` ever occurs — the multipliers are differences of eigenvalues.
  Both statements now carry the hypothesis `μ′ = 0`.
* Polynomiality of the tail `t` is not assumed but derived: the order-`r+1` symbol lies in the image
  of `Polynomial.mapRingHom (algebraMap C[s] C(s))`, a subring, so all of its coefficients — and
  hence `t = (C_s - c_{r+1}·X·L_0).coeff r` — are polynomials.

`formal/GaloisForLFunctions/HTGeometry/ExponentialModeAlgebraicIndependence.lean` (namespace
`GaloisForLFunctions.DerivEigen`) closes **item 4 (Lemma 5)**.

| Card step | Lean name |
|---|---|
| powers and finite products of eigenvectors are eigenvectors | `deriv_pow_eigen`, `deriv_prod_eigen` |
| every monomial in the modes is an eigenvector, of weight `⟨d, λ⟩` | `eigenWeight`, `deriv_monomialValue` |
| **algebraic independence from rigid weight separation** | `algebraicIndependent_of_deriv_eigen` |
| the weight of an exponent vector over `C` | `weightC`, `eigenWeight_algebraMap` |
| `Z`-independent frequencies separate weights | `weightC_sub_ne_zero` |
| `Q`-linear independence gives the `Z` form | `int_independent_of_rat_linearIndependent` |
| **the modes are algebraically independent over `C(s)`** | `algebraicIndependent_expEigen_over_ratFunc` |
| jets of a sum of modes | `differentialJet_sum`, `differentialJet_sum_eigen` |
| translation of the polynomial variables is injective | `transSubst`, `transSubst_injective` |
| **Vandermonde transfer to the jets** | `algebraicIndependent_jets` |
| `L_0(D) f = h`, so the `r`-th jet is an affine combination of the lower ones | `linOp_factorPoly_carrier` |
| **Lemma 5: the exact algebraic-differential order is `r`** | `exact_algebraic_differential_order` |

The card's route through algebraic independence of `exp(λ_i s)` is replaced by the equivalent and
purely algebraic statement that algebraic independence *is* linear independence of the monomials
(`BigradedCorank.algebraicIndependent_iff_linearIndependent_monomialValue`, already owned by the
corpus): each monomial `∏_i E_i^{d_i}` is again a derivation eigenvector, of eigenvalue
`∑_i d_i λ_i`, so the corpus's `linearIndependent_of_deriv_eigen` applies verbatim once distinct
exponent vectors are known to carry distinct weights — which is exactly `Q`-linear independence of
the frequencies.  No transcendence input (Lindemann--Weierstrass, Ax, Kolchin--Ostrowski) is needed.
The Vandermonde step uses the corpus's `matrixSubst_injective`; the affine part needed the new
`transSubst_injective`.

All four items of the candidate theorem are therefore closed unconditionally, with
`#print axioms` reporting only `propext`, `Classical.choice`, `Quot.sound`.
