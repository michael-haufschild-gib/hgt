# Exponential--rational shadow bidegree law

- **ID:** `exponential-rational-shadow-bidegree-law`
- **Stage:** 2-fully-proven
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
- [ ] Inspect existing Lean exponential-sum/Vandermonde and meromorphic-divisor infrastructure.

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
