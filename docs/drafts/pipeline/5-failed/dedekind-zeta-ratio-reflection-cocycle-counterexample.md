# Dedekind-zeta ratios kill the reflection-cocycle dichotomy

- **ID:** `dedekind-zeta-ratio-reflection-cocycle-counterexample`
- **Stage:** 5-failed
- **Type:** FALSIFIED CONJECTURE + THEOREM (paper) + THEOREM (Lean, abstract ratio mechanism)
- **Lean:** `formal/GaloisForLFunctions/RHTower/ReflectionCocycleClass.lean`
- **Statement:** Integral multiplicativity, meromorphic continuation, and infinite prime support do
  not force a differentially algebraic reflection cocycle to come from a Dirichlet polynomial.

## Claim falsified

`[CONJECTURE C-COC]` asserted that, for an integral multiplicative Dirichlet series with meromorphic
continuation,

\[
h_F(s)=\frac{F(1-s)}{F(s)}
\]

is differentially algebraic if and only if `F` is a Dirichlet polynomial.

The one-prime carrier `(1-p^{-s})^{-1}` already falsifies the literal statement.  The theorem below
also falsifies the obvious repair requiring infinitely many nontrivial prime factors.

## Counterexample theorem

`[PROVED]` Let `K` and `L` be distinct cubic number fields with the same discriminant.  Then

\[
F_{K,L}(s)=\frac{\zeta_K(s)}{\zeta_L(s)}
\]

has all of the following properties:

1. it is represented on `Re(s)>1` by an ordinary Dirichlet series with integer-valued
   multiplicative coefficients and coefficient `1` at `n=1`;
2. it has meromorphic continuation to the whole plane;
3. it has nontrivial Euler factors at infinitely many rational primes and is not a Dirichlet
   polynomial;
4. it is reflection invariant, `F_{K,L}(1-s)=F_{K,L}(s)`;
5. consequently `h_{F_{K,L}}=1`, hence its reflection cocycle is differentially algebraic.

There are infinitely many such counterexamples.

## Proof

For a number field `M`, write

\[
\Lambda_M(s)=A_M(s)\zeta_M(s),\qquad
A_M(s)=|D_M|^{s/2}\Gamma_{\mathbb R}(s)^{r_1(M)}
\Gamma_{\mathbb C}(s)^{r_2(M)}.
\]

The Dedekind functional equation is `Lambda_M(s)=Lambda_M(1-s)`.  Two cubic fields with the same
signed discriminant have the same signature, so `A_K=A_L`.  Dividing their two functional
equations gives the meromorphic identity

\[
\frac{\zeta_K(1-s)}{\zeta_L(1-s)}=
\frac{\zeta_K(s)}{\zeta_L(s)}.
\]

Thus `F_{K,L}` is reflection invariant and its cocycle is `1` wherever the pointwise quotient is
defined; the meromorphic identity then holds globally.

On `Re(s)>1`, `zeta_K` counts integral ideals by norm.  The reciprocal `1/zeta_L` is the Dirichlet
series of the ideal-Mobius function, aggregated by norm.  Both coefficient sequences are integral
and multiplicative, so their Dirichlet convolution gives an integral multiplicative coefficient
sequence for `F_{K,L}`.  Absolute convergence in this half-plane justifies the product.

Distinct cubic fields have distinct Dedekind zeta functions: Perlis proved that number fields of
degree at most six are arithmetically solitary.  Their local factors therefore differ at infinitely
many rational primes; otherwise equality of splitting types outside a finite set would make the
fields arithmetically equivalent.  Hence `F_{K,L}` has infinite prime support.  It cannot be a
Dirichlet polynomial: a reflection-invariant finite Dirichlet polynomial is constant by comparing
its two real-end asymptotics, and constant `F_{K,L}` with first coefficient `1` would give
`zeta_K=zeta_L`.

Davis--Spearman--Yoo construct infinitely many triples of distinct monogenic cubic fields with the
same discriminant.  Applying the argument to each pair gives infinitely many counterexamples.

## Formal theorem surface

- `reflCocycle_mul`
- `reflCocycle_div`
- `reflCocycleMonoidWithZeroHom`
- `reflCocycle_one_sub`
- `reflCocycle_eq_zero_iff`
- `reflCocycle_eq_ite_of_reflection`
- `reflCocycle_eq_zero_iff_of_reflection`
- `reflCocycle_eq_one_iff`
- `reflCocycle_eq_one_iff_reflection_fixed`
- `reflCocycle_eq_one_iff_reflectionInvariant`
- `reflCocycle_eq_iff_cross_mul`
- `reflCocycle_eq_iff_div_reflection_fixed`
- `reflCocycle_eq_iff_div_reflectionInvariant`
- `reflCocycle_eq_iff_of_common_reflection`
- `reflCocycle_eq_of_common_reflection`
- `ratio_one_sub_eq_iff_of_common_reflection`
- `ratio_one_sub_eq_of_common_reflection`
- `reflCocycle_div_eq_one_iff_of_common_reflection`
- `reflCocycle_div_eq_one_of_common_reflection`
- `reflCocycle_of_conductor_eq_ite`
- `reflCocycle_of_conductor_eq_zero_iff`
- `riemannZeta_one_sub_eq_gammaRatio_mul`
- `riemannZeta_one_sub_eq_zero_iff`
- `reflCocycle_zeta_eq_ite`
- `reflCocycle_zeta_eq_zero_iff`
- `reflCocycle_eq_one_iff_const`

The general laws classify the complete fiber of the reflection-cocycle map on nonvanishing
carriers: two carriers have the same cocycle exactly when their quotient is reflection invariant.
Multiplicativity and quotient compatibility themselves are unconditional, including at zeros,
because totalized inversion preserves the required product identities; nonvanishing first enters
only when cocycle equality is converted to equality of cross-multiplied or quotient values.
At each point the cocycle is therefore a zero-preserving monoid homomorphism in the carrier, and
argument reflection sends its value unconditionally to its inverse. Its exact trivial fiber needs
no external premise: `h_F(s)=1` is equivalent to `F(s) ≠ 0` together with
`F(1-s)=F(s)`, and the global version forces both nowhere-vanishing and reflection invariance.
Its zero support is equally exact: `h_F(s)=0` iff `F(s)=0` or `F(1-s)=0`, so totalization records
the reflection-saturation of the carrier divisor rather than discarding it.
More generally, a pointwise reflection law `F(1-s)=H(s)F(s)` evaluates the cocycle exactly as
`0` on the carrier zero locus and `H(s)` off it. This removes the old conductor-size premise from
the pure-conductor cocycle theorem and yields the exact conductor cocycle-zero/carrier-zero
equivalence whenever the natural conductor is nonzero.
For the actual Riemann zeta function, the completed functional equation is now exposed as an
unconditional open-strip value relation, including at zeros.  Consequently its totalized
reflection cocycle is the archimedean Gamma ratio off the zeta zero locus and zero exactly on that
locus; `reflCocycle_zeta_eq_zero_iff` is an exact Prop interface for the critical-strip divisor,
not a nonvanishing-conditioned formula.
Pointwise cocycle equality first factors through a denominator-free cross relation requiring
nonvanishing only at the evaluation point; reflected nonvanishing is needed solely to rewrite that
relation as invariance of a quotient.
The common-reflection specialization is now exact even at carrier zeros: the two cocycles agree
if and only if the shared multiplier vanishes or the two unreflected carrier values have matching
zero status. Thus equality does not require the shared reflection multiplier to be nonzero, since
a vanishing multiplier simply makes both reflected values and both cocycles zero. Quotient
invariance has the exact totalized boundary: it holds if and only if the multiplier is nonzero or
at least one unreflected carrier value vanishes. The quotient cocycle is one exactly when the
multiplier and both unreflected carrier values are nonzero; failure of any factor makes it zero,
not one. Dedekind zeta functions are not present in the current Lean dependency surface, so the number-field
instantiation remains a paper application of standard algebraic-number-theory theorems.
For the formal integral-multiplicative carrier class, the previous nowhere-nonzero input to
`reflCocycle_eq_one_iff_const` has consequently been removed: cocycle triviality supplies it.

## Parent-literature audit

- Hecke's functional equation shows that the completion factor of a Dedekind zeta function depends
  only on its discriminant and signature.
- Robert Perlis, *On the equation zeta_K(s) = zeta_K'(s)*, Journal of Number Theory 9 (1977),
  342--360, proves arithmetic solitude through degree six.
- Chad Davis, Blair Spearman, and Jeewon Yoo, *Cubic polynomials defining monogenic fields with the
  same discriminant*, Journal de Theorie des Nombres de Bordeaux 30 (2018), 991--996,
  https://doi.org/10.5802/jtnb.1061, supplies infinitely many triples.

## Scientific verdict

- `[PROVED]` C-COC is false as stated.
- `[PROVED]` Requiring infinite prime support does not repair it.
- `[PROVED]` The reflection cocycle forgets every quotient direction inside a common completion
  class; this is a structural kernel, not an infinite-order continuation gap.
- `[FALSIFIED RH ROUTE]` The cocycle alone also fails the report's first RH gate: common-completion
  quotients can change the arithmetic Euler data while leaving the cocycle identically trivial.
- `[OPEN CORE]` Any successor must impose a primitive/indecomposable condition that forbids
  common-completion quotients, then prove that the condition is intrinsic rather than chosen to
  exclude this counterfamily.  No such condition is presently supplied.

## Dual-gate verdict

The counterexample theorem is a direct synthesis of standard Dedekind-zeta functional equations,
arithmetic equivalence, and known equal-discriminant field families.  It decisively kills the
project conjecture but is `[BRIDGE]`, not new scientific knowledge.  The route is retired rather
than relabeled as a discovery.
