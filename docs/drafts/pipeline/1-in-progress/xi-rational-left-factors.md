# Rational left factors of the actual tilted Xi source

- **ID:** RH-XIRLF-20261007
- **Stage:** 1-in-progress; paper reduction closed, corpus/API audit pending
- **Parent:** `../2-fully-proven/xi-finite-cover-monodromy.md`
- **Predecessor:** `../3-formalized/xi-meromorphic-polynomial-lifts.md`
- **Verdict:** BRIDGE; rational-factor rigidity, no novelty claim

## Exact target and hostile boundary

For every real a, a nonconstant rational map R:P1->P1 and meromorphic h on
C satisfying R(h)=d_a everywhere as meromorphic functions force degree(R)=1.
Equivalently h is a Möbius transform of d_a. This covers every genus-zero
compactified finite-cover lift. It does not classify higher-genus covering
surfaces; their exclusion is a separate uniformization step in the parent.

Possible formal pitfall: totalized division at a pole is not a value of a
rational map on P1. Use identities in the global meromorphic field and
punctured-germ equality, with coprime numerator/denominator. Do not infer
analytic identities at poles by substituting totalized zero inverses.

## Dependency-closed paper reduction

Choose a pole b of R. If it is infinity set k=h. Otherwise set
k=1/(h-b). The identity R(h)=d_a, and the fact that d_a is entire, show that
h never equals b in the spherical meromorphic sense: a pole of R composed
with a zero of h-b would give a pole of d_a. Therefore k extends to an entire
function. The function is nonconstant because d_a is nonconstant.

In this coordinate write the outer rational map as A(k)/B(k), with A,B
coprime and B nonzero. Infinity is a pole by construction, so deg A>deg B.
Every finite root of B is omitted by k: evaluating the identity
A(k)=d_a B(k) there would contradict coprimality. Little Picard therefore
permits at most one distinct root of B.

If B is constant, d_a is a polynomial in k; the preceding actual polynomial
rigidity forces degree one. If B has one root c, factor B=beta*(X-c)^m,
with m>=1. The entire function u=k-c is nowhere zero. Expand A(u+c)/
(beta*u^m) as a finite sum of powers of u and 1/u. The audited Laurent
exclusion contradicts this representation of d_a. Thus only the degree-one
case survives. Undoing the Möbius coordinate change preserves rational-map
degree and gives h as a Möbius transform of d_a.

This is the elementary rational part of the classical polynomial/Laurent
reduction audited in the parent. No new compact-surface theorem is assumed
in this step. The polynomial pole-order theorem supplies one-pole removal;
the finite-pole coordinate still needs exact local proof and formal transport.

## Planned formal assembly

1. Prove that a coprime polynomial quotient with an entire composite excludes
   every finite denominator-root value, using meromorphic normal forms.
2. Show the reciprocal coordinate has no poles and preserve its field value.
3. Implement the Möbius substitution and coprime denominator normalization.
4. Apply actual polynomial/Laurent rigidity and recover the exact degree or
   equivalent Möbius-factor classification.

Corpus query `rational composition meromorphic inner entire outer polynomial
Laurent Picard omitted poles` completed partial=false, inventory68208; all
twenty candidate and nineteen source statements inspected. Compiler coverage
remains largely pending/stale and is not proof verification. The hits include
general meromorphic composition and the just-proved polynomial pole theorem,
but no ready rational-factor classification. Output:
`/tmp/rh-xi-rational-left-search-20261007.json`.

First exact local lemma: if p(f)=d*q(f) on punctured germs, d is analytic,
q(b)=0 and p(b) is nonzero, then ord(f-b)<=0, including exclusion of infinite
order. Otherwise a removable analytic representative g of f-b has positive
order, hence g(z)=0. Continuity extends p(g+b)=d*q(g+b) at z, contradicting
p(b) nonzero. Inverting yields nonnegative order; global normal form gives
the entire reciprocal coordinate. This closes the local proof before Lean.

## Sharper analytic implementation (paper closed)

The entire-inner rational case can bypass Picard and Laurent classification.
Let p(h)=d_a*q(h), with coprime p,q and entire h. Coprimality makes q(h)
nowhere zero. At an actual Xi zero rho put beta=h(rho): p(beta)=0 while
q(beta) is nonzero. On Re(s)>1, h omits beta. It also omits every root c of q
globally. If q is nonconstant, select such c. Schottky bounds h on the real
ray. For each root c, the analytic reciprocal 1/(h-c) omits 0 and
1/(beta-c), so it too has an exponential ray bound. Factor q over C with
multiplicities: its reciprocal is a fixed scalar times the finite product
of these reciprocals. Multiplication and polynomial evaluation preserve
exponential ray bounds. Thus p(h)/q(h)=d_a has one, contradicting actual Xi
superlinear ray growth. Therefore q is constant; polynomial rigidity then
forces p to have degree one. No Picard premise or denominator normalization
is needed for this exact entire-inner theorem.

This replaces only the planned analytic implementation, not the parent
statement. General meromorphic inner functions still require the finite-pole
coordinate and polynomial transport through that coordinate. All four
local/normal-form/field-preservation lemmas pass scratch Lean. Promoted and
wired `HTGeometry/MeromorphicRationalPoleLift.lean`. Both rational Schottky
estimates also pass scratch Lean; promoted and wired
`HTGeometry/SchottkyRationalGrowth.lean`. Their target builds, actual Xi
entire-rational assembly, and polynomial-reflection API/proof are checking
in a single sequential Lean chain. Final actual-source and axiom audits
remain pending; the general rational endpoint is not yet formalized.

## Exact coordinate algebra (paper closed)

For the general meromorphic lift, the constant-q case reduces directly to
polynomial rigidity after dividing p by its nonzero constant denominator.
If q is nonconstant, choose a root b; coprimality gives p(b) nonzero. Set
N=max(deg p,deg q), A(X)=X^N*p(b+1/X), B(X)=X^N*q(b+1/X).
These are polynomials: implement them by `Polynomial.reflect N` after
composition with X+C(b). The top coefficient of A is p(b), so deg A=N.
For a nonzero common root c of A,B, evaluation gives the common root
b+1/c of p,q, impossible. At zero, at least one of A(0),B(0) is the nonzero
leading coefficient of the polynomial whose degree is N. Therefore A,B are
coprime; no gcd normalization step is needed.

The entire reciprocal coordinate k represents (x-b)^(-1). This field element
is nonzero, since x=b would contradict p(b) nonzero and q(b)=0 in the original
identity. Reflection evaluation gives A(k)=d_a*B(k) as field elements.
Continuity makes this an identity of entire representatives even at k=0.
The entire rational theorem forces deg A=1, hence max(deg p,deg q)=1.
This formulation gives the rational-map degree directly without a separate
Möbius degree-invariance theorem. It also handles poles of the inner function.

The follow-up deep Schottky query completed partial=false, inventory68211;
all twenty candidate and twenty source statements inspected. No equivalent
ready theorem found; output `/tmp/rh-schottky-rational-search-20261007.json`.
External exact follow-up again found the classical Beardon--Ng and Pakovich
ancestry, not a certified new Xi result. Beardon--Ng is from 2006 despite
search-engine metadata suggesting a recent publication:
https://www.acadsci.fi/mathematica/Vol31/beardon.pdf. Verdict stays BRIDGE.

Additional hostile ancestry audit: Garunkstis, "Selberg zeta-function
associated to compact Riemann surface is prime", Rev. Un. Mat. Argentina
62 (2021), 213-218, DOI 10.33044/revuma.1729, was opened and its statements
and Lemma 1.3 proof inspected. Its one-root/simple-zero mechanism is an
adjacent classical predecessor, not an exact theorem about tilted Xi. It
references Liao--Yang (2003), Math. Nachr. 257, 59-66, for zeta primeness.
Do not transfer these to Xi, or conflate rational left-factor rigidity with
full compositional primeness. Rational degree is the invariant needed here:
for any nonzero entire F, F=(1/X) composed with (1/F), so a claim that the
outer map must literally be a polynomial needs a coordinate normalization.
Our degree-one endpoint includes this inversion and makes no such claim.
Source: https://revistas.uns.edu.ar/revuma/article/download/1729/1563/8952.
