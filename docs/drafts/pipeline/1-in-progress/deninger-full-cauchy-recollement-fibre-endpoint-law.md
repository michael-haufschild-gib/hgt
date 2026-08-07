# Deninger full-Cauchy recollement fibre endpoint law

- **ID:** `deninger-full-cauchy-recollement-fibre-endpoint-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE WITH PAPER-PROVED HOMOLOGICAL REDUCTION
- **Label:** `DAC_FULL_CAUCHY_RECOLLEMENT_FIBRE_ENDPOINT_LAW`
- **Parent:** `deninger-global-green-energy-radical`
- **Statement:** joint full-Cauchy restriction on the actual arithmetic relevant complex has
  endpoint-only homotopy fibre, so its map on middle cohomology is injective.

## Goal

Let
\[
 C^\bullet_{\rm arith}
 \xrightarrow{\ R_{\rm Cauchy}\ }
 \widehat\prod_{\alpha}' C^\bullet_{\partial,\alpha}
 \tag{1}
\]
be the joint Dirichlet--Neumann/residue restriction from Deninger's strict nuclear
Rost--Schmid/real-signature totalization to every generic Kummer, finite-prime extended-cusp, and
real-apex boundary complex.  Construct `(1)` before Hodge completion and prove a strict
quasi-isomorphism
\[
 \operatorname{Fib}(R_{\rm Cauchy})
 \simeq
 \mathbb C[0]\oplus\mathbb C(-1)[-2].
 \tag{2}
\]
In particular (H^1(\operatorname{Fib}R_{\rm Cauchy})=0), hence
\[
 H^1(R_{\rm Cauchy})
 \colon H^1_{\rm arith}
 \hookrightarrow
 \widehat\prod_{\alpha}'H^1(C^\bullet_{\partial,\alpha})
 \tag{3}
\]
is injective.  Equation `(3)` is exactly
`DAC_FULL_CAUCHY_BOUNDARY_CLASSIFICATION` after quotienting local Cauchy data by local
boundaries.

This is source-pure and strictly weaker than RH.  It mentions no Xi zero, mate gain, divisor
fibre, or spectral sign.  RH still additionally needs the global Green/Paugam form comparison and
source Hodge/resolvent faithfulness.

## Why this is Route L's upstream source theorem

The finite Calderon--Witt oriented complex is already exact in middle degree:
`deningerCalderonWittGlobalOrientedSourceComplex_H1_eq_zero`.  Its prime-two/prime-three Green
witness therefore supplies a canonical boundary and the sharp physical reporter, but it cannot
carry the nonzero Xi spectral middle class.  The latter lives only after the strict nuclear
Poisson--zeta/relevant-complex passage.  Linear source-inverse/analytic-dagger defect is also
mixed-cobar exact for every parameter, so no linear Bockstein on the finite source can select the
critical line.

The first non-tautological Route-L producer is consequently `(2)`: finite exactness must pass
through the singular cofinal source without creating middle fibre cohomology.  Once `(2)` is
combined with local positive Cauchy energy, the already-formalized Cauchy descent theorem makes
the global Green form faithful.  Restricting the eventual global Green--Stokes comparison to the
canonical two-prime boundary gives
`XI_TWO_PRIME_ORIENTED_BOUNDARY_STRICT_TRANSPORT`.

## Paper-proved homological reduction

For a chain map (F:C^\bullet\to D^\bullet) of three-term cochain complexes, a degree-one cocycle
(x\in C^1) represents an element of the kernel of (H^1(F)) precisely when there is
(y\in D^0) with
\[
 d_Cx=0,\qquad F_1x=d_Dy.                                      \tag{4}
\]
The pair ((x,y)) is a degree-one cocycle of the homotopy fibre.  If every such pair has an
(a\in C^0) satisfying
\[
 d_Ca=x,\qquad F_0a=y,                                         \tag{5}
\]
then (x) is a global boundary, so (H^1(F)) is injective.  This is the exact three-term form of
“(H^1(\operatorname{Fib}F)=0) implies middle conservativity”; it does not assume degree-zero
surjectivity separately.

The reduction is unconditional and formalized as
`DeningerArithmeticThreeTermChainMap.mapH1_injective_of_fiberH1_exact` in
`DeningerArithmeticCauchyCohomologyDescent.lean`.  It leaves only the arithmetic identification
`(2)`.

## Attack

1. Construct the five component full-Cauchy restrictions on the actual two-column
   Rost--Schmid/signature source and prove the six naturality squares already required by
   `deningerTwoColumnSignatureCauchyChainMap`.
2. Identify the homotopy fibre chartwise with the minimal-domain interior complex.  Local
   full-Cauchy uniqueness kills its nonconstant harmonic modes.
3. Pass through the restricted nuclear prime product.  Prove strictness and absence of a
   cofinal `lim^1` class; finite-stage exactness alone does not suffice.
4. Use the completed finite-plus-real Arakelov trace-kernel sequence to identify the surviving
   constant/residue/apex fibre with the two endpoint lines in `(2)`.
5. Apply the paper/Lean fibre-injectivity theorem to obtain `(3)`, then the existing local-energy
   descent theorem to close `DAC_GLOBAL_GREEN_ENERGY_RADICAL` on the constructed source.

## Hostile audit

- **Finite-source acyclicity.**  It proves no spectral result; it only forces the successful
  carrier to be the strict nuclear relevant complex rather than the finite algebraic packet
  source.
- **Unreduced torsion.**  Dense nonclosed Hilbert range is not admissible middle cohomology.
  Equation `(2)` is a strict nuclear fibre statement, not use of
  `closure(range)/range` as Deninger cohomology.
- **Local-to-global fallacy.**  Local Cauchy uniqueness does not imply `(2)` without strict
  recollement and control of the cofinal derived-limit term.
- **Endpoint erasure.**  Constants, logarithmic residues, product-formula charge, and real apex
  are retained and identified with degrees zero and two; they are not declared zero.
- **Scalar-reader insufficiency.**  One prime average misses mean-zero packet modes.  Full packet
  Dirichlet and Neumann data, including transverse Fourier coordinates, are mandatory.
- **Hopf-cyclic false shortcut.**  Modular pairs in involution and SAYD coefficients allow
  non-unimodular modular weights; they do not force the half-density character to have modulus
  one.
- **RH circularity.**  A proof of `(2)` may use only source sheaves, local PDE uniqueness,
  restricted-product estimates, and Arakelov endpoint exactness.  Any Xi-indexed boundary target
  or zero-dependent polarization invalidates the claim.

## Falsifier

The conjecture is false if the strict homotopy fibre of `(1)` has any nonzero middle class.  Such
a class must be recorded explicitly as the cofinal Cauchy-descent anomaly; it cannot be removed by
Hilbert closure, since that would repeat the retired scalar-(L^2) route.

## Gates

- [x] 0 -> 1 in-progress: exact source object, consequence, attack, and falsifiers fixed
- [ ] 1 -> 2 fully-proven: construct `(1)` and prove endpoint-only strict fibre `(2)`
- [ ] 2 -> 3 formalized: instantiate the existing fibre-injectivity and Cauchy-descent theorems
- [ ] 3 -> 4 publication-ready: integrate with the global Calderon--Paugam comparison

## Log

- 2026-08-07 -- Rejected linear Bockstein/dagger and generic Hopf-cyclic producers.  Finite
  Calderon--Witt middle acyclicity relocates the Route-L producer to strict cofinal Cauchy
  recollement.  Froze endpoint-only homotopy fibre `(2)` and proved the exact three-term
  fibre-to-(H^1)-injectivity reduction.
