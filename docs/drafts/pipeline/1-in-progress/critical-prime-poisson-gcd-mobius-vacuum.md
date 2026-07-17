# Critical prime Poisson--GCD Möbius vacuum

- **ID:** `critical-prime-poisson-gcd-mobius-vacuum`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + source-producer candidate
- **Scientific status:** `[BRIDGE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Source:** critical local Euler factor, squarefree prime tensor, and the Gamma/Mertens boundary scale
- **Statement:** The squarefree critical prime tensor has normalized GCD Gram kernel,
  a canonical Möbius boundary vector of energy `product_p(1-1/p)`, and an antipodal phase whose
  relative energy grows at least on the `log log` scale; hence no scalar Gamma normalization can
  retain both the pointed vacuum and the full prime-phase fibre with uniformly comparable norms.

## Goal

Construct the prime part of a pointed source object before inserting Xi or its divisor.  The local
two-state Gram block at a prime `p` is

```text
K_p = [[1, p^(-1/2)], [p^(-1/2), 1]].
```

On squarefree integers supported on a finite prime aperture `S`, its tensor product is exactly

```text
K_S(n,m) = gcd(n,m)/sqrt(nm).
```

The desired RH producer would Gamma-sew a nonzero cofinal boundary of this carrier to the completed
theta source and prove that its source orientation is the Weil/Xi orientation.  The first gate is to
determine whether one scalar completion can retain the pointed Möbius vacuum and the transported
prime phases in one Hilbert realization.

## Finite source construction

Put `r_p=p^(-1/2)` and `v_p(z)=(1,-r_p z)`.  Give the two coordinate vectors the Gram block `K_p`.
For unit phases `z,w`, the local pairing is

```text
k_p(z,w)
 = 1 - p^(-1) w - p^(-1) conjugate(z)
     + p^(-1) conjugate(z) w.                              (1)
```

This is a positive kernel because it is the ordinary Gram kernel of

```text
phi_p(z)
 = (1-p^(-1)z, -sqrt(p^(-1)(1-p^(-1))) z) in C^2.          (2)
```

Tensoring `(1)` gives a canonical positive finite-prime kernel.  At the pointed phase `1`,

```text
k_p(z,1)=1-p^(-1)                                           (3)
```

for every unit phase `z`.  Thus every phase fluctuation is orthogonal to the pointed vacuum.  In
the squarefree basis the pointed vector has coefficients

```text
mu(n)/sqrt(n),
```

and the exact energy identity is

```text
||v_S(1)||^2 = product_(p in S) (1-p^(-1)).                 (4)
```

The GCD-matrix positivity is classical: Beslin--Ligh, *Linear Algebra Appl.* 118 (1989), 69--76,
DOI `10.1016/0024-3795(89)90572-7`; Guillot--Wu, *Linear Algebra Appl.* 578 (2019), 446--461,
DOI `10.1016/j.laa.2019.05.016`.  The source interpretation and the comparison below are the
project-specific content; no novelty claim is made for GCD positivity.

## Scalar-normalization obstruction

At the antipodal prime phase `z=-1`,

```text
k_p(-1,-1)=1+3p^(-1).                                      (5)
```

Consequently its energy relative to the pointed vacuum is

```text
D(S)
 = product_(p in S) (1+3/p)/(1-1/p)
 = product_(p in S) (1+4/(p-1)).                           (6)
```

For `S={p:p<=X}`, positivity and the first-order product bound give

```text
D(S) >= product_(p in S)(1+4/p)
     >= 1+4 sum_(p in S) 1/p
     >= 4 log log(X+1)-3.                                  (7)
```

Therefore any scalar normalization that keeps `(4)` bounded below forces the antipodal norm to
escape at least by `(7)`.  Conversely a normalization that bounds the antipodal fibre collapses the
pointed vacuum.  This is the finite quantitative form of the critical prime superselection screen.
It rules out the naive claim that Mertens/Gamma scalar renormalization alone constructs the joint
pointed transported Hilbert object.

## RH discriminator

The obstruction does not exclude a non-scalar completion.  A live source producer must do all of:

1. retain the Möbius vacuum as a boundary/corona vector;
2. transport prime phases in a genuinely different fibre, rather than forcing false norm
   comparability;
3. use the archimedean Gamma/theta source to sew those fibres by an unbounded operator or relative
   form;
4. identify the sewn relative orientation with the existing Weil/Xi critical kernel without
   inserting the Xi divisor as input.

`[CONJECTURE]` The correct completion is a rigged or relative Hilbert object: the pointed Möbius
vacuum lives in a boundary quotient, prime heights live in mutually singular phase sectors, and the
Gamma operator is an unbounded correspondence between them.  Its relative Schur complement, not an
ordinary common norm, is the candidate source producer for Weil positivity.

## Gates

- [x] 0 -> 1: source-pure finite kernel and exact RH discriminator isolated
- [x] local weighted-Gram realization and quantitative scalar-normalization obstruction proved on
  paper
- [x] Lean module
  `formal/GaloisForLFunctions/RHTower/CriticalPrimePoissonGCDMobiusVacuum.lean` proves the local
  Gram formula, pointed and antipodal energy laws, exact finite distortion factorization,
  prime-harmonic lower bound, and normalized-energy obstruction unconditionally
- [x] exact module build passed; capstone axiom audit contains only `propext`,
  `Classical.choice`, and `Quot.sound`
- [ ] prove and formalize the squarefree GCD tensor identity and Möbius coefficient evaluation
- [ ] construct a non-scalar Gamma/theta sewing and prove its relative orientation
- [ ] connect that source orientation to the existing unconditional RH endpoint
