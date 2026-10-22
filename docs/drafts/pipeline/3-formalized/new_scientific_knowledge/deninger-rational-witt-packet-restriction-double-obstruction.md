# Rational-Witt packet restriction double obstruction

- **ID:** `deninger-rational-witt-packet-restriction-double-obstruction`
- **Stage:** 3-formalized
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Label:** `DAC_RATIONAL_WITT_PACKET_RESTRICTION_DOUBLE_OBSTRUCTION`
- **Parent:** `rh-current-frontier-map`, Route L
- **Scientific status:** `[NEW ARITHMETIC CONJUNCTION; LINEAR-ALGEBRA AND SUMMABILITY PARENTS STANDARD]`

## Problem

Route L now has exact finite rational-Witt evaluation on every prime packet and a faithful
all-prime Haar target.  Two superficially natural ways of producing the missing global comparison
are nevertheless wrong:

1. use the prime-packet component of the arithmetic residue differential as the Green
   restriction;
2. put raw rational-Witt coordinate functions into the global Bessel source with their literal
   packet evaluations.

The following theorem rules out both choices and identifies the exact survivor.

## Algebraic obstruction: residue cannot classify middle boundaries

Let
\[
 A^0\xrightarrow{d^0}A^1\xrightarrow{d^1}A^2,\qquad d^1d^0=0
 \tag{1}
\]
be a three-term complex over a field, and write
\[
 B^1=\operatorname{im}d^0,\qquad Z^1=\ker d^1,\qquad H^1=Z^1/B^1.
 \tag{2}
\]
For any linear map \(q:A^2\to K\), put \(r=q\,d^1\).

`[PROVED HERE] [DAC_RESIDUE_PACKET_KERNEL_NO_GO]`

If
\[
 \ker r=B^1,                                                       \tag{3}
\]
then \(H^1=0\).

Indeed, \(Z^1\subseteq\ker(qd^1)\).  Under `(3)` this gives
\[
 B^1\subseteq Z^1\subseteq B^1,
\]
so \(Z^1=B^1\).  Consequently, whenever the intended middle cohomology is nonzero, no
prime-packet projection of the degree-two residue differential can be the Route L Green
restriction.

The positive form is equally sharp.  If \(s:A^1\to K\) satisfies
\[
 s\,d^0=0,\qquad \ker s=B^1,                                     \tag{4}
\]
then \(s\) induces an injection
\[
 \bar s:A^1/B^1\hookrightarrow K,                                \tag{5}
\]
and hence an injection \(H^1\hookrightarrow K\).  If \(H^1\ne0\), such an \(s\) cannot factor
through \(d^1\).  Thus the missing packet map is necessarily a secondary degree-one restriction,
not the codimension-one residue already used to form the arithmetic fibre.

## Analytic obstruction: raw rational-Witt coordinates are not Bessel

Let \((K_p)_p\) be normed packet spaces and \(r_p:E\to K_p\) linear restrictions.  Suppose one
source vector \(x\in E\) has a cofinite norm floor
\[
 \|r_p x\|\ge\varepsilon>0.                                      \tag{6}
\]

`[PROVED HERE] [DAC_COFINITE_PACKET_NORM_FLOOR_NO_BESSEL]`

Then
\[
 \sum_p\|r_p x\|^2=\infty,                                       \tag{7}
\]
so the pointwise summability and global Bessel hypotheses of
`DeningerPrimeBlockRestrictionAssembly` fail.  If moreover
\(\|r_p x\|=1\) cofinitely, then
\[
 \sum_p {1\over(\log p)^2}\|r_p x\|^2=\infty,                    \tag{8}
\]
using the already-proved unconditional divergence of
\(\sum_p(\log p)^{-2}\).

This applies to the literal Teichmüller coordinate \([2]\).  For every odd prime \(p\), its
specialization is a nonzero element of \(\mathbb F_p^\times\).  Every unitary multiplicative
character sends it to a root of unity, so its continuous packet evaluation has pointwise modulus
one and normalized Haar-\(L^2\) norm exactly one.  Arithmetic Frobenius fixes \(2\in\mathbb F_p\),
so this function descends to the Frobenius quotient packet.  Therefore raw global rational-Witt
evaluation cannot be the Bessel comparison, even though finite local rational-Witt evaluations
are dense in each individual packet.

The obstruction survives realification: the squared norms of the real and imaginary parts add to
one.  It also survives insertion of the current Green coefficient, by `(8)`.

## Positive survivor

`[CONJECTURE] [DAC_SECONDARY_GRAPH_PACKET_RESTRICTION]`

The Route L comparison must be a map
\[
 s:\mathcal D^1_{\mathrm{rel}}\longrightarrow
 \ell^2\!\left(\mathbb P;L^2(\Gamma_p,\mathbb R)\right)           \tag{9}
\]
on a source-defined graph/nuclear degree-one domain with all of the following properties:

1. \(s\,d^0=0\);
2. \(\ker s=\overline{\operatorname{im}d^0}\);
3. \(s\) is not a factor of the residue differential \(d^1\);
4. the local range contains every finite Frobenius-fixed rational-Witt evaluation stage;
5. raw global Teichmüller coordinates such as \([2]\) are either outside
   \(\mathcal D^1_{\mathrm{rel}}\) or acquire source-derived square-summable damping;
6. the damping/domain comes from the relevant coefficient and transverse graph generator, not
   from a post hoc target norm.

Conditions 1--3 are forced by the algebraic theorem.  Conditions 4--5 separate local density from
global summability.  This is the first formulation compatible simultaneously with the constructed
arithmetic residue fibre, the finite rational-Witt admission theorem, and the all-prime Bessel
target.

## Theatre audit

- Local surjectivity at every prime does not imply one global Bessel map.
- The residue target already defines \(d^1\); reusing it as the Green restriction would force
  \(H^1=0\).
- Weighting packet evaluations by an arbitrary summable sequence preserves their kernel but is
  target-selected theatre.  The weight must be obtained from the source topology or flow.
- \(W_{\rm rat}\) supplies geometry and coordinate functions.  The class \([2]\) proves that those
  coordinates cannot all be degree-one Bessel vectors with literal normalization.

## Novelty audit

The linear-algebra and summability lemmas are standard.  The new claim is their arithmetic
conjunction with Deninger's Frobenius-quotient packets:

- prime residues and Green restrictions have provably different cohomological variance;
- finite local rational-Witt density is compatible with, but does not weaken, a global
  rational-Witt Bessel obstruction;
- the missing relevant coefficient must impose a secondary graph domain before packet assembly.

Targeted repository search and primary-source search found no statement of this conjunction.
Deninger's 2018 paper explicitly leaves the relevant complexes on the rational-Witt approximation
to be found; the 2025 rational-Witt sheaf paper supplies geometry and correspondences, not the
secondary Bessel domain.

## Gates

- [x] residue-factor kernel obstruction proved on paper
- [x] cofinite packet norm-floor obstruction proved on paper
- [x] unconditional Lean formalization
- [ ] source construction of `(9)`
- [ ] global Bessel estimate and exact kernel

## Lean certificate

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerRationalWittPacketRestrictionObstruction.lean`,
imported by `GaloisForLFunctions.RHTower`, formalizes:

- `deningerMiddlePacketMap` and `deningerMiddlePacketMap_injective`: `(4)` descends to the
  injection `(5)`;
- `deningerResidueFactoredPacket_kernel_eq_boundaries_forces_middle_subsingleton`: `(3)` forces
  trivial middle cohomology;
- `deningerPacket_not_summable_norm_sq_of_cofinite_floor`: `(6)` forces `(7)`;
- `deningerPacket_not_summable_graphGreenEnergy_of_cofinite_unit_norm`: cofinite unit norm forces
  `(8)`.

Direct `lake env lean`, targeted module build, and scratch `#print axioms` pass.  The declarations
use only `propext`, `Classical.choice`, and `Quot.sound`.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  https://arxiv.org/abs/1807.06400.
- Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  https://arxiv.org/abs/2508.05329.
- `DeningerArithmeticThreeTermCohomology.lean`
- `DeningerArithmeticThreeTermAssembly.lean`
- `DeningerPrimeBlockRestrictionAssembly.lean`
- `DeningerPrimeDiagonalGreenSummability.lean`
- `DeningerRationalWittFiniteEvaluationBridge.lean`

## Log

- 2026-08-01 — separated degree-two residue from the required secondary degree-one packet map and
  proved that raw global rational-Witt coordinates violate both unweighted Bessel summability and
  the current reciprocal-log-square Green summability.
