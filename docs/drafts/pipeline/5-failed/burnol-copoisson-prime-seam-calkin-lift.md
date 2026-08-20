# Burnol co-Poisson prime-seam Calkin lift

- **ID:** `burnol-copoisson-prime-seam-calkin-lift`
- **Stage:** 5-failed
- **Type:** `[FALSIFIED RH ROUTE] [NO-GO AUDIT]`
- **Scientific status:** `[PROVED OBSTRUCTIONS] [CIRCULAR ENDPOINT] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:**
  `../2-fully-proven/not_new_scientific_knowledge/burnol-prime-dilation-copoisson-quotient-law.md`;
  the formal Sonin aperture covariance,
  time-band ideal, compressed Euler orientation, and prime-seam coherence collapse.
- **Statement:** The prime seam is the reflection split of the scalar by which normalized
  dilation acts on the Burnol zero-evaluation quotient.  Its divided-difference remainder is an
  explicit compactly supported co-Poisson source.  The remaining RH-sufficient theorem is to lift
  that source radical to the concrete Sonin time-band/Calkin ideal in the phase-polarized
  prime-pair curvature.

## 1. Exact dilation value relation

Let `K_a` be the cosine-Sonine space at aperture `a`, let

```text
fhat(s)=integral_0^infinity f(t)t^(-s)dt,
M(f)(s)=pi^(-s/2) Gamma(s/2) fhat(s)
```

be the right and completed Mellin transforms, and let `Z^a_(w,k)` denote the continuous completed
evaluation-jet vector.  Away from Gamma poles the completed and uncompleted jets differ by an
invertible triangular change.  For the normalized dilation

```text
(D_r f)(t)=sqrt(r) f(rt),   r>0,
```

direct substitution gives

```text
(D_r f)hat(s)=r^(s-1/2)fhat(s),
M(D_r f)(s)=r^(s-1/2) M(f)(s).                         (1)
```

The formal corpus already proves the geometric half of this statement: `D_r` sends the Sonin
carrier at aperture `a` into the carrier at aperture `a/r`.  Riesz duality and differentiation of
`(1)` therefore give the unconditional **projected** cross-aperture evaluator transport

```text
P_a D_r^* Z^(a/r)_(w,k)
 =conj(r^(w-1/2))
   sum_(j=0)^k binom(k,j)(log r)^(k-j) Z^a_(w,j),       (2)
```

with the conjugations adjusted if Burnol's analytic bilinear convention is used.  For `k=0`,

```text
P_a D_r^* Z^(a/r)_w=conj(r^(w-1/2)) Z^a_w.             (3)
```

The projection is essential: the Riesz calculation tests only vectors in `K_a`, so it determines
only the `K_a` component of the ambient adjoint vector.  This is a constraint relation between two
apertures, not an eigenvector statement for the fixed-aperture compression `P_a D_r P_a`.  The
uncontrolled part is the cross-aperture evaluator defect

```text
epsilon^+_(a,r,w)=(1-P_a)D_r^*Z^(a/r)_w.               (4)
```

Ignoring `(4)` is the false proof that would make every compressed dilation simultaneously
diagonal on the zeta-zero evaluators.

There is nevertheless an exact positive replacement.  The inverse dilation also sends `K_a`
into `K_(a/r)` for `r>1`, so its projected evaluator law defines the opposite defect

```text
epsilon^-_(a,r,w)=(1-P_a)D_r Z^(a/r)_w.
```

The forward/inverse Pythagorean comparison gives the bilateral defect-energy identity proved in
`../2-fully-proven/not_new_scientific_knowledge/burnol-bilateral-aperture-defect-energy-law.md`.
It detects `Re(w)-1/2` exactly, but does not by itself place either defect in the time-band ideal.
Burnol's orthogonal-complement theorem further replaces the family of zero-evaluator inequalities
by one source-defined compression order on the co-Poisson quotient; see
`../2-fully-proven/not_new_scientific_knowledge/burnol-copoisson-quotient-bilateral-order-rh-law.md`.
That shorter route bypasses the Calkin lift if its quotient order can be proved.

## 2. The prime seam is a reflected quotient eigenvalue split

Put

```text
lambda_p(s)=p^(s-1/2).
```

For every point `rho` in the open critical strip, the canonical formal prime-seam charge satisfies
the elementary exact identity

```text
a_p(rho)
 =log(p)(p^(-conj rho)-p^(-(1-rho)))
 =(log p)/sqrt(p)
    (lambda_p(1-conj rho)-lambda_p(rho)).               (5)
```

Thus the same scalar which transports the Burnol evaluator in `(3)` carries the RH orientation:
functional-equation--Schwarz reflection sends the quotient character at `rho` to the character at
`1-conj rho`, and the seam is their normalized difference.  Equation `(5)` does not itself prove
that the two values agree.  It identifies exactly which source quotient must become
reflection-unitary.

## 3. Exact co-Poisson divided difference

For one zero `rho`, consider in the uncompleted right-Mellin model the dual extended-Sonine zero
function

```text
G_rho(s)=zeta(s)/(s-rho)                                (6)
```

in the simple-zero notation.  Higher multiplicities use the standard confluent family.  Then

```text
(lambda_p(s)-lambda_p(rho))G_rho(s)
 =zeta(s) theta_(p,rho)(s),                             (7)

theta_(p,rho)(s)
 =(p^(s-1/2)-p^(rho-1/2))/(s-rho)
 =p^(rho-1/2) integral_0^(log p) exp((s-rho)u)du.       (8)
```

Consequently `theta_(p,rho)` is the Mellin--Laplace transform of the explicit source

```text
g_(p,rho)(x)=p^(rho-1/2) x^rho 1_[1/p,1](x)             (9)
```

with multiplicative Haar measure.  The co-Poisson/Muntz formula turns the right side of `(7)` into
a source-side summation vector generated by the compactly supported seed `(9)`, and its Mellin
transform vanishes on every zeta zero.  In
Burnol's extended Sonine space it lies in the closed co-Poisson complement of the zero evaluators.
Equivalently,

```text
lambda_p(s)G_rho(s)
 =lambda_p(rho)G_rho(s)  modulo the co-Poisson radical. (10)
```

For the vanishing Sonine space `K_a`, two pole/residue directions must be removed.  Burnol's
critical-aperture theorem does this by omitting two evaluation jets and replacing `(6)` with the
corresponding pole-cleared dual.  This is a finite-dimensional correction, hence harmless only
after an actual operator realization has been constructed; it may not be discarded at the vector
level by assertion.

## 4. Exact open Calkin lift

The formal tree already proves all downstream operator statements:

1. the actual Sonin projection equals its physical--Fourier complement modulo the concrete
   time-band ideal;
2. every element of that ideal is Hilbert--Schmidt, hence compact;
3. actual prime normal corners equal their principal corners modulo that ideal;
4. the prime-pair orientation Gram is the negative commutator of two compressed Euler sources;
5. its essential norm is the absolute prime-seam coefficient;
6. pairwise compactness forces prime-charge coherence, cofinal decay kills the common charge, and
   RH follows.

The remaining theorem is therefore not another zero-evaluation identity.  It is the following
operator lift.

`[CONJECTURE — CO-POISSON/TIME-BAND LIFT]` There is a source-defined operator realization `T_a`
of the extended Sonine co-Poisson summation vectors such that, for every Xi divisor point `rho` and
prime pair `p,q`, the phase-polarized divided-difference combination obtained from `(7)`--`(10)`
belongs to the concrete Sonin time-band ideal and has Calkin principal part

```text
(a_p(rho)-a_q(rho)) L_p^* L_q.                          (11)
```

It is enough to prove the weaker conclusion that the completed phase-polarized curvature is
compact and differs from `(11)` by the already formalized prime residuals.  Then

```text
co-Poisson/time-band lift
 -> prime-pair completed curvature compact
 -> a_p(rho)=a_q(rho) for all p,q
 -> common charge = 0
 -> Re(rho)=1/2
 -> RH.                                                 (12)
```

## 5. Why the available theorems do not yet prove the lift

- A co-Poisson vector being orthogonal to every zero evaluator is a Hilbert-space radical
  statement.  It does not imply that an operator made from that vector is compact.
- Compact multiplicative support of `(9)` does not by itself place an associated operator in the
  formal time-band ideal, whose generators are physical--Fourier cutoff products.
- Burnol's evaluator transport is projected and cross-aperture.  The fixed-aperture compression
  contains the defect `(4)`, and the relevant prime-pair cancellation is a relation among these
  defects.  The exact bilateral defect-energy law detects their norm imbalance but supplies no
  source-side reason for its RH-favorable sign.
- The analytic zero quotient admits nonunitary characters off the critical line.  Promoting its
  dilation action to a faithful positive or Calkin `*`-representation without proving `(11)` would
  restate the old Hilbertization gap.
- Connes--Consani finite quasi-innerness makes completed Hardy off-diagonal blocks compact, but it
  does not identify their zero-fibre mixed derivative with `(7)` or `(11)`.

The smallest research target is therefore explicit: construct `T_a` for the single interval
source `(9)`, calculate its physical--Fourier block factorization, and test whether the
antisymmetric two-prime combination cancels every term outside the time-band ideal.  No infinite
prime limit, zero enumeration, or limiting measure is needed at this stage.

## 6. Corpus interfaces

- `formal/GaloisForLFunctions/RHTower/SoninDeBrangesCarrier.lean`: completed Mellin holomorphy
  bricks;
- `formal/GaloisForLFunctions/RHTower/SoninEulerCalkinPartialIsometry.lean`: aperture covariance;
- `formal/GaloisForLFunctions/RHTower/SoninTimeBandIdeal.lean` and
  `SoninTimeBandHilbertSchmidt.lean`: the concrete compact ideal;
- `formal/GaloisForLFunctions/RHTower/SemilocalProjectionConstraintOrientation.lean` and
  `SemilocalProjectionPhasePolarization.lean`: curvature/commutator conversion;
- `formal/GaloisForLFunctions/RHTower/SemilocalCompressedEulerOrientation.lean`: finite Euler
  orientation commutator;
- `formal/GaloisForLFunctions/RHTower/XiPrimeSeamCalkinGram.lean` and
  `XiPrimeSeamCoherenceCollapse.lean`: exact Calkin consumer and RH endgame;
- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/sonin-prime-seam-exterior-factorization.md`:
  existing operator-side open core;
- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/ccm-bv-muntz-graph-domain-extension.md`:
  existing global Muntz graph-domain/zero-radical bridge.

## 7. Literature boundary

- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, J. Théor. Nombres Bordeaux 16 (2004), 65--94.  Theorem 3.1 identifies the extended
  co-Poisson complement; Theorem 3.2 and Propositions 6.5--6.6 give the zero-evaluator completeness
  transition in the vanishing Sonine spaces.
- A. Connes and C. Consani, *Spectral triples and zeta-cycles*, Enseign. Math. 69 (2023), 93--148.
  Lemma 6.1 and Theorem 6.4 supply the scale-invariant summation map and its zero-character
  annihilation.
- A. Connes, C. Consani, H. Moscovici, *Zeta zeros and prolate wave operators*, Ann. Funct. Anal.
  15 (2024), Art. 87.  The semilocal Hardy--Titchmarsh transform and Sonin-space construction provide the
  intended operator setting, but no co-Poisson/time-band lift of `(11)` is stated there.

## 8. Gates

- [x] exact normalized-dilation Mellin scalar `(1)`
- [x] exact **projected** cross-aperture evaluator transport `(2)`--`(3)`
- [x] correct orthogonal evaluator defect `(4)` retained
- [x] exact prime-seam spectral split `(5)`
- [x] exact compact-support divided-difference source `(7)`--`(9)`
- [x] zero-radical/co-Poisson quotient interpretation `(10)`
- [x] formal compact-ideal and prime-coherence consumers located
- [ ] construct the source-to-operator map `T_a` on `(9)`
- [ ] prove the two-prime phase-polarized remainder lies in the time-band ideal
- [ ] identify the Calkin principal part with `(11)`
- [ ] formalize Burnol evaluators and the lift only after the operator theorem is proved
- [ ] compose `(12)` to an unconditional Lean proof of RH

## 9. Canonical singular Euler graph of the interval source

The interval seed `(9)` does have a canonical bounded operator lift, and its first normal block is
compact for a source reason.  This closes the ambient analytic part of the `T_a` experiment, but
not the co-Poisson-radical-to-time-band implication.

Let `U_r` be normalized dilation on `L2(R)`,

```text
(U_r f)(x)=sqrt(r) f(r x),
M(U_r f)(s)=r^(s-1/2) M(f)(s),
```

let `L=log p`, `lambda=w-1/2`, and define `T_(p,w)` by its bounded Mellin multiplier

```text
theta_(p,w)(s)
 =(p^(s-1/2)-p^(w-1/2))/(s-w)
 =integral_0^L exp(lambda(L-u)) exp(u(s-1/2)) du.         (13)
```

Equivalently, as a strong integral,

```text
T_(p,w)=integral_0^L exp(lambda(L-u)) U_(exp u) du.       (14)
```

This is precisely multiplicative convolution by `(9)`.  Let `K=x d/dx+1/2`, the closed centered
Euler generator, whose Mellin multiplier is `s-1/2`.  Equation `(13)` proves:

```text
T_(p,w)(L2) subset Dom(K),
(K-lambda)T_(p,w)=U_p-p^lambda I.                        (15)
```

No formal interchange with an unbounded integral is needed: `(15)` follows from bounded Mellin
multipliers, since the right side is bounded.

### Compact normal block at every fixed Sonin aperture

Let `a>0`.  Let `A_a` and `R_a` be the physical and Fourier central-interval projections, let `Q_a` be the
actual Sonin intersection projection, and put

```text
Q_a^0=I-A_a-R_a,
C_a=Q_a-Q_a^0.                                           (16)
```

The corpus already proves `C_a` Hilbert--Schmidt.  The interval operator satisfies the new fixed
aperture statement

```text
S_(a,p,w)=(I-Q_a)T_(p,w)Q_a  is Hilbert--Schmidt.         (17)
```

It is enough to prove `(17)` with `Q_a^0`, because expansion using `(16)` changes the block by

```text
(I-Q_a^0)T C_a-C_a T Q_a^0-C_a T C_a,                   (18)
```

which is Hilbert--Schmidt.  The principal block expands exactly as

```text
(I-Q_a^0)T Q_a^0
 =A_a T(I-A_a)-A_a T R_a
  +R_a T(I-R_a)-R_a T A_a.                              (19)
```

Every term in `(19)` is Hilbert--Schmidt:

1. `A_a T(I-A_a)` has multiplicative kernel

   ```text
   1_(same sign, 1<=|y/x|<=p)
   exp(lambda(L-log|y/x|))/sqrt(|x y|),                  (20)
   ```

   and its support after the two cutoffs lies in the finite shell
   `a/p<=|x|<=a<|y|<=pa`.
2. Fourier conjugation sends `U_(exp u)` to `U_(exp(-u))`, so the same shell calculation proves
   `R_a T(I-R_a)` Hilbert--Schmidt.
3. `A_a T R_a` is the strong integral of finite physical--Fourier time-band blocks
   `A_a U_(exp u)R_a`; their Hilbert--Schmidt norms are uniformly bounded for `0<=u<=L`.
4. `R_a T A_a` follows by the reflected calculation, or by adjointing the preceding block for
   `T^*`.

Thus `(17)` is a genuine compact-source operator theorem, not the false inference that an arbitrary
co-Poisson radical vector induces a compact operator.

### The principal part survives as an unbounded graph boundary

Despite `(17)`, applying the Euler graph derivative before the outer projection gives

```text
(I-Q_a)(K-lambda)T_(p,w)Q_a
 =(I-Q_a)U_p Q_a.                                        (21)
```

The scalar term in `(15)` vanishes across the projection.  The right side is the one-sided prime
dilation corner; its principal Sonin Calkin component is noncompact.  Hence the interval source
has exactly the singular behavior required of a Laurent/conormal connector:

```text
compact normal block S_(a,p,w)
  --Euler graph boundary--> noncompact prime corner.      (22)
```

This avoids the failure of the logarithmic Rademacher graph, whose completion subtracted the
principal part.

### Honest remaining gap

Equations `(13)`--`(22)` do **not** prove `(11)`.  They lift the compact interval seed to an
operator graph, but Burnol's relation

```text
zeta(s) theta_(p,rho)(s) lies in the co-Poisson radical
```

is still a vector/subspace statement.  What remains is now narrower: prove that the
phase-polarized two-prime combination of these singular graph blocks sends that radical relation
to a compact operator (or to the concrete time-band ideal), with graph boundary exactly `(11)`.
No passage from the radical to operator compactness has been assumed.

### Status and novelty audit

- Corpus research found the interval divided difference and the time-band Hilbert--Schmidt
  machinery separately, but not `(13)`--`(22)`.
- Targeted primary-literature search found standard continuous-Hankel/Hilbert--Schmidt facts, but
  no Burnol interval-source/Sonin Euler-graph synthesis.
- Scientific status: elementary source-specific operator synthesis, not new significant
  mathematics; not an RH proof.
- The live RH edge remains the radical-to-phase-curvature implication, not construction of another
  abstract graph.

## Gates after the singular-graph audit

- [x] construct canonical interval-seed convolution operator `(13)`--`(14)`
- [x] prove exact Euler graph endpoint identity `(15)`
- [x] prove fixed-aperture compact normal block `(17)` by the physical--Fourier decomposition
- [x] retain the noncompact prime-corner boundary `(21)`
- [ ] prove co-Poisson radical relation makes the two-prime phase curvature compact
- [ ] identify its Calkin boundary with `(11)`
- [ ] compose `(12)` to RH and only then formalize the new paper theorem

## 10. Zero-order Calkin opacity and the surviving conormal target

The singular graph in Section 9 does not itself transmit the zero-fibre character to the Calkin
boundary.  This is an exact obstruction, not merely a missing estimate.

Let `pi_C` denote the quotient map to the Calkin algebra and write

```text
S_(p,w)=(I-Q_a)T_(p,w)Q_a,
B_(p,w)=(I-Q_a)(K-(w-1/2))T_(p,w)Q_a.
```

Equations `(17)` and `(21)` give

```text
pi_C(S_(p,w))=0,
B_(p,w)=(I-Q_a)U_p Q_a.                                 (23)
```

In particular, the second class is independent of `w`.  Hence every noncommutative polynomial
in finitely many `S_(p,w)`, `S_(p,w)^*`, `B_(p,w)`, and `B_(p,w)^*`, with coefficients independent
of `w`, has Calkin class independent of `w`: every monomial containing an `S` dies, and every
surviving monomial contains only the `w`-independent `B` classes.  In particular the literal
reflection polarization

```text
pi_C(B_(p,w#)^*B_(q,w)-B_(p,w)^*B_(q,w#))=0             (24)
```

for `w#=1-conj(w)`.  It cannot equal the desired generally nonzero class

```text
(a_p(w)-a_q(w)) pi_C(L_p^*L_q).                         (25)
```

Thus compactness of the interval normal block plus the first Euler graph boundary cannot prove
the open Calkin lift.  Any successful construction must introduce the spectral coefficient
outside the zero-order compact block.  Merely renaming a polynomial in `(23)` as a
`phase-polarized curvature` would be circular.

There is one exact positive survivor.  Let `Lambda` be the completed co-Poisson multiplier and
`I=(Lambda)`.  The already formalized principal-source normal derivative factors through
`I/I^2`:

```text
[Lambda g] |-> [Lambda' g] in A/I.                      (26)
```

For the divided-difference seed,

```text
theta_(p,w)(w)=log(p) p^(w-1/2).                        (27)
```

Therefore its FE--Schwarz reflected conormal diagonal is exactly the prime seam:

```text
(theta_(p,w#)(w#)-theta_(p,w)(w))/sqrt(p)
 =log(p)/sqrt(p) (p^(w#-1/2)-p^(w-1/2))
 =a_p(w).                                               (28)
```

Unlike `(23)`, `(26)`--`(28)` retain the required spectral dependence.  The corrected open core is
therefore not another bounded interval-operator calculation.  It is construction of a
source-defined Calkin-valued conormal boundary map

```text
N_a : I/I^2 -> Calkin(H)                                (29)
```

compatible with the Sonin normal corner and completed prime--Gamma pairing, such that the
reflection-antisymmetric image of `(27)` has principal class `(25)` and the completed source
relation makes that image zero.  The corpus contains the algebraic conormal map `(26)` and the
operator Calkin target separately, but no map `(29)`.

This audit downgrades `(13)`--`(22)` to route-local analytic plumbing.  It is not a frontier
advance.  The only frontier-sized statement is the still-unproved arithmetic conormal-to-Calkin
descent `(29)` together with its completed-source vanishing law.

## Gates after the opacity audit

- [x] prove zero-order singular-graph Calkin opacity `(23)`--`(25)`
- [x] identify the reflected co-Poisson conormal diagonal with the seam `(26)`--`(28)`
- [ ] construct the arithmetic Calkin-valued conormal boundary map `(29)`
- [ ] prove completed-source vanishing of its two-prime reflected curvature
- [ ] compose the resulting compactness theorem to `(12)`, RH, and only then Lean

## 11. Rank-one conormal obstruction to the naive map

Map `(29)` is still too optimistic if `N_a` is required to be a local `A/I`-module map.  At any
divisor point `w`, the fibre

```text
(I/I^2) tensor_(A/I) C_w
```

is one-dimensional, generated by the class of `Lambda`.  This remains true at a multiple point:
the principal conormal module is locally rank one even though the divisor scheme is nonreduced.
Thus every complex-linear fibre map has the form

```text
N_(a,w)([Lambda g])=g(w) C_(a,w)                        (30)
```

for one fixed Calkin class `C_(a,w)`.

If `(29)` were to produce the required prime-labelled normal directions, equations `(27)` and
`(30)` would require

```text
log(p)p^(w-1/2) C_(a,w)
 =log(p)p^(w-1/2) pi_C(L_p)                             (31)
```

for every prime `p`.  The scalar is nonzero, so `(31)` forces

```text
C_(a,w)=pi_C(L_p) for every p.                           (32)
```

This contradicts the corpus theorem `finiteDilationCorners_calkinIndependent`: distinct
prime-dilation Sonin corners are linearly independent modulo compact operators.  The same
obstruction applies to the positive Euler corners by the formal finite Euler Calkin independence
theorem.

Therefore no local fibrewise `A/I`-linear conormal map from the single principal zeta ideal can
produce the prime-indexed Calkin frame.  The scalar conormal derivative `(26)` correctly extracts
the seam coefficient, but it has insufficient operator rank.

The strongest positive survivor is now exact.  A viable source object must retain both:

1. the principal co-Poisson conormal grade, which supplies the scalar in `(28)`; and
2. an independent prime-labelled normal module, for example

   ```text
   directSum_p (I/I^2) e_p,                              (33)
   ```

   together with a completed-source relation coupling the `e_p`.

Equivalently, the required boundary may be a genuinely nonlocal map which is not a morphism from
the local principal conormal fibre.  Merely declaring `(29)` to be module-linear is impossible.
The open mathematics is the arithmetic coupling on the decorated module `(33)` which makes its
reflected two-prime Gram compact; the scalar conormal and Calkin frame separately already exist.

## Gates after the rank audit

- [x] refute a local fibrewise module-linear map `(29)` by conormal rank one versus finite Calkin
  independence
- [x] isolate the minimal decorated source module `(33)`
- [ ] construct a completed prime--Gamma/co-Poisson coupling on `(33)` without inserting zero
  locations or seam coherence
- [ ] prove its reflected Gram descends to a compact Calkin class
- [ ] compose to RH and only then Lean

## 12. Collision audit: the decorated module already exists

The prime-labelled replacement `(33)` is not new.  The corpus's finite semilocal Euler chart
already has independent parameters `a_p`, with tangent directions `partial_(a_p)`, and
`semilocal-dual-pair-euler-connection-source-law.md` identifies the arithmetic contraction

```text
-sum_p log(p) partial_(a_p).
```

Its projection derivatives are the actual Sonin prime normals, and the formal phase-polarization
theorems already convert their mixed curvature to the Calkin-independent prime Gram.  Thus
Sections 10--11 do not expose a new construction route; they recover the exact existing split:

```text
principal co-Poisson conormal
  -> scalar FE--Schwarz seam,

independent semilocal Euler tangents
  -> prime-labelled Sonin Calkin frame.
```

The missing arrow is still the previously recorded one: a completed source--divisor theorem must
couple those two structures so that the Xi-zero radical kills the tangential connection term and
leaves compact reflected normal curvature.  Neither the interval graph nor principal conormal
module supplies that coupling.

Consequently no result in Sections 9--11 moves the mathematical frontier.  Section 9 is elementary
operator plumbing; Sections 10--11 are route closures; Section 12 identifies their collision with
existing corpus interfaces.  Further work on this lane is justified only by a concrete proof or
counterexample for the completed source--divisor coupling, not by additional repackaging.

## 13. The remaining modulo-compact value relation is exactly the RH endpoint

The final hostile audit closes the apparent survivor.  Let `pi_C` be the Calkin quotient, let
`G_rho` denote the charge-weighted finite Sonin orientation Gram on an actual Xi divisor fibre,
and let `K_rho` be the mixed derivative of a finite completed quasi-inner Hardy block.  The
proposed source--divisor relation has the form

```text
G_rho = K_rho modulo compact operators.                 (34)
```

Finite quasi-innerness and norm differentiability imply that `K_rho` is compact.  Therefore

```text
pi_C(G_rho)=pi_C(K_rho)=0
```

and conversely compactness of `G_rho` makes `(34)` true modulo compacts for every compact
`K_rho`.  Thus `(34)` contains no intermediate Calkin-level value information:

```text
(34) iff G_rho is compact.                              (35)
```

The formal theorem
`xiPrimeTwoThreeEulerOrientationGramCompact_iff_riemannHypothesis` already proves that
compactness of this fixed two-prime Gram on every Xi fibre is equivalent to RH.  Consequently the
remaining equation is not an independently specified source identity whose known properties
force RH; after passage to the stated quotient it is exactly the RH endpoint.

The divisor radical does not repair this circularity.  For a principal divisor `I=(Lambda)`,
the formal conormal law is

```text
D(Lambda g) mod I = (D Lambda)g mod I.                  (36)
```

At a simple zero the surviving coefficient is `Lambda'(rho)g(rho)`, generally nonzero.  Hence
zero specialization kills the tangential multiple of `Lambda` but preserves, rather than
annihilates, the transverse normal class.  Turning that class into compact reflected prime
curvature would require exactly the missing RH-selecting assertion.

No checked primary source supplies a pre-specialization operator identity that could replace
`(34)`.  Connes--Consani prove compactness of finite completed quasi-inner off-diagonal blocks;
Connes--Consani--Moscovici prove semilocal Sonin stability; Burnol supplies zero and jet
evaluators.  None identifies a compact differentiated Hardy block with the charge-weighted
noncompact Sonin normal Gram before imposing the divisor fibre.

### Route verdict

- `[FALSIFIED]` The interval singular graph has zero-order Calkin class independent of the
  spectral parameter.
- `[FALSIFIED]` A principal conormal module cannot produce independent prime-labelled Calkin
  directions.
- `[CIRCULAR]` The remaining modulo-compact coupling is equivalent to the already formalized
  Calkin RH criterion.
- `[NO POSITIVE SALVAGE FOUND]` The scalar conormal seam and semilocal prime frame are useful
  structures, but both predate this card and their juxtaposition yields no new theorem.

Further work must change representation and provide a source-side identity before zero
specialization whose content is neither compactness of `G_rho` nor an equivalent seam equality.
