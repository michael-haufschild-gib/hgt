# Arithmetic Xi--Stokes central rank-port law

- **ID:** `arithmetic-xi-stokes-central-rank-port-law`
- **Stage:** 3-formalized
- **Type:** BRIDGE / ARITHMETIC REALIZATION / VANISHING AND SCALING LAW / NO-GO CLOSURE
- **Upstream:** `arithmetic-xi-stokes-rank-port-realization.md`
- **Target manuscript:** `../4-publication-ready/polarized-stokes-microlocal-witt-law/`
- **Novelty label:** `[BRIDGE]`.  Scalar twists and determinant weights are standard separately.
  New claim is restricted to their exact identification with the coefficient-generated Stokes
  one-port functional and the certified rational-adelic Xi transgression, together with the
  reflection-product factorization and rank-renormalized Mertens three-regime theorem.

## 1. Setup

Let `A` be a nonempty finite equivariant Puiseux spectrum.  Let `I` be its set of cyclic
continuation orbits.  For `i in I`, let

```text
r_i = |i| > 0,
V_i = C^(r_i),
M(x) = sum_i r_i x_i.
```

For distinct orbit classes `i,j`, every pair `(a,b) in i x j` consists of distinct coefficient
vectors.  Hence its highest-difference numerator is positive, and therefore

```text
s_ij = sum_(a in i,b in j) h(a,b) > 0.              (1.1)
```

Thus the graph whose edges are nonzero mixed Hom irregularities is complete when `|I|>1` and is
connected in every case.

Let `T_i in GL(V_i)` be the ordinary/formal monodromy part of any Stokes datum with this formal
type.  For nonzero scalars `lambda_i`, define its scalar twist by

```text
T_i^lambda = lambda_i T_i.
```

The induced transport on a mixed Hom channel is

```text
f |-> T_j^lambda f (T_i^lambda)^(-1)
   = (lambda_j/lambda_i) T_j f T_i^(-1).           (1.2)
```

Call the scalar tuple Hom-invisible when (1.2) equals the untwisted transport on every nonzero
mixed Stokes/Hom channel.

## 2. Connected central-twist classification

### Theorem 2.1 (unique channel-invisible central twist)

For the coefficient-generated Stokes datum above, a nonzero scalar tuple is Hom-invisible if and
only if there is one `lambda in C^x` with

```text
lambda_i = lambda  for every i in I.               (2.1)
```

For an integral physical dimension vector `x in N^I`, the common twist acts on the determinant
line of

```text
V(x) = directSum_i V_i^(x_i)
```

by the scalar

```text
lambda^(M(x)).                                      (2.2)
```

Consequently the same linear form `M` has two independent characterizations:

1. it is the sole possibly nonpositive port in the Stokes coarea polarization;
2. it is the determinant weight of the unique connected scalar twist invisible to every relative
   Stokes/Hom channel.

#### Proof

If the tuple is Hom-invisible, (1.2) gives `lambda_j/lambda_i=1` on every edge: choose any nonzero
mixed-Hom vector and cancel the invertible untwisted transport.  By (1.1), every distinct pair is
an edge, so all `lambda_i` are equal.  The one-orbit case is immediate.  Conversely, a common
scalar cancels between target and source in (1.2), so every mixed channel is fixed.

For one block,

```text
det(lambda T_i) = lambda^(r_i) det(T_i).
```

Taking `x_i` direct-sum copies and multiplying determinants gives

```text
prod_i lambda^(r_i x_i)
  = lambda^(sum_i r_i x_i)
  = lambda^(M(x)).
```

The coefficient-generated coarea theorem independently identifies exactly the same
`M(x)=sum_i r_i x_i` in `Q=P-lambda_0 M^2`, with `P>0`.  This proves both characterizations.  No
zero of Xi and no vanishing premise occurs.  QED.

### Theorem 2.2 (universal component refinement)

For an arbitrary directed mixed-channel relation `E` on a finite Stokes block set, a scalar tuple
is invisible on every edge if and only if it is constant on the equivalence closure of `E`.  If
components are labelled by `alpha`, determinant response factors as

```text
prod_i lambda_[i]^(r_i x_i)
  = prod_alpha lambda_alpha^(sum_(i in alpha) r_i x_i).       (2.3)
```

Thus disconnected data have one central determinant port per component.  The unique-port claim is
sharp and follows for coefficient-generated data because (1.1) makes their graph complete.

#### Proof

Edge invisibility in (1.2) gives equality of endpoint scalars.  Equality propagates along the
reflexive, symmetric, transitive closure, and componentwise constants cancel on every edge.
Regroup the product of block determinant ratios by component to obtain (2.3).  QED.

## 3. Why arithmetic cannot live in physical rank or formal contact

### Proposition 3.1 (typing and contact-stratum no-go)

The continuous scalar `delta_n(s)-1` cannot be the physical rank of an object in a fixed
finite-length Stokes category on a connected parameter family.  It also cannot be recovered from
the coefficient-generated Cartan/coarea datum alone.

#### Proof

Physical dimension vectors and their `K_0` classes are integral; exact functors induce integral
maps and a continuous family of such discrete classes is locally constant.  For `n>=2`,

```text
delta_n(s)-1 = exp((2 Re(s)-1) log n)-1
```

is nonconstant in `Re(s)`.

For the second claim, all coefficient-generated contacts use only

```text
k(a,b) = max { k : c_(a,k) != c_(b,k) }.
```

Any deformation preserving the equality/non-equality pattern of coefficients at every exponent
preserves every `k(a,b)`, hence every threshold partition, persistence length, mixed Hom
irregularity, coarea form, capacity, and Rees/corona dimension.  Nonzero coefficient magnitudes
may vary continuously inside such a stratum.  Therefore the arithmetic clock `log n` is invisible
to bare formal-contact data.  QED.

This no-go forces arithmetic into monodromy/extension data over the fixed Stokes skeleton.  Theorem
2.1 then forces every relative-channel-invisible scalar realization into the unique common center.

## 4. Pre-divisor arithmetic central character

For `n>=2` and any `s in C`, define

```text
delta_n(s) = exp((2 Re(s)-1) log n) > 0.            (4.1)
```

Let `L_(n,s)` be the rank-one Betti local system on the boundary circle represented by

```text
chi_(n,s) : Z -> R_(>0),
chi_(n,s)(k) = delta_n(s)^k.                        (4.2)
```

Tensor every Stokes block by `L_(n,s)`.  Equivalently, set

```text
T_i^(n,s) = delta_n(s) T_i.                         (4.3)
```

### Theorem 4.1 (arithmetic rank-port realization)

The family (4.2)--(4.3) is defined before any Xi divisor is selected and has all of the following
properties.

1. It fixes every exponential-factor difference, analytic Stokes wall, mixed Hom transport,
   directed microstalk mass, contact cut, coarea polarization, Rees specialization, and capacity.
2. Its determinant response on dimension vector `x` is

   ```text
   delta_n(s)^(M(x)).                               (4.4)
   ```

3. It is multiplicative in the arithmetic clock:

   ```text
   delta_(mn)(s) = delta_m(s) delta_n(s)            (m,n>=1).
   ```

4. Critical reflection dualizes the local system:

   ```text
   delta_n(1-conj(s)) = delta_n(s)^(-1).            (4.5)
   ```

5. Among scalar twists invisible to all mixed channels, it is the unique twist with monodromy
   `delta_n(s)` on one, hence every, Stokes block.

#### Proof

A common regular-singular/Betti scalar twist adds no irregular exponential term, so exponential
differences and their phase walls are unchanged.  Equation (1.2) cancels the common scalar on
every Hom channel; all coefficient, microstalk, coarea, Rees, and capacity invariants are functions
of those unchanged differences and ranks.  Formula (4.4) is Theorem 2.1.

Multiplicativity follows from `log(mn)=log m+log n` for positive integers and additivity of the
exponent.  Since

```text
2 Re(1-conj(s))-1 = -(2 Re(s)-1),
```

(4.5) follows from `exp(-a)=exp(a)^(-1)`.  Uniqueness is Theorem 2.1.  QED.

## 5. Xi jet and rational-adelic residue realization

Let `rho` be a nontrivial Xi divisor point, `r_rho` its multiplicity, and

```text
c_rho = XiC^(r_rho)(rho) != 0                       (5.1)
```

its first nonzero jet.  Let `C_1(A_CCM)` be the literal degree-one cyclic bar of the rational-adelic
source, `tau` its cyclic rotation, and `epsilon_0^(1)` its zero-adele cyclic trace.  For every
ordinary prime `p`, the source cycle `u_p` labelled by `p` and `p^(-1)` satisfies

```text
epsilon_0^(1)(u_p) = 1.                             (5.2)
```

Land a source chain `x` on the Xi jet line by

```text
j_rho(x) = c_rho epsilon_0^(1)(x).                  (5.3)
```

The arithmetic local system acts on this line by holonomy `delta_n(rho)`.  Its holonomy defect is

```text
(Hol(L_(n,rho))-1) j_rho(x)
 = (delta_n(rho)-1)c_rho epsilon_0^(1)(x).          (5.4)
```

### Theorem 5.1 (Xi source transgression equals central holonomy defect)

For the certified physical two-leg paracyclic comparison `D_(n,rho)` and cyclic residue `Res`,

```text
Res(D_(n,rho)x)
  = (Hol(L_(n,rho))-1) j_rho(x)                    (5.5)
  = (delta_n(rho)-1)c_rho epsilon_0^(1)(x).
```

On every ordinary-prime trace-one cycle,

```text
Res(D_(n,rho)u_p) = (delta_n(rho)-1)c_rho.          (5.6)
```

For `n>=2`, this vector vanishes exactly when `Re(rho)=1/2`.  Vanishing at every Xi divisor point
is equivalent to RH, but no such global vanishing is asserted.

#### Proof

The literal rational-adelic source computation gives (5.2).  Cyclic trace invariance kills the
untwisted two-leg comparison defect.  The physical paracyclic rotation squares to and contributes
the mate gain `delta_n(rho)` on the second leg.  Taking coordinate-sum residue therefore gives
the already proved transgression on the right of (5.5).  By (4.2), that scalar is exactly
holonomy-minus-identity on (5.3), proving the first equality.  Equation (5.6) follows from (5.2).

For `n>=2`, `log n>0`, so `delta_n(rho)=1` iff `2 Re(rho)-1=0`.  The coefficient (5.1) is nonzero;
hence (5.6) vanishes exactly on the critical line.  Quantifying over Xi support is the definition
of the RH divisor condition.  QED.

### Theorem 5.2 (rank-powered determinant transgression)

Let `x` be an integral Stokes dimension vector and `M(x)=sum_i r_i x_i`.  For every positive
integer `n`,

```text
delta_(n^M(x))(s) = delta_n(s)^M(x).                         (5.7)
```

Consequently the physical source comparison at clock `n^M(x)` satisfies

```text
Res(D_(n^M(x),rho) y)
  = (delta_n(rho)^M(x) - 1)c_rho epsilon_0^(1)(y).            (5.8)
```

The multiplier is exactly holonomy minus identity on the determinant line of the central Stokes
twist.  On a trace-one prime cycle it is `(delta_n(rho)^M(x)-1)c_rho`; for `n>=2` and `M(x)>0`,
it vanishes exactly on the critical line.

#### Proof

Iterate multiplicativity in (4.1), or expand the real exponential, to obtain (5.7).  Apply Theorem
5.1 with clock `n^M(x)` and substitute (5.7).  The determinant interpretation is (2.2).  Since
`c_rho != 0` and exponent `M(x) log n` is positive, equality of the positive real exponential to
one is equivalent to `2 Re(rho)-1=0`.  QED.

## 6. Reflection-paired prime vanishing and Mertens scaling

For `s^vee = 1-conj(s)` and a positive physical rank `M`, define the normalized real defect

```text
a_(p,M)(s) = delta_p(s)^M - 1
```

and the cutoff prime energy

```text
E_(N,M)(s) = -sum_(p<=N) a_(p,M)(s) a_(p,M)(s^vee) / p.     (6.1)
```

At a Xi divisor, Theorem 5.2 identifies each `a_(p,M)` with the rank-powered cyclic residue on
the trace-one prime cycle divided by its nonzero leading Xi jet.

### Theorem 6.1 (Stokes--Mertens reflection and vanishing law)

For every positive integer `M`:

```text
E_(N,M)(s)
  = sum_(p<=N) 4 sinh^2(M (Re(s)-1/2) log p) / p >= 0.       (6.2)
```

If `N>=2`, then

```text
E_(N,M)(s)=0  iff  Re(s)=1/2.                                (6.3)
```

For an arbitrary sequence `s_N`, put `c_N=M(Re(s_N)-1/2)log N`.  Then

```text
c_N -> 0       implies E_(N,M)(s_N) -> 0;
c_N -> c in R  implies E_(N,M)(s_N) -> Phi(c);
|c_N| -> oo    implies E_(N,M)(s_N) -> oo,                   (6.4)

Phi(c)=4 int_0^1 sinh^2(cu)/u du.
```

The profile is even and strictly positive away from zero.  After the forced scaling, it is
independent of every Stokes rank, contact coefficient, and ramification pattern except through
the single port `M`, which has been absorbed into `c_N`.

#### Proof

Reflection gives `delta_p(s^vee)^M=delta_p(s)^(-M)`.  With `g=delta_p(s)^M`,

```text
-(g-1)(g^(-1)-1)=g+g^(-1)-2
                   =4 sinh^2(M(Re(s)-1/2)log p),
```

which proves (6.2).  For `N>=2`, all summands are nonnegative and the `p=2` summand vanishes only
when `M(Re(s)-1/2)log 2=0`; positivity of `M` proves (6.3).

Let `S_N=sum_(p<=N)(log p)^2/p`.  Mertens's first theorem in prime form,
`sum_(p<=x)(log p)/p=log x+O(1)`, and partial summation give

```text
S_N = (1/2)(log N)^2 + O(log N).                              (6.5)
```

Writing `epsilon_N=M(Re(s_N)-1/2)`, the elementary bounds
`|u|<=|sinh u|` and `|sinh u|<=|u|cosh C` for `|u|<=C` yield

```text
4 epsilon_N^2 S_N <= E_(N,M)(s_N)
  <= 4 cosh^2(C) epsilon_N^2 S_N       when |c_N|<=C.         (6.6)
```

Equations (6.5)--(6.6) prove the zero and divergent regimes.  For fixed `c`, the measures

```text
nu_N = (1/log N) sum_(p<=N) (log p)/p delta_(log p/log N)
```

converge weakly to Lebesgue measure on `[0,1]`, again by Mertens and partial summation.  Testing
against the continuous extension of `4 sinh^2(cu)/u` proves the middle limit for fixed `c`.
For `c_N->c`, the mean-value theorem bounds the difference by
`K|c_N-c|S_N/(log N)^2`, which tends to zero.  Positivity of `Phi` is immediate from the
integrand.  QED.

This is a genuine finite vanishing theorem and a number-theoretic scaling theorem.  It is not a
global theorem that (6.3) holds for every Xi divisor; that assertion remains RH.

## 7. Exact defect diagram

The arithmetic realization is summarized by

```text
degree-one rational-adelic source  --j_rho-->  first Xi jet line
             | D_(n,rho)                          | Hol(L_(n,rho))-1
             v                                    v
physical two-leg defect           --Res---->  first Xi jet line.
```

The failure of the square to commute has residue exactly
`(Hol(L_(n,rho))-1)j_rho`, by Theorem 5.1.  The top source and the family `L_(n,s)` are
pre-divisor.  Divisor specialization enters only through the first nonzero Xi jet.

## 8. Hostile audit

- This is not `delta_n(s)-1` renamed as rank.  Rank remains integral; arithmetic is central
  monodromy, and `M` is its independently forced determinant exponent.
- This is not coefficient insertion.  Formal-contact data are unchanged and cannot recover
  `log n`; arithmetic lives in the unique Hom-invisible central local system.
- This is not an irregular Riemann--Hilbert existence claim.  It constructs the Betti Stokes
  datum explicitly.  Any de Rham realization is external to this theorem and unnecessary for
  (2.1)--(5.6).
- This is not a new RH proof.  It identifies the only channel in which the certified arithmetic
  obstruction can live.  A theorem forcing its global triviality would still be exactly the open
  source-null-homology/RH step.
- The reflection energy is not positivity smuggled in as annihilation.  It has an exact finite
  vanishing locus and a Mertens scaling law, but supplies no reason every Xi divisor must lie in
  that locus.
- The theorem is false without connectedness: one common scalar survives on each connected mixed
  Hom component, producing one determinant port per component.  Coefficient-generated spectra
  avoid this failure because (1.1) makes the interaction graph complete.

## 9. Formalization closure

Module `GaloisForLFunctions.RHTower.ArithmeticXiStokesCentralRankPort` certifies:

1. connected/complete mixed-channel scalar classification;
2. common scalar cancellation on Hom transport;
3. determinant scaling by `M`;
4. arithmetic mate-gain multiplicativity and reflection inversion (reusing existing theorems);
5. equality of the certified source transgression with the central holonomy defect;
6. trace-one Xi specialization and exact zero classifier;
7. reflection-defect product factorization;
8. finite prime-energy vanishing iff criticality;
9. subcritical, critical-window, and supercritical Mertens regimes.

No axiom, `sorry`, `admit`, `opaque`, `unsafe`, RH assumption, or global vanishing theorem is
used. Targeted module build passes; axiom report contains only `propext`, `Classical.choice`, and
`Quot.sound`.

## Formal audit

- Module: `GaloisForLFunctions.RHTower.ArithmeticXiStokesCentralRankPort`
- Targeted source check: `lake env lean GaloisForLFunctions/RHTower/ArithmeticXiStokesCentralRankPort.lean` — PASS
- Module build: `lake build GaloisForLFunctions.RHTower.ArithmeticXiStokesCentralRankPort` — PASS
- Axiom audit: every public theorem uses only `propext`, `Classical.choice`, `Quot.sound`
- Forbidden declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- Umbrella: imported by `GaloisForLFunctions/RHTower.lean`

Declaration map for the nine closure items of section 9:

```text
1. scalarHomTransport_invisible_iff_componentwise,
   PuiseuxOrbitCoareaDatum.scalarTwistInvisible_iff_constant,
   PuiseuxOrbitCoareaDatum.normalizedHomIrregularity_pos_of_ne;
2. scalarHomTransport_const;
3. commonScalar_determinantWeight, componentScalar_determinantWeight, scalarTwist_det;
4. centralHolonomyDefect_mul_clock, centralHolonomy_reflection, centralHolonomy_pow_clock;
5. ccmXiResidue_eq_centralHolonomyDefect,
   ccmXiResidue_rankPortClock_eq_determinantCentralHolonomyDefect;
6. ccmXiPrimeResidue_eq_centralHolonomyDefect,
   ccmXiPrimeCentralHolonomyDefect_eq_zero_iff,
   ccmXiPrimeDeterminantCentralHolonomyDefect_eq_zero_iff;
7. determinantCentralGainDefect_reflection_product,
   stokesRankPortPrimeEnergy_eq_reflectionDefectSum;
8. stokesRankPortPrimeEnergy_eq_zero_iff;
9. tendsto_stokesRankPortPrimeEnergy_zero_of_scaled_tendsto_zero,
   tendsto_stokesRankPortPrimeEnergy_critical_profile,
   tendsto_stokesRankPortPrimeEnergy_atTop_of_scaled_tendsto_atTop.
```

The two no-gos of section 3 are `not_exists_continuousPhysicalRank_eq_centralDefect` and
`PuiseuxOrbitCoareaDatum.cartanQuadratic_eq_of_contactNumerator_eq`; the RH classifier is
`xiArithmeticCentralCharacterUnitary_iff_riemannHypothesis`.

## Log

- 2026-08-06 — promoted to Stage 3.  Every theorem of sections 2--6 is unconditional in Lean and
  the axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`.
