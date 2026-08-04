# Arithmetic Xi--Stokes central rank-port law

- **ID:** `arithmetic-xi-stokes-central-rank-port-law`
- **Stage:** 2-fully-proven
- **Type:** BRIDGE / ARITHMETIC REALIZATION / NO-GO CLOSURE
- **Upstream:** `../1-in-progress/arithmetic-xi-stokes-rank-port-realization.md`
- **Target manuscript:** `../4-publication-ready/polarized-stokes-microlocal-witt-law/`
- **Novelty label:** `[BRIDGE]`.  Scalar twists and determinant weights are standard separately.
  New claim is restricted to their exact identification with the coefficient-generated Stokes
  one-port functional and the certified rational-adelic Xi transgression.

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

## 6. Exact commutative diagram

The arithmetic realization is summarized by

```text
degree-one rational-adelic source  --j_rho-->  first Xi jet line
             | D_(n,rho)                          | Hol(L_(n,rho))-1
             v                                    v
physical two-leg defect           --Res---->  first Xi jet line.
```

The square commutes by Theorem 5.1.  The top source and the family `L_(n,s)` are pre-divisor.
Divisor specialization enters only through the first nonzero Xi jet.

## 7. Hostile audit

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
- The theorem is false without connectedness: one common scalar survives on each connected mixed
  Hom component, producing one determinant port per component.  Coefficient-generated spectra
  avoid this failure because (1.1) makes the interaction graph complete.

## 8. Formalization target

One new Lean module must certify:

1. connected/complete mixed-channel scalar classification;
2. common scalar cancellation on Hom transport;
3. determinant scaling by `M`;
4. arithmetic mate-gain multiplicativity and reflection inversion (reusing existing theorems);
5. equality of the certified source transgression with the central holonomy defect;
6. trace-one Xi specialization and exact zero classifier.

No axiom, `sorry`, `admit`, `opaque`, `unsafe`, RH assumption, or global vanishing theorem is
permitted.
