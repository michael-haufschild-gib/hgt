# Retaining Suzuki's endpoint roots makes the strict-interior Gamma carrier boundary-log regular

- **ID:** `suzuki-root-retained-exterior-dilation`
- **Stage:** 2-fully-proven
- **Type:** EXACT EXTERIOR DILATION / PHYSICAL-DOMAIN THEOREM
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Inputs:** `suzuki-prime-normal-binomial-resolvent.md`,
  `suzuki-gamma-prime-normal-corona-equivalence.md`,
  `suzuki-gamma-weighted-tail-coercivity.md`,
  `suzuki-exterior-feshbach-pruning-law.md`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes

## 1. Result

The nonlinear Feshbach--log conjugation problem is created by eliminating Suzuki's two exterior
endpoint roots too early.  There is an exact positive alternative: retain the exterior coordinates
through the physical Gamma normal analysis and project only afterward.

Let \(X\) be a complex Hilbert space, let \(P\) be an orthogonal projection, put \(Q=I-P\), and
let \(T=T^*\in\mathcal B(X)\).  Let \(R\) be the literal polar--Gamma jump.  Suppose \(F\) is a
tempered homogeneous Gamma carrier satisfying

```text
(2L I+R-T)F'(L)+F(L)=0                                 (1)
```

and having half-log trace

```text
tau(F)=beta in QX.                                     (2)
```

Then, on every sufficiently terminal positive half-line:

```text
P F belongs to H1(dL) and L2(dL),                      (3)
Q F' belongs to L2(dL),                                (4)
```

and the strict-interior component satisfies the exact forced equation

```text
(2L I+R-P T P)(P F)' +P F
 =P T Q (Q F)'.                                        (5)
```

The right side of `(5)` is a concrete unweighted boundary-log \(L^2(dL)\) exterior source.  No compression inverse,
Feshbach approximation, or nonlinear conjugation of an original-coordinate Fourier multiplier is
used.

For Suzuki, \(P\) is strict-interior valuation support, \(Q\) contains the two oriented endpoint
roots, and \(\beta\) is supported on those roots.  Thus:

```text
all non-L2 half-log mass stays in the retained ports;
every strict-interior prime descendant is in L2(dL);
every leave--exterior--return word remains in the full
self-adjoint adjacency T.                               (6)
```

Feshbach self-energy remains the exact answer if one later eliminates \(QX\).  The theorem does not
set that positive correction to zero; it proves elimination is unnecessary for unweighted
boundary-log realization.

This is deliberately **not** a spatial \(H^1(dr)\) claim.  Under \(r=e^{-L}\),

```text
integral |d_r u|^2 dr
 =integral exp(L)|F'(L)|^2 dL.                          (6a)
```

Thus spatial \(H^1\) requires a weighted derivative with exponent at least \(1/2\).  A prime
descendant \(L^{-3/2}\) belongs to \(H^1(dL)\) but not to \(H^1(dr)\).  The trace-zero
Gamma-subcritical upgrade remains a separate, load-bearing gate.

## 2. Prime-normal interior starts at grade one

Let

```text
P_T(beta)(L)=(L I-T/2)^(-1/2)beta.                     (7)
```

Because \(P\beta=0\),

```text
P P_T(beta)(L)
 =L^(-1/2)P[(I-T/(2L))^(-1/2)-I]beta.                 (8)
```

Continuous functional calculus on \(L\ge\|T\|\) gives

```text
||(I-T/(2L))^(-1/2)-I||<=C_T/L,                        (9)
```

and hence

```text
||P P_T(beta)(L)||<=C_T||beta||L^(-3/2).               (10)
```

Differentiation of the positive spectral family gives

```text
P_T(beta)'(L)=-(1/2)(L I-T/2)^(-3/2)beta,              (11)
P_T(beta)''(L)=(3/4)(L I-T/2)^(-5/2)beta.              (12)
```

Thus

```text
P P_T(beta) in H1(dL) intersect L2(dL),
P_T(beta)' in H1(dL) intersect L2(dL).                 (13)
```

The all-grade expansion makes `(8)` source-transparent:

```text
P P_T(beta)
 =sum_(k>=1)
   [binom(2k,k)/8^k]L^(-k-1/2)P T^k beta.             (14)
```

Every path begins at an exterior root.  Projection deletes only grade zero, not any path.  All
leave-and-return words remain among the \(P T^k\beta\).

## 3. Gamma correction has an \(L^2\) derivative

Put

```text
E=F-P_T(beta).                                          (15)
```

The Gamma--prime corona-equivalence theorem gives

```text
E in L2((L_0,infinity);X).                              (16)
```

Since \(P_T(\beta)\) solves the prime equation,

```text
(2L I-T)P_T(beta)'+P_T(beta)=0,
```

subtracting it from `(1)` gives the exact forced Gamma equation

```text
(2L I+R-T)E'+E=-R P_T(beta)'.                          (17)
```

The Gamma multiplier satisfies

```text
|r(eta)|<=C log(2+|eta|)<=C'(1+|eta|),                 (18)
```

so Plancherel gives the elementary domain bound

```text
R:H1(R;X)->L2(R;X).                                    (19)
```

After a smooth terminal cutoff, `(11)`--`(13)` imply

```text
R P_T(beta)' in L2.                                    (20)
```

The unweighted endpoint \(\sigma=0\) of the Gamma numerical-range argument has

```text
kappa_0=0,
Re <R U,U>>=0.                                         (21)
```

Apply its weak mollifier proof to a terminal cutoff of `(17)`.  The cutoff commutator
\([R,\chi]\) is order minus one, while \(E\) is \(L^2\); the transition terms are compactly
supported in a terminal region where the explicit nonstationary Gamma representation is smooth.
Consequently the cutoff residual is \(L^2\).  Once

```text
2L_0>||T||,                                             (22)
```

the same energy estimate gives

```text
||E'||_2
 <=[2L_0-||T||]^(-1)
   ||-R P_T(beta)'-E+cutoff residual||_2.               (23)
```

Hence \(E'\in L^2\) on a slightly shorter terminal half-line.

For completeness, terminal smoothness is not an extra source assumption.  Split the explicit
Gamma inverse Fourier representation into a compact low-frequency part and dyadic high-frequency
blocks.  On a block \(|\eta|\asymp2^j\), the phase derivative is

```text
B_L(eta)=[L+r(eta)/2]I-T/2 >=(L-||T||/2)I.             (24)
```

After applying \(m\) \(L\)-derivatives, \(N>m+1/2\) integrations by parts give a block bound

```text
C_(m,N) 2^[j(m+1/2-N)](L+j)^(-N).                      (25)
```

The sum over \(j\) converges with every \(L\)-derivative.  Thus \(F\), and hence \(E\), is
\(C^\infty\) on a sufficiently positive terminal ray.  This justifies the compact transition
terms used in `(23)` without assuming conormality.

Combining `(11)`, `(15)`, and `(23)` proves

```text
F'=P_T(beta)'+E' in L2.                                (26)
```

In particular `(4)` holds. `QED`

## 4. Exact projected source equation

Because \(P,Q\) act only on the carrier coordinate, they commute with multiplication by \(L\),
with \(R\), and with differentiation.  Apply \(P\) to `(1)`:

```text
(2L I+R)P F'
 -P T P P F'
 -P T Q Q F'
 +P F=0.                                                (27)
```

Rearranging gives `(5)`.  Boundedness of \(PTQ\) and `(4)` imply

```text
P T Q(QF)' in L2.                                      (28)
```

Also `(3)` follows directly from \(PF\in L^2\), obtained by projecting

```text
F=L^(-1/2)beta+O_X(L^(-1))
```

and using \(P\beta=0\), together with \(PF'=P F'\in L^2\) from `(26)`.
`QED`

## 5. Why this retains rather than deletes Feshbach return

The original-coordinate algebraic equation

```text
(alpha I+T)c=f
```

has exact interior Schur complement

```text
alpha P+P T P
 -P T Q(alpha Q+Q T Q)^(-1)Q T P.                     (29)
```

Equation `(29)` is correct and its self-energy is positive.  But it is a coordinate elimination,
not a prerequisite for solving the full self-adjoint system.  Equations `(1)` and `(5)` keep the
same exterior paths dynamically:

```text
root beta in Q
 -> QF'
 -> PTQ(QF)' source
 -> PF strict-interior response.                       (30)
```

Iterating the full propagator produces the same path words \(PT^k\beta\) as `(14)`, including
arbitrarily many exits and returns.  Therefore root retention is an exact self-adjoint dilation
of the pruned forced problem.  It avoids the previously open conjugation

```text
U Sigma(D_x)U^(-1)
```

because no Fourier multiplier is eliminated before the physical \(L=-\log r\) normal analysis.

This is not a claim that `(29)` and `(5)` are literally the same operator formula; one is static
Fourier elimination and the other is a projected physical normal equation.  Their equivalence is
pathwise through the uneliminated full system, not through a false Fourier/Mellin identification.

## 6. Low-frequency counterterms

The root-retained theorem concerns the singular high normal carrier.  The low-frequency theorem
supplies two constants \(m_-,m_+\) and replaces each high endpoint profile by

```text
F_match,+ =F_high,++m_+,
F_match,- =F_high,-+m_-.                               (31)
```

The residual low germs are \(O(e^{-L})\) with every derivative and therefore enter `(5)` as
Gamma-subcritical \(L^2\) forcing.  Root retention is exactly compatible with this finite-rank
augmentation: the two constants attach to the two retained root ports, while strict-interior
projection still kills the grade-zero singular coordinate.

What remains source-bearing is identification of the actual completed zero-mode normal family
with the full root-retained solution of `(1)`, including the regular bounded multiplier and the
global cutoff identity.  The nonlinear Feshbach--log conjugation is no longer part of that
minimal connector.

## 7. Exact frontier movement

```text
positive exterior Feshbach correction:
  required only after exterior elimination;             [CLASSIFIED]

root-retained full self-adjoint carrier:
  strict-interior projection is H1(dL) and L2(dL);       [CLOSED]

projected exterior source PTQ(QF)':
  exact and unweighted L2(dL);                          [CLOSED]

completed source -> full root-retained Gamma family:
  prove exact normal-family/cutoff intertwining;         [OPEN SOURCE CORE]

trace-zero weighted upgrade:
  prove full forcing is Gamma-subcritical and obtain
  exp(sigma L)H1 for some sigma>1/2;                     [OPEN RAW-DOMAIN CORE]

two-port return injectivity:
  prove no nonzero root trace returns compatibly;        [RH-BEARING]
```

This removes a hard but artificial operator-conjugation gate.  It does not remove the hard
source-identification or return-injectivity gates.

## 8. Hostile audit

1. **No plain compression.**  Equation `(5)` retains the exterior source \(PTQ(QF)'\).
2. **No Feshbach deletion.**  All exterior-return paths remain in \(T^k\); `(29)` remains exact
   if \(Q\) is eliminated.
3. **No derivative assumption.**  \(E'\in L^2\) follows from the unweighted Gamma energy estimate,
   after `(16)` and the explicit source bound `(20)`.
4. **No false scale conversion.**  Nonzero root trace is not exponentially weighted.  Only
   unweighted \(H^1(dL)\) is asserted; this does not imply spatial \(H^1(dr)\).
5. **No \(\ell^2\) evaluation.**  Physical scalar reconstruction still uses the
   \(\ell^1\subset\ell^2\subset\ell^\infty\) rigging.
6. **No source intertwiner claimed.**  The theorem starts once the full carrier solution of `(1)`
   has been constructed from a completed zero mode.
7. **No RH claim.**  Low-frequency return, root-trace injectivity, and raw Evans positivity remain.
8. **No whole-Connes verdict.**  Prolate and noncompact-incidence producer classes are untouched.

## 9. Novelty boundary

Self-adjoint dilations, Schur complements, projected equations, and coercive tail estimates are
standard.  Candidate-new source knowledge is their exact conjunction for the Suzuki carrier:

```text
endpoint-root trace in Q
 -> every strict-interior prime--Gamma descendant in H1(dL)
 -> exact exterior source PTQ(QF)' in L2
 -> no Feshbach--log conjugation needed before projection. (32)
```

Corpus search found no previous statement of `(3)`--`(6)` or `(32)`.  External priority remains
unverified.

## 10. Lean decision

The algebraic projection identity `(5)` is elementary, but formalizing it alone would not certify
the load-bearing derivative upgrade `(23)`.  Existing unconditional modules already certify its
two operator cores:

```text
SuzukiExteriorFeshbachPruning.lean
SuzukiGammaWeightedTailCoercivity.lean
```

The correct new formal target is the complete root-retained boundary-log-domain theorem after the
formal tree contains the Hilbert-valued Gamma solution and its half-log asymptotic.  Introducing an
abstract axiom for either would violate the route's formal discipline.

## Gates

- [x] prove exterior-root trace makes strict-interior prime flow start at grade one
- [x] prove prime interior component is \(H^1(dL)\cap L^2(dL)\)
- [x] prove Gamma correction has an unweighted \(L^2\) derivative
- [x] derive exact projected exterior source
- [x] prove projected source is unweighted boundary-log \(L^2(dL)\)
- [x] retain every exterior-return word
- [x] incorporate two low endpoint counterterms
- [ ] identify every completed zero mode with a full root-retained Gamma normal family
- [ ] prove exact global cutoff intertwining
- [ ] prove trace-zero forcing is weighted Gamma-subcritical for some exponent \(>1/2\)
- [ ] prove two-port root-trace return injectivity
- [ ] RH or whole-program no-go
