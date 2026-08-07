# Burnol--Hedenmalm archimedean completion domain--radical exchange

- **ID:** `burnol-hedenmalm-archimedean-completion-domain-radical-exchange`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Statement:** Burnol's uncompleted divided-zero vectors belong to a source-defined Sonine
  Hilbert space but lie outside the domain of spectral-coordinate multiplication.  Multiplication
  by the archimedean completion factor moves the divided vectors into the maximal coordinate
  domain, but the coordinate recurrence then has the nonzero completed Xi source as its defect.
  Thus completion transfers the obstruction from the operator domain to the metric radical; it
  does not manufacture a Hilbert--Pólya eigenvector.

## 1. The uncompleted Sonine carrier

Let `L` be Burnol's critical extended Sonine space on the line `Re s=1/2`.  Its definition uses
only the Mellin source and the cosine-transform support condition.  If `rho` is a nontrivial zero
of `zeta`, Burnol proves that

```text
x_(rho,k)(s)=zeta(s)/(s-rho)^k,       1<=k<=m_rho,        (1)
```

belong to `L`, form a complete and minimal system there, and have a complete biorthogonal system
given by triangular zero-evaluation jets.

Let `M_s` be maximal multiplication by `s` on `L`:

```text
dom(M_s)={f in L : s f in L}.                            (2)
```

Then every first divided vector `x_(rho,1)` lies outside `dom(M_s)`.

### Proof

Suppose `x_(rho,1)` were in `dom(M_s)`.  Both `x_(rho,1)` and `s x_(rho,1)` would then belong to
`L`, hence to `L^2` of the critical line.  But

```text
zeta(s)=(s-rho)x_(rho,1)(s)
       =s x_(rho,1)(s)-rho x_(rho,1)(s),                 (3)
```

so `zeta` itself would be square-integrable on the whole critical line.  This contradicts the
classical critical-line mean-square asymptotic

```text
integral_0^T |zeta(1/2+it)|^2 dt = T log T+O(T),          (4)
```

which diverges as `T` tends to infinity.  Therefore the exact algebraic eigenvector recurrence

```text
M_s x_(rho,1)=rho x_(rho,1)+zeta                         (5)
```

cannot be an operator identity in Burnol's Hilbert space: its common source term is not a Hilbert
vector.

This explains why Burnol's completeness theorem alone is not a Hilbert--Pólya construction.
Completeness supplies the vectors, but the natural spectral coordinate is not defined on them.

## 2. Archimedean completion repairs the domain

Write

```text
A(s)=s(s-1) pi^(-s/2) Gamma(s/2)/2,
xi(s)=A(s)zeta(s).                                       (6)
```

On the critical line the completion multiplier has exponential decay and no zero.  In centered
coordinates `s=1/2+i z`, put

```text
XiC(z)=xi(1/2+i z),
q_alpha(z)=XiC(z)/(z-alpha),                             (7)
```

with the removable value at a centered Xi zero `alpha`.  The completed function `XiC` is Schwartz
on the real axis.  Consequently

```text
q_alpha in L^2(R),
z q_alpha in L^2(R),                                    (8)
```

and `q_alpha` lies in the maximal domain of the self-adjoint real-coordinate multiplier `M_z`.
The recurrence is now a genuine `L^2` identity:

```text
M_z q_alpha=alpha q_alpha+XiC.                            (9)
```

Thus the archimedean factor repairs precisely the domain failure in Section 1.  It does not,
however, turn `q_alpha` into an eigenvector: the completed common source `XiC` is a nonzero
`L^2` vector.

## 3. The obstruction moves to the radical

Let `J` map a source core containing `XiC` and the divided functions into a Hilbert space, and
suppose coordinate multiplication descends to a symmetric operator `S` through `J`.  Equation
`(9)` can become the eigenvector identity

```text
S J(q_alpha)=alpha J(q_alpha)                            (10)
```

only if

```text
J(XiC)=0.                                                 (11)
```

If `J(q_alpha)` is nonzero, symmetry then forces `alpha` to be real.  The same divided recurrence
at the second level excludes a nontrivial Jordan step and hence excludes multiplicity greater
than one.

The live Hedenmalm metric classification shows that this radical cannot be produced by an
ordinary positive `L^2` metric.  A continuous positive translation-invariant source form killing
`XiC` is supported on the real Xi divisor; absolutely continuous and finite-order local metrics
collapse to zero.  Hence completion exchanges the two defects:

```text
uncompleted carrier: divided vectors present, source outside operator domain;
completed carrier:   source and divided vectors in the domain, source must be null. (12)
```

This is an exact positive statement, not merely a no-go: a successful direct symmetric carrier
must solve both sides simultaneously by a singular source-defined boundary completion which
kills the common completed source, retains every first divided vector, and transports at least
the first two coordinate recurrences.

## Boundary of the theorem

The theorem does not construct that singular boundary completion.  Declaring `XiC` null, or
quotienting by its span, is insufficient: coordinate multiplication must descend, the divided
vectors must survive, and the resulting form must be positive without selecting the Xi divisor.
The ordinary `L^2` quotient is not invariant under coordinate multiplication, while the canonical
translation-invariant positive form is already divisor-supported and its positivity is the Weil
RH criterion.

The resulting constructive route is recorded in
`../../1-in-progress/burnol-hedenmalm-boundary-null-graph-completion-rh.md`.

## Literature and corpus inputs

- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, J. Theor. Nombres Bordeaux 16 (2004), 65--94, Theorem 3.3.
- J.-F. Burnol, *On the system of the functions zeta(s)/(s-rho)^k*, 2011, especially Theorem 2
  and the paragraph immediately following it.
- H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494 (2026),
  Theorems 3.3.1, 3.3.3, and 4.2.2.
- `../new_scientific_knowledge/hedenmalm-pair-weil-polarization-law.md`.
- `../new_scientific_knowledge/hedenmalm-theta-pair-divisor-supported-metric-law.md`.
- `../../3-formalized/not_new_scientific_knowledge/hedenmalm-divided-chain-symmetric-carrier-law.md`.

## Gates

- [x] Burnol membership, completeness, and minimality separated from the operator-domain issue
- [x] first divided vectors excluded from the uncompleted coordinate domain
- [x] archimedean completion places the source and first divided vectors in the maximal domain
- [x] exact completed source-defect recurrence
- [x] radical requirement and symmetric contradiction endpoint
- [x] positive successor formulated from the obstruction
- [x] formalize the completed side: maximal-domain membership of the source and of every first
      divided vector, the exact completed source-defect recurrence `(9)`, both nonvanishing
      statements, and the symmetric radical endpoint `(10)`,`(11)`
      (`BurnolHedenmalmCompletionDomain.lean`, `XiHedenmalmSymmetricMultiplicity.lean`)
- [x] formalize the algebraic transport step `(3)` of the uncompleted exclusion and its
      contrapositive consumer (`BurnolHedenmalmUncompletedDomain.lean`)
- [ ] formalize the classical input `(4)`: zeta is not square integrable on the critical line
      (route and Lean plan in `../../1-in-progress/zeta-not-square-integrable-critical-line.md`)

