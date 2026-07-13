# Quadratic algebraic monodromy--Gelfond--Schneider route to RH

- **ID:** `quadratic-algebraic-monodromy-gelfond-schneider-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[LARGE OUTLANDISH DETOUR]`
- **Lean bridge:** `formal/GaloisForLFunctions/RHTower/PrimeQuadraticGelfondSchneiderPhase.lean`
- **Inputs:** `QuadraticCircleFreeOrbitCharge.lean`, `CompletedSEMContourBoundary.lean`,
  `GelfondSchneiderProof/Statement.lean`
- **Predecessors:** `quadratic-reflection-anomaly-rh.md`,
  `irrational-circle-sem-holonomy-collapse.md`

## Claim

The prime-log holonomy need not be trivial.  It is enough to construct it as the eigenvalue or
determinant of one source-defined monodromy object over a number field.

For a fixed prime `p` and a finite list of free functional-equation orbit multiplicities `m_i`,
consider the principal complex power

```text
H_p = p^(I * M),             M = 2 sum_i m_i^2.             (1)
```

The exponent `I*M` is algebraic and irrational whenever `M>0`.  Gelfond--Schneider therefore makes
`H_p` transcendental for every nonempty free-orbit divisor.  Consequently

```text
H_p algebraic  <->  M=0  <->  every free-orbit multiplicity is zero.  (2)
```

Thus a source construction over any fixed number field, together with a multiplicity-exact
comparison identifying one of its algebraic monodromy eigenvalues with `(1)`, proves RH.  No
holonomy trivialization, positivity, metric, limiting zero-free region, or all-depth character
tower is required.

Lean proves the more flexible base theorem as well: if `alpha` is any algebraic complex number
other than `0` or `1`, then `alpha^(I*m)` is transcendental for every natural `m>0`.  The source may
therefore provide an algebraic ideal norm, determinant, or monodromy eigenvalue as the base; a
literal prime base is only the canonical Euler specialization.

## Two-ended chain

```text
completed prime--Gamma / FE--Schwarz source before divisor expansion
  -> finite reflection-stable window object defined over a number field K
       [OPEN CORE A: arithmetic source object]
  -> source FE action groupoid and a quadratic determinant/Pfaffian monodromy H_p(W)
       [OPEN CORE B: source-defined quadratic transgression]
  -> H_p(W) is algebraic, because it is an eigenvalue/determinant over K
       [FORMAL ALGEBRA ONCE A-B EXIST]
  -> equivariant localization and marked-support diagonalization
       fixed Xi orbits contribute 0
       free orbit i contributes 2*m_i^2
       [local square and finite diagonalization already proved;
        OPEN CORE C: source comparison]
  -> H_p(W) = p^(I * 2 sum_i m_i^2)
  -> Gelfond--Schneider forces sum_i m_i^2=0
       [PROVED LEAN]
  -> no free reflection orbit in W
  -> exhaust reflection-stable windows
  -> every Xi zero is fixed by s -> 1-conj(s)
  -> RH.
```

The local right end is formalized more sharply: for every hypothetical right-half zero `rho`, the
quadratic phase

```text
p^(I * 2 * ord_rho(Xi)^2)
```

is algebraic exactly when its local order is zero.  Lean proves that algebraicity of these phases
at every right-half zero is equivalent to RH.  This equivalence is a consumer gate, not the source
producer claimed above.

## Why algebraicity is a real weakening

The linear and quadratic circle routes previously required

```text
H_p(W)=1.
```

A moving-fiber groupoid or determinant line can carry arbitrary nontrivial holonomy, so flatness
or triviality does not follow from the existence of a closed square.  The present route asks only

```text
H_p(W) in algebraic closure(Q).
```

Every root of unity and every eigenvalue of a finite matrix over a number field satisfies this,
but the value need not be one and the connection need not be flat.  Gelfond--Schneider supplies the
annihilation only after the exact prime-log comparison.

## Candidate source homes

1. A finite-window algebraic local system attached to the prime--Gamma SEM contour, with the FE
   groupoid acting over a number field and the quadratic incidence class appearing in its
   determinant monodromy.
2. An equivariant Pfaffian or determinant gerbe with a model over a cyclotomic field.  Its
   fixed-point correction must be source-functorial, while its free-orbit determinant is `(1)`.
3. A Gauss-component metaplectic representation whose unsquared placewise operators have algebraic
   matrix coefficients; the secondary determinant is taken before the all-place scalar ratio
   collapses.
4. A finite étale realization of the marked-support quadratic incidence object.  The arithmetic
   representation supplies algebraicity, and the already formalized marked selector removes
   cross-orbit terms.

The first is the cleanest target.  It changes the hard theorem from global vanishing of a
secondary character to descent of that character to a number-field monodromy representation.

## Attacks and firewalls

1. **Bare algebraicity is RH-equivalent.**  Declaring the Xi-indexed phase algebraic is only the
   Lean consumer.  The matrix/local system, coefficient field, and monodromy must be defined from
   the completed source before its Xi divisor is expanded.
2. **Scalar FE cancellation is too coarse.**  The linear reflected product is `p^(im)p^(-im)=1`
   for every `m`.  Algebraicity of that product proves nothing.  The quadratic refinement and
   fixed-point subtraction are load-bearing.
3. **A complex analytic matrix need not be arithmetic.**  Finite dimensionality alone does not
   make its eigenvalues algebraic.  The source representation must genuinely descend to a number
   field with an explicit algebraic characteristic polynomial.
4. **Gamma values are generally transcendental-looking.**  A matrix whose entries are raw Gamma
   values does not discharge algebraicity.  The arithmetic model must isolate topological or
   algebraic monodromy before evaluating transcendental connection coefficients.
5. **Target-selected blocks are circular.**  Decomposing a matrix after listing free Xi orbits
   merely inserts the sum of squares by hand.  Equivariant localization and marked-support labels
   must be functorial on the source FE groupoid.
6. **Cross terms remain dangerous.**  The existing marked-support diagonalization removes them
   only after source component labels are supplied.  An unlabelled square of total multiplicity
   does not equal the sum of local squares.
7. **Critical-line zeros must survive.**  A global arithmetic phase that assigns `(1)` to every
   zero would exclude the known critical-line divisor as well.  The fixed-point correction must
   vanish on FE-fixed orbits and retain only free pairs.
8. **Branch convention must match.**  The Lean theorem uses principal `Complex.cpow`.  The source
   comparison must determine the same branch, or prove that the actual monodromy value is one of
   the algebraic powers covered by Gelfond--Schneider.
9. **Raw Stokes data do not discharge algebraicity.**  The failed wild-kernel route and the proved
   `archimedean-wild-monodromy-tate-local` card identify the Gamma Stokes constants as Tate data
   involving powers of `2*pi*i`, while the seam is a global regulator.  Those analytic Stokes
   multipliers are not automatically algebraic numbers.  The viable object must be an algebraic
   Betti/étale monodromy or characteristic polynomial before the period comparison, not the raw
   archimedean Stokes matrix under a new name.

## Positive theorem extracted from the holonomy no-go

`[PROVED LEAN]` Nontrivial determinant-line holonomy is not itself an obstruction, but any nonzero
quadratic prime-log order forces that holonomy to be transcendental.  Therefore every
number-field-valued realization of the correct quadratic phase is automatically supported only on
FE-fixed orbits.

This is stronger as a diagnostic than the earlier statement that a moving groupoid square may
have arbitrary holonomy: it identifies the exact arithmetic category in which arbitrary holonomy
is impossible.

## Status

- `[PROVED LEAN]` `p^(I*m)` is transcendental for every prime `p` and natural `m>0`;
- `[PROVED LEAN]` the same holds for every nonzero, nonunit algebraic complex base;
- `[PROVED LEAN]` its algebraicity is equivalent to `m=0`;
- `[PROVED LEAN]` the quadratic phase of a finite free-orbit multiplicity list is algebraic exactly
  when every multiplicity vanishes;
- `[PROVED LEAN]` algebraicity of the local reflected quadratic phase at every hypothetical
  right-half Xi zero is equivalent to RH;
- `[PROVED]` local completed-flux/SEM quadratic indices and finite marked-support diagonalization
  are available in the corpus;
- `[OPEN CORE]` a source-defined number-field monodromy object and its quadratic phase comparison;
- `[OPEN CORE]` functorial fixed/free localization and finite-window exhaustion;
- `[CLOSED SHORTCUT]` ordinary FE-paired linear algebraicity is automatic and RH-blind.
