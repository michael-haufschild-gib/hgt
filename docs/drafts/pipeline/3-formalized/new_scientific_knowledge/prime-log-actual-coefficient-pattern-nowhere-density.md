# Prime-log actual coefficient-pattern nowhere-density law

- **ID:** `prime-log-actual-coefficient-pattern-nowhere-density`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED] [FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general HT source geometry; bounded prime-log Herglotz gauges
- **Statement:** Every finite injective translate packet, finite distinct actual differential-monomial
  support, and polynomial coefficient-degree bound admits a noncolliding upper evaluation packet
  whose rank-defect gauges form a closed nowhere-dense subset of the complete uniform space of
  bounded prime-log gauges.

## The law

Let `I` be a finite translate set with distinct shifts `h_i`, let `J` be the finite set of actual
differential coordinates

```text
g_u^(j)(z+h_i),    i in I, 0<=j<n_i,
```

and let `M_1,...,M_k` be distinct monomials in these coordinates.  Fix a polynomial
coefficient-degree bound `q`.  Put

```text
N=k(q+1).
```

There are evaluation bases `z_1,...,z_N` such that all nodes `z_a+h_i` are distinct and lie in the
upper half-plane.  Form the square expanded matrix

```text
A_u(a,(r,d))=z_a^d M_r((g_u^(j)(z_a+h_i))_(i,j)),
0<=d<=q.                                                   (1)
```

In the complete uniform gauge space

```text
B={u: primes -> R | sup_p |u_p|<infinity},
```

the rank-defect set

```text
D={u in B : det A_u=0}                                     (2)
```

is closed and nowhere dense.  Equivalently, the gauges for which (1) has full rank form an open
dense set.

Full rank excludes every complex coefficient vector of the pattern simultaneously.  If

```text
sum_(r,d) c_(r,d) z^d M_r((g_u^(j)(z+h_i))_(i,j))=0         (3)
```

holds identically, evaluation at the packet gives `A_u c=0`; invertibility forces every
`c_(r,d)=0`.  Thus (2) is a coefficient-uniform defect stratum rather than the zero set of one
preselected relation.

## Proof geometry

The expanded monomials

```text
(z,x) |-> z^d M_r(x)
```

are linearly independent.  A colored spanning-selection theorem chooses one admissible point in
each evaluation row so that their square evaluation matrix is invertible.  The admissible row sets
are separated vertical upper half-lines: their real parts are spaced farther apart than every
shift-real-part difference.  Hence every row-by-shift node is distinct without sacrificing the
spanning argument.

The determinant of the expanded matrix is one nonzero multivariate polynomial in the finite row
jet packet.  Simultaneous prime-log Cauchy-jet controllability escapes its zero set by a finitely
supported positive mass perturbation inside every uniform gauge ball.  Factorial diagonal scaling
transfers the result from normalized Cauchy jets to actual iterated derivatives.

For closedness, bounded gauges are realized as bounded continuous functions on the discrete prime
index set with the uniform norm.  This is a complete space.  On every unit gauge ball, each
prime-log Cauchy series has one summable dyadic majorant, so every finite normalized jet coordinate
is continuous.  The exact factorial identity gives continuity of actual derivatives.  Therefore
`u |-> det A_u` is continuous and (2) is closed.  Local determinant escape makes its interior
empty; a closed set with empty interior is nowhere dense. `QED`

## Positive necessity law for RH carriers

> **A perturbation-stable selector on bounded prime-log carriers must be carried by an unbounded
> compatibility, because every bounded-support, bounded-order, bounded coefficient-degree
> differential pattern is generically full.**

This does not assert RH and does not select zeta.  It says positively what any successful
zeta/RH marking in this carrier landscape must preserve: information that does not close inside a
finite differential window.  Candidate forms include global Euler multiplicativity,
functional-equation polarization, a boundary positivity cone, or a prime-indexed inverse-limit
class.  A finite differential-algebraic signature, even with arbitrary complex coefficients, is
not such information.

## Novelty and significance gate

The ingredients—finite-dimensional spanning, polynomial nonvanishing, uniform convergence,
complete metric spaces, and Baire category—are classical.  The candidate-new object is their exact
constraint geometry for the prime-log HT carrier: finite differential-algebraic possibilities are
organized as closed nowhere-dense determinant strata in gauge space, with one stratum excluding
all complex coefficient vectors of its combinatorial pattern.  This is scientifically stronger
than coefficient-by-coefficient escape and supplies the missing source geometry needed by the
facet-sewn Stanley--Reisner realization.

The novelty label remains provisional pending independent specialist comparison.  The theorem is
unconditional regardless of that classification.

## Lean certificate

`GaloisForLFunctions.HTGeometry.ExpandedMonomialEvaluation` proves the expanded-monomial
independence, colored full-rank selection, separated upper row geometry, and noncolliding packet.

`CoefficientPatternDeterminant` constructs the single determinant polynomial and proves that one
full-rank target makes it nonzero.

`CoefficientUniformJetEscape` proves coefficient-uniform bounded-gauge escape and transfers full
rank to actual iterated derivatives.

`BoundedGaugeContinuity` constructs `PrimeLogBoundedGauge`, proves completeness through the
bounded-continuous-function model, proves continuity of every actual differential-jet coordinate,
and proves every fixed actual coefficient-pattern defect is closed.

`BoundedGaugeGenericity` proves:

- `actualCoefficientPatternRankDefect_isNowhereDense_of_isUnit`;
- `actualCoefficientPatternFullRank_isOpen_dense_of_isUnit`;
- `exists_primeLog_actualCoefficientPattern_closed_nowhereDense`.

The certificate has no `sorry`, `admit`, project axiom, opaque postulate, or unsafe declaration.

## Gates

- [x] 0 → 1: coefficient-uniform source-space defect geometry isolated
- [x] 1 → 2: complete unconditional proof above
- [x] 2 → 3: noncollision, determinant escape, actual-derivative transfer, continuity, closedness,
  and nowhere-density formalized in Lean
- [ ] 3 → 4: standalone exposition and external novelty audit
