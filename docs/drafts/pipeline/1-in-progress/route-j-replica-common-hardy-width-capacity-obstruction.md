# Route J replica common-Hardy width--capacity obstruction

- **Status:** in progress; positive scalar replica class closed on paper and in Lean;
  pre-scalar operator-valued survivor open
- **Parent:** `rh-current-frontier-map.md`, Route J
- **Source papers:**
  - `../4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`
  - `../4-publication-ready/riemann-oriented-source-admission/main.tex`
- **Formal certificate:**
  `formal/GaloisForLFunctions/HTGeometry/FisherReplicaCommonHardyObstruction.lean`
- **Open core:** `PRE_SCALAR_OPERATOR_GAMMA_COPOISSON_REPORTER`

## Updated-paper impact

The updated Green-descent paper removes source capacity, reflection, Meyer quotient construction,
and pointwise topology construction from the RH frontier.  One reflected Gaussian family has
uniform half-density capacity, while actual Xi evaluation of that family is bounded exactly on the
critical line.  Its canonical common form remains arithmetic admission of the actual Xi functionals
into the half-density continuous dual.

The same paper identifies a concrete pre-admission source object still missing: a
presentation-independent infinite ordinary-prime Gamma/co-Poisson common Hardy reporter retaining
affine terms before scalar overlap division.  Existing finite reporter and cofinal replica theorems
do not yet construct it.

## Exact collision between the two existing constructions

Let one source atom have probability mass `p`, centered Fisher coordinate `a`, and reporter phase
`d`.  Replicate it `k` times with mass `p/k`.  The complete ordered off-diagonal replica collision is

```text
R_k^alg
 =sum_(r!=s)(p/k)^2(a+a)d
 =2p^2 a d(1-1/k).                                     (JRC1)
```

Thus the algebraic cofinal-replica construction recovers the nonzero doubled diagonal collision:

```text
R_k^alg -> 2p^2 a d.                                    (JRC2)
```

But the common-Hardy construction represents one ordered pair by the literal height interval
between its endpoints.  Give replica `r` height `eta_r`, assume all heights are nonnegative, and let

```text
Delta_k=sup_(r,s)|eta_r-eta_s|.
```

For every Hardy node `w` with `Re w>=0`, the exact interval coefficient satisfies

```text
|integral_(eta_s)^(eta_r) exp(-wu)K du|
 <= |K| |eta_r-eta_s|.                                  (JRC3)
```

Summing the complete ordered replica fibre gives the uniform width--capacity law

```text
C_k^Hardy
 <=2p^2 |ad| Delta_k.                                   (JRC4)
```

The bound is independent of `k`.  Consequently

```text
Delta_k->0  ==>  C_k^Hardy->0,                           (JRC5)
```

whereas `(JRC2)` stays nonzero whenever `p a d !=0`.

## Theorem: scalar cofinal replication is not the reporter mate

`[PAPER-PROVED] [LEAN-FORMALIZED]`

No vanishing-width orthogonal replication with uniformly bounded endpoint reporter can both

1. recover the algebraic omitted collision by the cofinal off-diagonal identity, and
2. realize that recovered collision as one literal hard-cut/soft-damping common-Hardy source.

Identical-height replicas make the incompatibility sharp: they recover `(JRC2)` algebraically but
every interval has length zero, so their common-Hardy contribution is exactly zero.  Infinitesimal
height splitting does not repair it because `(JRC4)` is uniform in replica count.

This is not the generic statement that a bounded map loses a singular limit.  It identifies the
exact source mechanism: cofinal collision evacuation is transverse to the interval geometry used by
the finite common reporter.

## Theorem: exact positive source preservation forbids persistent spread

`[PAPER-PROVED] [LEAN-FORMALIZED]`

The apparent persistent-width escape is unavailable to a positive scalar source.  Let
`q_r>=0`, `sum_r q_r=1`, let every inward Hardy displacement satisfy `eta_r>=0`, and fix one
`x>0`.  Exact preservation of the original atom at this single Laplace damping moment means

```text
sum_r q_r exp(-x eta_r)=1.                              (JRC6)
```

Each summand has deficit

```text
q_r(1-exp(-x eta_r))>=0.
```

Equation `(JRC6)` says the sum of these deficits is zero.  Hence every positive-mass deficit is
zero, strict injectivity of the real exponential gives `eta_r=0`, and the literal oriented
interval reporter vanishes.  Therefore a positive scalar replication cannot simultaneously

1. preserve even one nontrivial inward damping coefficient exactly, and
2. retain nonzero interval width with which to report the evacuated collision.

Unlike `(JRC4)--(JRC5)`, this is a finite-depth rigidity theorem and needs no limiting,
uniformity, or bounded-capacity hypothesis.

## Strongest positive survivor

`[CONJECTURE] [ROUTE J OPEN]`

A reporter mate can escape the combined width--capacity and exact-damping theorems only by at least
one of the following non-positive-scalar mechanisms:

1. **signed or complex replication:** cancellations preserve `(JRC6)` despite nonzero shifts;
2. **inverse-width singular capacity:** endpoint reporter norm grows at least as `1/Delta_k`;
3. **operator-valued transverse channel:** collision is retained before positive scalar interval folding in
   a channel not bounded by `(JRC3)`;
4. **affine Gamma cancellation before division:** the collision is cancelled against a separately
   transported Gamma/polar term before either is asked to define a Hardy vector.

Option 1 is no longer a positive source and must be controlled as an indefinite pre-scalar channel.
The updated Green-descent and source-admission results reject option 2 as a regular positive
admission mechanism: inverse-width growth is precisely singular Cartan transport.  Full-current
Hardy representation is independently impossible because the Gamma logarithmic derivative diverges
on every fixed vertical Euler line.  Therefore viable regular construction is narrowed to a
genuinely operator-valued Gamma/co-Poisson channel implementing option 3 or 4 before scalarization;
signed/complex realizations fall under the same pre-scalar control problem.

## Anti-theatre gate

Route J remains open.  Positive scalar cofinal replication is class-closed, not a survivor.  Any
replacement must expose an explicit signed/operator-valued pre-scalar Gamma cancellation and prove
its positivity or boundedness after folding.  Merely retaining nonvanishing replica width now
violates exact source preservation by `(JRC6)`.  Any proposed reporter must be tested against both
`(JRC4)` and `(JRC6)` before using analytic continuation or a divisor identity.

## Formal map

| Paper item | Lean declaration |
|---|---|
| `(JRC1)` | `fisherReplicaOffDiagonalCollision_eq` |
| interval capacity | `fisherReplicaIntervalCollisionCapacity` |
| `(JRC4)` | `fisherReplicaIntervalCollisionCapacity_le` |
| `(JRC5)` | `tendsto_fisherReplicaIntervalCollisionCapacity_zero` |
| abstract non-recovery | `no_vanishingWidthReporter_recovers_fisherReplicaCollision` |
| `(JRC3)` | `norm_orientedCutoffLaplaceCoefficient_le_width` |
| literal Laplace reporter | `fisherReplicaOrientedCollisionLaplace` |
| literal reporter bound | `norm_fisherReplicaOrientedCollisionLaplace_le_capacity` |
| literal reporter vanishing | `tendsto_fisherReplicaOrientedCollisionLaplace_zero` |
| headline incompatibility | `no_vanishingWidthOrientedLaplace_recovers_fisherReplicaCollision` |
| exact positive damping rigidity `(JRC6)` | `fisherReplicaDamping_eq_one_forces_zero_shift` |
| uniform-replica rigidity | `fisherUniformReplicaDamping_eq_one_forces_zero_shift` |
| exact-preserving reporter vanishes | `fisherReplicaOrientedCollisionLaplace_eq_zero_of_dampingPreserving` |
| positive scalar replica class no-go | `no_positiveDampingPreservingReplica_recovers_fisherReplicaCollision` |

## Novelty discipline

- Finite interval Laplace bounds and finite-sum algebra are classical ingredients.
- The source-specific incompatibility between cofinal Fisher collision evacuation, exact positive
  damping preservation, and literal common-Hardy interval geometry was not present in checked
  corpus.
- No external priority claim is made.  Scientific content here is the new exact obstruction and its
  forced depth-nonlocal survivor, not the individual inequalities.
