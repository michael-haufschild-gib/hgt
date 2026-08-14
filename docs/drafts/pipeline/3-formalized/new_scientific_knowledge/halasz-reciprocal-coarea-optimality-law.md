# Reciprocal coarea optimality for hyperbolic prime--cofactor decompositions

- **ID:** `halasz-reciprocal-coarea-optimality-law`
- **Stage:** `3-formalized`
- **Type:** `THEOREM (paper) [CORPUS] [PROJECT-LOCAL NEW KNOWLEDGE]`
- **Source:** `../not_new_scientific_knowledge/halasz-ghs-adaptive-coarea-completion.md`
- **Statement:** In any GHS-type triple convolution, the correct block coordinate is the
  complementary logarithmic scale `u=log(x/p)`.  A shell of bounded multiplicative width in
  `u` has reciprocal outer and inner energies.  After the atomic prime-measure correction is
  retained, the resulting triangle/Cauchy--Schwarz certification functional has a unique
  asymptotically optimal stationary shell ratio.  The globalized bounds in the live p-dyadic
  and independent-factor routes lose this pairing.

## Novelty calibration

The GHS proof uses the shells and their cancellation; that mechanism is `[LITERATURE]`.
What is proved here is a project-local conservation and dependency theorem for the proof
architecture: it identifies the invariant, gives a valid cost for every macroscopic shell, and
proves why the three apparent walls in the live formal programme are one loss of disintegration.
Corpus and primary-source searches found the mechanism but not this abstract invariant/dependency
statement.  No claim of external publication novelty is made without a separate expert audit.

## Abstract setup

Fix `x>1`.  Put

```text
v(p)=log(x/p).
```

For `0<u<v`, define a cofactor shell

```text
P[u,v]={p prime : u<v(p)<=v}.
```

Suppose a proof has the two standard prime-supported inputs

```text
MS(sum_p c_p log p/p^(1+it))
  <= C sum_p |c_p|^2 log p/p,                           (R1)

sum_(p in P[u,v]) log p/p <= C(1+v-u),                 (R2)
sum_(q<=exp(v)) log q/q <= C(1+v).                     (R3)
```

Here `MS` is whichever frequency mean square occurs after Perron; `(R1)` is the
adaptive Gallagher--Brun--Titchmarsh theorem.  Let `L` denote the norm of the third
Euler factor after its cellwise frequency supremum.

The outer recursion coefficient is `1/v(p)`.  The inner prime factor is supported at
`q<=exp(v)`.  Therefore define the certification energies

```text
E_out[u,v] = sum_(p in P[u,v]) log p/(p v(p)^2),
E_in [u,v] = L^2 sum_(q<=exp(v)) log q/q.               (R4)
```

## Reciprocal macroscopic-shell theorem `[PROVED HERE]`

Assume `u>=u_0>0`.  Then the unconditional estimates supplied by `(R2)`--`(R3)` are

```text
E_out[u,v] <= C_(u_0) (1+v-u)/u^2,
E_in [u,v] <= C_(u_0) L^2 v,                            (R5)

sqrt(E_out[u,v] E_in[u,v])
 <= C_(u_0) L sqrt(v(1+v-u)/u^2).                       (R6)
```

### Proof

On the shell, `v(p)>=u`, so `(R2)` gives

```text
E_out[u,v]
 <= u^(-2) sum_(p in P[u,v]) log p/p
 <= C_(u_0)(1+v-u)/u^2.
```

Equation `(R3)` gives the inner estimate, and multiplication gives `(R6)`.  The additive
`1` cannot be deleted for an arbitrarily thin interval: prime measure is atomic.  This is
exactly where the first, stronger version of this theorem failed hostile review.

For a geometric shell `v=r u`, with fixed `r>1`, `(R5)` reads

```text
E_out[u,ru] <= C_r/u,
E_in [u,ru] <= C_r L^2 u,
sqrt(E_out E_in) <= C_r L.                              (R7)
```

because `u>=u_0` absorbs the additive `1`.  The two powers of `u` cancel before any triangle
inequality is taken.

## Shell-count theorem under a ratio cap `[PROVED HERE]`

Consider a partition

```text
u_0=u_0<u_1<...<u_K=U
```

and put `r_j=u_(j+1)/u_j`.  If `r_j<=R` for every `j`, then

```text
K>=log(U/u_0)/log R.                                    (R8)
```

This follows from `U/u_0=product_j r_j<=R^K`.  Equality up to the final truncated shell is
attained by the geometric partition `u_j=u_0 R^j`.  Therefore geometric shells use the fewest
blocks among interval partitions obeying the same ratio cap, while `(R7)` certifies each of
their blocks at `O_R(L)` cost.

No converse is claimed: an upper bound becoming large does not prove that an actual Dirichlet
integral is large.  Cancellation between shells can improve special functions.  The proved
claim is exactly the conservation law `(R7)` plus minimal cardinality under a fixed ratio cap.

## Optimal stationary ratio for the certificate `[PROVED HERE]`

The atomic `1` in `(R6)` does not destroy asymptotic optimization.  For a partition
`P=(u_0<...<u_K=U)`, define the dimensionless coefficient delivered by summing `(R6)` as

```text
C(P)=sum_(j<K) sqrt(r_j(r_j-1+1/u_j)),
r_j=u_(j+1)/u_j.                                       (R9)
```

Thus the `L`-part of the triangle/Cauchy--Schwarz certificate is at most a constant times
`L C(P)`.  Put

```text
c(r)=sqrt(r(r-1))/log r,        r>1,
c_* = inf_(r>1) c(r).                                  (R10)
```

Then every partition satisfies

```text
C(P) >= c_* log(U/u_0).                                (R11)
```

Indeed, discard the positive atomic term and use the definition of `c_*` shell by shell:

```text
sqrt(r_j(r_j-1)) >= c_* log r_j.
```

The logarithms telescope to `(R11)`.

Conversely, fix `r>1` and take `u_j=u_0 r^j`, truncating the final shell at `U`.  Since
`sqrt(a+b)<=sqrt(a)+sqrt(b)`, the complete shells obey

```text
C(P)
 <= K sqrt(r(r-1)) + sum_(j<K) sqrt(r/u_j)
 <= c(r)log(U/u_0)+O_(r,u_0)(1).                       (R12)
```

The second sum is geometric with ratio `r^(-1/2)`; the truncated final shell changes only the
absolute `O_(r,u_0)(1)` term.  Hence the atom affects the boundary constant but not the optimal
coefficient of `log(U/u_0)`.

The infimum in `(R10)` is attained at a unique `r_*>1`, characterized by

```text
log r_* = 2(r_*-1)/(2r_*-1).                           (R13)
```

To prove uniqueness, logarithmically differentiate `c`.  Its stationary equation is `(R13)`.
For

```text
h(r)=log r-2(r-1)/(2r-1)
```

one has

```text
h'(r)=1/r-2/(2r-1)^2.
```

On `(1,infinity)`, this derivative changes sign only at `(3+sqrt(5))/4`: `h` first decreases
from `h(1)=0`, then increases to infinity.  It therefore has exactly one further zero `r_*`.
Finally `c(r)` tends to infinity as `r` tends to either `1` or infinity, so this stationary
point is the unique global minimizer.  Taking `r=r_*` in `(R12)` and combining with `(R11)`
proves

```text
inf_P C(P)=c_* log(U/u_0)+O_(u_0)(1),                  (R14)
```

where the upper `O` uses the fixed universal number `r_*`.

`(R14)` is an optimality theorem for the proof certificate only.  It neither lower-bounds the
actual Dirichlet integral nor improves the sharp Halász theorem.  It does show that the familiar
logarithmic shell count is intrinsic to every interval disintegration evaluated solely through
the local bounds `(R2)`--`(R3)` and triangle/Cauchy--Schwarz, and it identifies the unique
stationary ratio minimizing that certificate's leading constant.

## Coarea interpretation

The logarithmic recursion disintegrates the hyperbola `pqn<=x` along the map

```text
p |-> u=log(x/p).
```

Its Jacobian appears twice with opposite degree:

- outer recursion differentiates in the cofactor direction and contributes `u^(-1)`;
- available inner q-mass has logarithmic length `u`.

After squaring, prime mean square turns these into `u^(-1)` and `u`; Cauchy--Schwarz
restores degree zero.  This is the reciprocal coarea invariant.

The invariant is lost if either factor is evaluated after forgetting `u`:

```text
outer global energy  ~ integral du/u^2,
inner global energy  ~ U,
```

In the live proof map it was also lost by p-dyadic blocks near `p=x`: a fixed multiplicative
change in `p` does not preserve a fixed multiplicative change in `u`.  The resulting divergent
upper bound is a coordinate singularity of that certificate, not evidence that large primes
must be removed from the theorem.  This diagnoses the audited route; it is not a no-go theorem
against every possible p-dyadic argument.

## Three-wall collapse `[PROVED HERE]`

The in-progress Halász map treated these as independent obstacles:

```text
(W1) outer mass near p=x,
(W2) globally capped Selberg level,
(W3) Perron height forced above the distance range.
```

They are three consequences of applying a global operation before disintegration.

1. `(W1)` results from summing `1/v(p)^2` without pairing it with inner length `v(p)`.
   Equation `(R7)` removes it with no prime deletion.
2. `(W2)` results from choosing one sieve level before the almost-diagonal neighbour count
   sees its current prime.  Choosing `Z_p=sqrt(H_p)` pointwise proves `(R1)` directly; no
   level remains to thread through shells.
3. `(W3)` results from convolving `p,q,n` and then taking a uniform coefficient bound.
   Retaining the hyperbolic factors makes the near-cutoff lattice spacing `pq`; its harmonic
   sum is paired with `(R2)`--`(R3)` and closes at `T=(log x)^2`.

Hence the surviving dependency graph is

```text
adaptive prime neighbour count
          +
cofactor-shell disintegration
          +
factor-aware Perron lattice error
          |
          v
uniform O(xL+x) bound per shell.                        (R15)
```

No induction at `sqrt(x)`, block-dependent global sieve assembly, or generic near-diagonal
coefficient theorem is mathematically required by sharp Halász.

## Failure loops

- `[FALSIFIED]` “Large p is an exceptional range.”  It is a regular small-u coarea chart; only
  `p>x/2`, where `u<log 2` and the second recursion degenerates, is discarded.
- `[FALSIFIED]` “Outer damping decays as p approaches x.”  The coefficient
  `log p/log(x/p)` grows.  What remains bounded is its energy product with shrinking cofactor
  support.
- `[FALSIFIED]` “More dyadic coefficient blocks monotonically improve the bound.”  Blocks help
  only when they retain the causal scale consumed by the other factor.  Independent Minkowski
  can preserve or worsen the loss.
- `[SURVIVOR]` Complementary-scale variables must remain attached until after the bilinear or
  quadratic estimate.  This same principle is visible in Menon's 2026 widely separated final
  prime range: prime scale and remaining cofactor cannot be optimized independently.
- `[FALSIFIED]` “The additive `1` in the prime interval bound is harmless on every partition.”
  It is not harmless on arbitrarily thin shells.  `[SURVIVOR]` Retain it in `(R9)`; along any
  fixed-ratio geometric partition its total correction is summable and changes only the boundary
  constant in `(R14)`.

## Significance for Route E

This theorem changes the formalization frontier rather than the classical theorem:

- remove `p<=sqrt(N)` from the mathematical plan;
- do not finish the global `BlockSieveLevels -> TruncatedBlockMeanSquare` threading for this
  consumer;
- replace it by one adaptive prime mean-square theorem;
- formalize ordinary, not complete, multiplicativity before claiming the Möbius consumer;
- keep the MR Buchstab-weight transfer as a separate theorem.

The full Matomäki--Radziwiłł mean-square assembly and Route E's coherent Hall/seam statement remain
open.  This law closes the sharp Halász subroute and identifies the next genuine frontier without
pretending that a long-mean theorem proves short-interval coherence.

## Lean status

Formalized unconditionally in two modules, both auditing
`[propext, Classical.choice, Quot.sound]`:

`formal/GaloisForLFunctions/RHTower/ReciprocalCoareaOptimality.lean` — the certificate analysis:

- `coareaRatioCost r = sqrt(r(r-1))/log r` and the stationarity defect
  `coareaStationaryDefect r = log r - 2(r-1)/(2r-1)` with
  `hasDerivAt_coareaStationaryDefect` (derivative `(4r^2-6r+1)/(r(2r-1)^2)`), the sign lemmas at
  the inner critical ratio `(3+sqrt 5)/4`, `strictAntiOn`/`strictMonoOn`,
  `tendsto_coareaStationaryDefect_atTop`, and `exists_unique_coareaStationaryRatio` = `(R13)`;
- `hasDerivAt_coareaRatioCost` (`= (2r-1)·defect/(2 sqrt(r(r-1)) (log r)^2)`),
  `coareaRatioCost_min` (global minimality at the stationary ratio) and `coareaMinCost_eq`
  (the infimum `c_*` is attained there) = `(R10)`;
- `log_le_card_mul_log_of_ratio_le` and `card_ge_log_div_log` = `(R8)`;
- `coareaPartitionCost` = `(R9)`, `coareaMinCost_mul_log_le_sum` and
  `coareaMinCost_mul_log_le_partitionCost` = `(R11)`,
  `coareaPartitionCost_geometric_le` = `(R12)` (with the explicit boundary constant
  `sqrt(r/u_0)/(1 - sqrt(1/r))`), and `coareaPartitionCost_geometric_optimal_le`, which with
  `(R11)` is exactly `(R14)`.

`formal/GaloisForLFunctions/RHTower/ReciprocalCoareaEnergy.lean` — the reciprocal energies, with
`(R2)`/`(R3)` supplied *unconditionally* by the corpus Mertens layer rather than assumed:

- `primeLogWindowMass` and `abs_primeLogWindowMass_sub_le` (Mertens' first theorem in window
  form, from `abs_mertensPrimeWeightSum_floor_sub_log_le`), and `abs_coareaShellMass_sub_le`
  (the cofactor shell `x e^{-v} <= p <= x e^{-u}` has prime log-density `v-u+O(1)`) = `(R2)`;
- `coareaOuterEnergy`, `coareaOuterEnergy_le` (`<= (v-u+C)/u^2`) and `coareaInnerEnergy`,
  `coareaInnerEnergy_le` (`<= L^2 (v+C_0)`) = `(R5)`;
- `sqrt_coareaEnergy_product_le` = `(R6)` and `sqrt_coareaEnergy_product_geometric_le` = `(R7)`:
  on a fixed-ratio shell the certified cost is `|L| sqrt((r-1+C/u)(r+C_0/u))`, independent of the
  scale `u` up to `O(1/u)`.

The remaining sections of this card (coarea interpretation, three-wall collapse, failure loops,
Route E consequences) are architecture statements about the live formal programme, not
formalizable theorems.

Later work on the surrounding programme should use:

- `PNTPlus.BrunTitchmarsh.primesBetween_le` for the adaptive window count;
- `RHTower.Sieve.GallagherAlmostDiagonal` for `(R1)`;
- `PrimeLogQuotientSum` and existing Mertens modules for `(R2)`--`(R3)`;
- `PerronFiniteSum` plus a new factor-aware lattice lemma for the height reduction;
- `RamareWeight`, `SmoothRough`, `SmoothSum`, `SmoothTilt` for the MR transfer.

`HTGeometry.GeneralizedDirichletMeanValue` and `HTGeometry.LargeValuesDuality` are valuable
downstream, but neither contains the adaptive prime sparsity needed in `(R1)`.

## Gates

- [x] 0 -> 1: invariant and exact falsifiers stated
- [x] 1 -> 2: reciprocal macroscopic-shell conservation and ratio-capped shell count proved
- [x] atom-corrected certification functional optimized; unique stationary ratio proved
- [x] three prior walls reduced to one order-of-operations theorem
- [x] external novelty claim withheld; project-local novelty stated precisely
- [x] 2 -> 3: formalized unconditionally (see the Lean status section)

## Log

- 2026-08-08 -- extracted after the outer-prime restriction failed against the exact GHS proof;
  paper proof and formalization consequences completed.
