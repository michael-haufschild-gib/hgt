# Controlled obstruction cohomology and the bornological shape of a hypertranscendental field

- **ID:** `hypertranscendental-controlled-cohomology-and-bornological-shape`
- **Stage:** 3-formalized
- **Type:** GENERAL HT CONTROLLED-COHOMOLOGY / FILTRATION-INVARIANCE THEOREM
- **Scientific status:** `[CORE THEOREMS PROVED] [PSEUDOMETRIC NONABELIAN COFINALITY LEAN-FORMALIZED] [EXTERNAL NOVELTY PROVISIONAL] [NOT AN RH RESULT]`
- **Parents:**
  `../2-fully-proven/new_scientific_knowledge/hypertranscendental-nonabelian-asymptotic-connection.md`,
  `hypertranscendental-flat-positive-uniformization.md`,
  `gamma-factorial-asymptotic-connection.md`
- **Successor:** `hypertranscendental-two-scale-factorial-wall.md`
- **Statement:** The topology forced by a hypertranscendental capacity connection is controlled,
  not ordinary.  Every connection on the grading ray is algebraically trivial, but its failure to
  admit a bounded primitive is a complete analytic obstruction.  This obstruction is invariant
  under changes of filtration exactly when the comparison is bornologically cofinal.  Ordinary
  cofinality and every finite collection of normalized rates are strictly too weak.

## 1. Why ordinary topology loses the obstruction

Let `Gamma` be the one-sided infinite graph with vertices `0,1,2,...`, and let a finite-rank
positive realization supply group-valued links

```text
U_n in G,                  G=GL(r,C).                              (1)
```

Their ordered partial transports are

```text
P_0=1,
P_(n+1)=U_n P_n.                                                  (2)
```

A gauge `g:Gamma^0->G` acts by

```text
U_n^g=g_(n+1) U_n g_n^(-1),
P_n^g=g_n P_n g_0^(-1).                                          (3)
```

The ray is contractible.  Indeed the gauge `g_n=P_n^(-1)` sends every link to `1`, and every flat
gauge is `g_n=g_0 P_n^(-1)`.  Thus ordinary nonabelian `H^1` sees one point.

The positive realization has more structure: an admissible gauge and its inverse must be uniformly
bounded.  Define the bounded-primitive obstruction groupoid

```text
H^1_bp(Gamma;G) := [connections on Gamma / uniformly two-sided bounded gauges].       (4)
```

This is not ordinary bounded cohomology: the connection and its primitive are allowed to be
unbounded; the question is precisely whether a bounded primitive exists.

### Theorem A: algebraic acyclicity with controlled nontriviality

For every connection `(1)`, the following are equivalent:

1. its class in `(4)` is the flat class;
2. it has a uniformly two-sided bounded flat gauge;
3. `P_n` and `P_n^(-1)` are uniformly bounded.

Consequently

```text
ordinary H^1 of the grading ray = one point,
H^1_bp of the grading ray       = the complete bounded-uniformization obstruction.    (5)
```

For `G=R` additively, taking partial sums identifies `(4)`, after fixing the value at `0`, with

```text
R^N / ell^infinity.                                               (6)
```

This is the precise topology behind the earlier rank-one asymptotic connection class.  The
hypertranscendental condition supplies a grading that never terminates; the positive analytic
realization supplies the bornology that decides which algebraic trivializations are admissible.

## 2. No finite rate spectrum is conservative

Normalized Cartan, Lyapunov, Bohl, polynomial, and logarithmic rates are quotient observations of
the full growth germ `(6)`.  The failure is not specific to linear normalization.

### Theorem B: finite-rate invisibility

Let `r_1,...,r_k:N->R_(>0)` be any nonempty finite family with `r_i(n)->infinity`.  There exists an
unbounded positive profile `h` such that

```text
h(n)/r_i(n) -> 0                 for every i.                      (7)
```

Proof.  After discarding a finite prefix, put

```text
m(n)=min_i r_i(n),
h(n)=sqrt(m(n)).                                                   (8)
```

Then `m(n)->infinity`, hence `h(n)->infinity`, while

```text
0 <= h(n)/r_i(n) <= 1/sqrt(m(n)) -> 0.                            (9)
```

Thus `[h]` is nonzero in `(6)`, although every rate in the prescribed finite spectrum vanishes on
it.  Therefore no finite collection of normalized asymptotic rates can classify bounded
uniformizability.

The strong positive replacement is the entire controlled growth germ `(4)`, not a larger finite
list of exponents.

## 3. A filtration cannot be changed by ordinary cofinality

The derivative order, a pole lattice, a spectral cutoff, a prime cutoff, and a continuation tower
are different filtrations.  The theory must say when two such filtrations are charts of one
obstruction rather than unrelated sequences.

For a scalar transport profile `h:N->R` and a sampling map `phi:N->N`, call `phi`
**bornologically cofinal for `h`** when

```text
there is C such that for every m there is n with
|h(m)-h(phi(n))| <= C.                                           (10)
```

Equivalently, the sampled path is uniformly dense in the full transport path.

### Theorem C: controlled-cofinal invariance

If `(10)` holds, then

```text
h is uniformly bounded  <->  h composed with phi is uniformly bounded.               (11)
```

One direction is restriction.  Conversely, if `|h(phi(n))|<=B`, choose `n` from `(10)` and use

```text
|h(m)| <= |h(m)-h(phi(n))|+|h(phi(n))| <= C+B.                    (12)
```

The same statement holds for `GL(r)` transport with the symmetrized multiplicative distance

```text
d_pm(P,Q)=max(log^+ ||P Q^(-1)||, log^+ ||Q P^(-1)||).            (13)
```

If the sampled path is uniformly dense for `(13)`, two-sided boundedness of the full and sampled
transport paths is equivalent.

More generally, for a profile `p:I->X` into any pseudometric space, define metric-bornological
cofinality by

```text
there is C such that for every i in I there is j in J with
dist(p(i),p(phi(j)))<=C.
```

Then boundedness of `p` is equivalent to boundedness of `p composed with phi`.  This
coordinate-free theorem is Lean-formalized.  It contains the nonabelian statement once a
transport group or positive cone is equipped with its invariant pseudometric; the remaining work
is construction and source-naturality of the particular metric, not the cofinality argument.

### Theorem D: ordinary cofinality is insufficient

Let `phi(n)=2n`, which is cofinal in the ordered set `N`, and define

```text
h(2n)=0,
h(2n+1)=n.                                                       (14)
```

Then `h composed with phi=0`, but `h` is unbounded.  A cofinal filtration can therefore erase the
entire obstruction by skipping transport spikes.  Cofinality must be controlled in the geometry
of the connection, not merely in the index order.

Every no-go has a positive successor:

- ordinary cohomology collapses, but bounded-primitive cohomology is complete;
- finite spectra lose slow escape, but the full growth germ retains it;
- ordinary cofinality loses spikes, but bornological cofinality preserves flatability.

## 4. The higher object forced by the theorems

There is no universal scalar capacity law and no privileged clock parameter.  The invariant must
range over all source-natural exhaustive filtrations and remember controlled comparison between
them.  Define the provisional **bornological HT shape** by localizing the realization groupoid at
boundedly intertwining, bornologically cofinal comparison maps:

```text
Shape_bp(HT) = {source-natural exhaustive positive filtrations with capacity connection}
               [bornologically cofinal comparisons]^(-1).        (15)
```

The capacity field is a local chart of `(15)`.  Its bounded-primitive class `(4)` is the first
obstruction layer.  Derived inverse-limit failure, positivity, rank degeneration, and reflection
must be retained by a derived self-dual completion of `(15)`.

**[CONJECTURE: UNIVERSAL BORNOLOGICAL SHAPE.]**  The derived self-dual completion of `(15)` is an
initial conservative recipient of every persistent source-natural hypertranscendental
reconstruction obstruction.  Spectral incompleteness, continuation failure, positivity failure,
monodromy, and noncanonical boundary conditions are boundary functors of this one object.

This is stronger and more falsifiable than asserting that the proof chains share a metaphor.  For
two chains to represent the same obstruction, one must construct a comparison in `(15)` and prove
it bornologically cofinal and multiplicity-conservative.  Failure has a strong positive meaning:
it produces a genuinely new filtration invariant or a second HT shape component.

**[CONJECTURE: MINIMALITY.]**  Any conservative universal HT obstruction theory must retain at
least the full controlled transport germ over the localization `(15)`.  It cannot factor through
a fixed finite stage, a scalar capacity law, a finite rate spectrum, or the ordinary cofinal type
of a filtration.

The successor factorial-wall theorem gives a strict refinement.  A single grading ray is still
insufficient: source depth and observable order can have noncommuting limits.  Thus `(15)` is the
one-directional controlled-cohomology layer of a multifiltered bornological shape over the full
directed scale cone.

## 5. Consequences for current analytic sources

The reciprocal-Gamma pole grading gives an actual nonzero scalar transport class

```text
P_n=1/n!,
P_n^(-1)=n! -> infinity.                                         (16)
```

It is therefore a source-defined chart of `(15)` on the singularity lattice.  It is not yet proved
to be the same chart as the intrinsic Kähler derivative grading.  The missing moving-base bridge
has now acquired an exact target: it must be a bornologically cofinal comparison preserving the
capacity connection, not merely a correspondence between two sequences.

The first source comparison is now proved.  If `B_n` is the normalized inverse-Gamma branch and

```text
D_n=B_n/(1-(s_n/n)B_n)
```

is the intrinsic moving-base transition, then on the common closed analytic collar

```text
sup_t |D_n(t)-B_n(t)| <= 2 |s_n/n| -> 0,
B_n -> id uniformly,
D_n -> id uniformly.                                            (17)
```

Hence the `B_n` and `D_n` analytic filtrations are same-index bornologically cofinal.  This is an
actual two-filtration source theorem, not a relabeling.  The remaining bridge is sharper: prove
that the induced positive capacity forms are boundedly congruent and that the comparison preserves
the relevant algebraic multiplicities.

For a future completed-zeta source, equality of critical zeros with a common self-dual degeneracy
spectrum would require three independent proofs:

1. construct its source-natural object in `(15)` without using the zeros;
2. compare the different proof-chain filtrations by bornologically cofinal conservative maps;
3. identify the self-dual degeneracy divisor with the zero divisor, including multiplicity.

This remains a research hypothesis, not an RH result.

## 6. External novelty gate

Established parent theories include:

- coarse cohomology theories and bornological coarse spaces,
  https://arxiv.org/abs/1711.08599;
- coarse compactifications and the universal Higson compactification,
  https://arxiv.org/abs/2009.08147;
- sublinear Higson coronas, https://arxiv.org/abs/1002.4686;
- norm-controlled cohomology, https://arxiv.org/abs/2007.02649;
- reducibility and bounded conjugacy of linear cocycles, https://arxiv.org/abs/0810.0651;
- asymptotic differential algebra, https://arxiv.org/abs/1509.02588;
- modern hypertranscendence criteria, https://arxiv.org/abs/2007.10037.

These parents prevent priority claims for coarse localization, bounded primitives, cocycle gauge
laws, or asymptotic differential fields separately.  Targeted searches located no external theorem
that constructs `(4)` from the free Kähler grading of a hypertranscendental element, proves the
capacity-realization and single-carrier no-go that force it, localizes over all source-natural
filtrations by `(10)`, and proposes its derived self-dual completion as a conservative common
obstruction object.  This is a provisional absence result, not a priority proof.

## 7. Significance and anti-theatre gate

- `[PASS]` Theorems A--D identify the required topology: controlled topology at infinity, not an
  unspecified topology and not time.
- `[PASS]` Theorem B proves that adding finitely many spectral scales cannot repair the loss of the
  full transport class.
- `[PASS]` Theorems C--D give an exact criterion for when different proof-chain filtrations may be
  compared without erasing an obstruction.
- `[PASS]` The Gamma pole bridge now has a falsifiable mathematical specification.
- `[ANTI-THEATRE]` The generic notions of coarse cohomology, bounded gauge, Higson boundary, and
  cocycle reducibility are established mathematics.  Renaming them is not new science.
- `[CANDIDATE NOVELTY]` The source-forced HT capacity construction, its algebraic-versus-controlled
  collapse, finite-rate impossibility, and localization over bornologically cofinal filtration
  charts form the candidate new package.
- `[FAIL until proved]` Initiality/conservativity of `(15)`, construction of the source-natural
  positive-cone metric and Gevrey completion, and multiplicity-conservative comparison of distinct
  obstruction functors remain open.
- `[MEDAL-SCALE VERDICT]` A proof of Universal Bornological Shape together with two genuinely
  different analytic/arithmetic source charts and multiplicity-conservative obstruction functors
  would found the proposed field.  The controlled-cofinality theorem alone does not.

## 8. Lean certificate

`GaloisForLFunctions/HTGeometry/HypertranscendentalClockBoundary.lean` verifies:

- `IsUniformlyBoundedProfile`;
- `IsBornologicallyCofinal`;
- `uniformlyBoundedProfile_subsample`;
- `uniformlyBoundedProfile_of_bornologicallyCofinal`;
- `uniformlyBoundedProfile_iff_subsample_of_bornologicallyCofinal`;
- `IsUniformlyBoundedAround`;
- `IsMetricBornologicallyCofinal`;
- `uniformlyBoundedAround_of_metricBornologicallyCofinal`;
- `uniformlyBoundedAround_iff_subsample_of_metricBornologicallyCofinal`;
- `discreteConnectionGauge_flat`;
- `discreteConnectionTransport_gauge`;
- `discreteConnectionFlatGauge_unique`.

`GaloisForLFunctions/HTGeometry/GammaCommonInverseCollar.lean` verifies the first source-defined
controlled comparison `(17)` through:

- `gammaMovingBaseTransition_dist_branch_le`;
- `tendsto_gammaMovingBaseTransition_branch_uniformlyOn`;
- `tendsto_gammaCommonInverseCollar_branch_uniformlyOn`;
- `tendsto_gammaMovingBaseTransition_uniformlyOn`.

The cached module passed a direct Lean check after the controlled-cofinality theorem was added.  No
build was run.

## Gates

- [x] identify ordinary-cohomology collapse and exact controlled positive successor
- [x] prove complete bounded-primitive criterion
- [x] prove arbitrary finite-rate spectra are incomplete
- [x] prove scalar bornological-cofinality invariance
- [x] formalize the scalar cofinality theorem in Lean
- [x] give a strict ordinary-cofinality counterexample
- [x] run targeted external parent and novelty searches
- [x] construct and formalize a bornologically cofinal comparison between two actual Gamma source
      filtrations at finite analytic resolution
- [x] formalize bornological-cofinality invariance in arbitrary pseudometric transport targets
- [ ] construct the source-natural invariant metric on the positive-matrix category
- [ ] prove the Gamma comparison preserves the positive capacity connection up to bounded
      congruence
- [ ] prove or falsify Universal Bornological Shape
