# L4: all exponentially weighted periodic phases

Cycle 21, 2026-10-08. Paper proof; Lean construction in progress.

## Exact conjecture and competing case

**L4.** For every original full-cone source `hW : WeilPositiveFull λ`,
if its actual residual phase has an exponentially weighted bilateral Fourier
representation with frequencies `2 k log r`, for any real `r > 1`, then
`λ(n)=Λ(n)` for `n≥2` and RH holds.

Final source theorem must package this as rigidity OR exclusion of every such
representation. A representation is not supplied by `hW` in this argument.
That producer remains **[OPEN CORE]** for the original WP04 assignment.

Competing case: `r^N` is an integer. A height `r^k` then has infinitely many
resonances, so the cycle-20 single-resonance argument is false in this case.
No finite Toeplitz inverse, positivity of coefficients, or new convergence
premise is allowed. The proof below inverts the complete Dirichlet convolution.

## Closed paper proof

Write `a=dirichletExp(lamLog λ)` and `b=dirichletExp(-lamLog λ)`.
Both Dirichlet series converge absolutely on `Re s>1`, by the already proved
source summability and `LSeries_dirichletExp`. Their product is one there.
Dirichlet-series uniqueness therefore gives `b*a=δ₁`. This includes the
zero coefficient, which vanishes in both series and in the convolution.

Let `p_k` be the represented coefficients and set
`K=Σ_k |p_k| exp(|k log r|)<∞`. For `y>0` define

    c(y)=sqrt(y) p_k when y=r^k, and c(y)=0 otherwise.

The index is unique because `r>1`. Each summand bound gives
`|p_k|≤K exp(-|k log r|)≤K exp(k log r)`. Hence
`|c(y)|≤K y^(3/2)` for every positive `y`.

The cycle-20 real-height residue is exactly

    B(x)=Σ_{n≥1} a(n)c(x/n),                    x>0.       (1)

Indeed its resonance equation is `n r^k=x`; its factor is
`sqrt(x) exp((2k log r-2log x)/4)=sqrt(r^k)`.
The double sum can be reindexed: each `k` has at most one resonant `n`,
each `n` at most one resonant `k`, and the displayed bound gives absolute
summability. More generally,

    Σ_{n,m≥1}|b(n)a(m)c(x/(nm))|
      ≤K x^(3/2)(Σ_n |b(n)|n^(-3/2))(Σ_m |a(m)|m^(-3/2))<∞.

Fubini and grouping by `nm` are thus justified and give the exact inverse

    c(x)=Σ_{n≥1} b(n)B(x/n).                              (2)

Cycle 20 proved `B(x+1)=B(x)` for every `x>0`, directly from the actual
reflected defect Laplace transform. No boundary continuity was assumed.

If rigidity already holds, stop. Otherwise L3p supplies a positive integer
power `r^J∈Q`. Call a positive real number a positive radical when some
positive integer power belongs to Q. Every `r^k`, including negative powers,
and every positive rational multiple of it, is a positive radical.

Classical algebraic fact: a positive irrational radical `x` cannot have
`x+1` a positive radical. For a proof take a common exponent `M≥1` with
`x^M,(x+1)^M∈Q`. Every complex conjugate `z` of `x` satisfies
`|z|=x` and `|z+1|=x+1`. Squaring gives `Re z=x` and then `Im z=0`.
Thus every root of the minimal polynomial is `x`. Characteristic-zero
separability forces degree one, so `x∈Q`, a contradiction.

For any positive irrational radical `x`, a resonance at `x+1` would express
it as `n r^k`, another positive radical. Thus `B(x+1)=0`, so periodicity
gives `B(x)=0`. Every `x/n` with `n≥1` is again an irrational positive
radical. Applying (2) yields `c(x)=0`. In particular,

    p_k=0 whenever r^k is irrational.                    (3)

Choose the least positive integer `N` with `r^N∈Q`; it exists by L3p.
The set `{k∈Z : r^k∈Q}` is a subgroup, so it equals `NZ`. Explicitly,
divide `k` by `N` with remainder `0≤j<N`; rationality of `r^k` and `r^N`
makes `r^j` rational, so minimality forces `j=0`.
By (3), reindex the phase with `q=r^N>1` and `p'_l=p_(Nl)`.
The required moment is a subseries of the old one because
`2 l log q=2 (Nl) log r`.

Write `q=u/v` in lowest positive terms. If `v≥2`, cycle-20 L2 applies.
If `v=1`, `u≥2` and cycle-16 L1 applies; its weight `u^|l|` equals
`exp(|2l log u|/2)`. These exhaust the cases and prove L4.

## Dependency and novelty audit

* Source-dependent inputs: L3p, T20, absolute forward/reciprocal convergence,
  and the already formalized L1/L2 receivers. No WP01 existence input.
* Classical bridge: Dirichlet inversion, separability, and real radical
  independence. These are not claimed as new mathematics.
* Primary external audit: Antonella Perucca, *Linear relations among radicals*,
  arXiv:2511.02498, https://arxiv.org/pdf/2511.02498. Its real-field discussion
  of Kneser's criterion supplies the parent theory for radical independence.
  The elementary two-circle proof above pays the particular fact needed here.
* Candidate corpus advance: the actual residue convolution and its inverse
  convert unit translation into elimination of every irrational radical
  harmonic, closing arbitrary real periodic bases. Scientific novelty of the
  combined application is not established by this search alone.
* This does not construct a representation for arbitrary `hW`; it does not
  prove WP04, atomicity, integer spectral masses, or RH without the original
  source and the represented-phase case split.

## Implementation checkpoints

### T21: stronger positive survivor exposed during formalization

**T21.** In any weighted countable representation of the actual source phase
whose scales `exp(ω_j/2)` are positive radicals, the aggregate coefficient at
every irrational scale vanishes. Repeated frequencies are aggregated; individual
coefficients are not asserted to vanish unless the frequency map is injective.
For a periodic representation it is injective, so every active harmonic has
rational scale. The source-only periodic alternative obtains the radical-support
condition from L3p, adding no source premise.

This is a separate, stronger conjecture than the periodic-only support step.
Its paper proof is dependency-closed by the same argument: replace `c(y)` above
by `sqrt(y) Σ_{j:exp(ω_j/2)=y} p_j`. The moment bound still gives
`|c(y)|≤K y^(3/2)` by the triangle inequality, including repeated frequencies.
Absolute convergence justifies both grouping by scale and all product-index
regrouping. Equations (1) and (2) and the radical translation proof are unchanged.
Thus `c(x)=0` at each irrational positive radical. At a positive irrational
nonradical scale it is zero by the representation's support condition.

The formal normalization is `f(y)=c(y)/y^(3/2)` for positive `y`, zero otherwise.
Its summands are `p_j exp(-ω_j/2)` at `y=exp(ω_j/2)`, making the global bound
`|f(y)|≤K` explicit without choosing a frequency representative.

Competing case audited: duplicate irrational frequencies can cancel, so only
aggregate mass is forced to vanish in the general countable result. The periodic
corollary uses `r>1` to prove injectivity. Generic bounded dilation inversion and
classical radical translation remain BRIDGE results, not standalone novelty.
The actual source support collapse is the candidate corpus advance. No claim
of independent scientific novelty or of a phase representation producer follows.

1. Actual forward/reciprocal inverse coefficients and absolute weighted
   dilation inversion.
2. Positive radical translation lemma with the elementary conjugate proof.
3. Identify real-height residues with the dilation sum and eliminate irrational
   harmonics using the actual period-one law.
4. Rational-power subgroup reindexing, L1/L2 receiver, source-only alternative.
5. Direct leaf builds, axiom audit, lint, umbrella wiring, cleanup.


## Cycle 21 final formal status

T21 is fully formalized in six new leaves, all wired once into RHTower.lean.
Each final `lake --old env lean -o <leaf.olean> <leaf.lean>` exited 0 without
diagnostics. The twenty-nine-declaration scratch name/type/axiom audit exited 0;
all dependency sets contain only propext, Classical.choice and Quot.sound.
Complete output: radical-mass-lean-audit.txt. No full or umbrella build ran.
A default-heartbeat elaboration failure in the initial sum proof was removed by
explicit finite proof stages; no heartbeat or recursion limit was raised.

L4's final rational-base reindexing is still unformalized. This is the next
step, not an assumption used by T21. Full WP04 remains OPEN.


## Cycle 22 final formal closure

L4 is proved in Lean. RationalPeriodReindex constructs the additive subgroup
of rational exponents and takes the absolute value of a cyclic generator.
L3p supplies a nonzero member, so that generator is positive. T21 puts every
active harmonic in its range; injective reindexing preserves the complete
sum and its exponential moment. RealPeriodicRigidity reduces the resulting
rational base by its coprime numerator/denominator and applies L1 or L2.
The hW-only endpoint is quantization_rigidity_or_no_real_periodic_phase.

Both new final direct leaf audits exited 0 without diagnostics. All six new
declarations and their dependencies use only propext, Classical.choice and
Quot.sound; real-periodic-lean-audit.txt contains the successful scratch audit.
Both imports occur once, with fifty-eight quantization leaves wired overall.
No heartbeat changes, computations, full builds or umbrella builds were used.

This closes the periodic represented class, not the unrestricted source
producer. The subgroup algebra is a classical BRIDGE. Independent scientific
novelty of the source application is unestablished. Full WP04 remains OPEN.
