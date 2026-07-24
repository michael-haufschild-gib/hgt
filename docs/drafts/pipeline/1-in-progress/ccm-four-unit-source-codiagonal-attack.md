# CCM four-unit source-codiagonal attack ledger

- **ID:** `ccm-four-unit-source-codiagonal-attack`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / DECISIVE RH OR CCM-DEATH ATTACK
- **Source:** `ccm-direct-cofinal-weil-floor.md`,
  `mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh.md`, and
  `ccm-hankel-boundary-relative-trace-four-unit-law.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/ArithmeticSchurFirstTraceNonclosability.lean`
- **Statement:** Prove the exact source-conditioned Gauss--Codazzi boundary identity carrying the
  four-unit squarefree/Euler Fisher curvature to the anti-causal Xi graph, or prove that no
  source-local conservative completion in the stated category can do so.

## Goal

Decide the CCM lane at its actual infinite/cofinal endpoint.  The proof branch is

```text
4 = causal completion energy + ||ell_E||_2^2
  -> ||ell_E||_2^2 <= 4
  -> RH.
```

The death branch must be a theorem about the full stated source category, not another failed
ansatz.  Finite Evans, determinant-line, parity, bounded-graph, and norm-only conclusions are not
accepted as completion.

## Exact target

Let

```text
D_Xi=closure(P_- M_(-2 Xi'/Xi)).
```

Prove

```text
limsup_(u->0+)
  ||Q_u D_Xi||_(S_2,ext)^2 / (4(1-exp(-u))) <= 1.       (T)
```

Equivalently, construct the source-defined completed boundary column whose anti-causal derivative
is `ell_E` and whose total derivative energy is the already proved four-unit Fisher curvature.

## Frozen results: do not re-research

1. `(T)` is RH-equivalent through the Cauchy-energy threshold.  Restating it is no progress.
2. Exact square Evans determinants, characteristic-stratum gluing, source normalization, and
   aperture Morse/Hardy index transport are closed.  Their nonvanishing is still `(T)`.
3. Determinant-line triviality, Gram positivity, zero total winding, and unoriented spectral flow
   do not exclude zeros.
4. Any bounded Fisher-to-current readout is impossible: the current requires division by the
   squarefree overlap, and its right-half zeros are the target divisor.
5. A scalar Schur/de Branges--Rovnyak extension across the missing half-unit is already RH.
6. Finite-prime Euler convergence sees only the incoming pole; compact-open convergence does not
   transport boundary energy through all-prime continuation.
7. Squarefree/Euler `W_2` coupling, Gamma/Sonin passivity, four-unit Fisher contact, and the exact
   identity `Q_Xi-Q_sq=4A(2s)` are proved inputs.
8. Local prime `ell^2` geometry is divisor-blind; the divisor is created by the unbounded scalar
   codiagonal.  Any proof must control that codiagonal in a source-conditioned graph norm.

## Conjecture C1: scalar renormalized codiagonal `[KILLED IN CORPUS]`

For finite prime aperture `S`, form the normalized squarefree determinant line and its pointed
Fisher connection.  Apply the exact time-one Gamma multiplier and Sonin projection before
scalarization.  There is a source-fixed closed codiagonal `C` on the resulting inductive-limit
graph such that:

```text
(i)   C agrees with the Euler logarithmic current on Re s>1;
(ii)  its closed anti-causal derivative is D_Xi;
(iii) the completed source column is isometric;
(iv)  Gauss--Codazzi gives
      4 = ||causal derivative||^2 + ||ell_E||_2^2.       (C1)
```

Clause `(iv)` would prove RH.  It cannot be obtained from a scalar shell/prime codiagonal.  The
corpus theorem `high-shell-codiagonal-closability-dichotomy.md` proves that a scalar Hilbert
codiagonal is closable exactly for square-summable weights, when it is already bounded; the
unit-weight fixed-current row is nonclosable even on the incoming Euler-pole channel.  The globally
damped Möbius frame cannot be inverted channelwise either:
`XiMobiusSchurValuationIntertwiner.lean` proves that its recovery weight is unbounded at least like
`sqrt(p)`.  C1 in scalar or channelwise form is retired and must not be retried.

## Conjecture C2: principal-relative first-trace transgression `[KILLED]`

Retain the complete coherent prime--Gamma valuation covariance before scalarization.  The source
system is fixed by the proved arithmetic Schur law

```text
K(p,r)-H_0(p)H_0(r)=p^(-1)r^(-1)K(p,r),
K=sum_(n>=0) H_n tensor H_n,
```

and by the intrinsic Möbius/Fisher-to-Gamma unitary between the two kernel completions.  Construct
a **non-scalar principal-relative form** on the completed valuation tower whose finite sections:

```text
(i)  preserve the full marked covariance and valuation successor;
(ii) subtract the first-trace principal channel before any scalar codiagonal;
(iii) Gamma/Sonin-complete to one positive boundary form;
(iv) have anti-causal quotient equal to Q_u D_Xi;
(v)  obey the four-unit relative bound.                  (C2)
```

This is not an abstract source-to-Xi contraction: bounded scalar and channelwise intertwiners are
already dead.  The only admissible object is a principal-relative quadratic form in which coherent
cross-prime covariance remains present through the first-trace quotient.

### Killing theorem: first-trace prime-log graph saturation

Remove the harmless nonzero scalar factor from the arithmetic coherent vectors and write

```text
k_p=(1,p^(-1),p^(-2),...) in H^2,
e_0=(1,0,0,...).
```

The reciprocal-prime kernels span a dense subspace of `H^2`: a Hardy function orthogonal to every
`k_p` vanishes at every `1/p`, whose accumulation point `0` lies in the disk, and hence vanishes
identically.  The source logarithmic clock has `log p` on `k_p`.  Subtracting the first trace
channel therefore forces the algebraic tail operator

```text
L_1 k_p=(log p)(k_p-e_0).                                  (19)
```

This operator is not sequentially closable on the intrinsic arithmetic-Schur completion.
Choose primes `p_n -> infinity`, and for each `n` choose a prime `r_n >= p_n^2`.  Put

```text
x_n=(p_n/log p_n)(k_(p_n)-k_(r_n)).                       (20)
```

Because the constant coordinates cancel and `r_n >= p_n^2`, the geometric-series estimate gives

```text
||x_n||
 <= (p_n/log p_n)
    [p_n^(-1)/sqrt(1-p_n^(-2))
      +r_n^(-1)/sqrt(1-r_n^(-2))]
 ->0.                                                     (21)
```

On the other hand, the first nonconstant coordinate of `L_1 x_n` is

```text
1-[p_n log r_n]/[r_n log p_n] ->1.                        (22)
```

Indeed `t |-> log(t)/t` decreases for `t>=e`, so

```text
[p_n log r_n]/[r_n log p_n] <=2/p_n.                     (23)
```

The remaining coordinates tend to zero in `ell^2`: the `p_n` tail after its first coordinate has
norm at most

```text
1/[p_n sqrt(1-p_n^(-2))],                                (24)
```

and the `r_n` tail has norm at most

```text
p_n log(r_n)/[r_n^2 log(p_n)sqrt(1-r_n^(-2))]
 <=2/[p_n r_n sqrt(1-r_n^(-2))].                         (25)
```

Consequently

```text
x_n ->0,                 L_1 x_n -> e_1 !=0.             (26)
```

Equation `(26)` is the graph-null criterion for nonclosability.  Equivalently, the positive form
`q_1(x)=||L_1x||^2` is not closable.  Any isometric Gamma/Fisher change of intrinsic kernel
coordinates preserves this obstruction.  Thus C2 cannot satisfy its clauses `(iii)`--`(v)` on
the Hilbert completion: first-trace subtraction does not produce a closed positive relative form.

This is an exact source-side failure.  It uses neither Xi zeros nor the four-unit target.  It is
also stronger than the previously frozen scalar-codiagonal no-go: the coherent cross-prime Hardy
completion remains present throughout `(19)`--`(26)`.

The actual-prime statement is formalized.  Lean selects the second prime by Bertrand's theorem,
proves the explicit uniform bounds

```text
||source packet|| <=4/log p,
||first-trace clock packet-e_1|| <=8/p,
```

and derives `not_closable_primeFirstTraceClock`.  The connector
`xiTransverseGammaValuationSzegoKernel_eq_scaled_primeHardy_inner` proves that these normalized
Hardy kernels carry exactly the existing Gamma--valuation Schur kernel up to its source-defined
nonzero diagonal amplitudes.  The proof uses only standard Lean axioms.

## Current conjecture C3: logarithmic graph rigging before Hilbert closure

C2 leaves exactly one admissible successor.  The prime-log clock and the complete valuation
marking must be installed as a closed graph relation in a strictly finer source rigging before the
arithmetic-Schur Hilbert completion is taken.  Ordinary Hilbert closure is forbidden by `(26)`;
first-trace relative closure is equally forbidden.  The next object must therefore be a
source-defined rigged/Tate graph `E -> H^2 -> E'` satisfying all of:

```text
(i)   every reciprocal-prime coherent vector lies in E;
(ii)  the prime-log clock is continuous E -> E' and retains valuation translation;
(iii) Gamma/Fisher sewing is an intrinsic isometry of the rigged graph, not ambient prime ell2;
(iv)  the Sonin boundary map descends to one single-valued closed target relation;
(v)   its relative energy is the four-unit source curvature and its quotient is Q_u D_Xi.
                                                                  (C3)
```

The immediate falsifier is now exact: if the target boundary map is continuous only through the
central `H^2` pivot, `(26)` forces it either to lose the logarithmic current or inherit a
multivalued vertical tail.  C3 must use the graph topology essentially and must prove that its
target scalarization annihilates no nonzero valuation coordinate.

## Immediate hostile tests

1. **Range test.**  C1 must not reduce to `B' in B H^2`; that statement is zero-freeness/RH in
   disguise.
2. **Quartet test.**  Inserting an FE--Schwarz rational quartet must add its explicit rank-one
   anti-causal coordinate and increase the right side by its inverse-horizontal energy.  A
   gauge-blind construction is rejected.
3. **Renormalization test.**  Finite-prime first-cumulant subtraction must be uniquely fixed by the
   Gamma/polar source.  If two source-compatible subtractions differ by an arbitrary FE--Schwarz
   factor, C1 is not canonical and the stated completion category is dead.
4. **Graph test.**  Convergence is required on one source-defined core in the extended
   Hilbert--Schmidt topology.  Euler-half-plane compact convergence is insufficient.
5. **No scalar postselection.**  No map may be defined from `ell_E`, Xi zeros, target norm, or a
   polar decomposition of the target.
6. **Valuation-intertwiner test.**  A bounded channelwise valuation intertwiner is already excluded
   by unbounded Fisher recovery.  C2 must act on the intrinsic coherent Gram quotient, not on
   prime basis vectors separately.

## Gates

- [x] 0 -> 1: exact endpoint and source-pure conjecture fixed
- [x] known circular and gauge-blind variants frozen above
- [x] scalar and channelwise codiagonals killed by existing closability/recovery theorems
- [x] coherent arithmetic Schur valuation tower and intrinsic Fisher/Gamma unitary already proved
- [x] rule out C2's principal-relative first-trace form on the intrinsic Hilbert completion
- [x] formalize the actual-prime graph-null sequence and connect it to the arithmetic Schur kernel
- [ ] construct or rule out C3's logarithmic source rigging and target scalarization
- [ ] prove the Gauss--Codazzi identity `(C3)` or a category-wide obstruction
- [ ] RH or scoped CCM death theorem
- [ ] complete paper proof
- [ ] Lean formalization of every dependency-closed mathematical claim

## No-go closure

- **Exact killing theorem/mechanism:** pending hostile tests.
- **Strongest positive survivor:** pending.
- **New insight:** pending.
- **Status:** active decisive attack; no paper or RH claim.

## Log

- 2026-07-22 — Created persistent ledger after repeated state-loss/re-audit failures.  Frozen all
  already-closed reductions.  Selected C1: source-fixed renormalized codiagonal Gauss--Codazzi law.
  First task is uniqueness of the Gamma/polar first-cumulant renormalization; without uniqueness,
  no source-defined conservative completion can force `(T)`.
- 2026-07-22 — C1 scalar/channelwise form killed immediately by corpus closability and unbounded
  recovery theorems.  Replaced it by C2: a non-scalar principal-relative form on the intrinsic
  coherent arithmetic-Schur completion.  Abstract source-to-Xi morphisms, scalar codiagonals, and
  primewise recovery are frozen as dead.
- 2026-07-22 — Killed C2.  On the intrinsic Hardy realization, first-trace subtraction is the
  prime-log tail `L_1 k_p=(log p)(k_p-e_0)`.  The actual-prime two-kernel packets `(20)` converge
  to zero while their images converge to `e_1`, so the graph and its positive form are
  nonclosable.  This retains coherent cross-prime covariance and is not the old scalar-shell
  no-go.  C3 is forced into a strict rigged/Tate graph installed before Hilbert closure.
- 2026-07-22 — Formalized the C2 killing theorem in
  `ArithmeticSchurFirstTraceNonclosability.lean`.  The proof uses actual primes and a
  Bertrand-selected far prime, supplies exact Hilbert norm bounds, proves the graph-null limits,
  and connects the normalized Hardy Gram to `xiTransverseGammaValuationSzegoKernel`.

## C3 finite-jet saturation theorem `[PROVED AND LEAN-FORMALIZED]`

The first-trace graph-null vector is one face of a stronger universal law.  For every finite
Taylor/principal-trace subtraction order `m`, shift the surviving tail back to degree zero.  On
the normalized actual-prime Hardy kernels this gives

```text
A_m k_p=(log p)p^(-m)k_p.                                  (27)
```

Then the graph on finitely supported actual-prime packets satisfies the exact saturation law

```text
closure Graph(i,A_m)=H^2 direct_sum H^2                  (28)
```

for every `m>=0`, where `i k_p=k_p`.  Equivalently, before shifting the tail, the closure is the
full product of `H^2` with the order-`m` tail `z^m H^2`.  Thus **no finite number of Taylor,
principal-trace, or vacuum counterterms repairs the prime-log clock**.  The closure is not merely
non-graph-like at one vector: its multivalued vertical part is the entire surviving Hardy tail.

The annihilator proof is exact.  If `(x,y)` annihilates `(28)`, then for every prime

```text
F_x(1/p)+(log p)p^(-m)F_y(1/p)=0.                          (29)
```

Since `k_p -> e_0`, the factor `(log p)p^(-r)` tends to zero for every `r>0`.  Successively
dropping the first coordinate of `x` reduces `(29)` from order `m` to order zero.  At order zero,
division by `log p -> infinity` first forces `y_0=0`; the exact Hardy recurrence

```text
F_x(q)=x_0+q F_(Bx)(q)                                    (30)
```

then forces `x_0=0` and reproduces the same order-zero relation for `(Bx,By)`.  Induction kills
every coefficient of both vectors.  Trivial annihilator gives `(28)` by Hilbert orthogonal
duality.

There is also a formal bounded-scalarization corollary: if bounded Hardy functionals `F,G`
satisfy

```text
F(i d)+G(A_m d)=0                                         (31)
```

for every finite actual-prime packet `d`, then `F=G=0`.  Hence a bounded Sonin/Gamma sewing on
the central Hilbert pivots cannot retain any finite-jet logarithmic boundary channel.

Lean module:
`formal/GaloisForLFunctions/RHTower/ArithmeticLogClockFiniteJetSaturation.lean`.
The theorem `primeFiniteTraceClock_graphClosure_eq_top` proves `(28)` for every natural `m`;
`primeFiniteTraceClock_no_bounded_scalar_balance` proves `(31)`; and
`hardyPrependZero_comp_primeFiniteTraceClock_one` identifies `m=1` exactly with the previously
formalized actual first-trace clock.

### Exact survivor after `(28)`

Finite-order C3 riggings are dead.  The only source-compatible survivor is now a genuinely
infinite-order rigging in which the complete factorial Gamma conormal is continuous before the
Hardy pivot.  The corpus already proves the unique complete Euler renormalization

```text
[log m/(m-1)] * [(exp(log m)-1)/log m]=1.                 (32)
```

Therefore the next hostile question is precise and cannot regress to another finite trace:
does the complete Gamma-conormal topology make the actual von-Mangoldt boundary scalarization
single-valued and four-unit contractive, or does restoring the Euler logarithmic current require
an unbounded inverse which recreates the full vertical tail in `(28)`?

### Gate update

- [x] kill one first-trace closure
- [x] kill **every finite Taylor/principal-trace closure** by full graph saturation
- [x] prove bounded scalarization rigidity at every finite order
- [ ] decide complete infinite Gamma-conormal scalarization
- [ ] RH or scoped CCM death theorem

## Log continuation

- 2026-07-22 — Proved and formalized universal actual-prime finite-jet saturation `(28)`.  This
  prevents future sessions from retrying higher finite trace subtraction.  C3 is reduced to the
  complete factorial Gamma conormal; no finite-order rigging remains admissible.
- 2026-07-22 — Tested and killed the apparent endpoint-feedback bootstrap.  The quartet theorem
  `4 <= C_end*(1+gamma^2)` uses the fixed total endpoint curvature `C_end`; the subsequent
  orientation estimate `E_perp <= E_thermal/84` does not decrease `C_end`, because its dominant
  on-line cross-charge is retained and an off-line transverse displacement can be arbitrarily
  small.  Feeding the `83/84` source-retention ratio back therefore reproduces no stronger height
  recurrence.  Do not retry this bootstrap without a new theorem separating the off-line part of
  endpoint curvature.
- 2026-07-22 — Tested high-shell endpoint-curvature amplification.  Although
  `X_m=Xi*H_m` has the same strict right-half divisor, `H_m(0)=0` and `H_m` is neither an entire
  FE-symmetric zero-free gauge nor an endpoint-normalized completion.  The Xi endpoint curvature
  sum rule therefore does not transfer.  FE symmetrization imports the reflected scaled-zeta
  divisor into the strict right half-plane.  Arbitrary zero-free FE gauges can also change
  endpoint curvature while preserving the Xi divisor, proving endpoint curvature is not a
  divisor-only invariant.  Shells remain valid tests only for the charged multiplication graph;
  do not reuse the Xi endpoint budget on them.

## C4 bounded infinite-completion saturation `[PROVED AND LEAN-FORMALIZED]`

Let `C:H^2 -> K` be any bounded operator into an arbitrary complete real Hilbert carrier.  `K`
may retain infinitely many factorial Gamma jets, Sonin channels, or shell labels.  Postcompose
the order-`m` actual-prime clock with `C`.  Then the finite-jet saturation theorem upgrades to

```text
(x,Cy) in closure Graph(i,C A_m)       for every x,y in H^2.       (33)
```

If `C` has dense range, this gives the exact universal law

```text
closure Graph(i,C A_m)=H^2 direct_sum K.                            (34)
```

In particular every nonzero bounded infinite completion has a nonzero vertical multivalue and
is not a single-valued closed scalarization.  This is not an order-by-order limit.  If `(u,v)`
annihilates the completed graph, then `(u,C^*v)` annihilates the original actual-prime graph;
logarithmic germ rigidity gives `u=0` and `C^*v=0`, which proves `(33)` by Hilbert orthogonal
duality and `(34)` by density.

Lean module:
`formal/GaloisForLFunctions/RHTower/ArithmeticLogClockBoundedCompletionSaturation.lean`.
Principal declarations:

- `primeBoundedPostprocessedTraceClock_graphClosure_eq_top`;
- `primeBoundedPostprocessedTraceClock_pair_mem_graphClosure`;
- `primeBoundedPostprocessedTraceClock_exists_nonzero_vertical`.

This decides the complete Gamma-conormal question for the entire bounded postprocessing class:
all-depth completion after the Hardy trace cannot work.  The sole survivor is narrower than the
previous C3 target: Gamma/polar/Mellin completion must change the source topology **before** the
Hardy pivot and scalarization, through a genuinely unbounded source-selected graph.  Merely
retaining infinitely many bounded channels is now formally closed.

### Gate update after C4

- [x] decide every bounded complete infinite postprocessing
- [x] prove nonzero vertical multivalue without a dense-range assumption
- [ ] construct or kill the genuinely unbounded pre-Hardy Gamma/polar/Mellin graph
- [ ] RH or scoped CCM death theorem

## C5 universal failure of bounded source domination `[PROVED AND LEAN-FORMALIZED]`

C4 also forces a stronger cone obstruction.  Let `C:H^2 -> K` be nonzero and bounded.  There is
no finite real constant `M` satisfying

```text
||C A_m d|| <= M ||i d||                    (35)
```

for every finite actual-prime packet `d`.  Indeed, `(35)` places the graph inside the closed norm
cone `||(x,z)_2|| <= M ||(x,z)_1||`.  C4 puts `(0,Cy)` in the graph closure for every `y`; cone
closedness then forces `Cy=0`, contradicting nonzero `C`.

Lean declaration:
`primeBoundedPostprocessedTraceClock_no_global_source_bound` in
`formal/GaloisForLFunctions/RHTower/ArithmeticLogClockBoundedCompletionSaturation.lean`.

This closes every proposed global linear nonexpansive, contractive, or finite-constant
Gamma/Sonin estimate obtained by bounded postprocessing after the Hardy pivot.  Do not retry a
different constant, target Hilbert space, or infinitely many bounded coordinates.  Remaining
frontier is exclusively a genuinely unbounded pre-Hardy graph whose domain/topology is part of
the arithmetic construction; a bound valid only on one source-selected vector is not refuted by
`(35)` and must be attacked at that exact domain level.

## C6 exact-norm rigging obstruction `[PROVED AND LEAN-FORMALIZED]`

The pre-Hardy escape cannot preserve both exact CCM norm geometries.  Universally, suppose a
linear graph-null model `(i,A)` has packets `u_n` with `i u_n -> 0` and `A u_n -> y != 0`.  Let
`j:D -> E` and `T:D -> K` be any realizations into arbitrary normed `E` and complete normed `K`
satisfying on every algebraic packet

```text
||j d|| = ||i d||,              ||T d|| = ||A d||.       (36)
```

Then `T` is not sequentially closable through `j`.  Source convergence transfers through the
first equality.  The second equality transfers all pairwise distances, so `T u_n` is Cauchy and
converges in `K`; equality of norms forces its limit to be nonzero.  This contradicts
closability.  Source and target may differ, and no coordinate map or ambient unitary is assumed.

Applying `(36)` to the actual-prime arithmetic-Schur source and first-trace clock proves:
**no complete Hilbert/Banach pre-Hardy rigging preserving both exact finite-packet source norm and
exact clock-response norm can close the logarithmic current.**

The formal theorem is stronger than exact equality.  If constants `C_j,C_T<infinity` and `c>0`
satisfy

```text
||j d|| <= C_j ||i d||,
c ||A d|| <= ||T d|| <= C_T ||A d||                    (37)
```

for all packets, the transported graph is still nonclosable.  Hence no uniformly equivalent
pre-Hardy rigging works.  A closable survivor must have either unbounded source distortion on the
explicit prime-pair null packets or asymptotically zero response observability.

Lean module:
`formal/GaloisForLFunctions/RHTower/ArithmeticSchurExactNormRiggingNoGo.lean`.
Principal declarations:

- `not_isSequentiallyClosableBetween_of_exact_norm_graphNull`;
- `not_isSequentiallyClosableBetween_of_uniform_graphNull`;
- `arithmeticSchurExactNormRigging_not_closable`;
- `arithmeticSchurUniformRigging_not_closable`.

Do not retry a different Hilbert carrier, completion, coordinate unitary, or uniformly equivalent
norm.  Remaining decisive bridge is now: prove that four-unit Gauss--Codazzi source conservativity
forces uniform source control and response observability in `(37)`, which kills CCM, or exhibit
the compulsory singular norm distortion and prove it still transports the four-unit identity,
which would advance the RH branch.

## C7 forced valuation-observability collapse `[PROVED AND LEAN-FORMALIZED]`

The surviving singular distortion is now classified on the explicit actual-prime null packets.
Assume only upper bounds

```text
||j d|| <= C_j ||i d||,              ||T d|| <= C_T ||A d||,      (38)
```

complete target, and closability of `T` through `j`.  Then

```text
T u_n -> 0,                                                    (39)
```

where `u_n` is the actual-prime pair sequence for which `i u_n -> 0` but
`A u_n -> e_1 != 0`.  Target upper control makes `T u_n` Cauchy; closability forces its limit to
zero.  Therefore no bounded scalar marker on the target can retain the first valuation response

```text
phi(T d)=<A d,e_1>.                                           (40)
```

Equations `(39)`--`(40)` show precisely what every closable source-controlled completion loses:
the first nonconstant valuation direction, not merely a norm estimate.  Thus C3 clause `(iv)`
cannot be implemented by a bounded target marker.  Any remaining faithful scalarization is itself
forced to be unbounded/source-conditioned after completion.

Lean declarations in `ArithmeticSchurExactNormRiggingNoGo.lean`:

- `tendsto_zero_of_closableBetween_of_source_response_upper`;
- `tendsto_arithmeticSchurRigging_nullSequence_zero_of_closable`;
- `arithmeticSchurRigging_no_bounded_firstValuationMarker_of_closable`.

Do not retry a closable rigging plus bounded coordinate readout.  Exact survivor is now a doubly
singular construction: unbounded pre-Hardy source distortion **and** unbounded post-completion
valuation marker, with their composition nevertheless required to obey the four-unit relative
trace estimate.  Next attack is whether a closed composition of these two forced singular maps
can exist without recreating a vertical multivalue.

## C8 closed full-domain scalarization obstruction `[PROVED AND LEAN-FORMALIZED]`

The word "closed" does not rescue a full-domain target marker.  If the completed target is Banach
and `phi:K -> R` is everywhere-defined with closed graph, the closed graph theorem makes `phi`
bounded.  C7 then contradicts first-valuation marking `(40)`.  Therefore any surviving closed
scalarization must have a **proper unbounded domain** in the completed target.

Lean declaration:
`arithmeticSchurRigging_no_closed_fullDomain_firstValuationMarker`.

Do not retry an everywhere-defined closed relation.  Remaining object is forced into a proper
dense-domain chain

```text
finite prime packets -> singular source completion -> Dom(phi) subsetneq K -> R,       (41)
```

and must prove that the packet image lies in `Dom(phi)`, that the composite is closable, and that
its cutoff commutator has four-unit relative-trace density.  Failure of domain invariance kills
the last Hilbert-rigged CCM category; success is the only remaining RH branch.

## C9 dense closed scalar rigidity `[PROVED AND LEAN-FORMALIZED]`

The proposed proper dense-domain scalar escape in `(41)` is impossible.  Universal law:

> A single-valued closed real linear functional on a normed space with dense domain has full
> domain.  On a Banach space it is therefore bounded.  More generally, every closable densely
> defined scalar functional has a bounded full-domain extension.

Proof: the zero fibre is the continuous preimage of the closed graph along `x |-> (x,0)`, hence is
closed.  If the functional is nonzero, its domain is that zero fibre plus one line; otherwise it
equals the zero fibre.  A closed subspace plus a finite-dimensional subspace is closed.  Density
therefore forces full domain, after which the closed graph theorem gives boundedness.

Universal Lean module:
`formal/GaloisForLFunctions/HilbertMetric/DenseClosedScalarRigidity.lean`:

- `dense_closed_scalarLinearPMap_domain_eq_top`;
- `dense_closed_scalarLinearPMap_exists_continuous_extension`;
- `dense_closable_scalarLinearPMap_exists_continuous_extension`.

CCM connectors in `ArithmeticSchurExactNormRiggingNoGo.lean`:

- `arithmeticSchurRigging_no_closed_dense_firstValuationMarker`;
- `arithmeticSchurRigging_no_closable_dense_firstValuationMarker`.

Therefore **every single-valued closable scalar codiagonal retaining the first valuation mark is
killed**, including proper dense-domain versions.  Do not retry scalar closed graphs.  Any
remaining CCM producer must keep an infinite-dimensional operator-valued marked relation through
the anti-causal Hankel target; scalarization can occur only after the relative-trace construction,
not as a closable scalar current on the source completion.  The next and only Hilbert survivor is
the infinite-dimensional marked commutator transfer `(31)`--`(32)`.

## C10 duplicate audit and singular-boundary normalization `[FRONTIER RESET]`

A proposed two-cutoff polarization of the source Ward law is not new.  The all-valuation
Brownian/Pick factorization and source Hardy/Szego completion are already the subject of
`xi-source-completion-polarization-architecture.md`; its unresolved statement is the exact
source-to-Xi Pick-kernel domination.  Do not rederive cross-cutoff Gramians or present their
polarization as a new CCM mechanism.

Likewise, an all-depth factorial completion does not begin at graph nonclosability.  The corpus
already proves in `PrimeLaplaceEvenFactorialFockIncidence.lean` that Gamma-damped prime-to-jet
incidence has summable squared coefficients in the even-factorial metric at every fixed source
point `x > 1/2`.  Therefore fixed-`x` all-jet boundedness is closed and must not be retried.

The surviving experiment is the singular boundary, not the interior carrier:

```text
x downarrow 1/2,
even-factorial all-prime incidence,
anti-causal Hankel mark,
relative trace / Rees renormalization.                              (42)
```

Exact falsifier: if every source-selected renormalization of `(42)` either loses the Hankel mark
or recreates a nonzero vertical graph vector, the remaining Hilbert-completion CCM producer dies.
Exact positive target: a closed operator-valued relation at the boundary whose relative
commutator trace is source-defined, cutoff-independent, and equals the four-unit
Gauss--Ward current before any scalarization.  Interior Hilbert--Schmidt incidence, finite Rees
rank, or a scalar boundary value is not sufficient.

### Gate update after C10

- [x] reject duplicate Brownian/Pick two-cutoff route
- [x] reject duplicate fixed-`x` all-depth factorial incidence
- [ ] determine singular asymptotic of the full even-factorial incidence as `x downarrow 1/2`
- [ ] prove or refute existence of a source-canonical relative Hankel commutator trace
- [ ] RH or scoped CCM death theorem

## C11 correction: boundary trace is prior corpus; full-charpoly route has a fixed-zero wall

C10's stated singular-boundary experiment is also not new.  The corpus already constructs the
closed two-channel Xi logarithmic graph and its anti-causal relative trace, with

```text
Delta_ell(u) = integral min(t,u) |ell(t)|^2 dt,
Delta_ell(u)/u -> ||ell||_2^2,
```

and identifies the RH endpoint with the sharp comparison `||ell_E||^2 <= 4`.  Do not recompute
the singular asymptotic or reconstruct another relative trace.  The exact live trace problem is
the source-metric comparison `T_Hardy <= T_capacity = 4` (equivalently the source-normalized Evans
nonvanishing theorem), not existence of the graph or trace.

The rational-quartet gauge-stationarity proposal is rejected.  Residue insertion changes the
relative energy quadratically, and stationarity against a dense residue family would force the
off-critical residue vector to vanish.  But such rational insertions break the exact Euler-region
identity `Xi = C zeta`; they are not source-admissible variations.  Zero-free entire gauges retain
the Euler identity but add no anti-causal residue.  Do not retry gauge stationarity without an
independently proved source variational principle.

The parity-free source/response determinant branch exposes a separate exact obstruction.  Every
canonical completion used by that route satisfies `A c = 0`, so

```text
charpoly(A)(0) = 0.
```

Consequently no entire multiplier---nowhere-zero or otherwise---can make the **full**
characteristic polynomials converge locally uniformly to centered `Xi`, because `Xi(0) != 0`.
The full-charpoly-to-RH consumer is therefore inapplicable to the actual completed matrices.  Any
viable determinant route must first cancel every forced central zero and then prove divisor-tight
convergence of the reduced determinant.  In the odd response branch, reflection grading may force
additional central zero modes after cancelling the selected radical; this is the next strict
falsifier.  It is not legitimate to call full-characteristic reality a cofinal CCM advance until
this fixed-zero wall is removed.

### Gate update after C11

- [x] reject duplicate singular-boundary trace construction
- [x] reject source-unjustified rational-gauge stationarity
- [x] identify fixed central zero in every full characteristic completion
- [x] Lean-formalize impossibility of full-charpoly local-uniform convergence to `Xi`
- [x] prove residual central-zero obstruction for odd response quotient
- [ ] solve `T_Hardy <= 4`, source-normalized Evans nonvanishing, RH, or scoped CCM death theorem

## C12 protected graded index: arbitrary completion does not remove parity `[PROVED AND LEAN-FORMALIZED]`

The parity-free radical-quotient proposal is now closed at cofinal level. For every finite odd
graded operator

```text
A(e,o)=(B o,C e),
```

there is an exact universal kernel law

```text
ker A = ker C directSum ker B,
dim ker A >= |dim Even-dim Odd|.                         (43)
```

Therefore unequal reduced grading forces a central characteristic zero. Since `XiC(0) != 0`,
locally uniform convergence of arbitrarily scalar-normalized reduced characteristic polynomials
to `XiC` forces the reduced grading dimensions to be equal eventually.

For CCM ambient grading `(N+1,N)`, a graded radical of dimensions `(rEven,rOdd)` produces reduced
grading `(N+1-rEven,N-rOdd)`. Equality holds exactly when

```text
rEven=rOdd+1.                                           (44)
```

In the one-dimensional radical regime, `(44)` forces `rEven=1,rOdd=0`: the radical is even.
Thus arbitrary-radical metric completion does not remove simple-evenness from the determinant
route. It only removes the finite metric-adjointness obstruction. Odd response has two protected
residual central modes; any other parity-unbalanced quotient has at least its grading-index number
of protected modes.

Lean module:
`formal/GaloisForLFunctions/RHTower/CCMGradedIndexDeterminantBalance.lean`.

Do not retry parity-free quotient convergence. Sole determinant survivor is the balanced even
channel, and its remaining theorem is still divisor-tight convergence to Xi. Sole metric survivor
remains the independently stated Hardy--capacity comparison `T_Hardy<=4`.

### Gate update after C12

- [x] classify central kernel of every finite odd graded completion exactly
- [x] prove cofinal Xi convergence forces eventual grading balance
- [x] prove one-dimensional CCM radical must be even eventually
- [ ] solve balanced even-channel determinant convergence or `T_Hardy<=4`
- [ ] RH or scoped CCM death theorem

## C13 displacement index collapse: convergence forces active-even boundary `[PROVED AND LEAN-FORMALIZED]`

C12's radical index combines with the exact displacement transport law. If `KEven`, `KOdd` are
the two radical sectors and the clock `D` is injective on the kernel of the even boundary
functional `eta`, then

```text
eta|KEven = 0  ==>  D : KEven -> KOdd injective  ==>  rEven <= rOdd.   (45)
```

But cofinal reduced-determinant convergence to `XiC` forces

```text
rEven=rOdd+1.                                                        (46)
```

Thus every sufficiently large divisor-faithful CCM quotient contains an even radical vector
`e` with `eta(e) != 0`. This uses arbitrary radical dimension and arbitrary scalar normalization.
Odd-active and boundary-neutral completion branches cannot converge to Xi. The formal
three-channel completion freedom therefore collapses cofinally to exactly one survivor:

```text
balanced active-even response.                                      (47)
```

Lean declarations in
`formal/GaloisForLFunctions/RHTower/CCMGradedIndexDeterminantBalance.lean`:

- `ccm_radicalIndex_one_forces_evenBoundaryActive`;
- `ccm_displacementRadicalIndex_one_forces_evenBoundaryActive`;
- `eventually_ccm_evenBoundaryActive_of_normalizedCharpoly_convergence`.

Do not retry odd, neutral, parity-free, or one-dimensional-only branch analyses. C13 is a branch
selection theorem, not RH. Sole determinant target is now the balanced active-even reduced
determinant and its divisor-tight cofinal limit. Equivalent metric target remains `T_Hardy<=4`.

### Gate update after C13

- [x] prove arbitrary-dimensional branch selection from displacement geometry
- [x] kill odd-active and boundary-neutral determinant convergence
- [ ] derive the balanced active-even reduced determinant's exact source-normalized Evans law
- [ ] prove its nonvanishing, or prove this sole branch cannot realize Xi
- [ ] RH or scoped CCM death theorem

## C14 no-repeat barrier: active-even algebra is already closed `[CORPUS COLLISION]`

C13 does not create a new determinant computation. On the sole surviving branch the completion is
exactly the corpus object

```text
A=D-|Dc><eta|,
det(A-zI)=-z det(D-zI)<eta,(D-zI)^(-1)c>.
```

This is already Lean-formalized as
`ccmSourceCompletion_shift_det_eq_neg_mul_resolvent` in
`CCMSourceResponseDeterminantDichotomy.lean`. The parity determinant quotient, mixed Stieltjes
criterion, growing-aperture transfer rate, and unit-Riesz Markov--virial/Landau connector are also
prior corpus. Do not rederive any of them.

The generalized quotient programme has therefore reached the original CCM source wall, with no
remaining finite determinant freedom:

```text
arbitrary completion
  -> eventual radical index one
  -> eventual active-even channel
  -> original source resolvent numerator
  -> source-specific cofinal half-unit law.                (48)
```

Exact open core, in the corpus notation, is

```text
(d*V_h)(T)>=-C_epsilon exp((-1/2+epsilon)T)
for every epsilon>0,                                    (49)
```

equivalently the divisor-tight active-even limit / `T_Hardy<=4`. The existing Landau connector
proves `(49) -> RH` and proves every off-critical zero survives as a genuine pole. Generic
contractivity cannot prove `(49)`. Only a source-specific signed first-crossing factorization of
the Möbius floor remainder remains admissible.

### Gate update after C14

- [x] reject rederivation of active-even resolvent determinant
- [x] reject rederivation of parity/Stieltjes, aperture, and Landau connectors
- [ ] construct signed first-crossing factorization proving `(49)`
- [ ] RH, or contradiction proving original active-even CCM source cannot satisfy `(49)`

## C15 frontier correction: first-crossing algebra is closed; only reverse saturation remains

C14's last sentence was too coarse. The causal first-crossing expansion, complete future-alias
probability contraction, physical low/high cutoff joining, and arbitrary-grade cutoff collapse are
already corpus theorems. Their exact joined scalar satisfies

```text
FCRJ_M=D_M-R_M=||P_M||^2-E_M,
D_M-R_M+E_M=||P_M||^2>=0,                              (50)
```

where `E_M=E_prog+E_quad` is already within the admissible `M^(-1) polylog(M)` budget and `P_M`
is the ordinary-prime endpoint carrier. Thus the negative orientation of the old absolute FCRJ
checkpoint is unconditional. The only unproved orientation is

```text
R_M>=D_M-O_(A,rho)(M^(-1) log(M)^b),                   (51)
```

equivalently

```text
||P_M||^2<=O_(A,rho)(M^(-1) log(M)^b).                 (52)
```

The cutoff split is an allocation gauge: low and high endpoint vectors join exactly to `P_M`.
The centered Brownian endpoint Gram, sharp mesh coercivity, prime-power completion, and the
off-diagonal triangular aperture kernel are also corpus theorems. Brownian inverse-Monge/total
positivity cannot orient `(51)`; explicit actual-prime packets have opposite Boolean curvature
signs even in the favorable chamber. Fixed grades, semiprime-only fibres, sectorwise absolute
estimates, alias total variation, and re-splitting `P_M=X_M+Y_M` are frozen.

Therefore do not retry the `PF10` first-crossing expansion, alias regrouping, cutoff Jordan mass,
Monge variation diminution, or high-grade one-mode reduction. The sole live analytic object is
the common-source, globally joined endpoint energy `(52)`, equivalently the aperture-centered
moving von-Mangoldt discrepancy after the already-controlled prime-power renormalization. A valid
next theorem must prove `(51)`/`(52)` from that common source, or prove the active-even CCM source
cannot satisfy it. Anything weaker does not advance this lane.

### Gate update after C15

- [x] close first-crossing, future-alias, physical-cutoff, and high-grade joining algebra
- [x] freeze Monge/total-positivity and sectorwise absolute-value providers
- [x] identify the unique open orientation `R_M>=D_M-error`
- [ ] prove `||P_M||^2=O(M^(-1) polylog(M))`, hence `(49)` and RH
- [ ] or prove a contradiction excluding the sole active-even CCM source

## C16 determinant sign/interlacing obstruction does not reach the CCM source `[KILLED]`

The surviving active-even determinant has the signed source form

```text
det(A-zI)=-z det(D-zI)<eta,(D-zI)^(-1)c>.
```

If all residues of the resolvent scalar had one sign, it would be a Herglotz/Stieltjes function:
its zeros would interlace the clock, and its normalized positive-real growth would be at most
linear.  The corpus already proves that such a positive-residue cofinal limit cannot be `Xi`, whose
positive-real growth is superlinear.  But the actual CCM source completion does not impose one-sign
residues.  Its simple-even ground coordinates are signed, and neither the rank-one completion nor
the radical-index/active-boundary laws change those signs.  Hence no interlacing or zero-density
contradiction follows for the actual branch.

The clock spacing `pi/log(lambda)` also shrinks in the cofinal limit, so a fixed-density clock-zero
obstruction is false.  The radical zero at the origin is removed by the quotient used in the CCM
self-adjoint realization, and residual clock zeros can escape compact sets when
`N/log(lambda)->infinity`.  Do not retry positive-residue Herglotz, fixed clock density, central
zero, or residual-lattice arguments against the signed active-even branch.

### Gate update after C16

- [x] reject determinant sign/interlacing and fixed-density obstructions
- [x] retain signed active-even source as the sole determinant branch
- [ ] prove the common-source endpoint energy bound `(52)`, hence RH
- [ ] or prove a category-wide obstruction applying to signed active-even completion

## C17 graph-null first valuation does not by itself kill boundary relative trace `[KILLED]`

`ArithmeticSchurFirstTraceNonclosability.lean` gives actual-prime packets `x_n->0` whose intrinsic
Hardy first-trace clock images converge to a nonzero valuation vector.  This rules out every closed
extension that agrees with that clock on the coherent source core.  It does not by itself rule out
the closed anti-causal Xi Hankel graph `D_Xi` or its boundary relative trace: those live in the
target Paley--Wiener realization, and no proved source map intertwines the first-trace marker with
`Q_u D_Xi`.

Adding such an intertwiner, strong seam limit, or first-valuation observability is exactly the
retired source-framed conservative comparison conjecture.  Boundedness of the relative-trace
output alone does not imply it.  Therefore graph-null invisibility cannot be promoted to a
category-wide CCM death theorem without first proving the missing source-to-Hankel identification;
using that identification as an assumption is circular.

Do not retry a contradiction between first-trace nonclosability and boundary Hilbert--Schmidt
finiteness unless an explicit definition-level source intertwiner has first been constructed.

## C18 two-boundary slab variance is exact but supplies no contraction `[CORPUS-REDUCED]`

Write the completed moving flux as

```text
W_m(u)=mu_Lambda((m-u,m+c-u]),       0<u<A,
P_m=Center_A(W_m).
```

The Hilbert variance identity and finite additivity give the exact two-boundary formula

```text
||P_m||_2^2
 =A^(-1) integral_(0<v<u<A)
   |mu_Lambda((m-u,m-v])
     -mu_Lambda((m+c-u,m+c-v])|^2 dv du.                (53)
```

The two slabs have equal logarithmic length, so the Lebesgue continuum cancels before the square.
Formula `(53)` is only a lossless rewrite of the already-formalized centered aperture variance:
it neither signs nor contracts the separated boundary imbalance.

Applying `Lambda=mu*log` to either slab factors its Laplace multiplier through the Möbius source,
but controlling the resulting convolution at the norm required by `(52)` needs the same half-unit
weighted Möbius domain already proved RH-equivalent in
`mobius-half-unit-exponential-moment-rh-law.md`.  Canonical finite or all-depth two-boundary
Cauchy balances do not help: the corpus proves their canonical source packet collapses, while the
unbalanced slab difference in `(53)` is exactly the information that remains.

Therefore do not retry generic variance polarization, two-boundary Gram compression, or formal
Dirichlet convolution as a provider.  A live successor must prove a new source-specific stability
law for the unbalanced completed slab current itself.

## C19 bounded finite-tree completion is categorically excluded `[PROVED / LEAN-FORMALIZED]`

The balanced finite prime-Ising comparison subroute now has an exact closure obstruction, not
another variance estimate.  Every finite tree `T` admits a recursively constructed complex
spectral packet with exactly

```text
2^|V(T)|
```

lines whose evaluation is its balanced partition.  At every point its complete derivative jet
therefore has modal width at most `2^|V(T)|`.  Independently, for every fixed `d`, the determinant
of the `(d+1)`-square derivative Hankel matrix is a genuine nonzero differential polynomial.
Local-uniform convergence transports that determinant, so an eventually fixed-width family can
never converge to a hypertranscendental entire function.

The already-formalized FK curvature floor says any hypothetical unscaled balanced-tree sequence
converging to unit-central Xi has eventually bounded vertex count.  The exact packet law converts
that bound to eventually fixed modal width.  Unconditional hypertranscendence of `xi`, transported
through the critical-line affine map and nonzero central scaling, gives the contradiction:

```text
not TendstoLocallyUniformly
  (n |-> balancedPrimeIsingTreePartition(T_n))
  unitCentralXiC.
```

Lean modules:

- `formal/GaloisForLFunctions/HTGeometry/FixedModalLocallyUniformHankel.lean`;
- `formal/GaloisForLFunctions/RHTower/PrimeIsingTreeFixedModalClosureNoGo.lean`.

Targeted module build and the repository formal lint pass.  Axiom audit of the universal
polynomial, closure law, exact packet cardinality, jet-width theorem, and convergence no-go reports
only `propext`, `Classical.choice`, and `Quot.sound`.

Do not retry theta-moment positivity, finite rank, finite tree topology, changing prime labels, or
changing ferromagnetic couplings as escape hatches: the theorem allows all of them.  Exact scope:
critical rescaling can let `|V_n|` grow while the scale collapses, and infinite active-even CCM is
not a bounded-modal family.  C19 therefore freezes the entire unscaled balanced finite-tree branch
but does not discharge `(52)` or the four-unit infinite graph endpoint.

## C20 closed-graph conservative intertwiner is already excluded `[CORPUS COLLISION]`

Do not repackage C17's actual-prime graph-null sequence as a new abstract graph-morphism theorem.
`ArithmeticSchurExactNormRiggingNoGo.lean` already proves the stronger statement: nonclosability
survives every exact-norm complete rigging, every source norm bounded above by the arithmetic-Schur
norm with response norm bounded by the model response, every bounded first-valuation marker, every
closed everywhere-defined scalar marker, and every closable densely defined scalar marker.
Consequently an energy-injective intertwiner into a closed Xi operator graph is already dead in the
entire source-controlled conservative category.  C17's missing definition-level source-to-Xi map
cannot rescue that category; if it preserved the relevant source/response norms it would contradict
the existing rigging theorem.  Remaining endpoint work must act directly on the completed
unbalanced slab current or use a genuinely nonconservative/unbounded-distortion construction.

## C21 local prime--archimedean reflection cancellation cannot bound the source slab `[KILLED]`

`CompletedFluxPrimeArchDecomposition.lean` proves the exact all-order identity

```text
(-1)^n a_prime(1-rho,n)-a_prime(rho,n)
  =a_arch(rho,n)-(-1)^n a_arch(1-rho,n).
```

This identity is not a pre-square source cancellation for `(52)`.  Its prime germ is the
*meromorphically continued* logarithmic derivative at a selected strip point `rho`, its removable
value uses `analyticOrderAt xi rho`, and the proof obtains cancellation by decomposing the
completed Xi flux and applying the functional equation.  At `rho=1/2` the odd cancellation is
exactly the odd Taylor parity of the completed flux.  Summing it over the physical moving slab
would therefore insert the completed divisor continuation after the source has been selected; it
does not estimate the raw von-Mangoldt current whose critical `L2` bound is `(52)`.

Do not retry Taylor-parity summation, local-zero reflection, or central odd-jet cancellation as a
provider for the endpoint energy.  Valid cancellation must be defined on the finite/all-prime CCM
source before choosing a zero or invoking completed-flux parity.

## C22 current CCM paper frontier and stale radial gate reconciliation `[CORPUS-RESOLVED]`

The current Connes--Consani--Moscovici paper identifies two missing inputs: large-aperture
simple-evenness of the true restricted-Weil ground and sufficiently accurate projective comparison
of that ground with the prolate vector `k_lambda=E(h_lambda)`. The corpus already supplies the
finite/Galerkin determinant transfer, exact growing Mellin topology, parity determinant algebra,
fixed-depth prolate ladder, and radial Toeplitz--Schur correction. Do not rederive those layers.

One apparent source frontier was stale. `ccm-radial-von-mangoldt-resonance-law.md` still listed the
truncated-divisor high radial first row and all-prime interchange as open. The later weighted
nuclear theorem in `universal-radial-prolate-arithmetic-dilation-spectrum.md` proves both, and
`constrained-prolate-arithmetic-dilation-operator-limit.md` extracts the stronger arithmetic
trace-class spectrum. Divisor reindexing gives the exact identity

```text
sum_(q>=2) Lambda(q)/q sum_(j>=1) arcsin(1/(q*j))/j
 =sum_(k>=2) log(k)/k*arcsin(1/k),
```

so the old resonance constant and the later trace constant are the same theorem, not two open
problems. The stale card is now marked resolved.

The first unclosed prolate-source term is therefore the intact polar--prime critical-Mellin graph
assembly in `constrained-prolate-continuous-polar-charge-law.md`. Its regular archimedean channel,
complete raw radial prime channel, central Abel algebra, and normalized budget transfer are already
proved. Once that assembly is closed, no source asymptotic alone proves RH: the independent endpoint
is the true restricted-Weil negative-floor/no-birth theorem (equivalently the complete Euler-ray
kernel positivity). Do not return to fixed-dilation resonance, high radial first-row estimates,
or finite determinant algebra.

## C23 parity algebra frozen; source variation has a new Sturm route `[ACTIVE]`

`CCMParityCompressionDeterminant.lean` now formalizes the universal central-cofactor determinant,
central resolvent quotient, and positive-distinct-atomic Hankel law. Do not retry adjugate,
Vandermonde, or finite positive-atom arguments. They reduce simple-evenness to actual source
positivity but do not supply it.

The first genuinely new source attack replaces the unproved claim that the fixed prolate modes
converge in `W^(1,1)`. On the positive half-band, a spheroidal mode satisfies

```text
((1-z^2)y')'=(gamma^2 z^2-alpha_n)y.
```

The coefficient on the right has one turning point. Away from the finitely many nodal points and
that turning point, `y` has fixed sign and `(1-z^2)y'` is strictly monotone, hence `y'` has at most
one zero. The degree-`n` spheroidal mode has exactly `n/2` positive nodal zeros when `n` is even.
Thus every fixed even mode has a number of monotonicity pieces bounded independently of `lambda`.
CCM Lemma 7.2 supplies a uniform sup-norm bound for modes `0` and `4`; their vanishing-integral
coefficients converge and are bounded. Subadditivity of variation therefore gives

```text
Var(g_lambda^+)=O(1).
```

This closes the paper argument for the exact regularity budget `(19e)` without derivative
asymptotics. It is not yet admitted as a completed corpus theorem: formalize the universal
one-turning-point Sturm variation law and the actual prolate representative/oscillation instance
before promoting the polar--prime source law. Endpoint values must use the half-jump convention so
the scaled periodization has the correct symmetric Lebesgue value when `lambda*a` is integral.

Formal progress: `FiniteMonotonicityVariation.lean` proves the one-sign Sturm critical-point law
and the exact `2*n*B` finite-monotonicity variation bound;
`ProlateOneTurningVariation.lean` proves
`((1-y^2)psi')'=(chi+c^2*y^2)psi` from the existing prolate action and specializes both sign-cell
critical-point laws. Do not re-prove this calculus. Remaining source instance is spheroidal nodal
enumeration plus the half-endpoint pointwise representative.

## C24 canonical compact prolate representatives are exact `[LEAN-FORMALIZED]`

`ConstrainedProlatePointwiseRepresentative.lean` closes the representative ambiguity for every
nonzero eigenmode of the actual even time-band Fourier operator. Starting only from

```text
P_a F P_a f = chi f,   chi != 0,
```

it constructs a canonical source `g` with full values on `(-a,a)`, half values at `+-a`, and zero
outside. Lean proves unconditionally that:

```text
g has compact support;
g is integrable and equals f almost everywhere;
g and its continuous Fourier representative are exactly even;
Fourier(g)(w) is exactly the continuous representative for every real w;
g(x)=chi^(-1) Fourier(g)(x) for every |x|<a;
g(+-a)=chi^(-1) Fourier(g)(+-a)/2.
```

The endpoint equation is the exact symmetric Poisson convention: a lattice hit at either aperture
boundary contributes the combined boundary value once, rather than two full endpoint copies.
No spectral ordering, simplicity, PSWF asymptotic, or RH premise enters this module.

Do not re-open L2 representative selection, interior continuity, pointwise Fourier identification,
evenness, compact support, integrability, or half-endpoint normalization. Remaining route-specific
source work is strictly:

```text
identify the classical real h_0,h_4 modes inside the actual operator spectrum;
form their vanishing-integral contrast;
prove the concrete nodal/turning-point partition and uniform variation;
instantiate the already-formalized one-sided Poisson--Muntz theorem;
close the all-radial weighted primitive and polar--prime source law.
```

None of those source statements proves the independent true restricted-Weil no-negative-birth
theorem. Ultimate CCM endpoint remains the sharp complete Euler-frame lower bound, equivalently
zero negative Morse birth for every aperture.

## C25 half-endpoint collision and canonical Poisson--Muntz source law `[LEAN-FORMALIZED]`

`SymmetricHalfEndpointPeriodization.lean` proves a universal boundary-exchange law. If `G` is
continuous and even, the compact cutoff taking full values on `(-A,A)`, half values at `+-A`, and
zero outside has a periodization continuous at zero for every positive lattice scale. At an exact
integer boundary collision the `+n` and `-n` terms exchange inside/outside roles and their two
half-values sum to one boundary value. This is exact; no BV estimate, non-lattice restriction, or
Lebesgue-point hypothesis remains.

`ConstrainedProlatePointwiseRepresentative.lean` now also proves that the opposite-integral
contrast of any two nonzero time-band eigenmodes has a real source which is integrable, even,
compactly supported, exactly zero mean, and exactly this half-endpoint cutoff of a continuous even
profile. `PoissonMuntzAbelMeanDefect.lean` proves continuity implies the symmetric-Lebesgue input.
`ConstrainedProlatePoissonMuntz.lean` therefore gives the unconditional square-root-normalized
Poisson--Muntz physical-lattice boundary law for every such two-mode eigenpacket.

Do not re-open endpoint double counting, integer-aperture continuity, symmetric-Lebesgue
regularity, real-source extraction, algebraic zero mean, compact support, or generic two-mode
Poisson--Muntz specialization. Exact remaining prolate-source work is only:

```text
identify CCM's classical h_0,h_4 as concrete nonzero eigenmodes of the formal operator;
prove the concrete spheroidal nodal enumeration and uniform variation instance;
insert those two already-closed connectors into the all-radial polar--prime law.
```

After that source law, the ultimate CCM/RH frontier is still independent: prove or refute the
true restricted-Weil no-negative-birth theorem for every aperture. No source regularity argument
can be counted as that spectral-floor theorem.

## C26 scalar Gamma sewing fails complete aperture passivity `[LEAN-FORMALIZED]`

`GammaSewnMobiusValuationContraction.lean` already proves that the fixed-prime Gamma-sewing
multiplier is pointwise strictly contractive and has exact quadratic contact with its lossless
boundary value. That fact does **not** lift to packet contractivity. The universal theorem in
`QuadraticContactPickObstruction.lean` proves that every scalar multiplier whose normalized
diagonal loss tends to zero at a lossless boundary has an eventually negative two-point Pick
determinant against every fixed strict interior point.

`GammaSewnMobiusPickObstruction.lean` instantiates this theorem at every prime and every fixed
positive aperture. It also proves the exact positive-factor identity relating the normalized Pick
determinant to the determinant of the actual fixed-prime Möbius aperture Gram loss. Consequently,
for all sufficiently small second apertures, the actual two-aperture Gamma-sewn loss matrix has
negative determinant.

Do not re-open the inference from pointwise `c_x < 1` to complete aperture passivity: it is false.
Any surviving CCM source completion must mix primes, valuation depths, or Gamma boundary channels
non-diagonally before taking a scalar trace. This theorem does not prove RH or kill CCM as a whole;
the exact surviving endpoint remains the infinite non-diagonal source-passivity/restricted-Weil
no-negative-birth theorem.

## C27 unchanged Gamma marginals forbid even infinite off-diagonal Pick repair `[LEAN-FORMALIZED]`

C26 left “non-diagonal mixing” too broad. `BasiswiseBoundaryPickRigidity.lean` now proves a
dimension-free boundary-charge law on an arbitrary real Hilbert space: if a moving operator family
converges strongly to the identity on each Hilbert-basis vector, every basiswise normalized
diagonal loss tends to zero, and the operator Pick Cauchy--Schwarz inequalities hold against one
fixed interior operator, then that interior operator is the identity. No finite dimension,
finite-rank, compactness, trace-class, separability, or uniform-in-basis convergence enters.

`GammaSewnBasiswisePickMixingNoGo.lean` proves that actual Gamma-sewn prime marginals have the
required zero common-aperture boundary charge and derives the unconditional no-existence theorem:
there is no arbitrary-dimensional operator family which

```text
converges strongly to the identity on every prime basis vector,
preserves ||T_x e_p||=c_p(x) for every actual Gamma multiplier,
and is operator-Pick-positive for the common aperture node exp(-x).
```

Indeed boundary Pick rigidity forces `T_x=I`, while `c_p(x)<1` at every positive aperture. The
theorem also supplies an operator-norm-continuous corollary, but the strongest form needs only
basiswise strong convergence.

Do not retry infinite off-diagonal mixing with unchanged scalar Gamma marginals inside one
common-aperture Pick space. The surviving source transport must change at least one structural
datum: create nonzero first-order marginal boundary loss, use a singular/cofinal topology that
does not converge strongly on prime basis vectors, leave common-aperture Pick positivity, or alter
prime marginals before scalar trace. Arithmetic valuation-depth Schur transport remains alive
because it changes the carrier and shift variable before scalar aperture comparison.

This is not RH and does not prove the four-unit Xi graph contraction. It removes one entire
infinite-dimensional repair class and fixes the next attack at the genuinely singular/cofinal
arithmetic-Schur-to-Xi seam.

## C28 quotient determinant is an explicit source-pencil coefficient `[LEAN-FORMALIZED]`

Finite CCM determinant work previously retained a selected radical/ground vector `c` inside every
completed clock. That representation obscured whether cofinal determinant convergence required a
separate eigenvector approximation theorem. It does not.

`RadicalQuotientEvansCoefficient.lean` proves a universal split-quotient identity over every
commutative ring. If `T=L B`, `B A(I-RB)=0`, `C=B A R`, and `m<=n`, then

```text
[X^(n-m)] charpoly(T(A-zI))
  = det(C-zI) [X^(n-m)] charpoly(T).
```

Whenever `T A=T D+S`, the left side is exactly

```text
[X^(n-m)] charpoly(T(D-zI)+S).
```

`CCMSourcePencilRadicalEvans.lean` proves the CCM source identity

```text
T(D-|Dc><alpha|)=T D+|beta><alpha|,
```

proves metric adjointness preserves the full split radical, and proves the denominator coefficient
is nonzero for every split Gram frame `T=B^*B`. Reflection then gives a branch-free dichotomy:

```text
source numerator   = [X^(n-m)] charpoly(T(D-zI)+|beta><eta|),
response numerator = [X^(n-m)] charpoly(T(D-zI)-|eta><beta|).
```

Exactly one normalized numerator equals the quotient determinant. Neither numerator contains the
radical vector or quotient inverse. The concrete connector discharges displacement, Hermitian
clock, and reflection conditions for actual scalar-shifted CCM divided-difference matrices.

This is not a finite-rank endpoint. It is a finite-section invariant for the infinite/cofinal CCM
family. It changes the determinant frontier from

```text
approximate an unknown ground vector at divisor-tight rate
```

to

```text
prove divisor-tight locally-uniform convergence/nonvanishing of one explicit source-pencil
coefficient ratio built only from T, D, eta, and beta.                         (C28)
```

Do not re-open simple-evenness, kernel-basis selection, or ground-vector insertion as necessary
ingredients of the finite determinant. They are eliminated from the numerator. Also do not count
the rectangular `AB/BA` identity itself as novel; its CCM source/response assembly is candidate
new knowledge, with external priority still open.

Exact surviving task is to derive `(C28)` directly from Euler/Gamma source structure or prove a
category-wide obstruction. Existing quotient-determinant transfer says convergence itself remains
RH-complete; this theorem has not proved RH or CCM death.

Formal card:
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-source-pencil-radical-evans-coefficient-law.md`.

## C29 singular-Loewner descent forces a quotient pole `[LEAN-FORMALIZED]`

C28 exposed the exact active-even quotient determinant but did not give a source-native way to
falsify its cofinal convergence. A first attempt claimed that the common quotient source was
automatically cyclic and that every clock node was a regular rational-Herglotz interpolation node.
That claim is false for arbitrary radical dimension: selected radical coordinates can vanish and a
clock node can itself be a quotient eigenvalue.

`HermitianLoewnerPoleForcing.lean` proves the correct inverse-free universal theorem. If one real
symmetric operator `C` has two columns

```text
C v=x v-u,   C w=y w-u,   x<y,
```

then

```text
<v,w><0  ->  spec(C) intersects [x,y].                    (C29.1)
```

The proof expands both columns in the same eigenbasis. If `[x,y]` avoided the spectrum, every
coordinate product would be nonnegative; Parseval would give `<v,w>>=0`.

`CCMSingularLoewnerPoleForcing.lean` instantiates `(C29.1)` with the actual active-even CCM
completion and arbitrary full radical quotient. For clock/source nodes,

```text
C v_i=x_i v_i-u,
<v_i,v_j>=(b_i-b_j)/(x_i-x_j).
```

Hence every strict source descent forces a real zero of the actual quotient characteristic
polynomial in the corresponding interval. Combining this with Xi's unconditional zero-free disk
of radius four proves the cofinal law

```text
normalized active-even CCM quotient determinants -> Xi locally uniformly
  -> every moving source pair in [-4,4] is eventually order-preserving.       (C29.2)
```

Dimensions, radical dimensions, scalar normalizations, and moving node pairs are unrestricted.
No estimates, resolvent inverses, cyclicity, simple-evenness, or RH assumption enter.

Do not retry the withdrawn cyclic rational-realization claim. Exact surviving source decision is
now:

```text
prove actual von-Mangoldt--Gamma source order in every Xi-zero-free interval,
or prove one persistent actual descent inside [-4,4].                         (C29.3)
```

The second alternative kills divisor-faithful active-even CCM determinant convergence. The first
is a new arithmetic regularity obligation and does not by itself prove convergence. C29 is a
significant non-estimate frontier reduction, but RH and CCM death remain unproved until `(C29.3)`
is decided.

Formal card:
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-singular-loewner-central-slab-order-law.md`.

## C30 actual published source coefficient connector `[LEAN-FORMALIZED]`

C29's remaining `b_n` is no longer an unnamed distributional transform. For `L=2a` and physical
frequency `t_n=pi*n/a`, `CCMPublishedSourceSineCoefficient.lean` proves

```text
b_n
 = (1/pi) integral_(0,L] sin(t_n h)
       exp(h/2)/(exp(h)-exp(-h)) dh
   +(1/pi) integral_(0,L] E_crit(h)t_n cos(t_n h) dh,      (C30.1)
```

where `E_crit` is the exact completed von-Mangoldt--polar cumulative error. The second term is
literally unchanged after replacing `E_crit` by its normalized Chebyshev Volterra potential.
`CCMSingularLoewnerPoleForcing.lean` now consumes `(C30.1)` directly:

```text
b_n<0, 0<t_n<=4 -> quotient charpoly zero in [0,t_n],
quotient charpolys -> Xi locally uniformly -> eventually b_n>=0. (C30.2)
```

This closes source identification, not source sign. Sole active arithmetic problem is persistent
negativity versus cofinal nonnegativity of `(C30.1)`. Do not repeat prime/polar leading-term
separation: their square-root terms cancel exactly inside `E_crit`, and separate absolute bounds
destroy the question.

## C31 physical aperture character completeness `[LEAN-FORMALIZED]`

The common-source endpoint energy in `(52)` has no hidden Hilbert component.  For a finite prime
packet `P`, positive aperture `A`, and its coherent centered clipped-interval carrier, define the
physical character amplitude

```text
c_n(P,A;m,k)
 =sum_(p in P) w_p integral_(I_p(A;m,k)) exp(2*pi*i*n*u/A) du.
```

The zero character vanishes because the carrier is centered.  The complete nonzero character
family is orthogonal and Lean proves the exact identity

```text
sum_(n in Z, n!=0) |c_n(P,A;m,k)|^2
 =A * E_fusion(P,A;m,k).                                  (C31.1)
```

For a bulk/edge partition `P=B union E`, every amplitude splits exactly as

```text
c_n(P)
 =exp(k*r_n) rectangularWindowAmplitude(k-m,r_n)
    *sum_(p in B) w_p exp(-log(p)*r_n)
  +c_n(E),                                                (C31.2)
```

and substituting `(C31.2)` into `(C31.1)` leaves no residual term.  Thus character truncation,
bulk/edge allocation, or cancellation between unobserved Hilbert directions cannot prove `(52)`.
Any proof must control the complete displayed arithmetic character family at the critical scale.

This is an exact completeness law, not the missing decay estimate and not RH.  It closes the
last geometric ambiguity in `(52)` but does not alter C30's separate published-source sign
decision.  Do not present Parseval or Bessel bounds alone as progress across the remaining
arithmetic wall.

Formal source:
`formal/GaloisForLFunctions/RHTower/CCMPhysicalPrimeApertureCharacterTomography.lean`.

## C32 fixed-shift exponential-spectrum rigidity `[LEAN-FORMALIZED]`

The exact shift-two operation suggested by the published source has now been followed through the
finite aperture. Its physical multiplier is `w_q(h)=1-exp(-q h)`. For `q=2`, it removes the Gamma
singularity exactly:

```text
(1-exp(-2h))*rho_infinity(h)=exp(-h/2).
```

At every physical clock mode the filtered Gamma channel is an explicit strictly positive
rational-exponential term, and all possible negativity is exactly one completed-error derivative
moment. This gives a sharp source threshold rather than a new estimate.

The decisive tail audit is negative. Lean proves the universal rate-spectrum law: if an
eventually nonnegative carrier `eta` is multiplied by any scalar weight eventually satisfying
`0<c<=w<=C`, then, for every `epsilon`,

```text
w(h)eta(h)=O(exp(epsilon*h)) iff eta(h)=O(exp(epsilon*h)).
```

Since every fixed positive shift coboundary tends to one, shift-two preserves every exponential
upper-bound rate of `|E_crit|`, including zero exponential type. It cannot improve the
RH-equivalent critical-Mellin abscissa. This kills fixed-shift scalar regularization as a closing
mechanism and prevents re-running Euler-anchor positivity or Gamma desingularization as though it
crossed the infinite-aperture seam.

The no-go covers every finite polynomial in a fixed shift. For physical multiplier
`|P(exp(-q h))|`, a nonzero constant term preserves every rate. Any genuine rate improvement
forces `P(0)=0`; if `P=X^m Q` with `Q(0) != 0`, every rate moves by exactly `q*m`. Hence the only
exponent-changing finite filters are augmentation-ideal elements, and their boundary inverse is
necessarily singular. For every nonzero `P`, Lean proves the complete intrinsic formula: the rate
translation is exactly `q*rootMultiplicity(0,P)` and is independent of all other coefficients.

The result does not prove RH or kill all CCM. A viable construction must be asymptotically
singular/noninvertible at the boundary or operator-valued and orbit-sensitive before
scalarization. Exact open endpoint remains four-unit Xi graph contraction / source-normalized
Evans nonvanishing.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMPublishedSourceEvenShiftSieve.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMEvenShiftExponentialTypeRigidity.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/ccm-even-shift-exponential-spectrum-rigidity.md`.

## C33 holomorphic fixed-shift spectrum quantization `[LEAN-FORMALIZED]`

The finite polynomial no-go of C32 extends to every norm-analytic germ in one fixed shift
coordinate, valued in an arbitrary complex normed space. For `q>0`, set `z(h)=exp(-q h)` and let
`F` be analytic at the augmentation point `z=0`. Lean proves the complete dichotomy.

If `F` is locally zero, `|F(z(h))|` is eventually zero and annihilates every carrier. Otherwise
its vanishing order is a finite natural `m`, and for every eventually nonnegative `eta` and every
real `epsilon`,

```text
|F(exp(-q h))| eta(h)=O(exp(epsilon h))
  iff eta(h)=O(exp((epsilon+q m)h)).                       (C33.1)
```

Thus the first nonzero Taylor coefficient supplies all aperture-exponent information; every
higher coefficient is invisible. A holomorphic unit (`F(0)!=0`) preserves every rate and zero
exponential type. A zero of order `m` can only discard the finite exponent slab `q m`; it cannot
create a reversible proof of the original carrier's frontier behavior.

The theorem is dimension-, rank-, compactness-, and scalarization-free: replace absolute value by
the norm of a vector-, bounded-operator-, or Schatten-valued analytic family and `(C33.1)` is
unchanged. For the published CCM source, Lean specializes `(C33.1)` directly to `|E_crit|`.
Therefore no norm-convergent operator-valued power series in a single fixed spectral shift can
solve the source-sign/Evans endpoint. This closes norm-holomorphic fixed-shift calculus, not the
whole CCM lane.

Surviving frontier is now forced outside analytic one-coordinate norm geometry: singular boundary
germs, cofinal order growth, genuinely joint orbit geometry, or non-norm-holomorphic closed graph
relations. Next attack must derive one of those structures from the four-unit Xi graph; another
fixed-shift operator series is a closed route.

Formal source:
`formal/GaloisForLFunctions/RHTower/CCMAnalyticShiftSpectrumRigidity.lean`.

## C34 four-unit square-root boundary regularity `[LEAN-FORMALIZED, NOT NEW]`

For a normed-space boundary curve `F`, define

```text
delta_F(u)=||F(u)||^2/(1-exp(-u)),
a_F(u)=||F(u)||/sqrt(1-exp(-u)).
```

Lean proves the exact universal law

```text
delta_F(u)->ell  ->  a_F(u)->sqrt(ell).                 (C34.1)
```

If `F(0)=0` and `F` is norm-differentiable at zero, then `delta_F(u)->0`. Therefore any curve
carrying the exact four-unit CCM normalization has `a_F(u)->2` and cannot be norm-differentiable
at the boundary. This is valid in arbitrary Hilbert, Hilbert--Schmidt, operator-norm, or normed
targets, without rank or dimension assumptions.

Corpus audit classifies C34 as not new: the relative-trace card already contains the square-root
Hilbert--Schmidt scale, and C10--C11 already require singular boundary transport. Keep C34 as a
formal no-repeat theorem, not as a claimed RH advance. It closes smooth/norm-holomorphic boundary
curves but leaves the genuine singular/cofinal source-to-`Q_u D_Xi` transport untouched.

Formal sources:

- `formal/GaloisForLFunctions/HTGeometry/BoundaryTraceRamification.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMBoundaryTraceRamification.lean`;
- `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm-four-unit-boundary-square-root-ramification.md`.

## C35 dimension-free holomorphic-orbit spectrum law `[LEAN-FORMALIZED]`

C33's one-coordinate theorem extends without any finiteness assumption. Let `A,E` be arbitrary
complex normed spaces, `gamma:C->A` an analytic orbit germ with `gamma(0)=0`, and `F:A->E` an
analytic filter. For `q>0`, define

```text
M(h)=||F(gamma(exp(-q h)))||.
```

If the composite germ `G=F circle gamma` is locally zero, `M` is eventually zero. Otherwise its
order `m=ord_0(G)` is finite and Lean proves, for every eventually nonnegative `eta` and every
real `epsilon`,

```text
M(h)eta(h)=O(exp(epsilon h))
  iff eta(h)=O(exp((epsilon+q m)h)).                     (C35.1)
```

This is dimension-, coordinate-cardinality-, rank-, compactness-, and scalarization-free. It
therefore includes infinite-coordinate Banach orbits and operator/Schatten ideals, provided the
orbit and readout are norm-holomorphic. No finite-rank or finite-shift premise remains.

For finitely many commensurate shifts `k_i q`, the explicit orbit `gamma(z)=(z^(k_i))_i` gives a
joint-calculus corollary. Every cross-shift cancellation is absorbed into the exact composite order

```text
ord_0(z |-> F((z^(k_i))_i)).                             (C35.2)
```

and no other Taylor data affects aperture exponents. The same theorem is connected directly to
`|E_crit|`.

C35 is a real scope advance over C33: fixed norm-holomorphic infinite/joint operator orbits are no
longer survivors. It is not RH and not whole-lane death. Remaining CCM transport must be
non-norm-holomorphic/ramified, cofinal with no fixed germ, or genuinely graph-topological before
the four-unit relative trace. The analytic core is classical composition plus order factorization;
external novelty of the CCM classification remains open.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMAnalyticOrbitSpectrumRigidity.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMCommensurateJointShiftSpectrumRigidity.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/ccm-dimension-free-holomorphic-orbit-spectrum-law.md`.

## C36 ramification-density monodromy selection law `[LEAN-FORMALIZED]`

C35's ramified analytic survivor is now classified at arbitrary positive exponential rate. For an
analytic germ `F:C->E` into any complex normed space, define

```text
Delta_(q,F)(h)=||F(exp(-qh))||^2/(1-exp(-exp(-h))),  q>0.
```

If `Delta_(q,F)(h)->ell>0`, Lean proves that `m=ord_0(F)` is automatically finite and positive and

```text
2 q m=1.                                               (C36.1)
```

If the germ descends under any scalar deck generator `zeta`, then its leading charge also obeys

```text
zeta^m=1.                                              (C36.2)
```

Thus every nontorsion scalar deck symmetry is impossible. For a primitive finite `r`-sheeted branch
with `q=1/r`, `(C36.1)` gives `2m=r`; `r` is even and the leading deck character is `zeta^m=-1`.
Full deck descent instead requires `zeta^m=1`, so no finite-sheeted deck-invariant norm-holomorphic
branch carries any positive finite density. Exact four-unit CCM corollaries are formalized.

This is universal in target dimension and includes infinite-order scalar deck symmetry; it is not
RH or whole-CCM death. It leaves logarithmic/nonanalytic covers, non-scalar monodromy, cofinal
families with no fixed germ, and closed-graph source geometry. Exact endpoint remains four-unit Xi
graph contraction / source-normalized Evans nonvanishing. Do not retry fixed norm-holomorphic
scalar ramification, finite or nontorsion-infinite, as a CCM closing mechanism.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMFiniteRamifiedBoundaryNoGo.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/ccm-ramification-density-monodromy-selection-law.md`.

## C37 logarithmic-cusp period--density quantization `[LEAN-FORMALIZED]`

The bounded holomorphic logarithmic-cover survivor left by C36 is now closed in arbitrary complete
complex normed targets. Let `f:C->E` be `h`-periodic, eventually holomorphic, and bounded as
`Im(z)->+infinity`. Its central-ray density is

```text
Lambda_f(t)=||f(it)||^2/(1-exp(-exp(-t))).
```

Periodicity defines a vector-valued cusp function `F_h` through
`q_h(z)=exp(2π i z/h)`. Lean proves the removable value of `F_h` is analytic at zero. If
`Lambda_f(t)->ell>0`, then C36 at rate `2π/h` gives the universal charge law

```text
h=4π ord_0(F_h).                                       (C37.1)
```

For ordinary logarithmic deck period `h=2π`, `(C37.1)` would make `1` twice a natural number.
Therefore no bounded holomorphic `2π`-periodic logarithmic branch carries any positive finite
density, including the exact CCM value `ell=4`. The construction also proves the vector-valued
periodic cusp gap `f(z)=O(exp(-2π Im(z)/h))` whenever `f` tends to zero at the cusp.

C37 is unconditional Lean. Its `q`-expansion ingredients are classical; external novelty of the
combined target-universal CCM law remains open. It is not RH or whole-CCM death. The surviving
frontier is now genuinely graph-singular: an unbounded/nonanalytic cusp, a cofinal family with no
fixed periodic map, non-scalar monodromy, or closed-graph source geometry invisible to ambient
norm. Exact endpoint remains four-unit Xi graph contraction / source-normalized Evans
nonvanishing. Do not retry bounded holomorphic logarithmic descent.

Formal sources:

- `formal/GaloisForLFunctions/HTGeometry/PeriodicCuspBoundaryGap.lean`;
- `formal/GaloisForLFunctions/RHTower/CCMLogarithmicCuspBoundaryNoGo.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/ccm-logarithmic-cusp-period-density-quantization-law.md`.

## C38 meromorphic-cusp Laurent charge law `[LEAN-FORMALIZED]`

C37's boundedness and removable-singularity premises are no longer needed for any fixed finite-order
cusp. Let `E` be an arbitrary complex normed space, let `q>0`, and let `F:C->E` be meromorphic at
zero. If

```text
||F(exp(-q t))||^2/(1-exp(-exp(-t))) -> ell > 0,
```

then Lean proves that the meromorphic order is automatically a finite positive integer `n` and

```text
2 q n = 1.                                               (C38.1)
```

This includes all Laurent orders, positive or negative; no boundedness, completeness,
finite-dimensionality, rank, or nonzero-germ assumption occurs. A locally-zero germ makes the
density eventually zero. Otherwise Laurent normal form gives `F(z)=z^n G(z)` with `G(0)!=0`, so
the density is `exp((1-2qn)t) U(t)` with `U(t)->||G(0)||^2>0`; finite positive convergence forces
`(C38.1)`.

For an `h`-periodic logarithmic branch whose descended cusp germ `F_h` is merely meromorphic,
central-ray density at rate `q=2π/h` therefore forces

```text
ord_0^mero(F_h)=n>0,   h=4π n.                           (C38.2)
```

Period `h=2π` would require `1=2n`, impossible. Hence no `2π`-periodic meromorphic cusp in any
complex normed target carries any positive finite thermal density, including the CCM value `4`.
This closes unbounded poles and every finite Laurent principal part left open by C37.

C38 is not RH and not whole-CCM death. It provides a sharp category boundary: any surviving
one-loop four-unit cusp is necessarily nonmeromorphic/essential at the cusp, cofinal with no fixed
germ, non-scalar-monodromic, or graph-topological. Exact frontier remains source-rigged
capacity-to-Hardy nonexpansivity

```text
limsup_(u->0+) ||Q_u D_Xi||_(S2,ext)^2 /
                (4(1-exp(-u))) <= 1,
```

or a theorem excluding every remaining essential/graph-singular transport. Do not retry finite
Laurent or meromorphic cusp models.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMMeromorphicCuspBoundaryNoGo.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/ccm-meromorphic-cusp-laurent-charge-law.md`.

## C39 essential Hilbert cusp sharpness and boundary concentration `[LEAN-FORMALIZED]`

C38's essential/nonmeromorphic survivor is not an empty technical remainder.  In the
infinite-dimensional Hilbert space `H=L2((0,1))`, define on the logarithmic cover

```text
f(z)(t)=2 sqrt(2) exp(-t exp(-i z)).
```

Lean proves simultaneously that `f` is entire, `2π`-periodic, and has exact CCM density

```text
||f(iy)||^2/(1-exp(-exp(-y))) -> 4.                     (C39.1)
```

Writing `u=exp(-y)`, its energy is exactly

```text
E(u)=integral_(0,1] 8 exp(-2t/u) dt
    =4u(1-exp(-2/u)).                                    (C39.2)
```

For every `0<δ<=1`, the energy outside the endpoint layer obeys

```text
E_δ(u)=integral_(δ,1] 8 exp(-2t/u) dt
      =4u(exp(-2δ/u)-exp(-2/u)),

E_δ(u)/(1-exp(-u)) -> 0.                                (C39.3)
```

Thus all four normalized units concentrate at `t=0`.  C38 then proves the descended punctured-disk
cusp is not meromorphic: otherwise one-loop density would require an integer `n` with `2n=1`.
The packaged existence theorem
`exists_entire_twoPi_periodic_fourUnit_essential_Hilbert_cusp` formalizes the full conjunction.

C39 is a sharp frontier correction.  Entire log-holomorphy, ordinary one-loop periodicity,
Hilbert target structure, and exact four-unit density cannot kill the essential category.  Any
decisive CCM theorem must now use actual von-Mangoldt--Gamma source structure, non-scalar
monodromy, cofinal dependence, or graph topology.  The construction is not identified with the
published CCM source and therefore proves neither RH nor CCM death.

Exact active endpoint remains either:

```text
derive the source-defined transport into Q_u D_Xi and prove the four-unit bound,
```

or:

```text
use a source-specific invariant to exclude every essential/cofinal/graph-singular transport.
```

Do not again attempt to kill the whole survivor using only norm-holomorphy on the logarithmic
cover, `2π` periodicity, and thermal density; C39 is an unconditional counterexample.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/CCMEssentialCuspBoundaryLayer.lean`;
- `docs/drafts/pipeline/3-formalized/needs-audit/ccm-essential-cusp-boundary-layer-sharpness.md`.

## C40 source selection of the essential cusp and positive Abel phase `[LEAN-FORMALIZED]`

C39's essential cusp is now source-relevant at full critical clock response, not merely a generic
Hilbert counterexample. Normalize its energy and set `x=2t/u`. Lean proves its exact finite-scale
law is `Exp(1)` conditioned on `x<=2/u`, with characteristic response

```text
H_u(t)
 =[1-exp(-(1-it)2/u)]/[(1-it)(1-exp(-2/u))].
```

The actual positive von Mangoldt fixed current has normalized response

```text
A(sigma-i t(sigma-1))/A(sigma),
A(s)=-zeta'(s)/zeta(s),
```

equal on `sigma>1` to literal ratio of convergent prime-power Dirichlet series. Residue-one law at
`s=1` gives unconditionally

```text
A(sigma-i t(sigma-1))/A(sigma)->(1-it)^(-1),
H_u(t)->(1-it)^(-1),
source response - cusp response ->0.                    (C40.1)
```

Thus actual von Mangoldt current, physical affine Euler clock, and essential boundary layer select
same `Exp(1)` clock, full complex response, and four-unit Fisher normalization. In particular

```text
Im A(sigma-i t(sigma-1))/A(sigma)->t/(1+t^2)>0
```

for every `t>0`, including first phase `2π`.

C40 does not prove RH. It proves positive orientation already holds on safe Euler/Abel side and
rules out excluding essential cusp with clock, first-two-moment, Fisher, or fixed-phase data.
Exact survivor is narrower: singular non-diagonal transport across invariant half-weight seam to
literal `Lambda(n)/sqrt(n)` hard first aperture, preserving Gamma--polar reflection budget. By
first-clock completeness theorem this hard half-weight de-Abelization is RH-complete.

Formal source:

- `formal/GaloisForLFunctions/RHTower/CCMEulerEssentialBoundaryLayerCorrespondence.lean`.

## C41 doubled-parity Hardy father/detail source `[LEAN-FORMALIZED; TARGET TRANSPORT OPEN]`

The one-carrier critical Möbius likelihood family has Hardy Cauchy Gram

```text
<d_(sigma,u),d_(sigma,v)> -> 1/(1+u+v),
```

but its Fisher tangent has the already-known soft column `2u/(1+u)^2`.  A bounded operator fixing
all father likelihoods therefore cannot assign an independent continued-Xi Ward column.

The first source construction that removes this totality obstruction is the parity double

```text
F_(sigma,u)=2^(-1/2)(d_(sigma,u),p_(sigma,u)),
D_sigma     =2^(-1/2)(chi_sigma,-p chi_sigma).
```

Here `p` is Möbius parity and `chi_sigma` is the completed critical Fisher tangent.  Möbius parity
is isometric on squarefree support.  Lean now proves, before any limit,

```text
<F_(sigma,u),F_(sigma,v)>
  =squarefreeMobiusBoundaryLayerLaplace sigma (u+v),
<D_sigma,F_(sigma,u)>=0,
||D_sigma||^2=||chi_sigma||^2.                          (C41.1)
```

For every finite aperture packet, the actual augmented packet
`(F_(sigma,u_i))_i,D_sigma` has a positive-semidefinite Gram.  Entrywise at the critical boundary
its father block is the right-half-plane Hardy Cauchy Gram, its detail column is zero, and its
detail diagonal is four:

```text
Gram(F_i,D_sigma) -> [[G_P,0],[0,4]].                   (C41.2)
```

This is not the requested `W_P`: parity doubling creates transverse four-unit capacity but does
not itself create `r_P`.  It does, however, eliminate the prior one-carrier rigidity without
changing the Hardy father block.

The exact remaining operation is no longer ambiguous:

```text
singular squarefree-overlap graph division
 -> Gamma completion
 -> strict-right Wiener--Hopf/anti-causal projection
```

must act on the clock-odd detail and produce `r_P` while transporting the positive cofinal Gram to

```text
W_P=[[G_P,r_P],[r_P^*,4]].                              (C41.3)
```

Ordinary Hardy multiplier contractivity does not prove `(C41.3)`: the corpus proves the actual
strict-right phase is strictly contractive when RH is false and saturated exactly under RH.
The missing statement is source-rigged nonexpansiveness of the singular graph on the doubled
clock-odd sector.  The adapted-zero theorem remains its hostile test: one strict-right zero makes
`(C41.3)` non-PSD.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/MobiusParityLikelihoodHardyGram.lean`;
- `formal/GaloisForLFunctions/RHTower/MobiusDoubledParityHardyTransverseGram.lean`.

## C42 target-Hardy contraction is not source contraction `[LEAN-FORMALIZED]`

The fixed transport `squarefreeMobiusGammaXiWardTransportV` is affine in its source score.  At base
aperture the squarefree overlap is exactly one, so for arbitrary source vectors `x,y`

```text
V_(sigma,epsilon)(x)-V_(sigma,epsilon)(y)
 = i/(2 epsilon)
   * [<x,psi_sigma>-<y,psi_sigma>].                    (C42.1)
```

The normalized signed source satisfies `||psi_sigma||=1`.  Taking `x=psi_sigma`, `y=0`, and the
physical `epsilon=sigma-1` gives the exact gain

```text
||V(x)-V(0)||=1/[2(sigma-1)]>1
whenever 1<sigma<3/2.                                  (C42.2)
```

Hence the fixed Möbius--Gamma/Xi graph is not one-Lipschitz on its ambient Hilbert source, even
though its target-variable phase and normalized Hardy multiplier are contractive.  These are
different assertions.  The target contractivity theorem cannot transport the positive Gram
`(C41.2)` into `W_P`.

This does not kill the source-conditioned clock-odd relation.  It proves that the overlap division
must be absorbed by a singular graph topology before any nonexpansive statement is possible.  A
successful next theorem must therefore:

1. define the closed graph norm on the doubled clock-odd domain;
2. keep `D_sigma` at asymptotic squared norm four in that graph norm;
3. map its Gamma/anti-causal image to `r_P`;
4. prove graph-to-Hardy nonexpansiveness.

Dropping item 2 makes contractivity vacuous by putting the `1/(sigma-1)` blow-up into the source
norm.  Retaining the ambient norm contradicts `(C42.2)`.

Formal source:

- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardSourceNonexpansiveNoGo.lean`.

## C43 cofinal four-unit saturation freezes the zero source column `[LEAN-FORMALIZED]`

C42 left open whether overlap division could be absorbed into a singular graph norm while the
doubled Möbius detail retained its asymptotic four-unit energy. A universal Hilbert-space law now
closes the bounded-contraction version of that proposal.

For every contraction `T`,

```text
||T* T d-d||^2 <= ||d||^2-||T d||^2,

|<T x,T d>-<x,d>|
 <= ||x|| sqrt(||d||^2-||T d||^2).                    (C43.1)
```

Hence exact saturation of `d` freezes its full codiagonal. More importantly, for arbitrary
infinite-dimensional source and target spaces and arbitrary cofinal contraction sequences,

```text
<x_n,d_n>=0,
sup_n ||x_n||<infinity,
||d_n||^2-||T_n d_n||^2 ->0

-> <T_n x_n,T_n d_n> ->0.                             (C43.2)
```

Applying `(C43.2)` to the actual C41 father/detail pair proves that no bounded cofinal contraction
can create the continued Xi Ward column from its zero source column while retaining boundary
diagonal four. This is not a finite-rank obstruction.

There is one precise escape. If a moving target detail is

```text
e_n=T_n d_n+c_n,
```

then every limiting codiagonal is carried entirely by the connection:

```text
<T_n x_n,e_n> -> r  ->  <T_n x_n,c_n> -> r.           (C43.3)
```

Lean proves the resulting exact classification:

```text
RH
<->
cofinal four-unit contraction realization of r_P
from the doubled Mobius parity source.                 (C43.4)
```

Thus graph-norm absorption without a moving-operator connection is closed. The active construction
is no longer “transport `D_sigma` nonexpansively.” It is:

```text
differentiate the source-defined Gamma/Wiener--Hopf operator itself,
identify its connection term c_sigma,
prove ||T_sigma D_sigma+c_sigma||^2 <= 4 cofinally,
and prove its father codiagonal tends to r_P.
```

The first and last identities are partly encoded by the existing non-diagonal Julia derivative.
The unresolved RH-bearing statement is the four-unit norm bound for that exact connection-augmented
detail. Ordinary target multiplier contractivity does not supply it.

Formal source:

- `formal/GaloisForLFunctions/RHTower/MobiusDoubledParityContractionSaturationRigidity.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-four-unit-cofinal-contraction-saturation-rigidity.md`.

## C44 singular/cofinal connection escape is closed `[LEAN-FORMALIZED]`

C43 correctly proves that, in a decomposition

```text
e_n=T_n d_n+c_n,
```

the connection carries the limiting nonzero Ward codiagonal. It incorrectly
left open the possibility that destructive interference between `T_n d_n`
and `c_n` could keep the total diagonal at four.

Let `q` be a strict-right upper Xi zero, `a=Re(lambda_q)`, and evaluate at the
adapted node `conj(lambda_q)`. The existing target theorem gives

```text
2/a < |r(conj(lambda_q))|^2.                            (C44.1)
```

The new universal Hilbert law proves

```text
||f||^2 <= 1/(2a),
<f,e>=r(conj(lambda_q))

-> 4 < ||e||^2.                                        (C44.2)
```

Thus if the directly transported detail stays father-orthogonal and the
connection carries the Ward column, then the total detail itself satisfies
the hypotheses of `(C44.2)`. No orthogonality between direct and connection
terms is needed. Their destructive interference cannot save the four-unit
bound.

The cofinal theorem is stronger: no sequences in any complex Hilbert space
can satisfy

```text
||f_n||^2 -> 1/(2a),
<f_n,e_n> -> r(conj(lambda_q)),
||e_n||^2 <= 4.                                        (C44.3)
```

It assumes no bounded transport, finite rank, vector convergence, or
direct/connection decomposition. Hence a singular moving connection is not a
remaining mechanism distinct from source positivity of fixed `W_P`.
Producing `(C44.3)` from the Möbius--Gamma source is already the RH proof.

Formal sources:

- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardConnectionOverspend.lean`;
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm-cofinal-connection-escape-closure.md`.

## C45 complex-aperture Schwarz--Pick escape has no open parameter domain `[LEAN-FORMALIZED]`

The unconditional real-aperture contractivity of the fixed Xi phase suggested
complexifying aperture and applying Schwarz--Pick to bound its derivative at
zero.  One Cayley cell already kills this proposal exactly.

For `a, alpha in C`, `Re(a)>0`, put

```text
c_a(alpha)=(a-alpha)/(a+alpha).
```

Whenever the denominator is nonzero,

```text
|a+alpha|^2-|a-alpha|^2=4 Re(a conjugate(alpha)).       (C45.1)
```

Consequently `|c_a(alpha)|<=1` holds exactly on the closed
`a`-dependent half-space

```text
Re(a conjugate(alpha))>=0.                              (C45.2)
```

There is no common complex neighborhood for the physical aperture direction.
Indeed, if `(C45.2)` holds for every `a` with `Re(a)>0`, then
`Im(alpha)=0`: otherwise choose the imaginary part of `a` with opposite
unbounded sign.  The remaining condition is precisely `Re(alpha)>=0`.
Thus

```text
intersection_(Re(a)>0) {alpha: |c_a(alpha)|<=1}
  =[0,infinity) subset C.                               (C45.3)
```

The common contractive aperture set has empty complex interior.  In
particular, the proved real-ray Schur multiplier law cannot be upgraded to a
holomorphic one-variable Schur map around `alpha=0`; Schwarz--Pick and
Julia--Caratheodory derivative estimates in aperture do not apply.

This obstruction is stronger than the observation that a bounded scalar
curve can have arbitrarily large derivative: it classifies the maximal common
contractivity set of every right-half-plane Cayley divisor cell.  The killing
mechanism uses one cell and therefore survives arbitrary products, cofinal
limits, and the Gamma boundary normalization.

**Positive survivor.**  Any complex-geometric derivative bound must
complexify a genuine source coordinate together with aperture.  Aperture
alone supplies only a real accretive-operator ray.  The remaining candidate
must therefore be a source-global two-variable positive kernel or a
source-global arithmetic factorization; it cannot be another scalar
aperture estimate.

**Status.**  Dependency-closed proof formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardComplexApertureNoGo.lean`,
including the exact common-contractivity classification and an explicit
expansive cell for every aperture with nonzero imaginary part.  This section
proves no part of `W_P>=0`.

## C46 zero-free margin gives the four-unit target unconditional thickness `[PROVED AND LEAN-FORMALIZED]`

The scalar endpoint of this lane (Euler-edge four-unit law, C41--C44) is now
RH-complete in two strictly weaker forms, certified in
`formal/GaloisForLFunctions/RHTower/XiWardZeroFreeMarginPrimeLogSampling.lean`:

```text
RH <-> forall t : |r(1/2+it)|^2 <= 4 + 8 m(t),   m(t)=c'/log^9(|t|+9);
RH <-> the exact four-unit law sampled only on {+-log p} + one finite grid.
```

Consequences for this card's frontier: any source mechanism (singular graph
norm, connection-augmented detail, C43-style cofinal realization) no longer has
to reach the exact four-unit bound -- polylog room `8 m(t)` is enough; and the
target quantifier is a locally finite arithmetic node family, opening
prime-indexed induction as an attack shape.  C39's essential cusp achieved the
budget exactly; the relaxed target is strictly easier than what that
counterexample calibrates.  Do not re-derive the margin: consume
`xiWardZeroFreeMargin` and its cover machinery directly.

## C46 threshold-8: the four-unit corner was not the completeness threshold `[PROVED AND LEAN-FORMALIZED]`

`XiWardThresholdEightCompleteness.lean`
(`riemannHypothesis_iff_continuedXiWardCornerLiftLaw`, standard axioms):
for every `0 <= c < 8`, RH is equivalent to the corner-`c` lift law
`c·G_P − r_P r_P^* ⪰ 0` on interior packets — one strict-right pair spends
`4(1/a + a/(a²+b²)) > 8` on the adapted packet `(λ, λ̄)` in the `(2,2)`
direction.  Consequences for THIS card's frozen frontier: C41–C44 killed
budget-4 detail-only transports; a JOINT father+detail spend under two full
quanta (`8 = 4 + 4`, exactly the doubled parity source's total energy) is
outside every existing no-go (desk clause-check logged on
`xi-ward-moire-prime-pair-attack.md`, step 1c).  The lane's open core `(52)` /
`T_Hardy <= 4` gains the same doubling: `T_Hardy < 8` suffices.  Do not
re-attack budget-4 transport; the live object is the two-quantum energy law.

## C47 closed threshold eight and native commutator lift `[LEAN-FORMALIZED ENDPOINT; INCIDENCE OPEN]`

The strict inequality in the paired Cauchy energy is against the geometric
strip endpoint, not against the chosen corner budget.  Hence the preceding
threshold statement closes at eight:

```text
0 <= c <= 8
-> (ContinuedXiWardCornerLiftLaw c <-> RH).             (C47.1)
```

In particular no artificial strict loss is required from a doubled source:

```text
ContinuedXiWardCornerLiftLaw 8 <-> RH.                  (C47.2)
```

This is proved in
`formal/GaloisForLFunctions/RHTower/XiWardThresholdEightClosedCompleteness.lean`
and wired into the `RHTower` umbrella.

The source already has one exact, non-scalar eight-unit object: the
self-adjoint Möbius Fisher cutoff commutator.  Its unconditional critical
profile obeys

```text
0 <= E_W(u) <= 8(1-exp(-u)),
E_W(u)/(1-exp(-u)) -> 8.                                (C47.3)
```

Therefore the next conjecture is not another scalar four-unit estimate.

**C47-NCL (native commutator lift).** Before one-sided scalarization, Gamma
completion and strict-right Hardy projection send the two adjoint boundary
orientations of the source Fisher commutator to one joint finite-packet
column equal to `r_P`, and the associated Schur defect is exactly

```text
8 G_P-r_P r_P^*.                                       (C47.4)
```

If `(C47.4)` is obtained as a positive source Gram, `(C47.2)` proves RH and
then the original four-unit matrix `W_P` is positive because `r_P=0`.

Homogeneous tensor/power amplification is not a route to `(C47.4)`.
`XiHomogeneousChargeGateSaturation.lean` proves that every common positive
power, and more generally every strictly increasing reparameterization, has
exactly the same height content.  The only live operation is the actual
two-sided commutator incidence.  Its falsifier is exact: a construction that
first factors through the one-sided scalar graph is already excluded by
C42--C44; a construction that merely appends an orthogonal four-unit copy
still has zero Ward column.
