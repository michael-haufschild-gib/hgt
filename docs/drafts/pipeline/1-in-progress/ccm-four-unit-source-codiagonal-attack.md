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
