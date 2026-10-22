# Suzuki positive-arch Mangoldt quadrature deficit

- **ID:** `suzuki-positive-arch-mangoldt-quadrature-deficit`
- **Stage:** 5 — failed/retired as an independent scalar route
- **Type:** TERMINAL SCALAR-TRANSPORT NO-GO / POSITIVE SURVIVOR CLASSIFICATION
- **Scientific status:** `[SCALAR CLASS CLOSED] [UNCONDITIONAL LEAN NO-GO]`
  `[RH ENDPOINT RETAINED] [OPERATOR SURVIVOR MERGED INTO ROUTE G]`
- **Parent:** `suzuki-rectangular-positive-arch-lag-completion.md`
- **RH used in target proof:** forbidden
- **Computation used:** no

## Terminal closure — Route B retired as an independent route

Route B's exact fixed-width lower-floor endpoint remains Lean-equivalent to RH.  What is retired is
its advertised independent acquisition mechanism.

The scalar alternatives are exhausted at their stated information boundary:

1. universal integer-log quadrature is false;
2. pointwise apex cells are impossible on a cofinal actual Mangoldt family;
3. common-displacement bicausal splicing is identically the original capacity-one deficit after
   duplicate seam mass is removed;
4. capacity, atomlessness, exact exterior-flank capacity, and arbitrarily large flank surplus do
   not imply domination, even after an arbitrary tail threshold.  The cofinal atomless
   countermodel and universal-class negation are formalized in
   `SuzukiCriticalApexVacuumCapacityNoGo.lean`.

The former label `SUZUKI-SOURCE-COMMUTATOR-GRAM` is not a remaining Route-B step: finite source
identification, logarithmic commutator carrier, and compact-support cyclic descent already exist.
What remains after them is the signed/cofinal completed Burnol--Robin--Gamma Ward floor.  That is
the operator source-realization problem tracked by Route G and
`suzuki-terminal-frontier-ledger.md`; calling it block transport would duplicate that route.

**Exact killing mechanism.** Every scalar producer proposed on this card is either false on a
cofinal source class or algebraically equivalent to the RH-bearing target deficit.  The sole
source-specific escape leaves the scalar transport category and lands in Route G.

**Strongest positive survivor.** The completed-lag/positive-prime-wall identity remains a sharp
fixed-width RH detector.  More importantly, apex-vacuum amplification is a cofinal extremal law:
bounded cumulative displacement can cause unbounded quadrature excess at the moving exponential
apex while both exterior flanks stay exactly capacity one.  Any future source proof must therefore
carry a non-scalar, source-sensitive orientation invariant before taking a trace.

**Status.** Scalar no-go and survivor have dependency-closed paper proofs and unconditional Lean
certificates.  RH is neither proved nor disproved.  Route B is closed only as an independent
positive-transport route; its operator survivor is not discarded or relabelled as solved.

All later “open core” labels below are retained as research history and superseded by this terminal
closure.

## Exact frontier

For fixed `L>0`, define

```text
C_a(h)=R_(L,a)(h),
A_a(t)=exp(t/4)C_a(t/2),
K_a(t)=A_a(t)
 +exp(-t)/[1-exp(-t)] [C_a(0)-exp(-t/4)C_a(t/2)].
```

Parent theorem proves `K_a(t)>0`, `0<=A_a(t)<=K_a(t)`, and

```text
PrimeWall(L,a)=sum_(2<=n<=exp(2a)) Lambda(n)/n A_a(2 log n).
```

Actual unsolved statement is

```text
D_L(a):=integral_0^infinity K_a(t)dt
 -2 sum_(2<=n<=exp(2a)) Lambda(n)/n A_a(2 log n)
 -(gamma+log pi)2L >= 0                              (Q)
```

on every sufficiently large logarithmic aperture.  Lean proves `(Q)` on any admissible cofinal
tail is equivalent to RH.  No Gamma sign problem remains inside `(Q)`.

## Scientific method: competing mechanisms

### Q1. Restricted-Weil Robin defect square `[PRIMARY CONJECTURE]`

Actual finite restricted-Weil resolvent and Robin boundary observation should produce an exact
source-to-observer identity

```text
D_L(a)=WardBoundaryNorm(L,a)^2 + HolonomySchurRemainder(L,a),
```

with second term positive semidefinite after marked half-gap completion.  This is preferred because
S64 identifies observer-response orientation, S65 identifies correct compact prime source, and
S66 identifies exact continuous/atomic channels.  Proof must derive both terms from existing
restricted-Weil operator, not define them from `D_L(a)`.

### Q2. Source-adapted lag-cell transport `[COMPETITOR]`

Construct positive cells `I_n` and source-derived transport densities `rho_n(t)` satisfying

```text
2 Lambda(n)/n A_a(2 log n)
 <= integral_(I_n) rho_n(t) K_a(t)dt,
sum_n rho_n(t) <= 1,
```

with leftover mass paying fixed boundary charge.  Cells and densities must arise from sharp
restricted-Weil/Robin kernel.  Arbitrary fitted cells would merely rename target inequality.

### Q3. Universal integer-log quadrature `[FALSIFIED]`

Corpus proves actual archimedean seam functional does not factor through integer-log or prime-power
samples on arbitrary continuous tests.  Therefore no universal sampling reconstruction can prove
`(Q)`.  Only special rectangular-family transport can survive.

## Exact falsifiers and gates

1. **No target-defined square.**  Any `WardBoundaryNorm := sqrt(max(D,0))` is circular.
2. **Source degree.**  Prime term is quadratic gated bare wall Gram; linear observer ray is wrong.
3. **Sharp support.**  Prime source vanishes beyond `log n=2a`; observer response need not.
4. **No universal sampling.**  Seam gap-tent no-go kills family-independent factorization.
5. **Boundary charge sign.**  Target requires `+ (gamma+log pi)2L` on atomic side; dropping or
   reversing it proves wrong inequality.
6. **No duplicate polar mass.**  `A_a` is already first summand of `K_a`; transport cannot add its
   polar square a second time.
7. **No asymptotic estimate substitution.**  Desired advance is exact positive operator/transport
   decomposition, not another scalar upper bound.

## S67 transport advance: monotone bulk discharged

The first source-derived transport now exists.  Put

```text
F_n=2 sum_(d<=n) Lambda(d)/d,   tau_n=2 log n.
```

Ramaré--Zuniga Alterman's known log-Haar capacity theorem gives `F_n<=tau_n`.  A new
endpoint-retaining divisor/factorial argument gives `tau_n-2<=F_(n-1)`.  Therefore

```text
P_n=(F_(n-1),F_n] subset (tau_n-2,tau_n],
Q_n=(F_(n-1)+2,F_n+2] subset (tau_n,tau_n+2],
length(P_n)=length(Q_n)=2 Lambda(n)/n.
```

Each family is pairwise disjoint.  Past cells pay decreasing branches; future cells pay increasing
branches.  Lean also contains a fully unconditional wider-cell version using in-tree Mertens
constant, so transport geometry does not depend on the unformalized external capacity theorem.

For Suzuki channel, transported atom is definitionally the exact prime-wall cell

```text
2 Lambda(n)/sqrt(n) R_(L,a)(log n).
```

Hence every moving-tent atom outside two lag units of its turning point is discharged by a
capacity-one Lebesgue cell once elementary branch monotonicity is instantiated.  Remaining
arithmetic debt is no longer whole window: it is splice layer where future and past cell families
would overlap.

### S68 hostile verdict: pointwise seam cells are impossible

`SUZUKI-TURNING-SEAM-BICAUSAL-SPLICE` is **falsified in its per-atom pointwise form**.  Put

```text
L=log 2,  a_n=(1/2)log(2n),  tau_n=2log n.
```

Lean proves for every `n>=4` that `tau_n` is the unique positive-lag maximizer of
`A_(L,a_n)`.  Hence every set on which `A(tau_n)<=A(t)` holds pointwise is Lebesgue null.  At every
prime power its required mass `2Lambda(n)/n` is positive.  Powers of two give a cofinal family, so
no tail restriction repairs the route.

The obstruction is stronger than past/future overlap: even arbitrary non-interval adaptive cells
cannot put positive mass inside a singleton superlevel.  Bulk transport remains valid away from
turning layer.

### New exact open core

`SUZUKI-APEX-BLOCK-TRANSPORT`:

Construct capacity-one source-canonical **blocks**, not individual cells, grouping each apex atom
with flank atoms before comparison.  Prove aggregate sampled `A_a` mass of every block is at most
aggregate completed-kernel mass on its target block, with disjoint target blocks and unused mass
paying `(gamma+log pi)2L`.  Required new object is nonnegative block surplus.  Defining that surplus
from target deficit is circular.

## Next proof target

Attack `SUZUKI-APEX-BLOCK-TRANSPORT` first.  Derive exact two-sided block surplus in cumulative-mass
coordinates and test whether restricted-Weil Robin current equals this surplus.  Do not attempt
another pointwise cell assignment and do not return to global prime estimates.

## Gates

- [x] exact RH-equivalent deficit isolated
- [x] both variable sides represented as related positive lag channels
- [x] universal sampling route killed by corpus theorem
- [x] exact bi-causal Mangoldt transport cells
- [x] monotone branch discharge and exact Suzuki prime-cell weld
- [x] RH-bearing debt localized to bounded moving turning seam
- [x] pointwise capacity-one future/past seam splice falsified cofinally
- [x] exact Mangoldt/Suzuki apex-lock rigidity formalized
- [x] unconditional source-canonical prime block with sharp contraction and `sqrt(n)` surplus
- [x] capacity-one apex/flank scalar block transport class closed negatively
- [x] source commutator/Gram label audited as already closed infrastructure
- [x] surviving signed/cofinal operator floor transferred to Route G without duplication
- [x] exact positive survivor and no-go formalized unconditionally
- [ ] `(Q)` / RH — retained only as terminal endpoint, not claimed

## Hypothesis-free paper gate (2026-07-22)

No RH implication, literature capacity bound, abstract positivity premise, or paper-only operator
identity may be presented as a proved application. Candidate paper theorem must:

1. use only concrete Suzuki/Mangoldt objects whose prerequisites are already unconditional;
2. prove its block surplus rather than assume it;
3. receive a dependency-closed Lean proof with no `sorry`, `axiom`, `opaque`, or `unsafe` escape;
4. pass an axiom audit showing only Lean/mathlib foundations;
5. remain in Stage 1 if any source-to-operator connector is missing.

The rejected boundary-phase manuscript does not meet this gate because its Suzuki specialization
assumes RH and its unbounded-operator theorem is not Lean-complete.

### Competing apex-block mechanisms

- **B1: completed-kernel decreasing-rearrangement surplus.** Derive a sharp block-majorization
  identity comparing source flank deficit from the unique apex with continuum target deficit.
  This is viable only if the source-side flank term is proved nonnegative for actual Mangoldt
  blocks; naming the difference is circular.
- **B2: cumulative-mass bicausal splice.** Merge the future and past Haar cells at their unique
  overlap and prove that unused completed-kernel mass dominates the merged block. All capacity and
  multiplicity accounting must be exact.
- **B3: restricted-Weil Robin current.** Derive the merged-block surplus as an actual boundary
  norm/Schur complement from Suzuki's kernel. This remains preferred if B1/B2 reduce to the target
  deficit.

Immediate hostile test: integrate by parts against
`delta(t)=t-2*sum_(2 log n<=t) Lambda(n)/n`. If proposed surplus is merely the signed pairing of
`delta` with the derivative of the moving apex profile, then it is an equivalent reformulation of
the RH-bearing deficit, not a producer theorem.

## S69 source-scaling advance: sharp width-five block surplus

The width-`log 2` single-flank theorem is too small for the seam: its certified absolute surplus is
on the `n^(-1/2)` scale.  This is now repaired by changing object, not optimizing that estimate.

For

```text
L5=log 5,
a5(n)=log(5n)/2,
P_n={p prime : 2n<p<=5n},
q5=sqrt(2)(1-log(2)/log(5)),
```

Lean proves the universal subcritical tail law, including exact optimality of its tail ceiling,
and the source-specific statements

```text
0<q5<1,
sum_(p in P_n) 2log(p)/p >= 1/10,
A_n(2log p) <= q5 A_n(2log n),
S5(n) >= ((1-q5)/10)sqrt(n)log(5)>0
```

for every natural `n>=exp(20)`.  It further proves `S5` unbounded.  Proof is unconditional and
symbolic: exact aligned Suzuki sampling, tilted-tent derivative law, formalized Chebyshev theta
bounds, positive prime weights.  No zero statement, target deficit, prime-gap hypothesis, or
numerical certificate occurs.

Frontier effect: `SUZUKI-APEX-BLOCK-TRANSPORT` is no longer blocked by source positivity or source
scale.  The exact remaining theorem is target-capacity domination of this explicit prime block,
with disjoint continuum blocks and Gamma reserve.  Because `q5` is the least uniform continuous
ceiling on `[log 2,log 5]`, that coefficient cannot be improved without changing block geometry or
using additional target structure.  Next work must attack that capacity comparison, not return to
single-atom estimates.

## S70--S72 hostile closure: scalar apex-block transport is not a producer

Two exact no-go theorems overturn the final paragraph above.

First, common-displacement future/past targets overlap by exactly their displacement seam, and

```text
mixed target-source-seam = capacity-one target-source.
```

Thus B2 is identically the original quadrature deficit after duplicate capacity is removed.

Second, the atomless apex-vacuum theorem constructs a source measure satisfying the same sharp
width-two band `t-2<=F(t)<=t`, agreeing with Lebesgue measure on the full decreasing flank, and
having arbitrarily large apex-relative flank surplus, while violating the completed-lag inequality.
Its sample-channel excess is at least `H_a/128`; reflected-polar/Gamma reserve is uniformly bounded
by `16+rectangularGammaPolarUniformBound(2)`.  Therefore B1 cannot use capacity, atom-size control,
atomlessness, or unbounded flank deficit as sufficient data.  S69 remains a correct source theorem
but its surplus is consumed capacity until an independent source identity proves otherwise.

Verdict:

- B1 capacity/rearrangement producer: **FALSE for the exact information class above**;
- B2 common-shift splice: **CIRCULAR/IDENTICAL to `(Q)`**;
- arbitrary target-defined block certificate: not a producer; its existence is `(Q)`;
- B3 actual restricted-Weil/Robin source commutator: sole surviving route on this card.

The new exact open core is `SUZUKI-SOURCE-COMMUTATOR-GRAM`: derive from actual Mangoldt and Gamma
source, before knowing target sign, a positive Gram/Schur identity whose scalar trace is the
capacity-corrected displacement commutator.  Any construction factoring only through the S67 band
or S69 apex-relative scalar surplus is now forbidden by a formal countermodel.

Formal artifacts:

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiBicausalNoFreeSplice.lean`;
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalApexVacuumCapacityNoGo.lean`;
- `docs/drafts/pipeline/5-failed/suzuki-continuum-two-flank-surplus-pays-bicausal-seam.md`.

This closes a scalar transport sublane, not Suzuki's complete operator program, and does not prove
RH.  Next legitimate attack is B3 only; no further paper may promote block surplus without an
actual-source operator identity and completed-lag sign.
