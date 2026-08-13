# Xi reflection self-intersection charge

- **ID:** `xi-reflection-self-intersection-charge`
- **Stage:** 1-in-progress
- **Type:** FRANKENSTEIN BRIDGE / PRODUCER SPECIFICATION
- **Status:** `[PAPER-PROVED CORE] [LEAN-PROVED] [DIRECT CHECK PASS] [LEAF BUILDS PASS] [AXIOM-AUDITED] [GLOBAL LINT BLOCKED BY UNRELATED UNWIRED MODULES] [NOT RH]`
- **Targets:**
  `formal/GaloisForLFunctions/RHTower/XiReflectionSelfIntersectionCharge.lean`;
  `formal/GaloisForLFunctions/RHTower/XiReflectionIncidenceSchattenSpectrum.lean`

## Goal

Replace full horizontal collision charge by canonical part forced by critical-line reflection.
Identify each local square with literal cardinality of a multiplicity-copy incidence relation.  This
removes accidental horizontal collisions before asking source side for a strict quantized bound.

## Conjecture loop

### C1 — full horizontal collision charge is source reflection self-intersection

`[FALSIFIED]` Full charge

```text
O(T) = sum_rho m_rho (H_rho - m_rho)
```

counts every ordered pair of distinct zeros at same height.  If several reflection orbits, or an
additional critical-line zero, occur at one ordinate, `O(T)` contains cross-orbit incidences not
selected by involution `rho -> 1-conj(rho)`.  Those accidental collisions have no canonical
two-channel source interpretation.  Consequently equality between `O(T)` and source-reflection
self-intersection is false without an extra horizontal uniqueness theorem.

### C2 — split off canonical reflection self-intersection

`[PAPER-PROVED]` Put

```text
Q_right(T) = sum_{rho in S_T, 1/2 < Re rho} m_rho^2,
R(T)       = 2 * Q_right(T),
A(T)       = O(T) - R(T).
```

Critical-line reflection preserves window and multiplicity.  Applying finite-window reflection
identity with weight `m_rho^2` gives

```text
sum_{rho in S_T, Re rho != 1/2} m_rho^2 = 2 * Q_right(T) = R(T).
```

For each off-line `rho`, reflected partner is distinct, has order `m_rho`, and belongs to same
horizontal fibre.  Hence `2*m_rho <= H_rho`, so

```text
m_rho^2 <= m_rho * (H_rho - m_rho).
```

After summation, `R(T) <= O(T)`.  Natural-number subtraction therefore gives exact nonnegative
decomposition

```text
O(T) = R(T) + A(T).
```

Any right-half zero has positive integral order, so its square is at least one and `R(T) >= 2`.
Conversely RH makes right-half window empty.  Therefore

```text
RH <-> forall T, R(T) = 0
   <-> forall T, R(T) < 2.
```

Natural, arbitrary cofinal, and eventual strict-two variants follow exactly as for `O(T)`, but
`R(T)` is strictly cleaner: source must kill only forced line-reflection incidences, not unrelated
same-height collisions.

### C3 — local square is literal XiZeroCopy reflection incidence

`[PAPER-PROVED] [LEAN-PROVED]` For divisor-support point `rho`, let

```text
I_rho = Fiber(rho) x Fiber(1-conj(rho)).
```

`Fiber(rho)` has exactly `m_rho` multiplicity copies.  Reflection preserves divisor order, so
reflected fibre also has `m_rho` copies.  Thus

```text
card(I_rho) = m_rho^2.
```

The factor two in `R(T)` records both orientations of forced horizontal incidence.  This is
coefficient-faithful: no synthetic copies, tensor powers, or zero replication are introduced.

### C4 — Haar-translate amplification makes incidence rank beat source moments

`[FALSIFIED]` New quantile Haar carrier is sigma-finite and invariant under prime translation,
but it does not evade spectral-scale wall.  Unitarily normalized independent translates have
linear norm and Frobenius cost.  Half-density translates whose amplitudes decay give arbitrarily
large raw inertia at sublinear cost, but this is exactly already formalized moment-neutral packet:
rank--trace prices every nonzero positive-index unit, regardless of scale.  Finite-invariant-measure
no-go does not apply to actual infinite Haar carrier.  Haar completion changes admissibility, not
sign of rank--trace amplification.

### C5 — quadratic failure of linear source cancellation

`[PAPER-PROVED] [LEAN-PROVED]` Fix one ordinary prime `p` and write `a_rho(p)` for retained
prime-labelled horizontal carrier coefficient.  On every literal incidence `(q,r) in I_rho`,
line reflection gives

```text
a_q(p) + a_r(p) = 0,
-a_q(p) a_r(p) = a_rho(p)^2.
```

Thus complete linear incidence trace vanishes unconditionally, including off line, while
quadratic incidence energy is

```text
E_p(rho) = m_rho^2 * a_rho(p)^2 >= 0.
```

It is reflection invariant and vanishes exactly on critical line.  Away from line,
`a_rho(p) != 0`, and exact coefficient-faithful reconstruction holds:

```text
E_p(rho) / a_rho(p)^2 = card(I_rho) = m_rho^2.
```

Consequently, at any one fixed ordinary prime,

```text
RH <-> forall rho in Xi divisor support, E_p(rho)=0.
```

This proves higher principle shadowed by prior failures: all linear reflection observers erase
off-line orientation automatically; canonical horizontal charge is their nonzero quadratic
self-intersection.  Recovering integral charge from prime energy necessarily divides by same
coefficient that vanishes at desired radical, exposing singular-normalization wall exactly.

### C6 — source law kills reflection-copy incidence

`[OPEN CORE] [PRODUCER]` Existing source-horizontal carrier is odd under copy-level line
reflection.  Oddness exchanges the two orientations but does not make either orientation vanish.
Needed theorem must act on multiplicity-copy incidence, not unsigned multiplicity mass:

```text
for every right-half rho and every (q,r) in I_rho,
source pairing/transport law forces the oriented q->r incidence coefficient to vanish.
```

Because coefficient faithfulness fixes each divisor-copy coefficient at one, vanishing of every
incidence coefficient makes `I_rho` empty, hence `R(T)=0`.  Exact missing mechanism is therefore a
non-equivariant source pairing that both (i) identifies the two line-reflected transports on same
incidence carrier and (ii) retains existing reflection oddness.  Equality plus oddness gives zero;
cardinality then gives RH through C2.

This is stronger and more local than estimating `O(T)`: one forbidden right-half incidence is
enough.  A normalized density estimate, signed index, or ordinary tensor amplification does not
supply C6.

### C7 — literal incidence has an exact variable Schatten spectrum

`[PAPER-PROVED] [LEAN-PROVED]` Retain every one of the `m_rho^2` literal incidence copies and put

```text
S_q(rho,p) = card(I_rho) * |a_rho(p)|^q.
```

Then `S_2(rho,p)=E_p(rho)` prime by prime, and line reflection preserves `S_q` without erasing
either incidence orientation.  Because `card(I_rho)=m_rho^2>0` is finite and independent of `p`,
the exact cofinal Gamma wall gives

```text
sum_p S_q(rho,p) < infinity
  iff t_rho=0 or 1 < q(1-|t_rho|).
```

Thus membership for every `q>1` is equivalent to `t_rho=0`.  Globally, all-order admission of the
literal reflection-incidence carrier is equivalent to RH.  This is a coefficient-faithful splice
between canonical horizontal charge, source Bockstein, and Schatten routes; it is a reader, not
an admission proof.

### C8 — endpoint nuclearity is the fixed-ideal transport equality

`[PAPER-PROVED] [LEAN-PROVED]` At the endpoint `q=1`, the open fixed-order window disappears:

```text
sum_p S_1(rho,p) < infinity  iff  t_rho=0.
```

Lean proves this same proposition equivalent to each of the following source statements:

```text
primeGammaCofinalBockstein(t_rho)=0;
both Gamma orientations normalize the same fixed first-trace ideal;
ccmRationalAdelicPrimeFixedXiGammaBockstein(p,rho)=0, for any retained prime p.
```

The last class is the difference of the two actual fixed-Xi transports of the same period-one
rational-adelic source class.  Hence endpoint nuclearity is not another parallel receiver: it is
exactly the coefficient-faithful, non-equivariant transport identification requested in C6.
The sharpened producer is one loss-zero source theorem placing this raw incidence carrier in the
fixed `S_1` ideal simultaneously in both orientations.

### C9 — generic source nuclearity or quantum amplification supplies endpoint nuclearity

`[FALSIFIED; PIVOT]` Nuclearity of the rapid prime-log-height Köthe source permits a shift to a
stronger source seminorm.  The positive-chamber Stokes operators are continuous with a proved
two-height-step loss even at nonneutral grade, while fixed first-trace normalization fails in one
orientation there.  Frechet nuclearity therefore cannot discharge C8; the missing word is
*loss-zero on one fixed ideal*.

Quantum amplitude amplification also does not manufacture that fixed source law.  Its start-state
reflection depends on the prepared aperture state.  Using separate forward/reflected preparation
unitaries breaks the common-source absolute-continuity premise; controlling them by an orientation
register makes the two branches orthogonal before measurement.  A common unitary preserves their
overlap and cannot replenish one orientation while evacuating the other.  Positive survivor:
coherent amplification could only help after constructing the same missing common, loss-zero
source reflection; it cannot construct that reflection from the evacuated conditional laws.

## No-go closure for C1/C4

- **Exact killing mechanism:** full horizontal fibre contains all zeros at one ordinate, whereas
  source involution selects only `rho -> 1-conj(rho)`.
- **Strongest positive survivor:** canonical reflection charge `R(T)`, exact decomposition
  `O(T)=R(T)+A(T)`, literal `XiZeroCopy` incidence interpretation, prime-labelled quadratic
  energy `E_p(rho)`, and endpoint nuclear mass `S_1` identified with the actual fixed-Xi source
  transport defect.
- **New insight:** quadratic charge is self-intersection of multiplicity fibres, not signed
  Fredholm index.  Linear unsigned escape energy records copies; canonical incidence records their
  Cartesian square.
- **Status:** C2, C3, C5, C7, and C8 dependency-closed and Lean-proved.  C6/C8 loss-zero source
  admission is exact open core.

## Gates

- [x] 0 -> 1: well-posed, source-pure endpoint, failed equality classified
- [x] C2 dependency-closed paper proof
- [x] C3 dependency-closed paper proof
- [x] C2/C3/C5 unconditional direct Lean elaboration
- [x] exact leaf build and axiom audit for canonical charge leaf
- [x] exact leaf build and axiom audit for incidence Schatten leaf
- [x] local forbidden-token and diff checks
- [ ] repository lint (fails only on unrelated concurrent unwired modules; neither target named)
- [ ] C6/C8 coefficient-faithful loss-zero source incidence admission
- [ ] unconditional formal RH

## Log

- 2026-08-12 — C1 falsified; C2/C3 extracted as positive survivor; Lean implementation started.
- 2026-08-13 — Haar amplifier C4 falsified; quadratic source-incidence C5 extracted and Lean-proved.
- 2026-08-13 — C7/C8 proved: literal incidence Schatten spectrum, endpoint nuclear criterion, fixed
  ideal normalization, cofinal quotient, and actual rational-adelic transport defect are one law.
- 2026-08-13 — both exact leaf builds and standard-axiom audits pass. Repository lint reaches only
  pre-existing/concurrent umbrella-wiring failures outside these targets.
