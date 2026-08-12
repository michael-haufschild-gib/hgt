# Xi reflection self-intersection charge

- **ID:** `xi-reflection-self-intersection-charge`
- **Stage:** 1-in-progress
- **Type:** FRANKENSTEIN BRIDGE / PRODUCER SPECIFICATION
- **Status:** `[PAPER-PROVED CORE] [LEAN IN PROGRESS] [NOT RH]`
- **Target:**
  `formal/GaloisForLFunctions/RHTower/XiReflectionSelfIntersectionCharge.lean`

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

`[PAPER-PROVED] [LEAN PLANNED]` For divisor-support point `rho`, let

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

### C4 — source law kills reflection-copy incidence

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
supply C4.

## No-go closure for C1

- **Exact killing mechanism:** full horizontal fibre contains all zeros at one ordinate, whereas
  source involution selects only `rho -> 1-conj(rho)`.
- **Strongest positive survivor:** canonical reflection charge `R(T)`, exact decomposition
  `O(T)=R(T)+A(T)`, and literal `XiZeroCopy` incidence interpretation.
- **New insight:** quadratic charge is self-intersection of multiplicity fibres, not signed
  Fredholm index.  Linear unsigned escape energy records copies; canonical incidence records their
  Cartesian square.
- **Status:** C2 and C3 dependency-closed on paper.  C2/C3 Lean formalization in progress.  C4 is
  exact source-level open core.

## Gates

- [x] 0 -> 1: well-posed, source-pure endpoint, failed equality classified
- [x] C2 dependency-closed paper proof
- [x] C3 dependency-closed paper proof
- [ ] C2/C3 unconditional Lean theorem and audits
- [ ] C4 coefficient-faithful source incidence annihilation
- [ ] unconditional formal RH

## Log

- 2026-08-12 — C1 falsified; C2/C3 extracted as positive survivor; Lean implementation started.
