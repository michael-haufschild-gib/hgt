# Observer-channel recurrence–production dichotomy law

- **ID:** `observer-channel-recurrence-production-dichotomy-law`
- **Stage:** 2 -- fully proven on paper
- **Type:** exact universal history law / Brown-frontier reduction
- **Parent:** `selector-partition-observer-channel-recurrence-law.md`
- **Status:** `[PAPER-PROVED] [UNIVERSAL] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Lean promotion:**
  `../3-formalized/observer-channel-recurrence-production-dichotomy-law.md`
- **Date:** 2026-08-14

## Public sentence

A quantum history cannot keep producing strong recognizable events from a bounded observer
alphabet without paying same-channel recurrence.

## Setup

Use the selector-partition notation of the parent law. Let

```text
W_c = sum_(j:sigma(j)=c) w_j,          channel load,
W   = sum_j w_j = sum_c W_c,           total history mass,
L   = sum_c W_c^2,                     load energy,
R   = sum_c ||sum_(j:sigma(j)=c) w_j r_j||^2,
M   = #{c : W_c != 0},                 occupied-channel count.
```

Assume `w_j>=0`, `eta>=0`,

```text
eta <= <r_j,q_(sigma j)>               for every j,
||q_c||^2 <= B                         for every c.
```

## Theorem A — occupancy geometry

For arbitrary real weights,

```text
boxed: W^2 <= M L.                                          (RCP1)
```

### Proof

Zero-load channels contribute nothing. Apply finite Cauchy--Schwarz to the `M` nonzero loads:

```text
(sum_(c:W_c!=0) W_c)^2 <=
  M sum_(c:W_c!=0) W_c^2 = M L.
```

The left sum is `W` because channel loads partition sample weights exactly.

## Theorem B — recurrence-or-channel-production law

The selector observer--spectral law gives `eta^2 L<=B R`. Combining it with `(RCP1)` gives

```text
boxed: eta^2 W^2 <= B M R.                                  (RCP2)
```

Thus strong total recognized history has two—and only two in this positive-form accounting—ways to
pay: many occupied channels or large recurrence energy inside reused channels.

## Theorem C — capacity form and strict contrapositive

If an observer/circuit model can occupy at most `K` channels, then

```text
eta^2 W^2 <= B K R.                                         (RCP3)
```

Equivalently, if

```text
B K R < eta^2 W^2,
```

then

```text
boxed: M > K.                                               (RCP4)
```

This is the exact deterministic interface needed by a quenched static-H argument: prove `(RCP4)`'s
strict recurrence-budget inequality uniformly over all selectors of shallow-circuit capacity.

## Theorem D — intrinsic resolution channels

Arbitrary label duplication can inflate `M`, so physical use must impose an intrinsic channel
quotient. If preparation memories satisfy

```text
delta >= 0,
c != d  ->  delta < ||q_c-q_d||,
```

then `c -> q_c` is injective. Under this premise `(RCP4)` counts distinct preparation memories,
not duplicate names. A maximal resolution-separated target packing from the resolution-quotient
law supplies exactly such a canonical channel family.

## Theorem E — static two-memory capstone

For nested completed sectors `Pi<=P`, one static unitary flow `U(t)`, seed `x`, target family
`y_c`, and selector `sigma`, suppose every target has `Pi y_c=Pi x` and every selected collision
exceeds its target-specific completed baseline by `eta`. Put

```text
z   = x-Px,
q_c = y_c-Pi x.
```

Then

```text
boxed:
eta^2 W^2 <= B M
  sum_(i,j:sigma(i)=sigma(j)) w_i w_j
    <z,U(t_j-t_i)z>.                                      (RCP5)
```

Here `||q_c||^2<=B`. This is an exact stationary-kernel theorem for one time-independent flow, not
an ensemble or mixing assumption.

## Sharpness and extremes

- Identity selector with unit weights has `M=|C|`, `L=|C|`, `W=|C|`; `(RCP1)` is equality.
- Fresh self-target channels saturate the selector observer--spectral law term by term.
- Constant selector gives `M=1` whenever its total load is nonzero and recovers the complete scalar
  recurrence energy.
- Hence neither `M` nor `R` can be removed from `(RCP2)` by a stronger universal Hilbert inequality.

## Hostile audit

- **Duplicate labels:** invalidate physical channel counting. The separated-channel theorem is
  mandatory for applications.
- **Signed weights:** `(RCP1)` holds for signed weights, but collision-to-alignment and `(RCP2)` use
  nonnegative weights.
- **Zero mass:** theorem is valid but uninformative when `W=0` or `eta=0`.
- **Circularity:** `(RCP2)` is a dichotomy, not a proof that `M` is large. Static-H research must
  prove the strict budget inequality uniformly over bounded-capacity selectors.
- **Complexity:** occupied resolution channels are not automatically circuit complexity. A separate
  theorem must bound the channel image of all depth-`s` circuits.
- **Probability and rates:** no quenched ensemble event, growth slope, plateau measure or recurrence
  time is proved.
- **Physics:** no black-hole interior, holographic or gravitational consequence follows yet.
- **Novelty:** occupancy Cauchy, direct sums and the logical contrapositive are classical. External
  priority for this specific recurrence/complexity composition is unverified.

## Exact new frontier

For a canonical separated resolution quotient and one ordinary time-independent local-Hamiltonian
ensemble, prove on one high-probability event that every shallow selector with occupied-channel
capacity at most `K(s)` satisfies

```text
B K(s) R_sigma < eta^2 W^2
```

through the claimed onset window. This is selector-resolved cross-incidence anti-concentration; it
cannot be replaced by scalar source dephasing. A full Brown law additionally needs plateau measure,
first low-complexity recurrence scale and permanent non-Haar locality on the same event.

## Promotion gates

- [x] dependency-closed proof of `(RCP1)--(RCP5)`
- [x] duplicate-label attack closed by separated-channel theorem
- [x] sharp fresh-channel endpoint identified
- [x] hostile audit and exact remaining obligation
- [x] exact Lean theorem
- [x] umbrella wiring and axiom audit
