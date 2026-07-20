# Operational effective-support separation for projective recurrence

- **ID:** `projective-operational-support-separation`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Parent:** `projective-weighted-coherence-water-filling-law`
- **Statement:** At the trace-distance support scale used by the strongest published
  effective-support recurrence bound, two binary spectral packets can have identical effective
  support while their exact projective water entropies, and hence their finite worst-spectrum
  recurrence bands, are strictly separated.

## Goal

Repair the paper's earlier comparison at the amplitude-defect scale.  The published recurrence
literature measures pure-state neighborhoods in trace distance.  The comparison must therefore use
the same tail scale, not a bespoke `eta`-support convention.

## Definitions

Fix an amplitude defect `0 < eta < 2/5` and set

```text
epsilon_eta = sqrt(2 eta - eta^2),
delta_eta   = epsilon_eta / 2.                              (1)
```

The fidelity threshold `(1-eta)^2` is exactly the trace-distance threshold `epsilon_eta`, because
for pure states

```text
D_tr^2 = 1-F <= 1-(1-eta)^2 = 2 eta-eta^2.                 (2)
```

For a probability vector `w`, write

```text
s_delta(w)=min{|C| : sum_(j in C) w_j >= 1-delta}.         (3)
```

Kotowski--Oszmaniec's main truncation bound uses `delta=epsilon^2/4`; their sharper covering
remark improves the exponent to the support at `delta=epsilon/2`.  We use the latter, stronger
scale `delta_eta`.

## Theorem `[PAPER-PROVED]`

Let `q>1` and assume

```text
q delta_eta < 1/2.                                         (4)
```

Put

```text
w_eta=(1-q delta_eta, q delta_eta),
u=(1/2,1/2).                                               (5)
```

Then

```text
s_(delta_eta)(w_eta)=s_(delta_eta)(u)=2,                   (6)
```

while at the original fidelity defect `eta` their exact pivot water entropies are

```text
H_proj(w_eta,eta)
  =(1/2) log(q delta_eta/eta)
  < (1/2) log(1/(2 eta))
  =H_proj(u,eta).                                          (7)
```

Moreover the least worst-spectrum discrete Floquet deadline for `w_eta` satisfies

```text
(1/2)log(q delta_eta/eta)-pi/4-log 4
  < log T_(w_eta)(eta)
  <=(1/2)log(q delta_eta/eta)+log(2 pi sqrt 2).             (8)
```

## Proof

The radicand in `(1)` is positive.  Squaring `delta_eta` gives

```text
delta_eta^2=(2 eta-eta^2)/4.                               (9)
```

Because `eta<2/5`,

```text
2 eta-eta^2-4 eta^2=eta(2-5 eta)>0,                       (10)
```

so `(9)` and positivity imply `eta<delta_eta`.  Also
`2 eta-eta^2<1`, hence `delta_eta<1/2`.

Set `c=q delta_eta`.  From `q>1` and `eta<delta_eta` one gets
`eta<delta_eta<c`.  Assumption `(4)` gives `c<1/2`.  For the packet `(1-c,c)`, the heavy singleton
has mass `1-c<1-delta_eta`, while the light singleton has mass
`c<1-delta_eta` because `c+delta_eta<1`.  Thus neither singleton reaches the target mass and
`s_(delta_eta)(w_eta)=2`.  The same argument with `c=1/2` and `delta_eta<1/2` gives
`s_(delta_eta)(u)=2`.

For any binary packet `(1-c,c)` with `0<eta<c<=1/2`, the one-coordinate water program gives

```text
H_proj((1-c,c),eta)=(1/2)log(c/eta).                       (11)
```

Applying `(11)` first to `c=q delta_eta` and then to `c=1/2` proves the two equalities in `(7)`.
Since `q delta_eta<1/2` and `eta>0`, strict monotonicity of the logarithm proves the middle strict
inequality.  Finally `(8)` is the dimension-two specialization of the projective water-entropy
sandwich.

Every step is finite and unconditional.  This is a separation of triangular families at a common
operational scale.  It is not presented as a contradiction to the fixed-state high-resolution
support exponent.

## Anti-theatre audit

The support conversion `(1)`--`(3)` is standard pure-state geometry, and the binary calculation is
elementary.  Its role is not a second novelty headline.  It closes a validity gap in the significance
comparison for the parent theorem by aligning the comparison with the strongest support scale used
in the current recurrence literature.

## Gates

- [x] 0 to 1: operational scale identified and complete proof written
- [x] exact relation to the parent minimax theorem stated
- [x] fixed-state versus triangular-family scope made explicit
- [ ] 1 to 2: hostile proof audit
- [ ] 2 to 3: unconditional Lean theorem and targeted audit
- [ ] 3 to 4: replace the paper's obsolete support comparison

## Log

- 2026-07-20 — created after referee-scale audit of the publication draft.
