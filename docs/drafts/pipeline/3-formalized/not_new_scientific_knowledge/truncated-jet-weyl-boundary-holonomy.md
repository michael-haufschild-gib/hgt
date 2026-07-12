# Truncated-jet Weyl boundary holonomy

- **ID:** `truncated-jet-weyl-boundary-holonomy`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`, `[BRIDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/TruncatedJetWeylBoundary.lean`
- **Route:** `../../1-in-progress/dyadic-weld-weyl-multiplicity-route.md`

## Theorem

On the truncated coefficient space with basis

```text
1, X, ..., X^n,
```

let the clock be

```text
C_zeta = diag(1, zeta, ..., zeta^n),
```

and let `S_h` be the forward coefficient shift completed by the top-to-bottom wrap

```text
S_h(X^j)=X^(j+1)       for j<n,
S_h(X^n)=h.
```

The Weyl defect at the wrap entry is exactly

```text
(C_zeta S_h - zeta S_h C_zeta)_(0,n)
  = h (1-zeta^(n+1)).                                  (1)
```

If `h` is nonzero, then the complete matrix Weyl law holds exactly when

```text
C_zeta S_h = zeta S_h C_zeta
  iff zeta^(n+1)=1.                                    (2)
```

For the primitive dyadic phase `zeta=Bottcher.dyadicRoot(k)`, equation `(2)` implies

```text
2^k divides n+1.                                       (3)
```

## Proof

The interior arrow from `X^j` to `X^(j+1)` has clock weights differing by the factor `zeta`, so
every interior matrix entry satisfies the Weyl law identically.  The wrap arrow has source weight
`zeta^n` and target weight `1`; its defect is `(1)`.  If `h` is nonzero, cancellation gives
`zeta^(n+1)=1`.  Conversely that scalar identity closes the wrap and therefore every entry.  The
primitive-root characterization gives `(3)`.

## Positive statement from the no-go

An arbitrary cyclic or unitary completion of the one-sided compressed translation cannot be used
as harmless infrastructure.  Its sole top-jet holonomy equation is already the desired divisibility
law.  In particular, completing the old compressed-prime-shift parallelogram by a hand-chosen wrap
does not advance the RH route.

The surviving source target is sharper:

> construct a nonzero boundary holonomy from the Euler--Gamma--SEM incidence itself, then prove
> that the same source incidence annihilates `h(1-zeta^d)` without assuming `zeta^d=1`.

Thus the open core is not invertibility alone.  It is source annihilation of the canonical top-jet
Weyl anomaly.

## Formal surface

- `truncatedJetClock`
- `boundaryCompletedJetShift`
- `boundaryCompletedJetWeylDefect_zero_last`
- `boundaryCompletedJetWeyl_of_phase_pow_card`
- `phase_pow_card_of_boundaryCompletedJetWeyl`
- `boundaryCompletedJetWeyl_iff_phase_pow_card`
- `pow_dvd_card_of_dyadic_boundaryCompletedJetWeyl`
- `not_boundaryCompletedJetWeyl_of_phase_pow_card_ne_one`

## Verification

`lake env lean GaloisForLFunctions/RHTower/TruncatedJetWeylBoundary.lean` passes on the repository
toolchain.

## Novelty and significance gate

This is standard finite clock--shift algebra.  No claim of new scientific knowledge is made.  Its
role is to exclude a circular boundary-completion shortcut and to isolate the exact scalar anomaly
that a genuine source theorem must kill.

## Gates

- [x] 0 -> 1: finite jet clock, shift, and boundary wrap stated
- [x] 1 -> 2: exact defect and iff theorem proved
- [x] 2 -> 3: formalized and exact module check passes
- [ ] 3 -> 4: not promoted; source annihilation theorem remains open
