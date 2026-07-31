# Summable pure-point escape–return law

- **Status:** formalized
- **Lean module:** `GaloisForLFunctions.RHTower.SummablePurePointEscapeReturnLaw`
- **Scientific role:** countably infinite extension

## Result

For every nonnegative summable phase packet
\[
  a_m\ge0,\qquad \sum_{m=0}^{\infty}a_m<\infty,
\]
every finite head length \(M\), and every resolution \(Q\), define
\[
  B_{M,Q}=
  \left(\frac{2\pi}{Q+1}\right)^2
    \sum_{m<M}a_m
  +4\sum_{m\ge M}a_m.
\]
For the continuous-time phase energy
\[
  D(t)=\sum_{m=0}^{\infty}
    a_m|e^{it\omega_m}-1|^2,
\]
either \(D(t)\le B_{M,Q}\) for every \(t\ge0\), or some exit is followed
strictly later by a return with \(D(t_{\rm ret})\le B_{M,Q}\). The sampled
deadline obeys
\[
  n\le(Q+1)^M.
\]

Thus non-vacuous escape–return requires no finite ambient spectrum:
summability turns the infinite tail into explicit distortion while a finite
resolved head controls the deadline.

## Formal declarations

- `summablePhaseEnergyAt`
- `summablePhaseRecurrenceBudget`
- `summablePhaseEnergyAt_nat_mul_tick_eq_scaled`
- `exists_summablePhaseEnergyAt_postExit_recurrence_quantitative`
- `summablePhaseEnergyAt_neverExits_or_postExit_return`

## Verification

```text
lake env lean \
  GaloisForLFunctions/RHTower/SummablePurePointEscapeReturnLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SummablePurePointEscapeReturnLaw.olean
```

passed. Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Boundary

The theorem concerns countable pure-point phase packets with summable
weights. It does not cover continuous spectrum, open-system dissipation, or
a thermodynamic-limit Anderson ensemble without a pure-point/summability
transfer.
