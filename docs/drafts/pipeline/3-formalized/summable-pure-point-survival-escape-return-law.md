# Countably infinite pure-point survival escape–return law

- **Status:** formalized
- **Lean module:** `GaloisForLFunctions.RHTower.SummablePurePointSurvivalEscapeReturnLaw`
- **Claim class:** `[LEAN-PROVED] [NEW SYNTHESIS CANDIDATE]`

## Result

For every normalized nonnegative summable pure-point spectral packet
\[
 p_k\ge0,\qquad \sum_{k=0}^{\infty}p_k=1,
\]
let
\[
 A(t)=\sum_{k=0}^{\infty}p_k e^{it\omega_k},
 \qquad S(t)=|A(t)|^2.
\]
For every nonempty head of \(M\) modes and every resolution \(Q\), some
\[
 0<n\le (Q+1)^{M-1}
\]
satisfies
\[
 1-S(n)\le
 \left(\frac{2\pi}{Q+1}\right)^2
   \sum_{k=1}^{M-1}p_k
+ 4\sum_{j=0}^{\infty}p_{M+j}.
\]
The theorem also gives a strictly post-exit return and the exhaustive
never-exits/post-exit-return alternative in the same survival metric.

Only the \(M-1\) projective gaps relative to one reference mode enter the
clock. The complete infinite complement enters through its exact summable
tail; the state itself is not truncated.

## Formal declarations

- `summablePurePointSurvivalProbability_le_one`
- `summablePurePointSurvivalDeviation_nonneg`
- `exists_summablePurePointSurvival_recurrence_quantitative`
- `summablePurePointSurvivalDeviation_nat_mul_tick_eq_scaled`
- `exists_summablePurePointSurvival_postExit_recurrence`
- `summablePurePointSurvival_neverExits_or_postExit_return`

## Verification

Direct foreground compilation passed. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Boundary

The result covers normalized countable pure-point unitary spectral packets.
It does not establish pure-point localization for a concrete Hamiltonian and
does not cover continuous spectral mass.
