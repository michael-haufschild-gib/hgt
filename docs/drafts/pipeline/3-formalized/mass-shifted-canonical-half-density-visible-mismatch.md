# Mass-shifted canonical half-density visible mismatch

- **ID:** `mass-shifted-canonical-half-density-visible-mismatch`
- **Stage:** 3-formalized
- **Route:** mass-shifted spectral face / canonical admission drift
- **Type:** THEOREM + EXACT FRONTIER REDUCTION
- **Scientific status:** `[PROVED HERE] [LEAN FORMALIZED] [NOVELTY UNVERIFIED]`
- **Lean:** `RHTower.XiShiftedAdaptiveHalfDensityCanonicalMismatch`

## Public sentence

After constructing the positive monic half-density producer, actual inverse-Hankel admission
differs in odd current through one scalar only; raw canonical drift is exactly negative norm times
one reserve.

## Exact theorem

Let `V_n` be actual canonical inverse-Hankel coefficient velocity and `M_n` the source-native monic
half-density landing from the predecessor card. Both have degree `<n`. Define

`delta_n=[X^(n-1)](V_n-M_n)`.

Then, in a positive `(n+2)` block,

`<V_n-M_n,XP_n>=h_n delta_n`,

`delta_n=[X^(n-1)]V_n-E_n^mon`,

and the existing canonical source connection is

`C_n=2h_n(E_n^mon+delta_n)`.

Define

`R_n=E_n-E_n^mon-delta_n`,

where `E_n` is full adaptive Jacobi source energy. Actual canonical odd current satisfies

`I_n'=-2h_n R_n`.

Thus all coefficient-projection, terminal-port, and lower-polynomial ambiguity disappears from
the raw drift. Its sign is equivalent to one exact scalar reserve.

## Proof

Corpus theorems give `deg V_n<n`. The predecessor proves `deg M_n<n` and
`[X^(n-1)]M_n=E_n^mon`. The finite orthogonal-coupling theorem says every polynomial `W` of degree
`<n` obeys

`<W,XP_n>=h_n[X^(n-1)]W`.

Apply it to `W=V_n-M_n`; this proves the first two identities. Unfolding the canonical source
connection `C_n=2h_n[X^(n-1)]V_n` gives the third. Substitute it into the already-formalized
canonical odd-current derivative `I_n'=-2h_nE_n+C_n` and collect terms.

## Conjecture loop

1. **Canonical mismatch remains an uncontrolled lower polynomial — FALSIFIED.** Odd-current
   coupling annihilates every lower coordinate except degree `n-1`.
2. **Positive monic landing alone signs actual drift — FAIL.** Actual visible mismatch `delta_n`
   survives with unrestricted sign.
3. **Exact survivor — PROVED.** Raw drift is `-2h_n R_n`; route burden is exactly `R_n>0` or a
   source/arithmetic identity forcing the same conclusion.

## Remaining open core

This card's scalar identification burden is now closed by successor
`mass-shifted-half-density-adjacent-connection`. Actual canonical velocity satisfies

`V_n=M_n+(n-1/2)beta_n P_(n-1)`,

so `delta_n=(n-1/2)beta_n` unconditionally. The remaining open core is sign or accumulated control
of resulting terminal Jacobi Riccati defect along cofinal degree-changing first contact. RH is not
proved.

## Verification

- Direct Lean check: PASS.
- `lake build GaloisForLFunctions.RHTower.XiShiftedAdaptiveHalfDensityCanonicalMismatch`: PASS.
- Axiom audit of the canonical reserve derivative theorem: only `propext`,
  `Classical.choice`, and `Quot.sound`.
- No computation, `sorry`, `admit`, new axiom, or RH premise.
