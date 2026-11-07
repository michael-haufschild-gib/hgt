# Cumulative collision bounds and the exact isolation threshold

- **ID:** SPL-cumulative-collision-gcd-cancellation
- **Stage:** 0-backlog
- **Type:** CANDIDATE THEOREM

For actual balanced smooth rows `A` and prime columns `P`, seek

`E(1/T)≤#A #P+2 floor(4X²/T) #A²`,

and exact equality with the diagonal when `T>4X²`.

The corpus bound for a fixed pair of rows is `g` at differences divisible
by their gcd `g`, and zero otherwise. Summing over differences up to `H`
should give `g floor(H/g)≤H`, cancelling the gcd loss before summing rows.
The logarithmic window has integral difference at most `floor(4X²/T)`.

Inputs: `Goldbach.card_balancedProductCollisionFiber_le_gcd_gate`,
`RHTower.ThinDeletion.card_multiples`, and this programme's exact
smooth/prime diagonal. Corpus comparison finds the fixed-difference
bounds; the cumulative transfer remains to formalize.

This targets a uniform incidence envelope and sharp diagonal regime.
It does not claim the prime-density factors required for random energy.
The corpus's sharper affine prime-pair sieve uses a Selberg quadratic
majorant and is outside the present no-quadratic-sign route.
