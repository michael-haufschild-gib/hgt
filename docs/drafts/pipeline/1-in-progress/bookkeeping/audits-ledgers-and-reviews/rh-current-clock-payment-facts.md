# Current-clock payment from actual prime windows

Owner: critical-clock product task. RH and exhaustive completion remain open.

## Frozen producer target [BRIDGE]

Construct actual prime batches at the current cutoff, preserving the complete
weight `1 + log r`, with a uniform prefix allowance and a positive quadratic
terminal clock payment. Use the full available window capacity, rather than
only square-root many helpers. The initial receiving coordinates must be
controlled in the same weighted metric used by the clock energy.

## Source facts

- The literal quotient windows at 2, 7, and 14 supply fresh inward directions
  and positive copied-square reserves (`MobiusDivisorPrescribedWindowRepair`).
- Their common capacity is at least `N/(14 log(14 b N))` eventually
  (`MobiusDivisorLogarithmicWindowCapacity`).
- The exact logarithmic prime merger retains a negative `p log p` copied
  diagonal (`MobiusDivisorFiniteClockCountingCancellation`). Existing raw
  neutralization does not retain this weight in its selection metric.
- The prior current-clock depth theorem excludes repayment of certain whole
  old-prime debts using only these bounded-quotient windows. A successful
  local producer cannot be reported as an exhaustive repayment schedule.

## Closed source mechanism

Scale the second receiving coordinate by `sqrt(1 + log 2)`. Inward selection
then bounds the actual weighted receiving energy, including every prefix.
Each removed packet retains at least `(1 + log p)` times its raw square
reserve. With order `M/log M` actual primes, the cumulative payment has order
`M²`, while the terminal weighted receiving remainder has order `M`.

This targets a current-clock reserve with the full weight, not payment of
the order `M² log M` inherited debts from the preceding obstruction.

The complete finite identity is

`W(P ∪ S) + G(P) + sum(packet(p), p in S) = W(P) + G(P ∪ S)`,

where `G(P) = F(P,empty)² + (1 + log 2) F(P,{2})²`, and

`packet(p) = p ((1 + log p) u_p² + (1 + log p + log 2) v_p²)`.

Here `u_p,v_p` are the literal clipped child fibres at the current cutoff.
The identity retains all external source components; the prepared child
support proves their mixed terms vanish, rather than discarding them.

## Checked producer and route implication

Both public statements passed scratch Lean and axiom audit, with only
`propext`, `Classical.choice`, and `Quot.sound`:

- `eventually_exists_mobiusDivisorCurrentClockPayment` chooses fixed
  `b,R,delta > 0` before the admission constant `C`. At every sufficiently
  large current wall `M = 14(b+1)N`, it constructs `capacity(b,N)-1`
  distinct actual primes for every prime core containing the literal small
  core, omitting two, leaving the source pool unused, and satisfying
  `G(P) <= C M²`. Every prefix obeys `W(prefix) <= W(P) + R² M`;
  the endpoint satisfies `G(Q) <= R² M` and
  `W(Q) + G(P) + delta M² <= W(P)`.
- `eventually_exists_mobiusDivisorInitialClockPayment` supplies the literal
  initial core and proves its admission bound internally. It has no
  energy, source-sign, correlation, or payment hypothesis.

The first theorem's cutoff threshold depends on `C`, not on the admitted
core. This is uniform current-wall control across growing cores satisfying
those explicit structural conditions. It does not construct a history that
maintains them at successive cutoffs.

Whole-route consequence: bounded-depth source batches can genuinely produce
quadratic clock payment. The logarithmic source weight compensates for the
prime-window count's logarithmic loss. The earlier depth obstruction leaves
larger debts of order `M² log M`; this producer does not pay those debts.
The missing step is a multiscale producer retaining full signed components
at increasing child depth, together with cutoff transport and completion.

## Search discrimination

The weighted-source deep search completed (`partial=false`); the broader
cutoff-method search was partial. Candidate statements were checked against
source and scratch Lean. No retrieved theorem already supplied this clock
producer.

Broad recent searches opened [Farih, September 2026](https://arxiv.org/abs/2609.15443)
and [Liu et al., September 2026](https://arxiv.org/abs/2609.11595).
The former studies moment bounds for fluctuating efficiency; the latter
allows engineered quantum dissipation. Neither supplies cancellation for
the fixed arithmetic source, and neither is a premise of the proof.

## Audit

Promoted module:
`formal/GaloisForLFunctions/RHTower/MobiusDivisorCurrentClockPayment.lean`.
The named audit `lake build GaloisForLFunctions.RHTower.MobiusDivisorCurrentClockPayment`
passed; its only newly built module took 171 seconds. The RH umbrella imports
the module. No full or umbrella build was run. Index refresh and whitespace
checks passed. Global lint retains the same four unrelated unreachable
modules recorded in `rh-current-clock-depth-facts.md`; the new module has
no reported lint error.

Logs: `/tmp/hgt-clock-payment-{check,build,index,lint}.log`.
The compiled-module axiom audit also passed for both public theorems:
only `propext`, `Classical.choice`, and `Quot.sound`. Its log is
`/tmp/hgt-clock-payment-final-axioms.log`. Owned Lean processes exited;
the scratch Lean files and assembly fragments were removed.
