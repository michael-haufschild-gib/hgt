# CCM-FU: unconditional terminal cores with small successor envelope

- Stage: 3-formalized.
- Type: derived source theorem; no RH theorem claimed.
- Modules: `MobiusDivisorTerminalBudgetRecovery`, `MobiusDivisorTerminalCoreExistence`.
- Main theorem: `exists_mobiusDivisorSmallTerminalCore`.

## Exact result

There is a fixed integer b≥8 such that, for every ε>0 and all sufficiently
large N, let

`M = 7(b+1)(4N)`,
`A = primes in (b(4N), (b+1)(4N)]`,
`B = active primes in (M/2, M)`.

There exists an actual processed prime set P, contained in the primes below
M, with all four properties:

1. Every prime outside A∪B belongs to P.
2. Every prime p with p²<M belongs to P.
3. The retained head satisfies `|F(M,P,∅)| ≤ 5 sqrt(M)`.
4. The complete successor envelope satisfies `Psi(M,P) ≤ ε M²`.

The fourth bound includes current energy and the energy after inserting
each individual remaining prime. The threshold depends on ε and the fixed
window parameter. The theorem has no initial energy, prepared-front,
fresh-window, RH, or numerical-certificate premise.

## Source proof

Start with P₀ consisting of every prime below M outside A∪B. All remaining
quotients are at most seven. When M≥64, every retained nonempty label is
a singleton. The prime core below eight is already in P₀, so the actual
quotient-seven singleton profile agrees with the previously proved
positive source profile. Every active late singleton is the negative of
its literal unsigned channel.

Write X for the positive mass in A, Y for the positive magnitude of the
negative mass in B, H for the head at P₀, and S for the complete signed
arithmetic sum. The exact terminal identity is

`H + X - Y = S`.

The existing positive window has a fixed c>0 with each coefficient at
least c sqrt(n), at M=7(b+1)n. The prime-window count gives its eventual
mass floor `c n sqrt(n)/(2 log(bn))`. Quantitative PNT already proves
`S(M) log(M)/(M sqrt(M)) → 0`. Comparing these scales proves `|S|≤X`
eventually. The existing actual late-mass comparison gives `|S|≤Y` along
the same cutoff family. Consequently `-H≤X` and `H≤Y`: the head lies in
the interval that the two real signed supplies can cancel.

The finite mass-cover theorem chooses a subset L of whichever sign is
needed, with overshoot at most the largest coefficient. The uniform
prime-fibre estimate bounds every coefficient in A∪B by
`(3/5)·7 sqrt(M) ≤ 5 sqrt(M)`. For P=P₀∪L, exact terminal transport gives
the asserted head bound.

## Complete envelope estimate

The new general estimate, uniform in the processed core, is

`Psi(M,P) ≤ [(a+(3/5)J)² + (9/25)J² pi(M)] M`

whenever the core is terminal, every remaining quotient is at most J,
and the head magnitude is at most a sqrt(M). Each surviving singleton
has magnitude at most `(3/5)J sqrt(M)`, so its total square energy is at
most `(9/25)J² M pi(M)`. Inserting one further prime increases the head
magnitude by at most that one coefficient and leaves a bounded quotient
front. This controls every successor as well as the current state.

Prime density `pi(M)/M → 0` now gives the claimed bound with J=7 and a=5.
All inequalities apply to the literal arithmetic fibres, including signs
and clipped quotient blocks. No computation supplies a proof input.

## What remains for RH

This constructs a favorable terminal endpoint after processing all small
primes and all primes outside two fixed windows. It does not construct a
uniformly bounded ordering from the empty processed core to that endpoint.
It also does not bound the complete signed sum S by O(M).

The existing `exists_mobiusDivisorTerminalPrimeOrder_iff` retains the exact
completion condition: a complete terminal ordering below a budget exists
iff both its starting energy and S² fit that budget. The new construction
supplies the first condition with arbitrarily small quadratic constant;
the second remains the critical arithmetic obligation. A small complete
one-step envelope does not pay an arbitrary number of future insertions.

## Constraint on weighted monotone completion

The [weighted terminal head barrier](ccm-fu-weighted-terminal-head-barrier.md)
proves that, for every fixed positive head weight, these actual cores
exist arbitrarily far out with arbitrarily small quadratic successor
envelope and **no** complete monotone continuation for `V+alpha H²`.
The final signed source escapes every fixed square-root bound on the
same integer grid, whereas bounded terminal singleton leaves cannot
increase a small head beyond the sharp weighted amplitude ceiling.
This restricts that proposed continuation strategy; the core-existence
theorem and the O(M) RH endpoint question are unchanged.

## Validation

Scratch Lean checks and exact leaf emission passed for both proof files.
All five new public declarations were audited once in a temporary file;
each depends only on `propext`, `Classical.choice`, and `Quot.sound`.
No computation was run. Both modules are wired into the RHTower umbrella;
the umbrella was not built. Generated indexes were refreshed and
`scripts/formal_tools.py lint --check-generated` passed, with existing
large-file warnings. Owned scratch files were removed and every owned
Lean process exited. The frontier map was read only.

A scoped Lake package audit remains pending. It was not retried because
prior scoped audit planning requested a broad dependency rebuild,
prohibited by the current build constraints.
