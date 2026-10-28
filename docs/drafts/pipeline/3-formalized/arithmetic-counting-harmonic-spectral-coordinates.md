# Harmonic counts determine actual prime-parity spectral coordinates

- **ID:** ACP-HARMONIC-SPECTRAL-COORDINATES
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean checked)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md

## Statement

For prime `p` and positive conductor `m`, on the actual horizon `1<=n<=N` put

`v_p,N(n)=omega_p(n)/sqrt(n H_N)` and
`u_m,N(n)=c_m(n)/sqrt(phi(m)n H_N)`.

The first vector has norm one when `N>=1`. The second has squared norm tending
to one and vanishing residual for the literal full prime matrix at energy
`log N-E_m`. Its inner product with the first is exactly the mixed harmonic
count divided by `H_N sqrt(phi(m))`, hence tends to

`L_p,m = ((p-1)/(p+1))/sqrt(phi(m)) * sum_{d|m}mu(m/d)omega_p(d)`.

For each `m` an isolating window contains exactly one actual prime eigenline
eventually. The squared coordinate of `v_p,N` on that eigenline tends to
`L_p,m^2`. In particular the ground coordinate tends to `((p-1)/(p+1))^2`,
and every nontrivial conductor coprime to `p` has coordinate tending to zero.

## Dependency-closed proof

The exact sign identity `omega_p(n)^2=1` gives `||v_p,N||^2=H_N/H_N=1`.
Euler's harmonic asymptotic gives `H_N/log N ->1`. The corpus proves both
the raw Ramanujan squared norm divided by `log N` tends to one and the raw
squared matrix residual divided by `log N` tends to zero. Dividing those
limits by `H_N/log N` proves their harmonic-normalized counterparts.

The inner product identity follows termwise: the two square-root weights
multiply to `n H_N`, with the remaining factor `sqrt(phi(m))`. The exact
mixed-count theorem supplies its limit. No convergence of a chosen
eigenvector orientation is used.

Let `P_N` be the spectral projection onto a fixed radius `delta>0` about
`E_m` in renormalized energy. Off that window the spectral distance from
`E_m` is at least `delta`; Parseval therefore gives

`delta^2 ||u_m,N-P_N u_m,N||^2 <= ||residual_m,N||^2`.

The projection error tends to zero. Pythagoras gives
`||P_N u_m,N||^2 ->1`, and Cauchy with `||v_p,N||=1` gives
`<v_p,N,P_N u_m,N> ->L_p,m`. Thus

`<v_p,N,P_N u_m,N>^2 / ||P_N u_m,N||^2 -> L_p,m^2`.

Choose an isolating arithmetic radius using properness and separation of
adjunction energies. The existing exact full-prime spectral count makes
this window a singleton eventually. For its unit eigenvector `e_N`, write
`P_N u_m,N=alpha_N e_N`. The denominator tends to one and is eventually
nonzero, so the displayed quotient equals `<v_p,N,e_N>^2` exactly. This
discharges the actual eigenline interpretation rather than assuming it.

## Inputs and novelty

Inputs owned by Renormalized Arithmetic Potential Theory: raw Ramanujan
quasimodes, norm asymptotics, finite spectral exhaustion and isolated
eigenlines. Inputs owned by Arithmetic Counting Positivity: the exact parity
boundary count and mixed Mobius transform. The new bridge identifies a
nonperiodic multiplicative constraint in the actual finite prime spectrum.
It is not a claim to a new abstract spectral projection theorem.

## Gates

- [x] Closed paper argument with the actual matrix and normalization specified.
- [x] Corpus leads inspected before mathlib lookup.
- [x] All 14 exact Lean declarations checked and axioms audited; only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Final leaf audit, umbrella and README.

The checked source is installed as
`ArithmeticCountingPositivity/HarmonicParitySpectralCoordinates.lean` and
wired into the own umbrella. The foundational README states the coordinate
law and its scope. The final installed-source check exited zero without diagnostics. The
transitive axiom log and source hash are in
`arithmetic-counting-harmonic-spectral-coordinates-audit.txt`. No olean or
umbrella build was needed for this leaf.

## Scope

This coordinate theorem identifies the nonperiodic multiplicative constraint
on the actual spectrum; it does not by itself bound all constrained vectors.
It is retained as a reusable counting tool independently of the valuation-box
maximal-gap theorem for primes at least 11. The redundant spectral endpoint
for primes at least 41 has been dropped at the user's direction.
