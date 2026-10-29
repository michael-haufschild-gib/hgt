# Successor corrections beyond touching

Status: exploratory derivation. No new actual-source limit or positivity theorem.

## Concrete candidate law

For a fixed smooth profile `φ` supported on `[0,1]`, write `M=∫φ²` and
`G(u)=∫φ(v)φ(v+u)dv`. At a fixed overlap ratio `c>1`, the candidate correction
to conductor `m` is

`β_m(c) = (2/M) Σ_{1≤h<c} [c_m(h)/φ(m)] ∫_{h/c}^1 G(u)/u du`.

The proposed complete arithmetic energy is the separated adjunction energy
minus `β_m(c)`. This is a conjectured actual-source asymptotic, not an input
that may be assumed in a theorem.

## Why this correction appears

Group literal non-ratio down-lags by the integer product `ℓ=kj`. At fixed
bounded overlap, only finitely many integer successor shifts `ℓ=n+h` occur.
The exact divisor-convolution formula gives a leading `a(ℓ) log ℓ` term.
It must be combined with the new `log N` times the overlapping atom Gram.
Estimating these separately loses their cancellation.

The adjoint up-lags persist throughout the harmonic bulk. Their weighted prime
sum is expected to read the unit-orbit average

`average_{r∈(Z/m)×} c_m(rn+h) = c_m(n)c_m(h)/φ(m)`.

Weighted PNT in each fixed residue class should then give the stated integral.
The old separated energies therefore cannot be reused unchanged. Every step
needs an exact identity and a full norm estimate for the literal source.

## A symbolic consistency check

For the unit indicator, `G(u)=1-u` on `[0,1]`. At an integer ratio `K≥1`,

`β_1(K)=2[(K-1)log K-log((K-1)!)-(K-1)/2]`.

The proposed completed ground energy reduces to

`2[log Γ(K)-(K-1/2)log K+K-(1/2)log(2π)]`,

twice the classical Stirling remainder. This algebraic reduction suggests a
positive margin tending to zero as overlap grows. It does not prove the
actual-source asymptotic, and the indicator is not a smooth admissible test.
No numerical experiment has been used.

## First attainable target

Prove actual complete positivity on a fixed interval `0<c≤1+δ` for one smooth
near-unit plateau and some `δ>0`. Keep `δ` smaller than the profile's strict
charge deficit. A refined adjacent-lag bound may absorb the new boundary
cost into the prime defect. The full spectral argument then needs the
corrected arithmetic modes, not just their trial energies.

## Obligations

1. Classify every admitted product as a bounded integer successor shift,
   including products just outside the finite horizon.
2. Derive the exact joint archimedean-Gram and prime down-row cancellation.
3. Prove the finite unit-orbit identity and weighted prime-residue limit using
   existing unconditional corpus results.
4. Control the complete residual in norm, including the boundary block and
   both pole moments.
5. Prove uniform bounded-energy compactness for a nonzero overlap interval.
6. Produce a smooth profile with positive corrected ground margin and exhaust
   the complete low spectrum.

Searches153–161 investigate novelty. Existing separated spectral statements,
exact all-width lag calculus, and finite successor-fiber identities are leads;
none inspected so far establishes this proposed source law. The endpoint
chain and annular frame draft are separate active formalizations.
