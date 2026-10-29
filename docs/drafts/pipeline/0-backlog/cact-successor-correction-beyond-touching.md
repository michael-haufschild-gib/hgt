# Successor corrections beyond touching

Status: deferred conjectural programme. No paper proof of the proposed source law, integral symbol identity, or exhaustive overlap positivity is claimed. Existing finite-source drafts are being closed separately; this card authorizes no new implementation.

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

## Unproved model identities to investigate

For the unit indicator, `G(u)=1-u` on `[0,1]`. At an integer ratio `K≥1`,

`β_1(K)=2[(K-1)log K-log((K-1)!)-(K-1)/2]`.

The proposed completed ground energy reduces to

`2[log Γ(K)-(K-1/2)log K+K-(1/2)log(2π)]`,

the expression twice the classical Stirling remainder. This proposed identification suggests a
positive margin tending to zero as overlap grows. It does not prove the
actual-source asymptotic, and the indicator is not a smooth admissible test.
No numerical experiment has been used.

## Existing first crossing

The corpus already proves genuine first-overlap complete positivity for an explicit smooth profile in `TransMetzlerWeilPositivity.TransMetzlerPositivity`, including `c=1+10^-18`. Existence of a first crossing is therefore not a new target here. The open questions concern general profile dependence, larger overlap, actual successor norm residuals, and exhaustion.

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

A potentially shorter first crossing uses relative form continuity. Prove,
for the actual normalized complete forms and one fixed smooth profile,

`|W_{c,N}(x)-W_{1,N}(x)| ≤ C ω(c-1)(D_N(x)+‖x‖²)`, with `ω(δ)→0`,

uniformly in `N`. Combining endpoint bounds `W_1≥b‖x‖²` and
`W_1≥a‖x‖²+εD_N`, when `Cω(c-1)<ε`, gives
`W_c≥[b-Cω(c-1)((b-a)/ε+1)]‖x‖²`. This would prove positivity at
some genuine overlap without first identifying its full spectrum.

The analytic obligation is substantial: normalized ratio-prime terms cancel,
but the new near-neighbor Gram and non-ratio terms require small relative
bounds. The top-atom potential `(n/N)log n` is already paid by the prime defect.
Near overlapping archimedean pairs must retain the cancellation inside the
Lévy integral; the separate cross integral need not exist there. Self, pole,
and far-cross differences must have a modulus tending to zero, not merely
a bounded error. This relative-continuity statement is unproved.

Searches153–161 investigate novelty. Existing separated spectral statements,
exact all-width lag calculus, and finite successor-fiber identities are leads;
none inspected so far establishes this proposed source law. The endpoint
chain is formalized; the finite arithmetic and annular source modules are separate results. The actual larger-overlap law and the integral symbol matching remain open.
