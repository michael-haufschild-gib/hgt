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

The adjoint up-lags persist throughout the harmonic bulk. The finite unit-orbit
average is now formalized:

`average_{r∈(Z/m)×} c_m(rn+h) = c_m(n)c_m(h)/φ(m)`.

The literal fixed integer-window prime realization is also formalized in
`ActualPrimeWindowsDiagonalizeAffineRamanujanModes`. Continuous weighted
transfer and the required norm estimate remain open; they would be needed
to obtain the proposed integral correction.
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

The previously drafted integral-symbol programme is also deferred. Its proposed identities are

```
E_1(c) = integral_(c,infinity) fract(t)*(1-fract(t))/t^2 dt,
E_m(c) = sum_(d|m) d*mu(m/d)*E_1(c/d)/phi(m)
       = integral_(c,infinity) A_m(t)/t^2 dt / phi(m),
A_m(t) = sum_(d|m) d^2*mu(m/d)*fract(t/d)*(1-fract(t/d)).
```

These are unproved candidate symbol identities, not completed paper proofs.
The finite curvature and cyclotomic norm results are separate Lean modules;
they do not identify a complete overlapping operator with this symbol.
Conductor one alone retains the positive charge term; nontrivial conductors
have zero mean. No implementation of the integral or operator bridges is
part of the current closure work.

The earlier alternative Fourier description
`A_m(t) = (m^2/pi^2) * sum_(k>=1, gcd(k,m)=1) (1-cos(2*pi*k*t/m))/k^2`
is also an unformalized conjectural extension, not a premise of the finite
curvature results. The earlier triangular Ramanujan expansion
`P_m(k)=k*phi(m)+2*sum_(1<=h<k)(k-h)*c_m(h)` was not part of those drafted
modules and is likewise outside the closure scope.

The earlier distant-pair proposal is deferred as well: a normalized width
comparison of order `C_phi*(w-v)*(1/s+1)`, followed by a whole-form bound
`C_phi*(c-1)*(D_N+mass)`, remains unproved. The existing draft only supplies
the absolute-mass continuity of the separated scalar cross term. Continuous
compact-weight extensions of the prime-window limits likewise remain open.

## Existing first crossing

The corpus already proves genuine first-overlap complete positivity for an explicit smooth profile in `TransMetzlerWeilPositivity.TransMetzlerPositivity`, including `c=1+10^-18`. Existence of a first crossing is therefore not a new target here. The open questions concern general profile dependence, larger overlap, actual successor norm residuals, and exhaustion.

## Obligations

1. Classify every admitted product as a bounded integer successor shift,
   including products just outside the finite horizon.
2. Derive the exact joint archimedean-Gram and prime down-row cancellation.
3. The finite unit-orbit identity and fixed integer-window prime-residue
   limits are proved. Their extension to the proposed continuous weighted
   source law and its norm control remains deferred.
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
