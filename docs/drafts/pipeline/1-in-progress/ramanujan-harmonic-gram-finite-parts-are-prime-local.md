# Ramanujan harmonic Gram finite parts are prime-local

- **Stage:** 1-in-progress
- **Type:** THEOREM; final direct audits pending
- **Source:** `three-frontier-questions-full-solutions.md`, Q1/O1.

## Exact finite part

For positive conductors, let `u_m(n)=c_m(n)/sqrt(phi(m))` and
`G_m,l(N)=sum_(1≤n≤N)u_m(n)u_l(n)/n`. Then

`G_m,l(N)−1_(m=l) log N → B_m,l`
`B_m,l=gamma·1_(m=l)−I(m,l)/sqrt(phi(m)phi(l))`,

where `I` is the archimedean intersection of primitive torsion orbits.
In particular:

- `B_m,m=gamma−log m+tameDifferent(m)`;
- `B_m,mp^k=−log p sqrt(phi(m)/phi(mp^k))` for prime `p`, `k≥1`;
- symmetry gives the reverse edge; every other mixed entry is zero.

For `M>0`, `F(n)=sum_(m|M) f_m c_m(n)`, and
`mass=sum_(m|M)phi(m)f_m²`, the exact divisor-edge form is

`sum_(n≤N)F(n)²/n−mass log N`
`→ (gamma−log M)mass+sum_(k|m|M)Lambda(m/k)phi(k)(f_m−f_k)²`.

Every finite conductor packet has finite part `gamma·mass−sum f_m f_l I(m,l)`.
On conductors through `Q`, its absolute value is at most
`[|gamma|+4 log Q+log 4+4]mass`.

## Proof

For a gcd-class profile `V`, reciprocal inversion gives
`V(gcd(M,n))=sum_(d|M)a_d c_d(n)`, with
`a_d=M⁻¹sum_(j|M)V(M/j)c_j(M/d)`.
The harmonic limits are `H_N−log N→gamma` and
`sum_(n≤N)c_d(n)/n→−Lambda(d)` for `d>1`.
The finite part is therefore `gamma a_1−sum_(d|M)a_d Lambda(d)`.

The exact downward convolution is
`sum_(d|M)Lambda(d)c_j(M/d)=phi(j)[log M−log j−tameDifferent(j)]`.
Thus the gcd-class finite part equals
`M⁻¹sum_(j|M)phi(j)V(M/j)[gamma−log M+log j+tameDifferent(j)]`.
For `V=F²`, reciprocal Plancherel gives the mass and the divisor-jet
spectral identity gives the positive edge energy. Polarization and
conductor indicator functions identify every mixed entry.

The torsion self-intersection is `phi(m)[log m−tameDifferent(m)]`;
its mixed entries are `I(m,mt)=phi(m)Lambda(t)`, `t>1`, and zero
without a divisibility edge. These identify the sharp harmonic finite part.
Entrywise nonnegative intersections bound the absolute signed pairing by
the pairing of absolute coefficients. The logarithmic torsion counterterm
then gives the stated operator bound.

## Lean

Both modules lie in `SuccessorShellArithmetic/Conductor/`:

- `HarmonicGramFinitePart.lean`: gcd-profile finite part, reciprocal
  Plancherel, divisor-edge limit, polarization, diagonal and mixed raw entries.
- `HarmonicGramTorsionEnergy.lean`: exact torsion identification, normalized
  prime-power entries, finite-packet limit and logarithmic absolute bound.

Both compiled; all sixteen axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. Umbrella imports are present.
Final direct no-olean source audits remain.

The finite-horizon remainder is a separate target. The full Weil
agreement-shell identity remains open.
