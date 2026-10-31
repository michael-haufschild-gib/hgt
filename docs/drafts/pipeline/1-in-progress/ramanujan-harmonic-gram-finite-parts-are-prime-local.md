# Ramanujan harmonic Gram finite parts are prime-local

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `three-frontier-questions-full-solutions.md`, Q1/O1;
  `../3-formalized/cact-growing-conductor-gram.md`.
- **Target:** Identify the complete finite part of the harmonic Ramanujan
  Gram, including every mixed conductor entry.

Let `u_m(n)=c_m(n)/sqrt(phi(m))` and
`G_m,l(N)=sum_(1≤n≤N) u_m(n)u_l(n)/n`. For positive conductors, conjecture

`G_m,l(N) − 1_(m=l) log N → B_m,l`,

where

- `B_m,m = gamma − log m + tameDifferent(m)`;
- `B_m,l = −log p sqrt(phi(m)/phi(l))` when `l=m p^k`, `p` prime, `k≥1`;
- the symmetric value holds when `m=l p^k`;
- every other mixed entry is zero.

## Arithmetic mechanism

The divisor formula gives the exact finite Gram as

`sum_(d|m,e|l) mu(m/d)mu(l/e) gcd(d,e) H_floor(N/lcm(d,e)) / sqrt(phi(m)phi(l))`.

Its finite part is therefore `gamma·1_(m=l)` minus the same divisor
sum weighted by `log(lcm(d,e))`. Prime factorization separates that
logarithm into one local contribution at a time. Every remaining prime
contributes the ordinary Ramanujan orthogonality factor. Thus two primes
with different conductor valuations force zero. At the single differing
prime, the local logarithmic factor is the totient of the lower power.

The resulting finite-part matrix should have norm `O(log(2Q))` on
conductors up to `Q`: use Schur weights `1/sqrt(phi(m))`, divisor counting
for downward entries and the prime Mertens sum for upward entries.
This would retain cross-conductor cancellation absent from entrywise
polynomial bounds. The norm bound and the full Weil agreement-shell
identity remain separate targets.

## Divisor-edge formulation

For `M>0`, put `F(n)=sum_(m|M) f_m c_m(n)` and
`mass=sum_(m|M) phi(m) f_m²`. The proposed exact limit is

`sum_(n≤N) F(n)²/n − mass log N`
`→ (gamma−log M) mass + sum_(k|m|M) Lambda(m/k) phi(k) (f_m−f_k)²`.

For a gcd-class function `V`, reciprocal inversion gives
`V(gcd(M,n))=sum_(d|M) a_d c_d(n)`, where
`a_d=M⁻¹ sum_(j|M) V(M/j)c_j(M/d)`.
The known harmonic limits are `H_N−log N→gamma` and
`sum_(n≤N)c_d(n)/n→−Lambda(d)` for `d>1`. Thus the finite part is
`gamma a_1−sum_(d|M)a_d Lambda(d)`.

The exact downward convolution gives
`sum_(d|M)Lambda(d)c_j(M/d)=phi(j)[log M−log j−tameDifferent(j)]`.
Consequently the gcd-class finite part is
`M⁻¹ sum_(j|M)phi(j)V(M/j)[gamma−log M+log j+tameDifferent(j)]`.
Taking `V=F²`, reciprocal Plancherel supplies the mass and the existing
divisor-jet spectral identity supplies the edge energy. This is a closed
paper proof using existing finite identities and harmonic limits.
Expanding the edge squares gives the prime-local Gram entries.

## Open inputs

The divisor-edge finite part, its polarization, and the individual raw
Gram entries passed Lean with only the standard three axioms in
`SuccessorShellArithmetic/Conductor/HarmonicGramFinitePart.lean`.
The final source audit, torsion identification, and operator bound remain.
The full Weil agreement-shell identity remains unproved and is not assumed
in the growing-overlap positivity argument.

## Torsion interpretation

The proposed entry formula is equivalently
`B_m,l=gamma·1_(m=l)−I(m,l)/sqrt(phi(m)phi(l))`, where `I` is the
archimedean intersection of primitive torsion orbits. Its diagonal is
`I(m,m)=phi(m)[log m−tameDifferent(m)]`; its mixed entries obey the
prime-power Hecke law. These two torsion identities already exist in Lean;
identifying them with the sharp harmonic finite part is the new claim.

The existing logarithmic torsion counterterm and entrywise nonnegativity
then bound the absolute finite-part form on conductors `≤Q` by
`[|gamma|+4 log Q+log 4+4] sum phi(m)f_m²`.
This identifies the proposed logarithmic operator bound with an existing
torsion-energy estimate. The harmonic-to-torsion identity still needs Lean
verification; finite-horizon remainder bounds remain separate.
