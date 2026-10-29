# Small-prime flips lie below the maximal gap

- **ID:** ACP-SMALL-PRIME-GAP-BOUNDARY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Statement:** For a prime `p`, every hyperplane gap of its single-prime flip is at most `p log(p)/(p+3)`; primes below 11 therefore have positive but nonmaximal gaps. Together with the formalized large-prime lower bound, maximal-gap attainment is equivalent to `11 <= p`.

## Contribution and ownership

This settles the small-prime side left open by the independent valuation-box
result for primes at least 11. It uses the retained counting-to-spectral
bridge for a new upper bound, without replacing that researcher's lower
bound or resuming the discarded prime-41 endpoint. It does not claim the
exact optimal gap at each small prime.

## Checked inputs

`HarmonicParitySpectralCoordinates.lean` identifies squared coordinates of
`v_p,N(n)=omega_p(n)/sqrt(n H_N)` on each actual simple prime eigenline.
The isolating windows eventually contain one eigenline, their energies
converge to the arithmetic energies, and their normalized projected
coordinates equal the actual squared basis coordinates eventually.

The corpus theorem `quadratic_eigenvector_plane` gives the exact norm and
prime form on a plane of two distinct actual eigenvectors. The zero-extension
identities identify that finite matrix form with `atomicWeilForm`.

## Closed paper proof

Put `c=(p-1)/(p+1)>0` and `D=p log(p)/(p-1)>0`. Conductor one has energy
`gamma`; conductor `p` has energy `gamma+D`, since its tame different is
`log(p)/(p-1)`. The finite Mobius transform at conductor one is `1`, and
at conductor `p` is `mu(p)omega_p(1)+mu(1)omega_p(p)=-2`.
Consequently the squared coordinates of the unit parity constraint on the
actual ground and conductor-`p` eigenlines tend respectively to

`A=c^2` and `B=4c^2/(p-1)`.

These are squared coordinates: no choice of eigenvector orientation is
required. The energies are distinct, so sufficiently small energy errors
force the two actual eigenvectors to have distinct indices eventually.

Let their unit representatives be `e_1,e_p`, their actual renormalized
energies be `E_1,E_p`, and their signed parity coordinates be `a,b`.
The vector `z=b e_1-a e_p` satisfies `<v_p,N,z>=0` exactly. Its norm squared
is `a^2+b^2`, and its renormalized prime energy is
`E_1 b^2+E_p a^2`. Multiplying its zero extension by `omega_p` therefore
produces an exactly harmonic-orthogonal test for `HasHyperplaneGap`.

Suppose `g` is such a gap. For every `epsilon>0`, its inequality and the
actual eigenvalue upper bounds eventually give

`(gamma+g-epsilon)(a^2+b^2)
 <= E_1 b^2+E_p a^2
 <= (gamma+epsilon)b^2+(gamma+D+epsilon)a^2`.

Thus `(g-2epsilon)(a^2+b^2)<=D a^2`. Replace the actual squared coordinates
by the identical window-coordinate functions, whose limits are already
proved. Passing this real inequality to the limit gives

`(g-2epsilon)(A+B)<=D A`.

Here `A+B>0`, and `D A/(A+B)=p log(p)/(p+3)`. Letting `epsilon` decrease to
zero proves the upper bound. All eventual bounds are for fixed `p`; no
uniformity in the prime is assumed.

For primes `p<11`, elementary primality exclusion gives `p<=7`. Both
`p/(p+3)` and `log p` are nonnegative and at most their values at seven, so

`p log(p)/(p+3)<=7 log(7)/10<2 log(2)`.

The strict inequality is exactly the logarithm of `7^7<2^20`. This is a
finite exact arithmetic proof, not a numerical approximation. The existing
parity count simultaneously gives the positive lower gap
`(2 log 2)((p-1)/(p+1))^2` for each of these primes.

## Positive boundary

The count gives a nontrivial interval for the admissible gap and proves that
prime two, three, five and seven cannot attain the maximal margin.
The large-prime branch has now been promoted to
`../3-formalized/arithmetic-counting-maximal-gap-rigidity.md`, and its olean
exists. Combining its theorem with this upper bound gives
`HasHyperplaneGap (finiteFlip {p}) (2 * Real.log 2) <-> 11 <= p`
for every prime `p`: the forward implication excludes `p<11`, and the
reverse implication is the existing large-prime theorem. The upper bound
itself uses no large-prime lower bound. All three public endpoints,
including the combined classification, passed Lean and the transitive
axiom audit with only `propext`, `Classical.choice`, `Quot.sound`.

## Corpus audit

Searches for prime-parity upper gaps and small-prime constraints found the
known singleton lower bounds and the large-prime maximal-gap branch, but
no such upper bound. The proof reuses the existing eigenvector-plane law,
actual spectral-coordinate theorem, prime divisor and Mobius identities,
and closure of inequalities under limits. Their statements were inspected.

## Gates

- [x] Exact witness, all source identifications, and closed paper proof.
- [x] Corpus search before mathlib; existing tools reused.
- [x] Lean proof and transitive axiom audit.
- [x] Canonical source check, umbrella, README, scratch cleanup.

## Formal closure

Module: `ArithmeticCountingPositivity/SmallPrimeFlipsLieBelowTheMaximalGap.lean`.

- `primeFlip_hyperplaneGap_le_prime_log_div`: every gap is at most `p log(p)/(p+3)`.
- `smallPrimeFlip_has_positive_but_not_maximal_gap`: positive counted gap and
  failure of the maximal gap for every prime below eleven.
- `primeFlip_hasHyperplaneGap_two_mul_log_two_iff`: maximal-gap attainment
  is equivalent to `11 <= p` for every prime.

The canonical direct source check exited zero with no diagnostics. The
adjacent `arithmetic-counting-small-prime-gap-boundary-audit.txt` records
the exact commands, installed-source SHA256 and actual axiom output.
The leaf is wired into its umbrella and foundational README. No umbrella
was compiled and no olean was needed for this leaf.
