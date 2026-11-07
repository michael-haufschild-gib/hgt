# Gcd classes of smooth × prime near-collisions

- **ID:** SPL-smooth-prime-determinant-gcd
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM
- **Question:** Which arithmetic restrictions survive on a nonzero shifted-product fibre?

Let `m,m'` have only prime factors at most `y`, and let primes `p,p'>y`.
If `mp+h=m'p'`, then

`gcd(m,h)=gcd(m',h)=gcd(m,m')`.

Thus, for each nonzero difference `h`, contributing smooth rows belong to
the same exact class `d=gcd(m,h)`. This is stronger than the unrestricted
integer-fibre condition `gcd(m,m')|h`: the classes are disjoint, and the
column coprimality is an arithmetic consequence of smoothness and roughness.

The proposed proof uses `gcd(m,h)=gcd(m,m'p')` and `gcd(m,p')=1`, then
interchanges the rows. A finite incidence bound should retain these exact
classes before summing over differences within the logarithmic tolerance.
Existing balanced-integer fibre bounds already count at most gcd-many
column pairs; reproducing that bound alone is not the target.

Corpus comparison and Lean verification remain open. No prime-pair
asymptotic, random-energy law, or exponential-sum saving is claimed.
