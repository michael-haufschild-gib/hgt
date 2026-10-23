# Cubic rough dilation edges are scaled twin-prime pairs

- **ID:** twin-prime-cubic-dilation-classification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [signed cubic roughness](../1-in-progress/twin-prime-signed-cubic-roughness.md)
- **Statement:** Nontrivial dilation edges whose endpoints are below the
  cubic roughness boundary are exactly prime dilations of twin-prime pairs.

## Exact objects

For a natural number `z`, let `F_z` contain pairs `(a,b)` satisfying

`2≤a`, `2≤b`, `z≤P⁻(ab)`, and `ab<z³`.

Let `E_z` contain `(d,a)` for which `(d,a)` and `(d,a+2)` both belong to
`F_z`. These are precisely the nontrivial divisible edges
`da → da+2d` on this support, with both cofactors greater than one.

The exact classifications are

`F_z = {(p,q): p,q prime; z≤p; z≤q; pq<z³}`,

`E_z = {(q,p): q,p,p+2 prime; z≤q; z≤p; q(p+2)<z³}`.

Repeated prime factors are allowed: the first endpoint can be a prime
square. No squarefree restriction or sign approximation is used.

## Dependency-closed paper proof [PROVED HERE]

For a positive integer `n`, the fundamental theorem of arithmetic gives

`P⁻(n)^Ω(n) ≤ n`,

because every factor in its prime factorization is at least `P⁻(n)`.
If `z≤P⁻(n)` and `n<z³`, then `Ω(n)<3`: otherwise
`z³≤P⁻(n)³≤P⁻(n)^Ω(n)≤n`, a contradiction.

For `(a,b)∈F_z`, both `Ω(a)` and `Ω(b)` are positive, and their sum is
`Ω(ab)<3`. Both are therefore one, so `a,b` are prime. Since they divide
`ab`, each is at least its least prime factor and hence at least `z`.
Conversely, every prime factor of a product of two primes `p,q` is `p`
or `q`. Thus `z≤p,q` implies `z≤P⁻(pq)`; the other conditions are exactly
those defining `F_z`. This proves the first equality, including empty
cases `z=0,1`.

Apply the first equality to both members defining `E_z`. It gives
primality of `d,a,a+2`, both lower bounds, and the larger endpoint bound.
Conversely these conditions give both factor-pair memberships: `a+2≥a`
supplies its lower bound, and `da≤d(a+2)<z³` supplies the smaller height
bound. This proves the second equality.

For the Lean proof, the same contradiction needs only the smallest-factor
square bound. If a nonunit factor `a` were composite, then
`z²≤P⁻(a)²≤a`; its nonunit cofactor `b` satisfies `z≤b`. Hence
`z³≤ab`, contradicting the height bound. Exchange `a,b` for the other
factor. The square bound follows by writing `a=P⁻(a)c`: minimality of
the least prime factor gives `P⁻(a)≤c` when `a` is composite.

## Audit and scope

**Verdict: REDISCOVERED.** This is an exact application of elementary
factor-count additivity. No new analytic or number-theoretic advance is
claimed. It is the positive classification exposed by the failed direct
dilation transfer; it is stronger than saying that a particular label
supply becomes empty.

Internal search surfaced
`GaloisForLFunctions.Goldbach.minFac_pow_cardFactors_le` and the related
negative-Liouville cubic detector. Their Lean statements and proofs were
read. The final implementation uses Mathlib's equivalent smallest-factor
square bound, avoiding a new dependency on the Goldbach leaf. The reflected
Goldbach counting identity is not a twin-prime estimate.

The polynomial-height depth argument is separate: if a label contains
`J` prime factors all exceeding `X^(1/3)`, then it exceeds `X^(J/3)`.
A fixed polynomial height allows only bounded `J`. This does not prohibit
graphs at larger heights, fixed-depth methods, or other forms of
amplification.

The published rough-pair graph has physical heights larger than its
original counting scale. The classification does not apply to all its
edges; it applies exactly to edges with the displayed cubic endpoint
bounds. It neither refutes that paper nor supplies a lower bound for `E_z`.

## Lean status

Exact set equalities in
`formal/GaloisForLFunctions/twin-prime/CubicDilation.lean`:

- `TwinPrime.cubicFactorPairs_eq_prime_products`
- `TwinPrime.cubicDilationPairs_eq_prime_twin_parameters`

Leaf audit passed with
`lake --old env lean GaloisForLFunctions/twin-prime/CubicDilation.lean`.
Both dependency closures contain only `propext`, `Classical.choice`,
and `Quot.sound`. Own umbrella wired without compiling it. No infinitude
theorem, analytic premise, placeholder, or raised elaboration option added.

The initial Goldbach import reported a missing `.olean`. Its exact leaf
was audited with the prescribed plain command and passed, but retrying
the consumer still reported the missing artifact. The final proof uses
already compiled Mathlib imports and the smallest-factor square bound;
no output flags, build command, or unrelated source changes were used.
