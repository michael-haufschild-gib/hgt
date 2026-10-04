# BAG complete rational cubic and dilation orthogonality

- **ID:** BAG-C28.56ab.
- **Stage:** 3-formalized for the exact rational statements below.
- **Route:** BAG; physical prime contraction matching remains open.
- **Namespace:** `RHTower.BAGTrace`.
- **Leaves:** `ChiRamanujanFinsuppTrace`, `ChiRamanujanPositiveRationalTrace`,
  `ChiRamanujanRationalCubicTrace`.
- **Source basis:** complete local signed/absolute cubic in C28.56x;
  literal normalized Ramanujan weights in PMPowerDampedMobiusRamanujanWeights.

## Exact new identities

For sigma>1 and EVERY positive rational a, use the literal coefficient

    m_sigma(a) = mu(den(a))/product_(p|den(a))(p^sigma-1).

This is explicitly identified with pmPowerDampedRamanujanWeight(sigma-1,den(a))
divided by its source density. It is not a replacement abstract coefficient.

For EVERY positive rational b, the full unordered dilation sum is absolutely
convergent and satisfies

    sum_a m_sigma(a)*m_sigma(a*b)*a^(-sigma)
      = if b=1 then zeta(sigma)^2 else 0.

The complete unordered positive-rational pair sum is absolutely convergent:

    sum_(a,b) m_sigma(a)*m_sigma(b)*m_sigma(a*b)*a^(-sigma)*b^(-sigma)
      = zeta(sigma)^2.

Its EXACT absolute mass is

    zeta(sigma)^2 * product_p (1+4*p^(-sigma)).

Literal exclusion of both arithmetic axes a=1 and b=1 gives

    sum_(a!=1,b!=1) m_sigma(a)*m_sigma(b)*m_sigma(a*b)*a^(-sigma)*b^(-sigma)
      = 1-zeta(sigma)^2.

The excluded sum is also absolutely convergent. Lean statements use the
real part of riemannZeta at real sigma, as identified with the real Dirichlet
series by the corpus. Damping and positivity specify the domain; no unknown
arithmetic estimate, summability assertion, orthogonality or RH is a premise.

## Dependency-closed proof

For z=p^(-sigma), let c(i)=1 for i>=0, c(-1)=-z/(1-z), and c(i)=0 otherwise.
For j>0 the exact local row c(i)c(i+j)z^i is the geometric tail minus
(1-z)^(-1) times the atom at -1. Its sum is zero. The j=0 sum is
(1-z)^(-2); negative j follows by translation and the factor z^(-j).
This proof never divides by c(j), which can vanish.

Support exhaustion turns finite-prime products into a SINGLE unconditional
sum over finitely supported integer prime valuations. Every finite subsum
fits inside the finite union of its prime supports. Convergence of the
absolute Euler products bounds that subsum; Tannery's theorem identifies
the full sum with the directed cutoff limit. Applied to the complete cubic,
this proves both its signed sum and its exact absolute mass.

The actual square-energy sum is zeta(sigma)^2. A dilation row is dominated
by energy(v)+weight(j)^(-1)*energy(v+j). Translation preserves summability.
Every finite-prime cutoff containing a nonzero j has a zero local factor.
Support exhaustion therefore proves full-lattice dilation orthogonality.

The rational map v |-> product_p p^(v_p) is explicitly bijective. Rational
p-adic valuations recover each coordinate, proving injectivity. The inverse
of positive reduced n/d is factorization(n)-factorization(d); reconstruction
of natural prime factorizations proves surjectivity and multiplication
corresponds to addition.

Coprimality removes every numerator factor from the coefficient. At a
denominator prime power p^k, its factor equals mu(p^k)/(p^sigma-1): k=1 uses
the exact corpus negative-one coefficient, and k>1 is zero. Multiplicative
factorization of mu identifies the literal denominator product. Positive
real power laws identify the weight with a^(-sigma). An explicit pair
equivalence then transports both full cubic sums; no conditional iterated
Fubini interchange is used. Exact axis sums and inclusion-exclusion give
the stated connected rational sum.

## Audit

Foreground production audits FinsuppTrace47237, PositiveRationalTrace84654
and RationalCubicTrace95789 all exited0 without diagnostics using
`lake --old env lean <leaf> -o <olean>`. Axiom audit91107 exited0: all52 public
theorems depend only on propext, Classical.choice and Quot.sound. All three
leaves are wired into RHTower. Index45675 exited0 and all52 names occur in LEAN_API. Lint91425 exited1
with23 unrelated unreachable modules; no new-leaf or proof-debt error.
No full or umbrella build was run.

## Hard frontier still open

These theorems close balanced positive-rational reindexing and fixed-dilation
orthogonality. C28.56ac now proves frequency-weighted rational/tested transfer
and termwise rational-series integration; C28.56aa supplies the arithmetic
compact-test boundary. These results do not identify arithmetic a=1 or b=1 with the physical
prime diagonals p=r or q=r. Actual noncompact/growing profiles, finite-height
near-resonances and coupled damping/band limits remain unresolved, followed
by growing moments, moving cofactors and positive common-height self-return.
RH remains unproved.
