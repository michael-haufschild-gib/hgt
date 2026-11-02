# Prime incidence defects have an exact harmonic diagonal

- **Stage:** 2-fully-proven; formalization in progress.
- **Wall:** Σ1e.
- **Statement:** For every finite prime set `P`, real coefficients `b`, and horizon `N`,
  `J_N(Σ_p b_p(1_(p|n)−1/p))=Σ_p (log p/p)H_floor(N/p)b_p²`.

Put `K_N(n)=(log n−ψ₁(floor(N/n)))/n`. The source and target
identities for dilation edges give `Σ_(n≤N) K_N(n)=0`.
For every positive integer `d`, reindexing multiples `n=dj` gives

`K_N(dj)=(log d/d)/j+K_floor(N/d)(j)/d`.

Hence `Σ_(n≤N,d|n) K_N(n)=(log d/d)H_floor(N/d)` exactly.

On the support of von Mangoldt, each incidence jump changes only one prime
coordinate. Its square therefore equals the jump of the incidence packet
with coefficients `b_p²`. Source-target summation gives
`J_N(F_b)=Σ_n F_(b²)(n)K_N(n)`. Expand the prime sum; constant terms vanish
and the multiples identity gives the claimed diagonal.

No size restriction on primes or prime-distribution estimate enters.
The square-root restriction in the large-prime gap concerns the norm's
disjoint-support diagonal, not the defect. This separates the two obstacles.

Corpus boundary: `incidencePacket_dilation_jump`, `sum_dilation_source_eq`,
and `sum_dilation_target_eq` supply the edge identities. The corpus search
found no general finite harmonic evaluation of incidence jump energy.

Lean target: `CompletedArithmeticForms/PrimeIncidenceDefectsHaveAnExactHarmonicDiagonal.lean`,
`jumpEnergy_prime_incidence_eq_harmonic_diagonal`.
