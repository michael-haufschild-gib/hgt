# Frozen follow-up: preserve arithmetic before randomizing

Discovery C1 passes, with adjacent shares 1.3359..1.3748. This alone does not identify a new
producer: independent endpoint shuffles also erase the elementary dyadic Möbius relation.
The following control is frozen before its execution and before opening validation bands.

For each squarefree `d`, remove its prime factors at most `y`, obtaining `r_y(d)`. Replace
`mu(d)` by `mu(d)*epsilon(r_y(d))`, where different rough parts have independent Rademacher
signs and `epsilon(1)=1`. Keep the actual squarefree support and the exact divisor kernel.
This preserves every legal multiplication relation by primes at most `y`, including signs.
It does not preserve multiplication by larger primes or the full Möbius inversion identity.

For each endpoint sum the signed channel coefficients over each rough-part fiber, obtaining
`B_r(M)`. The ensemble mean square is computed exactly as the finite real formula
`E S(M)^2=sum_r B_r(M)^2`, including deterministic `r=1`; no random sampling is required.
For this experiment “exact” describes the finite formula, not machine-certified arithmetic.

Use `y=1,2,3,5,11,31`. Discovery endpoints are the 16 regularly spaced members `i=0,4,..,60`
of every discovery band. Validation uses the same predetermined subset of the two later bands.
Compare raw mean squares, not centered variances; preserve and report the distinction.

**C2 (new, frozen):** even the `y=31` relation-preserving ensemble has average mean square at
least four times the actual source, on every discovery and validation band. A pass would locate
measurable information beyond these finite prime relations; it would not prove a uniform bound,
novelty, or failure of all finite-prime approaches. A failure rejects this quantitative hunch.

Report all six cutoffs and all five bands. Do not move cutoffs or the factor-four threshold.
Validate any decisive finite formula independently at an endpoint using 60-digit arithmetic.
