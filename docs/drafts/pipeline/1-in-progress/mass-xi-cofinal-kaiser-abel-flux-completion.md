# Mass–Xi cofinal Kaiser–Abel flux completion

- **Lane:** `1-in-progress`
- **Conjecture:** `C40`
- **Parent:** C39 exact prime-graph Abel flux; Band–Kaiser packet envelope
- **Target:** mass-shifted spectral trace §9.3

## Corpus collision

C39 proves the scalar partial source is exactly

```text
F_(N-1) T_N + sum_{n<N-1} T_(n+1) (F_n-F_(n+1)).
```

Newest Band–Kaiser theorems give coefficient-uniform exponential time-band leakage for every
conditioned `m`-packet span. Their explicit, non-asymptotic hypotheses are

```text
8 m^2 <= sqrt(c),
32 m exp(-sqrt(c)/2) <= 1,
```

and their Rayleigh prefactor is explicit. Thus the construction is not intrinsically fixed-rank:
it permits cofinal schedules `m(c)->infinity` growing sufficiently slower than `c^(1/4)`.

## C40 exact interface

Construct a genuinely non-diagonal synthesis map `J_c` from the first `m(c)` prime-graph Abel-flux
coordinates into the conditioned Kaiser span such that:

1. `m(c)->infinity` and the two explicit Kaiser conditioning hypotheses hold;
2. the mass observation of `J_c` equals the finite C39 Abel flux up to an error uniformly bounded
   on `tau=sigma+iu`;
3. synthesis and observation condition numbers are `exp(o(c))`, uniformly in `m(c)`;
4. the cofinal tail error tends to zero or lies in the already formalized bounded ideal.

Then exponential Kaiser leakage can absorb every subexponential synthesis loss while cofinal rank
recovers the whole scalar prime mode. This is a concrete aperture-recovery mechanism unavailable
to fixed-rank trials.

## Hostile gates

- `J_c` cannot be diagonal or summably weighted diagonal: Hedenmalm/Kronecker recurrence gives
  arbitrarily deep simultaneous resonances.
- `J_c` cannot use uniformly bounded two-prime Bézout coefficients: Lean proves these do not exist.
- Fixed `m` is insufficient; cofinality must be part of the theorem.
- A statement that assumes the uniform C39 Abel-flux bound is circular—it is the scalar source.
- Relative leakage alone is insufficient if synthesis norm grows like `exp(2c)` or faster.
- Compact theta root-flux energy and Suzuki odd-floor amplification are faithful RH detectors, but
  using their vanishing/boundedness as input is also circular unless derived from `J_c`.

## Current status

Kaiser leakage side and C39 finite flux identity are unconditional in Lean. Missing object is the
cross-corpus synthesis map with cofinal, subexponential conditioning. No existing theorem supplies
it. This is the only surviving new avenue found in the latest corpus audit; it is neither a
classical PNT route nor another local prime-difference estimate.
