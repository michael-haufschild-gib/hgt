# Arithmetic Newton sampling below the length threshold

- **ID:** AHA-NEWTON
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/aha-adams-multiplicity-cost.md
- **Statement:** Weighted order-`d` torsion samples of Newton orders below `r` determine every coefficient supported on `1≤n<2^(dr)`.

## Exact statement

Let `d,r≥1`, let `P` be the primes below `2^(dr)`, and write
`v_p(n)=b_p(n)+d k_p(n)`, `0≤b_p(n)<d`. Set

`S_α(t)=Σ_n a_n (∏_p binom(k_p(n),α_p)) χ_n(t)`

and

`J(b,α)=Σ_{b(n)=b} a_n ∏_p binom(k_p(n),α_p)`.

Exact Fourier recovery gives
`Σ_t S_α(t) conj(χ_b(t)) = d^|P| J(b,α)`.
Two coefficient arrays have identical `S_α(t)` for every `|α|<r` and every
torsion point `t` if and only if the arrays are equal.

## Proof

Residues and quotients reconstruct every prime valuation, hence every
positive integer. Unique factorization gives
`2^(d Σ_p k_p(n))≤∏_p p^v_p(n)=n<2^(dr)`, so `Σ_p k_p(n)<r`.

For a nonzero array choose a nonzero term with maximal total quotient degree.
Its own Newton coefficient receives no contribution from any different
term in its residue fibre: a nonzero binomial product would require
componentwise larger quotient exponents, and maximal total degree then
forces equality. The surviving contribution is its original nonzero
coefficient. Thus some order below `r` detects the array. Fourier
orthogonality recovers that Newton coefficient from the samples. Apply
the zero-kernel result to the difference of two arrays.

## Lean

Namespace `GaloisForLFunctions.ArithmeticHarmonicAnalysis`.

- `ResidueNewtonDetection.lean`: `exists_top_residueNewtonCoefficient`,
  `residueNewton_vanishing_iff`.
- `ArithmeticNewtonResolution.lean`: `valuationQuotient_order_lt`,
  `arithmeticNewtonCoefficient_eq`, `arithmeticNewton_sample_recovery`,
  `arithmeticNewton_samples_eq_iff`.

Transitive axiom checks: `propext`, `Classical.choice`, `Quot.sound` only.
Source audit: `lake --old env lean GaloisForLFunctions/ArithmeticHarmonicAnalysis/ArithmeticNewtonResolution.lean`.

## Boundary

The binomial transform and finite Fourier inversion are classical. The
arithmetic content is the exact length filtration and its injective sampling
interface. These weighted samples have explicit coefficients. Their
identification with full torus jets is a separate open theorem on AHA-JETS;
no multiplicity or coefficient-height bound is assumed here.
