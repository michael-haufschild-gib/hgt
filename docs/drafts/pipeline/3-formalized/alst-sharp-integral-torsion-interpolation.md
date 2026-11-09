# Sharp integral torsion interpolation

- **ID:** alst-sharp-integral-torsion-interpolation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `q>0`, modulo `J_q^r`, every integer polynomial has a unique Newton remainder supported on `Σ_p floor(a_p/q)<r`; it minimizes arithmetic length in its class. For nonempty `P` and `r>0`, all integral classes admit representatives of length at most `N` exactly when `N ≥ (∏_p p^(q−1)) p_max^(q(r−1))`.

## Purpose
Determine the exact length needed to interpolate every admissible integral torsion jet. This is an arithmetic interpolation threshold for S1/S3 on the full torsion grid, not a claim about zeros on the prime orbit or separation of zeta from other Euler products.

## Proof route
Split the integral Newton coordinates into quotient orders below and at least `r`. The latter part is exactly `J_q^r`; the former is the unique remainder. Exact preservation of arithmetic length by Newton synthesis makes its length minimal in its congruence class. Every low-order index has remainder exponents at most `q−1` and at most `r−1` quotient blocks, so its weight is at most the displayed threshold. Equality is attained by putting every remainder exponent at `q−1` and all quotient blocks on the largest prime. That single Newton class forces the lower bound for every representative.

## Gates
- [x] Corpus search found no exact integral interpolation threshold or length-minimizing quotient representative.
- [x] Dependency-closed paper proof and boundary cases.
- [x] Lean formalization and transitive axiom audit.

## Dependency
Filtered integral torsion normal form: `torsionNewtonBasis`,
`length_torsionNewtonSynthesis`, and `fullTorsionMultiplicity_iff_mem_gridIdeal_pow`
in `TheFilteredTorsionKernelHasAnIntegralBasis.lean`.

## Boundary cases
For `r=0`, the quotient is zero and the universal cutoff is `0`. For empty
`P` and `r>0`, the quotient is `ℤ` and the cutoff is `1`. For `q=1`, the
nonempty-prime formula reduces to `p_max^(r−1)`. Uniqueness concerns the
low-quotient-order remainder; other representatives can share its minimum length.

## Exact quotient argument
Write `c(F)` for the unique Newton coordinates. Then `F−G∈J_q^r` exactly
when `c(F)_a=c(G)_a` for every `Q_q(a)<r`. Filtering `c(F)` to these indices
therefore gives the unique reduced representative. Its support is contained
in the coordinate support of every congruent polynomial; exact length
preservation gives minimality. Hence universal interpolation at `N` is
equivalent to `weight(a)≤N` for every `Q_q(a)<r`.

For such an index, write `a_p=s_p+qk_p`, with `0≤s_p≤q−1` and
`Σk_p≤r−1`. Then `∏p^a_p≤(∏p^(q−1))p_max^(q(r−1))`. Equality is attained
by `s_p=q−1` for every prime and `k_p=0` except `k_pmax=r−1`. Its single
Newton coordinate survives in every congruent polynomial, proving the
matching lower bound. All dependencies are the formalized integral basis,
its exact length identity, and its ideal-power characterization.

## Lean
- `TorsionNewtonRemainders.lean`: `exists_unique_torsionRemainder`, `length_torsionRemainder_le_of_congruent`, and `exists_bounded_torsion_representative_iff` give the canonical representative and its exact minimum-length property.
- `TheLargestPrimeControlsTorsionInterpolation.lean`: `universal_torsion_interpolation_iff_cutoff` gives the universal cutoff for every finite prime set and every order, including the empty and zero-order cases. `torsionInterpolationIndex` attains the nonempty positive-order threshold.

Both modules passed final plain `lake --old env lean` checks. Transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella imports are wired. The remainder theorem and sharp cutoff count
together as one contribution.
