# Adams multiplicity and arithmetic length

- **ID:** AHA-JETS
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** aha-adams-torsion-resolution.md
- **Statement:** A nonzero auxiliary vanishing to full prime-coordinate order `r` on the order-`d` Adams fixed locus must reach integer support `2^(dr)`. The integer auxiliary `(χ(2)^d−1)^r` attains this threshold.

## Exact meaning

For `d,r≥1`, put `P={primes below 2^(dr)}` and
`F(z)=Σ_(0<n<2^(dr)) c_n ∏_(p∈P) z_p^v_p(n)`, with `c_n∈ℂ`.
Evaluation at `z_p=χ_x(p)` equals the original sum `Σ_n c_n χ_x(n)`.
Vanishing of every ordinary complex mixed derivative of total order below
`r` at every `ψ^(d+1)` fixed point is equivalent to `c_n=0` for every `n`.

## Proof

Write `v_p(n)=b_p+d k_p(n)`, `0≤b_p<d`. Unique factorization gives
`2^(d Σ_p k_p(n))≤n`, hence `Σ_p k_p(n)<r` on the stated support.
The residue Newton coefficients are

`J(b,α)=Σ_(v(n)≡b) c_n ∏_p binom(k_p(n),α_p)`.

In a nonzero residue fibre, choose a quotient vector of maximal total
degree. Its own Newton coefficient detects it: a nonzero binomial factor
requires componentwise domination; maximality forces equality.

The shifted Euler word `∏_p∏_(j<α_p)(z_p∂_p−b_p−dj)` has order `|α|`.
Fourier averaging on the torsion grid recovers `J(b,α)` multiplied by
the nonzero scalar `d^(|P|+|α|)∏_p α_p!`.
[AHA-EULER](aha-euler-newton-extraction.md) proves this identity and
the required ideal-multiplicity loss. Full multiplicity `r` therefore
kills all detecting Newton coordinates. Centered Taylor coefficients,
with their nonzero factorials, identify ideal multiplicity with analytic
mixed jets. Embedded torsion gauges realize every point of the grid.

The boundary polynomial `(X^d−1)^r` has integer coefficients, leading
coefficient one and degree `dr`. Its roots have exact multiplicity `r`
because `X^d−1` is separable in characteristic zero. Reading exponent
`j` as the integer `2^j` gives largest support integer exactly `2^(dr)`.

## Scope and provenance

This sharp support law gives no coefficient-height gain. Arbitrary complex
coefficients can cancel along a single logarithmic direction; the
algebraic-coefficient vertical-jet question needs a separate analysis.

The grid multiplicity bound is classical:
[Dvir–Kopparty–Saraf–Sudan, Lemma 8](https://www.math.toronto.edu/swastik/multiplicities.pdf).
The contribution here is its exact arithmetic support filtration, explicit
Euler–Fourier extraction, and identification on actual Adams fixed points.

## Lean closure

Namespace `GaloisForLFunctions.ArithmeticHarmonicAnalysis`:

| Statement | Declaration |
|---|---|
| Original twist evaluation | `arithmeticAuxiliaryPolynomial_eval_twist` |
| Exact Newton recovery | `arithmeticAuxiliary_euler_recovery` |
| Point-ideal multiplicity | `arithmeticAuxiliary_multiplicity_vanishes_iff` |
| Ordinary mixed jets | `arithmeticAuxiliary_mixedJets_vanishes_iff` |
| Actual Adams fixed locus | `short_adams_mixedJets_vanishes_iff` |
| Integral boundary and support | `torsionBoundaryPolynomial_integral`, `torsionBoundaryArithmeticSupport_max` |
| Exact boundary multiplicity | `torsionBoundaryPolynomial_rootMultiplicity`, `torsionBoundary_mem_pointIdeal_pow` |

Modules `AdamsMultiplicityResolution.lean` and
`TorsionMultiplicityBoundary.lean` passed final `lake --old env lean`
audits. Transitive axiom checks contain only `propext`, `Classical.choice`,
`Quot.sound`. The three differential-interface leaves have the same audit.
