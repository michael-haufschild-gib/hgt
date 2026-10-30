# Adams multiplicity and arithmetic length

- **ID:** AHA-JETS
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** ../3-formalized/aha-adams-torsion-resolution.md
- **Statement:** An auxiliary vanishing to full torus order `r` on the order-`d` fixed locus needs integer support reaching `2^(dr)`, with equality attained by `(χ(2)^d−1)^r`.

## Exact coordinates

Write each prime exponent as `v_p(n)=r_p+d k_p`, `0≤r_p<d`.
Near the torsion locus use `Y_p=z_p^d−1`. Then

`z^v = z^r ∏_p (1+Y_p)^(k_p)`.

The coefficient at residue `r` and multiindex `α` is therefore

`J(r,α)=Σ_(v(n)≡r) a_n ∏_p binom(k_p(n),α_p)`.

These are Newton coordinates of the auxiliary. Fourier inversion separates
the residues, and the finite binomial transform detects every nonzero array.
The local maps `z_p↦z_p^d−1` have nonzero derivative at every torsion point
over characteristic zero; their effect on full jets requires a formal bridge.

## Algebraic detection mechanism

Among nonzero coefficients in one residue fibre choose `n` maximizing
`Σ_p k_p(n)`. For `α=k(n)`, a nonzero binomial product from another term
requires `k(m)≥k(n)` coordinatewise. Maximality and equality of sums force
equality of quotient vectors; the residue then forces `m=n`. Thus this coefficient
equals `a_n` and cannot vanish.

If `n<2^(dr)`, unique factorization gives `Σ_p k_p(n)<r`. Hence some Newton
coefficient of order below `r` detects every nonzero auxiliary of that length. The boundary
binomial has order exactly `r` in the coordinate `Y_2`.

## Boundaries

This is a support-length bound. It is not a bound on coefficient height or
integer evaluation size. Full-coordinate jets are essential: one vertical
derivative direction permits cancellations between different prime
coordinates. The analytic mixed-jet identification must be proved, not
folded into the definition of multiplicity.

## Exact differential bridge

For a residue vector `b` represented in `{0,…,d−1}`, let `E_p=z_p ∂/∂z_p`.
The required identity is

`d^|P| d^|α| (∏_p α_p!) J(b,α)`
`= Σ_t conj(χ_b(t)) [∏_p ∏_{0≤j<α_p}(E_p−b_p−dj)] F(t)`.

Fourier averaging kills all residue classes except `b`. In that class,
`v_p=b_p+d k_p`, so the Euler-operator eigenvalue is exactly
`d^α_p α_p! binom(k_p,α_p)`. The differential operator has total order
`|α|`; full torus jets below `r` therefore force every `J(b,α)` below `r`
to vanish. This route proves the needed implication without treating a
Newton coordinate as an analytic derivative by definition.

Existing analytic interface: `HTGeometry/MultivariatePolynomialJetCoefficient.lean`
identifies ordered coordinate derivatives with centered polynomial
coefficients, including factorials. `HTGeometry/MultivariateHermiteCRT.lean`
identifies point-ideal powers with centered coefficient constraints.
The Euler-operator identity is proved in `TorsionEulerJetExtraction.lean`;
ideal multiplicity loss is proved in `EulerOperatorsLowerMultiplicity.lean`.
`MixedJetMultiplicity.lean` identifies ordinary analytic mixed derivatives
with point-ideal powers. The arithmetic application and matching boundary
are being formalized from [AHA-EULER](../2-fully-proven/aha-euler-newton-extraction.md).

`HTGeometry.bgv_coordinateEuler_product` gives the coordinate Euler
eigenvalue on multivariate monomials. `HTGeometry.SparsePolynomial.pow_dvd_euler`
proves the one-variable multiplicity drop; the required extension is to
powers of multivariate point ideals.

## Positive survivor

The algebraic survivor is exact weighted torsion sampling below the arithmetic
degree threshold. It is formalized in
[AHA-NEWTON](../3-formalized/aha-residue-newton-resolution.md):
`arithmeticNewton_sample_recovery` and `arithmeticNewton_samples_eq_iff`,
in namespace `GaloisForLFunctions.ArithmeticHarmonicAnalysis`, have only
standard Lean axioms. The Euler extraction and mixed-jet bridge now connect
this survivor to ordinary multiplicity; their arithmetic application awaits
its final audit.

The classical multiplicity bound is not claimed as new number theory:
[Dvir–Kopparty–Saraf–Sudan, Lemma 8](https://www.math.toronto.edu/swastik/multiplicities.pdf)
bounds the sum of grid multiplicities by total degree times the appropriate
grid cardinality. The arithmetic contribution sought here is its exact
support filtration and constructive residue interface.
