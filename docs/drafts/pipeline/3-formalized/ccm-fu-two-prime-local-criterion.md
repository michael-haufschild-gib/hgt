# CCM-FU: sharp local two-prime criterion and bounded obstruction transport

- **Stage:** 3-formalized
- **Parent:** [source-local two-prime candidate](../1-in-progress/ccm-fu-two-prime-local-blocks.md)
- **Type:** exact arithmetic block decomposition and sharp comparison class
- **Boundary:** the actual all-cutoff unit-channel comparison remains open; no two-prime ceiling or RH proof is claimed.

## Closed mathematical statements

Every original oriented prime-label fibre is exactly the unsigned channel at the product of its primes. Splitting the original prime cube with respect to p,q therefore gives all its four-coefficient cofactor blocks, with no source term omitted. Processing p,q replaces each nonnegative block a,b,c,e by its alternating sum a-b-c+e.

If b,c<=2a and e<=2b,2c, then `e<=b+c` and `bc<=a(b+c)`. Put x=b+c. For a<=x, the cross reserve is `ax-bc+e(x-a)>=0`. For x<=a it is `(a-x)(x-e)+x^2-bc>=0`. Hence `(a-b-c+e)^2<=a^2+b^2+c^2+e^2`. The uniform factor two is sharp: at any kappa>2, the block `(1,kappa,kappa,0)` satisfies the factor-kappa edge comparisons but has square excess `2 kappa (kappa-2)>0`. This class boundary is proved for every real factor, not by a numerical counterexample.

Exact clipped homothety uses the same nonnegative weights for parent and child. A comparison `K_p(N)<=kappa K_1(N)` at the two adjacent quotient cutoffs transfers to `K_(pd)(M)<=kappa K_d(M)`. The universal dilation comparison is therefore equivalent to its unit-cofactor restriction, including zero and clipped channels.

The resulting actual-source theorem is an unconditional alternative for any distinct primes p,q<M:

`Q_{p,q}(M)<=Q_empty(M)`, or there exist r in {p,q} and `r<N<=M` such that `2 K_1(N)<K_r(N)`.

For cofactor one the comparison uses the original cutoff directly. For every larger positive cofactor, both interpolation endpoints are no larger than M. A violating channel must be active, which supplies r<N. Thus a two-prime failure cannot hide at a later cutoff or a different prime. This localizes the missing arithmetic comparison; it does not prove that the second alternative is absent. Controlling two initial mergers also leaves the complete growing schedule and final SD1 comparison open.

## Lean certificate

`RHTower.MobiusDivisorTwoPrimeLocalCriterion` contains eight public theorems. Its source statements include `mobiusDivisorOrientedFibre_empty_eq_unsigned_product`, both exact two-prime energy decompositions, `divisorUnsignedDilation_comparison_iff_unit`, and `mobiusDivisorSelectionEnergy_two_primes_le_or_unit_failure`. The final alternative has no unproved arithmetic premise. The local comparison class is characterized by `nonnegative_two_coordinate_factor_iff`.

The complete scratch proof and exact leaf/olean check passed with `lake env lean`, using existing dependencies. The module is wired once in `RHTower.lean`; no full, dependency or umbrella build was run. All eight new public declarations were axiom-audited once and use only `propext`, `Classical.choice` and `Quot.sound`. The literal source formulas are retained throughout; computations supply no Lean premise.

Global formal lint reports one unrelated concurrent wiring error: `RHTower.ThetaCuspNativeTwelfthJetLimit` is unreachable from its umbrella. It reports no error for this new CCM-FU leaf. This invocation does not establish a passing global lint gate.
