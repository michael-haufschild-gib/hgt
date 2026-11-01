# Algebraic-dilation independence over theta–Gamma coefficients

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [rational-dilation independence](../3-formalized/rational-dilation-theta-gamma-independence.md).

## Target

All actual functions `ζ(rs)`, indexed by positive real algebraic `r`, are
jointly differentially algebraically independent over
`ℂ(s)⟨Γ,θ₂,θ₃,θ₄,E₂⟩` in the common upper-end meromorphic field.
This would extend the differential–Mahler obstruction to every positive
algebraic multiplier `q≠1`; `q=1` repeats the same coordinate.

## Certified inputs

1. **Prime-jet separation.**
   `ArithmeticHarmonicAnalysis/PositiveDilationPrimeJetSeparation.lean`
   proves cofinite prime-jet independence for every finite packet of distinct
   positive **real** dilations. Its
   `multilinearMap_eq_zero_of_distinct_primeJets` detects arbitrary multilinear
   forms using distinct primes outside any finite exclusion set.

2. **Exact algebraic frequency collisions.**
   `ArithmeticHarmonicAnalysis/AlgebraicPrimeFrequencyRigidity.lean`
   proves that a frequency on `D` distinct primes with positive algebraic
   weights has no representation by fewer prime terms. Every representation
   with at most `D` terms permutes the same prime–weight pairs
   (`primeLog_short_representation`, `atom_tuple_frequency_iff`).
   Baker independence balances weights prime by prime; positivity identifies
   supports, and cardinality forces one term per prime.

3. **Actual analytic coefficients.**
   `ArithmeticHarmonicAnalysis/DilatedVonMangoldtJets.lean` proves, for
   `F_r(s)=−r ζ'(rs)/ζ(rs)` and `rσ>1`, the absolutely convergent expansion

   ```text
   F_r^(k)(σ+it) = Σ_p Σ_(m≥1)
     r (−mr)^k (log p)^(k+1) exp(−σmr log p) exp(−itmr log p).
   ```

   `source_jet_line_eq_expSeries`, `summable_norm_primeAmplitude`, and
   `primeAmplitude_eq` identify the literal jets, their summability, and their
   exact coefficients. Prime-power reindexing is explicit.

4. **Coefficient-preserving polarization.**
   `ArithmeticHarmonicAnalysis/DilationPolynomialPolarization.lean`
   constructs the symmetric multilinear form of each homogeneous component.
   Its diagonal is the component times the nonzero permutation count;
   `polynomialMultilinear_ne_zero` preserves every nonzero supported coefficient,
   including degree zero.

5. **Exact top-degree frequency fibers.**
   `ArithmeticHarmonicAnalysis/AlgebraicPrimeFrequencyFibers.lean` proves
   that shorter tuples have zero coefficient at a distinct-prime target;
   equal-length fibers are exactly finite permutation sums. No convergence
   assumption is required for these finite-fiber identities.

6. **Actual common-atom expansion.**
   `ArithmeticHarmonicAnalysis/AlgebraicDilationAtoms.lean` embeds every
   prime-power series into atoms `(p,α)` with positive algebraic `α`, preserving
   absolute summability and the literal analytic jets. At `(p,r_j)`,
   `atomAmplitude_eq_primeJet` gives the normalized prime-jet row times
   `log(p) exp(−σr_j log p)`, which is nonzero. Positive-integer incidence
   between dilation parameters is retained exactly.

7. **Exact polynomial coefficient extraction.**
   `ArithmeticHarmonicAnalysis/AlgebraicDilationPolynomialCoefficients.lean`
   expands every finite polynomial as one absolutely convergent exponential
   series. At a frequency on `D` distinct primes, with every supported monomial
   of degree at most `D`, `polynomial_fiber` identifies its coefficient with
   the degree-`D` symmetric multilinear form. A vanishing relation annihilates
   that form on every distinct-prime atom packet.

All seven modules have direct production checks and umbrella imports.
Their 48 public axiom audits use only the standard three axioms.
These inputs do not yet prove joint independence of the analytic functions.

## Remaining bridge

Combine the certified top-degree coefficient identity with the nonzero decay
factors and prime-jet separation. A nonzero polynomial relation of maximal
degree `D` would force its symmetric degree-`D` form to vanish identically,
contradicting `polynomialMultilinear_ne_zero`. This final actual jet-independence
bridge is drafted but not yet certified. The argument retains frequency
collisions and requires only absolute convergence of the actual line series.

After actual jet independence, pass through rotated right-half-plane germs.
`CoordinatewiseDifferentialFamilyMatroid.differentialIndependent_deriv_div_self_iff`
transfers independence to the actual zeta dilates. Recover physical zeta-jet
independence by analytic continuation, then apply physical Gamma separation
and theta differential-algebraic base change. Rotation factors remain
explicit; Gamma stays in the physical variable. Logarithmic derivatives
cannot themselves serve as analytic representatives in the upper half-plane.

The full target and stronger Mahler exclusion remain unproved. Special-value
relations and other nonlinear realizations remain outside this conjecture.
