# ArithmeticHarmonicAnalysis

Namespace `GaloisForLFunctions.ArithmeticHarmonicAnalysis`; umbrella `ArithmeticHarmonicAnalysis.lean`; 16 modules.
All results unconditional; several modules end with `#print axioms`.

## 1. Motivation

Stepanov's method over F_q builds an auxiliary polynomial vanishing to high order at the points fixed by
Frobenius x^q = x. Over ℤ the analogue of those points is the fixed locus of an Adams operation ψ^{q+1} on the
gauge torus (finite-order twists). The programme measures exactly what vanishing on such loci costs an
arithmetic auxiliary Σ c_n χ(n): in support length, in multiplicity, and in which derivatives count. It also
quantifies how additive (successor) observations reconstruct multiplicative phases. The answer is a sharp
support law: multiplicity r on the order-q torsion locus forces support ≥ 2^{qr}, attained by (z₂^q − 1)^r.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Torsion phase / polynomial | `torsionPhase`, `torsionPolynomial` | characters on (ZMod q)^ι; finite sums Σ c_n·phase(e_n) |
| Residue fibre sum | `residueCoefficient` | Σ of c_n with frequency ≡ r |
| Valuation residue / quotient | `valuationResidue`, `valuationQuotient` | v_p(n) mod q; ⌊v_p(n)/q⌋ |
| Short primes | `shortPrimes q` | primes below 2^q |
| Embedded grid | `torsionGauge` | torsion grid inside the gauge torus; ψ^{q+1}-fixed |
| Newton coefficient | `residueNewtonCoefficient`, `newtonOrder`, `newtonDegree` | Σ_{residue b} c·∏C(k_i, a_i) |
| Arithmetic Newton data | `arithmeticNewtonEmbedding`, `arithmeticNewtonArray`, `arithmeticNewtonSample` | (residue, quotient) encoding of n < 2^{qr} |
| Euler operators | `shiftedCoordinateEuler`, `shiftedEulerWord`, `newtonEulerWord`, `eulerWordWeight` | X_i∂_i − s and words of them |
| Auxiliary polynomial | `arithmeticAuxiliaryPolynomial`, `finiteMonomialPolynomial` | Σ c_n ∏ X_p^{v_p(n)} |
| Boundary auxiliary | `torsionBoundaryPolynomial q r` | (X^q − 1)^r |
| Log-flow trace | `primeLogTrace`, `primeLogEuler` | F(x_p p^s); Σ log p·X_p∂_p |
| Successor defect | `successorDefect`, `successorRadius` | χ(n+1) − χ(n); max over n < N |

External: `GaugeTorus`, `twist`, `twistSum` (ArithmeticCorrelationGeometry); `adams`, `IsAdamsFixed`
(ArithmeticGaugeTheory); `HTGeometry.multiIndexJetEvalCLM`; `friableExponentDirichletExp` (RHTower).

## 3. Language

- **Torsion resolution**: order-q grid reads valuations mod q (power classes), not residues mod q (congruences).
- **Full multiplicity r**: membership in the r-th power of the point ideal = all mixed derivatives of order < r vanish.
- **Vertical jet**: derivative along the logarithmic flow s ↦ (x_p p^s); **transverse**: individual coordinates.
- **Support threshold**: least integer support a nonzero auxiliary with the prescribed vanishing can have.

## 4. Mechanisms

1. Finite Fourier inversion on (ZMod q)^P recovers residue fibre sums; vanishing on the grid ⇔ fibre cancellation;
   Parseval in fibre sums.
2. Unique factorization: n < 2^q ⇒ all v_p(n) < q ⇒ no collisions; first collision 2^q ≡ 1.
3. Residue + q·quotient encoding is injective; n < 2^{qr} ⇒ quotient total order < r (2^{q|k|} ≤ n).
4. Newton triangularity: maximal-order monomial read unchanged ⇒ orders ≤ degree detect.
5. Euler words act diagonally on monomials; on residue b the weight is q^{|a|}∏a_i!∏C(e_i/q, a_i) (falling
   factorials). Fourier averaging extracts Newton coefficients.
6. Leibniz: a derivation lowers ideal powers by ≤ 1, so a word of length k keeps multiplicity r − k.
7. Centered Taylor coefficients = point-ideal powers = analytic mixed jets.
8. (X^q − 1) separable ⇒ multiplicity exactly r at each root for (X^q − 1)^r.
9. Baker / Gelfond–Schneider: algebraic data ⇒ first vertical jet detects all partials; homogeneous two-prime log
   monomials independent.
10. Multiplicative halving: n ↦ ⌊n/2⌋ with one successor step per bit ⇒ logarithmic reconstruction loss.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Torsion Fourier inversion and Parseval with collisions | `torsion_coefficient_recovery`, `torsion_parseval`, `torsionPolynomial_vanishes_iff` | proved |
| Short auxiliaries (< 2^q) vanish on grid ⇔ zero; 2^q collides with 1 | `short_torsion_vanishing_iff`, `valuationResidue_two_pow` | proved |
| Same on the ψ^{q+1}-fixed locus; χ(2^q) − 1 boundary | `short_adams_auxiliary_vanishes_iff`, `adams_boundary_binomial` | proved |
| Newton detection by orders ≤ degree | `residueNewton_vanishing_iff` | proved |
| Orders < r detect support < 2^{qr} | `arithmeticNewton_vanishing_iff`, `arithmeticNewton_samples_eq_iff` | proved |
| Fourier extraction of Euler jets | `newtonEuler_fourier_extraction`, `arithmeticAuxiliary_euler_recovery` | proved |
| Multiplicity r on grid ⇔ zero (support < 2^{qr}); analytic-jet and Adams-locus forms | `arithmeticAuxiliary_multiplicity_vanishes_iff`, `short_adams_mixedJets_vanishes_iff` | proved |
| Sharpness: (X^q − 1)^r reaches 2^{qr} with multiplicity r | `torsionBoundaryArithmeticSupport_max`, `torsionBoundaryPolynomial_rootMultiplicity` | proved |
| Vertical jets miss transverse directions (real-log coefficients) | `verticalFlatTrace_derivative`, `verticalFlatAuxiliary_transverse_jet` | proved |
| Algebraic data: first vertical jet ⇔ all partials | `algebraic_primeLogTrace_firstJets_vanish_iff` | proved |
| Homogeneous two-prime log forms independent | `twoPrimeLog_homogeneous_algClosure_linearIndependent` | proved |
| Point multiplicity ⇒ scalar log-jets vanish | `iteratedDeriv_primeLogTrace_eq_zero_of_mem_pointIdeal_pow` | proved |
| Scalar jets below support size detect prime-exponent auxiliaries | `friableExponentDirichletExp_initial_jets_zero_iff` | proved |
| Dyadic successor reconstruction, zero-defect fibre | `norm_twist_sub_one_le_dyadic_radius`, `successorRadius_eq_zero_iff_prime` | proved |
| Auxiliary beating the divisibility (support) cost | — | open |

## 6. Tools

**Developed**
- Torsion Fourier / Newton / Euler-jet extraction pipeline from coefficients to multiplicity.
- Point-ideal ↔ mixed-jet dictionary for prime-coordinate polynomials.
- Algebraic vertical-jet faithfulness at first order (Baker) and its higher-order Leibniz transport.
- Dyadic successor-defect reconstruction metric on the gauge torus.

**To build**
- Higher-order vertical-jet faithfulness for algebraic data (needs independence beyond homogeneous degree).
- Classification of minimum-support auxiliaries (rigidity at 2^{qr}).
- Coefficient-height and evaluation-size costs (support law says nothing about them).
- A coupling of successor constraints with Adams vanishing that improves the support cost.

## 7. Open questions

1. Can additive (successor) constraints lower the 2^{qr} support cost of multiplicity r on Adams loci?
2. Are all auxiliaries of support exactly 2^{qr} with multiplicity r equivalent to (z₂^q − 1)^r?
3. For algebraic data, do vertical jets of order < r detect full multiplicity r?
4. What height/size bound accompanies the support law, and does it beat the divisibility ledger?
5. Which quantitative successor observations determine a gauge point beyond the prime cutoff N?

## 8. Traps

| Trap | Fact |
|---|---|
| Torsion order = conductor | Order-q torsion reads v_p mod q; conductor reads n mod Q |
| Root-of-unity vanishing gives multiplicity for free | Multiplicity r costs support 2^{qr}, sharp |
| Vertical vanishing = torus multiplicity | False with real-log coefficients; true at first order only for algebraic data |
| Small successor defects determine the point | Primes above the cutoff N remain free |
| Algebraic uniqueness of fixed points gives cancellation | Fixed-locus vanishing is an algebraic support law, not an exponent bound |
| Homogeneous independence ⇒ algebraic independence of log p, log q | Only fixed-degree relations are excluded |

## 9. Context

**Uses** (import counts): HTGeometry 5, RHTower 3, ArithmeticCorrelationGeometry 2, ArithmeticGaugeTheory 1.

**Used by**: `MainTheorems` only.

| Neighbour | Relation |
|---|---|
| ArithmeticGaugeTheory | Adams operations and fixed points; this programme computes vanishing costs on those loci |
| ArithmeticCorrelationGeometry | Gauge torus, twists, gauge invariance of multiplicative observation |
| HTGeometry | Multivariate jets, Euler product identity, transcendental power independence, root multiplicity |
| RHTower | Gelfond–Schneider, Baker-type prime-log independence, exponential-sum zero estimates |
| RenormalizedArithmeticPotentialTheory | Single-prime flip thresholds (`TheFlipThresholdGrowsLikeAPowerOfThePrime`) give the overlap-side resolution analogue |

## 10. Big picture

The programme tests whether a Stepanov-type auxiliary can exist over ℤ by computing its exact price. The
answer is rigid: vanishing to order r on the natural torsion analogue of the Frobenius-fixed points forces the
auxiliary to reach integer support 2^{qr}, and a trivial polynomial already attains this. Unique factorization
is both the reason the cost is finite and the reason it cannot be beaten by torsion data alone.

For the RH effort this closes off the most direct transplant of the finite-field proof: multiplicity bought on
Adams loci is paid for exactly in support length, with no gain. Any gain must come from coupling the additive
structure (successor relations, which reconstruct phases only logarithmically and only below a cutoff) with
the multiplicative one, or from analytic jets along the logarithmic flow, where transcendence theory controls
first-order data but not yet higher orders.
