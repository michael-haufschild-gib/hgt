# Factorial--harmonic sequence freeness at Gamma poles

- **ID:** `gamma-factorial-harmonic-sequence-freeness`
- **Stage:** 3-formalized
- **Type:** STRUCTURAL THEOREM
- **Scientific status:** `[PROVED] [FORMALIZED] [NOVELTY UNVERIFIED]`
- **Lean modules:**
  - `formal/GaloisForLFunctions/HTGeometry/GammaFactorialHarmonicSequenceFreeness.lean`
  - `formal/GaloisForLFunctions/HTGeometry/GammaPoleFormalGermFreeness.lean`

## Theorem

Let `Germ_infinity(C^N)` be the ring of complex sequence germs modulo eventual equality.  Put

\[
  J_{j,n}=(-1)^j j!\,H_{n-1}^{(j+1)},
  \qquad
  t_n=\frac{(-1)^{n-1}}{(n-1)!}.
\]

For every finite `m`, the family `J_0,...,J_(m-1)` is algebraically independent over
`C(N)`, and `t` is transcendental over the resulting polynomial ring.  More generally, for
arbitrary constants `alpha_j,beta_j in C` with every `alpha_j != 0`, the sequence germs

\[
  t^{j+1}(\alpha_jJ_j+\beta_j), \qquad 0\le j<m,
\]

are algebraically independent over `C`.

The exact coefficient formula for the logarithm of the factorially rescaled Gamma pole family is
the specialization

\[
  c_j=t^{j+1}\left(-\frac{J_j}{(j+1)!}+\beta_j\right),
\]

where `beta_0` is Euler's constant and
`beta_j=zeta(j+1)/(j+1)` for `j>=1`.  Hence the countable family `(c_j)_(j>=0)` is
algebraically independent.

If `lambda_j=(j+1)!c_j` and `B_k` denotes the complete exponential Bell polynomial, then the
regular coefficients

\[
  r_j=-\frac{1}{(j+1)!}B_{j+1}(\lambda_0,\ldots,\lambda_j)
\]

also form a countably algebraically independent family.  Therefore the formal power series
`R(X)=sum_j r_j X^j` satisfies no nonzero finite-order algebraic differential equation over
`C[X]`.

## Proof mechanism

1. Evaluation on natural numbers embeds `C(X)` into the eventual sequence ring.  A nonzero
   polynomial has only finitely many natural zeros, so every localization denominator becomes a
   unit and the rational evaluation map is injective.
2. Sequence shift sends `J_j` to `J_j+(-1)^j j!/X^(j+1)`.  The kernel of harmonic evaluation is
   therefore a shift-stable ideal.  `no_shift_stable_annihilator` forces this kernel to vanish.
3. The factorial square obeys `sigma(t^(-2))=X^2t^(-2)`.  A least-degree polynomial relation and
   its shift have cancelling leading terms.  Any surviving lower coefficient yields the forbidden
   rational eigenrelation excluded by `no_shift_eigenrelation`.  Squaring and inversion transfer
   transcendence to `t`.
4. Weighting affine harmonic coordinates by distinct positive powers of `t` is injective: evaluate
   the factorial variable at one, where the substitution becomes an invertible affine coordinate
   map.
5. `exists_bellAt_solution` makes the finite Bell value map surjective.  Therefore Bell
   substitution on the polynomial algebra is injective.  This transports algebraic independence
   from the logarithmic derivatives to the regular coefficients.
6. `aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent` converts coefficient freeness into
   all-order formal differential separation.

## Formal declarations

- `harmonicJetEval_injective`
- `factorialSquareEval_injective`
- `reciprocalSignedFactorialEval_injective`
- `algebraicIndependent_weightedAffineGerm`
- `algebraicIndependent_gammaPoleLogCoefficientGerm`
- `bellCoefficientMap_injective`
- `algebraicIndependent_gammaPoleRegularCoefficientGerm`
- `gammaPoleRegularFormalGerm_formallyHypertranscendental`

The headline declarations have axiom set
`[propext, Classical.choice, Quot.sound]`.

## Boundary and remaining open core

This theorem is not yet promoted to new scientific knowledge.  Ablinger--Schneider prove broad
algebraic-independence results for harmonic-sum sequences over rational sequence rings; the exact
parent-theory comparison for the factorial adjunction and weighted Bell specialization still needs
independent literature review.

The Lean theorem treats the displayed exact Gamma coefficient formulas as definitions.  The
analytic/formal-power-series identity identifying them with the coefficients of

\[
  \Gamma\!\left(-n+\frac{(-1)^{n+1}}{n!}X\right)+\frac1X
\]

is not yet formalized.  That source-identification and the resulting composition-depth descent
remain in `gamma-pole-germ-harmonic-versal-deformation.md`.

## Gates

- [x] 0 -> 1: exact shift laws and falsifiers isolated
- [x] 1 -> 2: sequence-germ, factorial, weighted-affine, and Bell proofs complete
- [x] 2 -> 3: Lean declarations compile with touched-file checks and axiom audit
- [ ] 3 -> 4: primary-source novelty audit and independent expert review
