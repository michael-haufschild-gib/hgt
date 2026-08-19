# Literature capstone formalization plan

- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAM / AUDIT LEDGER
- **Status:** `[LITERATURE] [CORPUS AUDITED] [NO RH CLAIM]`

## Scope and rule

This ledger freezes four published capstones requested for Lean coverage.  A row is closed only
when its literal mathematical statement, rather than a convenient proxy, has an axiom-clean Lean
theorem.  A theorem conditional on a paper-only arithmetic or analytic input is recorded as a
conditional reduction, not as formalization of the cited capstone.

## Ordered work

| Priority | Published capstone | Exact target | Existing Lean coverage | Missing formal work |
|---|---|---|---|---|
| 1 | Deninger, [Theorem 2.13](https://arxiv.org/abs/2204.02714) | No functorial real-valued Weil cohomology satisfying property 2.12, using a quaternionic Artin representation with odd central multiplicity. | `DeningerQ8SymplecticGeneratorRealization.lean` now proves that the explicit `I,K` transitions satisfy the quaternion presentation and preserve a nondegenerate alternating form: the standard two-dimensional symplectic `Q₈` generator realization. `DeningerArtinCentralParityNoGo.lean` formalizes the exact final reduction: root number `-1` makes the central order odd, contradicting equality with an even multiplicity supplied by real symplectic descent. | Formalize the arithmetic witness itself: an explicit finite Galois quaternion field, its Artin representation and root number `-1`; then formalize the real-representation classification which supplies even multiplicity from a real descent, and instantiate property 2.12. The new reduction is conditional on exactly those still-unformalized published inputs, not Theorem 2.13 wholesale. |
| 2 | Connes--van Suijlekom, [Corollary 1.1 and Theorem 1.2](https://arxiv.org/abs/2511.23257) | A rank-`n` PSD Toeplitz `(n+1)`-matrix has a kernel polynomial with all roots on the circle; its distributional continuous simple-even-ground analogue has only real Fourier zeros. | `[LEAN-PROVED]` `CaratheodoryFejerPSDtoAtomicFactorization.lean` gives the reverse same-level finite truncated-Herglotz/Carathéodory--Fejér realization for every normalized Hermitian PSD `T_N`: `exists_atomic_caratheodoryFejer_psd_factorization`. The pre-existing atomic Gram and kernel-root modules provide its factorization-to-root successor. `TruncatedConvolutionOddGroundRealZeros.lean` remains only an odd smooth-kernel analogue. | Extract rank-many/distinct support from the finite atomic realization for the sharp corank-one statement; then build distributions, form closure, lower-bounded self-adjoint realization, and the simple isolated **even** ground required by Theorem 1.2. |
| 3 | Connes--Consani--Moscovici, [Theorem 6.6 and Lemma 5.5](https://arxiv.org/abs/2403.01247) | The literal one-prime Gamma--Euler measure has its finite Jacobi/characteristic data in `Z[1/sqrt 2]` after `q=1/p`; the central-binomial integrality lemma controls the rank-one harmonic coefficients. | `SoninSemilocalFinitePrimeMeasure.lean` formalizes finite-prime Euler-density/moment data. `CCMFiniteSemilocalHarmonic.lean` defines literal `p_ell(m)`. `CCMCentralBinomialIntegrality.lean` proves all three parts of Lemma 5.5. `CCMLambertRadicalIntegrality.lean` proves every complex square root of the literal equation-(53) radicand is an algebraic integer over `Z`. | Formalize the sharper cyclotomic containment of `sqrt (sigma(ell,i) sigma(ell,j))`, then equation (53)'s full Lambert coefficient and the finite characteristic-polynomial `q`-series argument of Theorem 5.6. Algebraic integrality alone does not prove the required cyclotomic-localized coefficient ring. |
| 4 | Burnol, [Theorems 3.1--3.3](https://arxiv.org/abs/math/0203120) | The multiplicity-indexed zeta evaluator systems have the stated aperture-dependent completeness/minimality, closed co-Poisson complement, and critical two-jet correction. | `BurnolCoPoissonRawZeroAnnihilator.lean` proves raw-span annihilation. `BurnolCoPoissonCosineClosedZeroAnnihilator.lean` proves that the literal reciprocal seed realizes every cosine generator, hence raw and cosine-closed source spaces coincide; it transports the annihilation to the full cosine-closed source space. | Formalize literal `L_a`, `K_a`, zero-jet families indexed by actual zeta multiplicity, `Y_a^perp = P_a`, aperture threshold completeness/minimality, and the `a=1` two-jet deletion statement. The closed source-annihilation theorem is not any of these completeness claims. |

## Execution order

1. Build priority 3 first: it is exact finite algebra/analysis, has literal source objects already
   represented, and supplies reusable finite rank-one data rather than a proxy.
2. In parallel in dependency order, build priority 2 finite corank-one Toeplitz theorem before any
   distributional continuous theorem.
3. The finite-dimensional representation-theoretic parity core is now closed in
   `DeningerQuaternionicMultiplicityParity.lean`.  Next build the Q8 Artin witness and
   central-order input; do not claim Deninger's global theorem before those arithmetic inputs are
   formalized.
4. Build priority 4 only on literal Burnol spaces and zero jets; no quotient-density substitution.

## Immediate active claim

`CCMCentralBinomialIntegrality.lean` now proves literal Lemma 5.5(i)--(iii), and
`CCMLambertRadicalIntegrality.lean` proves the square-root factor algebraically integral.  The
next CCM target is genuinely cyclotomic: containment in the cyclotomic integer ring and equation
(53)'s full Lambert coefficient.  In parallel, the Deninger parity spine is closed as described
above.  Neither result assumes RH, a spectral limit, or a numerical calculation.

## 2026-08-19 strict finite CF advance

`[LEAN-PROVED]` `CaratheodoryFejerStrictAtomicFactorization.lean` proves
`exists_atomic_caratheodoryFejer_strict_factorization`: from a normalized Hermitian moment
sequence and a strict positive-definite one-step extension `T_(N+1)`, it constructs exactly
`2*N+1` nonnegative unit-circle atoms whose weighted Vandermonde Gram matrix is `T_N`.
The proof is Bernstein--Szegő probability realization, exact finite circle cubature, Hermitian
moment reconstruction, then the literal `BᴴB` identity.  The theorem is axiom-clean apart from
Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

`[LEAN-PROVED]` `CaratheodoryFejerPSDtoAtomicFactorization.lean` now closes the missing
same-level PSD realization with diagonal strictification, compact weak limit, and exact finite
cubature.  It proves a `2*N+1`-atom factorization for arbitrary normalized Hermitian PSD
`T_N`.  It does **not** yet prove rank-many/distinct support, so the sharp corank-one root
conclusion and the continuous Theorem 1.2 branch remain open.
