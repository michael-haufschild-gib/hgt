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
| 1 | Deninger, [Theorem 2.13](https://arxiv.org/abs/2204.02714) | No functorial real-valued Weil cohomology satisfying property 2.12, using a quaternionic Artin representation with odd central multiplicity. | `DeningerArithmeticQuaternionicTransitionNoReal.lean` proves one explicit two-dimensional quaternionic transition atom has no equivariant real reduction.  `DeningerQuaternionicMultiplicityParity.lean` now proves the exact finite-dimensional parity spine: an anti-linear square-`-1` matrix forces even complex dimension. | Formalize the exact Artin/Q8 witness: a finite Galois field, its symplectic irreducible representation, root number `-1`, functional-equation odd central order, and property-2.12 identification.  The completed parity core plus local atom are still not Theorem 2.13. |
| 2 | Connes--van Suijlekom, [Corollary 1.1 and Theorem 1.2](https://arxiv.org/abs/2511.23257) | A rank-`n` PSD Toeplitz `(n+1)`-matrix has a kernel polynomial with all roots on the circle; its distributional continuous simple-even-ground analogue has only real Fourier zeros. | `CaratheodoryFejerLineReality.lean` proves the positive-definite OPUC/paraorthogonal Cayley connector. `CaratheodoryFejerAtomicKernelRoots.lean` now proves the entire post-factorization chain: zero weighted positive atomic energy forces every atomic kernel evaluation to vanish, then distinct unit-circle atoms give the exact root multiset and unit-circle conclusion. `TruncatedConvolutionOddGroundRealZeros.lean` proves an odd smooth-kernel analogue, not the published even distributional theorem. | Build the PSD-corank-one Carathéodory--Fejér factorization and derive its actual zero weighted energy for a kernel vector. Then build distributions, form closure, lower-bounded self-adjoint realization, and the simple isolated **even** ground required by Theorem 1.2. Neither proxy may be relabelled as the theorem. |
| 3 | Connes--Consani--Moscovici, [Theorem 6.6 and Lemma 5.5](https://arxiv.org/abs/2403.01247) | The literal one-prime Gamma--Euler measure has its finite Jacobi/characteristic data in `Z[1/sqrt 2]` after `q=1/p`; the central-binomial integrality lemma controls the rank-one harmonic coefficients. | The actual finite-prime Euler-density integral, termwise Poisson expansion, all-even Jacobi moments, strict signs, and normalized moment identity are formalized in `SoninSemilocalFinitePrimeMeasure.lean`. `CCMFiniteSemilocalHarmonic.lean` now defines the literal `p_ell(m)`, proves symmetric common finite support and normalization, and proves the exact reduction Lemma 5.5(ii) ⇒ (iii). | Formalize Lemma 5.5(i), its termwise lift to (ii), rank-one Lambert matrix coefficients, and the finite characteristic-polynomial `q`-series integrality. The all-even moment theorem is already closed; do not duplicate it. |
| 4 | Burnol, [Theorems 3.1--3.3](https://arxiv.org/abs/math/0203120) | The multiplicity-indexed zeta evaluator systems have the stated aperture-dependent completeness/minimality, closed co-Poisson complement, and critical two-jet correction. | `BurnolCoPoissonBerezinFaithful.lean` proves density of completed-Mellin kernels on the constructed co-Poisson quotient. `BurnolCoPoissonRawZeroAnnihilator.lean` now proves that every right-half-strip zeta-zero Riesz evaluator annihilates the **closed raw span** of all literal co-Poisson source vectors, using the general-source Mellin factorization. Prime-window completion and divided-jet transport are also formalized. | Extend that annihilation from the raw source span to the cosine-closed source space; then formalize literal `L_a`, `K_a`, zero-jet families indexed by actual zeta multiplicity, `Y_a^perp = P_a`, aperture threshold completeness/minimality, and the `a=1` two-jet deletion statement. The raw result is not the full theorem. |

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

`CCMFiniteSemilocalHarmonic.lean` now defines the literal finite harmonic coefficient
`p_ell(m)` and proves its symmetry and exact finite support.  The next finite CCM target is the
central-binomial integrality bridge of Lemma 5.5, then the rank-one Lambert coefficient needed for
the finite semilocal characteristic polynomial.  In parallel, the Deninger parity spine is closed
as described above.  Neither result assumes RH, a spectral limit, or a numerical calculation.
