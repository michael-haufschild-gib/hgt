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
| 1 | Deninger, [Theorem 2.13](https://arxiv.org/abs/2204.02714) | No functorial real-valued Weil cohomology satisfying property 2.12, using a quaternionic Artin representation with odd central multiplicity. | `[LEAN-PROVED]` `DeningerQ8ActualGroupRepresentation.lean` upgrades the earlier generator calculation to a literal `QuaternionGroup 2 →* Module.End ℂ (ℂ × ℂ)`: full action law, `a 1 = I`, `xa 0 = K`, central `a 2 = -1`, and preservation of the nondegenerate alternating form. `DeningerArtinCentralParityNoGo.lean` formalizes the final parity contradiction conditional on root number and descent inputs. | Formalize the arithmetic witness itself: an explicit finite Galois quaternion field, its Artin representation and root number `-1`; then formalize the real-representation classification which supplies even multiplicity from a real descent, and instantiate property 2.12. The new representation is the finite group-theoretic Artin shape, not a number-field or root-number realization. |
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

## 2026-08-19 Q8 and finite Toeplitz advances

`[LEAN-PROVED]` `DeningerQ8ActualGroupRepresentation.lean` is an axiom-clean literal group
representation, rather than a pair of matrices merely satisfying presentation relations.  The
only axioms printed are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

`[LEAN-PROVED]` `CaratheodoryFejerPSDtoAtomicFactorization.lean` now supplies same-level PSD
Toeplitz realization and `2*N+1` atomic factorization.  It removes the former one-step-extension
assumption but does not supply the rank-sharp support extraction needed by the cited corank-one
root theorem.

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

## 2026-08-19 Burnol completed zero-jet advance

`[LEAN-PROVED]` `BurnolCoPoissonCompletedZeroJets.lean` transfers exact zero multiplicity through
the literal Gamma-completed Mellin evaluation of every positive logarithmic co-Poisson subwindow.
For each actual Xi divisor it proves all lower jets vanish and the leading jet is nonzero.  The
proof uses equality with the co-Poisson formula on an open strip plus locality of iterated
derivatives, so it does not postulate differentiation under an improper integral.

This does **not** close Burnol’s Theorems 3.1–3.3.  The remaining literal work is the bounded
zero-jet evaluator family on all `L_a`, closure/complement equality with `P_a`, the aperture
thresholds, projection to `K_a`, and the `a = 1` two-jet deletion theorem.

## 2026-08-19 Q8 Artin-Galois advance

`[LEAN-PROVED]` `DeningerQ8ArtinGaloisRealization.lean` transports the literal Q8 action through
any field-Galois identification `G ≃ Q8`.  It proves the degree-eight extension, the
degree-two symplectic Artin representation, central scalar `-1`, and, for number fields, the
instantiated finite-place Artin Euler product is holomorphic and nonzero in `Re(s) > 1`.

This is not a construction of a Q8 number field, an analytic continuation, or the required global
root-number `-1`; those remain the exact Deninger core.

## 2026-08-19 finite Carathéodory--Fejér rank bridge — paper proof

`[PAPER-PROVED]` Let `T = circleToeplitzGram N c` be normalized, Hermitian and PSD, with
`rank(T) = N`, and let a nonzero kernel vector define `P`.  The existing same-level atomic
factorization gives `T = B^* B` with finitely many nonnegative circle atoms.  Let `S` be the
**distinct** nodes having positive weight.  Every row of `B` belongs to the span of the
Vandermonde rows indexed by `S`; therefore
`N = rank(T) = rank(B) ≤ #S`.  The kernel equation gives `P(z)=0` for every `z ∈ S`, while
`deg(P) ≤ N`.  Thus `deg(P) ≤ #S`, and the exact polynomial root-cardinality theorem forces
`P.roots = S` (with multiplicity one).  Consequently every root of `P` is one of the unit-circle
atoms.  No spectral, RH, or extension hypothesis is used.

This closes precisely the finite normalized corank-one statement.  It is not the continuous
distributional theorem, and normalization still has to be removed separately to state the paper’s
arbitrary nonzero-diagonal form.

`[LEAN-PROVED]` The paper proof is formalized in
`CaratheodoryFejerRankCorankOne.lean` as
`circleToeplitzGram_kernel_polynomial_roots_on_unitCircle_of_rank_eq`.  Its supporting theorem
`caratheodoryFejerAtomicFactor_rank_le_activeNodeCard` is the exact rank-to-distinct-support
extraction, and `caratheodoryFejerAtomicGram_kernel_eval_eq_zero_of_pos` removes an avoidable
all-weights-strictly-positive assumption.  The leaf `lake env lean`, targeted `lake build`, and
axiom audit passed; axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

## 2026-08-19 explicit Q8 radical certificate

`[PAPER-PROVED]` Put `r=2+x` and `u=z²`, with `x²=2`, `y²=3`, and
`z²=(2+x)(3+y)`. First `r²-4r+2=0`. Taking the quadratic norm in `y` gives
`u²-6ru+6r²=0`, hence `r(24-6u)=12-u²`. Squaring this identity and using the
quadratic equation for `r` yields `u⁴-24u³+144u²-288u+144=0`; substituting
`u=z²` is the standard degree-eight eliminant.

`[LEAN-PROVED]` `DeningerQ8ExplicitRadicalPolynomial.lean` proves this identity as
`deningerQ8_explicitRadicalPolynomial_eq_zero` over every commutative ring. It is an algebraic
certificate for the standard explicit quaternion-field candidate—not a claim that its splitting
field has Galois group `Q8`, and not a root-number calculation. Those two arithmetic steps remain
open and must not be merged by citation alone.

## 2026-08-19 literal CCM Lambert coefficient integrality

`[LEAN-PROVED]` `CCMLambertCoefficientIntegrality.lean` now represents the literal coefficient of
`q^n` in CCM equation `(53)`: the finite sum over `ell` with `2*ell+1 | n`, including its sign,
the `2^(3/2-2ell-i-j)` factor, and a chosen square root of
`sigma(ell,i)*sigma(ell,j)`.  The theorem
`ccmLambertEntryCoefficient_dyadicIntegral` proves that some power of `2` times this exact finite
coefficient is an algebraic integer, for every choice satisfying the literal radical equation.
It is unconditional and axiom-clean apart from Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`.

This closes the dyadic algebraic-integrality component of the paper's finite coefficient proof.
It does **not** establish equation `(55)`, cyclotomic-integer containment of the radical, the
intersection `Q(sqrt 2) ∩ Z^cyc[1/2]`, or Theorem 5.6(ii)--(iii). Those remain distinct literal
CCM targets.

## 2026-08-19 general Burnol compact-source lower zero jets

`[LEAN-PROVED]` `BurnolCoPoissonGeneralSeedCompletedZeroJets.lean` removes the former
logarithmic-subwindow restriction from the source-side lower-jet law.  A literal
`BurnolCoPoissonSource` has a seed supported in `[b,b⁻¹]`; the formal proof derives eventual
zero at both Mellin ends, applies Mathlib's dominated Mellin differentiation theorem throughout
the strip, and obtains holomorphy of the source Mellin factor.  Therefore, at every selected
right-half Xi divisor, the complete zeta factor forces every jet below its exact multiplicity to
vanish.  The theorem is transported to the actual Sonine evaluator, then to both literal branches
of every cosine-closed co-Poisson generator via the reciprocal-seed landing.

This is stronger than the previous single-subwindow statement and is coefficient-faithful to the
literal source definition.  It still does **not** prove Burnol Theorems 3.1--3.2: extending
higher-jet annihilation from generators to the topological closure requires bounded higher-jet
evaluators, and identifying their common kernel with `P_a` requires the paper's aperture
completeness/minimality argument.  Neither step is claimed here.

## 2026-08-19 cosine-closed algebraic zero-jet system

`[LEAN-PROVED]` `BurnolCoPoissonCosineClosedLowerJetSystem.lean` packages the literal result at
the correct algebraic scope.  For every selected right-half Xi divisor and every jet below its
exact multiplicity, `burnolCoPoissonLowerXiJetAnnihilator` is a genuine complex submodule of the
actual extended Sonine carrier.  It retains a local analytic germ as part of membership, so the
closure argument cannot silently use an unproved differentiation theorem.  The theorem
`burnolCoPoissonAlgebraicSourceSpace_le_lowerXiJetAnnihilator` proves that **every finite linear
combination** of literal co-Poisson sources and their cosine images belongs to this submodule.

This is the full cosine-closed algebraic lower-jet system, unconditional and source-faithful.  It
is not the Hilbert-space closure/complement equality in Burnol's Theorems 3.1--3.2: that exact
remaining step is a uniform boundedness theorem for all higher jet evaluators on literal `L_a`,
followed by the paper's `L_a/K_a/P_a` aperture-completeness argument.
