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
| 1 | Deninger, [Theorem 2.13](https://arxiv.org/abs/2204.02714) | No functorial real-valued Weil cohomology satisfying property 2.12, using a quaternionic Artin representation with odd central multiplicity. | `[LEAN-PROVED]` `DeningerQ8ActualGroupRepresentation.lean` gives a literal `QuaternionGroup 2 →* Module.End ℂ (ℂ × ℂ)` action, and `DeningerQ8ArtinGaloisRealization.lean` transports it through any field-Galois identification `G ≃ Q8`, proving degree eight and the right-half Euler-product facts. `DeningerArtinCentralParityNoGo.lean` formalizes final parity contradiction conditional on root number and descent inputs. | Formalize arithmetic witness itself: explicit finite Galois quaternion number field and its root number `-1`; then real-representation classification supplying even multiplicity from real descent and property 2.12 instantiation. Current Galois transport is not number-field or root-number realization. |
| 2 | Connes--van Suijlekom, [Corollary 1.1 and Theorem 1.2](https://arxiv.org/abs/2511.23257) | A rank-`n` PSD Toeplitz `(n+1)`-matrix has a kernel polynomial with all roots on the circle; its distributional continuous simple-even-ground analogue has only real Fourier zeros. | `[LEAN-PROVED]` `CaratheodoryFejerPSDtoAtomicFactorization.lean` gives the reverse same-level finite truncated-Herglotz/Carathéodory--Fejér realization for every normalized Hermitian PSD `T_N`: `exists_atomic_caratheodoryFejer_psd_factorization`. The pre-existing atomic Gram and kernel-root modules provide its factorization-to-root successor. `TruncatedConvolutionOddGroundRealZeros.lean` remains only an odd smooth-kernel analogue. | Extract rank-many/distinct support from the finite atomic realization for the sharp corank-one statement; then build distributions, form closure, lower-bounded self-adjoint realization, and the simple isolated **even** ground required by Theorem 1.2. |
| 3 | Connes--Consani--Moscovici, [Theorem 6.6 and Lemma 5.5](https://arxiv.org/abs/2403.01247) | Literal one-prime Gamma--Euler measure has finite Jacobi/characteristic data in `Z[1/sqrt 2]` after `q=1/p`; central-binomial integrality controls rank-one harmonic coefficients. | `[LEAN-PROVED]` `CCMCentralBinomialIntegrality.lean` proves Lemma 5.5. `CCMCyclotomicLambertIntegrality.lean` now proves the literal equation-(55) gate: every complex radical with square `sigma(ell,i)*sigma(ell,j)` is a concrete cyclotomic integer, and every literal equation-(53) coefficient belongs to `Z^cyc[1/2]`; it packages the whole coefficient system as a formal Lambert series. | Formalize CCM's intersection argument and the finite characteristic-polynomial/measure argument of Theorem 5.6. Coefficientwise containment alone does not identify `Q(sqrt 2) ∩ Z^cyc[1/2]` or prove the measure theorem. |
| 4 | Burnol, [Theorems 3.1--3.3](https://arxiv.org/abs/math/0203120) | Multiplicity-indexed zeta evaluator systems have stated aperture-dependent completeness/minimality, closed co-Poisson complement, and critical two-jet correction. | `BurnolCoPoissonCosineClosedZeroAnnihilator.lean` identifies raw and cosine-closed source spaces. `BurnolCoPoissonCosineClosedZeroJetDetection.lean` proves exact closed-space zeroth-jet detection: its Riesz evaluator is orthogonal to literal cosine source iff `zeta(w)=0`. General lower Xi jets are algebraically packaged in `BurnolCoPoissonCosineClosedLowerJetSystem.lean`. | Formalize literal `L_a`, `K_a`, bounded higher-jet family, `Y_a^perp = P_a`, aperture threshold completeness/minimality, and `a=1` two-jet deletion. Closed zeroth-jet detection is not those higher completeness claims. |

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

`CCMCyclotomicLambertIntegrality.lean` now closes CCM's literal cyclotomic radical gate and the
full formal equation-(53) coefficient system.  The next CCM target is the paper's separate
intersection/finite-characteristic-polynomial argument in Theorem 5.6, not a reproof of the
already closed coefficientwise containment.  In parallel, the Deninger parity spine is closed as
described above.  Neither result assumes RH, a spectral limit, or a numerical calculation.

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

## 2026-08-19 legacy radical certificate correction

`DeningerQ8ExplicitRadicalPolynomial.lean` proves an elementary eliminant for
`z²=(2+√2)(3+√3)`.  That identity is retained, but it is **not** evidence of the number-field
root-number witness required by Deninger's theorem.  In particular it must not be conflated with
Dedekind's `3+√6` quaternion field or the documented root-number-minus-one field below.

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

## 2026-08-19 closed cosine zeroth-jet detection

`[LEAN-PROVED]` `BurnolCoPoissonCosineClosedZeroJetDetection.lean` closes the exact missing
reverse implication at zeroth order:

```lean
(burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace) ∈
    (burnolCoPoissonSourceSpace b)ᗮ ↔ riemannZeta w = 0
```

for `0 < b < 1` and `1/2 < re w < 1`.  The forward direction is the existing closed-space
annihilation.  The reverse is source-faithful: the literal symmetric subwindow `[b,b⁻¹]` is a
cosine-source generator and its completed Mellin evaluation is nonzero whenever `zeta(w) ≠ 0`.
Thus no density or unproved higher differentiation is hidden in the result.

This completes the literal **closed cosine zeroth-jet detection** component.  It does not prove
the higher-jet closure/complement system of Burnol Theorems 3.1--3.3; the all-order bounded
`L_a`-jet family and the `L_a/K_a/P_a` aperture theorem remain the exact open core.

## 2026-08-19 exact CCM cyclotomic Lambert gate

`[LEAN-PROVED]` `CCMCyclotomicLambertIntegrality.lean` now formalizes the literal arithmetic
claim used at CCM equation `(55)`.  `CCMCyclotomicInteger z` is the concrete complex model of
`Z^cyc`: a finite `Z`-linear combination of roots of unity.  The new theorem
`ccmLambertRadical_cyclotomicInteger` states that every complex `z` satisfying

```lean
z ^ 2 = (ccmLambertRadicand ell i j : ℂ)
```

belongs to that ring.  The proof is unconditional: finite harmonic positivity plus Lemma 5.5
make the radicand a natural number; a quadratic Gauss sum gives a cyclotomic square root of every
prime (with the exact `I` correction in the negative-sign case); strong induction through a prime
divisor handles every natural radicand and both square-root branches.

The theorem `ccmLambertEntrySeries_coeff_literal_dyadicCyclotomic` packages the **entire formal
equation-(53) Lambert series**, coefficient by coefficient, in `Z^cyc[1/2]`.  This is stronger
than the earlier algebraic-integrality result and has an axiom audit containing only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`.

It does not prove CCM Theorem 5.6: the remaining literal frontier is the intersection
`Q(sqrt 2) ∩ Z^cyc[1/2]`, followed by the finite characteristic-polynomial and measure argument.

## 2026-08-19 actual Q8 root-number-minus-one witness correction

`[LITERATURE]` Deninger’s cited existence gate is made explicit in Example 1.3(ii) of
Shankar--Södergren--Templier, *Sato--Tate equidistribution of certain families of Artin
L-functions*: the field

```text
Q(sqrt((5 + sqrt(5)) * (41 + 6 * sqrt(41))))
```

is quaternionic and its unique two-dimensional Artin representation has root number `-1`.
The preceding `2,3` radical card is not this witness and is not used for the capstone.

`[LEAN-PROVED]` `DeningerQ8RootNumberNegOneRadicalCertificate.lean` now proves the exact
degree-eight eliminant

```text
z^8 - 820 z^6 + 146780 z^4 - 3362000 z^2 + 16810000 = 0
```

from the literal radical relations, entirely algebraically and without numerical calculation.
This is the correct input polynomial for the actual arithmetic witness.

The still-open, non-negotiable formal steps are: construct its number field, prove normality and
identify its Galois group with `QuaternionGroup 2`, then formalize the local epsilon-factor product
showing that the attached two-dimensional Artin representation has root number `-1`.  The existing
Artin pullback and parity contradiction can compose only after those three facts are proved.

## 2026-08-19 literal Q8 radical-coordinate lift system

`[LEAN-PROVED]` `DeningerQ8RootNumberNegOneRadicalLifts.lean` formalizes the exact field-generic
algebra that a construction of the documented witness must realize.  Given
`x² = 5`, `y² = 41`, and `z² = (5+x)(41+6y)`, the explicit candidate lifts

```text
I(z) = 2x(41+6y)/z,
J(z) = xy(5+x)/z
```

square to `(5-x)(41+6y)` and `(5+x)(41-6y)`, respectively.  The corresponding two composite
top-radical coordinates are proved to differ by a literal minus sign.  This is the source-level
quaternion relation, with every denominator independently proved nonzero from the defining
quadratic relations.

It remains deliberately below a Galois claim: an `AdjoinRoot` construction must prove the three
required nonsquare facts, install these coordinates as ring equivalences, prove normality and count
all eight automorphisms.  The epsilon-factor calculation remains a further independent gate.

## 2026-08-19 actual degree-eight Q8 witness field

`[LEAN-PROVED]` `DeningerQ8RootNumberNegOneFirstQuadratic.lean`,
`DeningerQ8RootNumberNegOneSecondQuadratic.lean`, and
`DeningerQ8RootNumberNegOneTopRadicand.lean` now construct the entire literal radical tower.
They prove, without a degree assumption, that `5` is nonsquare in `Q`, that `41` and `205` are
nonsquare in `Q(√5)`, and that the final radicand is nonsquare in `Q(√5,√41)`.

The last result is a relative-norm descent, not a finite search: second conjugation sends
`√41` to `-√41`; a hypothetical square root of `(5+√5)(41+6√41)` gives a fixed norm quotient
whose square is `205`; fixed-point descent returns a square root of `205` in `Q(√5)`, which is
formally impossible.  Consequently Lean proves the exact tower degree

```text
[Q(√5, √41, √((5+√5)(41+6√41))) : Q] = 8.
```

The module is wired into `GaloisForLFunctions.RHTower`, has passed its narrow source and leaf
build checks, and both capstone theorems have only `propext`, `Classical.choice`, and `Quot.sound`
in their axiom audits.  This closes the field-construction gate, but not yet the primitive-field
equality `Q(z)=Q(√5,√41,z)`, normality, an eight-element `Q8` automorphism group, or the Artin
epsilon-factor computation.  Those remain the exact next obligations; none is being inferred from
the degree calculation.

## 2026-08-19 primitive equality for the documented Q8 field

`[LEAN-PROVED]` `DeningerQ8RootNumberNegOnePrimitiveField.lean` now closes the next exact
field-theory gate.  In the constructed top field, let `z` be the literal final radical and
`u=z²`.  Lean proves the nonvanishing recovery law

```text
(5 + √5) * (2050 - 82u) = 4100 - u²,
```

then derives explicit rational-function recovery of `√5`, `41+6√41`, and `√41` from `z`.
The denominator nonvanishing is proved algebraically: its vanishing would force `u=25`, which
contradicts the displayed law.  Using exact normal forms for all three `AdjoinRoot` layers, the
formal theorem

```lean
deningerQ8RootNumberNegOne_primitiveField_eq_top
```

proves `Q(z)` equals the complete degree-eight radical tower.  The literal notation in the cited
source is therefore now represented faithfully, rather than as shorthand for a larger field.
Leaf build and axiom audit passed; only `propext`, `Classical.choice`, and `Quot.sound` occur.

`[OPEN CORE]` The field now has the documented primitive generator and degree.  The next distinct
proof obligation is arithmetic, not eliminant algebra: install the already-verified radical lift
coordinates as field automorphisms, prove their quaternion multiplication table and normality, and
only then attach the Artin representation.  The global epsilon-factor/root-number calculation
remains independent after that.

## 2026-08-19 literal quaternion automorphisms of the documented field

`[LEAN-PROVED]` `DeningerQ8RootNumberNegOneAutomorphisms.lean` installs the two radical lift
formulas as actual bijective ring endomorphisms of the literal degree-eight field.  The proof uses
the previously closed primitive equality `Q(z)=K`: maps agreeing on the final radical agree on the
whole field.  It then proves, without an assumed Galois action,

```text
I² = J² = C,   C² = 1,   I J = C J I,
```

where `C(z) = -z` and the maps fix `Q`.  The anti-commutation proof is coefficient-faithful: its
only nontrivial input is the already formalized equality of the two explicit composite radical
coordinates with opposite signs.  Targeted `lake env lean`, leaf `lake build`, and axiom audits
passed; listed axioms are only `propext`, `Classical.choice`, and `Quot.sound`.  The leaf is wired
into `GaloisForLFunctions.RHTower`; no umbrella build was run.

`[OPEN CORE]` These relations exhibit an eight-candidate quaternion subgroup but do not by
themselves prove its elements distinct, exhaust all `Q`-automorphisms, or establish normality.
The next exact field-theoretic target is an injective `QuaternionGroup 2` action into the actual
automorphism group, followed by the degree-eight automorphism-count criterion for `IsGalois`.
The source's global Artin epsilon-factor calculation remains a separate, presently unformalized
analytic-arithmetic theorem.
