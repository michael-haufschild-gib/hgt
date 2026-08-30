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

## 2026-08-19 Q8 witness audit correction

`[FALSIFIED]` The previously labelled radical field

```text
Q(sqrt((5 + sqrt(5)) * (41 + 6 * sqrt(41))))
```

is **not authenticated** by the cited literature as the root-number-minus-one witness.  Its
eliminant is

```text
z^8 - 820 z^6 + 146780 z^4 - 3362000 z^2 + 16810000,
```

and the Lean corpus now proves that this is a degree-eight Galois `Q8` field.  No checked source
establishes the required Artin root number for this particular field.  Thus its legacy
`RootNumberNegOne` file prefix records an abandoned attribution, not a formal root-number result.

`[LITERATURE]` The authenticated Serre witness is the root field of

```text
x^8 - 205*x^6 + 13940*x^4 - 378225*x^2 + 3404025,
```

which is Galois with group `Q8`; its unique nonabelian irreducible character is symplectic of
degree two and has root number `-1`.  This exact statement is recorded in Example 1.3 of
Fiorilli--Jouve, *Distribution of Frobenius elements in families of Galois extensions*, citing
Serre.  Equivalently, its degree-eight radical generator is one half of

```text
sqrt((5 + sqrt(5)) * (41 + sqrt(205))).
```

The scale by `1/2` converts the radical eliminant
`X^8 - 820*X^6 + 223040*X^4 - 24206400*X^2 + 871430400` to the displayed Serre polynomial.

`[LEAN-PROVED]` The literal Serre tower now has exact degree eight, explicit radical lifts,
`IsGalois ℚ SerreQ8TopField`, and
`Gal(SerreQ8TopField/ℚ) ≃* QuaternionGroup 2`
in `SerreQ8RootNumberNegOneTopRadicand.lean`,
`SerreQ8RootNumberNegOneAutomorphisms.lean`,
`SerreQ8RootNumberNegOneGalois.lean`, and
`SerreQ8RootNumberNegOneGaloisIdentification.lean`.  The two-dimensional symplectic Artin
representation is now pulled back over this exact Galois group in
`SerreQ8ArtinGaloisRealization.lean`.

`[OPEN CORE]` The local epsilon-factor product defining the Artin root number still needs a
genuine global epsilon-factor theory and its source calculation; it cannot be replaced by a Lean
declaration named `rootNumber = -1`.

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

## 2026-08-19 actual Q8 number field and Galois identification

`[LEAN-PROVED]` `DeningerQ8RootNumberNegOneGalois.lean` constructs eight distinct
`ℚ`-algebra automorphisms of the literal field, one for each element of
`QuaternionGroup 2`.  Its exact automorphism-count theorem is

```lean
q8Aut_card_eq_eight : Fintype.card Gal(K/ℚ) = 8
```

and the already formalized degree computation is also eight.  Mathlib’s finite-extension
criterion therefore gives the unconditional theorem

```lean
deningerQ8RootNumberNegOne_isGalois : IsGalois ℚ K.
```

`[LEAN-PROVED]` `DeningerQ8RootNumberNegOneGaloisIdentification.lean` then proves the stronger
literal group statement.  It derives the generic relation
`I^i J = J I^{-i}` from the field-level anti-commutation law, checks all four constructor
multiplication cases of mathlib’s `QuaternionGroup 2`, and packages the resulting bijective
homomorphism as

```lean
deningerQ8RootNumberNegOne_galoisEquivQ8 : Gal(K/ℚ) ≃* QuaternionGroup 2.
```

The leaf builds and axiom audits passed with only Lean’s standard `propext`, `Classical.choice`,
and `Quot.sound`; both new leaves are wired into `GaloisForLFunctions.RHTower`, without an
umbrella build.  This closes the **actual Q8 number-field and Galois-group** portion of the
literature witness.  The remaining Q8 obligation is no longer field theory: formalize the source’s
global epsilon-factor calculation that the unique irreducible two-dimensional Artin factor has
root number `-1`, then connect it to the existing Deninger parity endpoint.

## 2026-08-29 primary-source correction: literal Q8 root-number witness

`[FALSIFIED]` The 2026-08-19 “Q8 witness audit correction” above (lines 214--263 at the time of
this entry) reverses the source record.  Its claim that the legacy radical field was
unauthenticated and that a different “Serre witness” was Example 1.3 is false.  Do not use that
section as evidence for a root number.

`[LITERATURE]` The primary published source is A. Shankar, A. Södergren, and N. Templier,
[*Sato--Tate equidistribution of certain families of Artin L-functions*, Example 1.3(ii)](https://doi.org/10.1017/fms.2019.18).
It explicitly states that

```text
K = Q(sqrt((5 + sqrt(5)) * (41 + 6 * sqrt(41))))
```

is quaternionic over `Q`, contains `Q(sqrt 5, sqrt 41)`, and that the unique irreducible
2-dimensional Artin representation `rho_K` has root number `-1`.  This is exactly
`deningerQ8RootNumberNegOneTopField`, not the separate `SerreQ8TopField` construction.

`[LEAN-PROVED]` `DeningerQ8ActualArtinEulerProduct.lean` now attaches the source-selected
literal field to the corpus’s genuine finite-place Artin Euler product, using the already proved
facts

```lean
deningerQ8RootNumberNegOne_isGalois
deningerQ8RootNumberNegOne_galoisEquivQ8
```

It proves only unconditional source-side facts: holomorphy and nonvanishing on the
absolute-convergence half-plane.  Its exact new declarations are

```lean
deningerQ8ActualArtinEulerProduct
differentiableOn_deningerQ8ActualArtinEulerProduct
deningerQ8ActualArtinEulerProduct_ne_zero_of_mem_artinEulerAbsoluteHalfPlane
```

`[OPEN CORE]` The paper asserts the global root number but does not supply a Lean-ready local
factor table.  The remaining theorem is a literal global Artin epsilon calculation for this
field: construct the inducing order-four Hecke character on a quadratic subfield, prove its local
conductors and epsilon factors at every ramified and archimedean place, and prove their global
product is `-1`.  Neither finite-place Euler-product convergence nor the source citation can
replace that calculation.  The prior attribution to Fiorilli--Jouve and the claim that a distinct
Serre polynomial supplied this witness are retracted.

## 2026-08-29 fixed-base separation of the two Q8 radical presentations

`[LEAN-PROVED]` `Q8PresentationSquareClassSeparation.lean` closes the immediate
cross-presentation question raised by the primary-source correction.  Put

```text
A = (5 + sqrt(5)) * (41 + 6 * sqrt(41))
B = (5 + sqrt(5)) * (41 + sqrt(205))
```

over the common base `F = Q(sqrt(5), sqrt(41))`.  Lean proves

```lean
serreQ8TopRadicand_div_deningerQ8RootNumberNegOneTopRadicand_not_square
  (w : F) : w ^ 2 ≠ B / A
```

The proof is not a coefficient comparison masquerading as field theory.  It computes the quotient's
relative norm as `36/5` and trace as `(3362 - 492*sqrt(5))/205`; a hypothetical square gives a
fixed trace whose square is either `82/5` or
`(3362 - 984*sqrt(5))/205`.  Both are then ruled out using the literal `1, sqrt(5)` coordinate
rigidity already proved for the first quadratic field.

`[FALSIFIED]` Any planned Frankenstein transport that identifies these two top radicals by a
multiplier in their shared biquadratic base is false.  In particular,
`SerreQ8MonomialSourceLaw.lean` cannot be moved to the source-selected
`41 + 6*sqrt(41)` field by the ordinary Kummer square-class transport.

`[BRIDGE]` Fröhlich's 1972 theorem, *Artin-root numbers and normal integral bases for quaternion
fields* ([bibliographic record](https://eudml.org/doc/142165)), supplies the surviving literature
mechanism: for a tame quaternion extension over `Q`, normal-integral-basis freeness is equivalent
to root number `+1` for the unique symplectic character.  Thus a source proof that the selected
field is tame and its integer ring is not free over `Z[Q8]` would force the required `-1` sign and
simultaneously provide the Galois-module obstruction.  This is not formalized: the corpus lacks a
literal ring-of-integers, ramification, and locally-free-class framework for the selected field.

## 2026-08-29 CCM concrete cyclotomic-to-integral bridge

`[LEAN-PROVED]` `CCMCyclotomicAlgebraicIntegrality.lean` closes the missing bridge from the concrete definition of `Z^cyc` used by the literal CCM Lambert system to Mathlib's algebraic integrality predicate:

```lean
CCMRootOfUnity.isIntegral
CCMCyclotomicInteger.isIntegral
CCMDyadicCyclotomicInteger.dyadicIntegral
```

The proof is direct and source-faithful: a root of unity is integral because a positive power is one; a finite integer-linear combination is integral by finite-sum and product closure; clearing the supplied power of two gives the existing dyadic-integrality predicate. The leaf was checked with `lake env lean`, target-built as `GaloisForLFunctions.RHTower.CCMCyclotomicAlgebraicIntegrality`, and its public theorems have only `propext`, `Classical.choice`, and `Quot.sound`. It is wired into the RHTower umbrella without an umbrella build.

This does **not** prove the unresolved arithmetic intersection `Q(sqrt 2) ∩ Z^cyc[1/2] = Z[1/sqrt 2]`, nor the characteristic-polynomial descent in CCM Theorem 5.6. It supplies the exact algebraic-integrality premise needed for the first of those two remaining steps.

## 2026-08-30 CCM quadratic trace--norm entry

`[LITERATURE]` The standard quadratic-field classification says
`O_(Q(sqrt d)) = Z[sqrt d]` for squarefree `d = 2, 3 (mod 4)`; in particular
`O_(Q(sqrt 2)) = Z[sqrt 2]`.  The precise trace--norm/parity proof is recorded
in Proposition 2.24 of [Weston/Conrad's algebraic-number-theory notes](https://kconrad.math.uconn.edu/math5230f08/weston.pdf).

`[LEAN-PROVED]` `CCMSqrtTwoIntegralTraceNorm.lean` now formalizes the nontrivial entrance of that argument on the literal carrier `SqrtTwoRat = QuadraticAlgebra Q 2 0`:

```lean
ccm_rat_exists_int_of_isIntegral_image
ccmSqrtTwoRatConj
ccm_sqrtTwoRat_trace_eq
ccm_sqrtTwoRat_norm_eq
ccm_sqrtTwoRat_trace_exists_int
ccm_sqrtTwoRat_norm_exists_int
```

The module proves `Q(sqrt 2)` is a field from the irrationality of `sqrt 2`, builds its nontrivial conjugation over `Z`, reflects rational integrality across a faithful characteristic-zero extension, and proves that every integral element has integral rational trace and norm.  It was scratch-checked, target-built as `GaloisForLFunctions.RHTower.CCMSqrtTwoIntegralTraceNorm`, axiom-audited (only `propext`, `Classical.choice`, `Quot.sound`), and wired into `RHTower.lean` without an umbrella build.

`[OPEN CORE]` The remaining source-independent parity lemma is exact: for `a, b : Q`, integral `a + b sqrt 2` has `2a` and `a^2 - 2b^2` integral; reducing the two rational denominators forces `a, b : Z`.  Only after that classification is proved may localization at `2` state the required cyclotomic intersection.  Neither conclusion is claimed by the new leaf.

## 2026-08-30 CCM quadratic parity closure

`[LEAN-PROVED]` The preceding parity open core is now closed in the same module:

```lean
ccm_sqrtTwoRat_integral_has_integer_coefficients
ccm_sqrtTwoRat_integral_of_integer_coefficients
ccm_sqrtTwoRat_isIntegral_iff_integer_coefficients
```

This is the literal `O_(Q(sqrt 2)) = Z[sqrt 2]` classification, not an assumed
ring-of-integers object.  The forward proof uses the already formalized rational trace and norm;
it splits the trace integer by parity.  In the even branch a reduced rational square equalling an
integer divided by `2` has denominator one.  In the odd branch it would have to have denominator
whose square is `8`, an explicit contradiction.  The reverse proof exhibits the integer-coordinate
element as an integer plus an integer multiple of the integral root of `X^2 - 2`.

The remaining CCM arithmetic task is now genuinely narrower: construct the faithful literal
embedding `Q(sqrt 2) -> C`, transport this exact classification through it, and formalize the
localization statement
`Q(sqrt 2) ∩ Z^cyc[1/2] = Z[sqrt 2][1/2]` in those concrete representations.  The finite
characteristic-polynomial/measure descent of Theorem 5.6 remains after that intersection.

## 2026-08-30 CCM concrete dyadic cyclotomic intersection

`[LEAN-PROVED]` `CCMSqrtTwoDyadicCyclotomicIntersection.lean` closes the preceding localization
step in concrete, coefficient-faithful form.  It constructs the fixed faithful embedding

```lean
ccmSqrtTwoRatComplexEmbedding : SqrtTwoRat →ₐ[ℤ] ℂ
```

and represents `Z[sqrt 2][1/2]` without an abstract localization object:

```lean
ccmSqrtTwoDyadicInteger x :=
  ∃ d : Nat, ∃ a b : Int,
    (a : Q) = (2^d * x).re ∧ (b : Q) = (2^d * x).im
```

(The implemented formula uses the literal `algebraMap Q SqrtTwoRat` for the displayed scalar.)
The exact theorem is

```lean
ccm_sqrtTwoDyadicInteger_iff_complex_dyadicCyclotomic
```

which proves that this predicate holds exactly when the complex image lies in the existing
literal `CCMDyadicCyclotomicInteger` predicate.  The forward direction clears the same power of
two in `Z^cyc`, uses concrete cyclotomic integrality, reflects it through the injective embedding,
and invokes the proved `O_(Q(sqrt 2)) = Z[sqrt 2]` classification.  The reverse direction writes
the cleared image as `a + b sqrt(2)` and uses the concrete cyclotomic certificate for `sqrt(2)`.

Direct `lake env lean` and the sole target build
`GaloisForLFunctions.RHTower.CCMSqrtTwoDyadicCyclotomicIntersection` passed.  A public axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.  The leaf is imported by
`RHTower.lean`; no umbrella build was run.

This closes the exact CCM **intersection** part of the literature capstone.  It does not assert
the still-separate finite characteristic-polynomial/measure descent in CCM Theorem 5.6, nor any
source-order law or RH receiver conclusion.

## 2026-08-30 CCM finite determinant coefficient descent

`[LEAN-PROVED]` `CCMDyadicCyclotomicFiniteDeterminant.lean` closes the finite algebraic
coefficient step needed before the source-specific similarity used in
Connes--Consani--Moscovici Theorem 5.6.  The terminology is corrected here: the paper's step is a
finite `q`-matrix/exterior-trace/determinant descent, not a measure argument.

The new leaf realizes the existing concrete predicate `CCMDyadicCyclotomicInteger` as the literal
subring `ccmDyadicCyclotomicSubring : Subring C`, lifts coefficientwise-contained formal power
series to it, and proves

```lean
ccmDyadicCyclotomic_det_coeff
ccmLambertFiniteMatrix_det_coeff_literal_dyadicCyclotomic
ccmSqrtTwoDyadicInteger_of_complex_eq_ccmLambertFiniteMatrix_det_coeff
```

Thus every coefficient of the determinant of every finite literal CCM equation-(53) parity-block
`q`-matrix lies in `Z^cyc[1/2]`; the new source-selected nonnegative radical
`ccmLambertCanonicalRadical` removes the formerly conditional choice and gives the unconditional
matrix `ccmActualFiniteQMatrix`.  If a coefficient is represented in the fixed concrete
`Q(sqrt 2)` carrier, the previous intersection theorem puts it in `Z[sqrt 2][1/2]`.  This is a
reusable finite algebra bridge; the separate `Q(sqrt 2)` similarity in the paper is not yet
formalized.

The scratch proof, duplicate-declaration audit, direct `lake env lean`, and sole target build
`lake build GaloisForLFunctions.RHTower.CCMDyadicCyclotomicFiniteDeterminant` passed.  Its three
public endpoint theorems use only `propext`, `Classical.choice`, and `Quot.sound`; the leaf is
wired into `RHTower.lean` without an umbrella build.

`[OPEN CORE]` The source-specific part of Theorem 5.6 remains: construct the paper's normalized
moment matrices `D_n(q), D_n(0), E_n(q)` and prove its parity/source similarity placing the
relevant exterior traces in `Q(sqrt 2)`.  This leaf then discharges their coefficient-ring
consequence.  It clears no
`ORD/COF/ORIENT/LAND/COMP` RH gate and is therefore infrastructure for a literature capstone, not
a new Frankenstein merger law.

## 2026-08-30 CCM literal q-matrix correction and normalized determinant

`[BUG FIX + LEAN-PROVED]` Primary-source audit of CCM equation (53) exposed a concrete defect in
the former formal Lambert coefficient: the formal condition `2*ell+1 ∣ n` accidentally admitted
`ell=0` at `n=0`, although every term `q^(2*ell+1)/(1-q^(2*ell+1))` has zero constant coefficient.
`ccmLambertEntryCoefficient` now branches at `n=0`, and the new theorem

```lean
ccmLambertEntryCoefficient_zero
ccmLambertEntrySeries_coeff_zero
```

records that literal source fact.  Both coefficient-integrality leaves were rebuilt directly;
no unrelated module was built.

The finite CCM layer now also constructs the unconditional source-selected q-matrix
`ccmActualFiniteQMatrix`.  It uses the nonnegative real radical of the proven nonnegative
equation-(51) radicand and enforces the zero cross-parity block required by equation (53), so it
is the literal finite `A_n^+(q) ⊕ A_n^-(q)` carrier rather than an all-entry over-approximation.
It proves

```lean
ccmLambertCanonicalRadical_sq
ccmActualFiniteQMatrix_coeff_dyadicCyclotomic
ccmActualFiniteQMatrix_det_coeff_dyadicCyclotomic
ccmActualFiniteQMatrix_coeff_zero
ccmActualFiniteQNormalizedDeterminant_coeff_dyadicCyclotomic
ccmActualFiniteQNormalizedDeterminant_coeff_zero
```

In particular, the literal Lemma-5.1 generating determinant
`det(I + A_n(q))` has coefficientwise `Z^cyc[1/2]` containment and constant coefficient one,
unconditionally.  This is the cyclotomic/exterior-determinant half of the paper's finite result.

`[OPEN CORE]` It still does not identify this literal q-matrix with the source-normalized moment
matrix `D_n(0)^(-1) E_n(q)` over `Q(sqrt 2)`.  That identity is what turns the just-proved
cyclotomic containment into the `Z[1/sqrt 2]` theorem for exterior traces and
`D_n(q)/D_n(0)`.  No RH gate is claimed discharged.

## 2026-08-30 Burnol unit-aperture completed first jet

`[LEAN-PROVED]` `BurnolSoninUnitFirstJetEvaluation.lean` closes the first
nontrivial bounded-jet step for Burnol's literal extended Sonine carrier at
the exceptional aperture `a = 1`.  It does not postulate a jet functional:
the proof splits the literal Mellin integral into its constant head and its
`L²` tail.  The head is the intrinsic bounded indicator pairing and the tail
is a new Riesz functional against `t^{-w}`; its derivative uses the already
proved Riesz functional against `-log(t)t^{-w}`.

The exact outcome is a continuous linear map

```lean
burnolExtendedSoninUnitFirstJetEvaluation
```

and the literal derivative theorem

```lean
hasDerivAt_soninMellinEvaluation_unit_firstJet
```

for every `1/2 < Re w < 1`.  Its derivative is the coefficient-faithful
Gamma product rule: the completed-factor derivative times the raw head-tail
Mellin value, plus the completion factor times the head derivative and the
logarithmic tail integral.  No zeta-zero premise, multiplicity assumption,
or RH-equivalent boundedness is used.

Direct `lake env lean`, duplicate-declaration audit, and the sole leaf build
`lake build GaloisForLFunctions.RHTower.BurnolSoninUnitFirstJetEvaluation`
passed.  The public endpoint has only `propext`, `Classical.choice`, and
`Quot.sound` in its axiom audit.  The new leaf is wired into `RHTower.lean`;
no umbrella build was run.

`[OPEN CORE]` This is the unit-aperture first-jet base case, not Burnol's
aperture completeness theorem.  Remaining literature frontier is the
bounded all-order jet family, its closed-span identification with `P_aᗮ`, and
Burnol's aperture threshold/completeness-minimality passage.  This result
does not discharge an RH source gate on its own; it removes a concrete
analytic obstruction to applying the existing completed zero-jet system at
the `a = 1` endpoint.

## 2026-08-30 Burnol all-order bounded tail-jet family

`[LEAN-PROVED]` `BurnolSoninAllOrderTailJets.lean` removes the literal
all-order *tail* boundedness obstruction at the unit aperture. For every
natural `k` and every `w` with `1/2 < Re w`, it defines the coefficient-faithful
kernel

```lean
soninMellinLogPowerKernel k w t = (-log t)^k * t^(-w)
```

and proves

```lean
memLp_soninMellinLogPowerKernel_Ioi_one
soninMellinTailLogPowerEvaluation_apply
```

The proof loses a strictly positive amount in the real Mellin exponent and
uses `log(t)^k ≤ (t^δ / δ)^k` on the literal tail `(1,∞)`. Hence each finite
order has a genuine bounded Riesz evaluator on `SoninL2`, whose value is the
literal tail integral. The order-zero and order-one evaluators are proved
equal to the previously formalized Mellin and first-derivative functionals.

Direct source checking, the sole target build
`lake build GaloisForLFunctions.RHTower.BurnolSoninAllOrderTailJets`, corpus
duplicate audit, and axiom audits passed; the two public endpoints depend only
on `propext`, `Classical.choice`, and `Quot.sound`. The leaf is wired into
`RHTower.lean`; no umbrella build was run.

`[OPEN CORE]` This proves all finite tail evaluators, not the completed
all-order derivative theorem on the full `L₁` carrier. The remaining
literature obligations are the recursive dominated-differentiation theorem,
the unit-head/Gamma Leibniz jet formula, the closure identification with
`P_aᗮ`, and the aperture completeness/minimality theorem. No RH conclusion
or source gate is claimed from this analytic component alone.

## 2026-08-30 Burnol literal-source completed continuation and all-order jets

`[LEAN-PROVED]` `BurnolSoninCompletedJetBridge.lean` now separates two
objects that must not be conflated.  The raw literal integral
`soninMellinEvaluation` is proved to equal its analytic continuation only on
the absolute-convergence half-strip `1/2 < Re s < 1`; on the left half of the
strip it is not a valid substitute for continuation.  The new source-selected
object

```lean
soninExtendedCompletedMellinContinuation
```

is the central-band continuation transported through the proved embedding of
the literal positive-head/cosine-head carrier.  It agrees locally with the
Gamma-completed raw integral on that right half-strip:

```lean
eventuallyEq_soninEval_mul_completion_soninMellinEvaluation
```

and every one of its finite jets has a bounded linear representative on the
literal `soninExtendedSpace a` throughout `0 < Re s < 1`:

```lean
exists_soninExtendedCompletedMellinContinuationJetEvaluator
```

The same representative evaluates every finite derivative of the literal raw
completed integral wherever that integral is defined:

```lean
exists_soninExtendedCompletedMellinJetEvaluator
```

This consumes two distinct analytic prerequisites for the Burnol zero-jet
system—source-carrier selection and all-order bounded evaluation—while keeping
the physical integral/continuation distinction coefficient-faithful.  It does
not identify the common jet kernel with `P_aᗮ`, prove the `L_a/K_a/P_a`
complement, or establish aperture completeness/minimality; those remain the
actual Burnol topological core.  The preceding tail module also now proves the
recursive dominated-differentiation and literal all-order tail-jet formula,
not merely existence of individual Riesz evaluators.

Direct source checks and only the two leaf builds
`GaloisForLFunctions.RHTower.BurnolSoninAllOrderTailJets` and
`GaloisForLFunctions.RHTower.BurnolSoninCompletedJetBridge` passed.  Both are
wired into `RHTower.lean`; no umbrella build was run.  Axiom audits for the
tail formula and both bridge endpoints report only `propext`,
`Classical.choice`, and `Quot.sound`.

## 2026-08-30 Burnol closed cosine co-Poisson lower-jet descent

`[LEAN-PROVED]` The bounded all-order source jet now crosses the literal
cosine-closed co-Poisson Hilbert closure.  The new leaf
`BurnolCoPoissonCosineClosedContinuousLowerJetSystem.lean` proves, for every
right-half Xi divisor `rho`, every `j < m_rho`, and every `f` in the actual
closed source space,

```lean
iteratedDeriv j
  (fun w => soninMellinEvaluation w ((f : evenSubspace) : SoninL2)) rho = 0
```

The proof is coefficient-faithful: it obtains the bounded raw completed-jet
evaluator on `soninExtendedSpace b`, extends it to the ambient even Hilbert
carrier by orthogonal projection onto that closed source carrier, and applies
the generic continuous-detector closed-span theorem to the literal generator
set.  Thus no unproved topology is smuggled into the closure passage.

This closes the Burnol `BND + COMP` subgate: all lower completed zero jets
annihilate the full literal cosine-closed source, not only finite source
combinations.  It still does **not** identify that closed source with the
common jet kernel or `P_a` complement; that equality and the aperture
completeness/minimality consequence remain the nontrivial literature core and
are not RH consequences of this lemma alone.

Direct source checking and the only target build
`lake build GaloisForLFunctions.RHTower.BurnolCoPoissonCosineClosedContinuousLowerJetSystem`
passed.  The new theorem's axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  The leaf is wired into `RHTower.lean`;
no umbrella build was run.

## 2026-08-30 Burnol reflected closed lower-jet descent

`[LEAN-PROVED]` The source now carries the same full lower-jet relation in
both functional-equation orientations.  The new leaf
`BurnolCoPoissonCosineClosedReflectedContinuousLowerJetSystem.lean` proves
that, at every left-half Xi divisor `rho`, every `j < m_rho`, and every
member `f` of the literal closed co-Poisson source,

```lean
iteratedDeriv j
  (fun w => soninMellinEvaluation (1 - w)
    ((soninCosineUnitary f : evenSubspace) : SoninL2)) rho = 0
```

This is not a false claim about a divergent left Mellin integral.  The proof
reflects `rho` to its right-half Xi partner, preserves the exact conormal
order through `xiSupportMultiplicity_reflect`, applies the closed right-side
theorem to the cosine-stable source, and transports the derivative using the
affine reflection jet law.  The required analyticity of the right raw germ is
proved from the source-selected completed continuation plus its local equality
with the raw completed integral.  Thus the two orientations share the same
literal source carrier and retain exact multiplicity and derivative parity.

This is a genuine `COMP + ORIENT` subgate closure, not an RH endpoint: the
remaining Burnol barrier is still identification of the common two-sided
lower-jet annihilator with `P_aᗮ` (or another source-selected receiver strong
enough to exclude an off-line conormal top jet).  No such identification is
assumed here.

Direct source checking, the sole leaf build
`lake build GaloisForLFunctions.RHTower.BurnolCoPoissonCosineClosedReflectedContinuousLowerJetSystem`,
and its axiom audit passed.  The endpoint depends only on `propext`,
`Classical.choice`, and `Quot.sound`.  It is wired into `RHTower.lean`; no
umbrella build was run.

## 2026-08-30 Q8 epsilon audit: local norm is closed; local epsilon remains literal

`[LEAN-PROVED]` The literal order-four subgroup used by the monomial model is no longer merely an
abstract `Q8` subgroup.  In `DeningerQ8ActualQuadraticSource.lean`, Lean
identifies its fixed field exactly with the literal quadratic field
`Q(√41)`:

```lean
deningerQ8ActualQuadraticSourceField_eq_fixedField_cyclicSubgroup
```

The same leaf proves the degree-two assertion and that `√41` is not rational.
Together with the already formalized monomial equivalence, this identifies one
literal quadratic field on which an inducing Hecke character may be
constructed; it does not select such a character by assertion.

`[LEAN-PROVED]` A corpus-wide duplicate audit found that the local unramified
norm part is already complete.  In particular,

```lean
nonarchimedeanLocalFieldAdjoinRoot_integralNormPrincipalUnits_surjective
nonarchimedeanLocalFieldAdjoinRoot_integralNormUnits_surjective
```

prove exact principal-unit and unit norm surjectivity for the explicit finite
unramified root lift.  Rebuilding a finite-precision variant would therefore
be duplicate infrastructure, not progress.

`[LITERATURE]` The primary source confirms that the literal quaternionic field
has an order-four inducing Hecke character and global root number `-1`.
Fröhlich--Queyrut reduces a *relative* local character's epsilon factor to its
value on a trace-zero element.  See [Shankar--Södergren--Templier,
Example 1.3(ii)](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/14CF2CC1ED9CFB89A33006023929C5F2/S2050509419000185a.pdf/sato-tate-equidistribution-of-certain-families-of-artin-dollarldollar-functions.pdf)
and the stated local formula in
[Anandavardhanan--Tandon, p. 4](https://msp.org/pjm/2002/206-2/pjm-v206-n2-p02-s.pdf).

`[FALSIFIED AS A CURRENT COMPOSITION]` Neither route composes in the present
Lean corpus.  The norm theorem has no local Artin map or Hecke-character
transport for the literal `Q(√41)` completion.  The finite `Q_p` Tate package
handles primitive Dirichlet characters, not the source-selected local Hecke
components.  Consequently there is also no coefficient-faithful identification
between the `Q/Z` Brauer reciprocity phase and a local epsilon factor.  The
Fröhlich--Queyrut formula cannot be instantiated without first constructing
the actual local character, proving its relative restriction, and evaluating
it on the ramified trace-zero carrier.

**Exact remaining source theorem.** Construct the literal order-four Hecke
character of `Q(√41)` attached to the Q8 extension, its local components and
conductors at every ramified and archimedean place, and the Artin/Hecke local
epsilon comparison.  Only then can the finite epsilon product be calculated
as `-1`.  No wrapper from the cited sign, no ABHN circle-character proxy, and
no unramified norm lemma is an acceptable replacement.
