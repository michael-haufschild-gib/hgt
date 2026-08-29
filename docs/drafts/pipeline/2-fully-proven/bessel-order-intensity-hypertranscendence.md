# Modified-Bessel order and intensity are hypertranscendental

- **ID:** `bessel-order-intensity-hypertranscendence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / DIFFERENCE GALOIS THEORY / BLACK-HOLE RESPONSE
- **Statement:** For every real `s > 0`, both `ν ↦ K_ν(s)` and
  `ν ↦ K_ν(s) K_{ν-2}(s)` are hypertranscendental over `ℂ(ν)`.
- **Status:** `[PROVED HERE]` on paper; novelty search found no collision; Lean formalization has
  closed every analytic, recurrence, scalar-annihilator, arbitrary-period progression-growth,
  factorial-growth, rational-Riccati, meromorphic intensity-recovery, and physical-scan obligation.
  The exact Dreyfus higher-order classification theorem remains unformalized, so this card is not
  promoted.

## Theorem

Fix \(s>0\), and write

\[
  y(\nu):=K_\nu(s),\qquad
  I_s(\nu):=K_\nu(s)K_{\nu-2}(s).
\]

Then \(y\) and \(I_s\) are entire functions of \(\nu\), and neither satisfies a nonzero algebraic
differential equation over \(\mathbb C(\nu)\).

The second assertion matters physically: on the line
\(\nu=1+2i\omega/\kappa\),

\[
  \left|K_{1+2i\omega/\kappa}(s)\right|^2
  =K_\nu(s)K_{2-\nu}(s)
  =K_\nu(s)K_{\nu-2}(s),                                  \tag{1}
\]

because \(K_{-\mu}=K_\mu\). Thus the theorem applies directly to intensity, not only phase.

## Complete paper proof

### 1. Entire order dependence, recurrence, and positivity

For \(s>0\),

\[
  K_\nu(s)=\int_0^\infty e^{-s\cosh t}\cosh(\nu t)\,dt.    \tag{2}
\]

The superexponential decay of \(e^{-s\cosh t}\) dominates \(\cosh(\nu t)\) locally uniformly in
\(\nu\). Hence `(2)` defines an entire function of \(\nu\). It is positive for real \(\nu\).
Integration by parts, or the standard modified-Bessel recurrence, gives

\[
  y(\nu+1)=y(\nu-1)+\frac{2\nu}{s}y(\nu).                  \tag{3}
\]

In particular, for real \(\nu>0\),

\[
  y(\nu+1)>\frac{2\nu}{s}y(\nu).                          \tag{4}
\]

### 2. Both functions satisfy rational linear shift equations

Equation `(3)` is already a second-order linear shift equation over \(\mathbb C(\nu)\) for \(y\).
For the product, put

\[
  Z(\nu)=
  \begin{pmatrix}
  y(\nu)^2\\
  y(\nu)y(\nu-1)\\
  y(\nu-1)^2
  \end{pmatrix},
  \qquad a(\nu)=\frac{2\nu}{s}.
\]

Then

\[
  Z(\nu+1)=
  \begin{pmatrix}
  a(\nu)^2&2a(\nu)&1\\
  a(\nu)&1&0\\
  1&0&0
  \end{pmatrix}Z(\nu),                                    \tag{5}
\]

and the matrix in `(5)` is invertible. Equation `(3)` also gives

\[
  I_s(\nu)
  =y(\nu)^2-\frac{2(\nu-1)}s\,y(\nu)y(\nu-1).              \tag{6}
\]

Therefore \(I_s,\rho I_s,\rho^2 I_s,\rho^3 I_s\), with
\(\rho f(\nu)=f(\nu+1)\), are four rational linear forms on one three-dimensional rational
difference module. They are linearly dependent over \(\mathbb C(\nu)\). Taking a relation of
minimal shift length gives

\[
  a_0 I_s+a_1\rho I_s+\cdots+a_m\rho^m I_s=0,
  \quad a_j\in\mathbb C(\nu),\quad a_0a_m\ne0.             \tag{7}
\]

Thus Dreyfus's scalar theorem applies to both \(y\) and \(I_s\).

### 3. Differential algebraicity would force exponential-polynomial shift growth

Dreyfus proves: if a meromorphic solution \(f\) of a rational linear shift equation is
differentially algebraic over \(\mathbb C(\nu)\), then for some integer \(\ell>0\) and finitely many
\(\lambda_j\in\mathbb C\),

\[
  f\in C_\ell(\nu)
      [e^{\lambda_1\nu},\ldots,e^{\lambda_k\nu}],          \tag{8}
\]

where \(C_\ell\) is the field of \(\ell\)-periodic meromorphic functions.

Choose a real \(\nu_0>2\) avoiding the finitely many coefficient poles and denominator-degeneracy
sets in one representation `(8)`. On the progression \(\nu=\nu_0+\ell n\), every periodic
coefficient is constant. Every rational function over those coefficients has at most polynomial
growth, apart from finitely many denominator zeros, while every exponential monomial has
exponential growth. Consequently there are constants \(C,A>0\) and an integer \(d\) such that,
for all sufficiently large \(n\),

\[
  |f(\nu_0+\ell n)|\le C(1+n)^d A^n.                      \tag{9}
\]

### 4. Exact recurrence forces factorial growth

Iterating `(4)` gives, for every integer \(N\ge1\),

\[
  y(\nu_0+N)>
  y(\nu_0)\left(\frac2s\right)^N(\nu_0)_N.                \tag{10}
\]

This exceeds every polynomial times every fixed exponential: the final \(N/2\) factors in
\((\nu_0)_N\) are each at least \(N/2\). Taking \(N=\ell n\) contradicts `(9)`. Hence \(y\) is
hypertranscendental.

Applying the same bound separately at \(\nu_0\) and \(\nu_0-2>0\) yields

\[
  I_s(\nu_0+N)>
  I_s(\nu_0)\left(\frac2s\right)^{2N}
  (\nu_0)_N(\nu_0-2)_N.                                  \tag{11}
\]

This has factorial-squared growth and again contradicts `(9)`. Therefore \(I_s\) is
hypertranscendental. This proves the theorem.

## Exact extremal-radiation corollary

For the all-time extremal Reissner--Nordström moving-mirror kernel of Good, fix
\(\kappa>0\), and, for

\[
  0<\omega<\frac{\kappa s}{2},
\]

let

\[
  \omega_p=\omega+\omega',\qquad
  \omega_p(\omega)=\frac{\kappa^2s^2}{4\omega},
  \qquad
  \omega'(\omega)=\frac{\kappa^2s^2}{4\omega}-\omega>0.    \tag{12}
\]

Then the modified-Bessel argument is exactly \(s\), and Good's exact all-time coefficient gives

\[
 |\beta_{\omega\omega'(\omega)}|^2
 = \frac{e^{-2\pi\omega/\kappa}\,\omega'(\omega)}
        {\pi^2\kappa^2\omega_p(\omega)}
   I_s\!\left(1+\frac{2i\omega}{\kappa}\right).           \tag{13}
\]

The displayed prefactor is nonzero and differentially algebraic on this interval, while its
Bessel intensity is `(1)`.
Nonzero affine substitution and multiplication or division by a nonzero differentially algebraic
function preserve differential transcendence. Therefore the calibrated intensity scan in
`(12)`--`(13)` is hypertranscendental over \(\mathbb C(\omega)\) (equivalently, it satisfies no
algebraic differential equation on any nonempty open subinterval of the displayed domain).

Here \(\kappa=1/(2M)\) is the scale used in the extremal moving-mirror model; it is not the physical
surface gravity, which vanishes.

## Novelty and scope

Targeted searches across arXiv, zbMATH-indexed results, order-derivative literature, Bessel
inequality literature, and the internal corpus found no prior differential-transcendence theorem
for \(K_\nu(s)\) as a function of its order, nor for the intensity product \(I_s\). This is a
priority lead, not a conclusive global bibliographic proof.

The physical corollary is exact for the cited \(1+1\)-dimensional moving-mirror reduction. It does
not by itself establish a universal extremality phase transition: full nonextremal RN collapse has
variable-parameter confluent-hypergeometric kernels, and greybody factors, \(3+1\) propagation,
backreaction, and collapse stability remain outside the model.

## Lean obligations

- [ ] Formalize the needed special case of Dreyfus's DA-to-periodic-exponential theorem, with no
  axioms.  As of the linearisation pass this splits into exactly two items, both recorded below:
  (a) exclude the imprimitive case for the order recurrence — no rank-one sub-`σ`-module of the
  symmetric square, i.e. no `(α, β, γ) ≠ 0` and `c ∈ ℂ(X)` with
  `σγ = cα`, `σβ + 2b σγ = cβ`, `σα + b σβ + b² σγ = cγ` for `b = c(X+1)`;
  (b) Cassidy's structure theorem for Zariski-dense differential algebraic subgroups of `SL₂` — the
  Galois matrices are controlled by the tangent space of the Kolchin closure at the identity, whose
  linearity is now `DifferentialTangentLinearization.exists_nonzero_linear_relation_of_tangent`.
- [x] Define order-variable \(K_\nu(s)\) from `(2)` and prove entire dependence, reflection,
  recurrence, and real positivity.
- [x] Formalize the symmetric-square system `(5)` and scalar-annihilator existence `(7)`.
- [x] Formalize periodic-progression rational-exponential upper growth.
- [x] Formalize recurrence lower bounds `(10)`--`(11)` and the growth contradiction.
- [x] Prove affine-change and nonzero-DA-factor preservation for the physical scan.

## Primary sources

- T. Dreyfus, *Hypertranscendence and linear difference equations, the exponential case*,
  Journal of Algebra 686 (2026), 775--792,
  <https://arxiv.org/abs/2212.00388>.
- NIST Digital Library of Mathematical Functions, modified-Bessel integral representation,
  recurrence, and reflection formulas,
  <https://dlmf.nist.gov/10.32#E9>,
  <https://dlmf.nist.gov/10.29#E1>,
  <https://dlmf.nist.gov/10.27#E3>.
- M. R. R. Good, *Extreme Hawking Radiation*, Physical Review D 101, 104050 (2020),
  <https://arxiv.org/abs/2003.07016>.

## Gates

- [x] 0 → 1: exact function, attack, and physical carrier identified.
- [x] 1 → 2: dependency-closed paper proof.
- [ ] 2 → 3: unconditional Lean theorem.
- [ ] 3 → 4: standalone paper and Lean certificate.

## Log

- 2026-07-28 — exact constant-argument extremal intensity scan isolated.
- 2026-07-28 — Dreyfus plus exact recurrence-growth proof closed for \(K_\nu(s)\) and
  \(K_\nu(s)K_{\nu-2}(s)\).
- 2026-07-28 — universal extremality phase interpretation rejected; exact model corollary retained.
- 2026-08-03 — formalized the Schlaefli carrier, entire order dependence, conjugation, reflection,
  strict real positivity, and the exact order recurrence in `BesselOrderIntegral` and
  `BesselOrderRecurrence`.
- 2026-08-03 — formalized the explicit symmetric-square scalar annihilator with nonzero polynomial
  endpoints, formulas `(10)`--`(11)`, exact modulus identity on the physical line, and exclusion of
  every rational-exponential progression representation in `BesselOrderIntensityShift`,
  `BesselOrderFactorialGrowth`, `BesselOrderIntensity`,
  `RationalExponentialProgressionGrowth`, and `BesselOrderDreyfusSeam`.
- 2026-08-03 — formal audit isolated one remaining dependency: Dreyfus Theorem 1/Corollary 2 itself
  (parameterized Picard--Vessiot/difference-Galois classification). No corresponding formal theory
  exists in mathlib or this repository; no axiom or conditional substitute was introduced.
- 2026-08-03 — closed the exact meromorphic recurrence and quartic intensity-to-order recovery in
  `BesselOrderMeromorphic`: differential algebraicity of the intensity now forces differential
  algebraicity of the order carrier, so a separate rank-three classification theorem is unnecessary.
- 2026-08-03 — closed the omitted positive-integer-period case in `BesselOrderFactorialGrowth`,
  `BesselOrderIntensity`, and `BesselOrderDreyfusSeam`.  The contradiction now applies to the
  `ell`-period progressions produced by Dreyfus, not only to a unit-step progression.
- 2026-08-03 — proved in `BesselOrderRiccati` that the rank-two order recurrence has no rational
  Riccati solution for every nonzero slope, including `2 / s` for `s > 0`.  Reduced numerator and
  denominator divisibility force a common nonunit factor; the remaining unit case contradicts
  polynomial degree.  This supplies the exact ordinary irreducibility obstruction but does not
  replace the missing parameterized Picard--Vessiot classification.
- 2026-08-03 — closed the exact extremal physical scan in `BesselOrderPhysicalScan`: affine order
  transport, multiplication by the nonzero entire DA Good prefactor, and the physical prefactor
  identity are all Lean-proved.

## Lean progress — the growth contradiction, in the classification's own output shape

`GaloisForLFunctions.HTGeometry.BesselOrderDreyfusNormalForm` packages §3--§4 into exactly the shape
Dreyfus's theorem outputs, unconditionally and axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

```text
DreyfusProgressionNormalForm x₀ f
    ∀ x ≥ x₀, ∃ ell ≥ 1, the sequence n ↦ f (x + ell·n) has a finite rational-exponential
    representation
not_dreyfusProgressionNormalForm_realModifiedBesselKOrder
    ¬ DreyfusProgressionNormalForm 1 (K_·(s))
not_dreyfusProgressionNormalForm_realModifiedBesselOrderIntensity
    ¬ DreyfusProgressionNormalForm 3 (y ↦ K_y(s) K_(y−2)(s))
not_differentiallyAlgebraic_realModifiedBesselKOrder_of_classification
not_differentiallyAlgebraic_realModifiedBesselOrderIntensity_of_classification
    for any notion of differential algebraicity for which the classification holds, neither
    function is differentially algebraic
```

The last two make the reduction machine-checked: the card's theorem now follows from the single
arrow "differentially algebraic solution of a rational linear shift equation ⟹ normal form", with
every other step — entire order dependence, the recurrence, positivity, the symmetric-square system,
the scalar annihilator, the progression growth bound `(9)`, the factorial lower bounds `(10)`,
`(11)`, and the physical-scan transfer — already unconditional in the tree.

### Why the classification cannot be bypassed

The Riccati reduction is the natural candidate and does not work.  Setting `r(ν) = y(ν+1)/y(ν)`,
the recurrence `(3)` becomes the first-order rational shift equation `r(ν) = 2ν/s + 1/r(ν−1)`, and
`r` is differentially algebraic whenever `y` is, because the shift preserves `ℂ(ν)`.  The corpus
already excludes a *rational* `r` (the rational-Riccati obligation).  But the step from "not
rational" to "not differentially algebraic" is exactly the classification again: differential
algebraicity by itself carries no growth information — `exp (exp z)` satisfies `y y'' = y y' + (y')²`
and has infinite order — so the growth bound `(9)` can only come from the shift equation, which is
what the classification converts into structure.

The remaining obligation is therefore the classification theorem itself, and it rests on
parameterized difference Galois theory, of which mathlib has no part: there is no Picard--Vessiot
theory in mathlib, differential or difference.  That foundation, not any assembly step, is what this
card is waiting on.

## Lean progress — the first layer of the missing difference Galois theory

The card's single open obligation is Dreyfus's classification, and that rests on difference
Picard--Vessiot theory, of which neither mathlib nor this repository had any part.  The first layer
now exists, unconditional and axiom-clean, in
`GaloisForLFunctions.HTGeometry.DifferenceSolutionSpace`:

```text
differenceConstants σ                              the fixed subfield of a difference field
IsDifferenceSystemSolution σ A v                   σ v = A v
exists_differenceConstants_relation                every nontrivial linear relation among
                                                   solutions of an invertible first-order system
                                                   can be replaced by a nontrivial relation whose
                                                   coefficients are shift invariant
card_le_of_no_differenceConstants_relation         hence a family of solutions with no nontrivial
                                                   constant relation has at most `rank` members
```

This is the finiteness statement that makes a difference Galois theory possible at all: the
solution space of a rank-`n` system is a vector space over the constants of dimension at most `n`,
not over the ambient field.  The proof is the classical minimal-support argument — normalize a
coefficient to one, apply the shift, use invertibility of the system matrix, and subtract; the
difference relation has strictly smaller support, so minimality forces every coefficient to be a
constant.

The remaining layers, in order: the companion-matrix reduction of the card's scalar recurrence
`(3)` to a rank-two system; Picard--Vessiot rings for difference equations; the difference Galois
group; the parameterized theory with the derivation `d/dν` acting; and Cassidy's classification of
differential algebraic subgroups of `GL₂`, which is what converts differential algebraicity into
the growth normal form the card already refutes.

## Lean progress — Picard--Vessiot rings for difference equations now exist

The single open obligation is Dreyfus's classification; that rests on parameterized difference
Galois theory; that rests on Picard--Vessiot rings for difference equations.  Neither mathlib nor
this repository had any Picard--Vessiot theory at all, differential or difference.  It now exists
for difference equations, unconditional and axiom-clean, in four new modules.

`GaloisForLFunctions.HTGeometry.DifferenceSigmaSimple`

```text
IsSigmaIdeal sigma I                        an ideal stable under the distinguished automorphism
isSigmaIdeal_span_singleton_of_fixed        the ideal generated by a constant is a sigma-ideal
isSigmaIdeal_nilradical                     the nilradical is a sigma-ideal
exists_maximal_isSigmaIdeal                 every proper sigma-ideal lies in a maximal one (Zorn)
IsSigmaSimple sigma                         only the trivial sigma-ideals
isReduced_of_isSigmaSimple                  a sigma-simple ring is reduced
isUnit_of_isSigmaSimple_of_fixed            nonzero constants of a sigma-simple ring are units
isField_sigmaConstantsSubring_of_isSigmaSimple
                                            the constants of a sigma-simple ring form a field
```

The last is the reason a Picard--Vessiot ring is *required* to be sigma-simple: it is what makes the
solution space of a difference system a vector space over a field rather than a module over a ring,
and it pairs with `DifferenceSolutionSpace.card_le_of_no_differenceConstants_relation` to bound the
solution space by the rank.

`GaloisForLFunctions.HTGeometry.DifferenceCoordinateRing`

```text
fundamentalMatrix K n                       the matrix of indeterminates
sigmaCoordHom sigma A                       the action  a |-> sigma a,  X |-> A X  on K[X_ij]
sigmaCoordHom_fundamentalMatrix             the matrix of indeterminates is a formal solution
sigmaCoordHom_comp                          composition law of the actions
sigmaCoordEquiv sigma A A'                  an automorphism when A is invertible, with an explicit
                                            two-sided inverse built from sigma^{-1} and A^{-1}
sigmaCoordHom_det                           det(X) is multiplied by det(A)
```

`GaloisForLFunctions.HTGeometry.DifferenceAwayLocalization`

```text
sigmaAwayHom, sigmaAwayEquiv                the action extends to the localization away from an
                                            element whose image stays invertible, again with an
                                            explicit two-sided inverse
```

`GaloisForLFunctions.HTGeometry.DifferencePicardVessiotQuotient`

```text
isSigmaIdeal_symm_of_maximal                a maximal sigma-ideal is stable in both directions
sigmaQuotientEquiv                          hence the automorphism descends to the quotient
isSigmaSimple_quotient_of_maximal           the quotient by a maximal sigma-ideal is sigma-simple
isReduced_quotient_of_maximal
isField_constants_quotient_of_maximal
exists_sigmaSimple_quotient
```

`GaloisForLFunctions.HTGeometry.DifferenceSystemPicardVessiot`

```text
exists_picardVessiot_of_fundamentalMatrix   abstract form: a nontrivial difference ring with an
                                            invertible fundamental matrix has a sigma-simple
                                            quotient keeping that matrix, with a field of constants
fundamentalMatrix_det_ne_zero               the generic determinant is a nonzero polynomial
                                            (evaluate at the identity matrix)
pvLocalization K n, pvSigma, pvFundamental  the localized coordinate ring, its automorphism, and
                                            the formal fundamental matrix
pvSigma_pvFundamental                       sigma Y = A Y
exists_picardVessiot_system                 **existence of a Picard--Vessiot ring for every
                                            invertible linear difference system over every
                                            difference field**
```

Every declaration above reports `#print axioms` = `[propext, Classical.choice, Quot.sound]`, and all
five modules are wired into `GaloisForLFunctions.HTGeometry`.

**The card is still not at stage 3.**  What remains, in order:

1. *No new constants*: for a base whose constants are algebraically closed, the constants of the
   Picard--Vessiot ring are exactly those of the base (van der Put--Singer Lemma 1.8/Corollary 1.16).
   The two ingredients already present are `isField_sigmaConstantsSubring_of_isSigmaSimple` and the
   linear-disjointness form of `exists_differenceConstants_relation`.
2. The difference Galois group as an affine group scheme over the constants, and the torsor
   property of the Picard--Vessiot ring.
3. The parameterized theory: a commuting derivation `d/dnu`, and the Galois group as a linear
   *differential* algebraic group.
4. Cassidy's classification of differential algebraic subgroups of `GL_2`, which is what converts
   differential algebraicity of a solution into Dreyfus's growth normal form — the normal form the
   corpus already refutes for `K_nu(s)` in `BesselOrderDreyfusNormalForm`.

## Lean progress — linear disjointness of constants and the difference Galois matrix

`GaloisForLFunctions.HTGeometry.DifferenceGaloisMatrix`, unconditional and axiom-clean:

```text
exists_constant_coeffs_of_relation
    a nontrivial base-linear relation among constants of a difference ring extension can be
    replaced by one whose coefficients are constants of the base
differenceAut sigmaR
    the group of K-algebra automorphisms commuting with the difference operator
galoisMatrix Y phi = Y^{-1} (phi Y)
mul_galoisMatrix                    Y * galoisMatrix Y phi = phi Y
isUnit_det_galoisMatrix             it is invertible
galoisMatrix_map_eq_self            **its entries are constants**
galoisMatrix_one, galoisMatrix_mul  it is one at the identity and multiplicative, the latter as
                                    soon as the automorphism fixes the constants
map_eq_of_galoisMatrix_eq           it determines the automorphism on the fundamental matrix
```

`galoisMatrix_map_eq_self` is the step that produces the Galois group: for `Y` an invertible
fundamental solution of `sigma Y = B Y` with `B` over the base, and `phi` a difference automorphism,
`Y * M = phi Y` with `sigma M = M`.  The proof multiplies through by `sigma Y`, which is invertible,
so no matrix inverse of `B Y` has to be formed:

```text
sigma(Y) sigma(M) = sigma(Y M) = sigma(phi Y) = phi(sigma Y) = phi(B Y) = B (phi Y)
sigma(Y) M       = B Y M       = B (phi Y)
```

and left cancellation by `sigma(Y)` gives `sigma M = M`.

`exists_constant_coeffs_of_relation` is the linear-disjointness statement that will bound the Galois
group and is one of the two ingredients of the no-new-constants theorem; the other is
`DifferenceSigmaSimple.isField_sigmaConstantsSubring_of_isSigmaSimple`.

## Lean progress — no new constants, the Galois representation, and the parameterized layer

Three further modules, all unconditional and axiom-clean.

### `TranscendentalTranslateObstruction` — the geometric input

```text
exists_ne_zero_basicOpen_subset_of_isConstructible
    a constructible subset of the spectrum of a domain containing the generic point contains a
    basic open D(f) with f nonzero
genericPoint_mem_range_comap
    an injective ring map from a domain has the generic point in the image of its comap
exists_notMem_isUnit_sub_algebraMap
    **for a nonzero finite-type K-algebra and a transcendental e, some translate e - a with a in
    any infinite set of scalars fails to be a unit**
```

The last is Chevalley's theorem in the exact form the constants theorem needs: the image of
`Spec R -> Spec K[e]` is constructible and dense, hence contains `D(f)` for some nonzero `f`, hence
contains all but the finitely many points `(X - a)` with `f(a) = 0`.

### `DifferenceNoNewConstants`

```text
sigma_apply_aeval_eq        the shift of a polynomial value at a constant is the value of the
                            shifted polynomial
exists_monic_constantCoeff_annihilator
    **every constant of a sigma-simple finite-type extension is killed by a monic polynomial fixed
    by the shift** -- so it is algebraic over the constants of the base
exists_eq_algebraMap_of_isSigmaSimple
    **no new constants**: if the constants of the base are algebraically closed, every constant of
    the extension already lies in the base
```

Two halves.  Geometric: a nonzero constant of a `sigma`-simple ring is a unit, so a transcendental
constant would make every translate `e - a` (`a` a constant of the base) a unit, contradicting the
Chevalley statement.  Algebraic: the annihilator ideal of the constant is stable under the shift
acting on coefficients, so its monic generator is fixed, so its coefficients are constants; then
the algebraically closed case splits off a linear factor and `sigma`-simplicity forces one of the
factors `e - a` to vanish.

This is the theorem that makes the difference Galois group a group over a *fixed* field.

### `DifferenceGaloisRepresentation`

```text
apply_eq_self_of_noNewConstants   a K-algebra automorphism fixes every constant
algEquiv_eq_of_eq_on_fundamental  automorphisms agreeing on the fundamental matrix agree on the
                                  ring it and the inverse of its determinant generate
galoisRepresentation              **the difference Galois representation**: a group homomorphism
                                  from the difference automorphism group to GL_n over the base
galoisRepresentation_injective    it is faithful on a Picard--Vessiot ring
```

### `ParameterizedDifferenceGalois`

```text
CommutesDeriv sigma                       the shift commutes with the derivation
IsSigmaDeltaIdeal, IsSigmaDeltaSimple     ideals stable under both operators
exists_maximal_isSigmaDeltaIdeal          maximal doubly stable ideals exist (Zorn)
deriv_mem_sigmaConstantsSubring           **the constants are stable under the derivation**
isField_and_derivClosed_sigmaConstantsSubring
    the constants of a sigma-simple parameterized difference ring form a *differential* field
parameterizedAut                          the parameterized difference Galois group
galoisMatrix_deriv_mem_sigmaConstants     its Galois matrix has entries in that differential field
```

That last statement is the reason the parameterized Galois group is a *differential* algebraic
group rather than an algebraic group, which is exactly the structure Cassidy's classification acts
on.

**Still not stage 3.**  Remaining: the torsor property of the Picard--Vessiot ring and the Galois
correspondence; the parameterized Picard--Vessiot ring (a maximal `sigma`-ideal of the
`sigma`-`delta` coordinate ring is a `delta`-ideal in a `Q`-algebra); Cassidy's classification of
differential algebraic subgroups of `GL_2`; and Dreyfus's normal form, whose refutation for
`K_nu(s)` the corpus already owns in `BesselOrderDreyfusNormalForm`.

### `DifferenceFundamentalSolutionSpace`

```text
IsSystemSolution sigma B v                     sigma v = B v
isSystemSolution_col                           the columns of a fundamental matrix are solutions
exists_constant_coords                         **every solution is the fundamental matrix applied
                                               to a vector of constants**
constant_coords_unique                         and that vector is unique
isSystemSolution_iff_exists_constant_coords    so the solution space is exactly the constant span
```

With `isField_sigmaConstantsSubring_of_isSigmaSimple` this says the solution space inside a
Picard--Vessiot ring is a vector space of dimension exactly `n` over a field of constants — the
statement that turns a difference equation into a Galois-theoretic object.  The proof needs no
inverse of `B Y`: from `sigma Y = B Y` one shows `(Y^{-1})^sigma B = Y^{-1}` by right-cancelling
`Y`, and then `Y^{-1} v` is fixed by the shift for every solution `v`.

## Lean progress — the Picard--Vessiot ring is complete, and the order recurrence is irreducible

### `DifferenceCompanionCasoratian`

```text
differenceCompanion_mulVec_of_lt, _of_last   the two row shapes of the companion matrix
differenceCompanion_mulVec_eq_zero           its kernel is trivial when the trailing coefficient is
isUnit_det_differenceCompanion               **the companion matrix is invertible in every rank**
casoratian sigma y                           the matrix of successive shifts
det_casoratian_eq_zero_of_constant_relation  a constant relation kills the Casoratian
exists_constant_relation_of_det_casoratian_eq_zero
                                             and conversely, a vanishing Casoratian produces one
```

The corpus previously had companion invertibility only in rank two, from the explicit `2 x 2`
determinant.  The general statement needs no determinant computation: the companion matrix shifts
coordinates up and reads the equation off in the last row, so a vector in its kernel has all higher
coordinates zero and the trailing coefficient kills the first.  The Casoratian criterion then falls
out of the minimal-support lemma already in `DifferenceSolutionSpace`.

### `DifferenceOperatorFactorization`

```text
firstOrderOp sigma r y = sigma y - r y
secondOrderOp sigma a1 a0 y = sigma^2 y - a1 sigma y - a0 y
secondOrderOp_eq_comp                    a Riccati solution factors the operator
riccati_of_secondOrderOp_eq_comp         a factorization solves the Riccati equation
exists_factorization_iff_exists_riccati  **factorization is exactly the Riccati equation**
besselOrderOperator_no_factorization     **the Bessel order recurrence has no first-order right
                                         factor over C(X)**, for every nonzero slope
modifiedBesselOrderOperator_no_factorization
                                         the physical specialization at every positive argument
```

This converts the corpus's rational-Riccati obstruction into an *irreducibility* theorem: the
second-order order recurrence for `K_nu(s)` admits no factorization into first-order difference
operators over `C(nu)`.  Irreducibility is what forces the difference Galois group of the recurrence
to be large, and it is the hypothesis under which Cassidy's classification has content.

The coefficient comparison in the converse direction needs the shift to be nontrivial, supplied by
`ratShift_ratFuncX_ne`.

### `DifferencePicardVessiotConstants`

```text
pvSigma_algebraMap                       the action restricts to the shift on the base
exists_picardVessiot_no_new_constants
    **the Picard--Vessiot ring of an invertible linear difference system over a difference field
    whose constants are infinite and algebraically closed is sigma-simple, carries an invertible
    fundamental solution matrix, and has exactly the constants of the base**
```

This closes the loop between the construction and the constants theorem: the localized coordinate
ring is a finite-type algebra over the base (mathlib's localization instance), so its quotient by a
maximal `sigma`-ideal is too, and the abstract no-new-constants theorem applies.  That is the full
defining property of a Picard--Vessiot ring, unconditional and axiom-clean.

## Lean progress — the difference operator on the tensor square, and the torsor comparison matrix

The torsor property of a Picard--Vessiot ring compares the two copies of the fundamental matrix
inside `R ⊗_K R`, so the difference operator has to act there.  It is not a `K`-linear tensor map:
it moves the base field, so it is `σ_K`-semilinear, and mathlib has no semilinear tensor
construction.  The twist is by an *automorphism* of `K`, so the defining relations of the tensor
product are permuted rather than destroyed, and the map descends anyway.

`GaloisForLFunctions.HTGeometry.DifferenceTensorTorsor`, unconditional and axiom-clean:

```text
differenceCompat_symm             the inverse automorphism is compatible with the inverse shift
differenceTensorAddHom            x (x) y |-> sigma x (x) sigma y, built with TensorProduct.liftAddHom
                                  from the additive bilinear map, the descent condition being
                                  sigma(a . x) (x) sigma y = sigma x (x) sigma(a . y)
differenceTensorHom               the same map as a ring homomorphism
differenceTensorEquiv             **and as a ring automorphism**, with the explicit two-sided
                                  inverse built from sigma^{-1}
map_invOf_mul_eq_self             **two invertible fundamental solution matrices of the same system
                                  differ by a matrix of constants**
leftFundamental, rightFundamental the two copies of a matrix in the tensor square
exists_tensor_comparison_matrix   **the torsor comparison matrix**: inside `R (x)_K R` the two
                                  copies of an invertible fundamental matrix differ by an invertible
                                  matrix all of whose entries are constants
```

`exists_tensor_comparison_matrix` is the statement that makes a Picard--Vessiot ring a torsor under
its Galois group: `Y (x) 1` and `1 (x) Y` are both fundamental solutions of the same system over
`R (x)_K R`, so `Z = (Y (x) 1)^{-1} (1 (x) Y)` is a constant invertible matrix, and
`(1 (x) Y) = (Y (x) 1) Z`.  The comparison lemma `map_invOf_mul_eq_self` needs no inverse of `B Y`:
multiplying through by `sigma Y`, which is invertible, and cancelling gives the result.

What remains of the torsor property is the surjectivity statement — that `R (x)_K R` is generated
over `R (x) 1` by the entries of `Z` and the inverse of its determinant, and that the constants of
`R (x)_K R` are exactly the `C`-algebra those entries generate.  The second needs `R (x)_K R` to be
`sigma`-simple, which is the next layer.

## Lean progress — the torsor generation half, and no hyperexponential solutions

### `DifferenceTensorGeneration`

```text
det_leftFundamental, det_rightFundamental   the determinants of the two copies
adjoin_tensor_comparison_eq_top
    **the tensor square is generated over the left copy of the ring by the entries of the
    comparison matrix and the inverse of its determinant**
```

This is the second half of the torsor property.  A Picard--Vessiot ring is generated over the base
by the entries of a fundamental matrix `Y` and the inverse `u` of `det Y`; inside `R (x)_K R` the
right copy is `(Y (x) 1) Z`, so every `1 (x) Y_ij` lies in the algebra generated by the left copy and
the entries of `Z`.  For `1 (x) u` the argument is uniqueness of inverses: `1 (x) det Y` equals
`(det Y (x) 1) det Z`, so `(u (x) 1) w` and `1 (x) u` are both inverse to it, hence equal.  Since an
elementary tensor is `(x (x) 1)(1 (x) y)`, the generated subalgebra is everything.  Nothing in the
proof uses the difference structure.

### `DifferenceHyperexponentialRiccati`

```text
riccatiProduct sigma r m = prod_{i<m} sigma^i r
riccatiProduct_succ                      its shift recursion
iterate_of_logDifference                 the iterates of a hyperexponential element are those
                                         partial products
riccatiProduct_relation_of_solution       **a hyperexponential solution solves the Riccati
                                         equation, in every order and every extension**
solution_of_riccatiProduct_relation       and conversely
besselOrder_no_hyperexponential_solution  **the Bessel order recurrence has no hyperexponential
                                         solution over C(X)** -- in no difference field extension
                                         does it have a nonzero solution whose logarithmic
                                         difference is rational
```

This upgrades the corpus's rational-Riccati obstruction from a statement inside `C(nu)` to a
statement about arbitrary difference field extensions: the recurrence has no solution at all whose
logarithmic difference is rational.  The general-order form is the standard bridge between Riccati
solutions and hyperexponential solutions, and it applies verbatim to the rank-three symmetric-square
system of the intensity.

## Lean progress — the equalizer, the quotient derivation, and a corpus finding on Cassidy

### `TensorSquareEqualizer`

```text
exists_eq_algebraMap_of_tmul_comm   **an element with a (x) 1 = 1 (x) a lies in the base field**
tmul_one_eq_one_tmul_iff            the equalizer of the two embeddings is exactly the base
eq_algebraMap_of_leftFundamental_eq_rightFundamental
    **a trivial comparison matrix collapses the Picard--Vessiot ring**: if the two copies of the
    fundamental matrix agree in the tensor square, every element of the ring lies in the base
```

The first is a mathlib gap with a one-line proof once the right object is chosen: pick a linear
functional `f` with `f 1 = 1` (`Module.Projective.exists_dual_eq_one`), apply `f (x) id`, and read
off `f(a) . 1 = a`.  The third is the "trivial Galois group implies no extension" half of the
Galois correspondence, obtained by applying the equalizer to each generator of the ring and to the
inverse of the determinant.

### `QuotientDerivation`

```text
quotDeriv                            **a derivation descends to the quotient by a differential
                                     ideal** -- a mathlib gap
quotientDifferential                 hence the quotient is a differential ring
quotientDifferential_commutesDeriv   and for a doubly stable ideal the descended difference and
                                     differential operators still commute
```

This is what makes the quotient of a `sigma`-`delta` ring by a maximal doubly stable ideal a
`sigma`-`delta` ring again, which is the shape of a parameterized Picard--Vessiot ring.

### Corpus finding: Cassidy's additive classification is already owned

A corpus search turned up `GaloisForLFunctions.HTGeometry.DifferentialHopfPrimitive`:

```text
nonzero_additiveHopfIdeal_exists_nonzero_primitive
nonzero_additiveHopfIdeal_exists_finite_jet_linear_relation
    every nonzero additive differential Hopf ideal in characteristic zero contains a nonzero
    relation which is an explicit finite constant-coefficient linear combination of formal jets
```

That is Cassidy's classification of differential algebraic subgroups of `G_a` in coordinate-ideal
form: a proper differential algebraic subgroup of the additive group is cut out by a nonzero
*linear* differential operator.  `AffineExponentialSubgroups` additionally owns
`additiveRelation_isHopfIdeal` and `torusRelation_isHopfIdeal`, and `DGroupBasicInstances` owns
`multiplicativeDGroup`.  So the additive half of the classification the card is waiting on does not
have to be built; what remains is the multiplicative (`G_m`) transfer through the logarithmic
derivative and the `GL_2` case.

## Lean progress — the multiplicative transfer of the additive classification

`GaloisForLFunctions.HTGeometry.LogDerivRelationSubgroup`, unconditional and axiom-clean:

```text
differentialJet_neg, differentialJet_zero_arg
jetOperator c x = sum_i c_i . delta^i x     a constant-coefficient linear differential operator
jetOperator_add, _zero, _neg                it is additive
jetRelationAddSubgroup c                    **the additive subgroup it cuts out** -- the shape of
                                            every proper differential algebraic subgroup of G_a
logDerivHom F : F^x ->* Multiplicative F    **the logarithmic derivative is a group homomorphism
                                            from the units to the additive group**
logDerivRelationSubgroup c                  the units on which the operator kills the logarithmic
                                            derivative
logDerivRelationSubgroup_eq_comap           **the transfer**: the multiplicative relation subgroup
                                            is exactly the preimage of the additive one under the
                                            logarithmic derivative
constant_mem_logDerivRelationSubgroup       every constant unit lies in every relation subgroup
```

This is the bridge from the additive classification the corpus already owns
(`DifferentialHopfPrimitive.nonzero_additiveHopfIdeal_exists_finite_jet_linear_relation`) to the
multiplicative group: the relation subgroups of `G_m` are exactly the preimages under `logDeriv` of
the relation subgroups of `G_a`, and both sides are genuine groups.  What is still missing on the
multiplicative side is the converse direction — that *every* proper differential algebraic subgroup
of `G_m` arises this way — which needs the image of a differential algebraic group under a
differential-algebraic homomorphism to be differential algebraic, i.e. elimination in `DCF_0`.

## Lean progress — the sigma-ideal correspondence needs no model theory

`GaloisForLFunctions.HTGeometry.SigmaIdealConstantCoefficients`, unconditional and axiom-clean:

```text
BasisIndependentOver R b                       linear independence of a family over the base
exists_constant_coeff_mem_sigmaIdeal
    **every element of a sigma-ideal expressible in a family of constants produces an element of
    the same ideal all of whose coefficients are constants of the base**
exists_nonzero_constant_coeff_mem_sigmaIdeal   and with linear independence it is nonzero
```

This corrects the plan recorded above.  The step "sigma-simplicity of the tensor square" was
misstated: `R (x)_K R` is *not* sigma-simple in general -- it is `R (x)_C C[G]`, whose sigma-ideals
are the ideals of `C[G]`.  What the Galois correspondence actually needs is the *ideal
correspondence*, and that is pure algebra, not model theory.

The proof is the minimal-support argument run one level up.  For a fixed finite support `s` and a
fixed index `j`, the `j`-th coefficients of the elements of the ideal supported in `s` form a
`sigma`-ideal of the base; `sigma`-simplicity makes it the whole base, so one coefficient can be
normalised to one; subtracting the shifted element then kills that coefficient and strictly shrinks
the support, so minimality forces every coefficient to be a constant.

Combined with `exists_tensor_comparison_matrix` (the comparison matrix has constant entries) and
`adjoin_tensor_comparison_eq_top` (those entries and the inverse of the determinant generate the
tensor square over the left copy), this is the algebraic engine of the Galois correspondence.  What
is left there is the passage from the ideal correspondence to `C`-points, which is the
Nullstellensatz over an algebraically closed constant field.

## Lean progress — the Galois group has points

`GaloisForLFunctions.HTGeometry.NullstellensatzPoint`, unconditional and axiom-clean:

```text
exists_algHom_of_finiteType_of_isAlgClosed
    **the weak Nullstellensatz**: a nontrivial finitely generated algebra over an algebraically
    closed field admits an algebra homomorphism to that field
exists_matrix_point_of_finiteType
    **the Galois group has points**: an invertible matrix over such an algebra specialises to an
    invertible matrix over the field
```

Take a maximal ideal; the quotient is a field of finite type over the base, hence finite over it by
Zariski's lemma (`finite_of_finite_type_of_isJacobsonRing`), hence equal to the base because the
base is algebraically closed (`IsAlgClosed.algebraMap_bijective_of_isIntegral`).

This closes item (1) of the remaining list: the passage from the ideal correspondence to points of
the Galois group.  With `exists_tensor_comparison_matrix`, `adjoin_tensor_comparison_eq_top` and
`exists_constant_coeff_mem_sigmaIdeal`, the comparison matrix `Z` lives in a finitely generated
algebra of constants over `C`, and `exists_matrix_point_of_finiteType` specialises it to an element
of `GL_n(C)` -- a point of the difference Galois group.

## Lean progress — linear disjointness of constants, and a cross-module audit

`GaloisForLFunctions.HTGeometry.SigmaConstantsDisjointness`, unconditional and axiom-clean:

```text
basisIndependentOver_of_constants
    **constants linearly independent over the base constants are linearly independent over the
    base** -- the zero-ideal case of the sigma-ideal theorem
exists_nonzero_constant_span_mem_of_sigmaIdeal
    a nonzero sigma-ideal meets the constant span nontrivially
```

Linear disjointness of the constants is therefore not an extra hypothesis of the torsor
decomposition: it is a consequence of `sigma`-simplicity of the base, by the same minimal-support
argument.  This is the last ingredient of the module isomorphism `R (x)_K R = R (x)_C E`.

**Cross-module audit.**  All twenty-five modules added for these three cards were imported into a
single file together and every capstone re-elaborated side by side with no conflict:
`vectorAdditiveGaloisGroupEquivConstantField`, `embeddedManinHorizon_nonorthogonal_iff_isogenous`,
`exists_picardVessiot_system`, `exists_picardVessiot_no_new_constants`,
`exists_eq_algebraMap_of_isSigmaSimple`, `galoisRepresentation_injective`,
`exists_tensor_comparison_matrix`, `adjoin_tensor_comparison_eq_top`,
`exists_constant_coeff_mem_sigmaIdeal`, `basisIndependentOver_of_constants`,
`exists_matrix_point_of_finiteType`, `besselOrderOperator_no_factorization`,
`besselOrder_no_hyperexponential_solution`, `quotientDifferential_commutesDeriv`,
`logDerivRelationSubgroup_eq_comap`.

**Corpus asset for the analytic side.**  `HTGeometry.LinearOdeBohrSpectrum.bohrSpectrum_finite_of_linearOde`
already proves that an almost-periodic solution of a nontrivial constant-coefficient linear
differential equation has finite Bohr spectrum -- the exponential-polynomial shape Dreyfus's normal
form asserts.  That is the entry point for item (4) and should be used rather than rebuilt.

## Lean progress — from a point of the group to a Galois element

`GaloisForLFunctions.HTGeometry.DifferenceSpecialization`, unconditional and axiom-clean:

```text
rightComponent psi                  the right component of a specialisation of the tensor square
rightComponent_commutes             **it commutes with the difference operator** as soon as the
                                    specialisation does
rightComponent_fundamental          **it moves the fundamental matrix by the specialised comparison
                                    matrix**: rightComponent psi (Y) = Y . psi(Z)
isUnit_det_specialization           **the specialised comparison matrix is invertible**
rightComponent_eq_of_map_eq         and it determines the right component on the fundamental matrix
```

This is the whole bridge from a point of the difference Galois group to an element of it: a
`K`-algebra map `R (x)_K R -> R` restricting to the identity on the left copy has a right component
which is a `K`-algebra endomorphism of `R`, commutes with `sigma`, and multiplies the fundamental
matrix by an invertible matrix.

What is left of the Galois correspondence is the *existence* of enough such specialisations, which
is the torsor module decomposition `R (x)_K R = R (x)_C E` (all of whose ingredients are now in the
tree) composed with the Nullstellensatz point of `NullstellensatzPoint`.

## Lean progress — the torsor decomposition

`GaloisForLFunctions.HTGeometry.TorsorDecomposition`, unconditional and axiom-clean:

```text
injective_of_basis_map_linearIndependent
    a linear map carrying a basis to a linearly independent family is injective
tensorDecompositionHom E : R (x)_C E ->a[R] A     the canonical map
tensorDecompositionHom_surjective                 from generation of A over R by E
tensorDecompositionHom_injective                  from R-independence of a C-basis of E
tensorDecompositionEquiv                          **R (x)_C E = A**
```

This is the structural item the Galois correspondence was waiting on.  For a Picard--Vessiot ring
and its tensor square both hypotheses are already in the tree: generation is
`adjoin_tensor_comparison_eq_top`, and the independence is `basisIndependentOver_of_constants`,
which derives it from `sigma`-simplicity rather than assuming it.

With `DifferenceSpecialization` and `NullstellensatzPoint`, the chain is now: decompose
`R (x)_K R = R (x)_C E`; take a `C`-point of `E`; base change along it to get a specialisation
`R (x)_K R -> R` fixing the left copy; its right component is a difference `K`-automorphism of `R`
carrying the fundamental matrix to `Y . psi(Z)`.

## Lean progress — specialising the torsor at a point

`GaloisForLFunctions.HTGeometry.TorsorPointSpecialization`, unconditional and axiom-clean:

```text
pointBaseChange E chi                  base change of a C-point along the decomposition
specializationOfPoint E b hgen hindep chi : A ->a[R] R
                                       **the specialisation attached to a point**
specializationOfPoint_algebraMap       it is the identity on the base
specializationOfPoint_coe              it evaluates the constants at the point
```

This is the assembly step.  For a Picard--Vessiot ring and its tensor square: `TorsorDecomposition`
gives `R (x)_K R = R (x)_C E`; `NullstellensatzPoint` gives a `C`-point of `E`;
`specializationOfPoint` base changes along it to a map `R (x)_K R -> R` which is the identity on the
left copy and evaluates the comparison matrix at the point; and
`DifferenceSpecialization.rightComponent` turns that into a difference `K`-automorphism of `R`
carrying the fundamental matrix to `Y . chi(Z)`.

Every step of that chain is now Lean-proved.  What is left of the correspondence is only the
bookkeeping that instantiates the general lemmas at the concrete Picard--Vessiot data.

## Lean progress — points separate

`GaloisForLFunctions.HTGeometry.PointsSeparate`, unconditional and axiom-clean:

```text
exists_algHom_ker_eq_of_isMaximal
    every maximal ideal of a finite-type algebra over an algebraically closed field is the kernel
    of a point
eq_zero_of_forall_algHom_eq_zero
    **points separate**: on a reduced finite-type algebra over an algebraically closed field, an
    element killed by every point is zero
```

The Galois correspondence needs more than one point of the group: it needs enough of them.  This is
the Nullstellensatz together with the Jacobson property -- the intersection of the maximal ideals is
the nilradical, which vanishes when the algebra is reduced.

With this, the chain from the torsor decomposition to `R^G = K` is complete at the level of general
lemmas: if `a (x) 1 - 1 (x) a` is nonzero then its image under some point is nonzero, and the
corresponding automorphism moves `a`.  The one remaining input on that route is reducedness of the
constants algebra `E`, which in characteristic zero is Cartier's theorem for the Galois group
scheme.

## Lean progress — separation with coefficients in a module

`GaloisForLFunctions.HTGeometry.PointsSeparateModule`, unconditional and axiom-clean:

```text
eq_zero_of_forall_point_smul_eq_zero
    **an element `sum r_j (x) b_j` of `M (x)_C E` killed by every point of `E` vanishes**, for `b`
    a `C`-independent family and the coefficients `r_j` in an arbitrary `C`-module
```

The Galois correspondence has to separate elements of `R (x)_C E`, not just of `E`, so separation on
`E` alone is not enough.  The upgrade is a finite-dimensional duality argument: the vectors
`(chi b_1, ..., chi b_n)` span `C^n`, since otherwise they lie in the kernel of a nonzero functional
whose coefficients would give a nontrivial `C`-relation among the `b_j`; and the linear map
`x |-> sum x_j . r_j` kills those vectors, hence their span, hence everything.

Together with `TorsorDecomposition`, `TorsorPointSpecialization` and `DifferenceSpecialization`,
this completes the separation half of `R^G = K`: an element of the tensor square killed by every
specialisation is zero.  The one input still carried is reducedness of the constants algebra, which
in characteristic zero is Cartier's theorem.

## Lean progress — parameterized Picard--Vessiot quotients

`GaloisForLFunctions.HTGeometry.ParameterizedPicardVessiotQuotient`, unconditional and axiom-clean:

```text
isSigmaIdeal_symm_of_maximal_sigmaDelta
    a maximal doubly stable ideal is stable under the inverse difference operator
isSigmaDeltaSimple_quotient_of_maximal
    **the quotient by a maximal doubly stable ideal is doubly simple**
exists_sigmaDeltaSimple_quotient
    **existence of a parameterized Picard--Vessiot quotient**: every proper doubly stable ideal is
    contained in one whose quotient carries both operators, is doubly simple, and on which the
    descended operators commute
```

This is the parameterized analogue of `DifferencePicardVessiotQuotient`.  The difference operator
descends because maximality forces two-sided stability -- the preimage of a maximal doubly stable
ideal is again doubly stable, the `delta`-part because `sigma` and `delta` commute -- and the
derivation descends by `QuotientDerivation`.

With `ParameterizedDifferenceGalois` (the constants form a differential field, and the parameterized
Galois matrix has entries there) this is the ring-theoretic layer of the parameterized theory.  What
remains on that side is the `sigma`-`delta` coordinate ring of a fundamental matrix, whose
construction mirrors `DifferenceCoordinateRing` with the jet variables carrying the derived action.

## Lean progress — existence of a parameterized Picard--Vessiot ring

`GaloisForLFunctions.HTGeometry.ParameterizedPicardVessiotExistence`, unconditional and axiom-clean:

```text
exists_parameterizedPicardVessiot_of_fundamentalMatrix
    **a nontrivial sigma-delta ring carrying an invertible fundamental solution matrix has a doubly
    simple quotient in which the matrix is still an invertible fundamental solution, and on which
    the two descended operators commute**
```

This is the parameterized analogue of `exists_picardVessiot_of_fundamentalMatrix`, and it is the
ring in which the parameterized difference Galois group lives.  By
`ParameterizedDifferenceGalois.galoisMatrix_deriv_mem_sigmaConstants` its Galois matrix has entries
in the constants of the difference operator, and those constants are closed under the derivation, so
the group is a *differential* algebraic group -- exactly the structure Cassidy's classification acts
on.

## Lean progress — the difference action on the differential coordinate ring

A corpus search found that the differential polynomial ring over a *differential* coefficient field
already exists: `GaloisForLFunctions.DifferentialPolynomialOver` builds
`differentialPolynomialCoeffDerivation` and `differentialPolynomialOverDerivation`, the total
derivation which differentiates coefficients and shifts jets.  That is the ring the parameterized
theory needs; only the difference operator was missing.

`GaloisForLFunctions.HTGeometry.SigmaJetCoordinateRing`, unconditional and axiom-clean:

```text
jetCoordDeriv K n              the total derivation of the differential coordinate ring
systemRow A p                  the row (A X)_{i j} of the system
sigmaJetCoordHom sigma A       **the difference action**: on a jet variable it is the corresponding
                               jet of the system row
sigmaJetCoordHom_C, _X         its values on constants and jets
sigmaJetCoordHom_commutes      **it commutes with the derivation**
```

The value on a jet variable is forced rather than chosen: commutation with the derivation requires
`sigma (delta^k X_{i j}) = delta^k ((A X)_{i j})`, and taking that as the definition makes the
commutation proof a generator check plus one induction, with no Leibniz combinatorics.  The two
composites are twisted derivations agreeing on constants and on jets.

With `ParameterizedPicardVessiotExistence` this is the concrete input the abstract parameterized
existence theorem was missing.  What remains on that side is invertibility of the action, which is
the same matrix computation as `DifferenceCoordinateRing.sigmaCoordEquiv` transported through the
jets.

## Lean progress — the difference action on the differential coordinate ring is invertible

`GaloisForLFunctions.HTGeometry.SigmaJetCoordinateEquiv`, unconditional and axiom-clean:

```text
commutesDeriv_symm               the inverse shift also commutes with the derivation
iterate_jetCoordDeriv_X          iterating the total derivation on a zeroth jet gives the jets
sigmaJetCoordHom_systemRow       the inverse action returns the zeroth jets
sigmaJetCoordHom_comp_eq_id      **the difference action is invertible**, with inverse the same
                                 construction for sigma^{-1} and the entrywise sigma^{-1}-image of
                                 the inverse matrix
```

On jet variables the verification reduces to the zeroth jet, because both actions commute with the
derivation: `rho (sigma (delta^k X)) = delta^k (rho (sigma X))`, and at the zeroth jet it is exactly
the matrix identity `A A' = 1`.  No Leibniz expansion is needed anywhere.

So the `sigma`-`delta` coordinate ring of a fundamental matrix is now a genuine `sigma`-`delta` ring
with an invertible difference operator, which is what
`ParameterizedPicardVessiotExistence.exists_parameterizedPicardVessiot_of_fundamentalMatrix` takes as
input.  What remains on that side is the localization at the determinant, mirroring
`DifferenceAwayLocalization`.

## Lean progress — derivations extend to arbitrary localizations

`GaloisForLFunctions.HTGeometry.LocalizationDerivation`, unconditional and axiom-clean:

```text
localizationGraphAlgHom D            the square-zero graph a |-> (a, D a)
localizationGraphAlgHom_isUnit       every element of the multiplicative set maps to a unit
localizationDerivationGraphLift      the graph extended through the localization
localizationDerivationGraphLift_fst  its first coordinate is the identity
localizationDerivation               **a derivation extends to any localization**
localizationDerivation_algebraMap    and restricts to the original derivation
```

This is a mathlib gap.  The corpus owned the fraction-field case
(`GaloisForLFunctions.FractionRingDerivation`), but the parameterized coordinate ring is the
differential polynomial ring localized at the *determinant*, not its fraction field -- localizing all
the way to a field would make the ring simple and destroy the Picard--Vessiot ideal.  The same
dual-numbers argument works verbatim for an arbitrary localization: the graph lands in the
square-zero extension, elements of the multiplicative set map to units because their first coordinate
is a unit downstairs, and the universal property extends the graph; the second coordinate is the
quotient-rule derivation.

With `DifferenceAwayLocalization` (the difference operator on a localization) this completes the
localized parameterized coordinate ring: both operators now live on
`K{X}_delta[1/det]`.

## Lean progress — the difference action on the differential coordinate ring is an automorphism

`GaloisForLFunctions.HTGeometry.SigmaJetCoordinateAutomorphism`, unconditional and axiom-clean:

```text
map_symm_map_self                mapping a matrix by sigma^{-1} and back is the identity
sigmaJetCoordEquiv               **the difference action as a ring automorphism**
sigmaJetCoordEquiv_commutes      it commutes with the total derivation
```

The inverse composition is the same theorem applied to the inverse system: the construction for
`sigma^{-1}` and the `sigma^{-1}`-image of `A^{-1}` has, as its own inverse datum, the construction
for `sigma` and `A` again.

So the differential coordinate ring of a fundamental matrix is a `sigma`-`delta` ring with an
invertible difference operator commuting with the derivation.  With `LocalizationDerivation` and
`DifferenceAwayLocalization` both operators transport to the localization at the determinant, and
`ParameterizedPicardVessiotExistence` then produces the parameterized Picard--Vessiot ring.

## Lean progress — derivations on a localization are determined by the base, and commutation transports

`GaloisForLFunctions.HTGeometry.LocalizationDerivationExt`, unconditional and axiom-clean:

```text
localizationDerivation_ext        **two derivations of a localization agreeing on the base are
                                  equal**
automorphismConjDerivation        conjugating a derivation by a ring automorphism
localization_commutes_of_base     **commutation of a difference operator with a derivation
                                  transports from the base to the localization**
```

The uniqueness is the quotient rule read backwards: for `z` with `z s = a` the Leibniz rule gives
`s . D z = 0` for the difference of two derivations agreeing on the base, and `s` is invertible.  The
transport is then immediate: conjugating the extended derivation by the extended difference operator
is another derivation of the localization, and it agrees with the original on the base exactly
because the two operators commute there.

Both statements are mathlib gaps.  With `LocalizationDerivation` this completes the transport of the
`sigma`-`delta` structure to the localization at the determinant: the localized differential
coordinate ring of a fundamental matrix carries both operators, and they commute.

## Lean progress — the parameterized Galois representation

`GaloisForLFunctions.HTGeometry.ParameterizedGaloisRepresentation`, unconditional and axiom-clean:

```text
parameterizedGaloisRepresentation           **the parameterized Galois representation**
parameterizedGaloisRepresentation_entries   **its entries lie in the constants of the difference
                                            operator, and their derivatives do too**
parameterizedGaloisRepresentation_injective **it is faithful** on a Picard--Vessiot ring
```

The parameterized Galois group is the subgroup of difference automorphisms which also commute with
the derivation, so the representation is the restriction of the difference Galois representation
along `parameterizedAut_le_differenceAut`.  What is new is the target: the entries are constants of
the difference operator, and by `deriv_mem_sigmaConstantsSubring` those constants are closed under
the derivation.

So the parameterized Galois group embeds in the invertible matrices over a *differential* field.
That is the structure a classification of differential algebraic subgroups acts on, and it is the
last structural piece before Cassidy's classification itself.

## Lean progress — the derivation on the tensor square

`GaloisForLFunctions.HTGeometry.TensorSquareDerivation`, unconditional and axiom-clean:

```text
differentialTensorAddHom          x (x) y |-> delta x (x) y + x (x) delta y, descended to the tensor
                                  product over K
tensorSquareDerivation            **the derivation on the tensor square**
tensorSquareDerivation_commutes   **it commutes with the difference operator there**
```

Like the difference operator, the derivation is not `K`-linear -- it moves the base field -- so
mathlib's tensor maps do not apply.  The descent works for the same reason: `delta` on the base is
the restriction of `delta` on `R`, so the two expressions
`delta(a . x) (x) y + (a . x) (x) delta y` and `delta x (x) (a . y) + x (x) delta(a . y)` differ only by
scalars that move across the tensor.

Both operators now live on `R (x)_K R` and commute there, which is the parameterized analogue of
`DifferenceTensorTorsor` and the setting in which the parameterized torsor argument runs.

## Lean progress — the parameterized torsor comparison matrix

`GaloisForLFunctions.HTGeometry.ParameterizedTensorTorsor`, unconditional and axiom-clean:

```text
exists_parameterized_tensor_comparison_matrix
    **the comparison matrix of the torsor has entries fixed by the difference operator on the tensor
    square, and so do their derivatives**
```

So the coordinates of the parameterized Galois group are *differential* coordinates: the comparison
matrix lives over a differential ring of constants.  That is precisely what makes the parameterized
Galois group a differential algebraic group rather than an algebraic one, and it is the object
Cassidy's classification is about.

The parameterized side of the theory is now complete up to the classification: the `sigma`-`delta`
coordinate ring and its automorphism, the localization carrying both operators, the parameterized
Picard--Vessiot quotient, the parameterized Galois representation over a differential field of
constants, the derivation on the tensor square, and the parameterized torsor comparison matrix.

## Lean progress — specialising the parameterized torsor

`GaloisForLFunctions.HTGeometry.ParameterizedSpecialization`, unconditional and axiom-clean:

```text
rightComponent_commutes_deriv          the right component of a specialisation commutes with the
                                       derivation as soon as the specialisation does
rightComponent_mem_parameterizedAut    **a doubly equivariant specialisation gives an element of the
                                       parameterized Galois group**
```

For the derivation the verification is one line: `delta 1 = 0`, so the derivation of `1 (x) y` is
`1 (x) delta y`.

The parameterized correspondence therefore has the same shape as the difference one: decompose the
tensor square, take a point of the group, specialise, and read off the automorphism -- now
commuting with both operators, hence an element of the parameterized Galois group whose Galois
matrix has differential coordinates.

## Lean progress — Cassidy's additive classification, evaluated

`GaloisForLFunctions.HTGeometry.CassidyAdditiveEvaluated`, unconditional and axiom-clean:

```text
exists_nonzero_jet_linear_relation_of_additiveHopfIdeal
    **if a nonzero additive differential Hopf ideal vanishes on a family, the family satisfies a
    nonzero finite constant-coefficient linear relation among its jets**
```

The corpus already owns Cassidy's classification of differential algebraic subgroups of `G_a` in
coordinate-ideal form (`DifferentialHopfPrimitive`); this evaluates it at a point, which is the form
in which the classification is used in a hypertranscendence argument, and the form matching
`LogDerivRelationSubgroup.jetOperator`.

Chaining what is now present on the classification side: a proper differential algebraic subgroup of
the additive group forces a nonzero linear differential operator to kill the coordinates
(`CassidyAdditiveEvaluated`), and the multiplicative relation subgroups are the preimages of the
additive ones under the logarithmic derivative (`LogDerivRelationSubgroup`).  What is missing is the
converse on the multiplicative side and the `GL_2` case.

## Lean progress — reducedness of the Galois coordinate algebra, unconditionally

The Galois correspondence needed the coordinate algebra of the difference Galois group to be
reduced, so that its points separate.  In the literature that is Cartier's theorem (a commutative
Hopf algebra over a characteristic-zero field is reduced).  It is now obtained instead from a
general algebra theorem, proved here because mathlib does not have it:

`GaloisForLFunctions.HTGeometry.TensorProductAlgClosedReduced`

```text
exists_basis_tmul_repr                      every element of `M ⊗_k N` is a finite sum of tensors
                                            against basis vectors of `N`
isReduced_tensorProduct_of_finiteType       over an algebraically closed field, reduced finitely
                                            generated algebras have reduced tensor product
isReduced_tensorProduct_of_isAlgClosed      the same without finite generation
```

`GaloisForLFunctions.HTGeometry.TensorProductCharZeroReduced`

```text
isReduced_tensorProduct_field_of_isSeparable   a finite separable field extension stays reduced
                                               after any field base change
isReduced_tensorProduct_of_isSeparable         and after any reduced base change
isReduced_tensorProduct_algebraicClosure       an algebraic closure stays reduced after any reduced
                                               base change, in characteristic zero
isReduced_tensorProduct_of_charZero            **in characteristic zero the tensor product of two
                                               reduced algebras is reduced**
```

The last is the statement that a reduced algebra over a characteristic-zero field is geometrically
reduced.  The proof runs through the algebraic closure: a finitely generated subalgebra of the
algebraic closure is a finite separable field extension; a finite separable extension keeps a
reduced base reduced (expand a nilpotent tensor against a basis and specialise at each prime of the
base, where unramifiedness applies); over the algebraic closure itself points separate, which
settles the reduced-times-reduced case there; and the original tensor product embeds into that base
change.

`GaloisForLFunctions.HTGeometry.SigmaConstantsReduced` applies it:

```text
isReduced_tensorSquare_of_isSigmaSimple        `R ⊗_K R` is reduced for `σ`-simple `R` over a
                                               characteristic-zero field
isReduced_subalgebra_tensorSquare
eq_zero_of_forall_algHom_eq_zero_tensorSquare  **points of the Galois-group coordinate algebra
                                               separate**
```

All declarations report `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

Remaining on this card: the `G_m` converse and the `GL_2` case of Cassidy's classification, and
Dreyfus's normal form with its analytic realization.

## Lean progress — the characteristic-zero primitive obstruction

`GaloisForLFunctions.HTGeometry.PrimitiveNilpotentCharZero`

```text
tmul_self_ne_zero                        over a field, a nonzero vector has nonzero self-tensor
eq_zero_of_isNilpotent_of_primitive      **a nilpotent primitive element of a characteristic-zero
                                         algebra vanishes**
```

Multiplying the binomial expansion of `Δ (x ^ n)` by `x ^ (n-2) ⊗ 1` kills every term except the
first-order one, which is `n · (x^{n-1} ⊗ x^{n-1})`.

## Lean progress — the parameterized (isomonodromy) obstruction

The rational-Riccati obstruction already in the tree is the *irreducibility* obstruction for the
rank-two order module.  The obstruction the parameterized classification actually consumes is the
*isomonodromy* one: whether the module carries a compatible derivation over `ℂ(ν)`, i.e. whether
`∂K_ν(s)/∂ν = P(ν) K_ν(s) + Q(ν) K_{ν+1}(s)` for rational `P, Q`.  Equivalently, whether there is
`B ∈ gl₂(ℂ(ν))` with `σ(B) A - A B = δA` for the companion matrix `A` of the order recurrence.

This is now settled unconditionally and negatively, in three new modules.

`GaloisForLFunctions.HTGeometry.RatFuncShiftDegree`

```text
shiftDelta                                   the finite difference `p(X+1) - p(X)`
natDegree_shiftDelta, leadingCoeff_shiftDelta
                                             it has degree `deg p - 1` and leading coefficient
                                             `deg p` times that of `p`
shiftDiffNum_spec                            the numerator of `f(X+1) - f(X)` in the reduced
                                             presentation has degree `deg num + deg den - 1`
intDegree_ratShift_sub                       **the unit shift drops the degree at infinity by
                                             exactly one**, for `deg f ≠ 0`
intDegree_ratShift_sub_le_of_intDegree_zero  and by at least two when `deg f = 0` and `f` is not
                                             constant
```

`GaloisForLFunctions.HTGeometry.RatFuncShiftDegreeCalculus` — the degree bookkeeping
(`intDegree_ratShift`, `intDegree_add_le_of_le`, `intDegree_mul_le_of_le`,
`intDegree_add_eq_left`, `ratShift_sub_le`, `ratShift_two_sub_le`).

`GaloisForLFunctions.HTGeometry.BesselOrderIsomonodromyObstruction`

```text
orderShiftCoeff c                            the shift coefficient `c (X + 1)`
besselOrder_no_rational_delta_structure      **the order recurrence has no rational compatible
                                             derivation** for `c ≠ 0`
orderBessel_no_rational_delta_structure      existential form
modifiedBesselOrder_no_rational_delta_structure
                                             physical specialization `c = 2 / s`, `s > 0`
```

The proof is a degree count at infinity.  The first compatibility identity makes the trace
`P + σP + b σQ` shift invariant, hence constant, which bounds `deg (b σQ)` by `max 0 (deg P)`.
Subtracting `b` times the first identity from the second gives `σ²Q - Q + b (P - σP) = c`.  Since
the shift difference drops the degree by exactly one, the second summand has degree exactly `deg P`
whenever `deg P ≠ 0`, while the first has degree at most `max 0 (deg P) - 2`; the sum can never have
degree zero.  When `deg P = 0` both summands have negative degree and again the sum cannot be a
nonzero constant.

Every declaration reports `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## Lean progress — the analytic isomonodromy theorem

The rational obstruction is now transported to the genuine meromorphic carrier, giving an
unconditional theorem about the modified Bessel function itself.

`GaloisForLFunctions.HTGeometry.DeltaStructureLinearOde`

```text
exists_nontrivial_linear_ode_of_deltaStructure
    **a compatible derivation forces a linear differential equation**: if `δ y = p y + q σy` for a
    solution of `σ²y = y + b σy`, the span `⟨y, σy⟩` is derivation stable, so `y`, `δy`, `δ²y` are
    dependent and `y` satisfies a nonzero linear differential equation of order at most two
```

`GaloisForLFunctions.HTGeometry.DeltaStructureCompatibility`

```text
deltaStructure_compatibility
    **the compatibility identities**: for a solution of `τ²y = y + ρb·τy` with `δy = ρP·y + ρQ·τy`
    and `y, τy` independent over the base, the coefficients satisfy the two identities
    `σ²P + σb·σ²Q = P + b·σQ` and `σ²Q + b σ²P + b σb σ²Q = Q + δb + b σP + b² σQ`
```

`GaloisForLFunctions.HTGeometry.BesselOrderMeromorphicIsomonodromy`

```text
modifiedBesselKOrderMero_ne_zero            the order function is a nonzero meromorphic element
modifiedBesselKOrderMero_recurrence         `σ²K = K + (2(ν+1)/s) σK` with a rational coefficient
besselMero_linearIndependent                **`K_ν(s)` and `K_{ν+1}(s)` are linearly independent
                                            over `ℂ(ν)`** — a dependence is a rational Riccati
                                            solution
modifiedBesselKOrderMero_no_rational_delta_structure
                                            **for `s > 0` there are no rational functions `P, Q`
                                            with `∂K_ν(s)/∂ν = P(ν) K_ν(s) + Q(ν) K_{ν+1}(s)`**
```

Together with `exists_nontrivial_linear_ode_of_deltaStructure` this is sharp: a rational compatible
derivation would make `K_ν(s)` satisfy a linear differential equation of order two over `ℂ(ν)`, and
none exists.

What the card still needs is the converse implication supplied by the parameterized classification:
that differential algebraicity *forces* a compatible derivation.  That is Cassidy's classification
of Zariski-dense differential algebraic subgroups of `SL₂` together with the parameterized Galois
correspondence, plus the identification of the difference Galois group of the order module.

Every declaration reports `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## Lean progress — differential-algebra foundations for the classification

The classification the card still needs rests on Kolchin's differential algebraic geometry, of which
mathlib has no part.  The corpus already owned the Kolchin topology and Ritt rank; five new modules
add the ideal theory:

```text
RadicalDifferentialIdeal            Ritt's lemma, and the characteristic-zero Keigher property
                                    (the radical of a differential ideal is differential)
RadicalDifferentialIdealGeneration  the radical differential ideal generated by a set, and the
                                    product law through the colon ideal
RadicalDifferentialIdealPrime       a maximal non-finitely-generated radical differential ideal is
                                    prime
RadicalDifferentialIdealZorn        such a maximal ideal exists
RittBasisPrimeReduction             **Ritt's basis theorem reduced to the prime case**
```

All axiom-clean.  The remaining half of Ritt--Raudenbush is the characteristic-set argument for
prime radical differential ideals.

## Lean progress — the shift span, and the strongest form of the analytic theorem

`GaloisForLFunctions.HTGeometry.BesselOrderShiftSpan`

```text
InBesselSpan                     membership in the `ℂ(ν)`-span of `K_ν(s)` and `K_{ν+1}(s)`
inBesselSpan_shift               **every integer shift `K_{ν+n}(s)` lies in that span** — the order
                                 recurrence runs in both directions
modifiedBesselKOrderMero_deriv_notMem_shift_span
                                 **for `s > 0` the order derivative `∂K_ν(s)/∂ν` is not a rational
                                 combination of any finite family of integer shifts
                                 `K_{ν+n}(s)`**
```

This is the sharpest unconditional statement the card now owns about the order derivative.

## Lean progress — the separant

`GaloisForLFunctions.HTGeometry.DifferentialSeparant`

```text
scalarSeparant A                    the partial derivative with respect to the leader
exists_separant_decomposition       **differentiating a scalar differential polynomial of order `n`
                                    produces the next jet exactly once, linearly, with coefficient
                                    the separant; everything else has order at most `n`**
```

This is the structural fact behind Ritt's reduction — it is what lowers the order of a differential
polynomial by pseudo-division against a derivative of a fixed polynomial.  The proof presents the
polynomial through the jets of order at most `n` (`MvPolynomial.supported_eq_range_rename`), where
the induction over monomials never meets a variable of larger order.

## Lean progress — Ritt's order reduction

```text
DifferentialSeparantIterate
  vars_pderiv_subset                 differentiating does not introduce new variables
  scalarOrder_deriv_le               differentiation raises the order by at most one
  exists_iterated_separant_decomposition
                                     **every proper derivative of `A` is linear in its top jet with
                                     the same coefficient, the separant of `A`**
DifferentialPseudoDivision
  exists_pseudo_division             pseudo-division against a polynomial linear in the top jet
  exists_order_reduction             **the order-lowering step of Ritt's algorithm**
RittOrderReduction
  derivIdeal A                       the differential ideal generated by `A`
  exists_order_reduced               **Ritt's order reduction**: every differential polynomial
                                     reduces, at the cost of a power of the separant, to one of
                                     order at most `ord A`, modulo the differential ideal of `A`
```

All axiom-clean.  What remains of Ritt's reduction is the degree-lowering step (pseudo-division by
`A` itself in the leader, at the cost of powers of the initial), after which the prime case of
Ritt's basis theorem closes and `radDiffFG_of_prime_radDiffFG` becomes unconditional.

## Lean progress — Ritt's basis theorem

The tree already owned Ritt's *reduction* algorithm (`PseudoDivisionCommRing`,
`DifferentialKernelCharacteristic`: pseudo-division at a distinguished jet, the separant of every
proper derivative, the two-block reduction, and the minimal-rank characteristic with its initial and
separant outside the ideal).  What was missing was the ideal theory that turns the reduction into a
basis theorem.  It is now present:

```text
RadicalDifferentialIdeal              Ritt's lemma; radical of a differential ideal is differential
RadicalDifferentialIdealGeneration    `radicalDifferentialIdeal S`; the product law
RadicalDifferentialIdealPrime         a maximal non-finitely-generated one is prime
RadicalDifferentialIdealZorn          such a maximal one exists
RadicalDifferentialIdealSaturation    the saturation decomposition; finite exhaustion
RittBasisFinishingStep                `isRadDiffFG_of_saturation`
RittBasisTheorem                      **`radDiffFG_differentialPolynomial`: every radical
                                      differential ideal of `K{y}` is the radical differential ideal
                                      of a finite set**, for a differential field `K` of
                                      characteristic zero
```

This is Ritt--Raudenbush for one differential indeterminate — the Noetherianity that makes the
Kolchin topology (already in the tree) usable, and the foundation the classification of differential
algebraic groups is built on.  All axiom-clean.

## Lean progress — Noetherianity of the Kolchin topology

```text
RadicalDifferentialIdealACC
  acc_radicalDifferentialIdeal   **the ascending chain condition on radical differential ideals of
                                 `K{y}`** — the union of a chain is again one, hence generated by a
                                 finite set which already lies at one stage
KolchinNoetherian
  isRadical_differentialVanishingIdealOver
  dcc_isKolchinClosedOver        **the descending chain condition on Kolchin closed subsets of one
                                 differential coordinate**
```

The Kolchin topology was already in the tree; it is now Noetherian.  That is the property every
argument about differential algebraic groups (finite decomposition into irreducibles, dimension
theory, the classification the card still needs) rests on.

## Lean progress — the jet module is a non-split self-extension

`GaloisForLFunctions.HTGeometry.BesselOrderJetModule`

```text
jetMatrix A dA                     the first jet system `[[A, δA], [0, A]]`, from
                                   `σ(δY) = (δA) Y + A (δY)`
blockUnipotent B                   the block-unipotent gauge `[[1, B], [0, 1]]`
jetMatrix_gauge_split_iff          **the jet system splits under a block-unipotent gauge exactly
                                   when `σ(B) A - A B = -δA` is solvable over the base**
besselOrderCompanion c             `[[0, 1], [1, c(ν+1)]]`, the companion of the order recurrence
besselOrder_no_matrix_delta_structure
                                   **no `B ∈ gl₂(ℂ(ν))` satisfies `σ(B) A - A B = δA`**
```

So the first jet module of the Bessel order module is a non-split self-extension: the four entrywise
identities of the matrix equation reduce to the two scalar compatibility identities that the degree
count at infinity refutes.  This is the isomonodromy obstruction in its standard matrix formulation,
which is the form the parameterized classification consumes.

## Lean progress — the obstruction is intrinsic to the difference module

```text
MatrixLogarithmicDerivative
  matrixDeriv_mul                    the matrix Leibniz rule for an arbitrary finite index type
  matrixDeriv_invOf                  the derivative of an inverse
  logDerivMatrix                     **Kolchin's logarithmic derivative `ℓδ g = g′ g⁻¹`**
  logDerivMatrix_mul                 the crossed-homomorphism law
                                     `ℓδ (g h) = ℓδ g + g (ℓδ h) g⁻¹`
  logDerivMatrix_invOf, logDerivMatrix_eq_zero_iff
IsomonodromyGaugeInvariance
  isomonodromy_gauge_mul             **a gauge `σ(T) A = A' T` carries a connection to a connection**
                                     (proved with `T` cleared, so no invertibility is needed)
  isomonodromy_of_gauge              and back, when the gauge is invertible
BesselOrderIntrinsicObstruction
  ratShift_deriv                     **the unit shift commutes with the rational coordinate
                                     derivation** — transported through the faithful embedding of
                                     `ℂ(X)` into the meromorphic field
  matrixDeriv_besselOrderCompanion
  besselOrder_no_gauge_delta_structure
                                     **no system gauge equivalent to the Bessel order companion
                                     over `ℂ(ν)` admits a connection**
```

So the obstruction belongs to the difference module, not to the companion basis: it is the intrinsic
statement a parameterized classification consumes.  All axiom-clean.

## Lean progress — a constant Galois group forces a connection

`GaloisForLFunctions.HTGeometry.ConstantGaloisConnection`

```text
map_invOf                              a ring hom commutes with matrix inversion
logDerivMatrix_map                     `ℓδ` is natural for a ring endomorphism commuting with `δ`
logDerivMatrix_map_eq_self             **a constant Galois matrix fixes the logarithmic
                                       derivative**: `Y ↦ Y g` with `δg = 0` contributes
                                       `Y (ℓδ g) Y⁻¹ = 0` to the crossed-homomorphism law
exists_base_logDerivMatrix_of_galois_constant
                                       **if every Galois matrix is constant and the invariants of
                                       the Galois action are the base, then `ℓδ Y` has entries in
                                       the base** — the system carries a connection
```

This is the direction of the parameterized translation that turns "the parameterized Galois group is
conjugate to its constant points" into isomonodromy.  Combined with the intrinsic obstruction, the
card's remaining gap is now exactly: (i) Cassidy's classification, which produces the conjugating
element, and (ii) the parameterized Galois correspondence supplying `R^G = K`.

## Lean progress — the Galois correspondence is (almost) already owned

A corpus search found that the tree already contains the Galois correspondence in torsor form:

```text
PositiveDimensionalInvariantGeneration
  AffineTorsorCoaction.coinvariant_eq_range      coinvariants of an affine torsor are the base
                                                 field, by faithfully-flat descent
  PointSeparatingTorsorAction.fixedByPoints_eq_range
                                                 elements fixed by every separating rational point
                                                 are the base scalars
AffineRationalPointSeparation
  affineVarietyPointEvaluation_jointlyInjective  the Nullstellensatz supplies the separating points
  AffineTorsorCoaction.fixedByPresentedPoints_eq_range
```

These are stated for a torsor whose total object is a **field**.  A Picard--Vessiot ring is not a
field — only `σ`-simple, hence a finite product of domains — so the missing piece was the same
statement over a coefficient ring:

`GaloisForLFunctions.HTGeometry.RingTorsorCoinvariance`

```text
coinvariant_eq_range_of_canonical   **coinvariance over a coefficient ring**: for a canonical
                                    torsor map carrying the left embedding to the left embedding
                                    and the right embedding to the coaction, the elements whose
                                    coaction is the left embedding are exactly the base scalars
```

Faithful flatness of a nonzero algebra over a field is automatic and mathlib's descent equalizer is
already stated for an arbitrary commutative ring, so the field proof carries over.

**Revised remaining gap for the card.**  Item (ii), the parameterized Galois correspondence
`R^G = K`, is now essentially owned: what is left of it is the *instantiation* — building the
canonical torsor map for the Picard--Vessiot ring out of `tensorDecompositionEquiv`
(`R ⊗_C E ≅ R ⊗_K R`) and the base change `R ⊗_K (K ⊗_C E) ≅ R ⊗_C E`.  Item (i), Cassidy's
classification, is untouched.

## Lean progress — joint injectivity of the torsor points over a coefficient ring

`PointSeparatingTorsorAction.fixedByPoints_eq_range` *assumes* joint injectivity of the rational
point evaluations, and `AffineRationalPointSeparation` supplies it only when the coefficients of the
tensor product form a field.  A Picard--Vessiot ring is not a field, so the missing half is the
injectivity with coefficients in the ring:

`GaloisForLFunctions.HTGeometry.TorsorPointSeparation`

```text
pointAlgHom E χ                             evaluation of the torsor coordinates at a point
torsorPointHom E b hgen hindep χ            the `R`-algebra map `A → R` attached to a point,
                                            through the torsor decomposition `R ⊗_C E ≅ A`
eq_zero_of_forall_torsorPointHom_eq_zero    **an element of `A` killed by every point is zero**
eq_of_forall_torsorPointHom_eq              hence the point evaluations are jointly injective
```

Mechanism: expand the element against a `C`-basis of `E` through the decomposition, then apply
point separation with module coefficients (`PointsSeparateModule`), which needs `E` reduced and
finitely generated over the algebraically closed constant field — both already established for the
Picard--Vessiot torsor (`SigmaConstantsReduced`).

With `A = R ⊗_K R` and the two embeddings of an element of `R`, this says an element fixed by every
specialization lies in the equalizer of the two embeddings, which is the base field
(`TensorSquareEqualizer`).  Item (ii) of the card's remaining gap is therefore complete as
mathematics; what is left of it is threading the concrete instance setup of the Picard--Vessiot
construction.

## Lean progress — Cassidy for `sl₂`, graded case

The last piece of new mathematics the card needs is Cassidy's classification of Zariski-dense
differential algebraic subgroups of `SL₂`.  Its computational heart is now proved.

`GaloisForLFunctions.HTGeometry.CassidySl2Graded`

```text
eq_span_singleton_of_mul_mem_range   **two nonzero `k`-subspaces of a field whose product lands in
                                     `k` are both `k`-lines** — divide two elements of `V` by a
                                     common element of `W` and the ratio is in `k`
sl2E, sl2F, sl2H                     the standard `sl₂` matrices
sl2_bracket_smul_E_F                 the root bracket `[v e, w f] = (v w) h`
sl2Diag v                            the conjugator `diag(1, v)`
sl2Diag_conj_E/F/H                   its action: `v e ↦ e`, `w f ↦ (v w) f`, `h ↦ h`
graded_cassidy_sl2                   **the graded case of Cassidy's classification**: a graded
                                     `k`-Lie subalgebra of `sl₂(U)` with both root spaces nonzero has
                                     `k`-lines as root spaces, and conjugating by `diag(1, v₀)`
                                     normalises it to `sl₂(k)`
```

Two points worth recording.  Closure under the root bracket is what forces `V·W ⊆ k`, since
`[v e, w f] = (v w) h` and the toral part is `k h`.  And the normalising conjugation needs no square
root — `diag(1, v₀)` suffices, where the usual `diag(λ, λ⁻¹)` would demand `λ² = v₀⁻¹` — so the
statement holds over an arbitrary field, not only an algebraically closed one.

What remains of Cassidy is the reduction of the general case to the graded one: producing a torus,
i.e. showing that a Zariski-dense differential algebraic subalgebra can be conjugated so that it is
graded by the diagonal.

## Lean progress — Cassidy's reduction, step one

`GaloisForLFunctions.HTGeometry.Sl2RegularElement`

```text
detPolar X Y                        the polarisation of the determinant on `2 × 2` matrices
det_add_detPolar, det_smul_two      the determinant is a quadratic form
detPolar_comm/add_left/smul_left    its polarisation is symmetric and bilinear
exists_det_ne_zero_of_mem_span      **a `k`-subspace whose `U`-span contains a matrix of nonzero
                                    determinant contains one itself**
```

Mechanism: if the determinant vanished on the subspace, then — because the subspace is closed under
addition — its polarisation would vanish there too, and both would then vanish on the whole `U`-span
by span induction.  So a Zariski-dense subalgebra of `sl₂(U)` contains a regular semisimple element,
which is what the conjugation to the diagonal starts from.

## Lean progress — Cassidy's classification for `sl₂`, unconditionally

The last piece of new mathematics the card needed is now proved in full.

`GaloisForLFunctions.HTGeometry.Sl2DiagonaliseRegular`

```text
eq_traceless_matrix                  a traceless `2 × 2` matrix in explicit form
exists_conj_toral_of_det_ne_zero     **a regular element of `sl₂` is conjugate to `μ h`**, with the
                                     conjugator written down from the eigenvectors — no spectral
                                     theory, only `μ² = -det X` and one square root
```

`GaloisForLFunctions.HTGeometry.Sl2ToralClassification`

```text
adMap, conjLinear, smulMat           the adjoint action, conjugation and scaling as linear maps
bracket_toral, bracket_toral_sq      `[μ h, Z]` and `[μ h, [μ h, Z]]` in the `h, e, f` basis
bracket_root                         `[b e + c f, b' e + c' f] = (b c' - c b') h`
traceless_decomp                     the `h, e, f` coordinates of a traceless matrix
cassidy_sl2_of_toral                 **the toral case**: a bracket-closed `C`-subspace of `sl₂(U)`
                                     that `U`-spans, has trivial `U`-line stabilisers and contains
                                     `μ h` is `C·h + C·v₀e + C·w₀f` with `v₀w₀ ∈ C`
```

`GaloisForLFunctions.HTGeometry.CassidySl2Classification`

```text
conj_mul_conj, conj_conj_eq, conj_injective, conjLinear_comp
cassidy_sl2                          **Cassidy's classification for `sl₂`**: such a subalgebra is
                                     conjugate to `sl₂(C)`
```

The proof of the toral case is a chain of three brackets and needs no representation theory.
Doubling the bracket with `μ h` projects `L` onto the root part, so the spanning hypothesis and the
regular-element lemma put a root element `b e + c f` of nonzero determinant in `L`.  Bracketing that
element against its own `ad(μ h)`-image returns `(b c)·(μ h)`, and bracketing the image against
`μ h` returns `μ²·(b e + c f)`.  The line-stabiliser hypothesis therefore forces `b c ∈ C` **and**
`μ² ∈ C`; since `C` is algebraically closed, `μ ∈ C`, so `h` itself lies in `L`.  Once `h` is
present the eigenvalues `0, ±2` of `ad(h)` lie in `C`, the subalgebra splits into root spaces over
`C`, and the product of the two root spaces lands in `C` — exactly the hypothesis of the graded
classification proved earlier.  The general case follows by conjugating a regular element to the
diagonal and transporting all four hypotheses through the conjugation.

The line-stabiliser hypothesis is the honest form of "differential algebraic and proper": for a
Lie algebra cut out by linear differential equations, `{c : c A ∈ L}` is itself the solution set of
a linear differential system, hence finite dimensional over the constants, hence contained in the
algebraically closed constants.  That transfer is the next brick.

## Lean progress — the classification in the form the Galois group needs

Three further modules, all unconditional and axiom-clean.

`GaloisForLFunctions.HTGeometry.CassidyMatrixAlgebra`

```text
traceLinear, matrix_decomp_one_hef      the trace as a linear map; the `1, h, e, f` coordinates
mem_span_hef_iff, mem_span_one_hef_iff  `sl₂(C)` and `M₂(C)` are exactly the matrices with entries
                                        in `C` (traceless, resp. arbitrary)
cassidy_matrixAlgebra                   **a `C`-subalgebra of `M₂(U)` that `U`-spans and whose
                                        scalar line stabiliser is `C` is conjugate to `M₂(C)`**
cassidy_gl2_constant_conjugate          **hence one conjugation makes every element of a spanning
                                        matrix group constant**
```

The associative case reduces to the Lie case: commutators of the algebra lie in its traceless part
and `U`-span `sl₂(U)`, so the `sl₂` classification conjugates that part to `sl₂(C)`; bracketing an
arbitrary element against `e` and `f` then reads its off-diagonal and toral coordinates out of `C`,
and the line stabiliser of `1` reads the scalar coordinate.

The hypothesis was weakened in the process, and the weakening is what makes the theorem usable.
The classification needs the line stabiliser only for elements of **nonzero determinant**, and for
an algebra that hypothesis follows from the single scalar case: for traceless `Z` one has
`Z² = -det(Z)·1`, so `Z ∈ A` puts `det Z` in the scalar stabiliser and `c Z ∈ A` puts `c² det Z`
there too — whence `c² ∈ C`, and `c ∈ C` because `C` is algebraically closed.  So the final
hypothesis is only: *the scalars `c` with `c · 1` in the span are constants.*

`GaloisForLFunctions.HTGeometry.DifferentialSolutionSpace`

```text
IsDifferentialSystemSolution                      `v′ = A v`
exists_differentialConstants_relation             the minimal-support argument
card_le_of_no_differentialConstants_relation      **rank-`n` systems have solution spaces of
                                                  dimension at most `n` over the constants**
scalarCompanion, isDifferentialSystemSolution_jetVec, card_le_of_no_constantRelation_scalar
exists_constantCoeff_relation_of_powers           if every power of `x` solves one monic scalar
                                                  equation of order `n`, then `x` satisfies a
                                                  nonzero polynomial with constant coefficients
```

`GaloisForLFunctions.HTGeometry.DifferentialConstantsCollapse`

```text
exists_eq_algebraMap_of_isIntegral            integral over an algebraically closed base means in it
deriv_eq_zero_of_solution_powers              a power family of solutions collapses to a constant
exists_eq_algebraMap_of_smul_one_solution     **the scalar line stabiliser of a multiplicative set
                                              of matrices is constant** as soon as its elements
                                              solve one monic linear differential equation
```

Together these close the loop for a matrix group: the scalars `c` with `c · 1` in the `C`-span form
a ring, a ring of solutions of a linear differential equation is finite dimensional over the
constants, hence algebraic over them, hence equal to them — and the classification then makes the
group constant after a single conjugation.

## Lean progress — the classification, in differential form

The classification asks for line stabilisers that are *constant*; a differential-algebraic
structure supplies line stabilisers that are *bounded* — a fixed number of scalars always admits a
relation over the constants.  Three modules close that gap.

`GaloisForLFunctions.HTGeometry.BaseFieldCollapse`

```text
exists_eq_algebraMap_of_isIntegral            integral over an algebraically closed base ⟹ in it
exists_eq_algebraMap_of_sq                    a square root descends
exists_eq_algebraMap_of_polynomial_relation   a nontrivial polynomial relation descends
```

`GaloisForLFunctions.HTGeometry.Sl2LineStabiliserBridge`

```text
BoundedOverBase                        a fixed number of elements always admits a relation over `C`
exists_eq_algebraMap_of_powers_mem     a power family inside a bounded set is algebraic over `C`
adFun, adFun_cube                      `ad(Z)³ = 4δ·ad(Z)` for traceless `Z`, with `δ = -det Z`
iterate_adFun_smul, iterate_adFun_odd, iterate_adFun_mem
line_stabiliser_mem_base               **bounded line stabilisers are constant**
cassidy_sl2_of_bounded                 hence the classification under boundedness alone
```

The bridge is the iterated bracket.  Choose `W ∈ L` with `ad(Z) W ≠ 0` — one exists because `L`
spans `sl₂(U)` and `Z ≠ 0`.  Bracketing `c Z` against `W` an odd number of times gives
`c (δ c²)^k · ad(Z) W ∈ L` for every `k`, and the same computation with `c = 1` gives
`δ^k · ad(Z) W ∈ L`.  Boundedness of the stabiliser of `ad(Z) W` therefore makes `δ` and `δ c²`
algebraic over `C`, so `c²` lies in `C`, and `c` does too because `C` is algebraically closed.

`GaloisForLFunctions.HTGeometry.DifferentialCassidyClassification`

```text
boundedOverBase_of_scalarSolution        solution sets of a monic scalar linear differential
                                         equation of order `n` are bounded over the constants
cassidy_sl2_of_differentialSolution      **the classification for `sl₂` over the constants of a
                                         differential field**
constant_conjugate_of_differentialSolution
                                         **a spanning matrix group whose scalar stabiliser solves
                                         a linear differential equation becomes constant after one
                                         conjugation**
```

The last statement is the exact shape the difference Galois group needs: it says that a Galois
group which is Zariski dense (spanning) and differentially constrained is, after a single change of
fundamental matrix, a group of *constant* matrices — which is what
`ConstantGaloisConnection.exists_base_logDerivMatrix_of_galois_constant` turns into isomonodromy,
and isomonodromy is what `BesselOrderIntrinsicObstruction` refutes.

## Lean progress — Burnside, and the classification from irreducibility

`GaloisForLFunctions.HTGeometry.BurnsideTwoByTwo`

```text
exists_vecMulVec_of_det_eq_zero   a singular nonzero `2 × 2` matrix is an outer product
mul_vecMulVec_mul                 `x (v wᵀ) y = (x v)(w y)ᵀ`
vecMulVecLeft, vecMulVecRight     the outer product as a linear map in each factor
mem_span_vecMul                   the covectors `w y` sweep the plane as well
mem_of_irreducibleAction          **Burnside's theorem**: a matrix algebra acting irreducibly on
                                  the plane is everything
```

`DifferentialCassidyClassification.constant_conjugate_of_irreducible` puts the two halves together:
a multiplicative set of matrices acting **irreducibly**, whose scalar stabiliser solves a monic
linear differential equation, is conjugated into the constants by a single matrix.  Irreducibility
is the hypothesis the difference module supplies — the corpus already proves the Bessel order
operator has no first-order right factor — so this is the classification in the form the card's
Galois group will meet it.

## Lean progress — a Galois-stable line is a Riccati solution

`GaloisForLFunctions.HTGeometry.DifferenceSemiInvariantSolution`

```text
exists_eq_algebraMap_mul_of_tmul_comm   `y ⊗ z = z ⊗ y` forces `z = r y` with `r` in the base
isUnit_of_sigma_eq_smul                 a nonzero hyperexponential element of a `σ`-simple ring is
                                        a unit
riccati_of_sigma_eq_smul                and its ratio solves the Riccati equation
exists_riccati_of_tmul_comm             **a semi-invariant solution produces a base Riccati
                                        solution**
```

This is the half of the irreducibility arrow that needs no Galois theory at all.  A Galois-stable
line says, in the tensor square of the Picard--Vessiot ring, that `y ⊗ σ y = σ y ⊗ y`; applying a
linear functional with `f y = 1` to the left factor turns that into `σ y = r y` with `r` in the
base.  The ideal generated by such a `y` is a `σ`-ideal, so `σ`-simplicity makes `y` a unit, the
recurrence can be divided by it, and `r` solves the Riccati equation — which the corpus already
refutes for the Bessel order recurrence.

What remains of the arrow is the passage from "every Galois element scales `y`" to the tensor
identity: the specialisations of the tensor square separate its elements, and the corpus owns both
halves of that (`DifferenceSpecialization` for the passage from a point to a Galois element, and
`PointsSeparateModule` for separation with coefficients in a module).

## Lean progress — irreducibility from the Riccati obstruction

`GaloisForLFunctions.HTGeometry.TorsorSpecializationSeparation`

```text
torsorSpecialization                              the `R`-algebra map `A → R` attached to a point
                                                  of the group
eq_zero_of_forall_torsorSpecialization_eq_zero    **the specialisations separate the torsor**
mul_comm_embeddings_of_forall_specialization      proportionality at every point is a symmetry of
                                                  the tensor square
```

`GaloisForLFunctions.HTGeometry.DifferenceIrreducibilityCriterion`

```text
rightEmbedding                                          `r ↦ 1 ⊗ r`, over the constants
not_forall_specialization_semiInvariant_of_no_riccati   **no base Riccati solution ⟹ no
                                                        semi-invariant solution**
```

Separation is the Nullstellensatz through the torsor decomposition: writing an element of
`R ⊗_K R ≅ R ⊗_k E` in a `k`-basis of `E` turns its value at a point into a `k`-linear combination
of the basis values, and points separate on a reduced finite-type algebra over an algebraically
closed field, so all the coefficients vanish.

With the semi-invariant Riccati step this closes the arrow the classification was waiting on: the
Bessel order recurrence has no rational Riccati solution, hence no Galois-stable line, hence — by
Burnside — its Galois matrices span `M₂`, and the classification applies.

## Lean progress — the abstract endgame is closed

The whole chain from the two hypotheses the Bessel recurrence supplies to isomonodromy over the base
is now proved, unconditionally.

`PointSubsetSeparateModule`, `TorsorSpecializationSeparation` (generalised)

```text
eq_zero_of_forall_pointSubset_smul_eq_zero            separation by a *subset* of points, with
                                                     coefficients in a module
eq_zero_of_forall_torsorSpecialization_subset_eq_zero the torsor is separated by any separating set
                                                     of points — the parameterised Galois group uses
                                                     the differential points, not all of them
```

`DifferenceGaloisIrreducibility`, `DifferenceGaloisEndgame`

```text
galoisMatrixAt, galoisAutAt, galoisAutAt_fundamental  the Galois matrix and automorphism at a point
not_semiInvariant_coordinate_of_no_riccati           **no Galois-stable line**
galoisMonoid                                         the monoid generated by the Galois matrices
constant_conjugate_galoisMonoid_of_no_riccati        **one conjugation makes every Galois matrix
                                                     differentially constant**
exists_eq_algebraMap_of_forall_galoisAutAt           **the Galois correspondence**: an element fixed
                                                     by every Galois automorphism lies in the base
```

`FundamentalMatrixIsomonodromy`, `GaloisAutConstantConnection`, `DifferenceIsomonodromyEndgame`

```text
isomonodromy_of_fundamentalMatrix                    `ℓδ Y` solves `σ(B) A = δA + A B`
isomonodromy_descend                                 the equation descends to the base field
exists_base_logDerivMatrix_of_galoisAutAt_constant   a constant Galois group forces a connection
invOf_mul_map_galoisAutAt                            the Galois matrix of `Y` is the specialised
                                                     comparison matrix
isomonodromy_of_no_riccati_of_differentialSolution   **the endgame**: no base Riccati solution plus a
                                                     differentially constrained scalar stabiliser
                                                     forces isomonodromy over the base
```

Only two obligations remain for the card, both instantiations:

1. the differential constraint on the scalar stabiliser, which is what differential algebraicity of
   `K_ν(s)` provides through Cassidy's additive classification (already owned in evaluated form);
2. the concrete Picard--Vessiot data for the Bessel order recurrence — the ring, the fundamental
   matrix, the constants subalgebra of the tensor square with its basis, and the separating set of
   differential points.

The contradiction is then immediate: the endgame produces a connection over `ℂ(ν)`, and
`BesselOrderIntrinsicObstruction.besselOrder_no_gauge_delta_structure` refutes exactly that.

## Lean progress — the obstruction over an arbitrary base field

The parameterised theory needs a base whose `σ`-constants carry a nontrivial derivation, so the
obstruction has to hold over `C(ν)` for a differentially closed `C ⊇ ℂ`, not only over `ℂ(ν)`.  It
does.

`GaloisForLFunctions.HTGeometry.RatFuncFieldShift`

```text
comp_X_add_one_eq_self, shift_periodic_quotient_constant   shift-invariance is constancy
shiftDelta, natDegree_shiftDelta, leadingCoeff_shiftDelta  the finite difference of a polynomial
ratShift, ratShift_algebraMap, ratShift_fixed_eq_const     the shift on `F(X)`
intDegree_ratShift, intDegree_ratShift_sub                 **the shift difference drops the degree
                                                           at infinity by exactly one**
intDegree_ratShift_sub_le_of_intDegree_zero                and by at least two in degree zero
```

`GaloisForLFunctions.HTGeometry.BesselOrderFieldObstruction`

```text
orderShiftCoeff, besselOrderCompanion, besselOrderCompanionDeriv
besselOrder_no_rational_delta_structure    **no rational compatible derivation**, over any field of
                                           characteristic zero
besselOrder_no_matrix_delta_structure      the matrix form of the same obstruction
```

The proofs are the same degree count as over `ℂ`; what changes is that they now apply to the base
the parameterised Galois theory actually runs over.

## Lean progress — the difference-differential base, and the differential Nullstellensatz

`RatFuncFieldShiftEquiv`, `RatFuncTotalDerivation`, `RatFuncShiftDerivationCommute`

```text
ratShiftOf, ratShiftEquiv                  translations compose additively, so the unit shift is a
                                           ring automorphism of `K(X)`
coordinateTotalDerivation                  `D f = coeffDeriv f + (d/dX) f`, the derivation of `K(X)`
                                           extending a given derivation of `K` with `D X = 1`
coordinateTotalDerivation_base, _X          its two computational values
ratShift_coordinateTotalDerivation         **the shift commutes with the derivation**
```

`RadicalDifferentialIdealMaximal`, `DifferentialFieldSolution`, `DifferentialSystemSolution`,
`MvPolynomialBaseChangeProper`

```text
isPrime_of_maximal_proper_radicalDifferential   a maximal proper radical differential ideal is prime
exists_isPrime_radicalDifferential              hence every proper one lies in a prime one
exists_differentialField_hom_of_ne_top          **the weak differential Nullstellensatz**
exists_point_of_ne_top                          a consistent differential system has a solution
                                                point in a differential field extension
map_ne_top_of_ne_top                            consistency survives extending the coefficient field
```

These are the pieces a differential closure is assembled from, and a differentially closed field of
constants is what the parameterised Galois theory needs in order not to degenerate over `ℂ(ν)`.

## Lean progress — the differential closure, Kolchin, and the differential Galois points

The constants field the parameterised theory needs now exists, together with the Nullstellensatz
that makes its points separate.

`DifferentialPolynomialRename`, `DifferentialPolynomialBaseChange`

```text
differentialRename_deriv                     renaming commutes with the total derivation
isRadical_ker_of_field                       the kernel of a differential map to a field is a
                                             radical differential ideal
differentialCoeffExtend_deriv                extending the coefficients commutes with it
differentialPolynomialEvalOver_differentialRename / _differentialCoeffExtend
map_differentialPolynomialEvalOver           a differential map of the target carries a solution
                                             to a solution
```

`DifferentialFieldExtension`, `DifferentialJointSolvability`, `DifferentialClosureStep`

```text
DiffFieldExt                                 a differential field extension, bundled
exists_point_over_ext                        a consistent system stays solvable over any extension
exists_jointExt                              finitely many consistent systems are jointly solvable
exists_ext_solving_all                       **one step**: a single extension solves every
                                             consistent system over the base
```

`DifferentialClosureTower`, `DifferentialClosureClosed`

```text
diffTowerExt, diffTowerHom, diffClosure      the tower of one-step extensions and its union
diffClosureDerivation                        its derivation, from the universal property applied to
                                             the **dual numbers** of the union
exists_point_of_solution_ext                 **the union is differentially closed**
IsDifferentiallyClosed                       the property, with the union as an instance
```

`RadicalDifferentialIdealAvoiding`, `KolchinNullstellensatz`

```text
exists_isPrime_avoiding_radicalDifferential  Zorn and Ritt's product law avoiding an element
exists_differentialField_hom_of_notMem       the weak differential Nullstellensatz keeping an
                                             element nonzero
exists_differentialAlgHom_ne_zero            **Kolchin's Nullstellensatz**
differentialPoints, eq_zero_of_forall_mem_differentialPoints
                                             the differential points separate
```

`DifferentialGaloisPoint`, `DifferentialGaloisSeparation`, `DifferentiallyClosedAlgClosed`

```text
torsorSpecialization_deriv, galoisAutAt_deriv   a differential point has a differential Galois
                                                automorphism
tensorDifferentialPoints                        the differential points of the constants subalgebra
eq_zero_of_forall_mem_tensorDifferentialPoints  they separate
isomonodromy_of_no_riccati_of_differentiallyClosed
                                                **the endgame with `hsep` and `hδgal` discharged**
isAlgClosed_of_isDifferentiallyClosed           a differentially closed field is algebraically
                                                closed
isAlgClosed_differentialConstants               and so are its constants
```

`DifferentialRelationSigmaDescent`

```text
differentialPolynomialSigma, differentialPolynomialEvalOver_sigma
exists_sigmaFixed_relation                   **a differential relation satisfied by a `σ`-invariant
                                             point descends to `σ`-invariant coefficients**
```

So `diffClosure` of any characteristic-zero differential field supplies every hypothesis the endgame
makes on the constants: algebraically closed, characteristic zero, algebraically closed differential
constants, and differentially closed.  The remaining obligation is the differential-algebraic group
layer: from differential algebraicity of the solution, the descended relations make the Galois
points lie in a proper differential algebraic set, and Cassidy's additive classification — owned in
evaluated form — turns that into the bound the classification consumes.

## Lean progress — Cassidy's additive classification, elementarily, and the collapse it feeds

`AdditiveDifferentialSubgroupLinear`

```text
jetVecHom                                        the jet vector of an element, as an additive map
exists_nonzero_linear_jet_relation_of_addSubgroup
    **an additive subgroup lying in the zero set of a nonzero differential polynomial satisfies a
    nonzero linear relation among its jets**
```

The proof is elementary and needs no Hopf algebra: a differential polynomial in one indeterminate
involves finitely many jets, so it is an ordinary polynomial on a finite-dimensional jet space; the
jet vectors of an additive subgroup form an additive subgroup there on which it vanishes; if they
spanned, every point would be a finite linear combination of them and the pullback would vanish on
an integer lattice, hence be zero.  So they span a proper subspace and any annihilating functional
is the relation.  (`MvPolynomialInfiniteVanishing.mvPolynomial_eq_zero_of_eval_eq_zero_on_infinite_pow`
was generalised from `ℂ` to an arbitrary domain for this.)

`DifferentialSubringCollapse`

```text
exists_monic_jet_relation                     a nonzero linear jet relation can be taken monic
deriv_eq_zero_of_subring_of_zeroSet           **a subring inside a proper differential algebraic set
                                              consists of constants**
scalarStabilizer                              the scalars `x` with `x • 1` in a module of matrices
eq_algebraMap_of_scalarStabilizer_of_zeroSet  exactly the hypothesis
                                              `cassidy_gl2_constant_conjugate` consumes
```

**Correction to the route.**  The scalars of the `C^δ`-span of the Galois monoid are *not* bounded by
differential algebraicity alone: for `Z = {x : δ(δx/x) = 0}` the group

  `G = {diag(a,a⁻¹) : a ∈ Z} ∪ {antidiag(b,-b⁻¹) : b ∈ Z}`

is irreducible with determinant `1` and all entries in the zero set of `x δ²x - (δx)²`, yet
`diag(a,a⁻¹) + diag(a⁻¹,a) = (a+a⁻¹)·1` puts `{a + a⁻¹}` — the hyperbolic cosines — into the scalar
stabiliser, and those are unbounded.  The imprimitive case therefore has to be excluded separately
(the symmetric-square layer of this card), and in the primitive case Cassidy's structure theorem
makes the traces fill a differential subfield, which the two theorems above then collapse to the
constants.

## Lean progress — the classification's output, in linear form, closes the endgame

The endgame consumes `hsol`: a monic linear relation among the jets of every scalar `c` with
`c · 1` in the span of the Galois monoid.  Two new modules turn the two natural shapes of a
differential constraint into exactly that relation, unconditionally.

`GaloisForLFunctions.HTGeometry.DifferentialGaloisScalarZeroSet`

```text
deriv_eq_zero_of_scalarSpan_of_zeroSet   **the scalar stabiliser of the span of a multiplicative
                                         set of matrices consists of constants** as soon as it lies
                                         in the zero set of one nonzero differential polynomial —
                                         the stabiliser is a subring, and a subring inside a proper
                                         differential algebraic set is constant
jet_relation_of_scalarSpan_of_zeroSet    the same, in the monic jet shape (`δ c = 0`)
isomonodromy_of_no_riccati_of_zeroSet    **the isomonodromy endgame** with the differential
                                         constraint replaced by one nonzero differential polynomial
                                         vanishing on the scalar stabiliser
linearJetSolutions, matrixLinearJetSolutions
                                         the solution set of a scalar linear differential operator,
                                         as a subspace over the differential constants, and the
                                         matrices with entries there
linearJetPolynomial, linearJetPolynomial_ne_zero
                                         the operator as a differential polynomial
eval_linearJetPolynomial_eq_zero_of_scalarSpan
                                         **a linear relation on the entries of the group passes to
                                         the whole span**, because the solution set of a linear
                                         operator is a subspace over the constants
deriv_eq_zero_of_scalarSpan_of_linear    hence the scalar stabiliser is constant
isomonodromy_of_no_riccati_of_linearRelation
                                         **the endgame from a linear differential relation on the
                                         Galois matrices** — no other hypothesis
```

`GaloisForLFunctions.HTGeometry.DifferentialConstantRelationDescent`

```text
exists_descend_of_coeff_mem_range        a polynomial whose coefficients lie in the image of the
                                         base is the coefficient extension of one over the base
exists_constantCoeff_relation_of_sigmaFixed
                                         **a differential relation over the base satisfied by a
                                         `σ`-invariant point descends to a relation over the
                                         `σ`-invariants of the base** — the constants
differentialPolynomialEvalOver_eq_zero_of_point
                                         a differential point of the Galois group carries a
                                         constant-coefficient relation to its own coordinates
```

Together these two modules split the remaining arrow in two, and settle the second half:

1. *differential algebraicity produces a differential relation on the Galois matrices.*  The
   comparison matrix has `σ`-invariant entries, so `exists_constantCoeff_relation_of_sigmaFixed`
   turns a relation over `ℂ(ν)` into one over the constants, and
   `differentialPolynomialEvalOver_eq_zero_of_point` evaluates it at every differential point.
2. *a **linear** differential relation on the Galois matrices produces isomonodromy.*  This is
   `isomonodromy_of_no_riccati_of_linearRelation`, and it is now proved with no side hypothesis.

What separates them is exactly the linearity, and that is the whole remaining mathematical content
of the classification: the constraint that differential algebraicity supplies is a differential
algebraic set, while the constraint the collapse consumes is a *linear* differential operator.  The
card's own counterexample shows the gap is real — for `Z = {x : δ(δx/x) = 0}` the group
`{diag(a, a⁻¹)} ∪ {antidiag(b, -b⁻¹)}` with `a, b ∈ Z` has all entries in a proper differential
algebraic set, spans `M₂`, and yet its scalar stabiliser contains the unbounded family `a + a⁻¹`.
Linearity is what fails there: `Z` is not a subspace over the differential constants.

The classical source of linearity is the tangent space: the Lie algebra of a differential algebraic
subgroup is cut out by the linearisations of the defining differential polynomials, and those are
linear differential polynomials.  So the remaining obligation of this card is the differential
algebraic group layer in the following precise form, and nothing else:

> the Galois matrices of a Zariski-dense differential algebraic subgroup of `SL₂` whose defining
> ideal is proper satisfy one nonzero **linear** differential operator over the constants.

Every declaration reports `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

### Where the linearity has to come from, in the corpus's own terms

The tree already owns the implication *additive subgroup inside a proper differential algebraic set
⟹ nonzero linear relation among the jets*
(`AdditiveDifferentialSubgroupLinear.exists_nonzero_linear_jet_relation_of_addSubgroup`).  So the
linearity gate is not a missing implication but a missing **additive subgroup**: the scalar
stabiliser is additive, but nothing yet places it inside a proper differential algebraic set, and
the counterexample above shows it need not be.

The additive subgroup that does the work in Cassidy's proof is the unipotent parameter set

```text
k = { t : C | [[1, t], [0, 1]] ∈ H },
```

for `H` the Kolchin closure of the Galois group.  It is an additive subgroup because
`u(t) u(t') = u(t + t')`, and it is a differential algebraic set because it is the preimage of `H`
under a differential morphism — so *if* `H` contains a nontrivial unipotent one-parameter family,
the corpus's implication immediately produces the linear operator, and
`isomonodromy_of_no_riccati_of_linearRelation` finishes.  In the monomial counterexample `k = {0}`:
the group has no unipotents at all, which is exactly the imprimitive case the card's symmetric-square
layer has to exclude.

So the card's remaining obligation splits once more, into two statements neither of which is about
scalars:

1. **exclude imprimitivity** for the Bessel order recurrence — no Riccati solution over a quadratic
   `σ`-extension, equivalently no hyperexponential solution of the symmetric square (the card's
   `(5)`–`(7)` layer);
2. **produce a unipotent family** in a Zariski-dense, non-imprimitive differential algebraic
   subgroup of `SL₂` — the structural half of Cassidy's theorem.

With `(1)` and `(2)` the chain closes with theorems the tree already has.

## Lean progress — the linearisation, which is where linear differential operators come from

The gap identified above is *linearity*: a differential algebraic constraint on a group does not
descend to its span, a linear one does.  The classical source of linearity is the tangent space, and
that is now proved in Lean, from scratch, for arbitrary differential polynomials.

`GaloisForLFunctions.HTGeometry.DifferentialTangentLinearization`

```text
dualMk, dualDifferentialDeriv, dualDifferential
    **the dual numbers as a differential ring**: `δ(a + εb) = δa + ε δb`, with `ε` constant and
    square zero; the Leibniz law holds componentwise
dualDifferentialAlgebra, deriv_dual_fst, deriv_dual_snd, differentialJet_dual
    the base embeds differentially, and jets act componentwise
dualPoint, evalOver_dual_X
    the dual point `p + εX`
fst_differentialPolynomialEvalOver_dual
    the `ε`-free part of the value at `p + εX` is the value at `p`
snd_differentialPolynomialEvalOver_dual
    **the linearisation formula**: the `ε`-part is `∑_v (∂_v F)(p) · δ^{v.2} X_{v.1}`, summed over
    any finite set containing the variables of `F`
exists_linear_form_snd_evalOver_dual
    so the `ε`-part is a *linear* differential form in the perturbation
exists_scalar_linear_form
    for one differential indeterminate, `dF_p(X) = ∑_{i ≤ n} (∂_i F)(p) · δ^i X`, with the tail of
    the partial derivatives vanishing
exists_nonzero_linear_relation_of_tangent
    **a set of tangent directions lies in the solution set of one nonzero scalar linear
    differential operator** — exactly the hypothesis
    `DifferentialGaloisScalarZeroSet.isomonodromy_of_no_riccati_of_linearRelation` consumes
```

The proof of the linearisation formula is the three-case induction on the polynomial, with the
multiplication step supplying the product rule from `TrivSqZeroExt.snd_mul` and the identity
`(∂_v)(q · X_n) = q · ∂_v X_n + X_n · ∂_v q`.  Nothing is assumed about the coefficient ring beyond
being a commutative differential ring.

This closes the *mechanism* half of the linearity gap: a differential algebraic set has a tangent
space cut out by linear differential operators, and a linear operator's solution set is a subspace
over the differential constants, which is what makes the span of a group inherit the relation.  What
remains is the *geometry* half — that the Galois matrices are controlled by the tangent space of
their Kolchin closure at the identity, i.e. Cassidy's structure theorem for Zariski-dense
differential algebraic subgroups of `SL₂` — together with the exclusion of the imprimitive case.

Every declaration reports `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

### Item (a) reduced: the discriminant identity and what survives it

Imprimitivity of the order module is the existence of `e, p ∈ ℂ(X)`, `p ≠ 0`, with

```text
(E)  σe = e/p + 2b,
(P)  p σp = 1 + b e + b² p,                       b = c(X+1),  c ≠ 0
```

— `e = r₁ + r₂` and `p = r₁ r₂` for the two Riccati ratios `r_i = σy_i / y_i`, whose symmetric
functions are rational exactly when the Galois group permutes the two lines.  (These are the
`(α, β, γ)` equations of the symmetric square after eliminating: `α = 1`, `β`, `γ` are rational
functions of `e, p`.)

**The discriminant identity.**  Put `Δ = e² − 4p`.  Then `(E)` and `(P)` force

```text
(D)  σΔ · p² = Δ,
```

by direct substitution: `σΔ = (σe)² − 4σp = (e/p + 2b)² − 4[(1+be)/p + b²] = (e² − 4p)/p²`.
Conversely `(E) ∧ (D) ⟹ (P)`, so `(D)` is a faithful reformulation, not a weakening.

Three consequences, each unconditional:

1. `Δ ≠ 0`.  Otherwise `r₁ = r₂ = e/2 ∈ ℂ(X)` is a rational Riccati solution, which
   `BesselOrderRiccati.orderBesselRiccati_no_ratFunc_solution` refutes.
2. **`intDegree p = 0` and `ℓ(p)² = 1`.**  The shift preserves both the degree at infinity and the
   leading coefficient, so `(D)` gives `ν(Δ) + 2ν(p) = ν(Δ)` and `ℓ(Δ)·ℓ(p)² = ℓ(Δ)`.
3. Feeding `ν(p) = 0` back into `(E)` and `(P)`: `ν(e) = 1` (the other two cases `ν(e) > 1` and
   `ν(e) < 1` contradict `(P)` and `(E)` respectively), the degree-`2` terms of `(P)` must cancel,
   giving `ℓ(e) = −c·ℓ(p)`, and `(E)` at degree one gives `ℓ(e)(ℓ(p) − 1)/ℓ(p) = 2c`.  Together:
   **`ℓ(p) = −1` and `ℓ(e) = c`.**

So the imprimitive branch is pinned to `ν(p) = 0`, `ℓ(p) = −1`, `ν(e) = 1`, `ℓ(e) = c`, and the
branch `ℓ(p) = +1` is impossible.  The surviving branch admits a formal solution at infinity — the
asymptotic expansions of the two Bessel ratios — so no further degree count at infinity can close
it; the remaining argument has to be global, of the denominator/orbit type that
`orderBesselRiccatiPolynomial_no_solution` uses for the rank-one case.

### The descent step, assembled

`GaloisForLFunctions.HTGeometry.DifferentialConstantRelationDescent` now closes step 1 of the split
in one statement:

```text
exists_constantCoeff_relation_eval
    a nonzero differential relation over `ℂ(ν)` satisfied by a `σ`-invariant point yields a nonzero
    relation **over the constants** satisfied by the image of that point under every differential
    point of the ring
```

which is exactly "differential algebraicity produces a differential relation on the Galois
matrices", with the comparison matrix as the `σ`-invariant point and the Galois points as the
differential points.  What separates this from the endgame remains the *linearity* of that relation.

### Item (a) CLOSED on paper: the imprimitive branch is impossible

The previous entry left the imprimitive branch pinned to `ν(p) = 0`, `ℓ(p) = −1`, `ν(e) = 1`,
`ℓ(e) = c`, and observed that "no further degree count at infinity can close it; the remaining
argument has to be global".  It is global, and it is short.  `[PROVED HERE]`

**Step 1 — the discriminant identity.**  `(E) ∧ (P) ⟹ (D) σΔ·p² = Δ`, with `Δ = e² − 4p`, and
conversely; this was already recorded.

**Step 2 — every finite order of `Δ` is even.**  Write `v_a` for the order at `a ∈ ℂ`.  Since the
shift acts on orders by `v_a(σf) = v_{a+1}(f)`, `(D)` reads

```text
v_{a+1}(Δ) + 2·v_a(p) = v_a(Δ)      for every a ∈ ℂ.
```

`Δ ≠ 0` is a rational function, so `v_{a+n}(Δ) = 0` for all large `n`.  Descending from there along
the orbit `a + ℤ`, each `v_{a+k}(Δ)` is obtained from the next by adding the even number
`2·v_{a+k}(p)`.  Hence **every** `v_a(Δ)` is even.  The total degree of the divisor of a rational
function is zero, so the order at infinity is even too.

**Step 3 — `Δ` is a square.**  A rational function over an algebraically closed field whose divisor
is everywhere even is a square: its numerator and denominator have even root multiplicities, hence
are squares up to constants, and every constant is a square.  Write `Δ = k²`, `k ∈ ℂ(X)`, and put

```text
r₁ = (e + k)/2,   r₂ = (e − k)/2,     so   r₁ + r₂ = e,   r₁·r₂ = p.
```

**Step 4 — the pair `{σr₁, σr₂}` is the pair `{f(r₁), f(r₂)}`, `f(r) = b + 1/r`.**  Both are the
root pairs of monic quadratics, and the coefficients agree:
`f(r₁) + f(r₂) = 1/r₁ + 1/r₂ + 2b = e/p + 2b = σe = σr₁ + σr₂` by `(E)`, and
`f(r₁)·f(r₂) = (1 + b r₁)(1 + b r₂)/p = (1 + be + b²p)/p = σp = σr₁·σr₂` by `(P)`.
They are distinct (`f(r₁) = f(r₂)` forces `r₁ = r₂`, i.e. `Δ = 0`, excluded), so exactly one of the
two assignments holds.

**Step 5 — the swap is excluded at infinity.**  Normalise `k` so that `ℓ(k) = ℓ(e) = c`; then
`ν(r₁) = 1`, `ℓ(r₁) = c`, and from `r₁r₂ = p` with `ν(p) = 0`, `ℓ(p) = −1`: `ν(r₂) = −1`,
`ℓ(r₂) = −1/c`.  Hence `ν(1/r₂) = 1` with `ℓ(1/r₂) = −c`, which cancels the leading term of
`b = c(X+1)`:

```text
ν(f(r₂)) = ν(b + 1/r₂) < 1 = ν(σr₁),
```

because the shift preserves the degree at infinity.  So `σr₁ ≠ f(r₂)`: the swap assignment is
impossible.

**Step 6 — the identity assignment is a rational Riccati solution.**  `σr₁ = f(r₁) = b + 1/r₁`,
i.e. `r₁·σr₁ = 1 + b·r₁` — exactly the Bessel order Riccati equation, with `r₁ ∈ ℂ(X)`.  That is
refuted by `BesselOrderRiccati.orderBesselRiccati_no_ratFunc_solution`.

Both assignments are impossible, so `(E) ∧ (P)` has no solution with `p ≠ 0`: **the order module of
the Bessel order operator is not imprimitive**.  Together with the already-recorded exclusion of the
reducible case (no rational Riccati solution) and of `ℓ(p) = +1`, item (a) of the classification is
complete, and the Galois group is not contained in the normaliser of a torus.

The Lean formalisation of this argument needs, beyond what the tree already owns
(`BesselOrderRiccati`, `RatFuncShiftDegree`, `MultiplierDichotomyDegreeObstruction`), one new piece:
the order function `v_a` on `ℂ(X)` with its shift law and the "everywhere-even divisor implies
square" theorem.

### Lean progress — the global step of item (a): Steps 2 and 3, unconditionally

Two modules, wired, `lake build`-green, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

`GaloisForLFunctions.HTGeometry.RatFuncOrderSquare`

```text
ratOrd g c                          the order of a rational function at a point: zeros positive,
                                    poles negative
algebraMap_polynomial_ne_zero, algebraMap_num_eq
ratOrd_of_rep                       **the order can be read off any representation `g·B = A`**
ratOrd_mul                          additivity on products
exists_sq_of_even_rootMultiplicity  a polynomial over an algebraically closed field with
                                    everywhere-even root multiplicity is a constant times a square
isSquare_of_even_ratOrd             **a rational function of everywhere-even order is a square**
```

`GaloisForLFunctions.HTGeometry.RatFuncShiftSquareOrbit`

```text
rootMultiplicity_comp_X_add_one
ratOrd_ratShift                     **the shift moves the order along the orbit**:
                                    `ratOrd (σg) c = ratOrd g (c+1)`
finite_ratOrd_support               a rational function has finitely many zeros and poles
even_ratOrd_of_ratShift_mul_sq      **`σf·g² = f ⟹ the order of `f` is even at every point**
isSquare_of_ratShift_mul_sq         **hence `f` is a square**
```

This is exactly Steps 2 and 3 of the argument above, in the generality in which they are true: for
any field of characteristic zero (and algebraically closed for the square), any nonzero `f` and `g`
with `σf·g² = f`.  The descent is the orbit induction — the order of `f` vanishes from some index on
because it has finitely many zeros and poles, and each earlier order differs from the next by
`2·ratOrd g`, so all of them are even.  No degree at infinity is used; this is the global ingredient
the previous entry said the argument needed.

Applied to the imprimitive branch with `f = Δ = e² − 4p` and `g = p`, the discriminant identity
`σΔ·p² = Δ` now gives `Δ = k²` in Lean.  What remains of item (a) is the elementary part:
the identity `(E) ∧ (P) ⟹ (D)` (Step 1), the identification of the pairs `{σr₁, σr₂}` and
`{f(r₁), f(r₂)}` (Step 4), the degree exclusion of the swap (Step 5), and the appeal to
`BesselOrderRiccati.orderBesselRiccati_no_ratFunc_solution` (Step 6).

### Item (a) CLOSED IN LEAN — `no_imprimitive_pair`

`GaloisForLFunctions.HTGeometry.BesselOrderImprimitivity` (wired, built, axiom-clean
`[propext, Classical.choice, Quot.sound]`) proves the whole of item (a) unconditionally:

```text
intDegree_add_eq_of_lt          the strict ultrametric equality for the degree at infinity
ratShift_eq_fieldShiftRatShift  the two constructions of the unit shift agree
besselB, natDegree_besselPoly, besselB_ne_zero, intDegree_besselB, intDegree_two
no_imprimitive_pair             **there are no `e, p ∈ ℂ(X)` with `p ≠ 0` satisfying
                                `(E) σe = e/p + 2b` and `(P) p·σp = 1 + b·e + b²·p`**
```

with `b = c·(X+1)` and `c ≠ 0` — that is, the order module of the Bessel order operator is **not
imprimitive**.  The Lean proof follows the six steps recorded above exactly:

1. `σp = (1 + be + b²p)/p` and `σ(e² − 4p)·p² = e² − 4p` — the discriminant identity, by
   `field_simp`;
2. `e² − 4p ≠ 0`, because otherwise `e/2` solves the Bessel Riccati equation
   (`orderBesselRiccati_no_ratFunc_solution`);
3. `IsSquare (e² − 4p)` by `isSquare_of_ratShift_mul_sq` — the global orbit-parity theorem of the
   previous entry;
4. with `e² − 4p = k·k`, the ratios `r₁, r₂ = (e ± k)/2` satisfy `r₁ + r₂ = e`, `r₁r₂ = p`, and
   `(σr₁ − f(r₁))·(σr₁ − f(r₂)) = 0` for `f(r) = b + 1/r`, because the two pairs have the same sum
   (by `(E)`) and the same product (by `(P)`);
5. degrees at infinity: `ν(p) = 0` from the discriminant identity, `ν(e) = 1` from `(E)` and `(P)`
   via the strict ultrametric equality, hence `{ν(r₁), ν(r₂)} = {1, −1}`;
6. the identity assignment gives a rational Riccati solution, refuted; the swap assignment gives
   `σr = b + 1/r'` with `ν(1/r') = −1 < 1 = ν(b)`, so the right side has degree `1` while the left
   has degree `−1` — refuted.

**Consequence for the card.**  Item (a) of the classification is complete.  Together with the
already-recorded exclusion of the reducible case (no rational Riccati solution) and of the branch
`ℓ(p) = +1`, the Galois group of the Bessel order recurrence is not contained in the normaliser of
a torus.  What remains on this card is item (b): the *linearity* of the differential relation
produced by differential algebraicity, which is a separate open core recorded above.

### Lean progress — the unipotent route of item (b), reduced to one nonvanishing

The entry "Where the linearity has to come from" split the remaining obligation into

1. exclude imprimitivity — **now closed**, `no_imprimitive_pair`;
2. produce a unipotent family in a Zariski-dense, non-imprimitive differential algebraic subgroup
   of `SL₂`.

`GaloisForLFunctions.HTGeometry.UnipotentParameterSubgroup` (wired, built, axiom-clean) formalises
the whole of the mechanism `(2)` feeds:

```text
unipotentUpper, unipotentUpper_zero, unipotentUpper_mul, unipotentUpper_inv
unipotentParams          **the parameters `t` with `u(t) ∈ G` form an additive subgroup**, for any
                         multiplicative subgroup `G` of `2×2` matrices
unipotentSubstHom, unipotentSubst
                         substitution of `u(X)` into a differential polynomial in the four entries
evalOver_unipotentSubst  **the substitution computes the value at the unipotent** — the entries `1`
                         and `0` are differential constants, so all their jets above order zero
                         vanish and the substitution is a plain `MvPolynomial` algebra map
exists_nonzero_linear_jet_relation_of_unipotentParams
                         **a nonzero linear jet relation on the unipotent parameters**, from a
                         differential-algebraic constraint on the group
```

The last theorem is the exact shape
`DifferentialGaloisScalarZeroSet.isomonodromy_of_no_riccati_of_linearRelation` consumes, and it is
proved from `AdditiveDifferentialSubgroupLinear.exists_nonzero_linear_jet_relation_of_addSubgroup`
(Cassidy's additive classification, already in the tree).

Its one hypothesis is `unipotentSubst P ≠ 0`.  That is a *sharper* form of item `(2)`: it does not
ask for a unipotent in the group, only that the defining differential polynomial does not vanish
identically along the whole unipotent line — equivalently, that the group's differential-algebraic
constraint is not blind to the unipotent direction.  Since the group is Zariski dense, its
Kolchin closure is not contained in the normaliser of a torus (item `(1)`), and the unipotent
direction is exactly the one such a group cannot ignore; making that last implication a theorem is
what remains of item (b).

### Lean progress — the tangent space is a module over the constants

`cassidy_sl2` consumes a `C`-submodule `L` of `sl₂(U)`.  The Lie algebra of a differential algebraic
group is its tangent space at the identity, and
`GaloisForLFunctions.HTGeometry.DifferentialTangentSubmodule` (wired, built, axiom-clean) proves
that tangent spaces have exactly that structure, in any number of differential indeterminates:

```text
differentialJet_eq_zero_zero, differentialJet_const_mul
    **jets are linear over the differential constants**: `δ^n(c·x) = c·δ^n x` when `δc = 0`
linearisationForm, linearisationForm_add, linearisationForm_zero, linearisationForm_const_smul
    the linearisation `∑_v (∂_v F)(p)·δ^{v.2} X_{v.1}` is additive and constant-homogeneous in the
    perturbation
tangentSpace p F s : Submodule (differentialConstants C) (ι → C)
    **the tangent directions at a point of the zero set of `F` form a module over the constants**
mem_tangentSpace_iff_snd_eq_zero
    it is exactly the vanishing locus of the `ε`-part at the dual point `p + εX`
mem_tangentSpace_of_evalOver_dual
```

So the two hypotheses of `cassidy_sl2` that are about *linear structure* — that `L` is a
`C`-submodule — are now automatic for the tangent space of any differential algebraic set, with no
group hypothesis at all.  What the group hypothesis is still needed for is bracket-closure and the
line-stabiliser condition; those, together with the Zariski-density transfer, are the residue of
item (b).

### Lean progress — `Ad`-stability of the tangent space

`GaloisForLFunctions.HTGeometry.DifferentialTangentAdjoint` (wired, built, axiom-clean)

```text
dualMatrix p X                    the dual-number matrix `p + εX`
dualMk_mul, dualMatrix_mul        **dual-number matrices multiply by the first-order product
                                  rule**: `(p + εX)(q + εY) = pq + ε(pY + Xq)`
differentialJet_inl, evalOver_inl **the base embeds through the differential evaluation**
matrixZeroSet S                   the matrices over a differential `C`-algebra annihilated by every
                                  member of a family `S` of differential polynomials
mem_zeroSet_dualMatrix_inl        a constant matrix of the zero set stays in it over the duals
adjoint_mem_tangent_of_zeroSet    **the adjoint action preserves the tangent directions at the
                                  identity**: if the dual-number zero set is closed under
                                  multiplication and `g·h = 1` with `g, h` in the zero set, then
                                  `1 + εX` in the zero set gives `1 + ε(g X h)` in it
```

The computation is exact and needs no analysis: `(inl g)(1 + εX)(inl h) = 1 + ε(gXh)` because `ε`
squares to zero, and the two constant factors are in the dual-number zero set because `inl` is a
differential algebra map, so it commutes with every jet and hence with the evaluation of every
differential polynomial.

This is the step between "the tangent space is a module over the constants" and "the tangent space
is closed under the bracket", since the bracket is the derivative of `Ad` along a one-parameter
family: applying `Ad`-stability over `DualNumber C` with `g = 1 + ηX` gives
`Y + η[X, Y]` in the tangent space, and `η·(linearisation at Y)` vanishes exactly when the
linearisation does.  Formalising that last derivative step, together with the line-stabiliser
condition and the Zariski-density transfer, is what remains of item (b).

### Lean progress — the transfer lemma the layered dual-number argument needs

`GaloisForLFunctions.HTGeometry.DifferentialEvalTransfer` (wired, built, axiom-clean)

```text
differentialJet_algHom   **a derivation-compatible ring map moves through every jet**
evalOver_algHom          **the differential evaluation commutes with a differential algebra map**
matrixZeroSet_algHom     hence such a map carries the zero set of a family of differential
                         polynomials into the zero set of the same family over the target
evalOver_inl'            the base-embedding case, recovered from the general statement
```

`evalOver` is `aeval` on the jets of the coordinates, so an algebra map commuting with the
derivation moves through it: through each jet by induction, and through `aeval` because two algebra
maps out of a polynomial ring agreeing on the variables are equal.

This is the reusable form of the step that the previous entry's `evalOver_inl` did by hand, and it
is what the bracket argument needs, since that argument moves between three layers — `C`, its dual
numbers, and their dual numbers — and each move is a differential algebra map.  With it, the
adjoint derivative `(1 + ηX)(1 + εY)(1 − ηX) = 1 + ε(Y + η[X, Y])` becomes a computation in
`dualMatrix_mul` plus two applications of `matrixZeroSet_algHom`.

### The two-layer dual-number model is blocked by an instance diamond — use a four-dimensional model

`DifferentialEvalTransfer` gained the ring-map form of the transfer, which asks only for
compatibility with the derivation and with the constants and so needs no algebra structure of the
target over the source:

```text
evalOver_ringHom        φ (evalOver x P) = evalOver (φ ∘ x) P  for a derivation- and
                        constant-compatible ring map φ
matrixZeroSet_ringHom   hence φ carries the zero set into the zero set
```

That was built to run the bracket argument over `DualNumber (DualNumber C)`.  It cannot be run
there.  **`Differential.deriv` cannot be applied to an element of `DualNumber (DualNumber C)`**: the
`Differential` instance synthesises, but its `Derivation ℤ R R` is built over
`CommRing.toCommSemiring` while the elaborator resolves the `CommSemiring` of
`TrivSqZeroExt (DualNumber C) (DualNumber C)` through `TrivSqZeroExt.commSemiring`.  The two paths
are a diamond, and every form of the application — notation, explicit universe and instance
arguments, type ascription, tactic mode — is rejected with the same mismatch.

So the second infinitesimal must not come from iterating `TrivSqZeroExt`.  The replacement is a
four-dimensional model of `C[ε, η]/(ε², η²)` built directly — components `1, ε, η, εη` with

`(a, b, c, d)·(a', b', c', d') = (aa', ab' + ba', ac' + ca', ad' + da' + bc' + cb')`

— whose `CommRing` and `Differential` instances are one explicit construction each, with no
inherited diamond.  On it the identity `(1 + ηX)(1 + εY)(1 − ηX) = 1 + ε(Y + η[X, Y])` is the same
exact computation, and `matrixZeroSet_ringHom` transports along the two layer inclusions exactly as
intended.  That is the next brick of item (b).

### Lean progress — two independent infinitesimals, built directly

`GaloisForLFunctions.HTGeometry.BiDualNumbers` (wired, built, axiom-clean) supplies the ring the
previous entry named:

```text
BiDual C                       `C[ε, η]/(ε², η²)`, by its four coefficients `re, ep, et, mx`
                               (`1`, `ε`, `η`, `εη`), with explicit `Add`, `Zero`, `Neg`, `One`,
                               `Mul` and a `CommRing` instance proved componentwise
coeff, coeffHom, Algebra C     the base inclusion
derivFun, derivMap             the componentwise derivation, as a `Derivation ℤ`
Differential, DifferentialAlgebra C
epsFun/epsHom, etaFun/etaHom   **the two layer inclusions** `a + ηb ↦ a + εb` and `a + ηb ↦ a + ηb`
                               of the dual numbers, as ring maps
deriv_epsHom, deriv_etaHom, epsHom_algebraMap, etaHom_algebraMap
                               each is derivation- and constant-compatible, so
                               `matrixZeroSet_ringHom` transports along it
```

**The diamond is gone.**  `z′`, `differentialJet n z` and `differentialPolynomialEvalOver x P` all
elaborate on `BiDual C`, which none of them do on `DualNumber (DualNumber C)`.  The reason is that
`BiDual` carries exactly one `CommRing` instance, constructed here, instead of inheriting one
through `TrivSqZeroExt`.

Building the derivation needed one point of care: giving `Derivation ℤ` a `toFun` with `map_smul'`
forces a computation of `zsmulRec` on the four coefficients.  Supplying
`(AddMonoidHom.mk' derivFun _).toIntLinearMap` instead discharges the `ℤ`-linearity from additivity
alone, which is all that is true over `ℤ`.

With this in place the adjoint derivative is the exact computation
`(1 + ηX)(1 + εY)(1 − ηX) = 1 + εY + εη(XY − YX)` in `BiDual`, together with two applications of
`matrixZeroSet_ringHom` along `etaHom` and `epsHom`.

### Lean progress — the adjoint derivative, and with it the bracket

`GaloisForLFunctions.HTGeometry.BiDualAdjointDerivative` (wired, built, axiom-clean)

```text
biMatrix a b c d          the matrix `a + bε + cη + dεη`
biMatrix_mul              **the two-parameter first-order product rule**
                          `(a,b,c,d)(a',b',c',d')
                             = (aa', ab'+ba', ac'+ca', ad'+da'+bc'+cb')`
etaMatrix_eq, epsMatrix_eq
                          `1 ± ηX` and `1 + εY` are the images of the tangent matrices under the
                          two layer inclusions
adjointDerivative_mem_zeroSet
                          **if `1 + ηX`, `1 − ηX` and `1 + ηY` are in the zero set over the dual
                          numbers, and the zero set is closed under multiplication over
                          `C[ε,η]/(ε²,η²)`, then `1 + εY + εη(XY − YX)` is in it**
```

The computation is exact and finite:

`(1 + ηX)(1 + εY)(1 − ηX) = 1 + εY + εη(XY − YX)`,

by two applications of `biMatrix_mul`; the two layer inclusions are derivation- and
constant-compatible, so `matrixZeroSet_ringHom` carries the three factors into the zero set over
`BiDual C`, and closure under multiplication does the rest.

**So the commutator is now visibly a coefficient of a member of the zero set.**  This is the
content of "the Lie algebra of a differential algebraic group is closed under the bracket", up to
extracting the `εη`-coefficient.  That extraction is the statement that the `εη`-component of an
evaluation at a point whose `η`-component vanishes is the linearisation at the base applied to the
`εη`-component of the point — a three-case induction on the differential polynomial, on the same
pattern as the corpus's `snd_differentialPolynomialEvalOver_dual`.  After it, item (b) needs only
the line-stabiliser condition and the Zariski-density transfer, the remaining two hypotheses of
`cassidy_sl2`.

### Lean progress — BRACKET CLOSURE, proved

`GaloisForLFunctions.HTGeometry.BiDualBracketExtraction` (wired, built, axiom-clean)

```text
BiDual.jet_re, jet_ep, jet_et, jet_mx
    the derivation is componentwise, so every jet is
evalOver_biDual_of_et_zero
    **at a point whose `η`-coefficients vanish, the `η`-coefficient of the value vanishes and its
    `(1, εη)` pair is the value of the same polynomial at the dual-number point `re + ε·mx`**
mem_zeroSet_of_biMatrix_et_zero
    hence the `εη`-coefficient of an `η`-free member of the zero set is a tangent direction
bracket_mem_zeroSet
    **the Lie algebra of a differential algebraic group is closed under the bracket**:
    from `1 + ηX`, `1 − ηX`, `1 + ηY` in the zero set over the dual numbers and closure under
    multiplication over `C[ε,η]/(ε²,η²)`, one gets `1 + η(XY − YX)` in it
```

The mechanism is that on `{η-coefficient = 0}` the pair `(1, εη)` multiplies exactly like a dual
number — `(z·w).re = z.re·w.re` and `(z·w).mx = z.re·w.mx + z.mx·w.re`, the cross terms
`z.ep·w.et + z.et·w.ep` vanishing — and that this locus is closed under products and under the
derivation, hence under every jet.  The three-case induction on the differential polynomial then
transports the whole evaluation.

**Item (b)'s Lie-algebra half is complete.**  Combining with the earlier entries, the tangent space
at the identity of a differential algebraic subgroup is a module over the differential constants
(`DifferentialTangentSubmodule`), stable under the adjoint action (`DifferentialTangentAdjoint`),
and closed under the bracket (here) — the first two hypotheses of `cassidy_sl2`, `htr` being
immediate for `SL₂`.  What remains of item (b) is the line-stabiliser condition `hline` and the
Zariski-density transfer `hdense`.

### Lean progress — the tangent space at the identity, packaged

`GaloisForLFunctions.HTGeometry.IdentityTangentSubmodule` (wired, built, axiom-clean)

```text
matrixTangent S            the tangent directions at the identity, as a
                           `Submodule (differentialConstants C)` — the intersection of the
                           linearisation kernels over the family
dualMatrix_eq_dualPoint
mem_matrixTangent_iff      **`X` is a tangent direction exactly when `1 + εX` is in the zero set
                           over the dual numbers**: the `ε`-free part of the value is the value at
                           the identity, which vanishes because the identity is in the zero set,
                           and the `ε`-part is the linearisation
dualMatrix_neg_mem_zeroSet the negative of a tangent direction is a tangent direction
bracket_mem_zeroSet_of_one **bracket closure with no hypothesis on `−X`**
```

This closes the gap between the two vocabularies: the Lie-algebra statements are about the
`Submodule` over the constants, while the group statements are about membership of `1 + εX` in the
zero set, and `mem_matrixTangent_iff` is the translation.  In particular the earlier
`bracket_mem_zeroSet` loses its `−X` hypothesis, which was an artefact of stating the adjoint
conjugation with an explicit inverse.

Status of `cassidy_sl2`'s four hypotheses for the tangent space of a differential algebraic
subgroup of `SL₂`:

| hypothesis | status |
|---|---|
| `L` a `C`-submodule | `matrixTangent` |
| `htr` (traceless) | immediate for `SL₂` |
| `hbr` (bracket-closed) | `bracket_mem_zeroSet_of_one` |
| `hdense` (spans `sl₂(U)`) | **open** — the Zariski-density transfer |
| `hline` (trivial line stabilisers) | **open** |

### Lean progress — `hline`, reduced to one nonvanishing

`GaloisForLFunctions.HTGeometry.ScalarStabiliserRelation` (wired, built, axiom-clean)

```text
exists_monic_relation_of_linear
    **a nonzero linear jet relation becomes a monic one**: divide by the coefficient of the highest
    jet that occurs, by induction down the index
scalarStabiliser S Y
    **the scalars `c` with `c·Y` again in the tangent space form an additive subgroup** — the
    tangent space is a module over the constants and scaling is additive in the scalar
exists_monic_relation_scalarStabiliser
    **hence the scalar stabiliser solves a monic scalar linear differential equation** as soon as it
    lies in the zero set of one nonzero differential polynomial in one indeterminate
```

The last statement is exactly the `hsol` hypothesis of
`DifferentialCassidyClassification.cassidy_sl2_of_differentialSolution`, which is the differential
form of `cassidy_sl2`'s `hline`.  So `hline` has the same shape of residue as the unipotent route
of the previous entries: a *nonvanishing*, namely that the family's constraint does not vanish
identically along the line `c ↦ c·Y`.  Its failure is precisely the degenerate case where the
tangent space is all of `sl₂(U)` — in which the Galois group is everything and the card's conclusion
holds for a different and easier reason.

Updated status of `cassidy_sl2_of_differentialSolution` for the tangent space of a differential
algebraic subgroup of `SL₂`:

| hypothesis | status |
|---|---|
| `L` a submodule over the constants | `matrixTangent` |
| `htr` | immediate for `SL₂` |
| `hbr` | `bracket_mem_zeroSet_of_one` |
| `hsol` | `exists_monic_relation_scalarStabiliser`, modulo the nonvanishing |
| `hdense` | **open** — the Zariski-density transfer |

### Lean progress — `hdense`'s irreducibility half

`GaloisForLFunctions.HTGeometry.Sl2AdjointIrreducible` (wired, built, axiom-clean)

```text
unipotentLower, upperConj, lowerConj
upperConj_entry, lowerConj_entry
    the four entries of `u(t)·A·u(−t)` and `l(t)·A·l(−t)`, explicitly
raising_mem_of_adStable
    **the raising matrix is in every nonzero subspace of traceless matrices stable under the upper
    unipotents**
sl2_of_adStable
    **the adjoint action on `sl₂` is irreducible**: a nonzero subspace of traceless matrices stable
    under conjugation by both unipotent lines is everything
```

The proof is a finite computation.  Conjugating `A` by `u(t)` moves it by a quadratic polynomial in
`t`, so evaluating at `t = ±1` and subtracting twice the value at `t = 0` isolates the two
coefficients: `−2·A₁₀·e` and `2·A₁₀·h − 4·A₀₀·e`.  From a nonzero traceless `A` one of them is a
nonzero multiple of `e` in every case — `A₁₀ ≠ 0` gives it from the first, `A₁₀ = 0 ≠ A₀₀` from the
second, and `A₁₀ = A₀₀ = 0` makes `A` itself a multiple of `e`.  Conjugating `e` by the lower
unipotents then produces `−2f` and `−2h` the same way, and `h, e, f` span the traceless matrices.

This is the irreducibility that makes `hdense` work: the `U`-span of the Lie algebra of a
Zariski-dense subgroup is stable under the adjoint action of the whole group, hence — being nonzero
— is all of `sl₂(U)`.  What is left of `hdense` is the two remaining links: that the span is stable
under conjugation by the *unipotents of `SL₂(U)`* rather than only by group elements (the
Zariski-closure step), and that the Lie algebra is nonzero.

### Lean progress — `hdense`'s Zariski-closure step

`GaloisForLFunctions.HTGeometry.AdjointStableZariskiClosure` (wired, built, axiom-clean)

```text
adjugate_two                     the adjugate of a `2×2` matrix, explicitly
det_unipotentUpper/Lower, adjugate_unipotentUpper/Lower
                                 the unipotents have determinant one and adjugate `u(−t)`
conj_mem_of_dense                **adjoint stability passes from `G` to every determinant-one
                                 matrix**
upperConj_mem_of_dense, lowerConj_mem_of_dense
sl2_of_dense                     **the span of the Lie algebra of a Zariski-dense subgroup is all
                                 of `sl₂`**
```

For determinant one the inverse *is* the adjugate, which is a polynomial in the entries, so for
fixed `A` and fixed functional `φ` the map `g ↦ φ(g·A·adj g)` is a polynomial function of `g`.  If
`V` is stable under conjugation by `G`, that polynomial vanishes on `G` for every `φ` killing `V`;
density extends the vanishing to all determinant-one matrices; and over a field a subspace is the
common kernel of the functionals killing it
(`Submodule.exists_dual_map_eq_bot_of_notMem`), so the conjugate is back in `V`.

The density hypothesis is stated exactly where it is used — as the extension of vanishing for those
specific polynomial functions — rather than through a topology, so nothing about the Zariski
topology has to be built.

**`hdense` is now complete except for one point**: that the Lie algebra is nonzero.  Everything
else in `cassidy_sl2_of_differentialSolution` is supplied:

| hypothesis | status |
|---|---|
| `L` a submodule over the constants | `matrixTangent` |
| `htr` | immediate for `SL₂` |
| `hbr` | `bracket_mem_zeroSet_of_one` |
| `hsol` | `exists_monic_relation_scalarStabiliser`, modulo its nonvanishing |
| `hdense` | `sl2_of_dense`, modulo `L ≠ 0` |

### Lean progress — `htr`, with no nondegeneracy

`GaloisForLFunctions.HTGeometry.Sl2TangentTraceless` (wired, built, axiom-clean)

```text
detPoly                        the determinant equation `x₀₀x₁₁ − x₀₁x₁₀ = 1`, as a differential
                               polynomial
evalOver_detPoly               its value at any point
trace_eq_zero_of_mem_zeroSet   **a tangent direction at the identity of the determinant equation is
                               traceless**
```

Linearising the determinant at the identity gives the trace, exactly:

`det(1 + εX) = (1 + εX₀₀)(1 + εX₁₁) − εX₀₁·εX₁₀ = 1 + ε(X₀₀ + X₁₁)`

because `ε² = 0`.  So `htr` costs nothing beyond the determinant equation being in the family — no
nondegeneracy, no density, no closure hypothesis.

With this, the four structural hypotheses of `cassidy_sl2_of_differentialSolution` are all
unconditional for the tangent space of the zero set of a family containing `detPoly`:

| hypothesis | supplied by | residue |
|---|---|---|
| `L` a submodule over the constants | `matrixTangent` | none |
| `htr` | `trace_eq_zero_of_mem_zeroSet` | none |
| `hbr` | `bracket_mem_zeroSet_of_one` | none |
| `hsol` | `exists_monic_relation_scalarStabiliser` | the substituted polynomial is nonzero |
| `hdense` | `sl2_of_dense` | `L ≠ 0` |

The two residues are the content of the word "proper" in Cassidy's theorem — a Zariski-dense
*proper* differential algebraic subgroup is conjugate to `SL₂` over the constants — and are not
removable: they fail exactly when the differential Galois group is everything, which is the case in
which the card's conclusion holds for the direct reason that no differential relation exists at all.
Turning that observation into a Lean dichotomy is what closes item (b).

### Lean progress — the capstone: Cassidy for the tangent space, assembled

`GaloisForLFunctions.HTGeometry.DifferentialSubgroupCassidy` (wired, built, axiom-clean)

```text
matrixTangentM S hone            the Lie algebra, as a submodule of *matrices* over the constants
span_conj_stable                 the span of a conjugation-stable set is conjugation-stable
mem_scalarStabiliser_iff_smul_mem
cassidy_of_matrixTangent         **Cassidy's classification for the tangent space of a differential
                                 algebraic subgroup of `SL₂`**
```

`cassidy_of_matrixTangent` applies `cassidy_sl2_of_differentialSolution` to `matrixTangentM S hone`,
discharging its four structural hypotheses from the modules of the previous entries:

* the module structure is `matrixTangentM` itself;
* `htr` from `trace_eq_zero_of_mem_zeroSet` (needs `detPoly ∈ S`);
* `hbr` from `bracket_mem_zeroSet_of_one` (needs closure under multiplication over
  `C[ε,η]/(ε²,η²)`);
* `hdense` from `sl2_of_dense` via `span_conj_stable`;
* `hsol` from `exists_monic_relation_scalarStabiliser`.

Its remaining hypotheses are exactly the two nondegeneracies, now carried by one statement rather
than scattered across eight modules:

```text
hLne     : ∃ A ∈ matrixTangentM S hone, A ≠ 0
hsolres  : ∀ Y ∈ matrixTangentM S hone, Y ≠ 0 →
             ∃ P ≠ 0, ∀ c ∈ scalarStabiliser S Y, evalOver (fun _ => c) P = 0
```

together with the group data — closure of the dual-number zero set under multiplication, adjoint
stability of the Lie algebra under `G`, and the polynomial form of Zariski density.  Both
nondegeneracies are the word *proper* in Cassidy's theorem; they fail exactly when the differential
Galois group is everything.

**Conclusion for the card.**  Item (b) is reduced from "Cassidy's structure theorem for
Zariski-dense differential algebraic subgroups of `SL₂`" — a multi-module project — to a single
named Lean theorem plus the properness dichotomy.  The classification itself is no longer an open
core of this card.

### Lean progress — the line-stabiliser hypothesis, replaced by finite dimension

`GaloisForLFunctions.HTGeometry.BoundedLineStabiliserFinite` (wired, built, axiom-clean)

```text
boundedOverBase_smul_of_finiteDimensional
    **finite dimension bounds the scalars carrying `Y` into `L`**: `finrank L + 1` of them give
    that many elements of `L`, which are dependent, and the relation divides by `Y`
cassidy_sl2_of_finiteDimensional
    **Cassidy's classification for `sl₂` with a finite-dimensional Lie algebra** — no line-stabiliser
    hypothesis at all
```

This removes the `hsol`/`hline` residue outright.  In `cassidy_sl2_of_bounded` the line-stabiliser
condition asks that the scalars carrying a nonzero `Y` into `L` admit a fixed-length linear relation
over the base; if `L` is finite dimensional that is automatic, because `c ↦ c·Y` is an injective
base-linear map from those scalars into `L`, so `finrank L + 1` of them are already dependent, and
the resulting relation can be divided by `Y ≠ 0`.

So the classification now needs only three hypotheses about the Lie algebra — traceless,
bracket-closed, spanning — plus **finite dimensionality over the constants**, which for a
differential algebraic group of finite type is automatic and is a far more checkable condition than
the line-stabiliser bound.

Card 3 item (b) accordingly has one residue left rather than two:

| hypothesis | supplied by | residue |
|---|---|---|
| `L` a submodule over the constants | `matrixTangent` / `matrixTangentM` | none |
| `htr` | `trace_eq_zero_of_mem_zeroSet` | none |
| `hbr` | `bracket_mem_zeroSet_of_one` | none |
| line stabilisers | `cassidy_sl2_of_finiteDimensional` | `FiniteDimensional` of the Lie algebra |
| `hdense` | `sl2_of_dense` | `L ≠ 0` |

### The capstone in its final form, and what item (b) now is

`DifferentialSubgroupCassidy` gained `cassidy_of_matrixTangent_finite` (wired, built, axiom-clean):
Cassidy's classification for the tangent space of a differential algebraic subgroup of `SL₂`, with
the line-stabiliser hypothesis replaced by finite dimensionality.  Its complete hypothesis list is

```text
hone       : the identity is in the zero set
hdet       : the determinant equation is in the family
hmulBi     : the zero set is closed under multiplication over `C[ε,η]/(ε²,η²)`
hGstable   : the Lie algebra is `Ad`-stable under `G`
hdensePoly : `G` is Zariski dense, in the polynomial form the proof uses
hLne       : the Lie algebra is nonzero
hfin       : the Lie algebra is finite dimensional over the constants
```

and its conclusion is that one conjugation carries the Lie algebra onto the constant span of
`h`, `e`, `f`.

The first five are structural facts about a differential algebraic subgroup — three of them
(`hone`, `hdet`, `hmulBi`) say only that the family defines a group containing the identity inside
`SL₂`, and two (`hGstable`, `hdensePoly`) are the adjoint stability and Zariski density that the
card's setting supplies.  The last two, `hLne` and `hfin`, are the **dimension** statements, and
they are equivalent to the group being a *proper* differential algebraic subgroup: for the improper
group `SL₂(U)` the Lie algebra is all of `sl₂(U)`, which is infinite dimensional over the constants,
and for a group with no infinitesimal directions it is zero.

So item (b) is now exactly the properness dichotomy, in the parameterised Picard–Vessiot form the
card already names as its outstanding classical input:

> either the parameterised Galois group is the whole of `SL₂`, in which case the output satisfies no
> differential relation at all and the card's conclusion is immediate; or it is proper, in which
> case its Lie algebra is nonzero and finite dimensional over the constants, and
> `cassidy_of_matrixTangent_finite` conjugates it into the constants, which is what the
> isomonodromy endgame consumes.

Nothing between those two branches is missing any more: the classification, the Lie-algebra
structure, the adjoint action, the bracket, the trace, the line stabilisers, the spanning and the
irreducibility are all Lean theorems in the tree.

### Lean progress — a finite subgroup is not Zariski dense

`GaloisForLFunctions.HTGeometry.FiniteNotZariskiDense` (wired, built, axiom-clean)

```text
unipotentUpper_entry, unipotentUpper_injective
    the upper unipotents form an injective line inside the determinant-one matrices, their `(0,1)`
    entry running over the whole field
exists_separating_poly_of_finite
    **a finite set of matrices is separated from `SL₂` by one polynomial in the `(0,1)` entry**:
    the product of the linear factors at the entries occurring in the set vanishes on it, and
    — the field being infinite — misses some unipotent
```

This is the elementary half of `hLne`.  The chain is: a differential algebraic group whose Lie
algebra is zero has no infinitesimal directions, hence is finite; a finite group is not Zariski
dense, by the theorem above; but the Galois group of the Bessel order recurrence *is* Zariski dense,
because it is irreducible (no rational Riccati solution) and not imprimitive
(`no_imprimitive_pair`), so Burnside puts its span at all of `M₂`.  So the Lie algebra is nonzero.

The one link in that chain still to be formalised is the first: *zero Lie algebra implies finite*,
which is the Kolchin dimension statement for differential algebraic groups.  It, together with
finite dimensionality of the Lie algebra of a proper subgroup, is precisely the parameterised
Picard–Vessiot input the card lists as outstanding — and it is now the *only* input, with both of
its consumers (`hLne`, `hfin`) and every other step of the classification proved.

### Lean progress — the constant part of the Lie algebra is the classical one

`GaloisForLFunctions.HTGeometry.ConstantTangentDirections` (wired, built, axiom-clean)

```text
differentialJet_eq_zero_of_deriv_eq_zero
    a differential constant has no jets above order zero
linearisationForm_const
    **at a perturbation with constant entries the linearisation collapses to the algebraic
    differential**: only the partial derivatives with respect to the order-zero variables contribute
```

This is what makes `hLne` reachable without Kolchin dimension theory.  The constant part of the Lie
algebra of a differential algebraic group is the tangent space of the *underlying algebraic
variety* at the identity, cut out by finitely many ordinary linear equations rather than by
differential ones — and for a group whose Zariski closure is `SL₂` that tangent space is `sl₂`,
which is nonzero.

So the route to `hLne` is now:

1. `linearisationForm_const` reduces membership of a constant matrix in the Lie algebra to the
   vanishing of the order-zero differential;
2. that differential is the differential of the underlying algebraic variety, whose Zariski closure
   is `SL₂` because the group is irreducible (no rational Riccati solution) and not imprimitive
   (`no_imprimitive_pair`);
3. hence every constant traceless matrix is a tangent direction, and in particular the Lie algebra
   is nonzero.

Step 2's remaining content is the identification of the order-zero differential with the algebraic
one for the *specific* family, which is bookkeeping rather than new mathematics; nothing in this
route needs "zero Lie algebra implies finite".

### Lean progress — `hLne` reduced to the algebraic differential

`GaloisForLFunctions.HTGeometry.ConstantLieAlgebraNonzero` (wired, built, axiom-clean)

```text
const_mem_matrixTangentM
    **a constant matrix annihilated by every order-zero differential of the family at the identity
    is a tangent direction**
matrixTangentM_ne_bot_of_const
    **hence the Lie algebra is nonzero as soon as one nonzero constant matrix is annihilated**
```

This finishes the reroute of `hLne`.  Membership of a *constant* matrix in the Lie algebra is now
decided by an ordinary linear condition — the vanishing of

`∑_{v ∈ P.vars, v.2 = 0} (∂_v P)(1) · X_{v.1}`

for each `P` in the family — with no differential content at all, because constants have no jets
above order zero.  For a family defining a group whose Zariski closure is `SL₂`, that sum is the
differential of the underlying algebraic variety at the identity, which annihilates all of `sl₂`.

`hLne` is therefore no longer a Kolchin-dimension statement.  Combined with the previous entries,
item (b)'s complete state is:

| hypothesis of `cassidy_of_matrixTangent_finite` | supplied by |
|---|---|
| `L` a submodule over the constants | `matrixTangentM` |
| `htr` | `trace_eq_zero_of_mem_zeroSet` |
| `hbr` | `bracket_mem_zeroSet_of_one` |
| line stabilisers | `cassidy_sl2_of_finiteDimensional` |
| `hdense` | `sl2_of_dense` |
| `hLne` | `matrixTangentM_ne_bot_of_const` |
| `hfin` | **open** — finite dimensionality of the Lie algebra |

One hypothesis is left, and it is the one that expresses properness: an improper group has
`L = sl₂(U)`, infinite dimensional over the constants.

### The properness dichotomy, in Lean

`DifferentialSubgroupCassidy` gained `cassidy_dichotomy` (wired, built, axiom-clean):

> Either the Lie algebra of the differential algebraic subgroup is infinite dimensional over the
> constants — which is what happens when the group is the whole of `SL₂` — or one conjugation
> carries it onto the constant span of `h`, `e`, `f`.

Its hypotheses are the six structural ones, all discharged in the tree: `hone`, `hdet`, `hmulBi`
(the family defines a group inside `SL₂` containing the identity), `hGstable` and `hdensePoly`
(adjoint stability and Zariski density), and `hLne` (via `matrixTangentM_ne_bot_of_const`).  No
dimension hypothesis is left in the statement: the dichotomy is unconditional, and its positive
branch is the full classification.

**This is the final form of item (b) that the corpus can reach without the parameterised
Picard–Vessiot correspondence.**  What the correspondence supplies, and nothing else does, is that
differential algebraicity of the output rules out the first branch — a group with an infinite
dimensional Lie algebra over the constants imposes no differential relation on its matrices.  With
that one implication, `cassidy_dichotomy` closes item (b), and with it the card:
`isomonodromy_of_no_riccati_of_linearRelation` consumes the second branch directly, since a Lie
algebra conjugated into the constants gives `δ` of every entry equal to zero — a linear differential
relation.

## Lean progress — the dimension hypothesis is GONE, and the group step is proved (2026-08-29)

The previous entry left item (b) as `hfin`: finite dimensionality of the Lie algebra over the
constants.  That hypothesis is *equivalent to the conclusion* — for the improper group `SL₂(U)` the
Lie algebra is `sl₂(U)`, infinite dimensional over the constants — so `cassidy_dichotomy` carried no
information beyond an excluded middle.  It is now replaced by a sharp, unconditional dichotomy, and
the passage from the Lie algebra to the *group* is proved.  Six new modules, all axiom-clean
(`[propext, Classical.choice, Quot.sound]`) and wired into `GaloisForLFunctions.HTGeometry`.

### `Sl2AbsorbingLine` — absorption

```text
sl2E_00 … sl2H_11                   the entries of the standard basis
sl2_bracket_E, sl2_bracket_E_E,     one and two brackets against the raising matrix,
sl2_bracket_F_F                     two against the lowering matrix
sl2_bracket_EF, _FE, _HE, _HF       the structure constants
sl2_traceless_decomp                a traceless matrix is `Z₀₀ h + Z₀₁ e + Z₁₀ f`
absorbSubmodule L                   **the matrices whose whole `U`-line lies in `L`** — a
                                    `U`-submodule, not merely a `C`-submodule
bracket_mem_absorbSubmodule         it is a bracket ideal against every traceless matrix, because
                                    `c[Z,W] = [cZ, W]` and `span_U L = sl₂(U)`
sl2_eq_of_absorbing                 **absorption**: a bracket-closed `C`-subspace of `sl₂(U)` whose
                                    `U`-span is `sl₂(U)` and which contains one whole `U`-line is
                                    all of `sl₂(U)`
```

The proof of the last is `sl₂`-simplicity, done by hand in `2 × 2`: two brackets against `e` return
`−2 Z₁₀ · e`, two against `f` return `−2 Z₀₁ · f`, and a diagonal `Z` is handled by a single bracket
against `e`; then `[e,f] = h` and `[h,f] = −2f` fill in the rest.

### `TangentLineStabiliserDichotomy` — where the linear operator comes from

```text
differentialJet_mul_leibniz         the binomial Leibniz rule for the algebraic jets, from
                                    `DerivationIterateLeibniz` (no heavy import)
exists_linearOperator_linearisationForm_smul
    **substituting `c · Y` into a linearisation gives a linear differential operator in `c`**:
    `linearisationForm p P s (c·Y) = ∑_{k ≤ N} b k · δ^k c`, with
    `b k = ∑_{v ∈ s, k ≤ v₂} C(v₂,k) (∂_v P)(p) δ^{v₂−k}(Y_{v₁})`
exists_monic_of_linearOperator      a nonzero coefficient makes the relation monic
tangent_lineStabiliser_dichotomy    **the dichotomy**: for a direction `Y`, either every scalar
                                    multiple of `Y` is tangent, or the scalars `c` with `c·Y`
                                    tangent solve one monic scalar linear differential equation
```

This is the exact input `cassidy_sl2_of_differentialSolution` asks for, and it is *free*: the
tangent space is cut out by linearisations, and a linearisation is linear.

### `CassidyTangentDichotomy` — Cassidy with no dimension hypothesis

```text
mem_matrixTangentM_iff_linearisation   membership in the Lie algebra, spelled out
cassidy_tangent_dichotomy
    **either the Lie algebra is all of `sl₂(U)`, or one conjugation carries it onto `sl₂` over the
    differential constants** — no `hfin`, no side condition
```

The case split is on whether some nonzero `Y` has its whole `U`-line inside `L`.  If one does,
`sl2_eq_of_absorbing` gives everything; if none does, the dichotomy supplies the monic operator for
*every* nonzero `Y`, and the corpus's `cassidy_sl2_of_differentialSolution` applies.

### `Sl2ConstantNormaliser` — the normaliser of `sl₂(K)`

```text
entries_mem_of_conj_sl2
    **an invertible matrix whose adjoint action carries `e`, `f`, `h` into a square-root-closed
    subfield `K`, and whose determinant lies in `K`, has all four entries in `K`**
```

Explicit: writing `g = [[a,b],[c,d]]`,

```text
g e adj(g) = [[−ac, a²], [−c², ac]],
g f adj(g) = [[bd, −b²], [d², −bd]],
g h adj(g) = [[ad+bc, −2ab], [2cd, −(ad+bc)]],
```

so every pairwise product of `a,b,c,d` lies in `K`; `ad − bc = det g ∈ K` splits `ad` from `bc`;
one of `a`, `b` is nonzero, its square is in `K`, hence so is it, and dividing the products by it
recovers the other three entries.  Note the determinant need only lie in `K`, not equal one — the
difference Galois group of the order recurrence lands in `det = ±1`, not in `SL₂`.

### `FiniteConstantSpanOperator` — finite span ⟹ one operator

```text
exists_nonzero_linearJet_relation_of_span
    **a finite family `w : ι → U` lies in the solution set of a nonzero linear differential operator
    of order at most `#ι`**, and hence so does its whole span over the constants
```

No Wronskian: the `#ι + 1` jet vectors `(δ^k w j)_j` are that many vectors in a `#ι`-dimensional
space, hence dependent, and a dependence *is* the operator.  The solution set is a module over the
constants, so it swallows the span.

### `CassidyGroupConstants` — from the Lie algebra to the group

```text
entries_mem_of_mem_span_sl2         members of the constant span of `h,e,f` have constant entries
sq_root_mem_differentialConstants   algebraically closed constants are square-root closed
conj_entries_mem_constants
    **the group step**: if one conjugation carries the Lie algebra onto `sl₂` over the constants,
    then every group element with nonzero constant determinant has constant entries after that
    conjugation
conjProducts P Q                    the sixteen products `Q i l · P k j`
entries_mem_span_of_conj_constants  undoing the conjugation lands every entry in their constant span
exists_linearJet_relation_of_conj_constants
    hence **one** nonzero linear differential operator annihilates every entry of every element
cassidy_group_dichotomy
    **the capstone**: for a differential algebraic subgroup of `GL₂` with traceless, bracket-closed,
    spanning Lie algebra, either the Lie algebra is all of `sl₂(U)`, or one nonzero scalar linear
    differential operator annihilates every entry of every group element
```

The group step needs **no exponential map**.  The Lie algebra of a differential algebraic subgroup
is stable under the adjoint action of the group (`adjoint_mem_tangent_of_zeroSet`, already owned),
so after the conjugation every group element normalises `sl₂` over the constants, and
`entries_mem_of_conj_sl2` finishes.  Undoing the conjugation costs only a bounded-dimensional
constant span, which `exists_nonzero_linearJet_relation_of_span` converts into a single operator.

The second alternative of `cassidy_group_dichotomy` is **exactly** the hypothesis `hGL` of
`DifferentialGaloisScalarZeroSet.isomonodromy_of_no_riccati_of_linearRelation`.

### What item (b) now is

One statement, and it is the only thing between this card and the isomonodromy contradiction:

> **exclude the improper branch** — the tangent space of the difference Galois group of the order
> recurrence is not all of `sl₂`, given that `K_ν(s)` is differentially algebraic.

Everything else is proved: irreducibility (no rational Riccati solution), non-imprimitivity
(`no_imprimitive_pair`), the Lie algebra's tracelessness, bracket closure, spanning and adjoint
stability, the classification itself, the group step, and the endgame.

### The improper branch, stated exactly

`cassidy_group_dichotomy`'s first alternative is

```text
∀ Z, Z.trace = 0 → Z ∈ matrixTangentM S hone
```

i.e. **every linearisation `linearisationForm 1 P P.vars` of every `P ∈ S` vanishes on all of
`sl₂`**.  For the tautological family `S = {P over C : P vanishes on the Galois monoid}` — which is
radical, since `U` is a field — this says the Galois group has full Lie algebra, and the classical
consequence is that it is the whole of `SL₂`, whose Picard–Vessiot extension has differential
transcendence degree three; `K_ν(s)` would then not be differentially algebraic.

Three separate things are needed to make that argument Lean-complete, and none of them is a
classification statement:

1. **A family `S` with the monoid property.**  `hmulBi` (the zero set over the bi-dual numbers is
   closed under multiplication) is the statement that `S` is a differential *Hopf* ideal.  The
   corpus already owns the object that supplies it: `E`, the constants subalgebra of the tensor
   square, with `adjoin_tensor_comparison_eq_top` and `TorsorDecomposition`; `S` is the kernel of
   `C{X_ij}[1/det] → E`, and comultiplication gives `hmulBi`.
2. **Kolchin smoothness in characteristic zero** (Cartier), which is what makes the tangent space of
   a *radical* differential ideal the true tangent space — without it `{t : t² = 0}` has full
   tangent space at `0` and is a monoid, so no dimension argument can run.
3. **The dimension step**: a Kolchin-closed submonoid of `SL₂(U)` with full Lie algebra is
   `SL₂(U)`.  With (2) this is the one-parameter statement `k = {t : u(t) ∈ H}` is a Kolchin-closed
   additive submonoid of `U` with full tangent space at `0`, hence all of `U`, plus the elementary
   fact that two opposite unipotent one-parameter subgroups generate `SL₂`.

That is the remaining programme for item (b).  Everything downstream of it — the classification, the
group step, the operator, the endgame — is now unconditional in the tree.

## Lean progress — geometric reducedness in characteristic zero (a mathlib gap) (2026-08-29)

The Galois-correspondence half of the endgame carries one instance hypothesis it cannot yet
discharge: `[IsReduced E]` for the constants algebra `E ⊆ R ⊗_K R`.  The card previously recorded
this as "Cartier's theorem for the Galois group scheme".  **It is not**: `E` is a subalgebra of
`R ⊗_K R`, so it is enough that the *tensor square of the Picard–Vessiot ring* is reduced, and `R`
is reduced because it is `σ`-simple (`isReduced_of_isSigmaSimple`).  What is needed is therefore the
purely commutative statement

> over a field of characteristic zero, a reduced algebra stays reduced after base change,

which is Cartier-free.  Mathlib has the class `Algebra.IsGeometricallyReduced` but **no instance for
a perfect base field**, so the first half of that statement was a genuine mathlib gap.  It is now
closed, unconditionally and axiom-clean, in three new modules wired into `HTGeometry`.

### `SeparableAdjoinRootReduced`

```text
isReduced_adjoinRoot_of_separable
    **A reduced, f monic and separable ⟹ A[X]/(f) reduced**
```

Prime by prime: reduce a nilpotent modulo the monic `f`, leaving a representative of degree
`< deg f`; over the fraction field of `A/P` the polynomial `f` stays monic of the same degree and
stays separable, hence squarefree, hence *radical* in a unique factorisation domain, so it divides
the representative — and the degree bound forces the representative to vanish there.  Every
coefficient therefore lies in every prime, hence in the nilradical, hence is zero.

### `AdjoinRootTensorBaseChange`

```text
tensorPolyEquiv k A                        k[X] ⊗_k A ≃ₐ[k] A[X]
tensorPolyEquiv_includeLeft                and it sends p ⊗ 1 to p.map (algebraMap k A)
adjoinRootTensorRingEquiv f                **AdjoinRoot f ⊗_k A ≃+* AdjoinRoot (f.map …)**
isReduced_adjoinRoot_tensor_of_separable   hence reducedness survives that base change
```

The two algebra maps `k[X] → A[X]` agree because they agree on `X` (`Polynomial.algHom_ext`), and
the ideal bookkeeping is `Ideal.map_span` twice through mathlib's
`Algebra.TensorProduct.quotientTensorEquiv`.

### `GeometricallyReducedCharZero`

```text
isReduced_tensor_of_finiteDimensional
    a reduced algebra stays reduced after base change to a finite **separable** extension
isGeometricallyReduced_of_charZero
    **instance**: over a field of characteristic zero every reduced algebra is geometrically reduced
```

A finitely generated subalgebra of the algebraic closure is finite over `k`, hence a field, hence —
by the primitive element theorem, available because characteristic zero makes every algebraic
extension separable — of the form `AdjoinRoot (minpoly k α)`; mathlib's
`IsReduced.tensorProduct_of_flat_of_forall_fg` assembles the finitely generated pieces.

### What this leaves

Two things, both now precisely named:

1. `R ⊗_K R` reduced for `R` reduced over a characteristic-zero `K` — the *non-algebraic* half.
   With a separating transcendence basis (available in characteristic zero) it reduces to
   `D[X]/(g)` over the domain `D = F ⊗_K K(t₁,…,t_r)`, and
   `isReduced_adjoinRoot_of_separable` finishes; the missing steps are the identification of
   `F ⊗_K K(t)` with a localisation of `F[t]` and the reduction of a Noetherian reduced algebra to
   its finitely many minimal primes.
2. The improper branch of `cassidy_group_dichotomy`, as recorded above.

### The purely transcendental step — `TensorFractionRingDomain` (2026-08-29)

```text
tensorBaseHom                     the base change F ⊗_k P → F ⊗_k Q
exists_denominator_clears         **one nonzero denominator carries any element of F ⊗_k Q into
                                  the image of F ⊗_k P**
tensorBaseHom_injective           the base change is injective (P → Q is, and F is k-flat)
isDomain_tensor_of_isFractionRing **F ⊗_k Q is a domain whenever F ⊗_k P is**, for Q a fraction
                                  ring of the domain P
```

Applied to `P = k[t₁,…,t_r]` this says the base change of a domain along a purely transcendental
extension is a domain — the half of "reduced stays reduced" that the algebraic step
(`isReduced_adjoinRoot_of_separable`) cannot see.  No Nullstellensatz, no Cartier, no smoothness:
the whole proof is that `1 ⊗ q` is a unit and clearing denominators commutes with the tensor.

Unconditional, axiom-clean, wired into `HTGeometry`.

### The reducedness input is CLOSED (2026-08-29)

Two further modules finish the chain, so the endgame's instance hypothesis `[IsReduced E]` is no
longer an input at all.

`TensorReducedCharZero`

```text
isReduced_tensor_of_isAlgebraic          a reduced algebra stays reduced after base change to an
                                         algebraic field extension (characteristic zero)
isReduced_tensor_of_algebraic_over_domain
    the assembly step, with the intermediate field kept **abstract** — an `IntermediateField`
    coercion produces a scalar-action diamond that blocks the nested tensor's ring instance
isReduced_tensor_field_of_charZero
    **F ⊗_k L is reduced for any two field extensions of a characteristic-zero field**
```

The proof is the separating transcendence basis: `M = k(t)` with `t` a transcendence basis of `L`,
`F ⊗_k M` a domain by `isDomain_tensor_of_isFractionRing` (through
`MvPolynomial.algebraTensorAlgEquiv` and `AlgebraicIndependent.aevalEquivField`), and `L` algebraic
over `M`, so `isReduced_tensor_of_isAlgebraic` applies over `M` and `cancelBaseChange` transports
the conclusion back.

`TensorReducedGeneral`

```text
injective_toPi_minimalPrimes             a reduced ring embeds in the product of its minimal quotients
isReduced_tensor_of_isNoetherianRing     hence base change of a Noetherian reduced ring is decided by
                                         its finitely many minimal quotients
isReduced_tensor_field_algebra_of_charZero
isReduced_tensorProduct_of_charZero
    **the tensor product of two reduced algebras over a field of characteristic zero is reduced**
isReduced_tensorSquare_of_charZero
isReduced_subalgebra_tensorSquare_of_charZero
    **hence every subalgebra of `R ⊗_K R` is reduced** — in particular the constants algebra `E`
```

Mathlib's `IsReduced.tensorProduct_of_flat_of_forall_fg` reduces the general case to finitely
generated, hence Noetherian, subalgebras; `minimalPrimes.finite_of_isNoetherianRing` and
`Algebra.TensorProduct.piRight` do the rest.

**Consequence for the card.**  `isomonodromy_of_no_riccati_of_linearRelation`'s `[IsReduced E]`,
`PointsSeparate` and `PointsSeparateModule` are now all dischargeable from
`isReduced_of_isSigmaSimple` alone: the Picard–Vessiot ring is `σ`-simple, hence reduced, hence its
tensor square is reduced, hence so is `E`.  Cartier's theorem is **not needed anywhere**.

Item (b)'s residue is therefore exactly two statements: the improper branch of
`cassidy_group_dichotomy`, and the instantiation of the general lemmas at the concrete
Picard–Vessiot data of the order recurrence.

## Lean progress — the improper branch: the characteristic-zero Cartier mechanism (2026-08-29)

The three needs recorded above for item (b) have been replaced by a single elementary mechanism, and
two thirds of it are now Lean-closed.  **Kolchin smoothness (Cartier) is not needed as an input**:
in characteristic zero the whole content is that the vanishing ideal of a set with everywhere-full
tangent space is closed under partial derivatives, and differentiation lowers the total degree.

### Why the one-parameter route is dead

The route through the unipotent line `k = {t : 1 + t·e ∈ H}` cannot work, and the obstruction is
structural rather than technical.  `k` is a Kolchin-closed additive submonoid, but its tangent space
at `0` is computed from the *radical* ideal `I(k)`, and knowing the tangent space of `H` at `1`
gives only `T_0(k) ⊆ T_1(H) ∩ C·e`, an upper bound.  Slices do not inherit tangent spaces, and the
pullback of a radical ideal along the line need not be radical — the family `{t² = 0}` is a
Kolchin-closed additive monoid with full tangent space at `0` and is not `C`.  Every variant of the
route (Cassidy's additive classification, dual-number thickening, iterated jets) fails at the same
point.  **The argument must be run on the three-dimensional group itself.**

### `MonoidTangentTranslation` — the Lie algebra at every point

```text
linearisationForm_eq_zero_of_dualMatrix_mem      the ε-part of a dual-number point is the linearisation
dualMatrix_translate_mem_zeroSet                 g + ε(g·Z) is a point whenever g is and Z is tangent at 1
linearisationForm_translate_eq_zero
exists_traceless_mul_eq_of_trace_adjugate_zero   {W : tr(adj(g)·W) = 0} = g·sl₂ when det g = 1
linearisationForm_eq_zero_of_trace_adjugate_zero
    **the linearisation of every defining equation at every point of the monoid annihilates the
    whole tangent space of SL₂ there**
```

Only closure of the zero set under multiplication *over the dual numbers* is used — no inverses, no
bi-dual numbers, no Hopf ideal.

### `FreeJetTangentClosure` — the characteristic-zero engine

```text
totalDegree_pderiv_lt, exists_pderiv_ne_zero, vars_pderiv_subset
NoUniversalJetRelation C     no nonzero linear jet relation holds for every element of C
pderiv_mem_vanishing_of_full_tangent
    **full tangent space at every point ⟹ the vanishing ideal is closed under ∂_v**
eq_zero_of_pderiv_closed, eq_zero_of_vanishing_of_full_tangent
    **hence the vanishing ideal is zero**
```

The linearisation restricted to one indeterminate is a linear jet operator in that coordinate; over
a field admitting no universal jet relation it must vanish coefficientwise, which is exactly
`∂_v Q ∈ I(T)`.  The induction is on total degree: a variable-free polynomial vanishing at one point
of `T` is zero.

### `Sl2BigCellCartier` — the codimension-one obstruction, removed

The tangent space of `SL₂` at `g` is a *hyperplane* in the four matrix coordinates, so the engine
cannot run there — `det X − 1` is a nonzero element of every vanishing ideal with full `sl₂` tangent
space.  The fix is a single multiplication:

```text
linearisationForm_mul                            Leibniz for the linearisation
trace_adjugate_mul_fin_two                       g₁₁W₀₀ − g₀₁W₁₀ − g₁₀W₀₁ + g₀₀W₁₁
bigCellPoints S, bigCellIdeal S
X_mul_mem_of_mem_bigCellIdeal                    X₀₀·Q vanishes on the whole monoid
linearisationForm_eq_zero_of_mem_bigCellIdeal
    **the tangent space of the big cell, in the three coordinates X₀₀, X₀₁, X₁₀, is everything**
bigCellIdeal_eq_zero
    **no nonzero differential polynomial in those three coordinates vanishes on the big cell**
```

The projection of the tangent hyperplane onto `(W₀₀, W₀₁, W₁₀)` is surjective as soon as
`g₀₀ ≠ 0` — solve the hyperplane equation for `W₁₁` — so the three-coordinate tangent space is full
even though the four-coordinate one is not.  `X₀₀·Q` vanishes on the whole zero set (on the big cell
because `Q` does, off it because the factor does), so it lies in the vanishing ideal, and Leibniz
transports its linearisation back to `Q`'s after dividing by `g₀₀ ≠ 0`.

All three modules are unconditional, axiom-clean and wired into `HTGeometry`.

### What item (b) now is

Two steps, both bookkeeping rather than new mathematics:

1. **Eliminate the fourth coordinate.**  For `P` in the vanishing ideal produce `N` and a
   differential polynomial `Q` in `X₀₀, X₀₁, X₁₀` with `Q(g) = g₀₀^N · P(g)` for every `g ∈ SL₂` with
   `g₀₀ ≠ 0`.  The mechanism is `X₁₁^{(k)} = θ_k / X₀₀^{k+1}` with `θ_0 = 1 + X₀₁X₁₀` and
   `θ_{k+1} = X₀₀·δθ_k − (k+1)·X₀₀'·θ_k`, realised as an `MvPolynomial.aeval` into
   `Localization.Away X₀₀` — no differential structure on the localization is needed.
   `bigCellIdeal_eq_zero` then forces `Q = 0`, hence `P` vanishes on the whole big cell of `SL₂`.
2. **Generate.**  Every element of `SL₂` is a product of two elements with nonzero upper-left entry,
   so the monoid property upgrades the big cell to all of `SL₂`.

### The improper branch is CLOSED in Lean (2026-08-29)

The two remaining bookkeeping steps are done, and the classification statement they were needed for
is now a theorem in the tree.

`Sl2BigCellElimination`

```text
bigCellIndex, bigCellCoord, bigCellTriple      the three big-cell coordinates
elimA, elimTheta
    θ₀ = 1 + X₀₁X₁₀,  θ_{k+1} = X₀₀·δθ_k − (k+1)·X₀₀′·θ_k
evalOver_elimTheta
    **θ_k(g) = g₀₀^{k+1} · δ^k(g₁₁) at every point of `SL₂`**
elimPoint, elimHom
exists_bigCell_elimination
    **for every `P` there are `N` and a differential polynomial `Q` in `X₀₀, X₀₁, X₁₀` with
    `Q(g) = g₀₀^N · P(g)` at every `g ∈ SL₂` with `g₀₀ ≠ 0`**
```

The substitution `X₁₁^{(k)} ↦ θ_k / X₀₀^{k+1}` is performed on the *jet variables*, so it is an
ordinary `MvPolynomial.eval₂Hom` into `Localization.Away X₀₀` — **no differential structure on the
localization is needed**, which is what makes the step short.  `IsLocalization.surj` clears the
denominator and `IsLocalization.Away.lift` evaluates, the identification of the lifted substitution
with evaluation at `g` being one `MvPolynomial.ringHom_ext`.

`Sl2CassidyImproperBranch`

```text
lowerUnipotent, lowerUnipotent_mul, exists_bigCell_factorisation
    **every element of `SL₂` is a product of two elements with invertible upper-left entry**
mem_of_det_eq_one_of_ne_zero                  the big cell lies in the monoid
sl2_of_full_tangent
    **a differential algebraic monoid in `SL₂` whose tangent space at the identity is all of `sl₂`
    is the whole of `SL₂`**
```

The factorisation is `g = (g·u(t))·u(−t)` with `u(t)` lower unipotent and `t = (1 − g₀₀)/g₀₁` when
`g₀₁ ≠ 0` (and `g` already in the big cell otherwise, since `g₀₀g₁₁ = 1` there).

Hypotheses of `sl2_of_full_tangent`, all of them properties of the object rather than added
assumptions: the zero set contains `1`, is closed under multiplication over `C` and over the dual
numbers, lies in `SL₂`, is defined by its full vanishing ideal, its tangent space at `1` is all of
`sl₂`, and the base field admits no universal linear jet relation (`NoUniversalJetRelation`, which
fails only when the field is finite-dimensional over its constants).

Unconditional, axiom-clean, wired into `HTGeometry`.

### What item (b) now is

One statement, and it is no longer a classification:

> the parameterized Galois group of the order recurrence, as the zero set of its vanishing ideal, is
> a monoid over every differential `C`-algebra (it is a group scheme), and `H = SL₂` contradicts
> differential algebraicity of `K_ν(s)`.

The first half is the Hopf-ideal property of `E`, which the corpus's `TorsorDecomposition` and
`adjoin_tensor_comparison_eq_top` supply; the second is the differential transcendence degree of the
Picard–Vessiot extension of `SL₂`.

### `UniversalJetRelationRank` — the base-field hypothesis, discharged (2026-08-29)

```text
InfiniteConstantRank C
    for every `n`, `C` carries `n + 1` elements with no nontrivial relation over the constants
noUniversalJetRelation_of_infiniteConstantRank
    **hence `NoUniversalJetRelation C`**
```

A universal jet relation says the whole field solves one monic scalar equation of the order of the
relation's top nonzero coefficient, and the corpus's `card_le_of_no_constantRelation_scalar` caps
the independent solutions of such an equation by that order.  So the only hypothesis of
`sl2_of_full_tangent` that is not a property of the zero set itself is now a statement about the
base field that every differentially closed field satisfies.

## Lean progress — the full-group branch: a scalar orbit kills every differential relation (2026-08-29)

With the improper branch closed, item (b)'s residue is *"a full parameterized Galois group is
incompatible with a differentially algebraic solution"*.  Its mechanism is now Lean-proved, and it
needs neither the torsor decomposition nor differential dimension theory: a full group contains
`diag(c, c⁻¹)` for every `c ≠ 0`, so the relation satisfied by the solution `y` is satisfied by
**every scalar multiple** `c·y`, and a differential polynomial cannot vanish on a whole scalar orbit
unless it is zero.

### `DifferentialPolynomialNonRoot` — a mathlib-gap lemma

```text
differentialPolynomialEvalOver_generic   evaluating at the generic point returns the polynomial
scalarDiffFieldExt C                     `C⟨y⟩` as a differential field extension of `C`
exists_evalOver_ne_zero
    **a nonzero differential polynomial over a differentially closed field has a non-root**
```

Differential closedness is stated for *systems of equations*, and an inequation is an equation in
one more indeterminate: `F(x) ≠ 0` is `t·F(x) = 1`.  That auxiliary system has a solution over the
free differential field `C⟨y⟩` — at the generic point `F` evaluates to itself, which is nonzero —
so `IsDifferentiallyClosed.exists_point_finite` descends it to `C`.

### `DifferentialPolynomialSubfieldDescent`

```text
differentialJet_algebraMap        jets of a point of the subfield stay in the subfield
linearPush φ, coeff_linearPush, evalOver_linearPush
eq_zero_of_evalOver_subfield_eq_zero
    **a differential polynomial over `L` vanishing at every point of a differentially closed
    subfield `C` is zero**
```

Evaluation at a point of `C` is `C`-linear in the coefficients, so a `C`-linear functional
`φ : L → C` pushes a polynomial over `L` to one over `C` with the same values up to `φ`; each of
those is zero by the non-root lemma, and `Module.Projective.exists_dual_ne_zero` separates the
coefficients.

### `DifferentialPolynomialScaling`

```text
scaleSubst y F                    the substitution `u ↦ y·u`
evalOver_scaleSubst               its values are the values of `F` at scaled points
scaleSubst_scaleSubst             **`scaleSubst y⁻¹ ∘ scaleSubst y = id`** — substitution is
                                  functorial and the generic point is the identity
eq_zero_of_evalOver_scaled_subfield_eq_zero
    **a differential polynomial vanishing at every nonzero scaled point `y·c`, `c ∈ C`, is zero**
```

The excluded origin costs one multiplication by the indeterminate.  Invertibility of the scaling is
what turns "vanishes on the orbit" into "is zero": no leading-coefficient extraction and no
triangular-matrix inversion is needed, because `differentialPolynomialEvalOver` composes.

**Consequence.**  If the parameterized Galois group of the order recurrence is all of `SL₂` over the
(differentially closed) constants, then no nonzero differential polynomial annihilates a solution
entry — the solution is differentially transcendental, which is the card's conclusion in that
branch.  What remains of item (b) is the *transport*: from `F(y) = 0` and a Galois element `g`,
derive `F((Y·g)₀₀) = 0`, i.e. that the Galois action fixes the coefficient field of the relation.

### `MatrixTranslationZeroSet` — the monoid hypothesis over the constants, discharged (2026-08-29)

```text
matrixRightTranslate b P, evalOver_matrixRightTranslate
matrixLeftTranslate a P,  evalOver_matrixLeftTranslate
matrixVanishingIdeal H, subset_matrixZeroSet_vanishingIdeal
mul_mem_matrixZeroSet_vanishingIdeal
    **the zero set of the vanishing ideal of a multiplicative set of matrices is multiplicative**
```

Right and left translation by a fixed matrix are `C`-linear in the matrix entries, hence are
evaluations of the differential polynomial ring in itself; the classical two-step argument then runs
with no topology at all: right translation by a point of `H` keeps the vanishing ideal, so a point
of the zero set kills it there; the resulting left translate again lies in the vanishing ideal, and
the second point of the zero set finishes.

This discharges `sl2_of_full_tangent`'s `hmulC` for the vanishing ideal of the Galois monoid, and
`hrad` is definitional for a vanishing ideal.  The three hypotheses that remain to be produced from
the parameterized Galois data are `hone` (immediate), `hdet` (`H ⊆ SL₂`), and `hmul` **over the dual
numbers** — the group-functor property, which is where the Hopf structure of `E` enters.

### The transport is already in the tree

`DifferenceGaloisIrreducibility.galoisAutAt` is the Galois automorphism attached to a differential
point of `E`, built from `TorsorDecomposition.tensorDecompositionEquiv`, and
`galoisAutAt_fundamental` is exactly `σ_χ(Y) = Y · galoisMatrixAt χ`.  So the branch-(a) chain is

```text
F(y) = 0,  F ≠ 0 over K
  ⟹ F(σ_χ y) = 0 for every differential point χ         (σ_χ fixes K and commutes with δ)
  ⟹ F(c·y) = 0 whenever diag(c, c⁻¹) is a Galois matrix
  ⟹ F = 0                                                (eq_zero_of_evalOver_scaled_subfield_eq_zero)
```

and the only step not yet Lean-closed is that a *full* group supplies those diagonal matrices as
actual points `χ`, rather than merely as points of the Kolchin closure — which is again the
group-functor property of `E`.

### The Hopf/group-functor gate is REMOVED (2026-08-29)

The dual-number monoid hypothesis of `sl2_of_full_tangent` was the last structural input the improper
branch needed, and it is now unnecessary.  Only one consequence of it was ever used — that a point
of the zero set carries a tangent direction at the identity to a first-order deformation of itself —
and that consequence follows from *left-translation stability of the defining ideal*, which for a
vanishing ideal is the elementary two-step argument.

`MatrixTranslationPolynomial` (translation over an arbitrary differential base algebra)

```text
matrixLeftTranslate a P, matrixRightTranslate b P
evalOver_matrixLeftTranslate, evalOver_matrixRightTranslate
    **evaluating the translate at a matrix over any differential `C`-algebra is evaluating the
    original at the translated matrix**
evalOver_matrixLeftTranslate_self, evalOver_matrixRightTranslate_self
```

`MatrixTranslationZeroSet`

```text
matrixVanishingIdeal H, subset_matrixZeroSet_vanishingIdeal
leftTranslate_mem_matrixVanishingIdeal
    **left translation by a point of the zero set preserves the vanishing ideal of a monoid**
mul_mem_matrixZeroSet_vanishingIdeal
```

`MonoidTangentTranslation`

```text
TangentTranslates S hone                     the only property the derivation-closure argument uses
tangentTranslates_of_mul                     …from closure over the dual numbers
dualNumberDifferentialAlgebra                the dual numbers as a differential `C`-algebra
tangentTranslates_of_leftTranslate           …**from left-translation stability alone**
```

`Sl2CassidyImproperBranch`

```text
sl2_of_full_tangent_vanishingIdeal
    **a multiplicative set of determinant-one matrices containing the identity, whose Kolchin
    closure has all of `sl₂` as tangent space at the identity, has the whole of `SL₂` in its
    closure**
```

Its hypotheses are, in full: the base field admits no universal linear jet relation; `H` is closed
under multiplication and contains `1`; the closure lies in `SL₂`; the tangent space at `1` is all of
`sl₂`.  **No dual numbers, no radicality, no Hopf or group-scheme structure appears anywhere.**

### What item (b) now is

The galoisMonoid is a monoid containing `1` by construction, and lies in `SL₂` because `det Z = 1`
in the torsor.  So `sl2_of_full_tangent_vanishingIdeal` applies to it verbatim, and the improper
branch of the classification is closed for the actual object.  Item (b)'s residue is the endgame
bookkeeping: instantiate `cassidy_group_dichotomy` and `isomonodromy_of_no_riccati_of_linearRelation`
at the Picard–Vessiot data of the order recurrence, and in the full-tangent branch feed
`galoisAutAt_fundamental` into `eq_zero_of_evalOver_scaled_subfield_eq_zero`.

## Lean progress — the group law of the difference Galois group (2026-08-29)

Bracket closure (`hbr` of `cassidy_group_dichotomy`) is the one hypothesis that the left-translation
trick above cannot supply: it is genuinely second order, and `bracket_mem_zeroSet_of_one` asks for
closure of the zero set under multiplication over the *bi-dual* numbers.  That is the group-functor
property, and its source is a single algebraic identity, now Lean-proved.

`TripleTensorCocycle`

```text
tensor12, tensor23, tensor13                the three inclusions R ⊗ R → R ⊗ R ⊗ R
tripleFundamental₁ / ₂ / ₃                  the three copies of the fundamental matrix
map_leftFundamental_tensor12 …              six definitional identifications
torsor_cocycle
    **Z₁₃ = Z₁₂ · Z₂₃ inside the triple tensor product**
```

The proof is three instances of the torsor relation pushed forward along the three inclusions —
`Y₁Z₁₂ = Y₂`, `Y₂Z₂₃ = Y₃`, `Y₁Z₁₃ = Y₃` — and cancellation of the invertible `Y₁`.  Unconditional,
axiom-clean, umbrella-wired.

### What the cocycle still needs to become the group law

`hbr` follows once the two images `ι₁₂(E)` and `ι₂₃(E)` are linearly disjoint over `C` inside the
triple tensor product, since then `P(Z₁₃) = 0` descends to `P(Z ⊙ Z) = 0` in `E ⊗_C E`, which is
exactly the statement that the defining ideal is a **bi-ideal** — and a bi-ideal makes the zero set
a monoid over *every* base algebra, the dual and bi-dual numbers included.

That disjointness is the torsor decomposition applied twice:

```text
    R ⊗_K R ⊗_K R  ≅  (R ⊗_C E) ⊗_K R  ≅  R ⊗_C E ⊗_C E ,
```

each step being `TorsorDecomposition.tensorDecompositionEquiv`, and `E ⊗_C E ↪ R ⊗_C E ⊗_C E`
because `C` is a field.  Both `hgen` and `hindep` are already hypotheses of the endgame theorem, so
no new input is required — only the composition.

## Lean progress — bracket closure without the bi-dual numbers (2026-08-29)

The route through the triple-tensor cocycle is **not needed**.  Bracket closure — the last structural
hypothesis of `cassidy_group_dichotomy` besides Zariski density — follows from first-order data
alone, through the left-invariant derivations of the jet ring.

`LeftInvariantJetDerivation`

```text
rightMulEntry Z q                       the entries of 𝐗·Z as differential polynomials
leftInvariantDeriv Z                    the derivation 𝐗_{ij}^{(k)} ↦ δ^k((𝐗·Z)_{ij})
evalOver_rightMulEntry, evalOver_differentialJet, leftInvariantDeriv_C, deriv_mul_poly
evalOver_leftInvariantDeriv
    **its value at `x` is the ε-part of the value of the polynomial at `x + ε(x·Z)`** — i.e. the
    linearisation at `x` in the translated direction
leftInvariantDeriv_deriv                E_W ∘ δ = δ ∘ E_W
differentialJet_sub
leftInvariantDeriv_commutator
    **⁅E_Y, E_Z⁆ = E_{Y·Z − Z·Y}**
leftInvariantDeriv_mem_of_tangentTranslates
    **E_Z preserves the defining ideal** when the tangent directions translate and the ideal is the
    full vanishing ideal of its zero set
bracket_mem_matrixTangentM
    **Y·Z − Z·Y is tangent whenever Y and Z are**
```

The mechanism in one line: `E_Z` kills the ideal because `Λ_{P,x}(x·Z) = 0` at every point — which
is exactly `TangentTranslates` — so `E_Y(E_Z P)` and `E_Z(E_Y P)` are again killed at the identity,
and their difference is `E_{[Y,Z]}P`, whose value at `1` is `Λ_{P,1}([Y,Z])`.

**No dual-number multiplicativity, no bi-dual numbers, no Hopf ideal, no torsor.**  All of it rests
on `TangentTranslates`, which for the vanishing ideal of a monoid is the two-step left-translation
argument.

### What item (b) now is

`cassidy_group_dichotomy` has four structural hypotheses.  Three are now theorems for the vanishing
ideal of a monoid inside `SL₂`:

| hypothesis | source |
|---|---|
| `hone` | `subset_matrixZeroSet_vanishingIdeal` |
| `htr` | `trace_eq_zero_of_mem_zeroSet`, from `detPoly ∈ S` |
| `hbr` | **`bracket_mem_matrixTangentM`** |
| `hdense` | `sl2_of_dense`, whose residue is `L ≠ 0` — Zariski density, an item-(a) fact |

and the improper branch is `sl2_of_full_tangent_vanishingIdeal`.  What is left is the Zariski-density
input and the instantiation at the Picard–Vessiot data of the order recurrence.

### `CassidyMonoidDichotomy` — the dichotomy, assembled (2026-08-29)

```text
detPoly_mem_matrixVanishingIdeal        the determinant equation is in the ideal
trace_eq_zero_of_mem_matrixTangentM     hence tangent directions are traceless
cassidy_monoid_dichotomy
    **for a multiplicative set `H` of determinant-one matrices containing `1`:
     either `SL₂` lies in the Kolchin closure of `H`,
     or one nonzero linear differential operator annihilates every entry of every element of `G`**
```

Unconditional, axiom-clean, umbrella-wired.  Its hypotheses are now exactly:

* `H` multiplicative, `1 ∈ H`, `det = 1` on `H` and on its closure;
* the base field admits no universal linear jet relation;
* **Zariski density** `hdense`, and the three `G`-hypotheses of the group step
  (`det g` a constant, `det g ≠ 0`, and adjoint stability of the tangent space).

`htr` and `hbr` are gone — they are theorems now.  What remains for item (b) is `hdense` together
with `L ≠ 0` (both supplied by `sl2_of_dense` from item (a)'s irreducibility and non-imprimitivity)
and the instantiation at the Picard–Vessiot data of the order recurrence.

### `GaloisMonoidDichotomyEndgame` — the alternative the card consumes (2026-08-29)

```text
isomonodromy_or_sl2_galoisMonoid
    **either the Kolchin closure of the Galois monoid contains all of `SL₂`,
     or the difference equation carries a connection over the base**
```

Unconditional, axiom-clean, umbrella-wired.  It is `cassidy_monoid_dichotomy` fed into
`isomonodromy_of_no_riccati_of_differentiallyClosed`, with the passage from a linear jet relation on
the group entries to the scalar-stabiliser constraint supplied by
`deriv_eq_zero_of_scalarSpan_of_linear` (the relation forces `x′ = 0`, which is the `m = 1`,
`aa = 0` instance of the endgame's hypothesis).

Its inputs are exactly the Picard–Vessiot package the corpus already names — `E`, its basis, `hgen`,
`hindep`, `σ`-compatibility, `σ`-simplicity, the absence of a base Riccati solution, the fundamental
matrix and the comparison matrix — together with

* `det = 1` on the Galois monoid and on its Kolchin closure;
* Zariski density `hdense`;
* the three group-step hypotheses `hGdetK`, `hGdet0`, `hGinv`.

**Both branches are card conclusions.**  The second is the isomonodromy statement the card already
refutes for the order recurrence.  The first says the Galois monoid is Kolchin-dense in `SL₂`, and
then `eq_zero_of_evalOver_scaled_subfield_eq_zero` (this session) forbids any nonzero differential
relation on a solution entry, because the group contains `diag(c, c⁻¹)` for every `c ≠ 0` and
`galoisAutAt_fundamental` transports the relation along it.

Item (b) is therefore reduced to: the Zariski-density input `hdense` (an item-(a) consequence, via
`sl2_of_dense`, whose own residue is `L ≠ 0`), the three group-step hypotheses, and the construction
of the Picard–Vessiot package for the concrete order recurrence.

### The determinant normalisation, resolved (2026-08-29)

The order recurrence's companion matrix has `det A = −a₀ = −1`, so the Casoratian `w = det Y`
satisfies `σw = −w`.  There is no `c ∈ ℂ(ν)` with `σc = −c` — such a `c` is `σ²`-invariant, hence a
constant, hence `c = −c = 0` — so `w ∉ K` and the comparison matrix's determinant is **not** `1`.
It is, however, a square root of one:

```text
    σ(w²) = w² ⟹ w² ∈ C (no new constants) ⟹ (det Z)² = (1 ⊗ w²)(w² ⊗ 1)⁻¹ = 1 ,
```

the last step because `w² ∈ C ⊆ K` is `K`-balanced.  So the Galois monoid lies in
`{g : (det g)² = 1}`, not in `SL₂`, and the corpus's Cassidy chain — which reads tracelessness off
`detPoly ∈ S` — does not apply to it verbatim.

**The fix costs nothing**, because Cassidy's classification takes the Lie algebra and the group as
*independent* inputs: run the tangent-space half on the determinant-one part and the group half on
the whole monoid.

```text
mul_mem_detOne                              the determinant-one part of a matrix monoid is a monoid
isomonodromy_or_sl2_galoisMonoid_detOne
    **either `SL₂` lies in the Kolchin closure of the determinant-one part of the Galois monoid,
     or the equation carries a connection over the base**
```

Unconditional, axiom-clean, umbrella-wired.  `htr` is again free — `detPoly` lies in the vanishing
ideal of the determinant-one part by construction — and `hbr`, `hone` and the improper branch are
unchanged.  The Zariski-density input is now density of the determinant-one part in `SL₂`, which is
the form item (a) naturally produces.

## Lean progress — the Picard–Vessiot package: `E`, `hEδ` and `hgen` (2026-08-29)

Two of the three remaining inputs of the endgame are now *constructed* rather than assumed.

`ComparisonJetAlgebra`

```text
tensorJet k                             the iterated derivation of the tensor square
comparisonJetGens Z                     all jets of the entries of the comparison matrix
comparisonJetCore Z, comparisonJetAlgebra Z w
comparisonJetCore_deriv_stable          the jet algebra is derivation-stable
det_mem_comparisonJetCore               and contains `det Z`
comparisonJetAlgebra_deriv_stable
    **`E := C⟨Z_ij⟩[w]` is derivation-stable** — the inverse determinant contributes
    `δw = −δ(det Z)·w²`, and `δ(det Z)` is already in the core
adjoin_comparisonJetAlgebra_eq_top
    **`hgen`: the tensor square is generated over `C` by the left copy together with `E`**
```

Unconditional, axiom-clean, umbrella-wired.  `E` is the `C`-subalgebra generated by every jet of
every entry of the comparison matrix together with the inverse of its determinant; its entries and
their derivatives are `σ`-constants by
`ParameterizedTensorTorsor.exists_parameterized_tensor_comparison_matrix`, so `E` is a subalgebra of
constants, and `hZE` is `mem_comparisonJetAlgebra_entry`.

### The residue of item (b), current

| endgame input | status |
|---|---|
| `E`, `hZE`, `hEδ` | **constructed** (`ComparisonJetAlgebra`) |
| `hgen` | **constructed** |
| `IsReduced E` | `isReduced_subalgebra_tensorSquare_of_charZero` |
| `Z`, `hZ`, `IsUnit Z.det` | `exists_parameterized_tensor_comparison_matrix` |
| `hric` | `BesselOrderRiccati` |
| `Algebra.FiniteType C E` | **open** — finitely many jets suffice exactly when the parameterized group is finite-dimensional, which is the case under the differential-algebraicity assumption |
| basis of `E` and `hindep` | `Module.Basis.ofVectorSpace` plus `basisIndependentOver_of_constants` |
| `hdense`, `hGdetK`, `hGdet0`, `hGinv` | item (a) inputs |

### `TensorBasisIndependence` — `hindep`, constructed (2026-08-29)

```text
linearIndependent_of_basisIndependentOver
    `BasisIndependentOver` is linear independence (`Algebra.smul_def`)
linearIndependent_constants_basis
    **a `C`-basis of a subalgebra of `σ`-constants is linearly independent over `R`**
```

Unconditional, axiom-clean, umbrella-wired.  The corpus's
`basisIndependentOver_of_constants` forces the coefficients of a vanishing combination of constants
to be `σ`-constants; the no-new-constants property of the Picard–Vessiot ring then puts them in `C`,
where the basis is independent by construction.  Its hypotheses are `σ`-simplicity of `R`, the
constancy of `E`, and no new constants — all standing properties of the Picard–Vessiot setting.

### The residue of item (b), current

| endgame input | status |
|---|---|
| `E`, `hZE`, `hEδ`, `hgen` | **constructed** (`ComparisonJetAlgebra`) |
| basis of `E` | `Module.Basis.ofVectorSpace` |
| `hindep` | **constructed** (`TensorBasisIndependence`) |
| `IsReduced E` | `isReduced_subalgebra_tensorSquare_of_charZero` |
| `Z`, `hZ`, `IsUnit Z.det` | `exists_parameterized_tensor_comparison_matrix` |
| `hric` | `BesselOrderRiccati` |
| `Algebra.FiniteType C E` | **open** — equivalent to finitely many jets of `Z` generating, i.e. to the parameterized group being finite dimensional; this is a *consequence* of the differential-algebraicity assumption the card argues from, not an unconditional fact |
| `hdense`, `hGdetK`, `hGdet0`, `hGinv` | item (a) inputs |

## Consolidated status of item (b) after this session (2026-08-29)

The card's header still reads "the exact Dreyfus higher-order classification theorem remains
unformalized".  That is now a substantial understatement of what the tree holds.  The classification
itself — both branches — is proved; what remains is card-specific input, not general theory.

**Proved this session, all unconditional and `#print axioms`-clean:**

| module | content |
|---|---|
| `MonoidTangentTranslation` | the linearisation at every point kills `g·sl₂`; `TangentTranslates` and its two producers |
| `FreeJetTangentClosure` | full tangent space ⟹ vanishing ideal closed under `∂_v` ⟹ zero |
| `Sl2BigCellCartier` | the codimension-one obstruction removed in three coordinates |
| `Sl2BigCellElimination` | `X₁₁^{(k)} = θ_k/X₀₀^{k+1}` as a plain `eval₂Hom` into `Localization.Away X₀₀` |
| `Sl2CassidyImproperBranch` | **`sl2_of_full_tangent`** and its hypothesis-lean form `sl2_of_full_tangent_vanishingIdeal` |
| `UniversalJetRelationRank` | the base-field hypothesis from infinite rank over the constants |
| `MatrixTranslationPolynomial`, `MatrixTranslationZeroSet` | left/right translation; the zero set of a monoid's vanishing ideal is a monoid |
| `LeftInvariantJetDerivation` | `⁅E_Y, E_Z⁆ = E_{Y·Z − Z·Y}` ⟹ **bracket closure with no bi-dual numbers** |
| `CassidyMonoidDichotomy` | `htr`, `hbr`, `hone` discharged; the dichotomy for a matrix monoid |
| `GaloisMonoidDichotomyEndgame` | **`isomonodromy_or_sl2_galoisMonoid`** and its determinant-one form |
| `TripleTensorCocycle` | `Z₁₃ = Z₁₂·Z₂₃` — the group law (kept; no longer on the critical path) |
| `DifferentialPolynomialNonRoot` | **a nonzero differential polynomial over a differentially closed field has a non-root** (mathlib gap) |
| `DifferentialPolynomialSubfieldDescent`, `DifferentialPolynomialScaling` | vanishing on a scalar orbit forces zero |
| `ComparisonJetAlgebra` | `E`, `hZE`, `hEδ`, `hgen` **constructed** |
| `TensorBasisIndependence` | `hindep` **constructed** |

**The residue, exactly.**

1. `Algebra.FiniteType C E` — `E` is generated by all jets of `Z`, so this says finitely many jets
   suffice, i.e. the parameterized group is finite dimensional.  It is a *consequence* of the
   differential-algebraicity assumption the card argues from, so it enters as a DA-side input,
   not as an unconditional fact.
2. `hdense` for the determinant-one part — Zariski density, an item-(a) consequence via
   `sl2_of_dense`, whose own residue is `L ≠ 0`.
3. `hGdetK`, `hGdet0`, `hGinv` — the three group-step hypotheses.

Nothing in the residue is general differential Galois theory any more; all three are properties of
the specific Galois group of the order recurrence.

## `Algebra.FiniteType C E` is CLOSED (2026-08-29)

The first item of the residue recorded above is discharged, not by proving finite type — it is not
provable, and it was the wrong hypothesis — but by removing the need for it.

`E = comparisonJetAlgebra Z w` is generated by all `∂`-jets of five elements: the four entries of
the comparison matrix and the inverse determinant.  That is *differential* finite generation, and it
is the hypothesis Kolchin's Nullstellensatz actually needs.  The corpus now owns that theorem, and
with it the whole engine underneath:

* **`RittRaudenbushFinitelyMany.radDiffFG_differentialPolynomial_fin`** — the Ritt–Raudenbush basis
  theorem in finitely many differential indeterminates over a differential field of characteristic
  zero.  A mathlib gap; the corpus previously had only the one-indeterminate case over a field.
* **`KolchinNullstellensatzDiffFG.exists_differentialAlgHom_ne_zero_of_diffFG`** — Kolchin's
  Nullstellensatz for a differentially finitely generated differentially reduced algebra over a
  differentially closed field.
* **`TensorDifferentialPointsDiffFG.eq_zero_of_forall_mem_tensorDifferentialPoints_of_jetAdjoin`** —
  the separation property of the endgame, from a jet presentation.
* **`GaloisMonoidDichotomyDiffFG.isomonodromy_or_sl2_galoisMonoid_jetAdjoin`** and its
  determinant-one form — the endgame dichotomy with `[Algebra.FiniteType C E]` replaced by the jet
  presentation.
* **`ComparisonJetAlgebraDiffFG.adjoin_comparisonJetGeneratorsTwo`** — the jet presentation itself,
  proved from `Z.det * w = 1`.

The programme, its route and the two places where the mathematics came out stronger than planned are
recorded in `docs/drafts/pipeline/1-in-progress/ritt-raudenbush-several-variables.md`.

### Residue of item (b), updated

| input | status |
|---|---|
| Cassidy's dichotomy, both branches | **closed** |
| bracket closure, tracelessness, improper branch, jet elimination | **closed** |
| `E`, `hZE`, `hEδ`, `hgen`, `hindep` | **constructed** |
| `Algebra.FiniteType C E` | **removed** — replaced by the jet presentation, which is a theorem |
| `hdense` for the determinant-one part | open — an item-(a) consequence via `sl2_of_dense`, whose own residue is `L ≠ 0` |
| `hGdetK`, `hGdet0`, `hGinv` | open — the three group-step hypotheses |

Nothing in the residue is general differential Galois theory.  All three remaining items are
properties of the Galois group of the specific order recurrence.

## Kolchin-closure determinant premise removed (2026-08-29)

`CassidyMonoidDichotomy.det_eq_one_of_mem_matrixZeroSet_vanishingIdeal` proves that every point of
the differential zero set of a determinant-one family still has determinant one: the determinant
polynomial belongs to the family's full vanishing ideal, so its evaluation vanishes at every point
of that zero set.  Consequently the independent `hclosuredet` premise has been removed from
`cassidy_monoid_dichotomy` and from all four ordinary/differentially-finitely-generated Galois
endgames, including `isomonodromy_or_sl2_galoisMonoid_detOne_jetAdjoin`.

Direct checks and targeted builds pass.  The new lemma and every affected capstone audit to only
`[propext, Classical.choice, Quot.sound]`.  Remaining card-specific inputs are now `hdense` and the
three full-Galois-monoid structure facts `hGdetK`, `hGdet0`, `hGinv`; no separate closure determinant
hypothesis remains.

## Root-determinant group hypotheses reduced to the Casoratian (2026-08-29)

`GaloisMonoidRootDeterminant.lean`, unconditional and umbrella-wired, proves:

```text
comparisonMatrix_det_pow_eq_one_of_balanced
    equal m-th powers of the two tensor Casoratians force (det Z)^m = 1
comparisonMatrix_det_sq_eq_one_of_neg_one_system
    det A = -1 plus the no-new-constants theorem force (det Z)^2 = 1
galoisMatrixAt_det_pow_eq_one
galoisMonoid_det_pow_eq_one
    the relation propagates through every specialization and the generated Galois monoid
galoisMonoid_det_ne_zero_of_sq_eq_one
galoisMonoid_det_mem_differentialConstants_of_sq_eq_one
    at order two, `hGdet0` and `hGdetK` are consequences
```

Thus the card's Casoratian calculation is now a Lean theorem: a system of determinant `-1` has a
comparison determinant squaring to one as soon as its Picard--Vessiot no-new-constants property is
inserted, and that single relation discharges both determinant premises throughout the generated
Galois monoid.  Source check, targeted build, and all axiom audits pass with only
`[propext, Classical.choice, Quot.sound]`.

For the concrete order recurrence, remaining group work is now: instantiate the existing
no-new-constants producer on the parameterized Picard--Vessiot carrier, prove inverse/adjoint
stability `hGinv`, and prove `hdense`.  `hGdetK`, `hGdet0`, and the independent closure-determinant
premise no longer remain mathematical inputs.

## Galois monoid inverse and adjoint stability (2026-08-29)

`GaloisDifferentialPointGroup.lean` and `GaloisMonoidGroupStructure.lean`, both unconditional and
umbrella-wired, close the formerly independent `hGinv` group-law obligation:

```text
galoisAutAtK_injective
galoisAutAtK_surjective_of_pvGeneration
    a tensor differential point specializes the torsor to a genuine automorphism
exists_inverse_tensorDifferentialPoint
    the inverse automorphism reconstructs an inverse tensor differential point
galoisMonoid_exists_inverse_mem
    inverses propagate from specialization generators through the generated monoid
conj_mem_matrixTangentM_vanishingIdeal
galoisMonoid_detOne_inverse_adjoint
    conjugation by that inverse preserves the determinant-one Kolchin tangent space
```

Source checks, targeted builds, and axiom audits pass with only
`[propext, Classical.choice, Quot.sound]`.  This does **not** smuggle the Picard--Vessiot structure
in as an unconditional card conclusion: the concrete Bessel instantiation must still construct the
parameterized Picard--Vessiot carrier and discharge its sigma-simplicity, no-new-constants,
comparison-algebra invariance, and generation properties.  Once those structural facts are
instantiated, `hGinv` follows as a theorem rather than an extra premise.

The exact remaining card-specific residue is therefore:

1. construct the concrete parameterized Picard--Vessiot carrier with no new sigma constants and
   prove the comparison jet algebra is fixed by the tensor difference action;
2. prove `hdense` for the determinant-one Galois group of the Bessel order recurrence.

Until both are discharged in Lean, this card remains at Stage 2.

## Comparison-jet structural hypotheses eliminated (2026-08-29)

`ComparisonJetAlgebraFixed.lean` proves that the tensor difference automorphism fixes every tensor
jet of the comparison matrix, the chosen inverse determinant, and therefore every element of
`comparisonJetAlgebra Z w`.  `GaloisComparisonJetGroupStructure.lean` then combines this with
`comparisonJetAlgebra_deriv_stable`, `adjoin_comparisonJetAlgebra_eq_top`, and
`linearIndependent_constants_basis` to derive inverse-adjoint stability directly for the
comparison-jet Galois monoid.

Consequently `hEσ`, `hEδ`, `hgen`, and `hindep` are no longer exposed premises at the Bessel
endgame boundary.  Both modules pass source checks, targeted builds, and axiom audits with only
`[propext, Classical.choice, Quot.sound]`.

The genuine remaining structure is now narrower: construct a parameterized Picard--Vessiot carrier
which is sigma-simple and has no new sigma constants (the existing sigma-delta-simple quotient is
not enough by itself), then prove determinant-one Zariski density for the concrete Bessel order
system.  These hypotheses must be discharged, not carried into the final theorem.

## Sigma-delta simplicity now suffices for point injectivity (2026-08-29)

`GaloisDifferentialPointGroup.lean` now proves
`galoisAutAtK_injective_of_sigmaDeltaSimple`: at a tensor differential point, the specialization
kernel is stable under both the difference automorphism and the derivation.  Hence the existing
sigma-delta-simple parameterized quotient already forces injectivity.  The inverse-point proof was
factored through this exact injectivity property, yielding
`exists_inverse_tensorDifferentialPoint_of_sigmaDeltaSimple` while preserving the sigma-simple API.

Source check, targeted module build, and axiom audits pass with only
`[propext, Classical.choice, Quot.sound]`.  Sigma-simplicity is therefore no longer needed for the
inverse construction itself.  It remains used only by the current tensor constants/basis
independence theorem; replacing that use by the parameterized torsor theorem, together with proving
no new sigma constants, is the precise remaining PPV structural gap.  Concrete determinant-one
Zariski density remains the second gap.  Neither may appear as a premise of the final Bessel theorem.

## Density audit: Burnside does not discharge `hdense` (2026-08-29)

The current Lean route cannot infer Zariski density from irreducibility plus
`no_imprimitive_pair` alone.  Burnside's theorem proves that the matrix-algebra span is all of
`M₂`, but finite primitive subgroups of `SL₂` can also have that span while remaining Zariski
non-dense.  Therefore no unconditional `hdense` theorem may use Burnside as the missing implication.
The exact density proof must additionally exclude the finite primitive branch (or formalize the
relevant algebraic-subgroup classification).  This is part of the concrete Dreyfus/ordinary-PV
classification residue, alongside the parameterized torsor/no-new-constants construction.
