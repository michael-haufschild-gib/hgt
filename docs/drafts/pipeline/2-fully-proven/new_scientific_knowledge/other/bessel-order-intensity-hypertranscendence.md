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
  axioms.
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
