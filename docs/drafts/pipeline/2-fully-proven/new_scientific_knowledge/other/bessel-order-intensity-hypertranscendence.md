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
