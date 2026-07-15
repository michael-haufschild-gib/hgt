# Nonlinearity--valuation tomography law

- **ID:** `prime-valuation-veronese-master-law`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [MASTER THEOREM] [GENERAL HT LAW] [NOVELTY UNVERIFIED]`
- **Source:** finite-range prime-tail differential geometry, complete pivot relation ideals,
  prime-power valuation block separation, and Prime-Walsh Stone reconstruction
- **Statement:** Every finite recurrent prime-pattern constraint is recovered losslessly from its
  valuation-resolved differential relation system: polynomial nonlinearity of degree `m` becomes
  linear differential dependence in the `p^m` sector, the sector ranks are the Hilbert function,
  and there are no phantom nonlinear or cross-valuation relations.

## Goal

Replace the degree-one tail matroid and the list of separate prime-power constructions by one
geometric invariant.  Polynomial degree on the recurrent prime-pattern constraint is to become
prime-power valuation degree on the Dirichlet carrier.  The resulting valuation-resolved
differential rank spectrum must recover the Hilbert function and homogeneous ideal of the
constraint, while the complete differential relation ideal must contain no relations beyond the
prolonged linearizations of that homogeneous ideal.

The theorem is about finite-range prime-supported hypertranscendental systems in general.  Its
central law is a **nonlinearity--valuation duality**:

```text
polynomial degree on the source constraint
    = prime-power valuation degree on the carrier.
```

This is not a decomposition added to an existing construction.  It says that the valuation axis
is a lossless linearizing coordinate for nonlinear recurrent geometry.  Differential algebra sees
the entire finite constraint, one homogeneous degree at a time, and invents no additional
relations.  Its application to the Riemann zeta function is downstream: Euler plethysm completes
the valuation sectors, and the functional equation must act on that completion rather than on a
finite sector.

## Setup

Let `J` be finite and let

```text
c = (c_j)_(j in J) : Primes -> C^J
```

have finite range.  Adjoin the constant coordinate `c_0=1` and let

```text
R_c = {(1,v) : v is a recurring joint value of c} subset C^(1+J).
```

Thus a joint value belongs to `R_c` exactly when its prime fibre is infinite.  Let

```text
I_c subset C[X_0,(X_j)_(j in J)]
```

be the homogeneous ideal of the finite projective point set `[R_c]`.  For `m>=1`, write

```text
H_c(m) = dim_C Sym^m(C^(1+J)) / (I_c)_m.
```

Because `X_0=1` on `R_c`, this is equivalently the dimension of polynomial functions of degree at
most `m` on the affine recurring set.  It is nondecreasing and eventually equals `card(R_c)`.

For a degree-`m` monomial `X^alpha`, define the valuation-layer carrier

```text
G_(m,alpha,a)(s)
  = sum_p c(p)^alpha p^(-m(s+a)),
```

where `|alpha|=m`, the zeroth coefficient is `c_0(p)=1`, and `a` ranges through a finite shift set
whose real parts are pairwise distinct.

## Master theorem

**[CONJECTURE] Prime-valuation Veronese tomography.**  For every finite nonempty set `M` of
positive valuation degrees and finite nonempty shift sets `A_m` with pairwise distinct real parts:

1. **Layer kernel.**  The tail-coefficient map

   ```text
   Sym^m(C^(1+J)) -> C^Primes / C^(Primes),
   Q |-> [p |-> Q(1,c(p))]
   ```

   has kernel exactly `(I_c)_m`.  Its rank is `H_c(m)`.

2. **Complete differential rank.**  The valuation-resolved analytic palette has

   ```text
   dtrdeg = sum_(m in M) card(A_m) H_c(m)
   ```

   over the finite-prime Dirichlet coefficient field.

3. **Complete relation ideal.**  Choose at each `m` any monomial columns whose restrictions form a
   basis of the degree-`m` coordinate space of `R_c`.  Every remaining shifted carrier and every
   one of its derivative jets is an affine linear combination of the corresponding basis jets,
   with a finite-prime correction.  These prolonged affine relations generate the complete
   differential relation ideal.  There are no additional nonlinear relations and no relations
   mixing distinct valuation degrees.

4. **Reconstruction.**  The labelled relation ideals over all `m` recover every homogeneous piece
   `(I_c)_m`, hence `I_c`, the finite projective recurring pattern set, and its Hilbert function.
   Cofinal application to finite coordinate projections recovers the full compact Stone tail
   constraint.

   Equivalently, define the reduced valuation relation spectrum by discarding finite-prime base
   corrections and retaining the homogeneous coefficient relations in every sector.  Then

   ```text
   Spectrum(c)_m = (I_c)_m,
   Spectrum(c) = Spectrum(d) iff I_c = I_d.
   ```

   Thus two embedded finite-range sources have the same recurrent constraint geometry exactly
   when they have the same labelled reduced valuation relation spectrum.  This does not assert
   equality of their embedded differential fields: the assignment of recurring patterns to
   individual primes may differ even when the constraint set is identical.

5. **Slope and entropy law.**  Put

   ```text
   D_c(N,A) = card(A) sum_(1<=m<=N) H_c(m).
   ```

   Since `R_c` is finite and reduced, `H_c(m)=card(R_c)` for all sufficiently large `m`.  Hence

   ```text
   lim_(N->infinity) D_c(N,A)/N = card(A) card(R_c).
   ```

   For a countable finite-alphabet tail constraint with prefix recurring sets `R_n`, the
   exponential growth of these valuation-rank slopes is exactly the upper/lower prefix entropy;
   under shift invariance it is the topological entropy.  The previous Prime-Walsh entropy law is
   therefore the stabilized large-window shadow of the valuation--Veronese correspondence.

The theorem gives a new refinement of ordinary differential transcendence degree and, more
strongly, a complete nonlinear constraint invariant:

```text
m |-> H_c(m)
```

is the **valuation-resolved differential Hilbert function** of the HT source.  Ordinary tail rank
is only its degree-one value.  The complete relation spectrum, rather than the rank function alone,
is the **valuation tomography** of the source constraint.  The least degree at which
`H_c(m)=card(R_c)` is the **HT interpolation depth**: the first valuation sector that separates
every finite nonlinear observable of the recurrent constraint.

## Euler and Adams form

For a linear probe `ell` on the augmented coefficient space, put

```text
Z_ell(s) = product_p (1 - ell(1,c(p)) p^(-s))^(-1).
```

In a half-plane of absolute convergence,

```text
log Z_ell(s)
  = sum_(m>=1) (1/m) sum_p ell(1,c(p))^m p^(-m s).
```

Pure powers `ell^m` span the degree-`m` symmetric power by polarization.  Consequently the
`m`-th Euler ghost layer of all linear probes realizes exactly the `m`-th Veronese span of `R_c`.
The master theorem therefore identifies the complete finite differential geometry resolved by an
Euler product with the homogeneous coordinate geometry of its recurrent prime pattern.

For the positive unit `ell=X_0`, `Z_ell=zeta` and `H(m)=1` on every valuation degree.  Thus the
prime-power resolution of `log zeta` contains one new differentially independent ghost coordinate
at every positive degree.  This is a statement about the canonical resolved family, not a claim
that `log zeta` is differentially algebraically independent from every finite ghost field.

## Proof architecture

1. A polynomial `Q(1,c(p))` is finitely supported exactly when `Q` vanishes on every recurring
   joint value.  The nonrecurring fibres form a finite set.  This proves the layer kernel and the
   Hilbert-rank identity.
2. Choose a basis of the degree-`m` restriction space.  Its coefficient columns are independent
   modulo finite prime support.
3. Finite range and real-part separation imply that all shifted derivative columns of this basis
   remain tail-independent within the layer.
4. Prime-power valuation block separation supplies joint algebraic independence of the bases from
   distinct layers.  The analytic dilation law identifies support on `p^m` with argument dilation
   `s |-> m s` and gives the exact derivative weight `m^k`.
5. Every nonbasis monomial column differs from its coordinate-space expansion by finite prime
   support.  The same is true at every shifted derivative jet.
6. Affine differential pivot elimination identifies the complete relation ideal with the ideal
   generated by those jet relations.  Differential independence of the combined pivot family
   excludes every additional nonlinear relation.
7. The kernels in all homogeneous degrees assemble to `I_c`; finite projective algebraic geometry
   reconstructs `R_c`.  The established finite-observable inverse-limit law reconstructs the
   compact Stone tail from its finite projections.

## Attacks

1. **Classical-parent attack.**  Veronese embeddings, Hilbert functions, polarization, and the
   primitive/power-sum description of symmetric functions are classical.  They are not the claimed
   novelty.  The candidate contribution is the exact identification of those homogeneous pieces
   with complete differential relation ideals of analytic prime-power Dirichlet germs.
2. **Packaging attack.**  A rank formula alone would only repackage existing block independence.
   The theorem survives this attack only if the full relation ideal is computed and the converse
   reconstruction of `I_c` is proved.
3. **Infinite-range attack.**  Finite range is essential.  Without it, logarithmic clocks may be
   encoded directly in the coefficients, producing derivative relations not determined by a
   finite recurrent pattern geometry.
4. **Shift attack.**  Pairwise distinct real parts are a sufficient separation regime, not a
   claimed necessary condition.  Equal real parts can support oscillatory coincidences tailored to
   the prime set.
5. **Completion attack.**  Finite-stage freeness does not by itself prove that the completed Euler
   logarithm is external to every finite differential field.  Such analytic completion externality
   is a separate open problem and is not included in the theorem.
6. **Scheme attack.**  The recurring set is reduced and finite.  The theorem reconstructs its
   reduced homogeneous ideal; it does not manufacture nilpotent scheme structure absent from the
   coefficient data.
7. **Novelty attack.**  No primary source has yet been found that identifies a recurrent
   prime-pattern Hilbert function with valuation-resolved differential transcendence ranks or
   computes the complete relation ideal in this form.  A specialist literature verdict remains
   required before promotion as new scientific knowledge.

## Positive RH consequence

For the zeta Euler source, every finite valuation window is a direct sum of differentially free
Veronese layers, while the Euler logarithm is the canonical completion over all positive degrees.
Therefore an RH-bearing prime-side law must be a reflection-compatible operation on the completed
valuation module.  It must couple infinitely many valuation degrees to the archimedean functional
equation; no finite differential, translation, or prime-power window can supply that coupling.

Equivalently, the positive target is not another finite carrier layer.  It is an infinite-rank
reflection functional on the completed Veronese module whose restriction to every finite window
is compatible with the blockwise relation ideal.

## Physical research lens

The valuation degree `m` behaves like a winding or occupation-number sector.  The Euler logarithm
is the connected-cycle expansion with weight `1/m`, and `H_c(m)` counts the independent coherent
prime-pattern modes surviving in sector `m`.  Cyclotomic or sign phases lose rank exactly when the
`m`-fold power map identifies them.  This lens motivates questions about coherence, decoherence,
and completion, but it is not part of the mathematical statement.

## Formal status

The layer-kernel core is proved unconditionally in
`HTGeometry/PrimeValuationVeroneseKernel.lean`:

1. `finiteRange_observable_support_finite_iff` identifies eventual zero with vanishing on all
   recurrent values for every observable of a finite-range sequence.
2. `homogeneousTailRelationSubmodule_eq_recurringVanishing` identifies the homogeneous tail
   relation space with the homogeneous recurrent vanishing space.
3. `homogeneousTailQuotientEquivRecurringRange` gives the canonical linear equivalence from the
   homogeneous tail quotient to the recurrent evaluation image.
4. `finrank_homogeneousTailQuotient_eq_recurringRange` proves equality of their dimensions.

The module passes its direct check and targeted cached build.  Its principal theorems use only
`propext`, `Classical.choice`, and `Quot.sound`.

The valuation-resolved differential-basis core is proved unconditionally in
`HTGeometry/PrimeValuationVeroneseDifferentialBasis.lean`:

1. `rotatedLogArithmetic_primePowerColumn` proves the exact valuation weight of logarithmic
   differentiation on a `p^(e+1)` column.
2. `primePowerCoefficientShiftedRotatedJet_tailIndependent_iff` proves that the invertible
   `(e+1)^k` jet weight preserves and reflects the layer tail matroid.
3. `primePowerCoefficientShiftedJets_algebraicIndependent` proves joint algebraic independence
   of arbitrary finite, nonuniform coefficient--shift--jet rectangles across all layers in a
   finite valuation window.
4. `primePowerCoefficientShiftPalettes_differentialIndependent` proves differential independence
   of the complete finite-shift pivot palette across that window.  In particular, the pivot
   family has no hidden nonlinear or cross-valuation differential relations.

The module passes its direct check and targeted cached build.  Its principal theorems use only
`propext`, `Classical.choice`, and `Quot.sound`.

Finite-prime residuals and complete relations are proved unconditionally in
`HTGeometry/PrimeValuationVeroneseRelationIdeal.lean`:

1. `PrimeValuationTailPivotPresentation` permits independent pivot and dependent alphabets in
   every valuation degree; no uniform layer rank is assumed.
2. `exists_primeValuationTailPivotBaseCorrection` proves that every finite prime-tail residual at
   `p^(e+1)` contributes only a base-field correction at every derivative order.
3. `PrimeValuationTailPivotPresentation.complete_relationIdeal` proves that the prolonged affine
   coordinate reductions generate the complete relation ideal across all layers.
4. `PrimeValuationTailPivotPresentation.differentialBasis` identifies the global pivot palette as
   an exact differential transcendence basis of the full palette field.

The geometric capstone is proved unconditionally in
`HTGeometry/PrimeValuationVeroneseMaster.lean`:

1. `finiteRange_observable_tailIndependent_iff` identifies tail independence of arbitrary
   finite-range observables with linear independence of their restrictions to the recurrent set.
2. `RecurrentHomogeneousValuationPresentation.toTailPivotPresentation` converts homogeneous
   coordinate bases and expansions on the recurrent geometry into the prime-valuation pivot data.
3. `RecurrentHomogeneousValuationPresentation.complete_relationIdeal` proves the
   nonlinearity--valuation completeness statement: the homogeneous coordinate reductions are all
   differential relations, with no additional nonlinear or cross-degree relations.
4. `RecurrentHomogeneousValuationPresentation.differentialBasis` gives the exact global
   differential basis statement.

All four modules pass direct checks and targeted cached builds.  Their principal theorems use
only `propext`, `Classical.choice`, and `Quot.sound`.

## Open core

1. Formalize basis existence from the full degree-`m` monomial spanning family, polarization, and
   equality of the reduced valuation relation spectrum with the full homogeneous ideal.
2. Transfer the complete formal-carrier relation theorem to actual analytic Dirichlet germs and
   prove basis independence of the resulting analytic presentation.
3. Formalize Hilbert-function stabilization, interpolation depth, the slope law, and the cofinal
   Stone reconstruction/entropy consequence.
4. Audit the exact result against differential algebra of arithmetic functions, generalized Euler
   products, big-Witt/symmetric-function theory, and algebraic independence in the Selberg class.

## Gates

- [x] 0 -> 1 in-progress: well-posed statement, source-pure proof architecture, falsifiers, and
  novelty boundary stated
- [ ] 1 -> 2 fully-proven: complete paper proof of every clause, including the analytic relation
  ideal and reconstruction
- [ ] 2 -> 3 formalized: unconditional formal theorem surface with targeted cached verification
- [ ] 3 -> 4 publication-ready: standalone paper centered on the valuation--Veronese
  correspondence and differential Hilbert function
