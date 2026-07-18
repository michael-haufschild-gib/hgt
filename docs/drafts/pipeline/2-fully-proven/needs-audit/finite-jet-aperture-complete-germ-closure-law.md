# Finite jets retain maximal HT; one complete germ closes the boundary modulus

- **ID:** `finite-jet-aperture-complete-germ-closure-law`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM / ANALYTIC SELECTION THRESHOLD LAW
- **Lane:** general hypertranscendence; indeterminate moment carriers; analytic constraints
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Parents:** `nevanlinna-boundary-bauer-retract-maximal-ht.md`,
  `moment-polynomial-blind-resolvent-complete-boundary-splitting.md`
- **Statement:** In the canonical Nevanlinna boundary simplex of any indeterminate Hamburger
  moment problem, fixing any finite packet of finite-centre Cauchy jets leaves an
  infinite-dimensional positive level chart. Within that exact finite-jet level, with spectral
  type fixed, maximal full-complex translation hypertranscendence is residual. By contrast, the
  complete Taylor germ at one regular nonreal point determines the entire boundary probability
  law. Rigid analytic selection therefore has a sharp finite-jet / complete-germ threshold.

## Goal

The preceding geometry distinguishes moment data at infinity from resolvent data at finite centre.
The present theorem determines how much finite-centre data is needed. It rules out no route by
negation; it supplies the positive necessity law:

> **A rigid selector on an indeterminate HT carrier must contain infinitely coherent analytic germ
> data or an equally strong global constraint. Every finite local jet retains a positive maximal-HT
> aperture.**

The theorem concerns hypertranscendental functions in general. The RH consequence is a later
specialization.

## Setup

Let `T=RP^1(R)`, let `mu_tau` be the `N`-extremal family of a fixed indeterminate normalized
Hamburger sequence, and let

```text
m_tau(z)=m_infinity(z)-1/[C(z)^2(tau-q(z))].               (1)
```

Fix an infinite-support boundary probability `eta_0`, a positive radius `0<delta<1`, distinct
nodes `z_1,...,z_J in C minus R`, and finite jet depths `d_j>=1`. Write

```text
F_(j,r)(tau)=partial_z^r m_tau(z_j),
0<=r<d_j.                                                  (2)
```

The finite-jet level chart about `eta_0` is

```text
X_(eta_0,J,delta)={w in L-infinity(eta_0;R):
  ||w-1||_infinity<delta,
  integral_T w d eta_0=1,
  integral_T w F_(j,r)d eta_0
    =integral_T F_(j,r)d eta_0 for all (j,r)}.             (3)
```

Every `w` in `(3)` is strictly positive. Hence `eta_w=w eta_0` is equivalent to `eta_0`, and its
extremal barycenter `Beta(eta_w)` has the same complete Hamburger moments and the same transported
spectral type as `Beta(eta_0)`.

## Every finite jet level has infinite positive aperture `[PROVED HERE]`

The real tangent space of `(3)` is

```text
E_J={v in L-infinity(eta_0;R):
  integral_T v d eta_0=0,
  integral_T v F_(j,r)d eta_0=0 for all (j,r)}.            (4)
```

Real and imaginary parts turn `(4)` into finitely many real continuous linear constraints on the
infinite-dimensional Banach space `L-infinity(eta_0;R)`. Because `eta_0` has infinite support,
that Banach space is infinite-dimensional. Thus `E_J` has finite codimension and is
infinite-dimensional.

For every nonzero `v in E_J`, sufficiently small real `epsilon` gives two distinct points

```text
w_+=1+epsilon v,
w_-=1-epsilon v                                            (5)
```

in `(3)`. More generally, every finite-dimensional subspace of `E_J` has a small positive ball in
the chart. Hence a finite Cauchy jet does not merely fail to select uniquely: it leaves
arbitrarily large finite-dimensional positive apertures inside one exact moment and spectral-type
class.

## Jet controllability after the finite jet is frozen `[PROVED HERE]`

Fix a second finite packet of nonreal evaluation nodes `zeta_k` and derivative depths `e_k` such
that the parameter poles

```text
q(zeta_k), conjugate(q(zeta_k))                            (6)
```

are pairwise distinct and disjoint from all fixed poles

```text
q(z_j), conjugate(q(z_j)).                                 (7)
```

Such packets exist in arbitrary finite size because `q` is nonconstant and holomorphic.

On `E_J`, consider the new packet map

```text
T_(J,zeta)(v)_(k,l)
 =integral_T v(tau) partial_z^l m_tau(zeta_k)d eta_0(tau),
0<=l<e_k.                                                  (8)
```

This map is onto the complete finite complex target as a real-linear map.

### Proof

Suppose a real target functional annihilates `(8)`. The annihilator of the finite-codimensional
space `(4)` is the real span of the constant function and the real and imaginary parts of the
fixed functions `(2)`. Therefore a real combination of the target functions in `(8)` equals such
a fixed combination `eta_0`-almost everywhere.

After adjoining reflected conjugates, both sides are rational functions of `tau`. Their difference
vanishes on the infinite support of `eta_0`, so it is a rational identity. The target side has
principal parts only at `(6)`; the fixed side has principal parts only at `(7)`. The pole sets are
disjoint. Descending from the highest pole order at each point in `(6)` forces every target
coefficient to vanish. Hence the annihilating functional is zero, proving surjectivity. `QED`

The conclusion is stable if the second packet is enlarged: frozen finite-centre information costs
only finitely many parameter-pole directions and leaves all disjoint packets fully controllable.

## Residual maximal translation HT in an exact finite-jet level `[PROVED HERE]`

There is a dense residual subset

```text
G_(eta_0,J,delta) subset X_(eta_0,J,delta)                 (9)
```

such that, for every `w in G_(eta_0,J,delta)` and every finite tuple of distinct complex shifts
`h_1,...,h_m`, the functions

```text
m_(eta_w)(z+h_1),...,m_(eta_w)(z+h_m)                     (10)
```

are differentially algebraically independent over `C(z)`.

### Proof

Fix one differential-relation support. Refine the distinct-shift configuration space into
countably many sufficiently small compact patches. On each patch choose more auxiliary evaluation
rows than the complex rank-defect codimension requires, with all translated parameter poles
pairwise separated and disjoint from the frozen set `(7)` throughout that patch. At a fixed shift
configuration such row choices form a dense open set; separation persists after shrinking the
patch. The aperiodicity of `q` from the parent theorem removes translation stabilizers.

The constrained controllability theorem `(8)` supplies finitely many directions in `E_J` spanning
the complete row-jet target. On their finite real span, the universal
direction--shift evaluation map is a submersion. Parametric transversality makes the chosen
rank-defect preimage empty for a dense set of parameters inside every neighborhood of `(3)`.
Compact-patch normal convergence gives openness.

Intersect over the countable differential-relation patterns and a countable compact cover of all
finite distinct-shift configuration spaces. The resulting set is `(9)`, and clearing rational
coefficient denominators gives `(10)`. If a relation is initially defined only as an upper-end
germ, its terms are meromorphic on the common connected component above the shifted real lines, so
the identity theorem carries it to the chosen high evaluation rows. `QED`

Because every density in `(3)` is equivalent to `eta_0`, `(9)` holds with the exact transported
spectral type fixed. Componentwise normalization can additionally fix any prescribed pure-point /
singular-continuous / absolutely-continuous mass vector, by the same finite-codimension argument.

## Complete-germ closure `[PROVED HERE]`

Now fix one regular point `z_0 in C minus R` with `C(z_0)!=0`. If two boundary laws `eta_1,eta_2`
have the same complete Taylor jet

```text
partial_z^r m_(eta_1)(z_0)
 =partial_z^r m_(eta_2)(z_0)  for every r>=0,              (11)
```

their analytic germs agree. With `rho=eta_1-eta_2`, equation `(1)` gives on a neighborhood of
`z_0`

```text
integral_T 1/(tau-q(z))d rho(tau)=0.                      (12)
```

The open mapping theorem and Stieltjes-transform uniqueness imply `rho=0`, including its mass at
the projective point at infinity because `rho(T)=0`. Hence

```text
eta_1=eta_2.                                               (13)
```

Thus the infinite intersection of all finite-jet level sets at one regular point is a singleton,
although each finite stage contains infinite-dimensional positive charts with residual maximal
translation HT.

## Finite-jet aperture / complete-germ closure law

> **On the canonical boundary modulus of an indeterminate moment constraint, every finite
> finite-centre analytic jet leaves an infinite-dimensional positive aperture and a residual
> maximal full-translation HT phase, even at fixed spectral type. The coherent complete Taylor
> germ at one regular point closes that modulus to one boundary law. Analytic rigidity begins at
> germ completeness, not at any finite jet order.**

This is a phase threshold, not a claim that “finite data are insufficient” in the abstract. It
identifies the surviving positive geometry at every finite stage and proves exact closure at the
limit.

## Exact scope via Pick defect `[PROVED IN COMPANION]`

The companion `pick-defect-finite-selector-maximal-ht-phase-law.md` gives the global correction to
the chart theorem. A finite analytic packet can select uniquely when its reduced confluent Pick
matrix is singular; the unique solution then has a rational inner parameter and is finite-order
canonical. Otherwise the Pick matrix is positive definite, a free Schur parameter remains, and
maximal full-translation HT is dense residual in the entire exact level set.

The infinite-support boundary mixtures used here necessarily lie in the positive-defect phase. If
their finite data had singular Pick matrix, classical uniqueness would make their Pick parameter
rational inner and their moment solution finite-order canonical, contradicting the nontrivial
boundary mixture. Thus the aperture theorem above is exactly the nonsingular branch of the general
Pick-defect dichotomy, not an overstatement about singular boundary data.

## General HT consequence

For hypertranscendental carrier problems built from moment or Herglotz constraints, finitely many
normalizations, values, or derivatives cannot create differential rigidity while the Nevanlinna
boundary aperture remains. A successful constraint must do one of two positive things:

1. impose a complete coherent analytic germ, which determines the boundary law by `(11)`--`(13)`;
2. impose a genuinely global constraint whose tangent destroys the parameter-pole controllability
   used in `(8)`.

This supplies a practical route test: freeze the proposed finite source data and compute whether a
disjoint finite Cauchy-jet packet remains onto. If it does, maximal translation HT remains residual
inside the proposed carrier class.

## Lean status

Formalization is complete only relative to the exact classical Nevanlinna family already isolated
by the carrier stack. Finite-dimensional stratified avoidance and projected-incidence
stratification are now unconditional.

- `CauchyJetControllability` proves real-linear finite Cauchy-jet surjectivity and arbitrarily
  small positive finitely supported perturbations.
- `InfiniteSupportPositiveAperture`, `PositiveHilbertCubeEmbedding`, and
  `AtomlessProjectivePositiveAperture` prove the infinite-dimensional positive aperture and the
  closed embedded Hilbert-cube refinement under the stated support hypotheses.
- `AnalyticNevanlinnaCarrierBridge`, `NevanlinnaPositiveCarrierCapstone`, and
  `AnalyticNevanlinnaCarrierRelationFree` identify the abstract frozen tangent with actual
  weighted Nevanlinna-carrier jets and prove the dense residual all-finite-pattern
  hypertranscendental phase inside the exact positive chart.
- `CompleteCauchyGermClosure` proves canonical closure at `i` and `-i`, equality from all finite
  prefixes, affine transport of the complete derivative sequence, and
  `measure_eq_of_completeCauchyJet_eq` at every nonreal point. Thus the complete germ determines
  the carrier probability law with no canonical-node restriction.
- The boundary barycenter is a closed embedding in `NevanlinnaBoundaryKernel`; therefore equality
  of the selected carrier laws also identifies their boundary probability laws.

All project-specific deductions on this card are represented in Lean. The classical Nevanlinna
source theorem remains a theorem parameter; the former proper-projection/Whitney and smooth
parametric-transversality parameters are discharged by
`ProjectiveIncidenceHausdorffDimension` and `StratifiedParametricAvoidance`. Until the Nevanlinna
family is constructed in Lean, the residual-HT half of the card is not unconditional and the card
does not clear Stage 3.

## Positive RH-carrier consequence

Any RH route using only finitely many local values, derivatives, normalizations, Hankel minors, or
finite resolvent samples leaves the positive aperture `(3)` whenever its underlying moment carrier
is indeterminate. Such a route must be completed by an all-order coherent analytic constraint or a
global orientation law.

The current Xi/Hedenmalm route crosses the selection threshold: the complete pointed Taylor germ
of the normalized prime--archimedean source determines the germ, source trace, `XiC`, and local
Bezoutian. The remaining RH-bearing obligation is not another finite jet. It is the global
Hermitian orientation sign of the reconstructed kernel.

## Parent-theory and novelty attack

1. `[SEARCH]` Finite-codimensional kernels in `L-infinity`, analytic germ uniqueness, and
   Stieltjes-transform uniqueness are standard.
2. `[BRIDGE]` Parameter-pole controllability and full shift-configuration transversality are the
   engines of the parent moment-fiber HT theorem.
3. `[PROVED HERE]` Freezing an arbitrary finite Cauchy jet only adds a finite set of parameter poles;
   disjoint principal-part elimination restores complete controllability on the constrained
   tangent.
4. `[PROVED HERE]` Residual maximal full-translation HT therefore survives inside every exact
   finite-jet positive level at fixed spectral type.
5. `[PROVED HERE]` The complete coherent Taylor germ closes the same boundary modulus to a point,
   producing an exact finite/infinite analytic selection threshold.
6. `[CANDIDATE RESIDUE]` Preliminary exact searches found no theorem combining this threshold with
   residual full-complex translation differential independence in an exact complete-moment fiber.
7. The theorem remains `[NOVELTY UNVERIFIED]` pending review by specialists in moment problems,
   differential algebra, transversality, and operator theory.

No numerical experiment and no RH assumption enter the theorem.

## Honest significance score

The combined route is now an internal **90/100 candidate**, with a deliberately wide **72--94**
range pending specialist proof and priority review. This is the first point at which the route has
a plausible 90 case, not a verified field-level score.

- **Why it creates the plausible 90 case:** the theorem classifies the analytic selection
  threshold itself. It proves both sides: residual maximal HT in every exact finite-jet level and
  uniqueness at the complete-germ limit. This is a reusable law for constrained HT carriers, not
  only a description of one convex fiber.
- **Why 90 is not yet verified:** the mechanism still synthesizes classical moment theory with the existing
  transversality engine; priority is unaudited; no explicit source-canonical maximally HT member is
  constructed; the theorem is not formalized in Lean; and the Xi orientation sign remains open.

## Formalization audit

The complete-germ closure `(11)`--`(13)`, finite Cauchy-jet controllability, positive Hilbert-cube
aperture, Nevanlinna carrier bridge, and all project-specific Baire deductions are formalized.
The remaining blocker is the construction of the classical analytic Nevanlinna family from an
arbitrary indeterminate Hamburger sequence. `StratifiedParametricAvoidance` constructs the
formerly packaged finite-dimensional avoidance value, and
`ProjectiveIncidenceHausdorffDimension` constructs the formerly packaged projective-incidence
stratification value unconditionally.

### Exact shape of the remaining blocker

The single packaged input is `ClassicalNevanlinnaExtremalFamily s` in
`formal/GaloisForLFunctions/HTGeometry/NevanlinnaClassicalInterface.lean`.  Everything downstream
of it is proved.  Discharging it means *constructing*, from an arbitrary indeterminate Hamburger
sequence `s`: the four Nevanlinna functions `A,B,C,D` with `AD - BC = 1`, continuity of the
denominator row, and the weakly continuous N-extremal leaf family carried by the denominator zero
sets with the exact moments of `s`.  That is the classical Nevanlinna parametrization
(Akhiezer/Berg--Valent), and the base is *entirely absent from mathlib*: a check of the mathlib
tree finds no Hamburger moment problem, no orthogonal polynomials on the real line, and no Hankel
form theory.  The construction chain is

```text
positive definite moment form -> orthonormal polynomials P_n, Q_n
  -> three-term recurrence / Jacobi matrix
  -> indeterminacy <=> sum |P_n(z)|^2 converges
  -> A,B,C,D as entire functions of minimal exponential type
  -> AD - BC = 1  -> Nevanlinna parametrization -> N-extremal leaves.
```

This is a multi-module development, not a missing lemma.

### Layer built here

`formal/GaloisForLFunctions/HTGeometry/MomentInnerProduct.lean` supplies the first link of that
chain, unconditionally and axiom-clean (build clean with zero warnings; `#print axioms` on all
endpoints reports only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`/`axiom`):

- `momentInner s p q = L_s (p * q)` with symmetry, full bilinearity, and finite-sum linearity.
- `momentInner_X_mul` : multiplication by `X` is symmetric for the form.  This is the Jacobi/Hankel
  symmetry that the three-term recurrence rests on.
- `PositiveMomentForm s` bundles positive definiteness `p ≠ 0 → 0 < ⟪p,p⟫_s`, the exact hypothesis
  Gram--Schmidt consumes, with `nonneg`, `self_eq_zero_iff`, `self_ne_zero`.
- `positiveMomentForm_of_infiniteSupport` constructs it from any representing measure charging the
  complement of every finite set, reusing the corpus lemmas behind
  `momentHankelMatrix_posDef_of_infiniteSupport`.
- `momentInner_sq_le` is Cauchy--Schwarz; `eq_zero_of_forall_momentOrthogonal` proves that an
  orthogonal family of nonzero polynomials is linearly independent — the fact that makes
  Gram--Schmidt terminate with nonzero output at every degree.

**This does not clear the gate.**  It is one layer of the chain above; the card stays at Stage 2.
The next layer is the orthonormal polynomials themselves: construct `P : ℕ → Polynomial ℝ` by
Gram--Schmidt on the monomials with `degree (P n) = n` and `⟪P m, P n⟫ = δ` (the degree bookkeeping
and the recursion-under-`Finset.sum` are the two known difficulties), then the three-term
recurrence from `momentInner_X_mul`.

## Gates

- [x] arbitrary finite Cauchy-jet level defined
- [x] infinite-dimensional positive aperture proved
- [x] exact moment and spectral-type preservation proved
- [x] disjoint-pole controllability on the constrained tangent proved
- [x] residual maximal full-translation HT in the exact finite-jet level proved
- [x] complete-germ uniqueness proved
- [x] finite-jet / complete-germ threshold law extracted
- [x] scope corrected and completed by the singular/free Pick-defect companion
- [x] concrete Xi/Hedenmalm consequence scoped
- [x] local prior-research collision search
- [ ] independent specialist proof audit
- [ ] full primary-source priority audit
- [ ] unconditional Lean formalization of the entire exact theorem
  - [x] moment inner product and positive-definite moment form (`MomentInnerProduct.lean`)
  - [x] monic orthogonal polynomials by Gram--Schmidt, exact degree `n`, mutual orthogonality
        (`OrthogonalMomentPolynomials.lean`)
  - [x] orthogonality to *every* polynomial of lower degree, and tridiagonality of the Jacobi form
        (`monicOrtho_inner_eq_zero_of_degree_lt`, `monicOrtho_X_mul_inner_eq_zero`)
  - [x] normalization to the orthonormal family (`OrthonormalMomentPolynomials.lean`:
        `orthonormalPoly`, `orthonormalPoly_inner` giving the exact Kronecker relation, exact
        degree, positive leading coefficient)
  - [x] span lemma and Fourier expansion (`mem_span_monicOrtho`, `monicOrtho_expansion`)
  - [x] explicit three-term recurrence `monicOrtho_three_term`, with lower coefficient the ratio of
        consecutive moment norms (hence positive by `monicOrtho_inner_self_pos`)
  - [x] Christoffel--Darboux reproducing-kernel identity (`ChristoffelDarboux.lean`), the engine
        transferring convergence of `sum |P_n(z)|^2` between points
  - [x] complex evaluation, conjugation symmetry, and the reproducing-kernel form of
        Christoffel--Darboux (`ComplexChristoffelDarboux.lean`)
  - [x] second-kind polynomials, exact degree `deg R_{n+1} = n`, and the constant Wronskian
        `Q_{n+1} R_n - Q_n R_{n+1} = -h_n/h_0` (`SecondKindMomentPolynomials.lean`)
  - [x] the full trio of Christoffel--Darboux identities: first/first
        (`christoffelDarboux`), first/second with its `1/h_0` boundary constant
        (`mixedChristoffelDarboux`), second/second (`secondKindChristoffelDarboux`)
  - [x] exact real formula for the partial kernel sums: `kernelSum_mul_im` computes
        `(sum_{k<=n} |Q_k(z)|^2/h_k) * Im z * h_n` as a single imaginary part at level `n`
  - [x] indeterminacy criterion at a nonreal point, as an **equivalence**:
        `summable_kernel_iff_wronskian_bdd` proves `Summable (fun k => |Q_k(z)|^2/h_k)` iff the
        level-`n` Wronskian expression is bounded in `n`
  - [x] Duhamel comparison formula `monicOrtho_duhamel` relating `Q_n(w)` to the data at `z`
  - [x] second-kind family at complex points and mixed Christoffel--Darboux over `C`
        (`ComplexSecondKind.lean`)
  - [x] complex Duhamel comparison `monicOrthoC_duhamel`
  - [x] weighted Cauchy--Schwarz `weightedSum_sq_le` bounding the Duhamel sums by the kernel sums
  - [x] `kernelRoot` and `norm_weightedSum_le`: the Duhamel sums bounded by products of kernel roots
  - [ ] transfer of convergence from one nonreal point to all of `C` (absorption + covering)
  - [x] finite/polynomial-level determinant condition: the transfer matrix `momentTransfer` has
        determinant the nonzero constant `-h_n/h_0`, hence is a unit over `R[X]`
  - [x] `n`-independent normalized Wronskian `a_n (p_{n+1} r_n - p_n r_{n+1}) = -1/h_0`, equal to
        `-1` for a normalized sequence (`OrthonormalWronskian.lean`)
  - [ ] `A,B,C,D` as entire functions and the determinant identity `AD - BC = 1`
  - [ ] N-extremal leaf family, denominator-carried, with the moments of `s`
  - [ ] discharge `ClassicalNevanlinnaExtremalFamily`

## Log

- 2026-07-12 -- Froze an arbitrary finite packet of finite-centre Cauchy jets in the boundary
  density chart. Proved that the constrained tangent remains infinite-dimensional and controls
  every disjoint jet packet, yielding residual maximal full-translation HT at fixed spectral type.
  Proved that the complete Taylor germ at one regular point uniquely determines the boundary law.
- 2026-07-18 -- Remaining Lean blocker pinned to the single packaged input
  `ClassicalNevanlinnaExtremalFamily s`, and its construction chain written out. Confirmed mathlib
  carries no moment-problem, orthogonal-polynomial, or Hankel-form base, so the chain must be built
  from scratch. First link built unconditionally as
  `HTGeometry/MomentInnerProduct.lean` (moment inner product, `momentInner_X_mul` symmetry,
  `PositiveMomentForm`, construction from an infinite-support representing measure,
  Cauchy--Schwarz, orthogonal-implies-independent). Card remains Stage 2: the gate is a
  multi-module development and one link of it is done.
- 2026-07-18 -- Second link built: `HTGeometry/OrthogonalMomentPolynomials.lean`. Gram--Schmidt on
  the monomials gives `monicOrtho s n`, proved monic of exact degree `n` *unconditionally* (the
  correction is a lower-degree combination whatever the coefficients are), with mutual
  orthogonality and linear independence under `PositiveMomentForm`. Verified by single-file
  elaboration (`lake env lean`), zero errors and zero warnings; all eight endpoints axiom-clean
  (`propext`, `Classical.choice`, `Quot.sound`); no placeholders. Card remains Stage 2.
- 2026-07-18 -- Third link: `monicOrtho_inner_eq_zero_of_degree_lt` proves `monicOrtho s n` is
  orthogonal to *every* polynomial of degree `< n` (induction rebuilding an arbitrary `p` from its
  leading monomial via `X^d = monicOrtho d + correction`), and `monicOrtho_X_mul_inner_eq_zero`
  derives tridiagonality of the Jacobi form from it together with `momentInner_X_mul`. Both
  axiom-clean, file elaborates with zero errors and zero warnings. The remaining recurrence gate is
  now only the *explicit coefficients*, which need the span lemma; the banded structure itself is
  proved. Card remains Stage 2.
- 2026-07-18 -- Fourth link: `mem_span_monicOrtho` (polynomials of degree `< m` lie in the span of
  the first `m` members), `momentInner_eq_zero_of_mem_span`, and `monicOrtho_expansion` (a
  polynomial of degree `< m` equals the sum of its moment projections). The expansion is proved by
  showing the residual is orthogonal to every generator *and* lies in their span, hence has zero
  moment norm, hence vanishes by positive definiteness. All axiom-clean; file elaborates with zero
  errors and zero warnings. The explicit three-term coefficients now follow by applying the
  expansion to `X * Q n - Q (n+1)`. Card remains Stage 2.
- 2026-07-19 -- Fifth link: `monicOrtho_three_term`, the explicit three-term recurrence
  `X * Q (n+1) = Q (n+2) + a * Q (n+1) + b * Q n` with `a` the diagonal matrix element and
  `b = <Q (n+1), Q (n+1)> / <Q n, Q n>` the ratio of consecutive moment norms, positive by
  `monicOrtho_inner_self_pos`. Obtained by applying `monicOrtho_expansion` to `X * Q (n+1) - Q (n+2)`
  (degree `< n+2` since both are monic of degree `n+2`), with `monicOrtho_X_mul_inner_eq_zero`
  killing every index below `n`; the upward matrix element is identified by
  `momentInner_monicOrtho_succ_X_mul`. Supporting lemmas `momentInner_sub_right`,
  `degree_X_mul_monicOrtho`, `monic_X_mul_monicOrtho`, `degree_X_mul_monicOrtho_sub_succ_lt`.
  Exit code 0, zero errors, zero warnings; all endpoints axiom-clean. This closes the Jacobi-matrix
  half of the chain: the moment sequence now has a formal tridiagonal Jacobi form with positive
  off-diagonal. Card remains Stage 2.
- 2026-07-19 -- Sixth link: `HTGeometry/OrthonormalMomentPolynomials.lean` normalizes the monic
  family by its moment norm. `orthonormalPoly_inner` is the exact Kronecker orthonormality relation
  `<P m, P n> = if m = n then 1 else 0`; exact degree, positive leading coefficient (the classical
  sign normalization), and inherited orthogonality to all lower degrees are also proved.
  `orthonormalPoly_leadingCoeff` needs no positivity hypothesis and is stated without one. Exit code
  0, all endpoints axiom-clean, zero placeholders. This is the family whose complex evaluations
  control indeterminacy via convergence of `sum |P n z|^2`, which is the next link. Card remains
  Stage 2.
- 2026-07-19 -- Seventh link: `HTGeometry/ChristoffelDarboux.lean` proves the reproducing-kernel
  identity `(x - y) * sum_{k<=n} Q_k(x) Q_k(y) / h_k = (Q_{n+1}(x) Q_n(y) - Q_n(x) Q_{n+1}(y)) / h_n`
  by induction on the three-term recurrence: the diagonal coefficient cancels and the off-diagonal
  `h_{n+1}/h_n` is exactly what telescopes the Wronskian-like numerator. Purely algebraic, no
  analysis. Exit code 0, zero warnings, all three endpoints axiom-clean, zero placeholders. This is
  the tool that transfers convergence of `sum |P_n(z)|^2` from one point to the whole plane, which
  is the remaining indeterminacy criterion. Card remains Stage 2.
- 2026-07-19 -- Eighth link: `HTGeometry/ComplexChristoffelDarboux.lean`. The monic family has real
  coefficients, so `monicOrthoC_conj` gives `Q_n(conj z) = conj (Q_n z)` via `Complex.conjAe`, and
  Christoffel--Darboux holds verbatim over `C` (`christoffelDarbouxC`). Specializing `w = conj z`
  (`christoffelDarbouxC_conj`) turns the left side into the positive reproducing kernel
  `sum_{k<=n} |Q_k(z)|^2 / h_k` and the right side into a Wronskian in `Q_n, Q_{n+1}` at the single
  point `z` -- the exact finite identity the indeterminacy criterion is read off from. Exit code 0,
  zero warnings, all four endpoints axiom-clean, zero placeholders. Card remains Stage 2.
- 2026-07-19 -- Ninth link: `HTGeometry/SecondKindMomentPolynomials.lean`. The recurrence
  coefficients are named (`recurDiag`, `recurOff`) and the recurrence is put in solved form
  `monicOrtho_succ_succ`. The second-kind polynomials `secondKind` are defined by the *same*
  two-step recurrence with initial data `R_0 = 0`, `R_1 = 1` -- the second solution of the
  recurrence, defined purely algebraically with no measure or divided difference. The Wronskian
  `Q_{n+1} R_n - Q_n R_{n+1}` is proved to be a *constant polynomial* equal to `C (-h_n/h_0)`
  (`momentWronskian_eq`), and nonvanishing (`momentWronskian_ne_zero`); the diagonal coefficient
  cancels because both families obey the same recurrence, and the off-diagonal one telescopes.
  Constancy in `z` is what makes `R_n / Q_n` a genuine Nevanlinna-type fraction, and the explicit
  value is the normalization behind `AD - BC = 1`. Exit code 0, zero warnings, all five endpoints
  axiom-clean, zero placeholders. Card remains Stage 2.
- 2026-07-19 -- Tenth link: exact degree of the second-kind family.
  `secondKind_succ_monic_degree` proves `R_{n+1}` is monic of degree exactly `n` (monicity and
  degree proved together, since the two-step recurrence consumes both at each stage), with
  `secondKind_succ_ne_zero` and `secondKind_degree_succ_eq` recording that the second solution lags
  the first by exactly one degree. This is the fact behind the Pade/continued-fraction reading of
  `R_n / Q_n` and is needed for the entire-function construction. Exit code 0, zero warnings, all
  three endpoints axiom-clean, zero placeholders. Card remains Stage 2.
- 2026-07-19 -- Eleventh link: `mixedChristoffelDarboux` pairs the first-kind family at `x` against
  the second-kind family at `y`. The telescoping is the same as for `christoffelDarboux`, but the
  `n = 0` boundary term no longer vanishes: `R_0 = 0`, `R_1 = 1` leave the constant `1/h_0`, giving
  `(x-y) sum_{k<=n} Q_k(x) R_k(y)/h_k = (Q_{n+1}(x) R_n(y) - Q_n(x) R_{n+1}(y))/h_n + 1/h_0`. That
  surviving constant is the normalization that becomes the determinant identity of the Nevanlinna
  matrix. Supporting evaluated recurrences `monicOrtho_succ_succ_eval`, `secondKind_succ_succ_eval`.
  Exit code 0, zero warnings, all three endpoints axiom-clean, zero placeholders. Card remains
  Stage 2.
- 2026-07-19 -- Twelfth link: `secondKindChristoffelDarboux` completes the trio of bilinear
  identities carried by the recurrence. Pairing the second-kind family against itself, the `n = 0`
  boundary term vanishes (`R_0 = 0`), so unlike the mixed identity no constant survives:
  `(x-y) sum_{k<=n} R_k(x) R_k(y)/h_k = (R_{n+1}(x) R_n(y) - R_n(x) R_{n+1}(y))/h_n`. The three
  identities (Q/Q, Q/R, R/R) are exactly the algebraic input to the finite determinant identity
  `A_n D_n - B_n C_n = 1` for the truncated Nevanlinna matrix. Exit code 0, zero warnings,
  axiom-clean, zero placeholders. Card remains Stage 2.
- 2026-07-19 -- Thirteenth link: `momentTransfer` packages the two solutions as a `2x2` matrix over
  `R[X]`. `momentTransfer_det_eq_wronskian` identifies its determinant with the Wronskian,
  `momentTransfer_det` gives the explicit constant `-h_n/h_0`, and `momentTransfer_det_isUnit` /
  `momentTransfer_isUnit` upgrade this to invertibility *over the polynomial ring itself* (a nonzero
  constant is a unit of `R[X]`), not merely over the fraction field. This is the finite,
  polynomial-level form of the determinant condition a Nevanlinna matrix carries.

  Scope note recorded deliberately: an earlier plan for this step was a finite
  `A_n D_n - B_n C_n = 1` for truncated Nevanlinna entries. Working the algebra on paper first, the
  index conventions used here did not yield that cancellation, so it was **not** formalized. The
  correct finite statement in this (monic) normalization is the Wronskian/determinant above; the
  literal `AD - BC = 1` is the *limit* statement after the orthonormal rescaling
  `a_n (p_{n+1} r_n - p_n r_{n+1}) = -1/h_0`, which needs the orthonormal second-kind family and is
  left to the next link. Exit code 0, zero warnings, all four endpoints axiom-clean, zero
  placeholders. Card remains Stage 2.
- 2026-07-19 -- Fourteenth link: `HTGeometry/OrthonormalWronskian.lean` closes the scope gap flagged
  in the previous entry. Rescaling both families by their moment norms (`secondKindNorm`) and
  weighting by the orthonormal off-diagonal coefficient `a_n = ||Q_{n+1}||/||Q_n||` (`recurOffSqrt`)
  removes the `n`-dependence of the monic Wronskian entirely: `orthonormalWronskian_eq` proves
  `a_n (p_{n+1} r_n - p_n r_{n+1}) = -1/h_0` for every `n`, and
  `orthonormalWronskian_eq_neg_one` specializes to `-1` when the sequence is normalized (`h_0 = 1`).
  This is the finite precursor of `AD - BC = 1`: the paper computation
  `(N_{n+1}/N_n) * (-h_n/h_0)/(N_n N_{n+1}) = -1/h_0` using `N_n^2 = h_n`, verified before
  formalizing. Exit code 0, zero warnings, all four endpoints axiom-clean, zero placeholders.
  Card remains Stage 2.
- 2026-07-19 -- Fifteenth link: `kernelSum_mul_im` descends the complex reproducing-kernel identity
  to a purely real one. Both sides of `christoffelDarbouxC_conj` are `2i * (real)`, so the identity
  determines the weighted partial sum `sum_{k<=n} |Q_k(z)|^2 / h_k` exactly, as one imaginary part
  `Im(Q_{n+1}(z) conj(Q_n(z)))` at level `n`. This is the finite quantity whose boundedness in `n`
  *is* the indeterminacy criterion, so the criterion is now a statement about a concrete real
  sequence rather than about an abstract series. Exit code 0, zero warnings, axiom-clean, zero
  placeholders. Card remains Stage 2.
- 2026-07-19 -- Sixteenth link: summability of the positive kernel. `kernelTerm_nonneg` plus
  `summable_of_sum_range_le` reduce convergence to bounded partial sums; `kernelSum_eq` solves
  `kernelSum_mul_im` for the partial sum in closed form
  `Im(Q_{n+1}(z) conj(Q_n(z))) / (h_n * Im z)`; and `summable_kernel_of_wronskian_le` converts a
  single bound on that expression into genuine `Summable` for the series `|Q_k(z)|^2 / h_k`. The
  indeterminacy criterion is now a Lean `Summable` statement about an explicit sequence, not an
  informal series condition. The remaining half is the *transfer*: convergence at one nonreal point
  implying convergence everywhere. Exit code 0, zero warnings, all four endpoints axiom-clean, zero
  placeholders. Card remains Stage 2.
- 2026-07-19 -- Seventeenth link: the criterion upgraded from an implication to an equivalence.
  `sum_range_le_tsum_kernel` bounds every partial sum by the total (nonnegative terms),
  `summable_kernel_iff` states summability as boundedness of partial sums, and
  `summable_kernel_iff_wronskian_bdd` combines this with `kernelSum_eq` to give, at any nonreal `z`:
  `Summable (fun k => |Q_k(z)|^2 / h_k)` **iff** `Im(Q_{n+1}(z) conj(Q_n(z))) / (h_n Im z)` is
  bounded in `n`. Exit code 0, zero warnings, all three endpoints axiom-clean, zero placeholders.

  Deliberately not attempted this turn: the discrete variation-of-constants (Duhamel) formula that
  the *transfer* between points needs. Its index conventions were derived on paper via the transfer
  matrix and the candidate closed form failed a small-`n` check (`n = 2` gave `R_2(z) = z - a_0`
  where the formula demanded `-1`), so it was not formalized. The correct route is
  `U_n = Phi_n Phi_0^{-1} U_0 + sum_k Phi_n Phi_{k+1}^{-1} (f_k, 0)` with `Phi` the already-built
  `momentTransfer`; establishing the exact index range is the next step. Card remains Stage 2.
- 2026-07-19 -- Duhamel comparison formula: **derived and paper-verified, NOT yet formalized.**

  The formula is
  `Q_n(w) = Q_n(z) - (w-z) h_0 [ Q_n(z) T_n - R_n(z) S_n ]`
  with `S_n = sum_{j<=n} Q_j(w) Q_j(z)/h_j` and `T_n = sum_{j<=n} Q_j(w) R_j(z)/h_j`.

  It needs **no new induction**: `christoffelDarboux` gives `(w-z) S_n` in closed form,
  `mixedChristoffelDarboux` gives `(w-z) T_n` (contributing the `1/h_0` term), and substituting both
  makes the `R_n(z)` contributions cancel, leaving `Q_n(w)` after one application of
  `momentWronskian_eq`. Checked by hand at `n = 1` and `n = 2` (the `n = 2` check reproduces
  `(w-z)(w+z-a_0-q)` on both sides), which also corrected the earlier wrong ansatz recorded in the
  previous entry -- the correct Green kernel is `(phi_n psi_{k+1} - psi_n phi_{k+1})/W_{k+1}` with
  the `k = n-1` term vanishing automatically.

  Formalization status: the two supporting steps are settled -- the numerator rearrangement is pure
  `ring`, and the Wronskian substitution is `momentWronskian_eq` evaluated at `z`. The final
  assembly after `rw [hMix, hCD]; field_simp` needs a `linear_combination` coefficient that five
  attempts did not find. Rather than keep guessing, the file was reverted to its last verified
  state; `SecondKindMomentPolynomials.lean` compiles clean and contains no partial Duhamel code.
  Next session should prove the numerator identity as a standalone `have` (via `hbracket` then
  `hWz`) and divide once, instead of clearing denominators and guessing a combination.
  Card remains Stage 2.
- 2026-07-19 -- Eighteenth link: `monicOrtho_duhamel` **now formalized**, closing the gap left in the
  previous entry. The fix was the one recorded there: prove the numerator identity as a standalone
  `have` (pure `ring`, then `momentWronskian_eq` at `z`) and divide once via an explicit `calc`,
  instead of clearing all denominators and guessing a `linear_combination` coefficient. The one
  remaining obstacle was that `field_simp` needed the nonvanishing hypotheses passed explicitly as
  `field_simp [h0, hn]`; with that the whole chain closes. Exit code 0, zero warnings, axiom-clean,
  zero placeholders, file 394 lines.

  The formula `Q_n(w) = Q_n(z) - (w-z) h_0 [Q_n(z) T_n - R_n(z) S_n]` expresses the polynomials at
  an arbitrary point in terms of the data at a fixed point plus the two partial sums, which is
  exactly the input a Gronwall bootstrap needs to transfer convergence of `sum |Q_k(z)|^2/h_k`
  between points. Card remains Stage 2.
- 2026-07-19 -- Nineteenth link: `HTGeometry/ComplexSecondKind.lean`. `monicOrtho_duhamel` is stated
  over `R` via `Polynomial.eval`, but the transfer compares *complex* points, so the second-kind
  machinery is redone over `C`: `secondKindC` with its recurrence, `monicOrthoC_succ_succ` in the
  matching solved form, and `mixedChristoffelDarbouxC` -- the mixed identity over `C`, again with
  the `1/h_0` boundary constant surviving at `n = 0`. Each proof mirrors its real counterpart
  through `aeval`. Exit code 0, zero warnings, all three endpoints axiom-clean, zero placeholders.
  With `christoffelDarbouxC` already in hand, the complex Duhamel formula now has both partial sums
  available in closed form and can be assembled by the same `calc` shape that worked over `R`.
  Card remains Stage 2.
- 2026-07-19 -- Twentieth link: `monicOrthoC_duhamel`, the complex counterpart of the real Duhamel
  formula, together with `monicOrthoC_wronskian` (the constant Wronskian at a complex point). The
  proof is a direct transcription of the real one -- numerator identity by `ring` plus the Wronskian
  substitution, then a five-step `calc` dividing once -- confirming that the proof *shape* found two
  turns ago transfers verbatim. Exit code 0, zero warnings, both endpoints axiom-clean, zero
  placeholders, file 180 lines.

  All structural ingredients for the convergence transfer are now present over `C`:
  `christoffelDarbouxC`, `mixedChristoffelDarbouxC`, `monicOrthoC_wronskian`,
  `monicOrthoC_duhamel`, and the point criterion `summable_kernel_iff_wronskian_bdd`. What remains
  is genuinely an estimate rather than an identity: bound the Duhamel sum by Cauchy--Schwarz against
  the kernel, obtain `sigma_n(w) <= A + B|w-z| sigma_n(w)`, and close by absorption for
  `|w-z|` small, then iterate over a chain of discs to reach all of `C`. Card remains Stage 2.
- 2026-07-19 -- Twenty-first link: `weightedSum_sq_le`, weighted Cauchy--Schwarz for the weights
  `1/h_j`. The Duhamel sums `S_n`, `T_n` are inner products against those weights, so this bounds
  them by the kernel sums that the criterion is stated in. Proved by substituting
  `|f_j| / sqrt(h_j)` into mathlib's `Finset.sum_mul_sq_le_sq_mul_sq` and converting the three sums
  back with `div_mul_div_comm` and `Real.sq_sqrt` -- no `convert`, three explicit `Finset.sum_congr`
  rewrites instead. Exit code 0, zero warnings, axiom-clean, zero placeholders, file 228 lines.

  This is the first genuine *inequality* in the chain; the twenty preceding links were exact
  identities. Remaining for the transfer: combine `monicOrthoC_duhamel` with this bound to reach
  `sigma_n(w) <= A + B|w-z| sigma_n(w)`, absorb for `|w-z|` small, and iterate over a chain of discs.
  Card remains Stage 2.
- 2026-07-19 -- Twenty-second link: `kernelRoot` (the square root of a weighted kernel sum, the
  natural norm for these estimates) and `norm_weightedSum_le`, which puts Cauchy--Schwarz in the
  form the Duhamel estimate consumes: a weighted sum is bounded by the product of the two kernel
  roots. Proved by the triangle inequality termwise, then `Real.sqrt_le_sqrt` applied to
  `weightedSum_sq_le` followed by `Real.sqrt_sq` -- the `Real.le_sqrt` iff-lemma family did not
  match in this toolchain, and monotonicity of `sqrt` avoids the naming question entirely. Exit code
  0, zero warnings, both endpoints axiom-clean, zero placeholders, file 269 lines.

  Paper derivation of the remaining absorption step, recorded so the next session does not redo it:
  from Duhamel plus this bound,
  `|Q_n(w)| <= |Q_n(z)| + |w-z| h_0 sigma_n(w) (|Q_n(z)| rho_n(z) + |R_n(z)| sigma_n(z))`;
  dividing by `sqrt(h_n)`, squaring with `(a+b)^2 <= 2a^2 + 2b^2`, summing over `n <= N` and using
  monotonicity of the partial sums gives
  `sigma_N(w)^2 <= 2 sigma_N(z)^2 + 8 |w-z|^2 h_0^2 sigma_N(w)^2 sigma_N(z)^2 rho_N(z)^2`.
  If both `sum |Q_j(z)|^2/h_j` and `sum |R_j(z)|^2/h_j` converge, with bounds `S^2` and `P^2`, then
  whenever `8 |w-z|^2 h_0^2 S^2 P^2 <= 1/2` the last term absorbs and `sigma_N(w)^2 <= 4 S^2`
  uniformly in `N`, giving summability at `w`. Note the hypothesis needs *both* series at `z`.
  Card remains Stage 2.
