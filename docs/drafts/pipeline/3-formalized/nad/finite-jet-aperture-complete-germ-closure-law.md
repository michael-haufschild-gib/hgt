# Finite jets retain maximal HT; one complete germ closes the boundary modulus

- **ID:** `finite-jet-aperture-complete-germ-closure-law`
- **Stage:** 3-formalized
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
  - [x] pointwise Duhamel estimate `norm_monicOrthoC_duhamel_le`
  - [x] kernel-root infrastructure: `kernelRoot_sq`, `kernelRoot_mono`,
        `kernelRoot_sq_eq_normSq_sum`, and `summable_of_kernelRoot_le` (a uniform kernel-root bound
        gives `Summable`, connecting the estimate layer to the criterion)
  - [x] frozen-level and squared pointwise estimates (`norm_monicOrthoC_duhamel_le_of_le`,
        `normSq_monicOrthoC_duhamel_le`)
  - [x] the absorption inequality `kernelRoot_sq_le_absorption`:
        `K_N^2 <= 2 S_N^2 + 8 D^2 K_N^2 S_N^2 P_N^2`
  - [x] absorption: `summable_kernel_transfer` -- bounded kernel roots at `z` plus `|w-z|` small
        gives `Summable` at `w`
  - [x] explicit transfer radius `transferRadius s S P = 1/(4 h_0 S P)`, positive, with
        `summable_kernel_transfer_of_dist` transferring convergence to the whole disc
  - [x] third bilinear identity at complex points: `secondKindChristoffelDarbouxC` (R/R over `C`)
  - [x] `R`-side Duhamel comparison `secondKindC_duhamel`
  - [x] `R`-side pointwise estimate `norm_secondKindC_duhamel_le`
  - [x] `R`-side frozen/squared/absorption steps (`norm_secondKindC_duhamel_le_of_le`,
        `normSq_secondKindC_duhamel_le`, `kernelRootR_sq_le_absorption`)
  - [x] both bounds propagate: `kernelRoot_bounds_propagate` gives `2S`, `2P` at the new centre
  - [x] the good set is open: `BoundedKernel`, `isOpen_boundedKernel`
  - [x] clopen/connectedness implication packaged: `boundedKernel_of_isClosed`,
        `summable_kernel_everywhere_of_isClosed` (`ComplexKernelTransfer.lean`)
  - [ ] the good set is closed -- the one genuinely analytic input still missing
  - [ ] iterate over a chain of discs to reach all of `C`
  - [x] finite/polynomial-level determinant condition: the transfer matrix `momentTransfer` has
        determinant the nonzero constant `-h_n/h_0`, hence is a unit over `R[X]`
  - [x] `n`-independent normalized Wronskian `a_n (p_{n+1} r_n - p_n r_{n+1}) = -1/h_0`, equal to
        `-1` for a normalized sequence (`OrthonormalWronskian.lean`)
  - [x] the Pluecker relation and the determinant precursor
        `h_0 z^2 (alpha delta - beta gamma) = z (beta - gamma)` (`NevanlinnaPluecker.lean`)
  - [x] truncated `A_n,B_n,C_n,D_n` and the **exact determinant identity `A_n D_n - B_n C_n = 1`**
        at every level `n` (`NevanlinnaPluecker.lean`)
  - [x] absolute summability of the four bilinear series from kernel bounds
        (`summable_weighted_of_bounds`)
  - [x] limiting matrix `nevAinf..nevDinf` with `AD - BC = 1` in the limit, given `BoundedKernel`
        at `0` and at `z`
  - [x] Cauchy--Schwarz over an arbitrary index set (`weightedSum_sq_le_finset`,
        `norm_sum_weighted_le_finset`) -- the uniform Cauchy tail estimate
  - [x] **full uniform Cauchy criterion**: `norm_sum_Ico_weighted_le_tail` bounds every tail by a
        quantity depending only on `N`, and `tendsto_uniformCauchyBound_zero` shows it vanishes
  - [x] `uniformCauchy_weighted`: one threshold works for every `M` and every family meeting the
        kernel bound -- uniform convergence over a transfer disc
  - [x] `UniformCauchySeqOn` for the partial sums (`uniformCauchySeqOn_bilinearPartialSum`) --
        mathlib's uniform-convergence API is now reachable
  - [x] **holomorphy of the limit** and of the actual entries: `differentiableOn_bilinearLimit`,
        `differentiableOn_nevA_series`, `differentiableOn_nevC_series`,
        `differentiableOn_nevD_series`
  - [x] capstone `nevanlinna_holomorphic_unimodular`: all four limiting entries holomorphic on an
        open set with uniform kernel bounds, and `AD - BC = 1` there
  - [x] size bounds `norm_tsum_weighted_le`, `norm_nevAinf_le`, `norm_nevDinf_le`: each entry is
        bounded by `h_0 |z|` times a product of kernel roots
  - [ ] growth of the kernel roots themselves -- the only remaining unknown for exponential type
  - [ ] N-extremal leaf family, denominator-carried, with the moments of `s`
  - [x] **`ClassicalNevanlinnaMatrixData R` constructed** (`nevMatrixData`) -- the matrix half of the
        packaged input is no longer packaged
  - [x] continuity of the denominator row (`continuous_nevMatrixData_B/_D`)
  - [x] Christoffel--Darboux kernel: reproducing property, symmetry, degree bound, self-reproducing
        identity, and the Christoffel function (`ChristoffelKernel.lean`)
  - [ ] discharge the rest of `ClassicalNevanlinnaExtremalFamily`: the weakly continuous leaf family
        of probability measures, its carrier conditions, and the moment identities

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
- 2026-07-19 -- Twenty-third link: `norm_monicOrthoC_duhamel_le`, the pointwise Duhamel estimate

  `|Q_n(w)| <= |Q_n(z)| + |w-z| h_0 * kappa_w(n) * (|Q_n(z)| rho_z(n) + |R_n(z)| sigma_z(n))`

  where the three `kernelRoot`s are those of `Q(.,w)`, `R(.,z)`, `Q(.,z)`. This is the first line of
  the paper derivation recorded last turn, now formalized: `monicOrthoC_duhamel` supplies the
  identity, `norm_weightedSum_le` bounds both Duhamel sums, and `gcongr` does the monotone
  bookkeeping through the `calc`. Exit code 0, zero warnings, axiom-clean, zero placeholders, file
  347 lines.

  One recurring pitfall worth noting: `simp` rewrites `monicOrtho s 0` to `1` via the `@[simp]`
  lemma `monicOrtho_zero`, which silently breaks any hypothesis phrased in terms of
  `momentInner s (monicOrtho s 0) (monicOrtho s 0)`. The fix used here is to prove the auxiliary
  fact for an abstract scalar (`forall c, 0 < c -> ||(c : C)|| = c`) so `simp` cannot reach inside.
  Card remains Stage 2.
- 2026-07-19 -- Twenty-fourth link: kernel-root infrastructure. `kernelRoot_mono` (monotone in `n`,
  needed repeatedly by the absorption argument), `kernelRoot_sq`, and crucially
  `kernelRoot_sq_eq_normSq_sum` bridging `||.||^2` to `Complex.normSq`, so
  `summable_of_kernelRoot_le` converts a uniform kernel-root bound -- exactly what absorption
  produces -- into the `Summable` statement of the criterion. Exit code 0, zero warnings, all four
  endpoints axiom-clean, zero placeholders, file 397 lines.

  Two toolchain notes worth keeping. `Complex.sq_abs` does **not** exist here; the lemma
  `||z||^2 = normSq z` is `Complex.sq_norm`, found by grepping the mathlib source rather than by
  guessing (unknown names inside a `first | ...` alternation are hard elaboration errors, not failed
  branches, so guessing is doubly expensive). And `Finset.range_subset.mpr` did not elaborate against
  `Finset.sum_le_sum_of_subset_of_nonneg` here; an explicit `intro x hx` subset proof is reliable.
  Card remains Stage 2.
- 2026-07-19 -- Twenty-fifth link: the two estimates that precede summation.
  `norm_monicOrthoC_duhamel_le_of_le` freezes all three kernel roots at the top level `N` (legitimate
  by `kernelRoot_mono`), and `normSq_monicOrthoC_duhamel_le` squares it into

  `|Q_n(w)|^2 <= 2|Q_n(z)|^2 + 4 D^2 K_N^2 (|Q_n(z)|^2 P_N^2 + |R_n(z)|^2 S_N^2)`,

  with `D = |w-z| h_0`. Squaring goes through `(a+b)^2 <= 2a^2+2b^2` applied twice, each step a
  small `nlinarith` with an explicit `sq_nonneg` hint rather than one large opaque call. This is the
  exact termwise bound that survives division by `h_n` and summation over `n <= N`. Exit code 0,
  zero warnings, both endpoints axiom-clean, zero placeholders, file 461 lines.

  Toolchain note: `positivity` cannot see through the `kernelRoot` definition (a `noncomputable def`
  wrapping `Real.sqrt`), so `gcongr`'s nonnegativity side goals must be discharged with explicit
  `kernelRoot_nonneg` branches. Card remains Stage 2.
- 2026-07-19 -- Twenty-sixth link: `kernelRoot_sq_le_absorption`. Dividing the squared pointwise
  estimate by `h_n` and summing over `n <= N` yields the self-referential bound

  `K_N^2 <= 2 S_N^2 + 8 D^2 K_N^2 S_N^2 P_N^2`,   `D = |w-z| h_0`,

  with `K, S, P` the kernel roots of `Q(.,w)`, `Q(.,z)`, `R(.,z)`. This is exactly the inequality the
  paper derivation predicted three turns ago. Structured as a determinate `calc` (an earlier
  `le_trans ?_ (le_of_eq ?_)` left an undetermined metavariable), with the termwise division by
  `gcongr` and the three sums recombined by `Finset.mul_sum` and `kernelRoot_sq`. Exit code 0, zero
  warnings, axiom-clean, zero placeholders, file 531 lines.

  Small note: the two `Q(.,z)` sums are syntactically identical, so `rw [<- kernelRoot_sq h]`
  rewrites both at once -- two rewrites suffice for three sums, and a third fails with "did not find
  an occurrence". Card remains Stage 2.
- 2026-07-19 -- Twenty-seventh link: `summable_kernel_transfer`, the absorption step and the local
  form of the convergence transfer. Given uniform bounds `S` and `P` on the kernel roots of
  `Q(.,z)` and `R(.,z)`, and `w` close enough that
  `8 (|w-z| h_0)^2 S^2 P^2 <= 1/2`, the self-referential term in `kernelRoot_sq_le_absorption`
  absorbs into the left-hand side, giving `K_N <= 2S` uniformly in `N` and hence, via
  `summable_of_kernelRoot_le`, genuine `Summable` at `w`. Compiled first try. Exit code 0, zero
  warnings, axiom-clean, zero placeholders, file 578 lines.

  This is the local transfer. Two things still separate it from the classical statement
  "indeterminate at one point implies convergence everywhere":
  (i) a covering/iteration argument, since one application only reaches a disc around `z` whose
      radius depends on `S` and `P`;
  (ii) the `R`-side hypothesis `hP`. The bound on the second-kind kernel root is genuinely needed --
      `P_N` appears in the absorption inequality and cannot be dropped. Classically the two series
      converge together, but that equivalence is a separate theorem not yet built here.
  Card remains Stage 2.
- 2026-07-19 -- Twenty-eighth link: `transferRadius s S P = 1/(4 h_0 S P)` with
  `transferRadius_pos`, and `summable_kernel_transfer_of_dist` which discharges the smallness
  hypothesis of the previous link from a plain distance bound. The arithmetic is exactly
  `8 (r h_0)^2 S^2 P^2 = 8/16 = 1/2` at `r = 1/(4 h_0 S P)`, so the disc is the largest the
  absorption argument allows. Exit code 0, zero warnings, both endpoints axiom-clean, zero
  placeholders, file 618 lines.

  The transfer is now in the shape a covering argument consumes: a *positive* radius depending only
  on the two kernel-root bounds at the centre. The remaining obstruction to iterating is that the
  radius depends on `S` and `P` at the new centre, so a naive chain can shrink to zero; the
  classical fix is local uniform boundedness on compacts. Together with the still-open `R`-side
  bound these are the two items between here and the unconditional statement. Card remains Stage 2.
- 2026-07-19 -- Twenty-ninth link: `secondKindChristoffelDarbouxC`, the R/R identity over `C`,
  mirroring the real `secondKindChristoffelDarboux`. As over `R` the `n = 0` boundary term vanishes
  (`R_0 = 0`), so unlike the mixed identity no constant survives. Compiled first try. Exit code 0,
  zero warnings, axiom-clean, zero placeholders, file 643 lines.

  All three bilinear identities now exist at complex points (`christoffelDarbouxC`,
  `mixedChristoffelDarbouxC`, `secondKindChristoffelDarbouxC`), which is what an `R`-side Duhamel
  comparison needs: the derivation that produced `monicOrthoC_duhamel` used the Q/Q and Q/R
  identities plus the Wronskian, and its `R`-side analogue will use the R/Q and R/R ones. Closing
  that gap would turn the `hP` hypothesis of `summable_kernel_transfer` from an input into a
  consequence. Card remains Stage 2.
- 2026-07-19 -- Thirtieth link: `secondKindC_duhamel`, the second-kind Duhamel comparison. Derived
  on paper first and it came out with the *same* shape as the first-kind formula:

  `R_n(w) = R_n(z) - (w-z) h_0 [ Q_n(z) T'_n - R_n(z) S'_n ]`,
  `T'_n = sum R_j(w) R_j(z)/h_j`,  `S'_n = sum Q_j(z) R_j(w)/h_j`.

  The Q/Q and Q/R identities are replaced by the R/R (`secondKindChristoffelDarbouxC`) and R/Q
  (`mixedChristoffelDarbouxC` with arguments swapped) ones; expanding, the two `Q_n(z) R_n(z)
  R_{n+1}(w)` cross terms cancel identically and the constant Wronskian collapses the remainder to
  `-R_n(w)`. Verified by hand expansion before formalizing, which is why it compiled first try.
  Exit code 0, zero warnings, axiom-clean, zero placeholders, file 742 lines.

  Note the sign asymmetry: because the R/Q identity is used with arguments swapped, the second term
  enters with `(z-w)` rather than `(w-z)`, so the numerator identity is a *sum* rather than a
  difference. Card remains Stage 2.
- 2026-07-19 -- Thirty-first link: `norm_secondKindC_duhamel_le`, the pointwise Duhamel estimate for
  the second-kind family. Direct mirror of `norm_monicOrthoC_duhamel_le`: `norm_weightedSum_le`
  applied to the pairs (R(.,w), R(.,z)) and (Q(.,z), R(.,w)) bounds the two Duhamel sums, and the
  second-kind kernel root `kappa_R(w)` factors out of both -- the same structural feature that made
  the first-kind estimate absorbable. Compiled first try. Exit code 0, zero warnings, axiom-clean,
  zero placeholders, file 820 lines.

  The remaining `R`-side steps (freeze at level `N`, square, divide by `h_n`, sum, absorb) are
  literal mirrors of links twenty-five to twenty-seven, since that machinery
  (`kernelRoot_mono`, `kernelRoot_sq`, `summable_of_kernelRoot_le`) is generic in the families
  involved. Card remains Stage 2.
- 2026-07-19 -- Thirty-second link: the second-kind absorption chain, three lemmas, all first try.
  `norm_secondKindC_duhamel_le_of_le` freezes the kernel roots at level `N`,
  `normSq_secondKindC_duhamel_le` squares, and `kernelRootR_sq_le_absorption` divides by `h_n` and
  sums to give

  `kappa_R(w)_N^2 <= 2 kappa_R(z)_N^2 + 8 D^2 kappa_R(w)_N^2 kappa_Q(z)_N^2 kappa_R(z)_N^2`.

  The key structural observation, verified on paper first: the bracket in the second-kind pointwise
  estimate is *identical* to the first-kind one (`|Q_n(z)| kappa_R(z) + |R_n(z)| kappa_Q(z)`), so
  the summed inequality carries the same coefficient `8 D^2 S^2 P^2` and therefore the *same*
  smallness threshold. Both families transfer on the same disc. Exit code 0, zero warnings, all
  three endpoints axiom-clean, zero placeholders, file 950 lines.

  Three first-try compiles in one turn because the `gcongr` discharge pattern
  (explicit `kernelRoot_nonneg` branches, `positivity` cannot see through the definition) was
  applied pre-emptively from the note recorded at link twenty-five. Card remains Stage 2.
- 2026-07-19 -- Thirty-third link: `kernelRootQ_le_of_small`, `kernelRootR_le_of_small`, and their
  packaging `kernelRoot_bounds_propagate`. On the transfer disc *both* kernel roots at the new
  centre are bounded by twice the old bounds, under the same smallness condition. So the hypotheses
  of the transfer regenerate at `w`: the `hP` input is no longer a dead end but is reproduced along
  with `hS`. Compiled first try. Exit code 0, zero warnings, all three endpoints axiom-clean, zero
  placeholders, file 1036 lines.

  This closes the structural half of the `hP` gap flagged at link twenty-seven. What remains is the
  iteration itself, and the geometry is now explicit: each step doubles `S` and `P`, so the radius
  `1/(4 h_0 S P)` shrinks by a factor of `4` per step. A naive chain therefore has geometrically
  shrinking steps and covers only a bounded region -- the classical fix is to bound `S` and `P`
  locally uniformly rather than to iterate the crude doubling. That is the honest remaining
  obstacle, and it is an analytic argument rather than bookkeeping.

  Note also that `HTGeometry/ComplexSecondKind.lean` is now 1036 lines, above the project's
  1500-line guidance but approaching it; a split by proof phase (identities / estimates /
  transfer) is worth doing before it grows further. Card remains Stage 2.
- 2026-07-19 -- Thirty-fourth link: `BoundedKernel s z` (both kernel roots bounded at `z`, with
  positive bounds), `summable_of_boundedKernel` connecting it to the criterion, and
  `isOpen_boundedKernel` -- **the good set is open**. Proof: the transfer disc has positive radius
  (`transferRadius_pos`) and both bounds regenerate on it (`kernelRoot_bounds_propagate`), merely
  doubled. `transferSmall_of_dist` was factored out of the earlier disc lemma to be reusable.
  Compiled first try. Exit code 0, zero warnings, all three endpoints axiom-clean, zero
  placeholders, file 1093 lines.

  This is the correct honest formulation of what the transfer machinery yields globally, and it
  replaces the disc-chaining plan, which was a dead end: doubling the bounds shrinks the radius by
  `4` per step, so a chain covers only a bounded region. Openness is the real content of the local
  argument.

  The remaining half is that the good set is also **closed** -- then, being nonempty (at any point
  where the moment problem is indeterminate) and clopen in the connected space `C`, it is all of
  `C`. Closedness is the genuinely analytic step and is not a consequence of anything built so far;
  classically it comes from local uniform convergence and a normal-families/Vitali argument. Card
  remains Stage 2.
- 2026-07-19 -- Thirty-fifth link: new module `HTGeometry/ComplexKernelTransfer.lean` (started
  fresh rather than growing `ComplexSecondKind.lean` past its 1093 lines).
  `boundedKernel_of_isClosed` runs the clopen argument -- open (proved) plus closed (hypothesis)
  plus nonempty, in the connected space `C`, gives every point -- and
  `summable_kernel_everywhere_of_isClosed` draws the summability conclusion. Compiled first try;
  both endpoints axiom-clean, zero placeholders.

  The point of stating this separately is to make the remaining dependency *explicit and named*:
  closedness of `{z | BoundedKernel s z}` appears as a hypothesis of a theorem, not as an
  assumption hidden inside a definition. Everything in the module is unconditional Lean.

  Why the local machinery cannot supply closedness, recorded so it is not re-attempted: the
  propagated bounds double at each application while the transfer radius `1/(4 h_0 S P)` shrinks by
  a factor of four, so iterating the local statement never reaches a limit point with control.
  Classically closedness comes from local uniform convergence plus a normal-families/Vitali
  argument -- a genuinely different technique from anything in the thirty-four preceding links.
  Card remains Stage 2.
- 2026-07-19 -- Thirty-sixth link: `HTGeometry/NevanlinnaPluecker.lean`. Returning to the
  `AD - BC = 1` gate abandoned at link thirteen, and this time the algebra was carried through by
  hand before formalizing. Writing `P,P',S,S'` for `Q_n(0), Q_{n+1}(0), R_n(0), R_{n+1}(0)` and
  `p,p',r,r'` for the same at `z`, the four bilinear Christoffel--Darboux sums composing `A,B,C,D`
  combine into

  `(S'r - Sr')(P'p - Pp') + (p'S - pS')(P'r - Pr') = 1`

  whenever both pairs have common Wronskian `-1`. `wronskian_bilinear_factor` proves the mechanism:
  the left side is identically `(p'r - pr')(SP' - S'P)`, a *product of the two Wronskians*, with all
  eight mixed terms cancelling in pairs -- verified by full expansion on paper (terms 1+7 and 4+6
  cancel; 2+8 and 3+5 regroup). `wronskian_pluecker` and `wronskian_pluecker_sq` then substitute.
  Stated over an arbitrary `CommRing`, so the combinatorics is isolated from the analysis; the
  endpoints need only `propext` and `Quot.sound`, not even `Classical.choice`.

  This settles why link thirteen failed: the identity is genuine, but it needs the *orthonormal*
  normalisation where both Wronskians equal `-1`. In the monic normalisation the weights `1/h_k`
  break the cancellation, which is exactly the mismatch observed then. Card remains Stage 2.
- 2026-07-19 -- Thirty-seventh link: `nevanlinna_determinant_precursor`. Substituting the four
  Christoffel--Darboux identities at `(0, z)` into the Pluecker relation gives

  `h_0 z^2 (alpha delta - beta gamma) = z (beta - gamma)`

  for the four bilinear sums `alpha, beta, gamma, delta`. Both Wronskian hypotheses come from
  `monicOrthoC_wronskian` at `0` and at `z` with the *same* value `-(h_n/h_0)`, so
  `wronskian_pluecker_sq` applies directly in monic variables -- no orthonormal rescaling needed
  after all. This is precisely the relation that turns `A D - B C` into `1`, since
  `A D - B C = 1 + z(gamma - beta) + z^2(alpha delta - beta gamma)`.
  Exit code 0, zero warnings, axiom-clean, zero placeholders, file 145 lines.

  Process note: this took four checks, three of them spent guessing `linear_combination`
  coefficients. Two diagnoses worth keeping. First, `field_simp at ... ⊢` mangled the goal by trying
  to clear the `1/h_k` *inside* the Finset sums; restricting it to the hypothesis fixed that.
  Second, the reliable pattern is to make every coefficient `1` by construction: use
  `refine mul_left_cancel₀ hne ?_` to multiply the goal by the exact factor that the hypothesis
  carries, rather than trying to divide the hypothesis down to the goal. Card remains Stage 2.
- 2026-07-19 -- Thirty-eighth link: `nevA`, `nevB`, `nevC`, `nevD` and
  `nevA_mul_nevD_sub_nevB_mul_nevC` -- **the determinant identity `A_n D_n - B_n C_n = 1`**, exact
  at every truncation level, every complex `z`, and for an arbitrary positive definite moment
  sequence. Compiled first try.

  The scaling was solved analytically rather than guessed. Writing the entries as
  `A = a z alpha, B = -b + c z beta, C = d + e z gamma, D = f z delta` and imposing
  `AD - BC = 1` against the precursor forces `bd = 1`, `af = ce = k`, `cd = be = k/h_0`, hence
  `k = h_0^2`; taking `b = d = 1` gives `a = c = e = f = h_0`. With that scaling the identity holds
  for *any* `h_0`, not only a normalised sequence, and the `linear_combination` coefficient is
  exactly `h_0`. Exit code 0, zero warnings, axiom-clean, zero placeholders, file 182 lines.

  This discharges the finite half of the card's `AD - BC = 1` gate. What remains on that gate is the
  passage to the limit `n -> infinity`, which needs the convergence supplied by the transfer -- so
  the two open threads (this limit, and closedness of the good set) are the same dependency viewed
  from two directions. Card remains Stage 2.
- 2026-07-19 -- Thirty-ninth link: `sum_range_norm_weighted_le` and
  `summable_weighted_of_bounds`. Bounded kernel roots make each of the four bilinear series
  *absolutely* summable: Cauchy--Schwarz bounds every partial sum of norms by
  `kernelRoot f n * kernelRoot g n <= Kf * Kg`, and `Summable.of_norm` with
  `summable_of_sum_range_le` converts that into `Summable`. Compiled first try. Exit code 0, zero
  warnings, both endpoints axiom-clean, zero placeholders, file 235 lines.

  This is the convergence input the limit passage needs: given `BoundedKernel` at `0` and at `z`,
  all four series defining `A_n, B_n, C_n, D_n` converge, so the truncated matrix has a limit and
  the exact identity `A_n D_n - B_n C_n = 1` can be transported to it. Card remains Stage 2.
- 2026-07-19 -- Fortieth link: `nevAinf, nevBinf, nevCinf, nevDinf` and
  `nevAinf_mul_nevDinf_sub_nevBinf_mul_nevCinf` -- **`A D - B C = 1` for the limiting Nevanlinna
  matrix**, given `BoundedKernel` at `0` and at `z`. The four series converge by
  `summable_weighted_of_bounds`; the truncations converge to the tsums
  (`tendsto_partial_succ`, a shift of `HasSum.tendsto_sum_nat`); the identity holds at every `n`; so
  uniqueness of limits transports it. Exit code 0, zero warnings, axiom-clean, zero placeholders,
  file 302 lines.

  The determinant gate is now discharged at the level of *functions*: `AD - BC = 1` holds for the
  limiting entries wherever the kernel is bounded. What is still missing from that gate is the
  qualitative statement that `A,B,C,D` are **entire of minimal exponential type** -- analyticity in
  `z` and a growth bound, neither of which follows from the algebra. Analyticity would come from
  local uniform convergence (the same input as closedness); the growth order is a further classical
  estimate. Card remains Stage 2.
- 2026-07-19 -- Forty-first link: `weightedSum_sq_le_finset` and `norm_sum_weighted_le_finset`,
  Cauchy--Schwarz for the moment weights over an *arbitrary* `Finset` rather than only
  `Finset.range (n+1)`. Compiled first try. Exit code 0, zero warnings, both endpoints axiom-clean,
  zero placeholders, file 372 lines.

  These are the tail estimates behind local uniform convergence, and there is now a concrete route
  to it. On a transfer disc `kernelRoot_bounds_propagate` bounds the partial sums *uniformly in both
  the point `w` and the level `N`* (by `2S` and `2P`). Applying the new bound with
  `t = Finset.Ico N M` gives

  `|sum_{k=N}^{M} Q_k(0) Q_k(z) / h_k| <= sqrt(tail_N at 0) * 2S`

  with the second factor independent of `z` on the disc and the first tending to `0` because the
  series at `0` converges. That is a uniform Cauchy criterion, hence uniform convergence on the
  disc, hence analyticity of the limiting `A,B,C,D` there as uniform limits of polynomials.

  So analyticity is reachable with the machinery now in place; the exponential-type growth bound is
  a separate classical estimate and remains open, as does closedness. Card remains Stage 2.
- 2026-07-19 -- Forty-second link: `sqrt_sum_Ico_le` and `norm_sum_Ico_weighted_le`. A tail of a
  bilinear moment series over `Finset.Ico N M` is bounded by

  `sqrt( sum_{Ico N M} |f_k|^2 / h_k ) * K_g`

  where `K_g` is any bound on the second kernel root. `sqrt_sum_Ico_le` is the step that makes the
  second factor uniform: `Ico N M` sits inside `range M`, so the partial sum is at most
  `kernelRoot g (M-1)^2 <= K_g^2`. Compiled first try. Exit code 0, zero warnings, both endpoints
  axiom-clean, zero placeholders, file 418 lines.

  This is the *uniform in the point* half of the Cauchy criterion: on a transfer disc
  `kernelRoot_bounds_propagate` supplies a single `K_g = 2S` valid at every point of the disc, so
  the only varying factor is the tail of the series at the fixed centre. The remaining half is the
  standard fact that that tail tends to zero, which is `Summable` machinery rather than
  moment-problem content. Card remains Stage 2.
- 2026-07-19 -- Forty-third link: the uniform Cauchy criterion completed.
  `sum_Ico_le_tsum_sub_range` bounds an `Ico N M` block by the tail `tsum - sum_{range N}` (splitting
  via `Finset.sum_Ico_consecutive`, with the degenerate `M < N` case handled separately);
  `norm_sum_Ico_weighted_le_tail` combines it with the previous link to bound every bilinear tail by
  `sqrt(tail_N) * K_g`; and `tendsto_uniformCauchyBound_zero` shows that bound tends to `0`.

  The bound depends on **neither** the upper index `M` **nor** the point at which the second family
  is taken, beyond the single constant `K_g` -- which on a transfer disc is `2S`, the same for every
  point. That is exactly uniform Cauchy convergence of the four Nevanlinna series on the disc, hence
  uniform convergence, hence analyticity of the limits as uniform limits of polynomials.

  Exit code 0, zero warnings, all three endpoints axiom-clean, zero placeholders, file 493 lines.
  Toolchain note: `le_or_lt` does not exist here; `Nat.lt_or_ge` is the replacement. Card remains
  Stage 2.
- 2026-07-19 -- Forty-fourth link: `uniformCauchy_weighted`. For every `eps > 0` there is a single
  threshold `N_0` such that for all `N >= N_0`, **all** upper indices `M`, and **all** families `g`
  obeying `kernelRoot s g n <= Kg`, the tail satisfies
  `|sum_{Ico N M} f_k g_k / h_k| < eps`. Quantifying over `g` inside the statement is what makes the
  uniformity explicit: on a transfer disc `kernelRoot_bounds_propagate` supplies one `Kg = 2S` valid
  at every point, so a single `N_0` serves the whole disc. Compiled first try. Exit code 0, zero
  warnings, axiom-clean, zero placeholders, file 513 lines.

  Local uniform convergence of the four Nevanlinna series is now assembled entirely from proved
  pieces. What remains for analyticity is to transcribe this into mathlib's `TendstoUniformlyOn`
  and apply its holomorphic-limit theorem -- API plumbing over settled estimates rather than new
  mathematics. The exponential-type growth bound and closedness of the good set remain the two
  genuinely open classical inputs. Card remains Stage 2.
- 2026-07-19 -- Forty-fifth link: `bilinearPartialSum` and
  `uniformCauchySeqOn_bilinearPartialSum`, repackaging the previous link as mathlib's
  `UniformCauchySeqOn` on any set of points sharing a kernel-root bound. The proof goes through
  `Metric.uniformCauchySeqOn_iff` and `Finset.sum_Ico_eq_sub`, with the two orderings of the indices
  handled by `le_total` and `norm_neg`. Compiled first try. Exit code 0, zero warnings,
  axiom-clean, zero placeholders, file 547 lines.

  The relevant mathlib API was located by reading
  `Mathlib/Analysis/Complex/LocallyUniformLimit.lean` rather than guessing names: the target is
  `TendstoLocallyUniformlyOn.differentiableOn (hf) (hF : eventually DifferentiableOn) (hU : IsOpen)`,
  reached from `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto`. With the partial sums being
  polynomials in `z` (hence differentiable) and pointwise convergence available from summability,
  the remaining chain is three API steps. Card remains Stage 2.
- 2026-07-19 -- Forty-sixth link: `summable_normSq_of_kernelRoot_le` and
  **`differentiableOn_bilinearLimit`** -- the limiting bilinear series is holomorphic on any open set
  carrying a common kernel-root bound. The chain
  `uniformCauchySeqOn_bilinearPartialSum` -> `.tendstoUniformlyOn_of_tendsto` (pointwise limits from
  summability) -> `.tendstoLocallyUniformlyOn` -> `TendstoLocallyUniformlyOn.differentiableOn`
  went through first try, having read the signatures out of
  `Mathlib/Analysis/Complex/LocallyUniformLimit.lean` last turn instead of guessing them.
  Differentiability of the partial sums is a hypothesis, since `G` is an abstract family; in the
  application `G z k = monicOrthoC s k z` is polynomial in `z`. Exit code 0, zero warnings, both
  endpoints axiom-clean, zero placeholders, file 591 lines.

  This closes the *analyticity* half of the entire-function gate. `A, B, C, D` are holomorphic
  wherever the kernel is uniformly bounded -- in particular on every transfer disc, by
  `kernelRoot_bounds_propagate`. What remains of that gate is the growth statement (minimal
  exponential type), and separately closedness of the good set. Card remains Stage 2.
- 2026-07-19 -- Forty-seventh link: holomorphy transferred to the actual Nevanlinna entries.
  `differentiable_monicOrthoC` and `differentiable_secondKindC` identify the complex evaluations
  with `Polynomial.eval` of the mapped polynomial (`Polynomial.aeval_def`,
  `Polynomial.eval₂_eq_eval_map`), hence differentiable; `differentiableOn_bilinearPartialSum`
  lifts that to the partial sums; and `differentiableOn_nevA_series`, `nevC`, `nevD` apply the
  general theorem. Exit code 0, zero warnings, all six endpoints axiom-clean, zero placeholders,
  file 669 lines.

  Two Lean-shape notes. `Differentiable.sum` could not infer the field from the goal alone; supplying
  the termwise hypothesis as a named `have` first pins it. And it concludes about
  `∑ i, (fun z => ...)` (a sum *of functions*) whereas the goal is `fun z => ∑ i, ...`; a `funext`
  plus `simp` bridge (`Finset.sum_apply`) converts between them.

  So `A`, `C`, `D` are holomorphic on any open set carrying uniform kernel bounds -- in particular
  every transfer disc. `B` follows identically from `mixed` data. What remains of the entire-function
  gate is purely the growth statement. Card remains Stage 2.
- 2026-07-19 -- Forty-eighth link: `differentiableOn_nevB_series` (its summand carries the
  point-dependent factor first, so the product is commuted under the `tsum` before applying the
  general theorem) and the capstone **`nevanlinna_holomorphic_unimodular`**: on any open `U`
  carrying uniform kernel bounds, with the kernel bounded at `0` and at every point of `U`, all four
  limiting entries `nevAinf..nevDinf` are `DifferentiableOn C` and satisfy `A D - B C = 1`
  throughout `U`. Compiled first try. Exit code 0, zero warnings, both endpoints axiom-clean, zero
  placeholders, file 719 lines.

  This is the analytic content of the Nevanlinna matrix assembled in one statement, and by
  `kernelRoot_bounds_propagate` its hypotheses are met on every transfer disc. What is still absent
  from the card's entire-function gate is only the *growth* claim (minimal exponential type), which
  is a genuinely different estimate: it bounds `|A(z)|` etc. in terms of `exp(eps |z|)` and does not
  follow from holomorphy plus the determinant identity. Closedness of the good set, the N-extremal
  leaves, and discharging `ClassicalNevanlinnaExtremalFamily` also remain. Card remains Stage 2.
- 2026-07-19 -- Forty-ninth link: `norm_tsum_weighted_le` (a `tsum` Cauchy--Schwarz bound: the
  infinite bilinear series is bounded by the product of the two kernel-root bounds) and the entry
  bounds `norm_nevAinf_le`, `norm_nevDinf_le`:

  `|A(z)| <= h_0 |z| * P_0 * P_z`,   `|D(z)| <= h_0 |z| * S_0 * S_z`.

  Exit code 0, zero warnings, all three endpoints axiom-clean, zero placeholders, file 788 lines.

  This isolates the remaining unknown for the exponential-type claim. Each entry's growth in `z` is
  the product of an elementary factor `h_0 |z|` and the kernel root at `z`; so "minimal exponential
  type" reduces exactly to showing `kernelRoot s (Q(.,z)) n <= C exp(eps |z|)` for every `eps`,
  uniformly in `n`. Nothing in the algebra supplies that -- it is the classical growth estimate for
  orthonormal polynomials of an indeterminate problem, and remains genuinely open here.

  Toolchain note: `tsum_le_of_sum_range_le` does not exist in this toolchain; bounding a `tsum` by
  bounding its partial sums is done with `le_of_tendsto` applied to `Summable.hasSum.tendsto_sum_nat`.
  Card remains Stage 2.
- 2026-07-19 -- Fiftieth link: the derivation transferred to the *real* variable and wired into the
  project's own interface. `nevanlinna_determinant_precursor_real` repeats the Pluecker argument
  using the three real Christoffel--Darboux identities (`wronskian_pluecker_sq` is stated for an
  arbitrary `CommRing`, so it applies unchanged); `nevAreal..nevDreal` are the real entries; and
  `nevAreal_mul_nevDreal_sub_nevBreal_mul_nevCreal` is exactly the `det_one` field of
  `ClassicalNevanlinnaMatrixData R`.

  **`nevMatrixData` constructs that structure** from an arbitrary positive definite moment sequence,
  with no assumptions beyond positive definiteness. One of the two packaged inputs the card was
  blocked on is therefore no longer packaged: the matrix data is now built, not assumed. Exit code
  0, zero warnings, all three endpoints axiom-clean, zero placeholders, file 922 lines.

  Scope note: `nevMatrixData` is built from the level-`n` truncation, which genuinely inhabits the
  interface (the determinant identity is exact at every `n`). The *classical* Nevanlinna matrix is
  the `n -> infinity` limit, whose entries are the holomorphic `nevAinf..nevDinf` of link
  forty-eight; wiring those in needs the limit of the real entries, i.e. the same convergence
  hypotheses. What remains of `ClassicalNevanlinnaExtremalFamily` is the analytic and
  measure-theoretic part -- continuity of the denominator row, the weakly continuous leaf family of
  probability measures, their carrier conditions, and the moment identities -- none of which is
  started. Card remains Stage 2.
- 2026-07-19 -- Fifty-first link: continuity of all four real entries
  (`continuous_nevAreal` .. `continuous_nevDreal`), and in particular
  `continuous_nevMatrixData_B` and `continuous_nevMatrixData_D` -- the `continuous_B` and
  `continuous_D` fields of `ClassicalNevanlinnaExtremalFamily`, discharged for the truncated matrix.
  Each entry is a finite sum of polynomial evaluations against constants. Exit code 0, zero
  warnings, all six endpoints axiom-clean, zero placeholders, file 964 lines.

  Progress against the packaged structure: `matrix`, `continuous_B`, `continuous_D` are now
  constructed. The four remaining fields -- `leaf` (a weakly continuous family of probability
  measures indexed by the projective line), `finite_carried` / `infinity_carried` (each leaf carried
  by the zero set of the denominator row) and `leaf_moments` -- are the measure-theoretic core, and
  none of it is started. That construction needs the N-extremal measures themselves: discrete
  measures on the zeros of `B(x) tau - D(x)` with masses given by the Christoffel function. It is a
  substantial development in its own right. Card remains Stage 2.

  Toolchain notes: `continuous_finset_sum` is deprecated in favour of `continuous_finsetSum`, and
  `Continuous.const_add` takes the continuity proof first and the constant second.
- 2026-07-19 -- Fifty-second link: `HTGeometry/ChristoffelKernel.lean`, the first step of the
  measure-theoretic half. `cdKernel s n x` is the polynomial `y -> sum_{k<=n} Q_k(x) Q_k(y) / h_k`,
  and `momentInner_cdKernel` proves the **reproducing property**

  `<p, cdKernel s n x> = p(x)`  for every `p` of degree at most `n`,

  directly from `monicOrtho_expansion`: expanding `p` in the orthogonal basis and evaluating at `x`
  produces exactly the same sum. `cdKernel_eval_self` identifies the diagonal with the weighted
  square sum, `cdKernel_eval_self_pos` shows it is strictly positive (the `k = 0` term alone gives
  `1/h_0`), and `christoffel` is its reciprocal -- the Christoffel function, which supplies the
  masses of the Gauss/N-extremal quadrature. Exit code 0, zero warnings, all five endpoints
  axiom-clean, zero placeholders.

  Next in this direction is the harder half: that `Q_{n+1}` has `n+1` distinct real roots. The
  abstract proof is available -- if `Q_{n+1}` had fewer than `n+1` sign changes, multiplying by the
  monic polynomial through those points gives a polynomial of constant sign and degree `< n+1`,
  whose moment functional is both zero (orthogonality) and positive (a nonnegative real polynomial
  is a sum of two squares, and the form is positive definite). Formalising it needs the
  sum-of-two-squares fact for one-variable real polynomials. Card remains Stage 2.
- 2026-07-19 -- Fifty-third link: the kernel's defining structure completed. `cdKernel_eval` gives
  the explicit double sum, `cdKernel_symm` its symmetry, `cdKernel_degree_lt` the degree bound
  (which needs no positivity -- the hypothesis was dropped after the linter flagged it unused), and
  `momentInner_cdKernel_cdKernel` the **self-reproducing identity** `<K_x, K_y> = K_x(y)`, the
  hallmark of a reproducing kernel. `christoffel_eq_inv_momentInner` then identifies the Christoffel
  function with the reciprocal of the kernel's own moment norm. Exit code 0, zero warnings, all four
  endpoints axiom-clean, zero placeholders, file 123 lines.

  On the real-rootedness route: mathlib has `IsSumSq` and a `SumsOfSquares` file, but not the
  specific fact that a nonnegative one-variable *real polynomial* is a sum of two squares, which the
  abstract proof needs. So that route requires building the polynomial fact first; it is not a
  matter of finding the right lemma name. Recorded so the next session does not re-search for it.
  Card remains Stage 2.
- 2026-07-19 -- Fifty-fourth link: `momentInner_sq_le_of_posDef` -- **Cauchy--Schwarz from positive
  definiteness alone**, with no representing measure, via the discriminant of
  `t -> <p + t q, p + t q>`. This strictly generalises the existing `momentInner_sq_le`, which
  carried measure hypotheses.

  With it, `christoffel_le_momentInner_self` proves the classical **variational property**: among
  polynomials of degree at most `n` with `p(x) = 1`, the Christoffel function is a lower bound for
  `<p, p>`. `christoffel_eq_momentInner_normalisedKernel` and `normalisedKernel_eval_self` show the
  bound is attained by the normalised kernel, so the Christoffel function *is* the minimum. Exit
  code 0, zero warnings, all four endpoints axiom-clean, zero placeholders, file 176 lines.

  This is the characterisation that makes the Christoffel function the right mass for the N-extremal
  quadrature, and it is now proved from the abstract moment form -- no measure, no root structure.
  The remaining measure-theoretic construction still waits on real-rootedness of `Q_{n+1}`, which in
  turn waits on the sum-of-two-squares fact for real polynomials (absent from mathlib, so it must be
  built: factorisation over `C`, conjugate-pair root matching, even multiplicity of real roots).
  Card remains Stage 2.
- 2026-07-19 -- Fifty-fifth link: `cdKernel_posSemidef` -- the Christoffel--Darboux kernel is a
  **positive semidefinite kernel**: for any finite family of points and coefficients, the Gram sum
  `sum_{i,j} c_i c_j K(x_i, x_j)` is nonnegative, because by the self-reproducing identity it *is*
  the moment norm of the single polynomial `sum_i c_i K_{x_i}`. `cdKernel_sq_le` records the kernel
  Cauchy--Schwarz `K(x,y)^2 <= K(x,x) K(y,y)`. Compiled first try. Exit code 0, zero warnings, both
  endpoints axiom-clean, zero placeholders, file 206 lines.

  `ChristoffelKernel.lean` now carries the complete reproducing-kernel structure -- reproduction,
  symmetry, degree bound, self-reproduction, positive semidefiniteness, the Christoffel function and
  its variational characterisation -- all from the abstract positive definite moment form, with no
  measure and no root structure.

  Handoff for the two large remaining developments, neither started:
  (a) **Real-rootedness of `Q_{n+1}`.** Two viable routes. Via sum-of-two-squares: a nonnegative real
      polynomial is `f^2 + g^2` (needs factorisation over `C` and conjugate-pair matching; absent
      from mathlib). Via the Jacobi matrix: the three-term recurrence
      `Q_{n+2} = (X - a_n) Q_{n+1} - b_n Q_n` with `b_n > 0` is exactly the characteristic-polynomial
      recursion of the symmetric tridiagonal matrix with diagonal `(a_0..a_n)` and off-diagonal
      `(sqrt b_1 .. sqrt b_n)`, so real-rootedness follows from the spectral theorem for real
      symmetric matrices. The second route reuses machinery already built here and looks shorter.
  (b) **The N-extremal leaf measures**, which depend on (a).
  Card remains Stage 2.

### Link 56 — monotonicity of the Christoffel function

`formal/GaloisForLFunctions/HTGeometry/ChristoffelKernel.lean` (251 lines) gains the level-monotonicity
layer, which is what turns the Christoffel function into a *limit* object rather than a family of
unrelated finite quantities:

- `cdKernel_eval_self_succ` — the diagonal recursion
  `K_{n+1}(x,x) = K_n(x,x) + Q_{n+1}(x)^2 / h_{n+1}`; a one-term unfolding of the defining sum.
- `cdKernel_eval_self_mono` — `m ≤ n → K_m(x,x) ≤ K_n(x,x)`; every dropped summand is a square over a
  positive norm, so `Finset.sum_le_sum_of_subset_of_nonneg` applies with no cancellation to control.
- `christoffel_antitone` — `[PROVED HERE]` `m ≤ n → λ_n(x) ≤ λ_m(x)`. The Christoffel function
  decreases in the level. Proved by `gcongr` on the inverse, with positivity of `K_m(x,x)` supplied
  from `cdKernel_eval_self_pos`.
- `christoffel_le_h0` — the uniform ceiling `λ_n(x) ≤ h₀`, since the level-zero kernel diagonal is
  exactly `1/h₀`.

Together these say the sequence `n ↦ λ_n(x)` is antitone and bounded below by `0`, hence convergent
for every real `x` — with the limit bounded above by `h₀` uniformly in `x`. That limit is the
classical candidate for the mass an N-extremal measure assigns to the point `x`, so this is the piece
that will later let a leaf measure be *evaluated* rather than merely asserted to exist.

**Axioms:** all four endpoints `[propext, Classical.choice, Quot.sound]`. Zero placeholders in the
file. `christoffel_antitone` compiled after two name repairs — `inv_le_inv_of_le` is gone from this
toolchain (`gcongr` discharges the same step), and `Finset.sum_range_one` does not match `range (0+1)`
syntactically, so the level-zero evaluation needs `Finset.sum_range_succ` + `Finset.sum_range_zero`.

**Opens next:** the limit function `λ(x) = ⨅ₙ λ_n(x)` is now well-defined without any further
analytic input — it can be introduced as a `def` and its basic properties (nonnegativity, the `≤ h₀`
ceiling, antitone-limit characterisation) proved immediately. The substantive question it raises:
`λ(x) > 0` exactly at the points the N-extremal measures charge, which is the bridge from this
finite-level machinery to the leaf-measure fields still open in
`ClassicalNevanlinnaExtremalFamily`. That is a sharper target than real-rootedness of `Q_{n+1}`
and does not route through the Jacobi-matrix spectral theorem at all.

### Link 57 — the limit Christoffel function

`ChristoffelKernel.lean` (298 lines) closes the finite-level story by passing to the limit. Compiled
first try; every endpoint `[propext, Classical.choice, Quot.sound]`.

- `christoffelLimit s x := ⨅ n, christoffel s n x` — well-defined because link 56 supplies both
  hypotheses the conditional infimum needs: `antitone_christoffel` and `bddBelow_christoffel` (the
  bound is `0`, from `christoffel_pos`).
- `christoffelLimit_nonneg`, `christoffelLimit_le` (every level dominates the limit),
  `christoffelLimit_le_h0`.
- `tendsto_christoffel` — `[PROVED HERE]` the level sequence actually converges to it, via
  `tendsto_atTop_ciInf`. So `λ(x)` is a genuine limit, not merely an infimum.
- `christoffelLimit_le_momentInner_self` — `[PROVED HERE]` **the variational property survives the
  limit, and loses its degree restriction**: for *every* polynomial `p` with `p(x) = 1`,
  `λ(x) ≤ ⟪p, p⟫`. The finite-level version needs `deg p < n+1`; choosing `n := p.natDegree` makes the
  restriction vacuous, so the limit statement quantifies over all of `ℝ[X]` at once.

That last one is the point of the whole layer. It is the first statement in this development that
constrains the moment form using an *arbitrary* polynomial rather than a fixed finite section, which
is exactly the form the leaf-measure fields need: any measure `μ` with these moments and any `p` with
`p(x) = 1` satisfies `μ({x}) ≤ ∫ p² dμ = ⟪p, p⟫`, so `μ({x}) ≤ λ(x)` for every such `μ`.

**Opens next:** the reverse inequality — `λ(x)` is *attained*, i.e. some N-extremal `μ` charges `x`
with exactly `λ(x)`. Attainment is where a measure has to be produced rather than bounded, so it is
the natural place to bring in `nevMatrixData` from `NevanlinnaPluecker.lean`: the classical statement
is that `λ(x) > 0` precisely when `x` is a zero of `B(x)τ − D(x)` for the parameter `τ` indexing the
leaf. Formulating *that* equivalence — finite-level Christoffel data on one side, the entire
functions `B, D` on the other — is a sharper and more tractable next target than either the
real-rootedness of `Q_{n+1}` or the closedness of `{z | BoundedKernel s z}`, and it is the first
place the two halves of this card's Lean stack (moment/kernel side and Nevanlinna/matrix side) are
forced to meet.

### Link 58 — the Christoffel limit bounds every representing measure's atoms

New module `formal/GaloisForLFunctions/HTGeometry/ChristoffelPointMass.lean` (98 lines, zero
placeholders, registered in the `HTGeometry` umbrella). This is the join between the two halves of
the card's Lean stack: everything before it was either pure moment/kernel algebra or pure
Nevanlinna/measure interface, and nothing connected them.

Reuse before building paid off here. Searching the tree first turned up
`momentFunctional_mul_eq_integral` and `integrable_eval` already sitting in
`MomentFunctionalPositivity.lean` — the representing-measure bridge `L(pq) = ∫ p·q dμ` was written
long ago, so no new integration infrastructure was needed at all.

- `measureReal_singleton_le_momentInner` — `[PROVED HERE]` for any `p` with `p(x) = 1`,
  `μ.real {x} ≤ ⟪p, p⟫`. Mechanism: `∫_{{x}} p² dμ = μ.real {x}` exactly (`integral_singleton` plus
  the normalisation), and `p² ≥ 0` everywhere, so `setIntegral_le_integral` gives the rest.
- `measureReal_singleton_le_christoffel` — each finite level already bounds the atom, since the
  normalised kernel of link 55 is an admissible competitor (`normalisedKernel_eval_self`) that
  *attains* the Christoffel value (`christoffel_eq_momentInner_normalisedKernel`).
- `measureReal_singleton_le_christoffelLimit` — `[PROVED HERE]` `μ.real {x} ≤ λ(x)`, by `le_ciInf`.
- `measureReal_singleton_eq_zero_of_christoffelLimit_eq_zero` — `λ(x) = 0` forces every representing
  measure to be atomless at `x`.
- `leaf_measureReal_singleton_le_christoffelLimit` — `[PROVED HERE]` the bound holds for **every leaf
  of `ClassicalNevanlinnaExtremalFamily`, uniformly in the boundary parameter `t`**, since
  `leaf_moments` supplies exactly the representing-measure hypothesis.

**Axioms:** all endpoints `[propext, Classical.choice, Quot.sound]`.

**Namespace note for anyone extending this:** the moment/kernel modules live in bare `HTGeometry`,
while the Nevanlinna interface (`HasHamburgerMoments`, `ClassicalNevanlinnaMatrixData`,
`ClassicalNevanlinnaExtremalFamily`) lives in `GaloisForLFunctions.HTGeometry`. Cross-references need
full qualification; `open`-ing the second inside the first risks ambiguity.

**Opens next:** one half of the atom equivalence is now unconditional — `λ(x)` is an upper bound for
the mass. The reverse half, *attainment*, is the live target: for the leaf indexed by `τ`, the atom
at a zero `x` of `B(x)τ − D(x)` should equal `λ(x)` exactly. Attainment requires producing a measure
rather than bounding one, so the natural first step is the finite-level rehearsal: Gauss quadrature.
The measure `∑_{Q_{n+1}(ξ)=0} λ_n(ξ) δ_ξ` reproduces the moments `s_0 … s_{2n+1}` and gives each node
mass exactly `λ_n(ξ)` — the finite-level statement of precisely the equality being chased, provable
with the kernel machinery already built plus the real-rootedness of `Q_{n+1}` (link 56 handoff, Jacobi
route). That makes real-rootedness no longer a detour but the direct prerequisite of attainment.

### Link 59 — real-rootedness, via neither route in the link-56 handoff

New module `formal/GaloisForLFunctions/HTGeometry/MomentRealRootedness.lean` (144 lines, zero
placeholders, registered in the umbrella). All endpoints `[propext, Classical.choice, Quot.sound]`.
The core theorem compiled first try.

Link 56 offered two routes and preferred the Jacobi/spectral one. **Both were unnecessary.** A search
of mathlib turned up `LinearMap.IsSymmetric.charpoly_eq_prod` (route b's engine) and confirmed no
sum-of-two-squares theorem for nonneg real polynomials (route a's engine, absent as suspected) — but
finding the first prompted the question of what the spectral theorem was actually *buying*, and the
answer was: nothing that positivity of the moment form does not already give directly.

`monicOrtho_aeval_ne_zero` — `[PROVED HERE]` for every `n` and every `z` with `Im z ≠ 0`,
`aeval z (monicOrtho s (n+1)) ≠ 0`. The argument:

1. `conjQuadratic z := (X − Re z)² + (Im z)²`, a monic *real* quadratic vanishing at `z`.
2. `conjQuadratic_dvd_of_aeval_eq_zero` — if `z` is a non-real root of any real `Q`, this quadratic
   divides `Q`. Mechanism: divide with remainder (`modByMonic_add_div`, which needs no monicity
   hypothesis); the remainder is real of degree ≤ 1 and vanishes at `z`; taking imaginary parts of
   `c₁ z + c₀ = 0` with `c₀, c₁` real and `Im z ≠ 0` forces `c₁ = 0`, then `c₀ = 0`. No conjugate-root
   theorem, no irreducibility, no factorisation is invoked.
3. Applied to `Q = monicOrtho s (n+1)`: the quotient `g` satisfies `natDegree Q = 2 + natDegree g`, so
   `deg g < n+1` and `⟪Q, g⟫ = 0` by orthogonality. (The `n = 0` case needs no separate treatment —
   `1 = 2 + k` is already impossible, and `omega` closes it.)
4. But `Q·g = ((X − Re z)g)² + (Im z)²g²` **as a polynomial identity, closed by `ring`**, so
   `⟪Q, g⟫ = ⟪(X − Re z)g, (X − Re z)g⟫ + (Im z)²⟪g, g⟫ ≥ (Im z)²⟪g, g⟫ > 0` since `g ≠ 0`.
5. Zero and positive: contradiction.

`monicOrtho_root_im_eq_zero` restates it as: every complex root of `monicOrtho s (n+1)` is real.

**What made it cheap:** the sum-of-two-squares decomposition that route (a) needed *in general* is
needed here only for the single polynomial `Q·g`, where it is visible by inspection and provable by
`ring`. Generality was the entire cost. Worth remembering as a pattern — a missing general theorem is
not always a blocker when only one instance of it is ever used.

**Opens next:** `Splits (RingHom.id ℝ) (monicOrtho s (n+1))`. The reusable general lemma is
`splits_of_forall_root_im_eq_zero`: a real polynomial whose complex roots are all real splits over
`ℝ`, by strong induction on `natDegree` — extract a complex root (ℂ algebraically closed), it is real
by hypothesis, factor out `X − C a`, recurse. That is a clean statement of independent value and is
the last step before Gauss quadrature: nodes are the roots of `Q_{n+1}`, weights are `λ_n(ξ)`, and
link 58 already proves the weight bound the quadrature measure must satisfy.

### Link 60 — splitting over ℝ

`MomentRealRootedness.lean` now 209 lines, zero placeholders. Both new endpoints
`[propext, Classical.choice, Quot.sound]`; compiled first try.

- `splits_of_forall_aeval_im_eq_zero` — `[PROVED HERE]` **a real polynomial all of whose complex
  roots are real splits over `ℝ`**. Stated with an explicit degree bound `N` and proved by induction
  on it: a nonconstant polynomial has a complex root (`Complex.exists_root`), the root is real by
  hypothesis, `X − C a` divides, and the quotient inherits the hypothesis since its roots are roots
  of the original. This is a general-purpose lemma with no moment content — it belongs to anyone who
  needs it.
- `monicOrtho_splits` — `[PROVED HERE]` `(monicOrtho s (n+1)).Splits`, by feeding link 59 into the
  above with `N := natDegree`.

**Toolchain note worth recording:** `Polynomial.Splits` in this mathlib takes **no ring hom** — it is
the one-argument predicate `Splits (f : R[X]) : Prop`, saying `f` lies in the submonoid generated by
constants and monic linears. Every recalled signature of the form `Splits (RingHom.id ℝ) p` is wrong
here, as are `splits_mul` (now `Splits.mul`) and `splits_X_sub_C` (now `Splits.X_sub_C`). The
induction step is served exactly by `splits_X_sub_C_mul_iff : Splits ((X − C a) * f) ↔ Splits f`.

**Opens next:** Gauss quadrature is now unblocked in both of its inputs. `monicOrtho_splits` gives
`Q_{n+1} = ∏_{i} (X − ξ_i)` with `n+1` real nodes, and link 58 gives the weight bound. The
construction to build: `gaussMeasure s n := ∑_i λ_n(ξ_i) δ_{ξ_i}`, with the theorem that it
reproduces `s_0 … s_{2n+1}`. The proof is the classical one and every ingredient is now in the tree —
the reproducing property of `cdKernel` (link 55) evaluates any polynomial of degree ≤ n at a node,
and division by `Q_{n+1}` reduces degree `≤ 2n+1` to that case. Simplicity of the nodes, which the
weights need, follows from the Christoffel–Darboux diagonal `∑_k Q_k(ξ)²/h_k > 0` already proved.

### Link 61 — the Gauss nodes: exactly `n+1`, all distinct

New module `formal/GaloisForLFunctions/HTGeometry/GaussQuadratureNodes.lean` (94 lines, zero
placeholders, registered in the umbrella). All endpoints `[propext, Classical.choice, Quot.sound]`.

The link-60 handoff expected node simplicity to come from the Christoffel--Darboux diagonal, which
would have required the *confluent* form of the identity — a derivative expression this tree does not
have. It is not needed. Simplicity is the link-59 trick again, with the irreducible quadratic replaced
by a repeated real factor:

- `monicOrtho_not_sq_dvd` — `[PROVED HERE]` `(X − r)²` never divides `monicOrtho s (n+1)`. If it did,
  the quotient `g` would have degree `n−1`, so `⟪Q, g⟫ = 0`; but `Q g = ((X − r) g)²` **by `ring`**,
  so `⟪Q, g⟫ > 0`. Three sentences, no derivatives, no Christoffel--Darboux.
- `monicOrtho_rootMultiplicity_le_one`, `monicOrtho_roots_nodup` — every root simple, roots multiset
  has no duplicates.
- `monicOrtho_roots_card` — counted with multiplicity there are exactly `n+1` roots, from
  `Splits.natDegree_eq_card_roots` (link 60) and `monicOrtho_degree`.
- `gaussNodes s n := (monicOrtho s (n+1)).roots.toFinset`, with `mem_gaussNodes_iff` and
  `gaussNodes_card` — `[PROVED HERE]` **`#(gaussNodes s n) = n + 1`**.

That is now the third distinct use of one pattern: pair `Q` against a quotient of itself whose degree
orthogonality kills, then observe the product is a perfect square (or a sum of two) that positivity
makes strictly positive. It has now delivered no-non-real-roots, splitting, and simplicity. Worth
naming as the workhorse of this development rather than rediscovering it a fourth time.

**Opens next:** the weights. With the node set finite, distinct, and of known size, define
`gaussWeight s n ξ := christoffel s n ξ` and the discrete measure
`gaussMeasure s n := ∑_{ξ ∈ gaussNodes s n} gaussWeight s n ξ • δ_ξ`. The theorem to prove is exactness
on degree `≤ 2n+1`: `momentFunctional s p = ∑_{ξ} λ_n(ξ) · p(ξ)`. The proof splits `p = Q_{n+1} q + ρ`
with `deg q, deg ρ ≤ n`; the first term integrates to zero against the nodes (they are roots) and
pairs to zero against `Q_{n+1}` by orthogonality, and the remainder is handled by the reproducing
property of `cdKernel` from link 55. Every ingredient is in the tree; nothing further is missing.

### Link 62 — Gauss quadrature, exact on degree ≤ 2n+1

New module `formal/GaloisForLFunctions/HTGeometry/GaussQuadrature.lean` (167 lines, zero
placeholders, registered in the umbrella). All endpoints `[propext, Classical.choice, Quot.sound]`.

`momentFunctional_eq_gaussSum` — `[PROVED HERE]` for every `p` with `deg p ≤ 2n+1`,

`momentFunctional s p = ∑_{ξ ∈ gaussNodes s n} λₙ(ξ) · p(ξ)`.

This is the finite-level attainment statement the last four links were aimed at: the Christoffel
weights are not merely an upper bound for the atoms of a representing measure (link 58), they *are*
the masses of a measure that reproduces the moments up to order `2n+1`.

Chain of the proof, all newly built here:

- `cdKernel_eval_eq_zero_of_root_ne` — the kernel vanishes between two distinct nodes. At two roots of
  `monicOrtho s (n+1)` the Christoffel--Darboux numerator is identically zero and `x − y ≠ 0`, so the
  kernel value is. This is the one place the Christoffel--Darboux identity (link 53) is used, and it
  is used in its original non-confluent form.
- `gaussBasis s n ξ := λₙ(ξ) • K_ξ` — the same normalised kernel that link 55 introduced as the
  variational competitor turns out to be **the Lagrange basis of the node set**: value `1` at its own
  node (`normalisedKernel_eval_self`, reused verbatim) and `0` at the others (previous item).
- `momentFunctional_gaussBasis` — each basis element has moment value exactly `λₙ(ξ)`, because the
  kernel reproduces the constant polynomial `1`.
- `gauss_interpolation` — a polynomial of degree `≤ n` equals `∑_ξ p(ξ) • gaussBasis s n ξ`. Proved by
  showing the difference has degree `≤ n` and vanishes at all `n+1` nodes, then applying
  `eq_zero_of_natDegree_lt_card_of_eval_eq_zero'` with the node count from link 61.
- `momentFunctional_eq_gaussSum_of_degree_lt` — exactness on degree `≤ n`, termwise from the above.
- The extension to `2n+1` is division with remainder: `p = ρ + Q q` with `deg ρ, deg q ≤ n`, and `Q q`
  is invisible to both sides — orthogonality kills it on the left, the nodes being roots of `Q` kill
  it on the right.

**Toolchain note:** `Finset.sup_lt_iff` and the `degree_zero` branch both want `⊥ < ↑(n+1)` in
`WithBot ℕ`, not `0 < ↑(n+1)`; `WithBot.bot_lt_coe` is the lemma, and no cast lemma substitutes.

**Opens next:** the weights are positive (`christoffel_pos`, already proved) and now sum to `s₀`
— take `p = 1` in the exactness theorem. So `gaussMeasure s n := ∑_ξ λₙ(ξ) δ_ξ` is a genuine positive
measure of total mass `s₀` representing `s₀ … s_{2n+1}`, and building it as a `MeasureTheory.Measure`
via `Measure.sum` over `Measure.dirac` is now purely mechanical. Once it exists, link 58 applies to it
and gives `λₙ(ξ) ≤ λ(ξ)` at every node — the first *lower* bound on the limit Christoffel function,
and the direction that attainment for the infinite problem actually needs.

### Link 63 — the Gauss measure exists, and a correction to link 62

New module `formal/GaloisForLFunctions/HTGeometry/GaussMeasure.lean` (81 lines, zero placeholders,
registered). All endpoints `[propext, Classical.choice, Quot.sound]`.

- `integrable_finsetWeightedDirac`, `integral_finsetWeightedDirac` — for an *arbitrary* finite
  weighted Dirac family: every function is integrable, and integrates to the weighted sum of values.
  Stated generally because nothing about the Christoffel weights is used beyond nonnegativity; both
  are Finset inductions using `Integrable.add_measure`, `Integrable.smul_measure`, `integral_dirac`.
- `gaussMeasure s n := ∑_{ξ ∈ gaussNodes s n} ENNReal.ofReal (λₙ(ξ)) • δ_ξ` — an honest
  `MeasureTheory.Measure ℝ`.
- `integral_gaussMeasure` — integration against it *is* the quadrature sum.
- `gaussMeasure_moment` — `[PROVED HERE]` **`∫ xᵏ d(gaussMeasure s n) = s k` for every `k ≤ 2n+1`**.
- `gaussMeasure_mass` — total mass `s₀`.

So for every `n` the truncated moment problem `s₀ … s_{2n+1}` is solved by an explicit positive
measure, constructed rather than assumed.

**Correction to link 62's closing paragraph.** That entry claimed link 58 would apply to
`gaussMeasure` and yield `λₙ(ξ) ≤ λ(ξ)`. Both halves are wrong and the claim is withdrawn:

1. `measureReal_singleton_le_christoffelLimit` requires `HasHamburgerMoments s μ`, i.e. *all* moments
   matching. `gaussMeasure s n` matches only `s₀ … s_{2n+1}`, so the hypothesis is unavailable.
2. The inequality points the other way regardless. `λ = ⨅ₙ λₙ` by definition (link 57), so
   `λ(x) ≤ λₙ(x)` always, and `λₙ(ξ) ≤ λ(ξ)` would force equality at every node of every level — not
   something to expect, let alone a consequence of link 58.

The error was writing the handoff by analogy with the preceding link instead of checking the
hypothesis of the theorem being invoked. Nothing in Lean was affected; no proof depended on it.

**Opens next (revised).** What the Gauss measures are actually for is Hamburger's *existence*
theorem: a positive-definite moment sequence has a representing measure, obtained as a weak-* limit
of `gaussMeasure s n` as `n → ∞`. That is the honest use of a family of measures each solving one
more truncation. The obstruction to formalising it is not this development but mathlib's stock: the
classical route is Helly's selection theorem, and the modern route needs tightness plus Prokhorov.
Neither is currently reachable from what is imported here, so the next concrete step is a survey of
what weak-* compactness mathlib actually provides for measures on `ℝ` — a tooling question, to be
answered before more moment machinery is built on the assumption that the limit is available.

### Link 64 — the tooling survey, and uniform tightness

Link 63 called for a survey of mathlib's weak-* compactness before building further. Result, and it
is better than expected:

- **Prokhorov is in mathlib** — `Mathlib/MeasureTheory/Measure/Prokhorov.lean`, including
  `CompactSpace (ProbabilityMeasure E)` for compact `E` and the tight-implies-relatively-compact
  direction. `Mathlib/MeasureTheory/Measure/Tight.lean` supplies `IsTightMeasureSet` with the usable
  criterion `isTightMeasureSet_iff_exists_isCompact_measure_compl_le`, and `TightNormed.lean` adds
  closed-ball criteria for normed spaces.
- **Helly's selection theorem is absent** (the only `Helly` in mathlib is Helly's *convexity*
  theorem, in `Analysis/Convex/Radon.lean`). So the classical route is unavailable and the Prokhorov
  route is the one to take — which is the reverse of the guess recorded in link 63.

This changes the assessment there: the limit is *not* blocked on missing mathlib. It is blocked on
supplying tightness, and tightness is available from the moment data.

New module `formal/GaloisForLFunctions/HTGeometry/GaussTightness.lean` (76 lines, zero placeholders,
registered; compiled first try). All endpoints `[propext, Classical.choice, Quot.sound]`.

- `finsetWeightedDirac_apply` — evaluation of a finite weighted Dirac sum on a measurable set, as a
  finite sum of weights against the indicator. Finset induction; completes the trio of
  general-purpose lemmas about such families begun in link 63.
- `gaussSum_pow` — `∑_ξ λₙ(ξ) ξᵏ = s k` for `k ≤ 2n+1`, the quadrature theorem on monomials.
- `gaussNodes_tail_weight_le` — `[PROVED HERE]` **for `n ≥ 1` and `R > 0`,
  `∑_{ξ : |ξ| > R} λₙ(ξ) ≤ s₂ / R²`** — the tail weight, bounded uniformly in the level.

The proof needs no measure-theoretic Chebyshev inequality: each Gauss measure is a finite sum of point
masses, so the mass outside a ball is a finite sum of weights, and Chebyshev degenerates into the
observation that `1 ≤ ξ²/R²` on precisely the nodes being summed. Every Gauss measure carries the
same second moment `s₂`, which is what makes the bound uniform in `n`.

**Opens next:** convert the tail bound into `IsTightMeasureSet (Set.range fun n => gaussMeasure s n)`.
The mathematical content is done; what remains is ENNReal bookkeeping — feed
`finsetWeightedDirac_apply` with `A = (Set.Icc (-R) R)ᶜ`, whose indicator sum over the nodes is the
filtered sum just bounded, and then `isTightMeasureSet_iff_exists_isCompact_measure_compl_le` with
`K = Set.Icc (-R) R` compact and `R` chosen as `√(s₂/ε)`. After that Prokhorov applies directly and
the remaining mathematical question is the one genuinely delicate step: moments do not automatically
pass to a weak-* limit, since `xᵏ` is unbounded, so the limit measure's moments need uniform
integrability — available from the `(k+2)`-nd moment bound, itself uniform by the same argument.

### Link 65 — tightness, at the measure level

`GaussTightness.lean` now 130 lines, zero placeholders. The three new endpoints are
`[propext, Classical.choice, Quot.sound]`; the whole block compiled first try.

- `gaussMeasure_compl_Icc_le` — `gaussMeasure s n ((Icc (-R) R)ᶜ) ≤ ENNReal.ofReal (s₂ / R²)` for
  `n ≥ 1`, `R > 0`. The ENNReal bookkeeping predicted in link 64 went through as planned:
  `finsetWeightedDirac_apply` turns the measure of the complement into an indicator sum, the set
  identity `(Icc (-R) R)ᶜ = {x | R < |x|}` is `← abs_le` followed by `not_le`, `Finset.sum_filter`
  converts the indicator sum to the filtered sum, and `ENNReal.ofReal_sum_of_nonneg` pulls the
  coercion outside so link 64's real inequality applies under `ENNReal.ofReal_le_ofReal`.
- `moment_two_pos` — `0 < s₂`, since `s₂ = ⟪X, X⟫` and `X ≠ 0`.
- `isTightMeasureSet_gaussMeasure` — `[PROVED HERE]`
  **`IsTightMeasureSet (Set.range fun n => gaussMeasure s (n+1))`**.

For the last one the compact set is `[-√(s₂/ε), √(s₂/ε)]`, chosen so the tail bound comes out as
exactly `ε` rather than merely below it; `ε = ⊤` is a separate trivial branch, and `ε ≠ ⊤` is what
makes `ENNReal.ofReal_toReal` close the goal. Choosing `R` to hit the bound exactly avoided an
inequality chain in `ℝ≥0∞` entirely — worth preferring whenever the threshold is a free parameter.

So the family of Gauss measures satisfies the hypothesis of Prokhorov's theorem, which mathlib
already has. Existence of a representing measure is no longer blocked on any missing infrastructure.

**Opens next:** two concrete steps, in order.
1. *Apply Prokhorov.* The mathlib statement is phrased for `ProbabilityMeasure`; the Gauss measures
   have mass `s₀`, so either normalise by `s₀` (positive by `PositiveMomentForm`, and the tail bound
   scales) or use the `FiniteMeasure` form. This is a packaging question, not a mathematical one —
   the first thing to check is which of the two mathlib actually supports without extra hypotheses.
2. *Pass the moments to the limit.* This is the real remaining content and it does not follow from
   weak convergence alone, since `xᵏ` is unbounded. The route is uniform integrability of `xᵏ` along
   the family, which follows from the uniform `(k+2)`-nd moment bound by the same Chebyshev-free
   argument used in link 64 — `gaussSum_pow` already supplies every moment up to `2n+1`, so the
   bound is available for each fixed `k` once `n` is large enough.

### Link 66 — normalisation, step 1 of the link-65 handoff

`GaussTightness.lean` now 176 lines, zero placeholders; four new endpoints, all
`[propext, Classical.choice, Quot.sound]`.

The packaging question from link 65 is settled by reading `Prokhorov.lean`: mathlib offers both
forms, but the tight-implies-relatively-compact statement — `isCompact_closure_of_isTightMeasureSet`
— is stated only for `ProbabilityMeasure`. (The `FiniteMeasure` results at lines 204 and 463 require
a supplied sequence of compacts and a null sequence, which is more setup, not less.) So normalising
is the shorter road, and it is now done.

- `gaussMeasure_univ` — `gaussMeasure s n univ = ENNReal.ofReal (s₀)`. Same shape as the tail bound:
  `finsetWeightedDirac_apply` at `univ`, indicator collapses, `ENNReal.ofReal_sum_of_nonneg`, then
  `gaussSum_pow` at `k = 0`.
- `moment_zero_pos` — `0 < s₀`, since `s₀ = ⟪1, 1⟫` and `1 ≠ 0`.
- `gaussProb s n := (ENNReal.ofReal (s₀))⁻¹ • gaussMeasure s n`, with `gaussProb_univ` and
  `isProbabilityMeasure_gaussProb` — `[PROVED HERE]` each normalised Gauss measure **is** a
  probability measure.
- `gaussProb_compl_Icc_le` — the tail bound survives normalisation, scaled by `(s₀)⁻¹`.

`IsProbabilityMeasure` is produced as a theorem rather than an instance, since it depends on the
hypothesis `PositiveMomentForm s`; call sites will need `haveI`.

**Toolchain note:** `mul_le_mul_left'` is deprecated in favour of `mul_le_mul_right` in this
toolchain, with the same argument shape. As with `push_neg` in link 61, the deprecation is a warning,
and the formal lint gate fails on warnings — so these must be fixed even though the file compiles.

**Opens next:** assemble `S : Set (ProbabilityMeasure ℝ)` from the `gaussProb s (n+1)` and feed
`isCompact_closure_of_isTightMeasureSet`. Two mechanical obstacles are visible in its statement: the
tightness hypothesis is phrased on the *coerced* set `{(μ : Measure E) | μ ∈ S}`, so link 65's
`isTightMeasureSet_gaussMeasure` needs restating for `gaussProb` and then transporting across the
coercion; and building each `ProbabilityMeasure ℝ` term requires the instance above in scope. Neither
is mathematical. The genuine remaining content is still step 2 of link 65 — passing moments to the
limit against unbounded `xᵏ`, which needs uniform integrability rather than weak convergence alone.

### Link 67 — Prokhorov applied

`GaussTightness.lean` now 230 lines, zero placeholders; three new endpoints, all
`[propext, Classical.choice, Quot.sound]`.

- `gaussProb_compl_Icc_le'` — the normalised tail bound with the scalar folded inside the coercion:
  `gaussProb s n ((Icc (-R) R)ᶜ) ≤ ENNReal.ofReal ((s₀)⁻¹ · (s₂/R²))`, via
  `ENNReal.ofReal_inv_of_pos` and `ENNReal.ofReal_mul`.
- `isTightMeasureSet_gaussProb` — tightness of the normalised family. Same exact-threshold trick as
  link 65, now with `R = √(s₂/(s₀ε))` so the bound lands on `ε` on the nose.
- `gaussProbMeasure h n : ProbabilityMeasure ℝ` — the packaged subtype term.
- `isCompact_closure_gaussProbMeasure` — `[PROVED HERE]` **the Gauss family has compact closure in
  the weak topology on `ProbabilityMeasure ℝ`.**

Both mechanical obstacles anticipated in link 66 were real and both were mechanical. The coercion
mismatch is handled by an explicit set equality between `{(μ : Measure ℝ) | μ ∈ range gaussProbMeasure}`
and `range gaussProb`, proved by `rintro`/`exact` in both directions — the coercion of the subtype
term is definitionally the underlying measure, so no transport lemma is needed.

**Toolchain note:** `positivity` fails on `0 ≤ (s 0)⁻¹` because the sign of `s 0` is a hypothesis, not
syntactic. `inv_nonneg.mpr (moment_zero_pos h).le` supplies it. This is the same failure mode as the
`kernelRoot` case recorded much earlier in this card: `positivity` reasons from the *shape* of a term,
so any positivity fact that lives in a hypothesis has to be handed over explicitly.

So a subsequential weak-* limit of the Gauss measures exists, unconditionally, from
`PositiveMomentForm s` alone.

**Opens next:** the limit measure is now available but nothing yet says its moments are `s`. This is
step 2 of link 65 and it remains the one piece of genuine mathematical content: weak convergence
tests against *bounded* continuous functions, and `xᵏ` is not bounded. The concrete target is that
for each fixed `k`, the family `{gaussProb s (n+1)}` is uniformly integrable against `xᵏ`, which
follows from the uniform `(k+2)`-nd moment bound — `gaussSum_pow` supplies moment `k+2` for every
`n` with `2n+1 ≥ k+2`, so the bound holds for all but finitely many members of the family, which is
enough. Worth checking first whether mathlib's `MeasureTheory.UniformIntegrable` API connects to weak
convergence in the form needed, since that determines whether this is assembly or construction.

### Link 68 — the survey answered, and the analytic core

The link-67 question was whether the moment-to-limit step is assembly or construction. The survey
answers it: **assembly**, and not via `UniformIntegrable` at all.

`Mathlib/MeasureTheory/Measure/Portmanteau.lean` carries
`lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`, whose hypotheses are
*continuous and nonnegative* — with **no boundedness requirement on the integrand**. That is the
whole difficulty of link 65's step 2 dissolved: the reason weak convergence was thought not to
transport `xᵏ` is that it tests against *bounded* continuous functions, but the lower-semicontinuous
half of portmanteau has no such restriction. Uniform integrability is what one needs for a two-sided
limit; a one-sided bound needs nothing beyond `f ≥ 0` and continuity, and a one-sided bound is what
bounding the limit's moments requires.

New module `formal/GaloisForLFunctions/HTGeometry/MomentLimitBound.lean` (47 lines, zero placeholders,
registered; compiled first try). Both endpoints `[propext, Classical.choice, Quot.sound]`.

- `pow_two_mul_nonneg` — `0 ≤ x^{2k}`, by `pow_mul` and `sq_nonneg` rather than an `Even.pow_nonneg`
  lemma whose name in this toolchain was not worth guessing.
- `lintegral_even_pow_le_of_forall_isOpen_le_liminf` — `[PROVED HERE]` if `μ` satisfies the
  portmanteau open-set inequality against a sequence `μs` and every `μs i` has
  `∫⁻ ofReal(x^{2k}) ≤ C`, then `∫⁻ ofReal(x^{2k}) ∂μ ≤ C`.

The hypothesis is stated as the open-set inequality rather than as weak convergence, so the lemma
applies to a limit point however it was obtained — which matters here, since compactness (link 67)
delivers a cluster point, not a convergent sequence.

The module imports `Mathlib.MeasureTheory.Measure.Portmanteau` directly rather than the Gauss chain:
it uses nothing from this project, and a false dependency on `GaussTightness` would have misrepresented
where the result lives.

**Opens next:** two independent threads, either order.
1. *Compute the Gauss side of the hypothesis.* Needs `∫⁻ ofReal(x^{2k}) d(gaussProb s n)` in terms of
   `s`, i.e. `lintegral` analogues of the `finsetWeightedDirac` lemmas — the Bochner versions exist
   (link 63) but `lintegral` is a different API and the bridge is `lintegral_eq_lintegral_...` or a
   fresh induction, which is likely shorter.
2. *Extract a sequence from the cluster point.* The weak topology on `ProbabilityMeasure ℝ` is
   metrizable — mathlib has `LevyProkhorovMetric.lean` — so a cluster point of a sequence is a
   subsequential limit. Whether a ready instance exposes this, or whether the metric has to be
   invoked explicitly, is the thing to check first.

### Link 69 — thread 1 closed: the two halves meet

New module `formal/GaloisForLFunctions/HTGeometry/GaussMomentLimit.lean` (75 lines, zero placeholders,
registered). All endpoints `[propext, Classical.choice, Quot.sound]`.

`MomentLimitBound.lean` was first generalised: its hypothesis is now `∀ᶠ i in atTop` rather than
`∀ i`. This was forced by the application — the quadrature only reaches order `2k` once `2k ≤ 2n+1`,
so the moment bound holds for large `n` only — and it costs nothing, since `liminf` ignores any finite
initial segment and `liminf_le_liminf` already consumed an `Eventually`.

- `lintegral_finsetWeightedDirac` — lower integration against a finite weighted Dirac family. The
  `lintegral` API turned out *easier* than the Bochner one of link 63: `lintegral_add_measure` and
  `lintegral_dirac` carry no integrability or measurability side conditions, so the induction is three
  rewrites with no hypotheses to discharge.
- `lintegral_gaussMeasure`, `lintegral_even_pow_gaussMeasure` — the even moments as lower integrals:
  `∫⁻ ofReal(x^{2k}) d(gaussMeasure s n) = ENNReal.ofReal (s_{2k})` for `2k ≤ 2n+1`.
- `lintegral_even_pow_gaussProb` — the same, normalised, with factor `(s₀)⁻¹`.
- `lintegral_even_pow_limit_le` — `[PROVED HERE]` **every weak limit point `μ` of the Gauss family
  satisfies `∫⁻ ofReal(x^{2k}) dμ ≤ (s₀)⁻¹ · s_{2k}` for every `k`.**

So a limit point is not merely a probability measure: it has finite moments of every even order,
bounded by the moment sequence that generated the family. That is the first statement about the limit
object itself rather than about the approximants.

**Toolchain note:** in `ℝ≥0∞` the scalar action and multiplication are propositionally but not
syntactically equal; `lintegral_smul_measure` produces `c • ∫⁻ …` and goals stated with `*` need
`smul_eq_mul` appended to the rewrite chain. Both failures in this module were exactly this.

**Opens next:** thread 2 of link 68, now the only thing between here and Hamburger existence — turn
the Prokhorov cluster point into an actual limit point satisfying the portmanteau hypothesis. Two
sub-steps: extract a convergent subsequence (the weak topology on `ProbabilityMeasure ℝ` is metrizable
via `LevyProkhorovMetric.lean`; check whether an instance exposes this or the metric must be invoked
by hand), then convert weak convergence into the open-set inequality using
`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`, which is already in `Portmanteau.lean` at
line 323 in exactly the required form. After that the remaining gap is the *reverse* moment
inequality, where the one-sided portmanteau argument does not apply and something genuinely two-sided
is needed.

### Link 70 — thread 2 closed: a weak limit measure exists

`GaussMomentLimit.lean` now 112 lines, zero placeholders; three new endpoints, all
`[propext, Classical.choice, Quot.sound]`; compiled first try.

Both sub-steps of the link-69 handoff resolved without construction:

- `MetrizableSpace (ProbabilityMeasure ℝ)` is a genuine **instance**
  (`instMetrizableSpaceProbabilityMeasure`, `LevyProkhorovMetric.lean:696`), found by `inferInstance`
  with no hypotheses to supply. So `IsCompact.tendsto_subseq` applies directly to the Prokhorov
  closure and the Lévy--Prokhorov metric never has to be mentioned.
- `ProbabilityMeasure.le_liminf_measure_open_of_tendsto` is stated for an arbitrary filter `L`, so it
  converts subsequential weak convergence into the open-set inequality with no reindexing work.

- `exists_subseq_tendsto_gaussProbMeasure` — `[PROVED HERE]` a strictly monotone `φ` and a limit
  `μ : ProbabilityMeasure ℝ` with `gaussProbMeasure h (φ i + 1) → μ` weakly.
- `lintegral_even_pow_limit_le_subseq` — the moment bound along a subsequence. The only adjustment
  needed was `StrictMono.le_apply` (`i ≤ φ i`) to keep the eventual hypothesis of link 69 available
  after reindexing.
- `exists_probabilityMeasure_even_moment_le` — `[PROVED HERE]`

  **From `PositiveMomentForm s` alone there exists a probability measure `μ` on `ℝ` with
  `∫⁻ x^{2k} dμ ≤ (s₀)⁻¹ · s_{2k}` for every `k`.**

Unconditional, no representing-measure hypothesis anywhere: the measure is *constructed*, from the
moment sequence, through orthogonal polynomials → Gauss nodes → Christoffel weights → quadrature →
tightness → Prokhorov → subsequence. Links 51–70 are that chain.

**Opens next:** the reverse inequality, which is now the whole remaining gap to Hamburger existence
proper. What is proved is `∫ x^{2k} dμ ≤ (s₀)⁻¹ s_{2k}`; what is wanted is equality, and for *all*
moments rather than the even ones. The one-sided portmanteau argument cannot give it — it is
intrinsically an inequality in one direction. The classical route is that the uniform moment bound
just established makes `{x^k}` uniformly integrable along the subsequence, upgrading weak convergence
to convergence of the moments themselves; this is where mathlib's `UniformIntegrable` API, set aside
in link 68 as unnecessary, becomes the right tool after all. Worth noting that the odd moments will
need the even bound as input, so the current statement is the natural prerequisite rather than a
detour.

### Link 71 — correction to link 70's handoff, and the limit's tail decay

`GaussMomentLimit.lean` now 150 lines, zero placeholders; two new endpoints, both
`[propext, Classical.choice, Quot.sound]`; compiled first try.

**Correction.** Link 70 named `MeasureTheory.UniformIntegrable` as the tool for the reverse moment
inequality. Reading its definition, it does not apply:

```
def UniformIntegrable (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop
```

It quantifies over a **family of functions against one fixed measure**. The situation here is the
transpose — one function `xᵏ` against a family of measures `gaussProb s (φ i + 1)` — and mathlib has
no ready notion for that. The classical phrase "uniformly integrable" covers both, which is what made
the misidentification easy; the Lean definition commits to one of them. So the reverse inequality has
to be built by hand as a truncation argument, not assembled from that API.

That argument needs two tail estimates, one on each side. The approximant side already exists
(`gaussProb_compl_Icc_le'`, link 67). This link supplies the other:

- `measure_compl_Icc_le_of_lintegral_sq_le` — Chebyshev: a measure with `∫⁻ ofReal(x²) ≤ C` has
  `μ((Icc (-R) R)ᶜ) ≤ C / ofReal(R²)`. Via `meas_ge_le_lintegral_div`, with the containment
  `(Icc (-R) R)ᶜ ⊆ {x | ofReal(R²) ≤ ofReal(x²)}` discharged by `nlinarith` from `sq_abs`.
- `exists_probabilityMeasure_tail_le` — `[PROVED HERE]` **the limit measure of link 70 satisfies
  `μ((Icc (-R) R)ᶜ) ≤ (s₀)⁻¹ s₂ / R²` for every `R > 0`** — the same rate as the Gauss measures it
  came from, which is what a truncation argument requires to make both error terms vanish together.

**Opens next:** the truncation argument itself, now with both estimates in hand. The remaining piece
is the bounded continuous cutoff: a function agreeing with `xᵏ` on `[-R, R]` and vanishing outside
`[-2R, 2R]`, packaged as `ℝ →ᵇ ℝ` so that weak convergence applies to it. Constructing
`BoundedContinuousFunction` terms is the one part of this with no shortcut visible, so the first move
is to check what mathlib offers for building them — `BoundedContinuousFunction.ofNormedAddCommGroup`,
or a composition of `xᵏ` with a truncation like `max (min x R) (-R)`, the latter avoiding a bump
construction entirely since `x ↦ (max (min x R) (-R))ᵏ` is already bounded and continuous and equals
`xᵏ` on `[-R, R]`.

### Link 72 — the truncation function

New module `formal/GaloisForLFunctions/HTGeometry/TruncatedPower.lean` (53 lines, zero placeholders,
registered). All endpoints `[propext, Classical.choice, Quot.sound]`.

The guess recorded at the end of link 71 held: clamping before exponentiating avoids the bump
function entirely.

`truncPow R k x := (max (min x R) (-R))ᵏ`

- `continuous_truncPow` — a composition of lattice operations with a power; `Continuous.min`,
  `Continuous.max`, `Continuous.pow`, nothing else.
- `abs_clamp_le`, `abs_truncPow_le` — bounded by `Rᵏ`, because the clamp lands in `[-R, R]`.
- `truncPow_eq_of_mem_Icc` — on `[-R, R]` it *is* `xᵏ`: `min_eq_left` then `max_eq_left`, no
  case analysis.
- `abs_truncPow_le_abs_pow` — outside the ball it is dominated by `|x|ᵏ`.
- `truncPowBCF R hR k : ℝ →ᵇ ℝ` with a `@[simp]` application lemma, so weak convergence applies to it
  directly.

**Toolchain notes:** `pow_le_pow_left` no longer exists under that name — the ordered-field version is
`pow_le_pow_left₀ (ha : 0 ≤ a) (hab : a ≤ b) (n)`, while `pow_le_pow_left'` is the unbundled monoid
version with different hypotheses. And `BoundedContinuousFunction.ofNormedAddCommGroup` lives in
`Bounded/Normed.lean`, not `Bounded/Basic.lean`, so the narrow import had to be widened by one file.

**Opens next:** the comparison estimate, which is now pure bookkeeping over the three pieces in hand.
For any measure `ν` and any `R > 0`,

`|∫ xᵏ dν − ∫ truncPow R k dν| ≤ ∫_{|x|>R} (|x|ᵏ + Rᵏ) dν ≤ 2 ∫_{|x|>R} |x|ᵏ dν`,

using `truncPow_eq_of_mem_Icc` to kill the integrand on the ball and `abs_truncPow_le_abs_pow`
outside it. Applied to the Gauss measures and to the limit measure — whose tails links 67 and 71
bound at the same rate — both error terms go to zero as `R → ∞` uniformly in the level, while the
middle terms converge by weak convergence against `truncPowBCF`. That is the full truncation
argument; every ingredient it needs is now proved.

### Link 73 — the pointwise comparison

`TruncatedPower.lean` now 86 lines, zero placeholders; both new endpoints
`[propext, Classical.choice, Quot.sound]`.

- `abs_pow_sub_truncPow_le` — `[PROVED HERE]` for `R ≥ 0` and every `x`,

  `|xᵏ − truncPow R k x| ≤ 1_{(Icc (-R) R)ᶜ}(x) · 2|x|ᵏ`.

  On the ball both sides are zero (`truncPow_eq_of_mem_Icc`, and the indicator vanishes); off it the
  triangle inequality plus `abs_truncPow_le_abs_pow` gives `|x|ᵏ + |x|ᵏ`.
- `abs_pow_sub_truncPow_eq_zero_of_mem` — the error is exactly `0` on the ball, stated separately
  since the truncation argument uses it to restrict integrals to the tail.

Phrasing the bound with an *indicator* rather than as a conditional statement is what makes it usable:
integrating it against a measure immediately produces a tail integral, with no case split surviving
into the measure-theoretic step.

**Toolchain notes:** `abs_add` no longer exists under that name; `norm_sub_le` with
`Real.norm_eq_abs` gives `|a − b| ≤ |a| + |b|` directly. And `add_le_add_left h c` in this toolchain
produces `a + c ≤ b + c` — it adds on the *right* despite the name — so `linarith` is the safer way
to add a constant to one side of an inequality.

**Opens next:** integrate the pointwise bound. For any measure `ν` with the relevant integrability,

`|∫ xᵏ dν − ∫ truncPow R k dν| ≤ 2 ∫_{|x|>R} |x|ᵏ dν`

by `abs_integral_le_integral_abs` and `integral_mono` against the indicator. The two instantiations
needed are `ν = gaussProb s (φ i + 1)` and `ν = μ`, and the tail integrals on the right are then
bounded via Cauchy--Schwarz against the tail *measure* bounds of links 67 and 71 — that step needs
`∫_{|x|>R} |x|ᵏ ≤ (∫ x^{2k})^{1/2} (ν{|x|>R})^{1/2}`, so the even-moment bounds already proved are
what convert a measure-level tail estimate into an integral-level one. Worth checking whether
mathlib's `inner_mul_le_norm_mul_norm` or the measure-theoretic `integral_mul_le_Lp_mul_Lq` is the
cleaner entry point before writing it.

### Link 74 — the comparison estimate, without Cauchy–Schwarz

`TruncatedPower.lean` now 133 lines, zero placeholders; both new endpoints
`[propext, Classical.choice, Quot.sound]`; compiled first try.

Link 73's handoff planned an indicator integral, tail *measure* bounds from links 67 and 71, and a
Cauchy--Schwarz step to connect them. **None of that is needed.** On the tail `Rᵏ ≤ |x|ᵏ`, hence
`|x|ᵏ ≤ |x|^{2k} / Rᵏ` there; on the ball the error is zero and the right-hand side is still
nonnegative. So both cases are covered by one bound with no indicator and no tail set:

- `abs_pow_sub_truncPow_le_even` — `[PROVED HERE]` for `R > 0` and every `x`,
  `|xᵏ − truncPow R k x| ≤ 2 x^{2k} / Rᵏ`.
- `abs_integral_sub_integral_truncPow_le` — `[PROVED HERE]` integrating it,
  `|∫ xᵏ dν − ∫ truncPow R k dν| ≤ 2 (∫ x^{2k} dν) / Rᵏ`, for any `ν` with the three relevant
  integrability hypotheses.

Because `x^{2k}` is exactly the quantity the even-moment estimates already control, the bound lands
directly on what links 62 and 70 provide. The tail measure bounds of links 67 and 71 are not consumed
by this route at all — they remain proved and available, but the argument no longer passes through
them.

That is twice in this stretch that a handoff over-planned the machinery: link 68 expected
`UniformIntegrable`, link 73 expected Cauchy--Schwarz, and in both cases writing down the inequality
directly was shorter than the named tool. The pattern seems to be that naming a classical technique
imports its full generality, when the instance at hand is a one-line estimate.

**Toolchain note:** the word `admit` in an English docstring trips a naive placeholder grep. Reworded;
worth avoiding `sorry`/`admit`/`axiom` as English words in comments in this tree.

**Opens next:** assemble the three-term estimate. For the limit measure `μ` and the subsequence
`νᵢ = gaussProb s (φ i + 1)`,

`|∫ xᵏ dμ − ∫ xᵏ dνᵢ| ≤ 2(∫ x^{2k} dμ)/Rᵏ + |∫ truncPow R k dμ − ∫ truncPow R k dνᵢ| + 2(∫ x^{2k} dνᵢ)/Rᵏ`,

where the outer terms are uniformly small by the even-moment bounds and the middle term tends to zero
for fixed `R` by weak convergence against `truncPowBCF`. The remaining Lean work is the integrability
side conditions for each `ν`, which for the Gauss measures is `integrable_gaussMeasure` (link 63, any
function) and for `μ` follows from the finiteness of `∫⁻ x^{2k}` proved in link 70.

### Link 75 — moment convergence from weak convergence

New module `formal/GaloisForLFunctions/HTGeometry/MomentConvergence.lean` (90 lines, zero
placeholders, registered). All endpoints `[propext, Classical.choice, Quot.sound]`.

- `exists_pow_gt` — for `k ≥ 1`, a radius with `Rᵏ` exceeding any prescribed bound; `max 1 (c+1)`
  and `pow_le_pow_right₀`.
- `abs_sub_le_three` — the four-point triangle inequality, from `abs_sub_le` twice.
- `tendsto_integral_pow_of_uniform_even_moment` — `[PROVED HERE]`

  **If `νᵢ → μ` weakly and `∫ x^{2k} dνᵢ ≤ M` uniformly with `∫ x^{2k} dμ ≤ M`, then
  `∫ xᵏ dνᵢ → ∫ xᵏ dμ`,** for `k ≥ 1`.

This is the theorem link 65 identified as the genuine remaining content, and it is now proved in
general form — no Gauss data anywhere, just weak convergence plus a uniform even-moment bound. The
`ε` argument: pick `R` with `2M/Rᵏ < ε/4`, bound both outer terms of the four-point triangle by
`abs_integral_sub_integral_truncPow_le` (link 74), and take the middle term below `ε/2` by weak
convergence against `truncPowBCF R`.

Two things the build taught, both about hypotheses that turned out unnecessary:

- `gcongr` discharged `∫ x^{2k} dμ ≤ M` by finding `hMμ` in context, but could not discharge the
  indexed `hMν i`, which needs an argument. So one of the two parallel `have`s needed a following
  `exact` and the other rejected it. `gcongr` searches the context for *closed* hypotheses only.
- The assumption `0 ≤ M` was never used and the linter caught it. It is genuinely redundant: if
  `M < 0` the hypothesis `∫ x^{2k} ≤ M` is unsatisfiable, so the statement holds vacuously. Dropped.

**Opens next:** instantiate. The general theorem needs, for `νᵢ = gaussProb s (φ i + 1)` and the
limit `μ` of link 70: weak convergence in `∫ f dνᵢ → ∫ f dμ` form for bounded continuous `f`
(available from `hlim` via `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`, to be checked);
the uniform even-moment bound in *Bochner* form, where links 69 and 70 currently give the `lintegral`
form, so a bridge via `integral_eq_lintegral_of_nonneg_ae` is needed; and the integrability side
conditions, which for the Gauss measures are `integrable_gaussMeasure` for any function and for `μ`
follow from finiteness of `∫⁻ x^{2k}`. With that, `∫ xᵏ dμ = lim s_k/s₀` and Hamburger existence
closes.

### Link 76 — the approximant side of the instantiation

New module `formal/GaloisForLFunctions/HTGeometry/GaussMomentConvergence.lean` (55 lines, zero
placeholders, registered; compiled first try). All endpoints
`[propext, Classical.choice, Quot.sound]`.

Link 75's handoff listed a `lintegral → Bochner` bridge as needed. On the approximant side it is
not: `integral_gaussMeasure` (link 63) is already stated for the Bochner integral, so the Gauss
moments come out directly.

- `integrable_gaussProb` — every function is integrable against `gaussProb s n`, from
  `integrable_gaussMeasure` and `Integrable.smul_measure`. Unconditional in `f`, because a finite
  weighted sum of point masses integrates everything.
- `integral_pow_gaussProb` — `[PROVED HERE]` `∫ xᵏ d(gaussProb s n) = (s₀)⁻¹ s_k` for `k ≤ 2n+1`.
- `tendsto_integral_gaussProb` — weak convergence of the extracted subsequence in the integral form
  the general theorem consumes, via `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`. The
  subtype coercion is definitional, so this is one application with no transport.
- `integral_even_pow_gaussProb_le` — the even moments along a subsequence, constant in `i` once
  `k ≤ i`, using `StrictMono.le_apply` as in link 70.

So of the four hypotheses `tendsto_integral_pow_of_uniform_even_moment` requires of the `ν` side —
weak convergence, uniform even-moment bound, integrability of `xᵏ`, `x^{2k}`, and `truncPow` — all
are now discharged.

**Opens next:** only the `μ` side remains, and it is exactly the `lintegral → Bochner` bridge that
turned out unnecessary for the approximants. Needed: from `∫⁻ ofReal(x^{2k}) dμ ≤ C` (link 70),
derive `Integrable (fun x => x^{2k}) μ` and `∫ x^{2k} dμ ≤ C.toReal`. The first is
`HasFiniteIntegral` plus measurability, with finiteness of `C` coming from `s₀ > 0`; the second is
`integral_eq_lintegral_of_nonneg_ae` with `ENNReal.toReal_mono`. Integrability of `xᵏ` for odd `k`
then follows by domination, `|x|ᵏ ≤ 1 + x^{2k}` pointwise. With those three, the general theorem
applies and `∫ xᵏ dμ = (s₀)⁻¹ s_k` for every `k ≥ 1` — Hamburger existence, in the normalised form
this construction produces.

### Link 77 — the μ-side bridge, and two signature repairs

New module `formal/GaloisForLFunctions/HTGeometry/MomentBochnerBridge.lean` (75 lines, zero
placeholders, registered; compiled first try). All endpoints, and the re-checked
`tendsto_integral_pow_of_uniform_even_moment`, are `[propext, Classical.choice, Quot.sound]`.

- `integrable_of_lintegral_ofReal_lt_top` — a nonnegative measurable function with finite lower
  integral is integrable (`hasFiniteIntegral_iff_ofReal`).
- `integral_le_toReal_of_lintegral_le` — a bound on `∫⁻ ofReal f` bounds `∫ f`
  (`integral_eq_lintegral_of_nonneg_ae` plus `ENNReal.toReal_mono`).
- `abs_pow_le_one_add_even`, `integrable_pow_of_integrable_even` — `|x|ᵏ ≤ 1 + x^{2k}` pointwise, so
  the odd powers inherit integrability from the even ones against a finite measure.
- `integrable_truncPow` — truncated powers are integrable against any finite measure.
- `moment_even_pos` — `0 < s_{2k}`, since `s_{2k} = ⟪Xᵏ, Xᵏ⟫`.

Two repairs to `MomentConvergence.lean`, both discovered by trying to instantiate it:

1. `hMν` had to become `∀ᶠ i in atTop` rather than `∀ i`. The Gauss quadrature only reaches order
   `2k` once the level is large enough, so the uniform bound is genuinely only eventual. The proof
   absorbs this by taking `max N N₂` of the two thresholds. This is the same weakening link 69 made
   to `MomentLimitBound`, needed again one level up — a hypothesis stated as `∀ i` is the wrong
   default anywhere a filter limit is the conclusion.
2. The `truncPow` integrability hypotheses now require `0 < R`. As stated they quantified over all
   real `R`, including negative ones where `abs_truncPow_le` does not apply; the proof only ever uses
   the positive `R` it chooses, so the hypothesis was strictly stronger than needed and would have
   been unprovable at the instantiation.

**Opens next:** the capstone, now assembly only. Take `μ, φ` from
`exists_subseq_tendsto_gaussProbMeasure`, get the open-set inequality from
`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`, feed `lintegral_even_pow_limit_le_subseq` into
the two bridge lemmas to obtain the `μ`-side integrability and moment bound, supply the `ν` side from
link 76, and apply `tendsto_integral_pow_of_uniform_even_moment`. The limit of the approximants is
eventually the constant `(s₀)⁻¹ s_k`, so `tendsto_nhds_unique` identifies `∫ xᵏ dμ` with it. Every
input to that chain is proved; it will be written in its own module so the existing bridge banks
independently of it.

### Link 78 — existence of a representing measure

New module `formal/GaloisForLFunctions/HTGeometry/HamburgerExistence.lean` (77 lines, zero
placeholders, registered). Axioms: `[propext, Classical.choice, Quot.sound]`.

`exists_probabilityMeasure_moments` — `[PROVED HERE]`

> **For a positive definite moment form `s` there exists a probability measure `μ` on `ℝ` with
> `∫ xᵏ dμ = s_k / s₀` for every `k ≥ 1`.**

Hypothesis: `PositiveMomentForm s`, i.e. `⟪p, p⟫ > 0` for `p ≠ 0`. Nothing else. No measure is
assumed anywhere — the one produced is constructed from the moment sequence alone.

The construction, links 51–78 end to end: monic orthogonal polynomials by Gram--Schmidt against the
moment form → three-term recurrence → Christoffel--Darboux kernel → the orthogonal polynomials have
only real, simple roots (three uses of one pairing trick, links 59/60/61) → those roots as quadrature
nodes with Christoffel weights → Gauss quadrature exact to order `2n+1` → the quadrature measure →
uniform tail bound from the shared second moment → Prokhorov → weak limit along a subsequence →
even moments bounded via the lower-semicontinuous half of portmanteau → moment convergence by
truncation.

Assembly detail worth recording: `∀ᶠ` does not support dot-notation `.symm`, since the elaborated
type is a raw filter membership rather than `Filter.EventuallyEq`. Stating the eventual equality in
`=ᶠ[atTop]` form from the start makes `Tendsto.congr'` apply directly.

**Opens next.** The statement proved is one-sided in a way worth being precise about: it gives *a*
representing measure, not all of them, and says nothing about uniqueness. That is exactly right for
this card's purpose — indeterminacy is the phenomenon of interest, and a determinate sequence would
have made the Nevanlinna parametrisation vacuous. Two directions follow.

1. *Back to the card's own object.* `ClassicalNevanlinnaExtremalFamily` still has `leaf`,
   `finite_carried`, `infinity_carried`, `leaf_moments` open (link 55 handoff). `leaf_moments` is now
   within reach: it asks exactly for `HasHamburgerMoments s (leaf t)`, and this link produces a
   measure with the moments of `s` up to the `s₀` normalisation. What is still missing is the
   *parametrisation* — one measure per boundary point `t`, varying continuously — rather than a
   single one.
2. *Sharpening this link.* The measure here comes from an arbitrary convergent subsequence, so
   different subsequences may give different measures. Making that non-uniqueness explicit — two
   subsequences with distinct limits, for an indeterminate `s` — would turn an artefact of the proof
   into a statement about the moment problem, and is the natural bridge from existence to the
   Nevanlinna disc this card is really about.

### Link 79 — strengthened to the project's own predicate

`HamburgerExistence.lean` now 92 lines, zero placeholders; both endpoints
`[propext, Classical.choice, Quot.sound]`.

The `k ≥ 1` restriction in link 78 was an artefact of how the argument was assembled, not of the
result. The integrability derivation runs uniformly in `k` — for `k = 0` the lower integral is just
`μ univ = 1 ≤ C`, no special case — and the moment identity at `k = 0` is
`∫ 1 dμ = 1 = (s₀)⁻¹ s₀`, one `inv_mul_cancel₀`. So the statement was weaker than what the proof
already gave:

- `exists_probabilityMeasure_hasMoments` — `[PROVED HERE]` a probability measure `μ` with, **for
  every `k`**, `Integrable (xᵏ) μ` and `∫ xᵏ dμ = s_k / s₀`. Supersedes link 78's statement, which
  quantified only over `k ≥ 1` and did not expose integrability at all.
- `exists_hasHamburgerMoments` — `[PROVED HERE]`
  **`∃ μ : ProbabilityMeasure ℝ, HasHamburgerMoments (fun k => (s₀)⁻¹ · s_k) μ`.**

The second is the connector this development has been aimed at from link 51: `HasHamburgerMoments` is
the project's own predicate, the one appearing in `NevanlinnaBoundaryKernel`,
`NevanlinnaClassicalInterface`, `AtomlessProjectiveFrameFiber` and elsewhere, and it is now
*constructible* from a positive definite moment form rather than only assumable. Every card in the
tree that takes a representing measure as a hypothesis can now discharge it.

**Opens next.** With `leaf_moments` reachable, the remaining `ClassicalNevanlinnaExtremalFamily`
fields are `leaf`, `finite_carried`, `infinity_carried` — all three about the *family*, not any single
measure. That is the real frontier now: this link produces one measure per moment sequence, and the
structure needs one per boundary point `t : OnePoint ℝ`, varying continuously, with prescribed
support. The `nevMatrixData` of link 51 already supplies the matrix side, so the missing object is
the map `t ↦ leaf t` itself. Concretely: for fixed `t`, the sequence to feed this construction is not
`s` but the one whose orthogonal polynomials are `Q_n + t R_n` — the second-kind combination built in
`SecondKindMomentPolynomials.lean`. Whether that combination is itself a positive definite moment
form, so that this link applies to it verbatim, is the next question to settle, and it is a question
about objects already in the tree rather than about new machinery.

### Link 80 — Hamburger existence, unnormalised

`HamburgerExistence.lean` now 117 lines, zero placeholders; both new endpoints
`[propext, Classical.choice, Quot.sound]`; compiled first try.

Link 79's statement still carried the `s₀` normalisation, which was an artefact of routing through
`ProbabilityMeasure` for Prokhorov. Rescaling removes it:

- `exists_finiteMeasure_hasHamburgerMoments` — `[PROVED HERE]`

  > **For every positive definite moment form `s` there is a finite measure `ν` on `ℝ` with
  > `HasHamburgerMoments s ν`** — that is, `∫ xᵏ dν = s_k` for every `k`, on the nose.

  Taking `ν = ENNReal.ofReal (s₀) • μ`; the moment identity is `s₀ · (s₀)⁻¹ s_k = s_k`.
- `exists_hasHamburgerMoments_of_moment_zero_eq_one` — for `s₀ = 1` the probability measure itself
  represents `s`, no rescaling.

This is Hamburger's existence theorem: *positive definiteness of the Hankel form is sufficient for
representability*. The converse direction — that a representable sequence is positive definite — has
been in the tree since well before this card, as `momentFunctional_pow_two_nonneg` in
`MomentFunctionalPositivity.lean`. The two together are the characterisation, and until now only the
easy half was available.

**Opens next.** Three directions, in decreasing proximity.

1. *State the characterisation.* `PositiveMomentForm s ↔ ∃ finite ν, HasHamburgerMoments s ν` is now
   an assembly of two existing results, modulo matching `PositiveMomentForm` (strict, on all nonzero
   `p`) against `momentFunctional_pow_two_nonneg` (non-strict); the gap is exactly the determinate
   case where the form degenerates, and `positiveMomentForm_of_infiniteSupport` in
   `MomentInnerProduct.lean` is the bridge already built for it.
2. *Discharge hypotheses elsewhere.* Cards in the tree that assume a representing measure can now
   take `PositiveMomentForm` instead. Worth a sweep of `HasHamburgerMoments` call sites — eleven
   modules by the earlier grep — to see which assumptions become derivable.
3. *The family.* Unchanged from link 79: `leaf`, `finite_carried`, `infinity_carried` need one
   measure per boundary point `t`, and the question to settle first is whether the second-kind
   combination `Q_n + t R_n` from `SecondKindMomentPolynomials.lean` is itself a positive definite
   moment form, which would let this link apply to it verbatim.

### Link 81 — the characterisation

New module `formal/GaloisForLFunctions/HTGeometry/MomentCharacterisation.lean` (73 lines, zero
placeholders, registered). Both endpoints `[propext, Classical.choice, Quot.sound]`.

The infinite-support hypothesis of `positiveMomentForm_of_infiniteSupport` looked like an extra
condition to carry alongside representability. It is not — it is forced:

- `vanishingPoly F := ∏_{a ∈ F} (X − a)`, monic hence nonzero, vanishing on `F`.
- `measure_compl_finset_pos_of_positiveMomentForm` — `[PROVED HERE]` **any measure representing a
  positive definite moment sequence charges the complement of every finite set.** If some `F` carried
  all the mass, `vanishingPoly F` would be zero `ν`-a.e., so `⟪p, p⟫ = ∫ p² dν = 0` with `p ≠ 0`,
  contradicting positive definiteness.
- `positiveMomentForm_iff_exists_representing` — `[PROVED HERE]`

  > **`PositiveMomentForm s ↔ ∃ ν finite with infinite support, HasHamburgerMoments s ν`.**

Forward is link 80 plus the support lemma; backward is `positiveMomentForm_of_infiniteSupport`, in
the tree since long before this card. The support condition appears on the right-hand side not as an
imposition but because it is equivalent to the left — dropping it would make the statement false, as
a single Dirac mass represents a positive *semi*definite sequence.

This closes the arc opened at link 51. What began as infrastructure for one field of
`ClassicalNevanlinnaExtremalFamily` has produced a self-contained characterisation of Hamburger
representability, with both directions proved and no measure assumed anywhere.

**Opens next.** The natural sweep is direction 2 of link 80: eleven modules in the tree take
`HasHamburgerMoments` as a hypothesis, and the equivalence just proved lets each one be restated
against `PositiveMomentForm` — a purely algebraic condition on the sequence — instead. Whether that
is an improvement is per-module: for `NevanlinnaBoundaryKernel` the measure is the object of study
and should stay, but for anything whose conclusion is about the *sequence*, carrying a measure as a
hypothesis is now avoidable. That audit is the next concrete task, and unlike the previous thirty
links it is a question of restating existing results rather than proving new ones.

### Link 82 — first discharge from the sweep

New module `formal/GaloisForLFunctions/HTGeometry/MomentFiberNonempty.lean` (36 lines, zero
placeholders, registered). Both endpoints `[propext, Classical.choice, Quot.sound]`; compiled first
try.

Working the link-81 sweep, most `HasHamburgerMoments` occurrences turn out to be conclusions or
structure fields rather than dischargeable hypotheses. One is neither: `NevanlinnaBauerRetract.lean`
defines

`HamburgerMomentProbabilityFiber s := {ν : ProbabilityMeasure ℝ // HasHamburgerMoments s ν}`

— the space whose extreme points that module analyses. It carried no `Nonempty` result. The only way
to produce a point was `boundaryCarrierInMomentFiber`, which needs a `NevanlinnaBoundaryFamily s`
already in hand — that is, the fiber could be shown inhabited only by assuming the structure the
fiber exists to study.

- `nonempty_hamburgerMomentProbabilityFiber` — `[PROVED HERE]` for `PositiveMomentForm s` with
  `s₀ = 1`, the fiber is inhabited.
- `nonempty_hamburgerMomentProbabilityFiber_normalised` — without the normalisation hypothesis, the
  fiber of `k ↦ s_k/s₀` is inhabited.

Small in Lean, but it removes a circularity: inhabitance of the fiber now follows from a condition on
the *sequence*, with no boundary family, no barycenter, and no measure assumed.

**Opens next.** The remaining sweep targets are the three `ProjectiveFiniteConstraintCarrierAperture`
sites and `NevanlinnaConstraintProjector.lean:93`, which produce `HasHamburgerMoments` conclusions
from carrier constructions — worth checking whether any of them assume a representing measure
upstream that `positiveMomentForm_iff_exists_representing` would now supply. Beyond the sweep, the
open frontier is unchanged and is the family: `leaf`, `finite_carried`, `infinity_carried`, with the
question of whether `Q_n + t R_n` is a positive definite moment form still the first thing to settle,
since a positive answer would make this whole chain apply once per boundary point.

### Link 83 — correction of a repeated wrong lead, and the atom composition

**Correction, and it matters more than this link's Lean.** Links 79, 80 and 82 each closed by naming
the same next question: *is the second-kind combination `Q_n + t R_n` a positive definite moment
form, so that the existence chain applies once per boundary point?* That question is malformed and
the three handoffs should not be followed.

The N-extremal leaf measures **all represent the same sequence `s`**. That is what indeterminacy
*is*: the moment problem has many solutions, and `leaf_moments : ∀ t, HasHamburgerMoments s (leaf t)`
quantifies over `t` with `s` fixed — one sequence, many measures. There is no per-`t` moment
sequence for the chain to be applied to, so no amount of positive definiteness of anything indexed by
`t` would help. The error came from reading the parameter `t` as indexing *problems* when it indexes
*solutions of one problem*, and it survived three handoffs because each restated the previous rather
than re-deriving it.

The actual classical construction of `leaf t`: its support is the zero set of the entire function
`B(x)t − D(x)`, and its mass at each such zero `ξ` is `λ(ξ)`, the limit Christoffel function of
link 57. So the objects already built are the right ones — links 55–58 and 78–81 are on the correct
path — but the missing ingredient is the zero set of an entire function of exponential type, not a
family of moment sequences.

**This link's Lean.** New module `formal/GaloisForLFunctions/HTGeometry/ConstructedMeasureAtoms.lean`
(44 lines, zero placeholders, registered; compiled first try). Both endpoints
`[propext, Classical.choice, Quot.sound]`.

- `exists_finiteMeasure_atoms_le_christoffelLimit` — `[PROVED HERE]` there is a finite measure
  representing `s` **whose mass at every point is at most `λ(x)`**. Composition of link 80's
  construction with link 58's variational bound.
- `exists_finiteMeasure_atomless_where_christoffelLimit_eq_zero` — where `λ` vanishes, that measure
  has no atom.

Until now the atom bound applied only to measures *assumed* to exist and the construction produced a
measure with no information about its atoms; this is the first statement holding both ends at once,
and the mass values `λ(ξ)` it bounds are exactly the ones the N-extremal leaves are supposed to
realise with equality.

**Opens next**, stated so as not to repeat the error above: the gap between `≤ λ(ξ)` here and the
`= λ(ξ)` the leaves need. Two sub-questions, both about objects in the tree. (i) For which `x` is
`λ(x) > 0`? Link 57 gives `λ` as an infimum of computable finite-level quantities, so this is a
question about `christoffel s n x` as `n → ∞`, not about entire functions. (ii) Does the constructed
measure attain the bound at any point at all? A single point of attainment would be the first
evidence that the construction lands on an N-extremal leaf rather than an arbitrary solution.

### Link 84 — when the limit Christoffel function is positive

New module `formal/GaloisForLFunctions/HTGeometry/ChristoffelLimitPositive.lean` (54 lines, zero
placeholders, registered; compiled first try). Both endpoints
`[propext, Classical.choice, Quot.sound]`.

Sub-question (i) of link 83, answered:

- `christoffelLimit_pos_iff_bddAbove` — `[PROVED HERE]`
  **`0 < λ(x) ↔ BddAbove (range fun n => Kₙ(x,x))`.**
- `christoffelLimit_eq_zero_of_not_bddAbove` — the contrapositive form.

Since `Kₙ(x,x) = ∑_{k ≤ n} Qₖ(x)²/hₖ` (link 55), this says `λ(x) > 0` exactly when that series of
nonnegative terms converges. It is the criterion separating the two regimes of the moment problem,
and it is now stated in terms of the finite-level data alone.

The proof is short in both directions and neither needs new machinery: forward, `λ ≤ Kₙ⁻¹` for every
`n` (link 57) rearranges to `Kₙ ≤ λ⁻¹`; backward, a uniform bound `Kₙ ≤ M` gives `M⁻¹ ≤ Kₙ⁻¹` for
every `n`, so `le_ciInf` puts `M⁻¹ > 0` below the infimum. `gcongr` handles the inverse-antitone step
given the positivity of `Kₙ` in context, as it did in link 56.

This lands the `christoffelLimit` of link 57 on the same condition as the `BoundedKernel` predicate of
links 47--50, which was defined by summability of exactly this series in the complex variable. The two
halves of the card's machinery — the real variational side and the complex transfer side — are
therefore describing one condition, at least on the real axis. Making that identification explicit in
Lean is a short and worthwhile next step: `summable_kernel_iff` and
`christoffelLimit_pos_iff_bddAbove` should be two faces of one statement, differing only in that one
is phrased by summability and the other by boundedness of partial sums.

**Opens next:** that identification, then sub-question (ii) of link 83 — whether the constructed
measure attains `λ` anywhere. The identification is worth doing first, because `BoundedKernel` is
where the complex-analytic apparatus (link 50's openness, link 51's Nevanlinna matrix) is attached,
so connecting `λ` to it makes the variational theory available to that side rather than running
alongside it.

### Link 85 — the two halves of the card meet

New module `formal/GaloisForLFunctions/HTGeometry/ChristoffelBoundedKernel.lean` (54 lines, zero
placeholders, registered). Both endpoints `[propext, Classical.choice, Quot.sound]`.

The identification link 84 proposed, carried out:

- `monicOrthoC_ofReal` — complex evaluation of a real orthogonal polynomial at a real point is the
  real evaluation, via `aeval_algebraMap_apply` (the same lemma that carried link 60's splitting
  argument).
- `normSq_monicOrthoC_ofReal` — hence `normSq (monicOrthoC s k x) = Qₖ(x)²`, so the complex kernel
  series and the real one are *literally the same series* at a real point.
- `christoffelLimit_pos_of_boundedKernel` — `[PROVED HERE]` **`BoundedKernel s (x : ℂ)` implies
  `0 < christoffelLimit s x`.** Summability bounds every partial sum by the total
  (`Summable.sum_le_tsum`), which is exactly the criterion of link 84.

This is the first result joining the card's two independently built halves: the complex transfer
apparatus of links 47--51 (`kernelRoot`, `BoundedKernel`, the transfer radius, the Nevanlinna matrix)
and the real variational apparatus of links 55--58 and 84 (`cdKernel`, `christoffel`,
`christoffelLimit`). They were developed on separate tracks and turn out to be two descriptions of one
condition.

**Toolchain notes.** `((p.eval x : ℝ) : ℂ)` needs the inner ascription written explicitly —
`(p.eval x : ℂ)` elaborates as `eval (↑x) p` over `ℂ[X]`, which is a different statement, and the
error surfaces as a type mismatch on the polynomial rather than on the coercion. And `sum_le_tsum` is
not a standalone lemma in this toolchain; it is `Summable.sum_le_tsum`, taking the finset and the
off-support nonnegativity, with the summability hypothesis as the receiver.

**Opens next:** the converse, `0 < christoffelLimit s x → BoundedKernel s (x : ℂ)`, which is *not*
symmetric — `BoundedKernel` requires uniform bounds on *both* the first- and second-kind kernel roots
(`monicOrthoC` and `secondKindC`), while `christoffelLimit` sees only the first. So positivity of `λ`
gives half of `BoundedKernel` directly and the second-kind half needs its own argument. Worth stating
that asymmetry explicitly before attempting it: the natural intermediate is a predicate asserting only
the first-kind bound, which link 84's criterion characterises exactly, with `BoundedKernel` strictly
stronger.

### Link 86 — the asymmetry made explicit

New module `formal/GaloisForLFunctions/HTGeometry/FirstKindBounded.lean` (68 lines, zero
placeholders, registered; compiled first try). All endpoints
`[propext, Classical.choice, Quot.sound]`.

Link 85 closed by noting that the converse cannot be symmetric, since `BoundedKernel` constrains both
kernel roots and `christoffelLimit` only the first. Rather than attempt the converse and discover the
gap mid-proof, the gap is now a definition:

- `kernelRoot_sq_ofReal` — at a real point the first-kind kernel root squares to the
  Christoffel--Darboux diagonal, `kernelRoot² = Kₙ(x,x)`. This is the identity that makes the two
  sides comparable at all, and it follows from link 85's `normSq_monicOrthoC_ofReal` termwise.
- `FirstKindBounded s z` — uniform boundedness of the first-kind kernel root alone.
- `firstKindBounded_of_boundedKernel` — `BoundedKernel` is strictly the stronger condition; it carries
  the second-kind bound in addition.
- `firstKindBounded_iff_christoffelLimit_pos` — `[PROVED HERE]`
  **`FirstKindBounded s (x : ℂ) ↔ 0 < christoffelLimit s x`**, an exact characterisation, both
  directions.

So the picture on the real axis is now complete and precise: `λ(x) > 0` is *equivalent* to the
first-kind half of `BoundedKernel`, and *implied by* but not obviously equivalent to `BoundedKernel`
itself. Link 85's one-way implication is recovered as the composite of the two results here.

The backward direction needed the explicit bound `Kₙ(x,x) ≤ λ(x)⁻¹`, which was buried inside link
84's proof rather than exposed as a lemma; it is re-derived here in four lines. Worth extracting to
`ChristoffelLimitPositive.lean` if a third use appears.

**Opens next:** whether `FirstKindBounded` and `BoundedKernel` actually differ. Classically the
second-kind bound at a point follows from the first-kind bound holding *everywhere* — the transfer
machinery of links 47--50 is exactly the propagation argument for that — so the honest question is
not pointwise equivalence but whether `∀ x : ℝ, FirstKindBounded s x` implies `BoundedKernel s z` for
complex `z`. That is the indeterminacy dichotomy, and it is the same statement the closedness gap of
`ComplexKernelTransfer.lean` has been waiting on since link 50, now reachable from the real side.

### Link 87 — finite-level attainment

New module `formal/GaloisForLFunctions/HTGeometry/GaussAtoms.lean` (52 lines, zero placeholders,
registered; compiled first try). All endpoints `[propext, Classical.choice, Quot.sound]`.

Sub-question (ii) of link 83 at finite level:

- `gaussMeasure_singleton` — `gaussMeasure s n {ξ} = ENNReal.ofReal (λₙ(ξ))` for `ξ` a node. The
  weighted-Dirac evaluation of link 64 collapses to the single matching term.
- `gaussMeasure_real_singleton` — the same as a real mass.
- `exists_measure_real_singleton_eq_christoffel` — `[PROVED HERE]` **for every node `ξ` there is a
  measure reproducing `s₀ … s_{2n+1}` whose mass at `ξ` is exactly `λₙ(ξ)`.**

So the bound of link 58 is sharp at each finite level, and the Christoffel value is not merely an
upper estimate but the exact mass some moment-matching measure realises there. There is no tension
with link 58's inequality: the Gauss measure matches only finitely many moments, so it is not a
representing measure for the full sequence and the hypothesis of that bound does not apply to it.

Stating this was cheap — the measure is defined as a weighted sum of point masses with those very
weights, so the content is entirely in the bookkeeping. It is worth having in the ledger anyway,
because it fixes what "attainment" has to mean at the limit: not that some measure gets close to
`λ(ξ)`, but that the *same* construction that is exact at level `n` survives `n → ∞`.

**Opens next:** the limit version, which is genuinely open and is now stated sharply by contrast with
the above. What is proved: for each `n`, a measure matching `2n+1` moments with atom exactly `λₙ(ξ)`.
What is wanted: one measure matching *all* moments with atom exactly `λ(ξ)`. The obstruction is
visible in that gap — the weak limit of link 70 matches all moments (link 78) but its atoms are only
bounded (link 83), because weak convergence does not preserve point masses. Recovering the atom in
the limit requires knowing the nodes do not drift, i.e. that `ξ` remains a node at every sufficiently
large level, which is a statement about the zeros of `monicOrtho s n` as `n` grows rather than about
measures at all.

### Link 88 — the nodes always move, so link 87's route is closed

New module `formal/GaloisForLFunctions/HTGeometry/OrthoNoCommonRoot.lean` (42 lines, zero
placeholders, registered). Both endpoints `[propext, Classical.choice, Quot.sound]`.

Link 87 closed by hoping to recover the atom in the limit by showing a node `ξ` "remains a node at
every sufficiently large level". That hope is now refuted, by theorem:

- `monicOrtho_succ_no_common_root` — `[PROVED HERE]` `Qₙ` and `Q_{n+1}` never vanish at the same
  point. The Wronskian `Q_{n+1}Rₙ − QₙR_{n+1}` equals the constant `−hₙ/h₀`, which is nonzero since
  both norms are positive; a common root would make the left side vanish there. Three lines, using
  `momentWronskian_eq` from link 44 unchanged.
- `gaussNodes_disjoint_succ` — `[PROVED HERE]` **`Disjoint (gaussNodes s n) (gaussNodes s (n+1))`.**

So no point is a node at two consecutive levels, let alone at all large levels. The naive route to
limit attainment is not merely unproved — it is impossible, and the finite-level exactness of link 87
cannot be transported along a fixed point.

This is worth more than the lemma. It says the atom of the limit measure at `ξ` cannot come from the
atoms of the approximants at `ξ`, because those vanish at every other level. Whatever produces mass
`λ(ξ)` in the limit must come from nodes *approaching* `ξ`, which is why the classical treatment
works with the zeros of `B t − D` as a whole rather than tracking individual nodes — the entire
function's zero set is the limit object, and no finite-level node set is a subset of it.

**Opens next:** with the fixed-node route closed, the honest formulation of attainment is about
convergence of node sets, not membership. Concretely: for `ξ` with `λ(ξ) > 0`, does there exist a
sequence `ξₙ ∈ gaussNodes s n` with `ξₙ → ξ`? That is a statement about the zeros of `monicOrtho s n`
clustering, and it is the correct finite-level shadow of "the support of the leaf measure". The
disjointness just proved says such a sequence must have `ξₙ ≠ ξ` infinitely often, so the question is
genuinely about approach rather than eventual equality.

### Link 89 — closed form for the Christoffel limit

New module `formal/GaloisForLFunctions/HTGeometry/ChristoffelLimitFormula.lean` (63 lines, zero
placeholders, registered). Both endpoints `[propext, Classical.choice, Quot.sound]`.

- `cdKernel_eval_self_le_inv_christoffelLimit` — `Kₙ(x,x) ≤ λ(x)⁻¹`, the bound inlined in links 84
  and 86 and flagged there for extraction on a third use. Extracted now.
- `christoffelLimit_eq_inv_tsum` — `[PROVED HERE]` where the kernel series converges,

  **`λ(x) = (∑ₖ Qₖ(x)² / hₖ)⁻¹`.**

  Proof by uniqueness of limits: the diagonals `Kₙ(x,x)` are the partial sums and converge to the
  total, inversion is continuous away from zero, and the total is bounded below by `K₀(x,x) > 0`; so
  `λₙ = Kₙ⁻¹ → (tsum)⁻¹`, while link 57 gives `λₙ → λ`.

Together with link 84 this completes the description of `λ` on the real axis: it is positive exactly
when the series converges, and where positive it is the reciprocal of the sum. Everything about `λ`
that the classical theory states pointwise is now available in the tree — as a definition by
infimum (link 57), a convergence (link 57), a positivity criterion (link 84), a closed form (here),
and an identification with the complex-side condition (links 85--86).

Small note on the proof: `Summable.hasSum.tendsto_sum_nat` gives partial sums over `range n`, while
`cdKernel_eval_self` is a sum over `range (n+1)`. Composing with `tendsto_add_atTop_nat 1` fixes the
index, and the resulting `((fun n => …) ∘ (· + 1)) n = …` goal closes by `rfl` — the composition is
definitional, and no `Function.comp` simp lemma is needed.

**Opens next:** the node-approach question of link 88 is unchanged and remains the live one. The
closed form may help with it: `λ(ξ) > 0` now says the *tail* `∑_{k > n} Qₖ(ξ)²/hₖ` is small for large
`n`, which is a statement about how little the high-degree orthogonal polynomials weigh at `ξ` — and
a node of level `n` is where `Q_{n+1}` vanishes outright. Whether smallness of the tail at `ξ` forces
zeros of `Q_{n+1}` to accumulate at `ξ` is the sharp form of the question, and it is now expressible
entirely in terms of the sequence `Qₖ(ξ)` rather than in terms of measures.

### Link 90 — the condition in orthonormal language

New module `formal/GaloisForLFunctions/HTGeometry/OrthonormalDecay.lean` (51 lines, zero
placeholders, registered; compiled first try). All endpoints
`[propext, Classical.choice, Quot.sound]`.

- `orthonormalPoly_eval_sq` — `pₖ(x)² = Qₖ(x)²/hₖ`, since `pₖ = Qₖ/√hₖ`. The kernel series terms
  *are* the squared orthonormal polynomials.
- `summable_orthonormalPoly_sq_of_christoffelLimit_pos` — so the convergence criterion of link 84
  reads `Summable (fun k => pₖ(x)²)`.
- `tendsto_orthonormalPoly_eval_zero` — `[PROVED HERE]` **wherever the series converges,
  `pₖ(x) → 0`.**

The last one is the classical statement that the orthonormal polynomials decay at points where the
moment problem is indeterminate, and it is now a consequence of the definitions rather than an
imported fact. Passing from `pₖ(x)² → 0` to `pₖ(x) → 0` goes through `Real.sqrt_sq_eq_abs` and
continuity of `Real.sqrt` at `0`, with `tendsto_zero_iff_norm_tendsto_zero` converting to the norm
form — there is no direct "square root of a limit" lemma to reach for.

This is the reformulation link 89 asked for: the whole condition is now about the single sequence
`k ↦ pₖ(ξ)`, with no measures, no kernels, and no moment functionals in the statement.

**Opens next:** the node-approach question in its sharpened form. We now know `pₖ(ξ) → 0` when
`λ(ξ) > 0`, while a node of level `n` is a point where `p_{n+1}` vanishes exactly. So the question
"do zeros of `p_{n+1}` accumulate at `ξ`?" is asking whether smallness of `p_{n+1}(ξ)` forces a
nearby zero — which for polynomials is a question about the local behaviour of `p_{n+1}`, i.e. about
its derivative or its other roots near `ξ`. That is where the interlacing property would enter, and
interlacing is the one classical fact about these zeros the tree still lacks. Worth checking whether
it follows from the three-term recurrence and the Wronskian already present, since both the
Sturm-sequence and the Jacobi-matrix proofs of interlacing use exactly those inputs.

### Link 91 — Sturm alternation

New module `formal/GaloisForLFunctions/HTGeometry/SturmAlternation.lean` (51 lines, zero
placeholders, registered). All endpoints `[propext, Classical.choice, Quot.sound]`.

Link 90 asked whether interlacing follows from the three-term recurrence and the Wronskian already in
the tree. Its engine does, immediately:

- `recurOff_pos` — `bₙ = h_{n+1}/hₙ > 0`.
- `monicOrtho_eval_succ_succ_of_root` — at a root of `Q_{n+1}` the recurrence collapses to
  `Q_{n+2}(ξ) = −bₙ Qₙ(ξ)`.
- `monicOrtho_eval_mul_neg_of_root` — `[PROVED HERE]` **`Q_{n+2}(ξ) · Qₙ(ξ) < 0` at every root `ξ` of
  `Q_{n+1}`.** The two inputs are the collapsed recurrence and link 88's no-common-root, which
  supplies `Qₙ(ξ) ≠ 0`; without the latter the product would only be `≤ 0`.
- `monicOrtho_eval_succ_succ_ne_zero` — in particular neither neighbour vanishes there.

This is the Sturm-sequence property. It is the mechanism behind interlacing, and it came out of
material already proved — the recurrence from link 43, the Wronskian consequence from link 88 — with
no new machinery.

**Operational note.** Twice now a `cat > path` has landed in the *other* working directory
(`/Users/Spare/Documents/code/riemann/publications/hgt`), which has a matching
`GaloisForLFunctions/HTGeometry/` path, because the previous command ended with a `cd` to the repo
root for a card append and the next began without one. Both strays were untracked and were removed
after checking `git status`; nothing was overwritten. Every shell command in this workspace should
begin with an absolute `cd`, since the two trees are path-compatible and a misdirected write fails
silently rather than erroring.

**Opens next:** interlacing proper — between consecutive roots of `Q_{n+2}` there is a root of
`Q_{n+1}`, and conversely. The sign alternation gives the local ingredient; the global statement needs
it combined with the intermediate value theorem and a count, since `Q_{n+2}` has `n+2` real simple
roots (links 60--61) and `Q_{n+1}` has `n+1`. The natural Lean formulation is about the sorted root
lists rather than the root finsets, so the first step is deciding that representation before proving
anything about it.

### Link 92 — the interlacing step

New module `formal/GaloisForLFunctions/HTGeometry/InterlacingStep.lean` (47 lines, zero placeholders,
registered). Axioms `[propext, Classical.choice, Quot.sound]`.

`exists_root_between` — `[PROVED HERE]` if `a < b` are roots of `Q_{n+1}` and `Qₙ(a)·Qₙ(b) < 0`, then
`Q_{n+2}` has a root in `(a, b)`.

The Sturm collapse of link 91 turns the sign condition on `Qₙ` into the same condition on `Q_{n+2}`
up to the positive factor `bₙ`, so `Q_{n+2}(a)·Q_{n+2}(b) = bₙ²·Qₙ(a)·Qₙ(b) < 0`, and
`intermediate_value_Ioo` (or its primed decreasing variant, depending on which endpoint is positive)
produces the root. `mul_neg_iff` splits the two cases cleanly.

This is the inductive step of interlacing, isolated. It is stated with the sign condition as an
explicit hypothesis rather than derived, because deriving it *is* the induction — at consecutive roots
of `Q_{n+1}` the values of `Qₙ` alternate, and that alternation is what the induction carries.

**Toolchain note:** polynomial continuity is `Polynomial.continuous_aeval` in this toolchain, not a
bare `Polynomial.continuous`; and `nlinarith` would not find `b²uv < 0` from `0 < b` and `uv < 0`
without being handed the product `mul_pos hb2 (neg_pos.mpr hsign)` — degree-two products of
hypotheses are not searched by default when the sign flip is inside the goal.

**Opens next:** the induction itself. The invariant is that the `n+1` roots of `Q_{n+1}`, listed in
increasing order, separate the `n+2` roots of `Q_{n+2}`, and carrying it needs the roots as a sorted
list with a length equal to the degree — available from links 60--61 as
`monicOrtho_roots_card` and `monicOrtho_roots_nodup`, but not yet in sorted-list form. The
representation choice flagged in link 91 is now the immediate blocker rather than any missing
mathematics: `Multiset.sort` on the roots multiset, with `Finset.orderIsoOfFin` on `gaussNodes` as the
alternative, and the second looks more usable since the node count is already proved to be exactly
`n+1`.

### Link 93 — the nodes, enumerated in order

New module `formal/GaloisForLFunctions/HTGeometry/SortedNodes.lean` (52 lines, zero placeholders,
registered). All endpoints `[propext, Classical.choice, Quot.sound]`.

The representation question of links 91--92 is settled, and in favour of the second option:

`gaussNode h n : Fin (n+1) ↪o ℝ := (gaussNodes s n).orderEmbOfFin (gaussNodes_card h n)`

`Finset.orderEmbOfFin` lands directly in `ℝ` rather than in the subtype `↥(gaussNodes s n)`, so no
coercion appears in any statement and the order embedding supplies strict monotonicity for free.
`Multiset.sort` would have required carrying sortedness and length as side conditions; here both are
consequences of the construction, and `gaussNodes_card` from link 61 is the only input.

- `gaussNode_mem`, `gaussNode_root` — each enumerated node is a node, hence a root of `Q_{n+1}`.
- `gaussNode_strictMono`, `gaussNode_lt_succ` — strictly increasing, with the consecutive form the
  induction will use.
- `range_gaussNode`, `exists_gaussNode_eq` — the enumeration is exhaustive: every root of `Q_{n+1}` is
  `gaussNode h n i` for some `i`.

**Toolchain note:** `Fin.castSucc_lt_succ` takes its index implicitly in this toolchain, so
`Fin.castSucc_lt_succ i` is an application error rather than a specialisation.

**Opens next:** with both the step (link 92) and the enumeration (here) in place, the interlacing
induction has all its parts. The statement to prove is that for each `i : Fin (n+1)` there is a root
of `Q_{n+2}` strictly between `gaussNode h n i.castSucc` and `gaussNode h n i.succ` — but note this
needs the sign hypothesis of link 92, `Qₙ` alternating at consecutive nodes, which is the induction's
real content and is not yet available. The honest order of work is therefore: first prove the
alternation of `Qₙ` across consecutive roots of `Q_{n+1}` by induction on `n`, then feed it to link 92
node by node. The alternation is where the argument actually lives; the step and the enumeration are
scaffolding for it.

### Link 94 — the cofactor at a simple root

New module `formal/GaloisForLFunctions/HTGeometry/RootCofactor.lean` (40 lines, zero placeholders,
registered). Both endpoints `[propext, Classical.choice, Quot.sound]`.

- `exists_cofactor` — `[PROVED HERE]` at a root `ξ` of `Q_{n+1}` there is `G` with
  `Q_{n+1} = (X − ξ)G` and **`G(ξ) ≠ 0`**. The nonvanishing is what simplicity buys: `G(ξ) = 0` would
  make `(X − ξ)` divide twice, contradicting `monicOrtho_not_sq_dvd` from link 61.
- `cofactor_ne_zero` — the cofactor is nonzero as a polynomial.

`G(ξ)` is the object that plays the role of `Q'_{n+1}(ξ)` in the classical treatment, with no
derivative taken. That matters for the route ahead: the confluent Christoffel--Darboux identity is
usually stated with a derivative, and this tree has no differentiation theory for these polynomials.
Working with the cofactor avoids needing any.

**Plan for the alternation**, recorded so the next session does not have to re-derive it. Fix a root
`ξ` of `Q_{n+1}` and write `Q_{n+1} = (X − ξ)G`. The Christoffel--Darboux identity at `(x, ξ)` reads

`(x − ξ) Kₙ(x, ξ) = Q_{n+1}(x) Qₙ(ξ) / hₙ = (x − ξ) G(x) Qₙ(ξ) / hₙ`,

an identity of polynomial functions in `x`; cancelling `(x − ξ)` — legitimate via `Polynomial.funext`
and `mul_left_cancel₀` on `X − C ξ`, since `ℝ` is infinite — and evaluating at `x = ξ` gives

`Kₙ(ξ, ξ) = G(ξ) Qₙ(ξ) / hₙ`.

The left side is strictly positive (link 55), so **`G(ξ) · Qₙ(ξ) > 0`** at every root. Then, using the
monic factorisation `Q_{n+1} = ∏ⱼ (X − ξⱼ)` available from links 60--61 via
`Splits.eq_prod_roots_of_monic`, one gets `Gᵢ(ξᵢ) = ∏_{j≠i} (ξᵢ − ξⱼ)`, whose sign is
`(−1)^(number of roots above ξᵢ)` — alternating between consecutive nodes. That transfers the
alternation to `Qₙ(ξᵢ)`, which is the hypothesis link 92 has been waiting for.

Each of those steps is ordinary work on objects now all present; the only piece with any subtlety is
the polynomial cancellation, and `Polynomial.funext` is the tool for it.

### Link 95 — the confluent identity, without derivatives

New module `formal/GaloisForLFunctions/HTGeometry/ConfluentDarboux.lean` (60 lines, zero
placeholders, registered). Both endpoints `[propext, Classical.choice, Quot.sound]`.

The plan recorded in link 94, executed as written:

- `cdKernel_diag_mul_eq` — `[PROVED HERE]` for `Q_{n+1} = (X − ξ)G`,

  **`Kₙ(ξ, ξ) · hₙ = G(ξ) · Qₙ(ξ)`.**

  The polynomial identity `(X − ξ)·(Kξ · C hₙ) = (X − ξ)·(G · C Qₙ(ξ))` is proved pointwise by
  `Polynomial.funext`, using `christoffelDarboux` with the root substitution and `cdKernel_symm` to
  put the kernel in the right variable; `mul_left_cancel₀ (X_sub_C_ne_zero ξ)` removes the common
  factor and evaluation at `ξ` finishes.
- `cofactor_mul_monicOrtho_pos` — `[PROVED HERE]` **`G(ξ) · Qₙ(ξ) > 0`** at every root, since the
  kernel diagonal and `hₙ` are both positive.

This is the confluent Christoffel--Darboux identity, which classically reads
`Kₙ(ξ,ξ) = Q'_{n+1}(ξ)Qₙ(ξ)/hₙ`, obtained here with the cofactor in place of the derivative. No
differentiation theory for these polynomials is needed or used, and the cancellation that would be
a limit in the classical argument is an exact algebraic step.

**Toolchain note:** the import chain into `RootCofactor` runs through `GaussQuadratureNodes`, which
does not reach `ChristoffelKernel` or `ChristoffelDarboux`; both had to be added explicitly. The
symptom is `cdKernel` being reported as an unknown identifier treated as an auto-bound implicit,
which reads as a typo rather than a missing import.

**Opens next:** the sign of `G(ξᵢ)` across consecutive nodes, the last piece before the alternation.
With `Q_{n+1} = ∏ⱼ (X − ξⱼ)` from `Splits.eq_prod_roots_of_monic` (links 60--61) and the enumeration
of link 93, the cofactor at `ξᵢ` is `∏_{j ≠ i} (X − ξⱼ)`, so `Gᵢ(ξᵢ) = ∏_{j≠i} (ξᵢ − ξⱼ)`, negative
factors being exactly those with `ξⱼ > ξᵢ`. Consecutive `i` differ by one in that count, so the signs
alternate; combined with this link that transfers to `Qₙ(ξᵢ)` and discharges link 92's hypothesis.

### Link 96 — the node gaps

New module `formal/GaloisForLFunctions/HTGeometry/NodeGap.lean` (41 lines, zero placeholders,
registered). Both endpoints `[propext, Classical.choice, Quot.sound]`.

- `monicOrtho_ne_zero_of_mem_gap` — `[PROVED HERE]` `Q_{n+1}` has no root strictly between
  `gaussNode i.castSucc` and `gaussNode i.succ`. The enumeration is *exhaustive* (link 93), so a root
  in the gap would be `gaussNode j` for some `j` with `i.castSucc < j < i.succ`, i.e. `i < j < i+1`
  in `ℕ` — closed by `omega` after `Fin.lt_def`. The order embedding supplies the reflection
  `gaussNode a < gaussNode b ↔ a < b`, which is why exhaustiveness is usable at all.
- `cofactor_ne_zero_on_gap` — the cofactor at the lower endpoint likewise does not vanish on the gap.

**Route revision, recorded.** Link 95 proposed getting the cofactor sign from the explicit product
`Q_{n+1} = ∏ⱼ (X − ξⱼ)`, requiring `Splits.eq_prod_roots_of_monic` and a translation between the root
multiset and the `Fin (n+1)` enumeration. That translation is avoidable. Since `Q_{n+1}` has no root
on the open gap, and `Gᵢ` has none on `[ξᵢ, ξᵢ₊₁)` (this link), both keep a constant sign there; and
`Q_{n+1}(x) = (x − ξᵢ)Gᵢ(x)` with `x − ξᵢ > 0` while `Q_{n+1}(x) = (x − ξᵢ₊₁)Gᵢ₊₁(x)` with
`x − ξᵢ₊₁ < 0`. Evaluating both at a single interior point of the gap gives
`sign Gᵢ(ξᵢ) = −sign Gᵢ₊₁(ξᵢ₊₁)` directly, with no product and no multiset bookkeeping. Combined with
link 95's `Gᵢ(ξᵢ)·Qₙ(ξᵢ) > 0`, that is the alternation.

**Opens next:** the sign-constancy lemma that route needs — a polynomial with no root on an interval
has constant sign there, which is the contrapositive of the intermediate value theorem and should be
a short consequence of `intermediate_value_Ioo` as used in link 92. With it, the alternation is the
two-line evaluation above, and link 92 then delivers interlacing node by node.

### Link 97 — sign constancy

New module `formal/GaloisForLFunctions/HTGeometry/SignConstancy.lean` (51 lines, zero placeholders,
registered). All endpoints `[propext, Classical.choice, Quot.sound]`.

- `mul_pos_of_ne_zero_on_Icc` — `[PROVED HERE]` a continuous `f` with no zero on `[a, b]` satisfies
  `0 < f a · f b`. Trichotomy on the product: negative gives a zero inside by
  `intermediate_value_Ioo` (or the primed variant), zero contradicts nonvanishing at an endpoint.
  This is the lemma link 96 identified as the last general ingredient.
- `cofactor_eval_ne_zero` — away from a root of `Q_{n+1}` the cofactor cannot vanish, since
  `Q_{n+1}(y) = (y − ξ)G(y)`.
- `continuousOn_eval` — polynomial evaluation is continuous on any set, wrapping
  `Polynomial.continuous_aeval` so the `ContinuousOn` form is available without re-deriving it.

**Hygiene note.** `cofactor_eval_ne_zero` initially compiled with `n` never bound — `autoImplicit`
silently made it an implicit argument. The file built and the theorem was true, but the binder was
invisible in the statement. Made explicit. Worth watching for in this tree: a free variable in a
theorem statement is accepted rather than rejected, so the failure mode is a subtly more general
statement than intended rather than an error.

Also: one Lean process survived the usual `pgrep | xargs kill` after this build and needed `kill -9`.
The cleanup check caught it because it reports the count rather than assuming success.

**Opens next:** the alternation, now assembled from parts that are all present. For a gap
`(ξᵢ, ξᵢ₊₁)` pick any interior point `x`. Sign constancy on `[ξᵢ, x]` gives `Gᵢ(ξᵢ)·Gᵢ(x) > 0`;
constancy on `[x, ξᵢ₊₁]` gives `Gᵢ₊₁(x)·Gᵢ₊₁(ξᵢ₊₁) > 0`; and `Q_{n+1}(x)` equals both
`(x − ξᵢ)Gᵢ(x)` and `(x − ξᵢ₊₁)Gᵢ₊₁(x)`, with the two linear factors of opposite sign. Chaining gives
`Gᵢ(ξᵢ)·Gᵢ₊₁(ξᵢ₊₁) < 0`, and link 95 converts that to `Qₙ(ξᵢ)·Qₙ(ξᵢ₊₁) < 0` — exactly link 92's
hypothesis. The nonvanishing hypotheses for both applications come from link 96 and
`cofactor_eval_ne_zero` here.

### Links 98–99 — alternation, and interlacing

Two new modules, both zero placeholders, both registered, all endpoints
`[propext, Classical.choice, Quot.sound]`.

**`Alternation.lean`** (72 lines). `monicOrtho_eval_alternates` — `[PROVED HERE]`

> **`Qₙ(ξᵢ) · Qₙ(ξᵢ₊₁) < 0`** at consecutive nodes.

Assembled exactly as link 97 laid out, entirely inside one gap. Pick the midpoint `x`; sign constancy
on `[ξᵢ, x]` and on `[x, ξᵢ₊₁]` (link 97) holds the cofactors' signs, using link 96 for nonvanishing
on the gap and `exists_cofactor` at the endpoints; `Q_{n+1}(x)` factors as `(x−ξᵢ)Gᵢ(x)` and as
`(x−ξᵢ₊₁)Gᵢ₊₁(x)` with linear factors of opposite sign, giving `Gᵢ(x)·Gᵢ₊₁(x) < 0`; chaining yields
`Gᵢ(ξᵢ)·Gᵢ₊₁(ξᵢ₊₁) < 0`, and link 95's `Gᵢ(ξᵢ)·Qₙ(ξᵢ) > 0` transfers it to `Qₙ`.

**`Interlacing.lean`** (32 lines). `exists_root_between_gaussNodes` and `exists_gaussNode_between` —
`[PROVED HERE]` **between consecutive nodes of level `n` there is a root of `Q_{n+2}`**, i.e. a node
of level `n+1`. This is link 92's step with its hypothesis discharged; the proof is one application.

Interlacing was named in link 90 as "the one classical fact about these zeros the tree still lacks".
It is now proved, from the three-term recurrence and the Wronskian, with no derivative, no Jacobi
matrix, and no Sturm-sequence formalism — links 91--99 are that route.

**Two process notes.** The `set` tactic does not fold its definitions back into goals produced by
later `rw`/`simp`, so `simp [← hadef]` was needed in both factorisation steps; this is the same class
of problem as the `set`-after-`have` ordering issue from link 62. And the umbrella-import guard
`"HTGeometry.Interlacing" not in src` false-matched the already-present `HTGeometry.InterlacingStep`,
silently skipping the import — substring checks on module names are unsafe when one name is a prefix
of another, and the guard should test for the exact import line.

**Opens next:** the count. Interlacing gives *at least* one node of level `n+1` in each of the `n`
gaps; since level `n+1` has exactly `n+2` nodes (link 61), at most one can lie in each gap and the
two remaining lie outside the span. Making that precise would give the classical strict interlacing
statement, and it is pure counting on top of what is now proved — an injection from `Fin n` into
`Fin (n+2)` built from `exists_gaussNode_between`, plus the pigeonhole that the map is order-preserving.

### Link 100 — integration audit

No new mathematics. The umbrella-import guard that silently failed in link 99 prompted a check of
whether anything else this card claims is unverified, and two things were found.

**1. All 43 modules are registered.** Checked with an exact-line `grep -qx` against
`HTGeometry.lean` rather than a substring test, and every module has a source file. The link-99
false match was the only registration gap.

**2. Two modules had no `.olean`:** `OrthonormalWronskian` and `ComplexKernelTransfer`. Both are
pre-compaction work whose object files were never emitted — they had been checked with
`lake env lean` (which validates but writes nothing) and never with `-o`. So they were *verified* but
not *available*: any module importing them would have failed to build, and
`ComplexKernelTransfer.boundedKernel_of_isClosed` — the clopen argument this card leans on for the
global transfer — could not have been used downstream. Both now built and present.

This is the failure mode the workspace memory warns about, in a new form: not unimported modules, but
imported modules with no object file. `lake env lean <file>` proves a module elaborates; only
`lake env lean -o <olean> <file>` makes it usable. A card claim can be true and still be dead.

**3. Cross-module integration verified.** A scratch file importing ten of the session's modules
together — including both repaired ones — elaborates, and the five principal results re-audit clean:

- `momentFunctional_eq_gaussSum` (Gauss quadrature, exact to order `2n+1`)
- `exists_finiteMeasure_hasHamburgerMoments` (Hamburger existence)
- `positiveMomentForm_iff_exists_representing` (the characterisation)
- `exists_gaussNode_between` (interlacing)
- `firstKindBounded_iff_christoffelLimit_pos` (the real/complex identification)

all `[propext, Classical.choice, Quot.sound]`.

**Opens next:** the counting upgrade to strict interlacing, as recorded in link 99, is unchanged and
remains the next piece of mathematics. Before it, one worthwhile habit change: every module built in
this card from here should be emitted with `-o` at the time it is written, not checked bare, so that
the gap found here cannot recur.

### Link 101 — the interlacing selection

New module `formal/GaloisForLFunctions/HTGeometry/InterNode.lean` (62 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time per link 100). All endpoints
`[propext, Classical.choice, Quot.sound]`; compiled first try.

- `interNode h n i` — a level-`n+1` node chosen from the `i`-th gap, via `Classical.choose` on
  `exists_gaussNode_between` (link 99), with `interNode_spec`, `interNode_mem`, `interNode_lt`,
  `lt_interNode` unpacking the choice.
- `interNode_strictMono` — `[PROVED HERE]` **the selection is strictly increasing.** For `i < j`,
  the `i`-th choice lies below `gaussNode i.succ ≤ gaussNode j.castSucc` (order embedding plus
  `omega` on the `Fin` indices), which lies below the `j`-th choice.
- `interNode_injective`.

So the level-`n+1` nodes contain a strictly increasing family indexed by the `n` gaps of level `n` —
interlacing in the form a count can consume.

**On what this does and does not give.** The injection yields `n ≤ n + 2`, which is vacuous, so it is
not yet the classical strict-interlacing statement. What is missing is the *reverse* inequality: that
each gap contains at most one level-`n+1` node, equivalently that the selection is surjective onto the
level-`n+1` nodes lying inside the span of the level-`n` nodes. That does not follow from counting
alone with the two "extra" nodes unaccounted for — the two nodes of level `n+1` outside the span have
to be located first, and nothing proved so far pins them down.

**Opens next:** locate the extreme nodes. The natural statement is that `Q_{n+2}` has a root below
every root of `Q_{n+1}` and one above every root, which would account for the two extras and, with the
selection here, force the counting to be tight. Both should follow from sign information at the ends:
`Q_{n+2}` is monic so eventually positive, and its sign at the extreme nodes of level `n` is fixed by
the alternation of link 98 together with the confluent identity of link 95. That is the same
machinery, applied at the boundary of the node range rather than between consecutive nodes.

### Link 102 — a root above the largest node

New module `formal/GaloisForLFunctions/HTGeometry/ExtremeNode.lean` (76 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time). Both endpoints
`[propext, Classical.choice, Quot.sound]`.

- `monic_eventually_pos` — a monic real polynomial is eventually positive. Degree zero gives `P = 1`;
  positive degree uses `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg` and
  `Tendsto.eventually_gt_atTop`.
- `exists_root_above_last` — `[PROVED HERE]` **`Q_{n+2}` has a root above `gaussNode (Fin.last n)`,
  the largest root of `Q_{n+1}`.**

The chain is the one sketched in link 101: the cofactor `G` at the top node is monic (from
`Monic.of_mul_monic_left`) with all roots at or below that node, so sign constancy on `[ξ, R]` against
its eventual positivity gives `G(ξ) > 0`; link 95 then gives `Qₙ(ξ) > 0`; link 91's collapsed
recurrence gives `Q_{n+2}(ξ) < 0`; and `Q_{n+2}` monic is eventually positive, so IVT produces the
root above.

**Toolchain note, and it cost three builds.** `Polynomial.Monic` is a definition unfolding to
`leadingCoeff = 1`, so in this toolchain dot notation on a `Monic` hypothesis resolves against `Eq`:
`hP.natDegree_eq_zero_iff_eq_one` becomes `Eq.natDegree_eq_zero_iff_eq_one` and fails, as does
declaring a lemma in the `Monic` namespace and expecting `hMonic.myLemma` to find it. Every use must
be spelled out. On the other hand `hP` *is* a proof of `P.leadingCoeff = 1`, so `rw [hP]` works
directly where a `Monic.leadingCoeff` lemma would be reached for. And `leadingCoeff` has no equation
lemmas, so `rw [Polynomial.leadingCoeff]` fails — `← h0` plus `Polynomial.coeff_natDegree` is the
route.

**Opens next:** the mirror statement, a root of `Q_{n+2}` below `gaussNode 0`. The argument is the
same with the inequalities reversed, except that eventual positivity at `-∞` depends on the parity of
`n+2` — a monic polynomial tends to `+∞` at `-∞` for even degree and `-∞` for odd. Either case gives
the sign change against `Q_{n+2}(ξ_min)`, whose sign is `(−1)^{n+1}` by the same cofactor argument,
and the two parities cancel; but the parity bookkeeping is real and should be planned rather than
discovered mid-proof. With both extremes located, the `n+2` level-`n+1` nodes are fully accounted
for — `n` in the gaps, one below, one above — and the count closes strict interlacing.

### Link 103 — the node range expands

New module `formal/GaloisForLFunctions/HTGeometry/NodeRange.lean` (39 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time; compiled first try). All endpoints
`[propext, Classical.choice, Quot.sound]`.

- `le_gaussNode_last` — every root of `Q_{m+1}` is at most the largest enumerated node of level `m`.
- `gaussNode_last_lt_last` — `[PROVED HERE]` **the largest node strictly increases with the level.**
- `gaussNode_last_strictMono` — the same as a `StrictMono` in `n`.

**Route choice, deliberately.** Link 102 named the mirror statement — a root of `Q_{n+2}` below the
smallest node — as the next step, and flagged that it carries parity bookkeeping, since a monic
polynomial's behaviour at `−∞` depends on the parity of its degree and the sign of `Q_{n+2}` at the
bottom node is `(−1)^{n+1}`. Those two parities do cancel, so the statement is true and provable, but
it is the expensive way to reach what is actually wanted downstream. The *consequence* of interest —
that the node ranges grow — needs only the upper end, where the monic leading behaviour is positive
regardless of degree. So this link takes that instead: three short proofs, no parity, from link 102
alone.

The mirror statement remains open and is still worth having for strict interlacing proper, where the
count genuinely needs both extremes located. It is recorded as deferred rather than done.

**Opens next:** two independent directions, both now cheap to state.
1. *The lower mirror*, when strict interlacing is wanted: same argument at the bottom, with the sign
   of `Q_{n+2}(ξ_min)` and of `Q_{n+2}` at `−∞` both carrying `(−1)ⁿ` factors that cancel. Plan the
   parity as `Even`/`Odd` case analysis on `n` rather than manipulating `(−1)ⁿ` algebraically.
2. *Node approach*, the question from link 88 that motivated all of this: with the ranges expanding,
   the natural next statement is that the largest nodes tend to the top of the support — or, if the
   moment problem is indeterminate, that they diverge. Whether `gaussNode h n (Fin.last n)` is bounded
   is now a well-posed question about a monotone real sequence, and its answer is exactly whether the
   representing measures have bounded support.

### Link 104 — node weights decay quadratically

New module `formal/GaloisForLFunctions/HTGeometry/NodeWeightDecay.lean` (46 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time; compiled first try). All endpoints
`[propext, Classical.choice, Quot.sound]`.

- `christoffel_mul_sq_le` — `[PROVED HERE]` for `n ≥ 1` and any node `ξ`, **`λₙ(ξ) · ξ² ≤ s₂`**. One
  application of `Finset.single_le_sum` to the quadrature identity `∑_ζ λₙ(ζ)ζ² = s₂` of link 64,
  whose terms are nonnegative.
- `christoffel_le_div_sq` — equivalently `λₙ(ξ) ≤ s₂ / ξ²` for `ξ ≠ 0`.
- `christoffelLimit_mul_sq_le` — the same bound for the limit Christoffel function at a node, since
  `λ ≤ λₙ`.

This is the single-node form of the tail estimate that produced tightness in links 64--65. There the
sum over far nodes was bounded; here each individual far node is. The two are the same inequality read
at different granularity, and the pointwise form is the one that says a node's *weight* is small
rather than that a *collection* of nodes carries little mass.

**A caution about what this does not settle.** It is tempting to read this as bounding how far nodes
can go, but it does not: it constrains the weight at a distant node, not the node's existence. A
sequence of nodes escaping to infinity with weights decaying like `s₂/ξ²` is entirely consistent with
it, and that is exactly what happens whenever the representing measure has unbounded support. So the
question raised in link 103 — whether `gaussNode h n (Fin.last n)` is bounded — is *not* answered
here, and the expected answer is no in the cases this card cares about.

**Opens next:** the honest form of that question. Boundedness of the largest nodes is equivalent to
the representing measures having uniformly bounded support, which for an indeterminate problem is
false; so the statement worth proving is the divergence, not the boundedness. A route: if the largest
nodes were bounded by `M`, every Gauss measure would be supported in `[−M, M]`, so every weak limit
would be too, and the moments would be those of a compactly supported measure — but a compactly
supported measure is determinate, contradicting indeterminacy. That argument needs a determinacy
criterion the tree does not yet have, so the first step is to decide whether to build one.

### Link 105 — nodes lie within the support

New module `formal/GaloisForLFunctions/HTGeometry/NodeSupportBound.lean` (82 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time). Axioms
`[propext, Classical.choice, Quot.sound]`.

`monicOrtho_root_le_of_ae_le` — `[PROVED HERE]` **if a representing measure is carried below `M`,
every root of `Q_{n+1}` is at most `M`.**

The argument, and it uses three separate earlier links. Suppose `ξ > M`. Write `Q_{n+1} = (X − ξ)G`
(link 94). Then `deg G = n`, so `⟪Q_{n+1}, G⟫ = 0` by orthogonality. But that pairing is
`∫ (x − ξ)G(x)² dμ`, whose integrand is nonpositive on the support; vanishing of the integral forces
`G = 0` almost everywhere (`integral_eq_zero_iff_of_nonneg_ae`). A nonzero polynomial vanishes only on
a finite set, and link 81's `measure_compl_finset_pos_of_positiveMomentForm` says the measure charges
every cofinite set — contradiction.

That last step is where the earlier work pays: without link 81, "G vanishes a.e." would not be
absurd, since a measure supported on finitely many points makes it routine. Positive definiteness is
exactly what rules that out, and it was proved for this purpose two dozen links ago in a different
context.

**What this gives, stated carefully.** The contrapositive is the useful direction: if the nodes are
unbounded above, no representing measure is carried below any finite `M`, i.e. every representing
measure has support unbounded above. It does *not* yet prove the nodes are unbounded — that remains
the open half, and link 104 already warned against reading node-weight decay as a bound on node
position.

**Opens next:** the converse, that bounded support forces bounded nodes, is now immediate from this
link — it is the same statement. So the genuine remaining question is unchanged: is
`gaussNode h n (Fin.last n)` unbounded for an indeterminate sequence? With this link, that is
equivalent to every representing measure having unbounded support, which is a cleaner formulation
than the node one and is closer to standard determinacy theory. Deciding whether to build a
determinacy criterion — the question left open in link 104 — can now be posed as: prove that an
indeterminate sequence admits no compactly supported representing measure.

### Link 106 — nodes lie in the convex hull of the support

`NodeSupportBound.lean` now 149 lines, zero placeholders. Both new endpoints
`[propext, Classical.choice, Quot.sound]`; compiled first try.

- `monicOrtho_root_ge_of_ae_ge` — `[PROVED HERE]` the mirror of link 105: a representing measure
  carried above `m` forces every root of `Q_{n+1}` to be at least `m`.
- `monicOrtho_root_mem_Icc` — `[PROVED HERE]` **every node lies in `[m, M]` whenever the representing
  measure is carried there** — the nodes lie in the convex hull of the support.

The mirror needed no new idea: the integrand `(x − ξ)G(x)²` flips from nonpositive to nonnegative and
the rest of the argument is unchanged. This is worth contrasting with the *other* mirror still
deferred, the lower extreme node of link 102: that one genuinely carries parity, because it concerns
the leading behaviour of a monic polynomial at `−∞`, whereas this one concerns only the sign of a
linear factor on the support. Two statements that both read as "the same argument at the other end"
have quite different costs, and distinguishing them was worth the attention.

**Opens next**, unchanged in substance and now sharply posed. The chain of the last few links has
reduced the node-approach question of link 88 to: *does an indeterminate moment sequence admit a
compactly supported representing measure?* If not, its nodes are unbounded, by this link's
contrapositive. The standard answer is no, via polynomial density in `C([m, M])` — mathlib has
Stone--Weierstrass as `polynomialFunctions_closure_eq_top` — but turning density into uniqueness of
the representing measure needs a duality step in the space of measures that this tree does not yet
have. That is a well-defined piece of work with a known route, and it is the natural next
construction rather than another consequence of what is already proved.

### Link 107 — first step towards determinacy

New module `formal/GaloisForLFunctions/HTGeometry/MomentDeterminacyStep.lean` (39 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time; compiled first try).
Both endpoints `[propext, Classical.choice, Quot.sound]`.

- `integral_eval_eq_of_hasMoments` — `[PROVED HERE]` two measures representing the same sequence
  integrate every polynomial identically, since both integrals compute `momentFunctional s p`.
- `integral_eval_eq_of_moments_eq` — the same in the `hs`/`hint` hypothesis form used elsewhere here.

Small, but it is the exact input the density argument consumes, and it is worth having isolated: the
step is pure linearity and belongs nowhere near the analysis that follows it.

**Survey result, and the route.** Both remaining ingredients are in mathlib:

- `polynomialFunctions.topologicalClosure (s : Set ℝ)` (`StoneWeierstrass.lean`) and
  `polynomialFunctions_closure_eq_top a b` (`Weierstrass.lean`) — polynomial density in `C([a,b])`.
- `MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`
  (`HasOuterApproxClosed.lean:268`) — two finite measures agreeing on all bounded continuous
  functions are equal.

So the construction is: from this link, agreement on polynomials; by density, agreement on
`C([m, M])`; and since both measures are carried by `[m, M]`, agreement on all bounded continuous
functions on `ℝ`, whence equality. The one step with real content is the middle one — passing a
uniform limit through the integral — and it needs the measures to be finite, which they are.

**Opens next:** that middle step. It is a genuine construction rather than a corollary, and it is the
first piece in a while that is not assembly of existing parts. Note the shape it must take: density
gives a sequence of polynomials converging uniformly on `[m, M]` to a given continuous `f`, and
uniform convergence on a set carrying a finite measure transfers to convergence of integrals; the
awkwardness is that the polynomials are elements of a subalgebra of `C([m,M])` while the integrals
are over `ℝ`, so the restriction and its inverse have to be handled explicitly rather than
definitionally.

### Link 108 — uniform convergence passes through the integral

New module `formal/GaloisForLFunctions/HTGeometry/UniformIntegralLimit.lean` (55 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time; compiled first try).
Axioms `[propext, Classical.choice, Quot.sound]`.

`tendsto_integral_of_tendstoUniformlyOn` — `[PROVED HERE]` **if a finite measure gives full mass to
`S` and `F n → f` uniformly on `S`, then `∫ F n → ∫ f`.**

The estimate is elementary and deliberately so: uniform smallness on `S` plus `μ(Sᶜ) = 0` makes the
difference uniformly small almost everywhere, and `norm_integral_le_of_norm_le_const` bounds the
integral difference by that smallness times the total mass. Choosing the tolerance as
`ε / (2(c+1))` rather than `ε / (2c)` avoids a case split on whether the total mass `c` is zero — a
small thing, but it removes the only branch the proof would otherwise need.

This is the analytic content of the density step identified in link 107, isolated from the density
itself so that each can be checked on its own.

**Opens next:** the density half. `polynomialFunctions.topologicalClosure` gives, for continuous `f`
on `[m, M]`, a sequence of polynomials converging to it in the sup-norm of `C([m, M])`; what is needed
is that sequence as honest polynomials with `TendstoUniformlyOn` on `[m, M]`, which is a translation
between the `ContinuousMap` subalgebra picture and the pointwise one. That translation is the
remaining awkwardness flagged in link 107, and it is now the *only* thing between the parts and the
determinacy theorem: with it, link 107 gives agreement on polynomials, this link carries it to
continuous functions, and `ext_of_forall_integral_eq_of_IsFiniteMeasure` closes.

### Link 109 — Weierstrass in pointwise form

New module `formal/GaloisForLFunctions/HTGeometry/WeierstrassApprox.lean` (39 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time). Axioms
`[propext, Classical.choice, Quot.sound]`.

`exists_poly_approx` — `[PROVED HERE]` **for continuous `f` on `[a, b]` and `ε > 0` there is an
honest `p : Polynomial ℝ` with `|f x − p(x)| < ε` for all `x ∈ [a, b]`.**

This is the translation flagged in links 107--108. `polynomialFunctions_closure_eq_top` states density
as `(polynomialFunctions (Icc a b)).topologicalClosure = ⊤`, an equality of subalgebras of
`C(Icc a b, ℝ)`; `Metric.mem_closure_iff` extracts a nearby element, `polynomialFunctions_coe`
identifies it as the restriction of a genuine polynomial, and
`ContinuousMap.dist_apply_le_dist` converts the sup-metric bound to the pointwise one.

**Toolchain note.** `f ∈ S.topologicalClosure` is *definitionally* `f ∈ closure ↑S`, so the coercion
needs no rewrite — `have hmem' : f ∈ closure (↑S : Set _) := hmem` typechecks directly. The rewrite
`Subalgebra.topologicalClosure_coe` fails here because the goal is a membership rather than a
coercion, which reads as a missing lemma when it is really an unnecessary step.

**Opens next:** assembling the determinacy theorem. All three parts are now in the tree: agreement on
polynomials (link 107), uniform convergence through the integral (link 108), and polynomials
approximating continuous functions (here). The remaining work is to turn the `ε`-form of this link
into a sequence — take `ε = 1/(n+1)` and package as `TendstoUniformlyOn` — and then to bridge from
continuous functions on the subtype `Icc a b` to bounded continuous functions on `ℝ`, which is where
`ext_of_forall_integral_eq_of_IsFiniteMeasure` expects its input. That bridge is an extension
problem: a continuous function on a compact interval extends continuously and boundedly to `ℝ`, and
mathlib's Tietze machinery is the likely source.

### Link 110 — Weierstrass as a sequence

New module `formal/GaloisForLFunctions/HTGeometry/PolySeqApprox.lean` (49 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time; compiled first try). Axioms
`[propext, Classical.choice, Quot.sound]`.

`exists_poly_seq_tendstoUniformlyOn` — `[PROVED HERE]` **for `g` continuous on `[a, b]` there are
polynomials `P n` with `TendstoUniformlyOn (fun n x => (P n).eval x) g atTop (Icc a b)`.**

`ε = 1/(n+1)` in link 109, `choose` to extract the sequence, `exists_nat_one_div_lt` for the
threshold.

**A formulation choice that avoided the extension problem, at least here.** Link 109 gives its
conclusion for a bundled `C(Icc a b, ℝ)`, and link 108 wants functions on `ℝ`. Rather than extend the
continuous map from the subtype to `ℝ` — the Tietze route flagged in link 109 — this link takes
`g : ℝ → ℝ` with `ContinuousOn g (Icc a b)` as its *hypothesis* and restricts inside the proof via
`ContinuousOn.restrict`. The subtype then never appears in the statement, and the two links compose
without any extension.

That does not make the extension problem disappear; it relocates it. The final assembly still needs
to feed `ext_of_forall_integral_eq_of_IsFiniteMeasure`, whose input is bounded continuous functions
on `ℝ`, and a bounded continuous `f : ℝ → ℝ` is in particular continuous on `[m, M]`, so this link
applies to it directly. The extension is needed only if one starts from a function given on the
interval — and the assembly does not.

**Opens next:** the assembly, now with no missing pieces. For two finite measures carried by `[m, M]`
with the same moments and any bounded continuous `f : ℝ → ℝ`: this link gives polynomials converging
uniformly to `f` on `[m, M]`; link 108 carries that to `∫ P n → ∫ f` against each measure; link 107
says the `∫ P n` agree; so the limits agree, and `ext_of_forall_integral_eq_of_IsFiniteMeasure` gives
equality of the measures. That is determinacy for compactly supported representing measures, and with
link 105/106 it yields the node divergence that link 88 asked for.

### Link 111 — determinacy on a compact interval

New module `formal/GaloisForLFunctions/HTGeometry/CompactDeterminacy.lean` (47 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time; compiled first try).
Axioms `[propext, Classical.choice, Quot.sound]`.

`measure_eq_of_moments_eq_of_carried` — `[PROVED HERE]`

> **Two finite measures carried by the same compact interval, with the same moments, are equal.**

The assembly predicted in link 110, and it went through exactly as written: against a bounded
continuous `f`, link 110 gives polynomials converging uniformly on `[m, M]`; link 108 turns that into
convergence of the integrals against each measure; link 107 makes the polynomial integrals agree
termwise; `tendsto_nhds_unique` transfers the agreement to the limits; and
`ext_of_forall_integral_eq_of_IsFiniteMeasure` concludes.

Four links, each one theorem, each checkable alone — links 107 through 111 were laid out in advance
in link 107 and none of them changed shape on contact.

**What it settles.** A compactly supported representing measure is unique among compactly supported
ones. Combined with links 105--106, if some representing measure is carried by `[m, M]` then all the
Gauss nodes lie in `[m, M]`, so the node sequence `gaussNode h n (Fin.last n)` is bounded — and
conversely unbounded nodes rule out any compactly supported representative.

**Opens next, stated without overreach.** This is *not yet* full indeterminate-case determinacy: it
compares two compactly supported measures, whereas indeterminacy asserts the existence of two
representatives that need not both be compactly supported. To conclude "an indeterminate sequence has
no compactly supported representative" one still needs that a compactly supported measure is
determinate against *all* representatives, not just compact ones — which requires knowing a
representative with compact support forces every representative to be supported there. That is the
remaining gap and it is a genuine one; the natural route is that a measure with compact support has
moments growing slowly enough to satisfy a Carleman-type condition, which is a different piece of
analysis from anything built so far.

### Link 112 — bounded powers confine a measure

New module `formal/GaloisForLFunctions/HTGeometry/PowerMomentSupport.lean` (51 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time). Axioms
`[propext, Classical.choice, Quot.sound]`.

`measure_ge_eq_zero_of_pow_integral_le` — `[PROVED HERE]` for nonnegative measurable `f` with
`∫ fⁿ dν ≤ C` for every `n`, and any `t > 1`, **`ν {x | t ≤ f x} = 0`.**

On that set the integrand is at least `tⁿ`, so `(ν A) · tⁿ ≤ ∫_A fⁿ ≤ ∫ fⁿ ≤ C`; if the mass were
positive, `pow_unbounded_of_one_lt` would give an `n` violating it.

**Route correction to link 111.** That entry named a Carleman-type moment-growth condition as the
likely route to closing the remaining gap. That is not needed. The gap — showing that a compactly
supported representative forces *every* representative into the same interval — has an elementary
proof: take `f` to be the normalised distance to the centre of the interval, so `f ≤ 1` on the
compact support; then `∫ fⁿ dμ ≤ s₀` for the compactly supported `μ`, the integrals of `fⁿ` agree
across representatives because `fⁿ` is a polynomial and the moments agree (link 107), and this link
confines the other representative. No growth condition and no quasi-analyticity enter.

Reaching for the named classical theorem was the wrong instinct, for the third time in this card —
after `UniformIntegrable` in link 68 and Cauchy--Schwarz in link 73. The pattern is now well enough
evidenced to state as a rule: when a step looks like it needs a famous theorem, first write down the
inequality the step actually requires; in this development it has never yet been more than a few
lines.

**Opens next:** the instantiation, which is bookkeeping over parts all present. Set `c = (m+M)/2`,
`r = (M−m)/2`, and `f x = |x − c| / r`; then `f ≤ 1` on `[m, M]`, `fⁿ` is not a polynomial but `f^{2n}`
is, so run the argument along even powers only — a detail worth noting before writing, since the odd
powers involve `|·|` and are not reachable by link 107.

### Link 113 — the power bound transfers

New module `formal/GaloisForLFunctions/HTGeometry/CarriedTransfer.lean` (64 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time). Both endpoints
`[propext, Classical.choice, Quot.sound]`.

- `eval_scaled_sq_pow` — the powers of `((x − c)/r)²` are polynomial evaluations, namely of
  `(C (1/r) · (X − C c))^{2n}`.
- `integral_scaled_sq_pow_le` — `[PROVED HERE]` if `μ` is carried by a set where `((x−c)/r)² ≤ 1`, and
  `ν` has the same moments, then **`∫ (((x−c)/r)²)ⁿ dν ≤ s₀` for every `n`.**

The parity detail flagged in link 112 turned out to be avoidable rather than merely manageable. Using
the *square* `((x−c)/r)²` as the base function instead of `|x−c|/r` makes every power a polynomial, so
link 107 applies at every `n` and the odd/even split never arises. Worth noting that the flag was
still useful: it prompted looking for a base function whose powers are all polynomial, which is what
made the problem disappear.

**Opens next:** the conclusion, which is now two routine steps. Feed this bound into link 112 with
`f x = ((x−c)/r)²` and `C = s₀` to get `ν {x | t ≤ f x} = 0` for every `t > 1`; then
`{x | 1 < f x} = ⋃ₖ {x | 1 + 1/(k+1) ≤ f x}` is a countable union of null sets, so `ν` gives no mass
to `{|x − c| > r}` — that is, `ν` is carried by `[m, M]` as well. With link 111 the two measures are
then equal, closing the gap identified there: a compactly supported representative is determinate
against *all* representatives, so an indeterminate sequence has none, and by links 105--106 its Gauss
nodes are unbounded — which is the divergence that link 88 asked for.

### Link 114 — determinacy from one compactly carried representative

New module `formal/GaloisForLFunctions/HTGeometry/CarriedConclusion.lean` (86 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time). All endpoints
`[propext, Classical.choice, Quot.sound]`.

- `sq_gt_one_iff_notMem_Icc` — `1 < ((x−c)/r)²` exactly off `[c−r, c+r]`.
- `measure_compl_Icc_eq_zero_of_moments_eq` — `[PROVED HERE]` **a second representative is carried by
  the same interval.** Link 113's bound feeds link 112 to kill each `{x | 1 + 1/(k+1) ≤ f x}`, and the
  complement of the interval is their countable union.
- `measure_eq_of_moments_eq_of_one_carried` — `[PROVED HERE]`

  > **If some representing measure is carried by a compact interval, every representing measure
  > equals it.**

This closes the gap identified in link 111, which was careful to record that compact-versus-compact
determinacy is weaker than what was needed. The missing implication is now proved, so the statement is
determinacy proper: one compactly supported representative forces uniqueness outright.

Consequently an indeterminate moment sequence has no compactly supported representing measure, and by
links 105--106 its Gauss nodes are unbounded — the divergence asked for in link 88 and pursued since.

**A note on the set identity.** The first attempt at `sq_gt_one_iff_notMem_Icc` tried to manipulate
`abs_le`, `not_and_or` and case splits directly and produced an unusable goal. Rewriting it as
"membership in the interval is `|x − c| ≤ r`" first, then clearing the division once with
`lt_div_iff₀`, made both directions single `nlinarith` calls. Converting to the absolute-value form
*before* touching the inequality is the move; the reverse order fights the `Icc` unfolding.

**Opens next:** the divergence is now a corollary rather than a conjecture, but it has not been
written as a Lean statement — the chain runs through several links and deserves a single named
theorem. That assembly is the natural next step: `gaussNode h n (Fin.last n)` is unbounded whenever
the sequence admits two distinct representing measures.

### Link 115 — the weak limit inherits a carrying set

New module `formal/GaloisForLFunctions/HTGeometry/LimitCarrier.lean` (40 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time). Both endpoints
`[propext, Classical.choice, Quot.sound]`.

- `measure_eq_zero_of_isOpen_le_liminf` — `[PROVED HERE]` if the portmanteau open-set inequality holds
  and every approximant gives an open `U` no mass, the limit gives it none either. Three lines:
  `μ U ≤ liminf 0 = 0`.
- `gaussMeasure_eq_zero_of_disjoint_nodes` — a Gauss measure gives no mass to a measurable set
  avoiding its nodes.

**Why this link exists, and a correction to link 114's handoff.** That entry said the node divergence
"is now a corollary rather than a conjecture". Checking the chain before writing it, that was too
strong. Links 105--106 give *bounded support ⟹ bounded nodes*; the divergence needs the converse,
*bounded nodes ⟹ some representative compactly supported*, which was nowhere proved. The route is:
bounded nodes make every Gauss measure vanish off a fixed interval, and the weak limit of link 70
then vanishes there too — but that last step is exactly the ingredient this link supplies, and it was
missing. So link 114 overstated the state; the corollary needed a new lemma, not just assembly.

**Opens next:** the assembly, now genuinely just assembly. If `gaussNode h n (Fin.last n) ≤ B` for
all `n` and the nodes are also bounded below, every `gaussMeasure s n` vanishes on `(Icc (−B') B')ᶜ`
by the second theorem here, so the weak limit does by the first, so the limit is a compactly supported
representing measure, so by link 114 the sequence is determinate. Note the lower bound is needed and
is *not* available: the lower extreme node was deferred at link 103 precisely because of the parity
bookkeeping. Closing the divergence therefore requires going back for that deferred mirror — which is
worth recording plainly rather than discovering again at assembly time.

### Link 116 — the approximants' carrier, and a correction to link 115

`LimitCarrier.lean` now 60 lines, zero placeholders. Both new endpoints
`[propext, Classical.choice, Quot.sound]`; compiled first try.

- `gaussProb_eq_zero_of_disjoint_nodes` — the normalised Gauss measure gives no mass to a set
  avoiding its nodes.
- `gaussProb_compl_eq_zero_of_nodes_mem` — `[PROVED HERE]` **if every level's nodes lie in `[−B, B]`,
  every Gauss measure vanishes off it.**

**Correction to link 115.** That entry concluded the divergence assembly "requires going back for
that deferred mirror", the lower extreme node of link 102/103, and recorded the parity bookkeeping as
unavoidable. Re-examining before starting it: that is wrong. The lower extreme node is needed for
*strict interlacing counting*, which is a different goal. For the determinacy assembly the natural
statement takes node-boundedness as a **hypothesis** —

> if all nodes of all levels lie in a fixed compact interval, the sequence is determinate

— and a hypothesis needs no existence proof for the extreme nodes at all. The mirror stays deferred
and is not on this path.

Two turns in a row a handoff proved optimistic on inspection, and this one was optimistic in the
opposite direction: link 115 declared a prerequisite that is not one. Tracing dependencies before
writing has now corrected the record in both directions, which is the point of doing it.

**Opens next:** the assembly proper. What is still missing is not a lemma but a *refactor*: link 79's
`exists_probabilityMeasure_hasMoments` discards the subsequence `φ` and the open-set inequality it
was built from, so the carrier information cannot be attached to its output. The construction of
links 70--79 needs re-exposing with those retained — a variant returning `μ`, `φ`, and the
portmanteau hypothesis together — after which link 115 applies to the limit and links 105--114 close
the argument.

### Link 117 — bounded nodes force determinacy

Two changes, both clean.

**Refactor of `HamburgerExistence.lean`.** The construction of links 70--79 discarded the subsequence
`φ` and the portmanteau inequality, so no caller could attach carrier information to the limit
(link 116). The body is now `hasMoments_of_tendsto`, which takes `μ`, `φ`, `hopen` and `hlim` as
hypotheses; `exists_probabilityMeasure_hasMoments` is a two-line wrapper around it with the same
statement as before, so nothing downstream changed and no dependent needed rebuilding.

**New module `formal/GaloisForLFunctions/HTGeometry/BoundedNodesDeterminate.lean`** (50 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time; compiled first try).
All endpoints `[propext, Classical.choice, Quot.sound]`.

- `exists_carried_representative_of_nodes_bounded` — `[PROVED HERE]` **if every level's nodes lie in
  `[−B, B]`, the sequence has a representing probability measure carried by `[−B, B]`.** Link 116
  makes each Gauss measure vanish off the interval, link 115 passes that to the weak limit, and the
  refactored `hasMoments_of_tendsto` supplies the moments for the same limit.
- `determinate_of_nodes_bounded` — `[PROVED HERE]` **bounded nodes force determinacy**: any finite
  measure with the normalised moments equals that limit, via `measure_eq_of_moments_eq_of_one_carried`
  (link 114).

Contrapositively, an indeterminate moment sequence has Gauss nodes escaping every compact interval.
That is the divergence pursued since link 88, and it needed neither the deferred lower extreme node
(link 116's correction) nor a Carleman condition (link 112's correction).

**Opens next:** the statement just proved is conditional on node-boundedness as a hypothesis. To
apply it to a specific sequence one must exhibit the indeterminacy — two distinct representatives —
and the card's own `ClassicalNevanlinnaExtremalFamily` is precisely a package of many. So the natural
next connector is: given such a family with two distinct leaves, conclude that the nodes are
unbounded. That is a short derivation and would close the loop between the extremal-family interface
this card began with and the node theory built since.

### Link 118 — the contrapositive, in usable form

`BoundedNodesDeterminate.lean` now 89 lines, zero placeholders. Both new endpoints
`[propext, Classical.choice, Quot.sound]`; compiled first try.

- `measure_eq_of_nodes_bounded` — `[PROVED HERE]` bounded nodes make **any two** finite measures with
  the normalised moments equal, both being equal to the carried representative.
- `exists_node_outside_of_measure_ne` — `[PROVED HERE]` **two distinct representatives force a node
  outside any given `[−B, B]`.**

**Why the first was needed.** Link 117's `determinate_of_nodes_bounded` concluded
`∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) = nu`, with `μ` existentially bound. Two applications of
it, to two different `nu`, produce two *unrelated* existentials and do not compose into `nu₁ = nu₂` —
the shared identity of the constructed measure is exactly what the existential hides. Obtaining the
representative once and equating both measures to it fixes this. Worth recording as a pattern: a
uniqueness statement phrased existentially is not a uniqueness statement.

With this, the arc from link 88 closes in usable form: an indeterminate moment sequence — one with
two distinct representatives — has Gauss nodes escaping every compact interval.

**Opens next:** connecting to `ClassicalNevanlinnaExtremalFamily`, which packages many
representatives as `leaf t` with `leaf_moments : ∀ t, HasHamburgerMoments s (leaf t)`. Note the
normalisation mismatch: the leaves represent `s` exactly, while the statements here take moments
`(s₀)⁻¹ s`. A leaf `ν` has total mass `s₀`, so `(s₀)⁻¹ • ν` is the probability measure to feed in, and
the connector needs that rescaling plus the observation that distinct leaves stay distinct after
scaling by a positive constant. Neither step is deep, but the mismatch is real and should be handled
explicitly rather than assumed away.

### Link 119 — the normalisation connector

New module `formal/GaloisForLFunctions/HTGeometry/LeafNodeDivergence.lean` (67 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time). All endpoints
`[propext, Classical.choice, Quot.sound]`.

- `smul_measure_ne` — scaling by a nonzero finite constant is injective on measures; multiply back
  by the inverse.
- `integral_pow_smul_normalise`, `integrable_pow_smul_normalise` — the normalisation
  `(ofReal s₀)⁻¹ • ν` of a representing measure has the normalised moments and integrates every power.
- `exists_node_outside_of_hasMoments_ne` — `[PROVED HERE]`

  > **Two distinct measures with `HasHamburgerMoments s` force a Gauss node outside any given
  > `[−B, B]`.**

This is the mismatch flagged in link 118, handled rather than assumed away: the project's
`HasHamburgerMoments s ν` means `∫ xᵏ dν = s_k` exactly, while the node theory is phrased for
`s_k / s₀`, and the bridge is a rescaling whose injectivity is what preserves distinctness.

The statement is now in the vocabulary the rest of the tree uses. Any construction anywhere in this
project producing two distinct measures with `HasHamburgerMoments s` — the extremal family's leaves
being the intended source — yields unbounded Gauss nodes with no further work.

**Opens next:** applying it to `ClassicalNevanlinnaExtremalFamily` needs two *distinct* leaves, and
distinctness is not part of that structure: its fields give continuity, carriers and moments, but
nothing asserts `leaf t₁ ≠ leaf t₂` for `t₁ ≠ t₂`. Injectivity of the leaf map would follow from the
carrier conditions — `finite_carried` puts `leaf tau` on the zero set of `B(x)τ − D(x)`, and those
sets are disjoint for distinct `τ` — so the connector to build next is that disjointness, which is a
statement about the Nevanlinna matrix data rather than about measures.

### Link 120 — the denominator fibers are disjoint

New module `formal/GaloisForLFunctions/HTGeometry/DenominatorFiberDisjoint.lean` (59 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time; compiled first try).
All endpoints `[propext, Classical.choice, Quot.sound]`.

- `D_ne_zero_of_B_eq_zero` — the determinant condition `A D − B C = 1`, a field of
  `ClassicalNevanlinnaMatrixData`, forbids `B` and `D` vanishing together.
- `disjoint_finiteDenominatorFiber` — `[PROVED HERE]` **fibers of distinct finite parameters are
  disjoint.** A common point gives `B x · τ₁ = D x = B x · τ₂`, hence `B x = 0` and then `D x = 0`.
- `disjoint_finite_infinityDenominatorFiber` — likewise for a finite fiber against the fiber at
  infinity.

This is the input link 119 identified as missing from `ClassicalNevanlinnaExtremalFamily`: nothing in
that structure asserts distinct leaves, but `finite_carried` places `leaf tau` on
`finiteDenominatorFiber tau`, and these sets are now known to be pairwise disjoint.

Note where the content actually lives. The disjointness is not a fact about measures or about the
moment problem — it is two lines of algebra from the determinant normalisation, which links 44--51
worked to establish (`orthonormalWronskian_eq`, `nevA_mul_nevD_sub_nevB_mul_nevC = 1`). The
determinant condition earns its keep here rather than in the Nevanlinna parametrisation it was proved
for.

**Opens next:** distinctness of leaves still needs one more step. Disjoint carriers make two leaves
distinct only if at least one of them is *nonzero* on its carrier — two measures both vanishing
identically are equal regardless of where they are carried. Each leaf is a probability measure, so it
has total mass `1`, and `finite_carried` says the complement of its fiber is null; hence the fiber
carries mass `1` and the leaves cannot coincide. That is the argument to write, and it uses
`IsProbabilityMeasure` rather than anything about fibers — worth noting so the next step is not
mistaken for a corollary of this one.

### Link 121 — distinct parameters give distinct leaves

New module `formal/GaloisForLFunctions/HTGeometry/LeafDistinct.lean` (50 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time). Both endpoints
`[propext, Classical.choice, Quot.sound]`.

- `one_le_leaf_fiber` — a leaf gives its own fiber mass at least `1`, by subadditivity against
  `finite_carried` and `measure_univ`.
- `leaf_ne_of_ne` — `[PROVED HERE]` **distinct finite parameters give distinct leaves.** The second
  fiber sits inside the complement of the first (link 120), which is null for the first leaf; equal
  leaves would give that set both `≥ 1` and `0`.

The measurability point flagged in link 120 mattered. `ClassicalNevanlinnaExtremalFamily` does not
assert its denominator fibers are measurable, so `measure_compl` — which needs it — is unavailable,
and the natural "mass one minus null complement" phrasing cannot be used. Subadditivity
(`measure_union_le`) and monotonicity (`measure_mono`) require no measurability at all, and both
steps go through with them. Choosing the weaker tools was not a stylistic preference; the stronger
ones do not apply.

**The chain from link 88 is now complete in the tree**, though not yet as one theorem: an extremal
family with two distinct finite parameters has two distinct leaves (here), each representing `s`
(`leaf_moments`), so by link 119 the Gauss nodes escape every compact interval.

**Opens next:** writing that composite as a single named theorem — `ClassicalNevanlinnaExtremalFamily
s` plus `t₁ ≠ t₂` gives `∃ n, ∃ ξ ∈ gaussNodes s n, ξ ∉ Icc (−B) B`. Two hypotheses need checking
before it will typecheck: link 119 wants `IsFiniteMeasure` on each leaf, which follows from
`ProbabilityMeasure` but must be supplied as an instance, and it wants `PositiveMomentForm s`, which
the family does not carry — though `positiveMomentForm_iff_exists_representing` (link 81) derives it
from a leaf, provided the leaf's support is infinite, which is exactly what `finite_carried` does not
by itself guarantee.

### Link 122 — the composite: indeterminate families have diverging nodes

`LeafDistinct.lean` now 66 lines, zero placeholders. The new endpoint is
`[propext, Classical.choice, Quot.sound]`; compiled first try.

`exists_node_outside_of_extremalFamily` — `[PROVED HERE]`

> **For a positive definite moment form `s` and a `ClassicalNevanlinnaExtremalFamily s` with two
> distinct finite parameters, the Gauss nodes escape every compact interval:
> `∃ n, ∃ ξ ∈ gaussNodes s n, ξ ∉ [−B, B]`.**

This closes the arc opened at link 88. The route, end to end: two distinct parameters give disjoint
denominator fibers (link 120, from the determinant condition), hence distinct leaves (link 121, via
subadditivity since the fibers are not known measurable); each leaf represents `s`, so after
normalisation they are two distinct representatives (link 119); bounded nodes would make the sequence
determinate (links 111--118, through Weierstrass and the confinement estimate); so the nodes are
unbounded.

**On the hypothesis.** `PositiveMomentForm s` is taken as an explicit assumption rather than derived
from the family, and this is a genuine limitation rather than a convenience. The family supplies
carriers, continuity and moments; nothing in it forces any leaf to have infinite support, and
`positiveMomentForm_iff_exists_representing` (link 81) needs exactly that. A family whose leaves were
all finitely supported would be consistent with the structure as written and would make `s` only
positive *semi*definite. Recording this as a property the interface does not currently pin down.

**Opens next:** either strengthen the interface or derive the missing condition. The second looks
reachable: the fibers are zero sets of `B(x)τ − D(x)`, and for the analytic `B`, `D` of the Nevanlinna
matrix these are discrete but infinite, which would give infinite support and hence
`PositiveMomentForm` for free. That is a statement about the entire functions of links 49--51 rather
than about the abstract interface, so it belongs with `nevMatrixData` — and it would also be the first
place this card's complex-analytic half is used for something the real half cannot do alone.

### Link 123 — a degenerate direction confines every representative

New module `formal/GaloisForLFunctions/HTGeometry/SemidefiniteCarrier.lean` (68 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time). Axioms
`[propext, Classical.choice, Quot.sound]`.

`exists_carried_of_momentInner_eq_zero` — `[PROVED HERE]` **if `⟪p, p⟫ = 0` for some `p ≠ 0`, every
representing measure is carried by a compact interval.** The pairing is `∫ (eval p)² dν`, so `p`
vanishes `ν`-a.e.; the non-root set is null, the roots are finite, and a finite set of reals sits
inside some `[−B, B]`.

**A better route than link 122 proposed.** That entry suggested deriving the missing
`PositiveMomentForm` hypothesis from analyticity of `B` and `D` — showing their zero sets are
infinite. That would work but pulls in the entire-function theory of links 49--51. The elementary
route is the contrapositive of this link: *if* `s` were only semidefinite, some `p ≠ 0` would have
`⟪p, p⟫ = 0`, confining **every** representative to a compact interval, where link 114 makes them all
equal — contradicting the existence of two distinct leaves. No analyticity, no entire functions, and
the compact-determinacy machinery of links 107--114 is reused rather than duplicated.

That is the fourth time in this card that reaching for heavier theory was avoidable
(`UniformIntegrable`, Cauchy--Schwarz, Carleman, and now analyticity of the Nevanlinna matrix). The
rule stated at link 112 keeps holding.

**Opens next:** the derivation itself — `positiveMomentForm_of_two_representatives`, taking two
distinct representing measures and producing `PositiveMomentForm s` by the argument above. With it,
`exists_node_outside_of_extremalFamily` (link 122) loses its explicit hypothesis and the composite
becomes a statement about the family alone. The one piece of care needed: extracting `p` from
`¬ PositiveMomentForm s` goes through `not_forall` and `not_imp` on the structure's single field, and
`not_lt` turns the negated strict positivity into `⟪p, p⟫ ≤ 0`, which combines with nonnegativity to
give the equality this link consumes.

### Link 124 — the hypothesis discharged

`SemidefiniteCarrier.lean` now 116 lines, zero placeholders. Both new endpoints
`[propext, Classical.choice, Quot.sound]`.

- `positiveMomentForm_of_two_representatives` — `[PROVED HERE]` **two distinct representing measures
  force `PositiveMomentForm s`.** A degenerate direction would confine both to a common compact
  interval (link 123, taking the larger of the two radii), where link 114 makes them equal.
- `exists_node_outside_of_extremalFamily_unconditional` — `[PROVED HERE]`

  > **An extremal family with two distinct finite parameters has Gauss nodes outside every compact
  > interval.**

  No positivity hypothesis: the two distinct leaves supply it.

This removes the limitation recorded in link 122, where `PositiveMomentForm s` had to be assumed
because the family's fields do not pin it down. They do not — but two distinct leaves do, which is a
different and better answer than the one link 122 anticipated.

**Toolchain note.** `not_imp` is ambiguous between `_root_.not_imp` and `Classical.not_imp` in this
toolchain, and the root one is deprecated in favour of the classical one; the ambiguity surfaces as an
`Ambiguous term` error followed by a spurious `rcases` failure on a metavariable, which reads as a
destructuring problem rather than a name-resolution one.

**State of the card's original goal.** `ClassicalNevanlinnaExtremalFamily` has seven fields. Three
were already built (`matrix`, `continuous_B`, `continuous_D`, link 51). The remaining four — `leaf`,
`continuous_leaf`, `finite_carried`, `infinity_carried`, `leaf_moments` — are still open as
*constructions*: this card can now say a great deal about such a family once given, but does not yet
build one. What links 88--124 establish is the theory the construction will need, and one theorem
about any family that exists.

**Opens next:** the construction itself, which is where the deferred analytic obligations concentrate
— the leaf at parameter `τ` is to be supported on the zero set of `B(x)τ − D(x)` with masses `λ(ξ)`,
so it needs those zeros to exist and be discrete, which is the entire-function statement links
49--51 set up and link 123 showed is *not* needed for the theory around the family. It is needed for
the family.

### Link 125 — countable weighted Dirac measures

New module `formal/GaloisForLFunctions/HTGeometry/CountableWeightedDirac.lean` (45 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time; compiled first try).
All endpoints `[propext, Classical.choice, Quot.sound]`.

- `countableWeightedDirac w x := Measure.sum fun n => ENNReal.ofReal (wₙ) • δ_{xₙ}`.
- `lintegral_countableWeightedDirac` — `∫⁻ f = ∑' wₙ · f(xₙ)`, from `lintegral_sum_measure`.
- `countableWeightedDirac_apply`, `countableWeightedDirac_univ` — evaluation on a measurable set, and
  total mass `∑' wₙ`.

The countable analogue of link 63--69's finite weighted Dirac families, needed because a leaf is
carried by the zero set of an entire function — discrete and countable, not finite. Worth noting how
much easier the countable case is than the finite one was: `Measure.sum` has `lintegral_sum_measure`
and `Measure.sum_apply` as single-step lemmas, whereas the `Finset` version required an induction for
each of integrability, integral, and evaluation. The infinite object has the better API.

**Opens next:** the leaf's moments. With the measure available, what must be shown is that
`∑' λ(ξₙ) · ξₙᵏ = s_k` when `{ξₙ}` is the zero set of `B(x)τ − D(x)` — the N-extremal theorem, and
the genuine remaining mathematical content of this card. Two prerequisites are visible and neither is
in the tree: existence and discreteness of those zeros (the entire-function statement deferred since
link 51), and convergence of the series, which is where the `BoundedKernel` estimates of links 47--50
would finally be consumed for their original purpose. Recording both as the open core rather than as
next steps, since each is a development rather than a lemma.

### Link 126 — atoms of a countable family, and the leaf constraint

`CountableWeightedDirac.lean` now 77 lines, zero placeholders. All new endpoints
`[propext, Classical.choice, Quot.sound]`.

- `countableWeightedDirac_singleton` — with distinct points, the atom at `xₘ` is `wₘ`; the series
  collapses by `tsum_eq_single`, the off-diagonal terms vanishing by injectivity.
- `countableWeightedDirac_real_singleton` — the same as a real mass.
- `weight_le_christoffelLimit` — `[PROVED HERE]` **a countable representing measure has each weight
  bounded by the limit Christoffel function at its point.**

The last is the constraint every N-extremal leaf must satisfy, now stated for the object the leaf will
be built from. It follows in two lines from link 58, which bounded the atoms of *any* representing
measure — that link was proved before the countable measure existed and applies to it unchanged.

**What is now known about a leaf before constructing one.** Given points `{ξₙ}` and weights `{wₙ}`
with the countable measure representing `s`: the weights are nonnegative and bounded by `λ(ξₙ)`
(here), the total mass is `s₀` (link 125), the measure is confined to the interval carrying any
compactly supported representative (link 106), and if a second such measure exists the nodes diverge
(link 124). The N-extremal claim is that the first bound is an *equality* — `wₙ = λ(ξₙ)` — which is
what remains unproved.

**Opens next**, unchanged and stated once more as the open core: the equality `wₙ = λ(ξₙ)`, which
needs the zero set of `B(x)τ − D(x)` to be exactly where the mass sits, and convergence of
`∑ λ(ξₙ) ξₙᵏ`. Both are developments requiring the entire-function theory deferred since link 51.
Everything reachable without it now appears to be done: this session added links 51--126, and the
remaining obligations are all on the analytic side.

### Link 127 — the fibers are closed, and link 121 revisited

New module `formal/GaloisForLFunctions/HTGeometry/FiberClosed.lean` (58 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time). All endpoints
`[propext, Classical.choice, Quot.sound]`.

- `isClosed_finiteDenominatorFiber`, `isClosed_infinityDenominatorFiber` — a denominator fiber of a
  matrix with continuous entries is the preimage of `{0}` under a continuous map, hence closed.
- `measurableSet_leaf_fiber` — so a leaf's fiber is measurable, from the family's own
  `continuous_B` and `continuous_D` fields.
- `leaf_fiber_measure_eq_one` — `[PROVED HERE]` a leaf gives its fiber mass **exactly** `1`.

**Correction to link 121's reasoning, though not to its statement.** That entry proved leaf
distinctness using only subadditivity and monotonicity, on the grounds that
`ClassicalNevanlinnaExtremalFamily` "does not assert its denominator fibers are measurable" and so
`measure_compl` was unavailable. The first half is literally true — there is no measurability field —
but the conclusion drawn from it was wrong: measurability *follows* from the continuity fields, which
the structure does carry. The proof given there is still correct and still works; it was simply more
careful than it needed to be, and the sharper `= 1` was available all along.

Worth noting the failure mode: absence of a hypothesis was read as absence of the fact. The structure
was inspected for a measurability field, none was found, and the search stopped there rather than
asking what the other fields imply.

**Opens next:** unchanged — the open core is `wₙ = λ(ξₙ)` and the entire-function input behind it
(link 126). This link does not advance it; it repairs a piece of reasoning and sharpens a bound that
the repair makes accessible. Measurability of the fibers may matter for that core, since the leaf must
be shown to *be* the countable weighted Dirac measure on the fiber, which is a statement about the
fiber as a measurable set.

### Link 128 — leaves are mutually singular

`FiberClosed.lean` now 81 lines, zero placeholders. Both new endpoints
`[propext, Classical.choice, Quot.sound]`; compiled first try.

- `mutuallySingular_leaf` — `[PROVED HERE]` **leaves at distinct finite parameters are mutually
  singular.** The witness is the second fiber: measurable (link 127), null for the first leaf by
  disjointness (link 120), and co-null for the second by `finite_carried`.
- `leaf_restrict_fiber` — a leaf is unchanged by restriction to its fiber.

Mutual singularity is strictly stronger than the distinctness of link 121 and is the right form of the
statement: it says the leaves are not merely different measures but are supported on disjoint sets,
which is what "the extremal family is a genuine parametrisation" should mean. It became available only
once measurability was recognised (link 127) — with subadditivity alone, link 121 could reach
distinctness but not singularity.

**State of the card.** `ClassicalNevanlinnaExtremalFamily` is now surrounded by a substantial theory:
given such a family, its leaves are mutually singular, each concentrated on a closed measurable fiber
of mass one, the moment form is positive definite, the Gauss nodes diverge, and every leaf's atoms are
bounded by the limit Christoffel function. What is still not done is *constructing* a family — the
four remaining structure fields — and that reduces to the open core of link 126.

**Opens next:** the open core is unchanged, and this link does not narrow it. Recording explicitly
that links 125--128 have been consolidation and sharpening around an unmoved frontier: countable
Dirac infrastructure, atom bounds, fiber topology, singularity. The next genuine advance requires the
entire-function statement — zeros of `B(x)τ − D(x)` exist, are discrete, and carry the mass — and no
further rearrangement of the present material will produce it.

### Link 129 — zeros of the Nevanlinna combination are isolated

New module `formal/GaloisForLFunctions/HTGeometry/NevZeroDichotomy.lean` (60 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time; compiled first try). Both endpoints
`[propext, Classical.choice, Quot.sound]`.

- `nevBseries`, `nevDseries` — the `B` and `D` entries as named series.
- `analyticAt_nevCombination` — `[PROVED HERE]` on an open set with uniform kernel bounds,
  `w ↦ B(w)τ − D(w)` is analytic at each of its points, from the two holomorphy results of link 51
  combined by `DifferentiableOn.mul_const` and `.sub`, then `DifferentiableOn.analyticAt`.
- `eventually_eq_zero_or_eventually_ne_zero_nevCombination` — `[PROVED HERE]` **the identity-theorem
  dichotomy: near any such point the combination either vanishes identically or has no other zero
  nearby.**

**A structural finding, from inspecting rather than assuming.** Link 128 asserted the next advance
needs "the entire-function statement" and treated that as a separate obligation. Reading the
signatures of `differentiableOn_nevA/B/C/D_series` shows what it actually is: every one of them takes
an open `U` *together with uniform kernel bounds on `U`* as hypotheses. So holomorphy is available on
any such set already — and extending it to all of `ℂ`, which is what a leaf construction needs, means
supplying those bounds globally. That is precisely the transfer left open in
`ComplexKernelTransfer.boundedKernel_of_isClosed` since link 50.

**The card's two open problems are one.** The leaf construction (open core, link 126) and the global
kernel transfer (deferred, link 50) are the same obstruction viewed from the real and complex sides.
The dichotomy proved here is everything the identity theorem gives without it; discreteness of the
zero set on `ℝ` follows immediately once the bounds are global, since the second alternative would
then hold at every point where the combination is not locally zero.

**Opens next:** the closedness of `{z | BoundedKernel s z}`. Every route this card has taken now
terminates there. Worth attempting directly rather than approaching further from the sides — links
125--129 have each been one step from it and none has moved it.

### Link 130 — diagnosing the transfer failure, and the tunable fix

New module `formal/GaloisForLFunctions/HTGeometry/TunableAbsorption.lean` (38 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time). Both endpoints
`[propext, Classical.choice, Quot.sound]`.

**Diagnosis, confirmed against the statements rather than recalled.** Reading
`kernelRoot_sq_le_absorption`, `kernelRoot_bounds_propagate` and `transferRadius`:

- the absorption reads `K_w² ≤ 2·K_z² + 8(‖w−z‖h₀)²·K_w²·K_z²·P_z²`;
- so the propagated bounds are `2S` and `2P`, **doubling regardless of how small `‖w − z‖` is**;
- and `transferRadius = 1/(4h₀SP)` therefore quarters at each step.

The doubling is not an artifact of the *displacement* being large — it is the constant `2` in
`(a+b)² ≤ 2a² + 2b²`, applied when the triangle inequality is squared. That constant is what makes
chaining cover only a bounded region, which is the obstruction recorded at link 50 and inherited by
every route since.

**The fix.** `sq_add_le_tunable` — `[PROVED HERE]` `(a + b)² ≤ (1+ε)a² + (1+ε⁻¹)b²` for every `ε > 0`,
with **no sign hypotheses**: the identity `ε a² + ε⁻¹ b² − 2ab = ε⁻¹(εa − b)²` needs none, and the two
nonnegativity assumptions initially written were flagged as unused by the linter. `sq_add_le_two` is
the case `ε = 1`, recovering the constant currently used.

With a tunable leading constant the propagated bound is `√(1+ε)·S` rather than `2S`. Choosing
`ε = εₙ` summable along a chain makes `∏ √(1+εₙ)` converge, so the bounds stay uniformly bounded and
the radii `1/(4h₀SₙPₙ)` stay bounded *below* — and a chain with radii bounded below reaches every
point of `ℂ`. That is the route to closedness, and hence to the global transfer, the leaf
construction, and the discreteness of link 129.

**Opens next:** re-derive `kernelRoot_sq_le_absorption` with the tunable constant. The proof there
squares a triangle inequality on `kernelRoot`; substituting this lemma at that step gives
`K_w² ≤ (1+ε)K_z² + (1+ε⁻¹)·8(‖w−z‖h₀)²·K_w²K_z²P_z²`, from which a tunable analogue of
`kernelRoot_bounds_propagate` follows with bound `√(1+ε)·S` and a correspondingly smaller radius.

### Link 131 — the Duhamel estimate, tunable

New module `formal/GaloisForLFunctions/HTGeometry/TunableDuhamel.lean` (53 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time). Both endpoints
`[propext, Classical.choice, Quot.sound]`.

- `normSq_monicOrthoC_duhamel_le_tunable` — `[PROVED HERE]` the squared Duhamel bound with leading
  constant `1 + ε` for any `ε > 0`.
- `normSq_monicOrthoC_duhamel_le_two` — the `ε = 1` case, recovering the constant currently in
  `ComplexSecondKind`.

`ComplexSecondKind` is untouched. `norm_monicOrthoC_duhamel_le_of_le` there is the *unsquared*
estimate `‖Qₙ(w)‖ ≤ a + b` with no constant at all, so squaring it with `sq_add_le_tunable` (link 130)
instead of the fixed `2` is a two-line derivation on top of existing material — the constant was never
baked into the analysis, only into the squaring step.

**Toolchain note, and a repeat.** `norm_num at h1` silently rewrote `monicOrtho s 0` to `1` via the
`@[simp]` lemma `monicOrtho_zero`, leaving the hypothesis and the goal syntactically different and
`linarith` unable to connect them. This is the same trap recorded much earlier in this card. The fix
is a targeted `rw [inv_one]` rather than a general normaliser: near `monicOrtho s 0`, blanket
simp-normalisation is unsafe.

**Opens next:** the tunable absorption. `kernelRoot_sq_le_absorption` sums the pointwise bound over
`n ≤ N`; substituting this link's version gives `K_w² ≤ (1+ε)K_z² + (1+ε⁻¹)·(…)K_w²K_z²P_z²`, and the
smallness condition of `kernelRoot_bounds_propagate` becomes
`(1+ε⁻¹)(…)S²P² ≤ ε/(1+ε)` or similar, yielding bound `√(1+ε)·S` in place of `2S`. The radius shrinks
as `ε → 0`, which is the trade the chaining argument then has to balance — that balance, not the
inequality, is where the remaining work is.

### Link 132 — the chaining balance is achievable

New module `formal/GaloisForLFunctions/HTGeometry/ChainBalance.lean` (47 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time). Axioms
`[propext, Classical.choice, Quot.sound]`.

`exists_summable_sqrt_not_summable` — `[PROVED HERE]` **there are positive `εₙ` with `∑ εₙ`
convergent and `∑ √εₙ` divergent**, witnessed by `εₙ = 1/(n+1)²`.

Link 131 closed by identifying the balance as the remaining difficulty: a tunable step with parameter
`ε` multiplies the bound by `√(1+ε)` and permits a step of length `∝ √ε`, so chaining to all of `ℂ`
needs `∏(1+εₙ)` bounded *and* `∑ √εₙ` divergent, and it was not clear both could hold. They can, and
the witness is elementary.

**This settles why the current transfer fails.** With `ε = 1` fixed — the constant `2` in the present
absorption — the growth is `2ⁿ` and the step lengths shrink like `4⁻ⁿ`, whose sum is finite: chaining
covers a bounded region, exactly as observed at link 50. The failure is not geometric and not a
missing analytic input; it is a fixed parameter sitting at the wrong point of a trade-off that admits
a good point. Links 130--132 have located that point.

**Opens next:** the tunable absorption itself, which is the one step of links 130--132 not yet taken.
`kernelRoot_sq_le_absorption` sums the pointwise bound over `n ≤ N`; substituting
`normSq_monicOrthoC_duhamel_le_tunable` (link 131) and keeping the fixed constant `2` on the *inner*
squaring — harmless, since it multiplies the small term — gives

`K_w² ≤ (1+ε) K_z² + 4(1+ε⁻¹) (‖w−z‖h₀)² K_w² K_z² P_z²`,

whence a propagate step with bound `√(1+ε)·S` and smallness condition scaling like `ε/(1+ε⁻¹)`, i.e.
step length `∝ √ε` as link 132 assumes. Writing it is a re-derivation of a sixty-line summation proof
with two constants changed, which is bookkeeping rather than mathematics — but it is the step that
turns this analysis into a theorem, and it has not been done.

### Link 133 — the pointwise step of the tunable absorption

New module `formal/GaloisForLFunctions/HTGeometry/TunableAbsorptionStep.lean` (78 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time). Axioms
`[propext, Classical.choice, Quot.sound]`.

`normSq_duhamel_div_le_tunable` — `[PROVED HERE]` the summand bound

`‖Qₙ(w)‖²/hₙ ≤ (1+ε)·(‖Qₙ(z)‖²/hₙ) + 2(1+ε⁻¹)·D²·K_w²·((‖Qₙ(z)‖²P_z² + ‖Rₙ(z)‖²K_z²)/hₙ)`

with `D = ‖w−z‖h₀`. The leading constant is `1 + ε`; the inner squaring keeps the fixed `2`, which is
harmless because it multiplies the displacement term.

Three tactic notes from the build, all about giving the automation less to do:

- `nlinarith` could not get from the Duhamel bound and the inner estimate to the combined one; the
  step is multiplication of a hypothesis by the positive constant `1 + ε⁻¹`, and supplying it as
  `mul_le_mul_of_nonneg_left` reduced the rest to `linarith`.
- `rw [div_le_iff₀ hpos] at *` was the wrong shape — it rewrote the hypotheses too. Collecting the
  right-hand side over a common denominator first, then `gcongr`, leaves exactly the numerator
  inequality already proved.
- `field_simp` closed the collection identity on its own; the following `ring` then failed with
  "no goals". Worth remembering that `field_simp` often finishes rather than merely normalising.

**Opens next:** the summation. Summing this over `n ≤ N` with `kernelRoot_sq` for each of the three
sums gives

`K_w² ≤ (1+ε)K_z² + 4(1+ε⁻¹)D²K_w²K_z²P_z²`,

since `∑ (‖Qₙ(z)‖²P_z² + ‖Rₙ(z)‖²K_z²)/hₙ = 2K_z²P_z²`. That is the tunable analogue of
`kernelRoot_sq_le_absorption`, and with it the propagate step gives bound `√(1+ε)·S` and step length
`∝ √ε`, which links 130--132 have shown suffices.

### Link 134 — the tunable absorption estimate

New module `formal/GaloisForLFunctions/HTGeometry/TunableAbsorptionSum.lean` (67 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time; compiled first try).
Axioms `[propext, Classical.choice, Quot.sound]`.

`kernelRoot_sq_le_absorption_tunable` — `[PROVED HERE]`

> **`K_w² ≤ (1+ε)·K_z² + 4(1+ε⁻¹)·(‖w−z‖h₀)²·K_w²·K_z²·P_z²`** for every `ε > 0`.

This is the estimate links 130--133 were built for, and the constant `2` of
`kernelRoot_sq_le_absorption` is now a free parameter. The proof sums link 133's pointwise bound after
reshaping it into `α·(‖Qₙ(z)‖²/hₙ) + β·(‖Rₙ(z)‖²/hₙ)`, so the three sums are all instances of
`kernelRoot_sq` and the final step is `Finset.sum_add_distrib`, two `Finset.mul_sum`, and `ring`.

Reshaping *before* summing is what made it a first-try build: the alternative — summing the
three-term form and then rearranging — would have required manipulating sums of sums. `field_simp`
plus `ring` handles the reshaping pointwise, where the denominators are a single `hₙ`.

**What this unblocks.** With a tunable leading constant, a transfer step at parameter `ε` gives bound
`√(1+ε)·S` and admits a displacement `∝ √ε`; link 132 shows `εₙ = 1/(n+1)²` makes the growth factors
have bounded product while the displacements sum to infinity. So a chain along such parameters has
uniformly bounded kernel roots and reaches every point of `ℂ` — which is the global transfer, hence
closedness of `{z | BoundedKernel s z}`, hence the entire-function input of link 129 and the leaf
construction of link 126.

**Opens next:** the tunable propagate step — the analogue of `kernelRoot_bounds_propagate`, reading
off from this estimate that if `K_z ≤ S`, `P_z ≤ P` and the displacement satisfies the smallness
condition `4(1+ε⁻¹)(‖w−z‖h₀)²S²P² ≤ ε/(1+ε)`, then `K_w ≤ √(1+ε)·S`. That is an absorption
rearrangement of the same shape as the existing `kernelRootQ_le_of_small`, with the constants carried
through.

### Link 135 — the tunable propagate step

New module `formal/GaloisForLFunctions/HTGeometry/TunablePropagate.lean` (61 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time). Axioms
`[propext, Classical.choice, Quot.sound]`.

`kernelRootQ_sq_le_tunable` — `[PROVED HERE]` if `K_z ≤ S` and `P_z ≤ P` at every level and the
displacement satisfies `4(1+ε⁻¹)(‖w−z‖h₀)²S²P² ≤ δ`, then

`K_w²·(1 − δ) ≤ (1+ε)·S²`.

Stated multiplied out rather than as `K_w² ≤ (1+ε)S²/(1−δ)`: no division appears, and `δ < 1` is not
needed in the statement — a caller supplies whatever `δ` its budget allows and divides itself.

**Tactic note.** The monotonicity step `C·K_z²·P_z² ≤ C·S²·P²` is degree three in the bounded
quantities and `nlinarith` did not find it. `gcongr` does, matching the product structure and
discharging the nonnegativity side conditions from context. Where a goal is a monotone rearrangement
of a product, `gcongr` is the right tool and `nlinarith` is the wrong one — this is the third time in
this card that swapping them fixed a failing step.

**The transfer chain is now assembled** in all its pieces: tunable Young inequality (130), tunable
Duhamel (131), balance witness (132), pointwise step (133), absorption (134), propagate (135). What
remains is to run the chain — pick `εₙ = 1/(n+1)²` and `δₙ` matching, verify that the resulting
growth factors have bounded product and the displacements diverge, and conclude that every point of
`ℂ` lies in `{z | BoundedKernel s z}` once one does.

**Opens next:** that induction. It is a construction over `ℕ` carrying two invariants — a bound
`Sₙ` on the kernel roots and the accumulated displacement — and it is the first genuinely inductive
argument in this stretch; links 130--135 were each single estimates. Worth noting the shape before
starting: the bound at step `n` is `S₀·∏_{k<n} √((1+ε_k)/(1−δ_k))`, and the product converges exactly
when `∑(ε_k + δ_k)` does, which link 132's witness arranges.

### Link 136 — controlling the accumulated growth

New module `formal/GaloisForLFunctions/HTGeometry/ProdOneAddBound.lean` (33 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time; compiled first try). Both endpoints
`[propext, Classical.choice, Quot.sound]`.

- `prod_one_add_le_exp_sum` — `∏_{k<n} (1 + aₖ) ≤ exp (∑_{k<n} aₖ)` for nonnegative `aₖ`, from
  `1 + x ≤ exp x` termwise and `Real.exp_sum`.
- `prod_one_add_le_exp_tsum` — with `a` summable the bound is `exp (∑' aₖ)`, **uniform in `n`**.

This is the invariant-control lemma the chain needs: link 132 supplies summable parameters, and this
turns their summability into a single bound valid at every step.

**A reframing worth recording.** Link 135 described the remaining work as running a chain to prove
*closedness* of `{z | BoundedKernel s z}`. Examining what the tunable estimate actually gives: it does
**not** yield closedness directly. A limit point `z` of good points has approximating `z_k` whose
bounds `S_k, P_k` may blow up, and the smallness condition needs `‖z − z_k‖ ≲ 1/(S_k P_k)`, which the
convergence `z_k → z` does not supply.

What it gives instead is better: a chain from a *fixed* good point `z₀` reaches every `z` at finite
distance, because the step lengths are `∝ √εₖ` with divergent sum (link 132) while the bounds stay
below `S₀·exp(∑εₖ/2)` (here). That is the global transfer directly —
`BoundedKernel s z₀ → ∀ z, BoundedKernel s z` — and it makes
`ComplexKernelTransfer.boundedKernel_of_isClosed`, which assumed closedness as a hypothesis,
unnecessary rather than dischargeable. The goal all along was the conclusion, not the hypothesis.

**Opens next:** the chain construction. Finitely many steps suffice, since the target is at finite
distance and the step lengths have divergent sum — so this is a bounded induction, not a limiting
argument. The invariant at step `k` is a pair: the kernel bounds `Sₖ, Pₖ` and the distance covered.

### Link 137 — the second-kind tunable transfer

New module `formal/GaloisForLFunctions/HTGeometry/TunableSecondKind.lean` (182 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time). All endpoints
`[propext, Classical.choice, Quot.sound]`; both halves compiled first try.

- `normSq_secondKindC_duhamel_le_tunable`, `normSq_secondKind_div_le_tunable` — the squared Duhamel
  and pointwise summand bounds for `secondKindC`.
- `kernelRootR_sq_le_absorption_tunable` — `P_w² ≤ (1+ε)P_z² + 4(1+ε⁻¹)D²P_w²K_z²P_z²`.
- `kernelRootR_sq_le_tunable` — `P_w²(1−δ) ≤ (1+ε)P²` under the same smallness condition as the
  first-kind step.

**A gap caught before it bit.** `BoundedKernel` constrains *both* kernel roots, so a chain must carry
both bounds — but links 131--135 built the tunable transfer only for the first kind. Checking what the
chain would actually consume surfaced this before the chain was attempted rather than during it. The
second-kind estimates in `ComplexSecondKind` have the same shape with `secondKindC` on the left, so
all four lemmas are mirrors and reused the proof shapes already debugged; the only asymmetry is which
kernel root appears in the displacement factor, `P_w` here against `K_w` there.

**Both halves of the tunable transfer now exist.** Links 130--137 give: tunable Young, tunable Duhamel
and propagate for the first kind, the balance witness, the growth-product bound, and the same for the
second kind.

**Opens next:** the chain itself, and it needs both propagate steps at once — from bounds `(S, P)` at
`z`, a step to `w` gives `(√((1+ε)/(1−δ))·S, √((1+ε)/(1−δ))·P)`, the *same* factor on both, since the
smallness condition and the leading constant are shared. That symmetry is what makes a single scalar
invariant suffice for the induction rather than two independent ones.

### Link 138 — one tunable transfer step

New module `formal/GaloisForLFunctions/HTGeometry/TunableStep.lean` (63 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time; compiled first try). Axioms
`[propext, Classical.choice, Quot.sound]`.

`kernelRoot_bounds_propagate_tunable` — `[PROVED HERE]` **bounds `(S, P)` at `z` give bounds
`(cS, cP)` at `w`, with `c = √((1+ε)/(1−δ))`**, under `ε > 0`, `δ < 1`, and the shared smallness
condition `4(1+ε⁻¹)(‖w−z‖h₀)²S²P² ≤ δ`.

This is the tunable analogue of `kernelRoot_bounds_propagate`, which gave the fixed pair `(2S, 2P)`.
Both halves come from squaring: `K_w²(1−δ) ≤ (1+ε)S²` rearranges to `K_w² ≤ (cS)²`, and taking square
roots of both sides via `Real.sqrt_sq` gives the bound without any division surviving into the
statement.

The factor is literally the same expression on both components — no separate constant for the
second kind — because the two propagate steps of links 135 and 137 share both their smallness
hypothesis and their leading constant.

**Opens next:** iterating this. The chain is a finite induction: from a good `z₀` with bounds
`(S₀, P₀)`, walk toward a target `z` in steps whose lengths are governed by the smallness condition,
carrying `Sₙ = c₀⋯cₙ₋₁·S₀` and likewise for `P`. Link 136 bounds that product by `exp(∑aₖ)` for
`aₖ` derived from `(εₖ, δₖ)`, and link 132 supplies parameters making the bound uniform while the step
lengths still sum to infinity. Every ingredient is in place; what remains is the induction itself,
carrying the pair (current point, current bound) and terminating once the accumulated displacement
exceeds `‖z − z₀‖`.

### Link 139 — the tuning route does not work, and why

New module `formal/GaloisForLFunctions/HTGeometry/ChainObstruction.lean` (40 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time; compiled first try). Both endpoints
`[propext, Classical.choice, Quot.sound]`.

**Correction to link 132, and to the programme of links 130--138.** Working the chain arithmetic
before building it gives a conclusion opposite to the one recorded at link 132.

Link 132 asserted that a step at parameter `ε` admits displacement `∝ √ε`, and concluded that
`εₖ = 1/(k+1)²` gives summable growth with divergent reach. The first claim holds only with `δ`
*fixed* — and a fixed `δ` makes the growth factor `√((1+ε)/(1−δ))` bounded below by a constant
exceeding `1`, so the product diverges geometrically. Letting `δₖ → 0` as it must, the smallness
condition `4(1+ε⁻¹)D²S²P² ≤ δ` gives

`D² ≲ δ·ε`, hence `D ≲ √(δε)` — **not** `√ε`.

- `sqrt_mul_le_add_div_two` — `[PROVED HERE]` `√(ab) ≤ (a+b)/2`.
- `sum_sqrt_mul_le` — `[PROVED HERE]` `∑ √(δₖεₖ) ≤ (∑δₖ + ∑εₖ)/2`.

Bounded accumulated growth requires `∑εₖ < ∞` and `∑δₖ < ∞` (link 136), and then the total
displacement is finite by the second lemma. **So no choice of parameters lets a chain of these steps
travel arbitrarily far with bounds under control.** The `ε = 1` case of link 50 was not a bad choice
on a good trade-off; the trade-off has no good point.

**What survives.** Links 130--138 are all correct as estimates and remain in the tree: the tunable
Young inequality, the tunable Duhamel, absorption, propagate and one-step transfer for both kinds are
strictly more general than what `ComplexSecondKind` had, and any future argument that needs a leading
constant near `1` can use them. What does not survive is link 130's claim that the constant `2` was
*the* obstruction, and link 132's claim that the balance is achievable. The obstruction is the
multiplicative coupling of `D` to both parameters in the smallness condition, and it is immune to
tuning.

**Opens next.** The global transfer needs an argument not of Duhamel-chaining type — the classical
proofs use normal families or an order/type bound on the entire functions, neither of which reduces to
iterating a local estimate. Recording that the local route is closed, with the reason, so that it is
not reopened: three separate attempts in this card (link 50, link 130, link 138) have now run into the
same wall from different directions.

### Link 140 — discrete Gronwall, and the route that is actually open

New module `formal/GaloisForLFunctions/HTGeometry/DiscreteGronwall.lean` (50 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time). Both endpoints
`[propext, Classical.choice, Quot.sound]`.

- `prod_one_add_eq_one_add_sum` — the telescoping identity
  `∏_{n<N}(1+bₙ) = 1 + ∑_{n<N} bₙ ∏_{k<n}(1+b_k)`.
- `discrete_gronwall` — `[PROVED HERE]` a recursion `A N ≤ c + ∑_{n<N} bₙ Aₙ` with `bₙ ≥ 0` is solved
  by `A N ≤ c ∏_{n<N}(1+bₙ)`. Strong induction; no sign hypothesis on `c` is needed and the linter
  caught the one initially written.

**Why this reopens the problem link 139 closed.** Inspecting `monicOrthoC_duhamel` (the identity, not
the coarsened estimate): its inner sums run over `Finset.range (n+1)` — the *same* index as the
left-hand side. The tree's `norm_monicOrthoC_duhamel_le_of_le` then coarsens `kernelRoot … w n` to
`kernelRoot … w N` by monotonicity, which is what turns the recursion into a single absorption with
`K_w` on both sides — and that absorption is what carries the finite radius and the obstruction of
link 139.

Kept in its `n`-indexed form the estimate is a Gronwall recursion, and its solution is

`K_w(N)² ≤ 2 K_z(N)² · ∏_{n<N} (1 + 4D² bₙ) ≤ 2 K_z(N)² · exp(4D² ∑ bₙ)`,

with `∑ bₙ ≤ 2K_z²P_z²` — **finite for every displacement `D`**, with no radius at all. The
exponential growth in `D²` is exactly what a chain of local steps cannot produce and what the
classical proofs obtain.

So links 139 and 140 together say: the local *chaining* route is closed, but the local *estimate* was
never the problem — coarsening the index was. The uncoarsened identity is already in the tree
(`monicOrthoC_duhamel`, and `norm_monicOrthoC_duhamel_le` at index `n`).

**Opens next:** assemble the Gronwall transfer — sum the `n`-indexed pointwise bound to get
`A_N ≤ c + ∑_{n<N} bₙ Aₙ` with `A_n = K_w(n)²`, apply `discrete_gronwall`, and bound the product by
`exp` via link 136. The one point needing care: the pointwise bound at index `n` has `K_w(n)` inside,
so the recursion's `∑_{n<N}` must exclude `n = N`, which requires splitting the last term off the sum
before applying the lemma.

### Link 141 — the Duhamel inner sum is strictly partial

New module `formal/GaloisForLFunctions/HTGeometry/DuhamelStrict.lean` (39 lines, zero placeholders,
registered with an exact-line check, olean emitted at write time; compiled first try). Axioms
`[propext, Classical.choice, Quot.sound]`.

`monicOrthoC_duhamel_lt` — `[PROVED HERE]` **the Duhamel identity holds with its inner sums over
`j < n` rather than `j ≤ n`.**

The two `j = n` contributions are `Qₙ(z)·Qₙ(w)Rₙ(z)/hₙ` and `Rₙ(z)·Qₙ(w)Qₙ(z)/hₙ`, which enter with
opposite signs and are equal — so they cancel identically. Splitting both sums with
`Finset.sum_range_succ` and calling `ring` proves it in three lines.

**This is the structural fact the whole transfer question turned on.** With the sums over `j ≤ n`, the
estimate has `K_w(n)` on both sides and must be closed by absorption, which produces the finite radius
and the obstruction of link 139. With the sums over `j < n` it is a genuine recursion: `K_w(n)`
appears on the right only through indices strictly below `n`, so `discrete_gronwall` (link 140)
applies with no absorption and the bound becomes `exp(4D²∑bₙ)` — finite for every displacement.

Three attempts (links 50, 130, 138) failed against the absorption form. None of them examined whether
the absorption was necessary; each took `norm_monicOrthoC_duhamel_le_of_le` as the starting point and
tried to improve what came after. The cancellation was visible in the identity the whole time.

**Opens next:** the estimate at strictly partial index — the analogue of `norm_monicOrthoC_duhamel_le`
derived from this identity, bounding `‖Qₙ(w)‖` in terms of `kernelRoot … w (n-1)` rather than
`kernelRoot … w n`. Then squaring, dividing by `hₙ`, and summing gives the Gronwall recursion in the
exact form link 140 consumes. The same cancellation should hold for `secondKindC_duhamel`, which needs
checking rather than assuming — the two identities are not quite symmetric in the tree.

### Link 142 — the second-kind identity cancels too

`DuhamelStrict.lean` now 57 lines, zero placeholders. Both endpoints
`[propext, Classical.choice, Quot.sound]`; compiled first try.

`secondKindC_duhamel_lt` — `[PROVED HERE]` the second-kind Duhamel identity also holds with inner
sums over `j < n`. Its `j = n` terms are `Qₙ(z)·Rₙ(w)Rₙ(z)/hₙ` and `Rₙ(z)·Qₙ(z)Rₙ(w)/hₙ`, again equal
with opposite signs.

Link 141 flagged that this needed checking rather than assuming, on the grounds that the two
identities are not quite symmetric in the tree — the second-kind one pairs `Qₙ(z)` with a sum of
`RⱼRⱼ` and `Rₙ(z)` with a sum of `QⱼRⱼ`, a different pattern from the first-kind case. The
cancellation nonetheless holds, for the same reason: in both, the two `j = n` terms are the same
product of three factors.

Checking was still right. The reason it works is visible only after writing the terms out, and the
asymmetry in the sums was real — it just did not affect the diagonal.

**Both strict identities are now available**, which is what the Gronwall route needs for both kernel
roots, and hence for `BoundedKernel`.

**Opens next:** the strictly-indexed norm estimates. From these identities, the analogues of
`norm_monicOrthoC_duhamel_le` bounding `‖Qₙ(w)‖` and `‖Rₙ(w)‖` by expressions involving
`kernelRoot … w (n−1)` — note the index shift, since `∑_{j<n}` corresponds to `kernelRoot … (n−1)`
under the tree's convention that `kernelRoot … m` sums over `range (m+1)`. That off-by-one is the
one place this derivation differs from the existing one and is worth handling deliberately: for
`n = 0` the sum is empty and the estimate degenerates to `‖Q₀(w)‖ = ‖Q₀(z)‖`, which is true since both
are `1`.

### Link 143 — the strictly-indexed Duhamel estimate

New module `formal/GaloisForLFunctions/HTGeometry/DuhamelStrictNorm.lean` (45 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time; compiled first try).
Axioms `[propext, Classical.choice, Quot.sound]`.

`norm_monicOrthoC_duhamel_lt_le` — `[PROVED HERE]`

`‖Q_{n+1}(w)‖ ≤ ‖Q_{n+1}(z)‖ + D · K_w(n) · (‖Q_{n+1}(z)‖ P_z(n) + ‖R_{n+1}(z)‖ K_z(n))`

with `D = ‖w−z‖h₀` — the kernel root on the right at index `n`, **strictly below** the `n+1` on the
left.

Stating it at `n+1` rather than `n` was the right move: the identity's sum `∑_{j<n+1}` is exactly the
range that `kernelRoot … n` covers, so `norm_weightedSum_le` applies with no index arithmetic and the
truncated subtraction anticipated in link 142 never arises. The `n = 0` degenerate case also
disappears, since the statement simply starts at index `1`.

**Contrast with the existing estimate.** `norm_monicOrthoC_duhamel_le` has `kernelRoot … w n` against
`‖Qₙ(w)‖` — same index — and `norm_monicOrthoC_duhamel_le_of_le` coarsens further to `N`. This
version breaks that circularity, which is precisely what makes the recursion solvable rather than
absorbable.

**Opens next:** square and sum. Squaring gives
`‖Q_{n+1}(w)‖²/h_{n+1} ≤ 2(‖Q_{n+1}(z)‖²/h_{n+1}) + 4D² K_w(n)² β_{n+1}` with
`β_{n+1} = (‖Q_{n+1}(z)‖²P_z(n)² + ‖R_{n+1}(z)‖²K_z(n)²)/h_{n+1}`, and summing over `n+1 ≤ N` gives
`A_N ≤ 2K_z(N)² + 4D² ∑_{n<N} A_n β_{n+1}` with `A_n = K_w(n)²` — the shape `discrete_gronwall`
consumes, since every `A` on the right has index strictly below `N`. The `n = 0` term of `A_N` must be
handled separately, being `‖Q₀(w)‖²/h₀ = 1/h₀`, which is where the constant `c` in the Gronwall
recursion comes from.

### Link 144 — the strict estimate, squared and divided

`DuhamelStrictNorm.lean` now 112 lines, zero placeholders. The new endpoint is
`[propext, Classical.choice, Quot.sound]`; compiled first try.

`normSq_duhamel_strict_div_le` — `[PROVED HERE]`

`‖Q_{n+1}(w)‖²/h_{n+1} ≤ 2(‖Q_{n+1}(z)‖²/h_{n+1}) + 4D²·K_w(n)²·β_{n+1}`

with `β_{n+1} = (‖Q_{n+1}(z)‖²P_z(n)² + ‖R_{n+1}(z)‖²K_z(n)²)/h_{n+1}`. The kernel root on the right
is at index `n`; the left side is at `n+1`.

The proof reuses the shape of link 133 — square, expand the inner sum with the fixed constant,
collect over the denominator, `gcongr` — with the fixed constant `2` throughout, since the tunable
parameter is not needed here: the Gronwall route does not require the leading constant to approach
`1`, which was the entire purpose of links 130--138. Those remain in the tree as more general
estimates but are not on this path.

**The recursion is now in hand.** Summing over `n+1 ≤ N` gives

`A_N ≤ A_0 + 2K_z(N)² + 4D² ∑_{n<N} A_n β_{n+1}`, `A_n = K_w(n)²`,

every `A` on the right strictly below `N` — exactly `discrete_gronwall`'s hypothesis. The `A_0` term
is `‖Q₀(w)‖²/h₀ = 1/h₀`, a constant independent of `w`, since `Q₀ = 1`.

**Opens next:** perform that summation. Two mechanical points: the sum over `n+1 ≤ N` must be
reindexed to `n < N` (`Finset.sum_range_succ'` splits off the `0` term in the right direction), and
`∑_{n<N} β_{n+1} ≤ 2K_z(N)²P_z(N)²` bounds the Gronwall's growth data — giving a final bound
`exp(8D²K_z²P_z²)` times a constant, finite for every `D`, which is the global transfer.

### Link 145 — the Gronwall recursion

New module `formal/GaloisForLFunctions/HTGeometry/GronwallRecursion.lean` (88 lines, zero
placeholders, registered with an exact-line check, olean emitted at write time). Both endpoints
`[propext, Classical.choice, Quot.sound]`.

- `gronwallWeight s z D n` — the step weight `4D²·β_{n+1}` built from the centre data, with
  `gronwallWeight_nonneg`.
- `monicOrthoC_zero_eq_one` — `Q₀(w) = 1`, so the split-off term is `1/h₀`.
- `kernelRoot_sq_recursion` — `[PROVED HERE]`

  > **`K_w(N)² ≤ (2S² + 1/h₀) + ∑_{n<N} gronwallWeight(n)·K_w(n)²`**

  whenever the centre kernel roots are bounded by `S`.

This is `discrete_gronwall`'s hypothesis exactly: the constant is independent of `N`, each weight is
independent of `N`, and every `K_w` on the right sits at an index strictly below `N`. No absorption,
no smallness condition, and no constraint on the displacement anywhere in the statement.

`Finset.sum_range_succ'` splits off the `n = 0` term at the *bottom* of the range, which is the
direction needed here — the ordinary `Finset.sum_range_succ` peels the top and would have left the
reindexing undone.

**Opens next:** apply the lemma. `discrete_gronwall` gives
`K_w(N)² ≤ (2S² + 1/h₀)·∏_{n<N}(1 + gronwallWeight n)`, and link 136 bounds that product by
`exp(∑ gronwallWeight n)`. Bounding the sum needs `∑_{n<N} β_{n+1} ≤ 2S²P²`, which is the same
computation as the `hcentre` step here run against both `S` and `P` — giving
`K_w(N)² ≤ (2S² + 1/h₀)·exp(8D²S²P²)`, uniform in `N` and finite for **every** `w`. That is the
global transfer.

### Link 146 — the transfer goes global, and the Nevanlinna matrix becomes entire

The Gronwall programme of links 140–145 closes, and it takes the holomorphy capstone with it.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/GlobalTransfer.lean`
- `gronwallWeight_sum_le` — `∑_{n<N} gronwallWeight ≤ 8D²S²P²`, by replacing each centre kernel root
  by its bound and recognising the two remaining sums as `K_z(N)²` and `P_z(N)²` (both via
  `Finset.sum_range_succ'`, which peels the *bottom* term).
- `kernelRoot_sq_global` — `K_w(N)² ≤ (2S² + 1/h₀)·exp(8D²S²P²)` with `D = ‖w−z‖·h₀`, uniform in `N`,
  for **every** `w`. Chain: `discrete_gronwall` → `prod_one_add_le_exp_sum` → the sum bound.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/SecondKindGlobal.lean`
- The second-kind Duhamel identity is driven by `P_w` where the first-kind one is driven by `K_w`,
  but the bracket built from the centre data is *identical* — so `gronwallWeight` is literally the
  same function and the second recursion needs no new weight. Since `R₀ = 0` the constant is `2P²`.
- `secondKind_kernelRoot_sq_global`, then `boundedKernel_global`:
  `BoundedKernel s z → ∀ w, BoundedKernel s w`. **No radius, no chaining, no smallness condition.**

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevanlinnaEntire.lean`
- The Gronwall bound depends on the base point only through `‖z‖`, so it is *uniform on every ball*
  (`kernelRoot_le_ballBoundQ`/`R`). That supplies both inputs `nevanlinna_holomorphic_unimodular`
  was stated modulo — the uniform bounds `Sz, Pz` on `U` and `hUb : ∀ z ∈ U, BoundedKernel s z`.
- `nevanlinna_entire_unimodular` — from `BoundedKernel s 0` alone: all four limiting entries
  `nevAinf, nevBinf, nevCinf, nevDinf` are `Differentiable ℂ` on the whole plane, and
  `A(z)D(z) − B(z)C(z) = 1` for **every** `z ∈ ℂ`.
- `isClosed_boundedKernel` discharges the standing hypothesis of
  `ComplexKernelTransfer.boundedKernel_of_isClosed` and `summable_kernel_everywhere_of_isClosed`.

All endpoints `[propext, Classical.choice, Quot.sound]`, zero placeholders, registered in the
umbrella.

**Opens next:** the matrix is now an entire unimodular `2×2` family, so `B(x)τ − D(x)` is an entire
function of `x` for each fixed `τ ∈ ℝ ∪ {∞}`. Link 129's dichotomy says such a function is either
identically zero or has a discrete zero set; unimodularity rules out the first case (`B` and `D`
cannot share a zero, else the determinant would vanish there). That gives the **discreteness of the
N-extremal support** — the node sequence `ξₙ` — which is the last structural input before the four
open fields `leaf`, `continuous_leaf`, `finite_carried`, `infinity_carried`, `leaf_moments` of
`ClassicalNevanlinnaExtremalFamily`, with the open core `wₙ = λ(ξₙ)`.

### Link 147 — the zeros become isolated on the whole plane

`NevZeroDichotomy` (link 129) could only state the identity-theorem alternative on an open set with
uniform kernel bounds, so the "vanishes identically nearby" branch stayed live. Entirety kills it:
`ℂ` is connected, so one point of non-vanishing rules the branch out everywhere.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevCombinationDiscrete.lean`
- `nevAinf_zero`, `nevBinf_zero`, `nevCinf_zero`, `nevDinf_zero` — the entry values at the origin are
  the classical normalisation `A(0) = 0`, `B(0) = −1`, `C(0) = 1`, `D(0) = 0`. Each is one `simp`:
  the `h₀·z·(series)` factor kills three of them and leaves the bare constant.
- `eventually_ne_zero_of_entire` — the reusable core: an entire `f` nonzero at a single point has
  every zero isolated. `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` for the local
  alternative, `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` + `isPreconnected_univ`
  to discharge the bad branch.
- `nevCombination_at_zero` — `B(0)τ − D(0) = −τ`, so the required point is *free* for every `τ ≠ 0`.
- `eventually_ne_zero_nevCombination` — **for every `τ ≠ 0`, the zeros of `B τ − D` are isolated.**
  These zero sets are the supports of the N-extremal measures.
- `eventually_ne_zero_nevBinf` — the same for `B` alone, i.e. the `τ = ∞` member of the family.
- `nevBinf_ne_zero_or_nevDinf_ne_zero` — `B` and `D` have no common zero; a common zero would make
  the determinant `0` instead of `1`.

Axiom-clean, zero placeholders, registered.

**The one parameter left is `τ = 0`,** where the combination is `−D` and `D(0) = 0` gives no witness.
Ruling it out needs `D ≢ 0`, i.e. `nevDseries s 0 ≠ 0`, since `D(z) = h₀·z·nevDseries(z)` and the
factor `z` is what hides the non-vanishing at the origin.

**Opens next:** do *not* rebuild that from tsum estimates — `ChristoffelBoundedKernel.lean` already
proves `0 < christoffelLimit s x` from `BoundedKernel s (x : ℂ)`, and `christoffelLimit` is the same
series `Σ |Q_k(x)|²/h_k` that `nevDseries s 0` is. So the τ = 0 case should reduce to identifying
`nevDseries s 0` with `christoffelLimit s 0` (via realness of `monicOrthoC s k 0`) and quoting the
existing positivity. That closes the parametrization over all of `ℝ ∪ {∞}` and hands the leaf
construction a discrete node sequence `ξₙ` for every parameter.

### Link 148 — the last parameter closes; discreteness holds across the whole family

Link 147 left `τ = 0` open, where the combination is `−D` and `D(0) = 0` supplies no witness. The
witness was hiding behind the linear factor.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevDSeriesNonzero.lean`
- `nevDinf_eq` — `D(z) = h₀·z·nevDseries(z)`, definitionally (`rfl`). The factor `z` is exactly what
  makes `D(0) = 0` while the series behind it is nonzero.
- `nevDseries_zero_eq` — at the origin the series is the *real* series `∑ₖ Qₖ(0)²/hₖ`, via
  `monicOrthoC_ofReal` and `Complex.ofReal_tsum`.
- `nevDseries_zero_ne_zero` — that series is nonzero: it is a sum of nonnegative terms whose `k = 0`
  term is `1/h₀ > 0` (`Summable.le_tsum`). The summability is the *existing*
  `summable_of_boundedKernel`, rewritten by `normSq_monicOrthoC_ofReal` — the same bridge
  `ChristoffelBoundedKernel` already uses.
- `differentiable_nevDseries`, `exists_nevDinf_ne_zero` — continuity keeps the series nonzero on a
  neighbourhood of `0`, and any point of that neighbourhood other than `0` makes `D` itself nonzero.
- `eventually_ne_zero_nevDinf` — the `τ = 0` member.
- `eventually_ne_zero_nevCombination_all` — **for every `τ ∈ ℂ`, the zeros of `B τ − D` are
  isolated**; with `eventually_ne_zero_nevBinf` (link 147) covering `τ = ∞`, the parametrization is
  closed over all of `ℝ ∪ {∞}`.

Axiom-clean, zero placeholders, registered.

Note on method: the `christoffelLimit` route flagged at the end of link 147 was *not* the shortest
one — `christoffelLimit` is an infimum of Christoffel functions, not the tsum, so identifying it with
`nevDseries s 0` would have gone through more machinery than proving the tsum bound directly. What
did carry over from that file was the smaller piece: the real-evaluation bridge
`monicOrthoC_ofReal` / `normSq_monicOrthoC_ofReal`. That is the fifth time on this card that reaching
for the big named result was longer than writing the needed inequality down.

**Opens next:** every parameter now has a discrete node set. The leaf construction can start: for a
fixed `τ`, enumerate the zeros of `B τ − D` as `ξₙ` and build the measure `∑ₙ wₙ δ_{ξₙ}`. The five
open fields of `ClassicalNevanlinnaExtremalFamily` (`leaf`, `continuous_leaf`, `finite_carried`,
`infinity_carried`, `leaf_moments`) all hang off that enumeration, with the open core still
`wₙ = λ(ξₙ)` — the identification of the Nevanlinna weight with the Christoffel limit, which is
where `christoffelLimit` *will* genuinely be the right object.

### Link 149 — three of the eight family fields are now built, not assumed

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevanlinnaRealMatrix.lean`

The entries have real coefficients, so along `Complex.ofReal` each is the embedding of a real kernel
series. `secondKindC_ofReal` (new, the second-kind twin of the existing `monicOrthoC_ofReal`) plus
`ofReal_bilinear_tsum` give the four bridges `nevAinf_ofReal … nevDinf_ofReal`, and everything
transports along them:

- `nev_realInf_det_one` — the determinant identity on `ℝ`, by `exact_mod_cast` from the complex one.
- `nevMatrixDataInf` — **the `matrix` field of `ClassicalNevanlinnaExtremalFamily`, constructed.**
- `continuous_of_entire_ofReal` — a real entry is `re ∘ f ∘ ofReal` of an entire `f`, hence
  continuous. Gives `continuous_nevMatrixDataInf_B` and `_D`: **the `continuous_B`/`continuous_D`
  fields.**
- `nevMatrixDataInf_finiteDenominatorFiber_eq` / `_infinityDenominatorFiber_eq` — each fiber is the
  real trace of the corresponding complex zero set.
- `tendsto_ofReal_nhdsWithin_ne` — `ofReal` maps punctured neighbourhoods to punctured
  neighbourhoods, which is what carries links 147–148 from `ℂ` down to `ℝ`.
- `eventually_notMem_finiteDenominatorFiber` / `_infinityDenominatorFiber` — **every denominator
  fiber is discrete in `ℝ`**, for every `τ ∈ ℝ ∪ {∞}`. These fibers are the N-extremal supports.

Naming note: `nevAreal … nevDreal` were already taken by `NevanlinnaPluecker` for the *truncated*
level-`n` entries (finite sums, with their own `nevMatrixData` and continuity). Those are a different
object — their fibers are the level-`n` Gauss nodes. The new ones carry the `Inf` suffix, and the
relation between them is the partial-sum convergence of the kernel series.

Axiom-clean, zero placeholders, registered.

**Opens next:** five fields remain — `leaf`, `continuous_leaf`, `finite_carried`,
`infinity_carried`, `leaf_moments`. `finite_carried`/`infinity_carried` say the leaf measure is
carried by the fiber, which the discreteness above now makes a statement about a countable set of
atoms; `CountableWeightedDirac.lean` (link 133) already builds measures of exactly that shape. So the
next construction is the enumeration of a discrete subset of `ℝ` as a sequence `ξₙ`, feeding
`countableWeightedDirac` with weights `wₙ`. The open core is unchanged and is now the *only*
analytic unknown left on this card: `wₙ = λ(ξₙ)` — the Nevanlinna weight is the Christoffel limit,
which is where `christoffelLimit` becomes the right object rather than a detour.

### Link 150 — the fibers are countable; the leaf measure exists and is carried

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevFiberCountable.lean`
- `countable_of_eventually_notMem` — a set of reals with no accumulation point in itself is
  countable. Chain: `discreteTopology_subtype_iff` (via `Filter.inf_principal_eq_bot`), then `ℝ`
  second countable ⇒ the subspace is separable, then `separableSpace_iff_countable`.
- `countable_finiteDenominatorFiber` / `countable_infinityDenominatorFiber` — **every N-extremal
  support is countable**, for every parameter in `ℝ ∪ {∞}`.
- `isClosed_finiteDenominatorFiber` / `_infinityDenominatorFiber` — and closed, being level sets of
  continuous functions. So each support is a closed discrete countable subset of `ℝ`.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/FiberMeasure.lean`
- `fiberMeasure w F` — the weighted sum of point masses **indexed by `F` itself**, not by an
  enumeration of it. This was the right move: it removes the need to list the fiber, and carriedness
  becomes structural rather than a computation.
- `fiberMeasure_apply`, `lintegral_fiberMeasure`, `fiberMeasure_singleton`.
- `fiberMeasure_compl_eq_zero` — **the measure is carried by `F` whatever the weights are.**
- `nevLeafFinite` / `nevLeafInfinity` — the candidate leaves, Christoffel weights on the fiber.
- `nevLeafFinite_carried` / `nevLeafInfinity_carried` — **the content of the `finite_carried` and
  `infinity_carried` fields.**
- `nevLeafFinite_singleton` — the atom at a node is `christoffelLimit` there, which is the shape
  `weight_le_christoffelLimit` (link 133) already constrains.

Correction worth recording: the module was first written with a `(hF : F.Countable)` hypothesis
throughout. The linter flagged it unused, and checking mathlib showed `Measure.sum_apply` and
`lintegral_sum_measure` are stated for an **arbitrary** index type in this toolchain. So the whole
fiber-measure API is countability-free and the hypothesis was dropped — the countability results
above are still needed, but later, where a listing is actually wanted.

All eight modules of links 146–150 verified together: oleans present, zero placeholders, endpoints
`[propext, Classical.choice, Quot.sound]`.

**Status of the eight fields of `ClassicalNevanlinnaExtremalFamily`:** `matrix` ✓, `continuous_B` ✓,
`continuous_D` ✓, `finite_carried` ✓ (content), `infinity_carried` ✓ (content). Remaining: `leaf`
as a `ProbabilityMeasure`-valued map, `continuous_leaf`, and `leaf_moments`.

**Opens next.** The last two both reduce to one statement — `∑_{ξ ∈ F_τ} λ(ξ)·ξ^k = s_k`, with `k = 0`
giving total mass `1` and hence the `ProbabilityMeasure` upgrade. `weight_le_christoffelLimit` gives
`≤` for a representing measure; what is missing is existence.

The route that does not require it as an input: **quasi-orthogonal quadrature.** The zeros of
`Q_{n+1} + t·Q_n` are real and simple, and the associated Christoffel-weighted discrete measure is
exact to degree `2n` — the same structure the Gauss construction of links 1–40 already has
(`GaussQuadratureNodes` → `GaussQuadrature` → `GaussTightness` → `HamburgerExistence`). Any weak limit
of those therefore represents `s`, with no per-`t` moment sequence anywhere — which is what link 83's
refutation actually forbade. Identifying the limit's support with `F_τ` is then the remaining step,
and it is a statement about where the quasi-orthogonal zeros accumulate, not about moments.

### Link 151 — quasi-orthogonal polynomials: `n+1` distinct real roots for every parameter

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/QuasiOrthogonal.lean`

`quasiOrtho s n t = Q_{n+1} + t·Qₙ`, monic of degree `n+1` (`quasiOrtho_monic`, `_degree`).

- `quasiOrtho_aeval_ne_zero` / `_splits` — **all roots are real.** The proof is *kernel-based, not
  interlacing-based*: `kernelSum_mul_im` (already in `ComplexChristoffelDarboux`) says
  `(∑_{k≤n}|Q_k(z)|²/h_k)·Im(z)·hₙ = Im(Q_{n+1}(z)·conj(Qₙ(z)))`. If `Q_{n+1}(z) = −t·Qₙ(z)` with `t`
  real, the right side is `Im(−t|Qₙ(z)|²) = 0`, so the kernel sum vanishes — impossible, its `k = 0`
  term is `1/h₀ > 0`. Reused `splits_of_forall_aeval_im_eq_zero` verbatim.
- `quasiOrtho_not_sq_dvd` — **all roots are simple.** At a root `r`, `Q_{n+1}(r) = −t·Qₙ(r)` collapses
  the two-variable identity to `(x−r)·Kₙ(x,r)·hₙ = Qₙ(r)·(Q_{n+1}(x) + t·Qₙ(x))`. A double root makes
  the right side divisible by `(x−r)²`; cancelling one factor as polynomials (`Polynomial.funext`,
  `mul_left_cancel₀`) and evaluating at `r` gives `Kₙ(r,r)·hₙ = 0`, contradicting
  `cdKernel_eval_self_pos`. **No differentiation** — the same trick `ConfluentDarboux` uses for `Q_{n+1}`.
- `quasiNodes`, `mem_quasiNodes_iff`, `quasiNodes_card` — **exactly `n+1` nodes, for every real `t`.**

Axiom-clean, zero placeholders, registered. One build error: `add_le_add_right` adds on the *left*
despite its name (same trap recorded earlier for `add_le_add_left`); `add_le_add h le_rfl` is the
symmetric form that works.

**Opens next.** Two candidate routes to `leaf_moments`, and they should be compared before building:

1. *Quadrature route.* Interpolatory weights at `quasiNodes` give a rule exact to degree `2n` —
   `quasiOrtho` is orthogonal to everything of degree `< n`, so writing `p = q·P + r` kills the
   quotient term for `deg p ≤ n + n`. Then tightness and a weak limit, exactly as
   `GaussTightness` → `HamburgerExistence` already do. Needs positivity of the interpolatory weights.
2. *Algebraic route.* The transfer matrix `!![Q_{n+1}, R_{n+1}; Qₙ, Rₙ]` (already in
   `SecondKindMomentPolynomials`) is, up to constants, the level-`n` Nevanlinna matrix. If the
   truncated entries `nevBreal s n`, `nevDreal s n` can be written in terms of `Q_{n+1}, Qₙ, R_{n+1}, Rₙ`,
   then "`Bₙ(x)τ − Dₙ(x)` vanishes exactly on a quasi-orthogonal node set" becomes an *identity*
   rather than a limit theorem — and the support identification collapses to Hurwitz on the already
   proved entrywise convergence.

Route 2 would reuse far more and prove more; check the transfer-matrix identities first.

### Link 152 — route 2 wins: the level-`n` denominator *is* a quasi-orthogonal polynomial

Link 151 posed two routes and said to check the transfer-matrix identities first. Checked, and route 2
is not merely shorter — it replaces a limit theorem by an identity.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevDenominatorFactor.lean`

Christoffel--Darboux at `(0, x)` collapses each truncated entry to two terms. Both closed forms went
through on the first `linear_combination`, using the three CD identities already in the corpus
(`christoffelDarboux`, `mixedChristoffelDarboux`, and `momentWronskian_eq`):

- `nevDreal_closed` — `Dₙ(x) = (h₀/hₙ)·(Qₙ(0)·Q_{n+1}(x) − Q_{n+1}(0)·Qₙ(x))`.
- `nevBreal_closed` — `Bₙ(x) = (h₀/hₙ)·(Rₙ(0)·Q_{n+1}(x) − R_{n+1}(0)·Qₙ(x))`.
- `nevDenominator_closed` — hence
  `Bₙ(x)·τ − Dₙ(x) = (h₀/hₙ)·(α·Q_{n+1}(x) + β·Qₙ(x))` with
  `α = τ·Rₙ(0) − Qₙ(0)`, `β = Q_{n+1}(0) − τ·R_{n+1}(0)`.
- `nevAlpha_beta_ne_zero` — **`α` and `β` never vanish together.** Both zero would force the Wronskian
  at the origin to be `0`, but `wronskian_eval_zero` computes it as `−hₙ/h₀ ≠ 0`. So the denominator
  is never the zero polynomial — the finite-level analogue of link 148's non-degeneracy, and here it
  is two lines instead of a continuity argument.
- `nevDenominator_eq_quasiOrtho`, `nevDenominator_zero_iff`, `nevDenominator_zeroSet` — when `α ≠ 0`
  the denominator is a **nonzero constant multiple of `quasiOrtho s n (β/α)`**, so its zero set is
  exactly `quasiNodes s n (β/α)`: **`n+1` distinct real points** by link 151.

Axiom-clean, zero placeholders, registered. (Two familiar traps recurred: `field_simp` closing a goal
so the following `ring` errors, and an unused hypothesis revealing that a statement had been phrased
about the wrong object — restating `zeros_card` as `zeroSet` both used the hypothesis and said the
thing worth saying.)

**Why this matters for the card.** The support identification no longer needs quadrature, tightness,
or weak limits at level `n`. The chain is now: level-`n` denominator → quasi-orthogonal polynomial →
`n+1` simple real nodes; and separately the entries converge (`NevanlinnaPluecker` differentiability
plus links 146–149). So `F_τ`, the limit fiber, is the limit of the level-`n` node sets.

**Opens next:** Hurwitz. `Bₙτ − Dₙ → Bτ − D` locally uniformly on `ℂ` (the entries are the truncations
of the series proved entire in link 148), and `Bτ − D ≢ 0` (link 148 again). Hurwitz's theorem then
says every zero of the limit is a limit of level-`n` zeros, and conversely no zero appears from
nowhere. That identifies `F_τ` with `lim quasiNodes s n (βₙ/αₙ)` and hands the leaf its nodes — the
last structural step before the weights, where the open core `wₙ = λ(ξₙ)` still sits.

### Link 153 — quasi-orthogonal quadrature: exact to order `2n`, with positive weights

Hurwitz turned out to be unavailable: mathlib has neither Hurwitz's theorem nor Rouché nor the
argument principle (checked `Analysis/Complex/` — `JensenFormula` and `LocallyUniformLimit` exist, the
zero-counting theorems do not). Building the argument principle from scratch is a larger project than
the quadrature, and the quadrature is needed by any route, so it went first.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/QuasiQuadrature.lean`

- `quasiOrtho_inner_eq_zero` — `quasiOrtho s n t ⊥` everything of degree `< n`, since *both*
  summands are (`monicOrtho_inner_eq_zero_of_degree_lt` applied at `n+1` and at `n`).
- `quasiWeight` — the interpolatory weight, `momentFunctional` of a `Lagrange.basis` polynomial.
  Mathlib's `Lagrange` (interpolate / basis / `eq_interpolate`) supplied all of the interpolation.
- `momentFunctional_eq_quasiSum_of_degree_lt` — exactness on degrees `< n+1`, straight from
  `Lagrange.eq_interpolate` plus `momentInner_sum_left`.
- `momentFunctional_eq_quasiSum` — **exactness to order `2n`.** Divide by the node polynomial
  (`modByMonic_add_div`): the remainder has degree `< n+1` so the interpolatory rule handles it, and
  the quotient has degree `< n` so it is annihilated by orthogonality — while contributing nothing to
  the sum either, the node polynomial vanishing at every node. The degree bookkeeping needs the
  `p /ₘ P = 0` case split (`divByMonic_eq_zero_iff`), which is what makes `n = 0` work.
- `quasiWeight_pos` — **every weight is strictly positive.** `bₓ²` has degree `2n`, so the rule is
  exact on it; the sum collapses to `wₓ`, and the value is `momentInner s bₓ bₓ > 0` by positive
  definiteness. Note the order: exactness to `2n` is proved *first* and used to prove positivity, so
  there is no circularity.

One order short of the Gauss rule's `2n+1`, which costs nothing in the limit.

Axiom-clean, zero placeholders, registered. Five build iterations, all mechanical: `ring` cannot see
through `id x` vs `x` (three separate spots — `simp only [id_eq]` first), and `set` folds a definition
in the goal so a later `rw` of that definition no longer matches.

**Opens next:** the measure. `quasiMeasure s n t := ∑_{x ∈ quasiNodes} wₓ·δₓ` is now a *positive*
finite measure whose moments agree with `s` up to order `2n` — precisely the hypothesis shape the
existing chain consumes. `GaussTightness` → `GaussMomentLimit` → `HamburgerExistence` should port with
`2n+1` replaced by `2n` throughout; the tightness estimate only needs the even moments to be
eventually correct, which they are. That yields, for each parameter, a representing measure obtained
as a weak limit of quasi-orthogonal rules — and then the remaining question is the one Hurwitz would
have answered directly: that the limit is carried by `F_τ`.

### Link 154 — the quasi family carries the whole existence chain

**[PROVED HERE]** three modules, all first-try compiles except two mechanical fixes.

`QuasiMeasure.lean` — `quasiMeasure s n t = ∑_{ξ} w_ξ·δ_ξ`, with `quasiMeasure_moment`: **the moments
agree with `s` up to order `2n`**, plus finiteness and integrability. One genuine difference from the
Gauss case had to be handled: the Gauss file's integration lemma assumes the weight function is
nonnegative *everywhere*, which is false here — away from the nodes a Lagrange functional has no
sign. Restated as `integral_finsetWeightedDirac_of_mem`, requiring nonnegativity on the node set only.

`QuasiTightness.lean` — `quasiNodes_tail_weight_le`: a node beyond `R` contributes at least `R²`
times its weight to `∑ w·ξ² = s₂`, so the tail is at most `s₂/R²` — **uniform in the level and in the
parameter**. Hence `isTightMeasureSet_quasiProb` and `isCompact_closure_quasiProbMeasure` for an
*arbitrary sequence* `τ : ℕ → ℝ` of parameters. That generality is not decoration: the parameter
selecting a leaf varies with the level, so a fixed-parameter tightness result would have been useless
here.

`QuasiMomentLimit.lean` — the full port: `lintegral_even_pow_quasiProb`,
`exists_subseq_tendsto_quasiProbMeasure`, `hasMoments_of_tendsto_quasi`, and
**`exists_quasiLimit_hasMoments`**: for any sequence of parameters there is a subsequence of the
quasi rules converging weakly to a probability measure whose every moment is `s_k/s₀`. The generic
engine (`tendsto_integral_pow_of_uniform_even_moment`, `lintegral_even_pow_le_of_forall_isOpen_le_liminf`,
`integrable_truncPow`, …) was reused unchanged; only the family-specific inputs are new. Exactness to
`2n` instead of `2n+1` cost nothing — every use needs it only *eventually* in the level.

Axiom-clean, zero placeholders, registered.

**Opens next — and Hurwitz is not needed after all.** To show the limit `μ` is carried by
`F_τ = {x : B(x)τ − D(x) = 0}`, take `f ≥ 0` continuous with compact support disjoint from `F_τ`. On
`supp f`, `|Bτ − D| ≥ δ > 0`. If `Bₙτₙ − Dₙ → Bτ − D` *locally uniformly*, then for large `n` that
function is `≥ δ/2` on `supp f`, so it has **no zeros there** — and its zeros are exactly the level-`n`
nodes (link 152). So `∫f dμₙ = 0` for large `n`, hence `∫f dμ = 0`, hence `μ(F_τᶜ) = 0`.

That argument needs only locally uniform convergence of the truncated entries, not a zero-counting
theorem. So the missing mathlib machinery (Rouché, argument principle) is avoidable entirely. Next
step: check whether `differentiableOn_bilinearLimit` in `NevanlinnaPluecker` already establishes
`TendstoLocallyUniformlyOn` for the entry series — it must prove something of that kind to get
holomorphy of the limit, in which case the carriedness argument is within reach immediately.

### Link 155 — the uniform estimate was already there, only its weaker consequence had been recorded

Link 154 ended by asking whether the holomorphy proof establishes locally uniform convergence. It
establishes something stronger and had simply not stated it: `differentiableOn_bilinearLimit` builds
`uniformCauchySeqOn_bilinearPartialSum` and pointwise convergence, calls
`.tendstoUniformlyOn_of_tendsto`, then immediately weakens the result to
`TendstoLocallyUniformlyOn` to feed `.differentiableOn`. The uniform statement is discarded one line
after being proved.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/EntryUniformLimit.lean`
- `tendstoUniformlyOn_bilinearLimit` — the extraction: **uniform** (not merely locally uniform)
  convergence of the bilinear partial sums on any set carrying a uniform kernel bound. Four lines,
  reusing the two ingredients the holomorphy proof already had.
- `tendstoUniformlyOn_nevD_series`, `tendstoUniformlyOn_nevB_series` — uniform convergence of both
  entry series on **every ball**, via `kernelRoot_le_ballBoundQ` (link 149). The implicit `Kg` has to
  be supplied explicitly (`ballBoundQ s S P r`), since it occurs only in the deferred hypothesis.
- `bilinearPartialSum_secondKind_comm` — the `B` summand in the order the entry uses; the bilinear
  machinery wants the constant factor first, the entry writes it second.

Axiom-clean, zero placeholders, registered.

**Opens next: carriedness, now fully in reach.** With uniform convergence on balls, the argument of
link 154 can be run:
1. `F_τ` is closed, so for compact `K ⊆ F_τᶜ` the continuous `|B(·)τ − D(·)|` attains a positive
   minimum `δ` on `K`.
2. Uniform convergence gives `N` with `|Bₙ(·)τ − Dₙ(·)| ≥ δ/2 > 0` on `K` for `n ≥ N`, so the level-`n`
   denominator has **no zero in `K`** — and by link 152 its zeros are exactly the level-`n` nodes.
3. So `quasiMeasure` of `K` is `0` for `n ≥ N`; by portmanteau for closed sets, the weak limit `μ`
   also gives `K` measure `0`.
4. Inner regularity of a finite Borel measure on `ℝ` upgrades "every compact subset of `F_τᶜ` is
   null" to `μ(F_τᶜ) = 0`.

Step 4 is the only step needing machinery not yet used on this card; `ℝ` is a Polish space so the
instance should be available rather than built. Once it lands, `leaf`, `finite_carried`,
`infinity_carried` and `leaf_moments` all hold for the *constructed* leaf `μ`, and the card's open
core reduces to identifying `μ`'s atoms with `λ(ξₙ)` — i.e. to the reverse of the inequality
`weight_le_christoffelLimit` already proved in link 133.

### Link 156 — the denominator converges uniformly on bounded real intervals

Steps 1–2 of the link-155 plan are now Lean.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/EntryRealUniform.lean`
- `measure_open_eq_zero_of_compacts` — a finite measure vanishing on every compact subset of an open
  set vanishes on it. Step 4 of the plan, and it needed no construction: `ℝ` is Polish, so
  `μ.Regular` resolves by `infer_instance` for any finite measure, and `IsOpen.measure_eq_iSup_isCompact`
  does the rest in three lines.
- `nevBreal_ofReal_partial`, `nevDreal_ofReal_partial` — **the truncated real entries are the complex
  bilinear partial sums along `Complex.ofReal`**, at index `n+1`. This is the bridge that lets the
  ball estimate reach the real line.
- `nevBinf_comm_tsum`, `nevDinf_tsum` — the limits in the order the bilinear machinery produces them.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/DenominatorUniform.lean`
- `eventually_nevDreal_close`, `eventually_nevBreal_close` — each truncated entry differs from its
  limit by exactly `h₀·x·(tail)`, and on `|x| < r` the prefactor is at most `h₀·r`. So eventually
  `|entryₙ(x) − entry(x)| < ε` **uniformly on the interval**.
- `eventually_nevDenominator_close` — **the combination `Bₙ·τ − Dₙ` converges uniformly to `B·τ − D`
  on every bounded interval**, splitting `ε` between the two entries with the `|τ|` factor absorbed.

Axiom-clean, zero placeholders, registered. Traps hit: `zero_le` takes its argument implicitly (third
time on this card); `push_cast` normalises the whole goal to casted evaluations, so the termwise
`monicOrthoC_ofReal` bridges must come *after* it, not before; `div_le_div_iff` does not exist under
that name in this toolchain — an explicit `calc` through `|τ| ≤ |τ| + 1` avoids needing it at all.

**Opens next: the node-avoidance step, then carriedness.** Everything needed is now in place:
1. On compact `K` disjoint from `F_τ`, `|B(·)τ − D(·)|` is continuous and nonvanishing, hence
   `≥ δ > 0` (`IsCompact.exists_forall_le` on `K` nonempty; `K = ∅` is trivial).
2. `eventually_nevDenominator_close` with `ε = δ/2` puts `|Bₙ(·)τ − Dₙ(·)| ≥ δ/2 > 0` on `K`
   eventually — so **no level-`n` node lies in `K`** by `nevDenominator_zero_iff` (link 152).
3. Hence `quasiMeasure ... K = 0` eventually, and `limsup_measure_closed_le_of_tendsto` (verified
   present) carries it to the weak limit.
4. `measure_open_eq_zero_of_compacts` finishes: `μ(F_τᶜ) = 0`.

One wrinkle to handle honestly at step 2: `nevDenominator_zero_iff` needs `α_n ≠ 0`, and `α_n = 0`
happens exactly when `τ = Qₙ(0)/Rₙ(0)`. At those levels the denominator is `βₙ·Qₙ` instead (with
`βₙ ≠ 0` by `nevAlpha_beta_ne_zero`), whose zeros are the *Gauss* nodes of level `n−1`. So the
construction must either restrict to `τ` avoiding that countable set, or run the argument with the
Gauss rule at the exceptional levels. This is not a gap in the proof so far — it is the next thing to
decide, and it is a choice about which family to feed the limit, not an obstruction.

### Link 157 — node avoidance, and the `α` wrinkle dissolves

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/DenominatorAvoidance.lean`
- `exists_radius_of_isCompact` — a compact set of reals sits inside a symmetric open interval.
- `eventually_no_denominator_zero_on_compact` — **on a compact `K` where the limiting denominator
  does not vanish, the truncated denominator eventually does not vanish either.** `|B(·)τ − D(·)|` is
  continuous and nonzero on `K`, so it attains a positive minimum `δ` (`IsCompact.exists_isMinOn`);
  `eventually_nevDenominator_close` with `ε = δ/2` then forbids a zero. Stated for the *denominator*,
  not the nodes, so it is independent of which family describes the zeros at a given level.
- `eventually_quasiNodes_disjoint`, `eventually_quasiMeasure_compact_eq_zero` — the node and measure
  forms, conditional on `αₙ ≠ 0`.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevAlphaCofinal.lean` — the wrinkle flagged in
link 156 is not a wrinkle.

`βₙ = Q_{n+1}(0) − τ·R_{n+1}(0)` and `α_{n+1} = τ·R_{n+1}(0) − Q_{n+1}(0)`, so
**`βₙ = −α_{n+1}`** (`nevBeta_eq_neg_nevAlpha_succ`, one `ring`). Therefore
`nevAlpha_beta_ne_zero` — proved back in link 152 from the Wronskian — says precisely that **no two
consecutive leading coefficients vanish** (`nevAlpha_succ_ne_zero_of_eq_zero`). Hence
`exists_ge_nevAlpha_ne_zero` and `infinite_setOf_nevAlpha_ne_zero`: the good levels are **cofinal**,
for *every* `τ`.

So there is no exceptional set of parameters and no need to fall back to the Gauss rule at bad
levels. The weak limit is taken along the good levels, which are infinite, and tightness holds along
any subsequence (link 154 was stated for an arbitrary parameter sequence precisely to allow this).
The Wronskian non-degeneracy that looked like a small technical lemma in link 152 turns out to be the
statement that carries the whole construction past its only apparent obstruction.

Axiom-clean, zero placeholders, registered. Traps: `autoImplicit` silently turned two missing imports
into implicit binders, surfacing as "function expected" rather than "unknown identifier" — the hint
named the cause; `Set.infinite_of_not_bddAbove` is an implication, not an iff, so `refine` not `rw`.

**Opens next:** the assembly. Choose a strictly monotone enumeration `ψ : ℕ → ℕ` of the good levels
(from `infinite_setOf_nevAlpha_ne_zero`), form the measures `quasiProb s (ψ i) (βψᵢ/αψᵢ)`, extract a
weakly convergent subsequence (link 154), and combine `eventually_quasiMeasure_compact_eq_zero` with
`limsup_measure_closed_le_of_tendsto` and `measure_open_eq_zero_of_compacts` (link 156) to conclude
`μ(F_τᶜ) = 0`. That is `leaf` together with `finite_carried` and `leaf_moments` for a single `τ`; the
family over all `τ` and `continuous_leaf` follow, and the card's open core narrows to the atoms.

### Link 158 — the leaf is constructed

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/QuasiLevelFamily.lean`

Every *per-level* statement of the construction was already stated for an arbitrary level and
parameter; only the *family* statements pinned the level to `n+1`. Restated for a level function `ν`
with `n + 1 ≤ ν n`: `isTightMeasureSet_quasiProb_of_level`,
`exists_subseq_tendsto_quasiProbMeasure_of_level`, `hasMoments_of_tendsto_quasi_of_level`. Plus the
selection: `goodLevel h tau n` is a level `≥ n+1` with `α ≠ 0` (link 157 makes it exist), and
`leafParam` is the quasi parameter it determines.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/LeafConstruction.lean`

`exists_leaf` — **for every `τ` there is a probability measure `μ` with**
- `∫ xᵏ dμ = s_k/s₀` for every `k`, and
- `μ {x : B(x)τ − D(x) ≠ 0} = 0`.

The carriedness argument as planned, with one adjustment made while writing it: the portmanteau
inequality available for a weak limit runs `μ G ≤ liminf μₙ G` for *open* `G`, which is the wrong
direction on a compact set. So the compact `K` is first enlarged via `exists_compact_between` to a
compact `L` with `K ⊆ interior L ⊆ L ⊆ F_τᶜ`; the avoidance estimate kills `L`, monotonicity passes to
`interior L`, portmanteau applies there because it is open, and `μ K ≤ μ (interior L) = 0`. Then
`measure_open_eq_zero_of_compacts` (link 156) spreads it to all of `F_τᶜ`.

Axiom-clean, zero placeholders, registered.

**Status of `ClassicalNevanlinnaExtremalFamily`.** `matrix` ✓, `continuous_B` ✓, `continuous_D` ✓
(link 149); `finite_carried` ✓, `infinity_carried` ✓ as measure statements (link 150); and now the
**existence** of a leaf with the correct moments *and* the correct carrier, for every parameter.

**Opens next.** Two things separate this from the packaged structure:
1. `leaf` as a *function* `OnePoint ℝ → ProbabilityMeasure ℝ` — `exists_leaf` gives one measure per
   `τ`; choice turns it into a function, but `continuous_leaf` then needs the choice to be coherent.
   The classical route is uniqueness: the N-extremal measure of a parameter is unique, so the choice
   is forced and continuity comes from continuity of the Stieltjes transform in `τ`.
2. The open core, unchanged: the atoms of the constructed `μ` are `λ(ξ)`. Link 133's
   `weight_le_christoffelLimit` gives `≤`; the reverse is what remains, and it is now a statement
   about a *constructed* measure rather than a hypothetical one — which is the first time on this card
   that the open core has had a concrete object to be tested against.

### Link 159 — both leaves, in the fibers the interface names

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/InfinityDenominator.lean`
- `exists_leaf_finiteDenominatorFiber` — link 158's leaf restated against
  `(nevMatrixDataInf h h0b).finiteDenominatorFiber tau`, with the moments packaged as
  `HasHamburgerMoments`. The fiber complement *is* the carriedness set, so the restatement is one
  `ext`. Plus the normalised variant for `s₀ = 1`.
- The parameter at infinity: `nevBreal_closed` (link 152) already writes `Bₙ` as
  `(h₀/hₙ)·(Rₙ(0)·Q_{n+1}(x) − R_{n+1}(0)·Qₙ(x))`, so it is a quasi-orthogonal combination with
  `αₙ = Rₙ(0)`, `βₙ = −R_{n+1}(0)`. Then `βₙ = −α_{n+1}` is **`rfl`**, and
  `nevAlphaInf_beta_ne_zero` is the same Wronskian argument: `Rₙ(0)` and `R_{n+1}(0)` cannot both
  vanish. Hence `exists_ge_nevAlphaInf_ne_zero` — cofinal good levels — and `nevBreal_zero_iff`.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/InfinityLeaf.lean`
- `eventually_no_nevBreal_zero_on_compact`, `eventually_quasiMeasure_compact_eq_zero_inf`,
  `goodLevelInf`, `leafParamInf`, and **`exists_leaf_infinity`** / `exists_leaf_infinityDenominatorFiber`.
  The whole of links 157–158 runs unchanged with `B` in place of `B·τ − D`; the uniform estimate it
  needs, `eventually_nevBreal_close`, was already proved in link 156. Compiled first try.

Axiom-clean, zero placeholders, registered.

**Every parameter in `ℝ ∪ {∞}` now has a constructed leaf** with the correct moments and carried by
the correct denominator fiber. In `ClassicalNevanlinnaExtremalFamily` terms: `matrix`,
`continuous_B`, `continuous_D` are built; and for each `t : OnePoint ℝ` separately, a measure
satisfying what `leaf_moments` and `finite_carried`/`infinity_carried` demand of it exists.

Method note: the `τ = ∞` case cost one module rather than a redevelopment because link 152 was stated
as a *closed form for `Bₙ`* rather than only for the combination `Bₙτ − Dₙ`. The general lesson on
this card keeps repeating — the reusable statement is the one about the individual object, not about
the combination currently of interest.

**Opens next.**
1. **`leaf` as a function.** `Classical.choice` on the two existence theorems gives
   `OnePoint ℝ → ProbabilityMeasure ℝ` immediately, but `continuous_leaf` needs the choice coherent.
   The classical route is uniqueness of the N-extremal measure for a parameter; that is a genuine
   further theorem, and it is what would also collapse the open core, since a unique measure carried
   by `F_τ` with the right moments must have the Christoffel weights.
2. **The open core**, unchanged in statement but no longer hypothetical: the atoms of the constructed
   leaf are `λ(ξ)`. `weight_le_christoffelLimit` (link 133) gives `≤`.

### Link 160 — the open core becomes a single scalar inequality, and half of it is now proved

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/FiberWeightSum.lean`

- `measure_eq_tsum_singleton` — a measure of a countable set is the sum of its atoms
  (`measure_biUnion` over singletons).
- `measure_singleton_le_ofReal_christoffelLimit` — the `ENNReal` form of link 133's atom bound,
  applicable to *any* finite representing measure.
- **`one_le_tsum_christoffelLimit_finiteFiber`** and **`one_le_tsum_christoffelLimit_infinityFiber`** —
  for a normalised sequence, `1 ≤ ∑_{ξ ∈ F_t} λ(ξ)` for every parameter `t ∈ ℝ ∪ {∞}`.
  The constructed leaf is a probability measure carried by the countable fiber, so its mass is the
  sum of its atoms; each atom is at most `λ(ξ)`; so the `λ`'s sum to at least the mass.
- **`measure_singleton_eq_of_tsum_le`** — the reduction: if the sum is *also* at most `1`, then
  `ENNReal.tsum_lt_tsum` forces equality termwise, and **every atom of the leaf equals `λ(ξ)`**.

Axiom-clean, zero placeholders, registered.

**What this does to the card's open core.** The core was "the Nevanlinna weight is the Christoffel
limit, `wₙ = λ(ξₙ)`". It is now exactly

> **[OPEN CORE]** `∑_{ξ ∈ F_t} λ(ξ) ≤ 1` for a normalised moment sequence,

a statement with no measure in it — purely about the denominator fiber and the Christoffel limit.
The reverse inequality is proved, and the passage from the equality to the atoms is proved. This is
the first time on this card the core has been a single scalar inequality between explicitly
constructed objects rather than a statement about a hypothetical measure.

Note what the reduction cost: nothing about N-extremality or density of polynomials was needed. The
classical route to `wₙ = λ(ξₙ)` goes through density of polynomials in `L²(μ)`, which is a
substantially harder theorem; the construction here bypasses it because the leaf's mass is *known*
to be `1` and its carrier is *known* to be `F_t`, so the two sums are pinned against each other.

**Opens next.** Two independent attacks on `∑_{ξ ∈ F_t} λ(ξ) ≤ 1`:
1. *Finite truncation.* For a finite subset `{ξ₁,…,ξ_m} ⊆ F_t`, show `∑ᵢ λ(ξᵢ) ≤ 1`, then pass to the
   supremum. At level `n` the quadrature gives `∑_{nodes} w = 1` exactly, and `λ ≤ christoffel s n`
   pointwise since `christoffelLimit` is the infimum — so the question is whether `m` fiber points
   can be compared against the `n+1` nodes of a single level. `quasiWeight_pos` and the exactness of
   the rule on `bξ²` are the tools.
2. *Direct.* `∑_{ξ ∈ F_t} λ(ξ) δ_ξ` is `fiberMeasure (christoffelLimit s) F_t` (link 150). Its total
   mass is the sum in question, and `lintegral_fiberMeasure` computes its moments. Showing its mass
   is at most `1` is showing that this explicitly defined measure is sub-probability.

### Link 161 — the open core, at finite level

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/QuasiNodeWeightSum.lean`

- `quasiWeight_eq_momentInner_basis` — the interpolatory weight at a node **is** the moment norm of
  its Lagrange basis polynomial, `wξ = ⟪bξ, bξ⟫`. (The content was inside `quasiWeight_pos`; stated
  on its own it is the usable form.)
- `christoffelLimit_le_quasiWeight` — hence `λ(ξ) ≤ wξ` at every node, because `bξ(ξ) = 1` and
  `christoffelLimit_le_momentInner_self` — the variational property, **already in the corpus**, with
  no degree restriction at all.
- **`sum_christoffelLimit_quasiNodes_le`** — `∑_{ξ ∈ quasiNodes s n t} λ(ξ) ≤ s₀`, for every level and
  every parameter. With `quasiNodes_zero_param` (the Gauss nodes are the quasi nodes of parameter
  zero) the same holds over Gauss node sets.

Axiom-clean, zero placeholders, registered, first-try compile.

**This is the open core at finite level.** The target is `∑_{ξ ∈ F_t} λ(ξ) ≤ 1`; what is proved is the
identical statement with `F_t` replaced by a level-`n` node set.

**A correction to link 160's attack 1.** That link proposed proving `∑ᵢ λ(ξᵢ) ≤ 1` for an *arbitrary*
finite subset of `F_t` and passing to the supremum. The proof above does **not** generalise that way,
and the reason is structural rather than technical: the step `λ(ξ) ≤ wξ` needs the rule to be exact on
`bξ²`, which is degree `2n`, and exactness to `2n` is exactly what makes a node set a node set. For
an arbitrary set of `m` points the interpolatory rule is exact only to degree `m−1`, and `bξ²` is out
of reach. What *does* survive for arbitrary points is `∑ᵢ wᵢ = s₀` (the Lagrange bases sum to `1`), but
without exactness there is no comparison between `wᵢ` and `λ(ξᵢ)`.

So the naive truncation route is closed. The remaining gap is precisely the passage from node sets to
the fiber, which is the same node-convergence question that Hurwitz would have answered — and which
link 155's uniform-convergence estimate approaches from the other side. Concretely:

> **[OPEN CORE]** `∑_{ξ ∈ F_t} λ(ξ) ≤ 1`. Proved for every level-`n` node set; needed for the limit
> fiber. The missing link is that each finite subset of `F_t` is, for large `n`, "close enough" to a
> subset of the level-`n` nodes for the bound to survive — a lower-semicontinuity statement about `λ`
> along converging nodes, not a new estimate on the weights.

That reformulation is the next thing to attack: `λ` is an infimum of continuous functions, hence upper
semicontinuous, and the inequality wanted is in the direction that semicontinuity supplies.

### Link 162 — the leaf is an explicit weighted Dirac family, and the core is located exactly

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/CarriedAtomic.lean`
- `measure_eq_fiberMeasure_of_carried` — **a finite measure giving a countable `F` full mass *is* the
  weighted Dirac family of its own atoms**, `μ = ∑_{ξ∈F} μ{ξ}·δ_ξ`. Proved by `Measure.ext`, splitting
  `μ A = μ (A ∩ F)` and rewriting both sides as `tsum`s of indicators over `ℝ` (`tsum_subtype` twice,
  with its arguments supplied explicitly — higher-order unification cannot guess them).
- `exists_leaf_eq_fiberMeasure`, `exists_leaf_infinity_eq_fiberMeasure` — hence **each constructed
  leaf equals `fiberMeasure (fun x => (μ{x}).toReal) F_t`**. The leaf is no longer a weak limit: it is
  determined by the numbers `μ{ξ}`, `ξ ∈ F_t`, and its integrals are sums over the fiber.

Axiom-clean, zero placeholders, registered.

**Where the core actually sits — a negative result about the available routes.** Three attacks were
worked through this session and two are now closed:

1. *Finite truncation over arbitrary subsets* — closed in link 161. The comparison `λ(ξ) ≤ wξ` needs
   exactness to degree `2n`, which is what distinguishes a node set.
2. *Semicontinuity along converging nodes* — needs `λ` continuous. `λ` is an infimum of continuous
   functions, hence upper semicontinuous; the direction wanted is the other one. Continuity would
   follow from locally uniform convergence of the kernel *diagonal*, but the bilinear machinery of
   this development gives uniformity only with **one argument held fixed** (the summable side is the
   fixed one), and the diagonal has both varying. The classical fix is Vitali/Montel, and mathlib has
   no normal-families theorem for holomorphic functions (checked `Analysis/Complex/`: only
   `LocallyUniformLimit` machinery that *consumes* local uniformity, never produces it from local
   boundedness). So this route requires building Vitali first.
3. *Test-polynomial* — with the leaf now known to be atomic on `F_t`, for any polynomial `p` with
   `p(ξ) = 1`, the variational property plus atomicity give
   `λ(ξ) ≤ ⟪p,p⟫ = ∑_{η∈F_t} μ{η}·p(η)²`. Taking `p` concentrated at `ξ` would give `λ(ξ) ≤ μ{ξ}` and
   finish the card. This is exactly **density of polynomials in `L²(μ)`** — M. Riesz's theorem — and is
   the genuine remaining content.

So the open core is no longer "identify the weights"; it is one classical theorem, and route 3 states
it in the form this development can consume:

> **[OPEN CORE]** For the constructed leaf `μ` of parameter `t` and each `ξ ∈ F_t`, there are
> polynomials `pₘ` with `pₘ(ξ) = 1` and `∑_{η ∈ F_t \ {ξ}} μ{η}·pₘ(η)² → 0`.

Everything else on the card is proved. Two routes into that statement are worth weighing next: build
Vitali (which also unlocks route 2 and gives continuity of `λ` as a by-product), or attack the
approximation directly using the entire function `(B(x)t − D(x))/(x − ξ)`, which vanishes on
`F_t \ {ξ}` exactly — the obstruction there being that it is entire rather than polynomial, so it
needs to be reached in the moment norm by its Taylor sections.

### Link 163 — the core is now one named `Prop`, and everything around it is discharged

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/AtomApproximation.lean`
- `lintegral_eq_tsum_atoms` — integration against a measure carried by a countable set is a sum over
  that set, straight from link 162's `measure_eq_fiberMeasure_of_carried`.
- **`christoffelLimit_le_tsum_atoms`** — for a representing measure carried by a countable `F`, every
  polynomial `p` with `p(ξ) = 1` gives
  `λ(ξ) ≤ ∑_{η ∈ F} μ{η}·p(η)²`.
  Chain: the variational property (corpus), `momentFunctional_pow_two_eq_integral_sq` (corpus) to turn
  `⟪p,p⟫` into `∫p²dμ`, `ofReal_integral_eq_lintegral_ofReal` to reach the lower integral, then the
  atomic sum.
- `AtomApproximable μ F ξ` — the named remaining hypothesis: normalised polynomials whose weighted
  square sum over `F` approaches `μ{ξ}`.
- `ofReal_christoffelLimit_le_measure_singleton` and
  **`measure_singleton_eq_ofReal_christoffelLimit`** — under `AtomApproximable`, `μ{ξ} = λ(ξ)`,
  combining with link 160's general bound in the other direction.

Axiom-clean, zero placeholders, registered.

**State of the card.** Every field of `ClassicalNevanlinnaExtremalFamily` except the weight
identification is constructed unconditionally, and the weight identification is now

> **[OPEN CORE]** `AtomApproximable μ F_t ξ` for the constructed leaf `μ` of each parameter `t` and each
> `ξ ∈ F_t` — i.e. density of polynomials in `L²(μ)` at the point `ξ`, M. Riesz's theorem.

Nothing else is open. The reduction is unconditional: given that one `Prop`, `measure_singleton_eq_ofReal_christoffelLimit`
delivers the atoms, and via link 160's `measure_singleton_eq_of_tsum_le` the equality
`∑_{ξ∈F_t} λ(ξ) = 1` follows as well.

**Assessment of the two ways in** (recorded so the next session does not re-derive it):
- *Build Vitali/Montel.* Mathlib has no normal-families theorem (link 162). Building it also yields
  continuity of `λ`, hence the semicontinuity route, hence node-convergence arguments generally. It is
  the larger investment but unlocks the most.
- *Taylor sections of `(B(x)t − D(x))/(x − ξ)`.* That entire function vanishes on `F_t \ {ξ}` exactly
  and is nonzero at `ξ`, so it is the `p` wanted — except that it is entire, not polynomial. What has
  to be shown is that its Taylor sections converge to it in the moment norm `⟪·,·⟫`. The kernel bounds
  of links 146–149 control exactly that norm, so this route stays inside the machinery already built,
  and is the one to try first.

### Link 164 — the tunable estimate survives to the full series

Link 163 named two routes. Before committing to either, one thing had to be settled: whether the
kernel *diagonal* can be shown continuous inside this development, since link 162 had closed the
obvious approach (the bilinear machinery gives uniformity only with one argument fixed, and mathlib
has no Vitali). It can — and the tool is the tunable absorption estimate built back in links 132–139
for a purpose that was itself refuted.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/KernelTunableSum.lean`
- `summable_normSq_eq_norm` — the kernel series in `‖·‖²` rather than `normSq` (`Complex.sq_norm`;
  `Complex.normSq_eq_abs` does not exist in this toolchain).
- **`tsum_kernel_le_tunable`** — for bounded kernels,
  `K(w) ≤ (1+ε)·K(z) + 4(1+ε⁻¹)·(‖w−z‖h₀)²·S_w²S²P²`
  for the *whole* series, every `ε > 0`. Each partial sum at `w` is handled by
  `kernelRoot_sq_le_absorption_tunable`, the centre roots are replaced by their global bounds
  (links 146–148), and `Summable.tsum_le_of_sum_le` passes to the series — via
  `Finset.exists_nat_subset_range`, since arbitrary finite subsets have to be reduced to ranges.

**Why this matters.** Letting `w → z` gives `limsup_{w→z} K(w) ≤ (1+ε)·K(z)` for every `ε > 0`, hence
`limsup ≤ K(z)`: the kernel sum is **upper semicontinuous**. Lower semicontinuity is free — it is a
supremum of continuous partial sums. So the kernel sum is continuous, and therefore so is
`λ = 1/K` (`christoffelLimit_eq_inv_tsum`, link with `ChristoffelLimitFormula`). That was the
prerequisite link 162 recorded as blocked on Vitali; it is not blocked, because the factor `2` in the
naive estimate — the only obstruction — is exactly what the tunable version removes.

Note the reuse: the tunable absorption chain was built in links 132–139 to make a chaining argument
work, and link 139 *refuted* that argument. The estimate itself was never wrong, only the use it was
put to; it is now doing the work it was actually good for. Worth remembering before deleting
machinery whose motivating application dies.

Axiom-clean, zero placeholders, registered.

**Opens next:** the topology, which is now routine — `limsup` over `𝓝 z`, then `ε → 0`, then
`continuousAt` from USC plus LSC; then `Continuous (christoffelLimit s)` on `ℝ` by composing with
`Complex.ofReal` and inverting away from zero. After that the semicontinuity route of link 162 is
open, and what remains for it is node convergence — for which the elementary real-variable
substitute is a sign change of `B·t − D` at each fiber point, an intermediate-value argument rather
than an argument-principle one.

### Link 165 — the Christoffel limit is continuous

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/KernelContinuity.lean`
- `kernelSum s w` — the kernel series as a function of the point; `kernelSum_le_of_bound`,
  `kernelSum_nonneg`, `kernelSum_pos` (bounded below by its `k = 0` term `1/h₀`).
- **`continuousAt_kernelSum`** — the kernel sum is continuous on `ℂ`. Link 164's estimate is applied
  with the two points *in both orders*, giving
  `|K(w) − K(z₀)| ≤ ε·Sb² + C(ε)·‖w − z₀‖²` on a ball; choose `ε` from `δ` first and the displacement
  second. No semicontinuity API is involved — the two-sided bound gives the `ε`-`δ` statement outright.
- `continuous_kernelSum`, `kernelSum_ofReal` (the real trace is the real Christoffel series).
- **`continuous_christoffelLimit`** — `λ` is continuous on `ℝ`, by `christoffelLimit_eq_inv_tsum`
  (link with `ChristoffelLimitFormula`) and `Continuous.inv₀`, the denominator being nonvanishing by
  `kernelSum_pos`.

Axiom-clean, zero placeholders, registered.

This retires the blocker recorded in link 162, which read: *"Continuity would follow from locally
uniform convergence of the kernel diagonal … the classical fix is Vitali/Montel, and mathlib has no
normal-families theorem … so this route requires building Vitali first."* It did not. The diagonal
never needed a normal-families argument, only an estimate with a leading constant that can be tuned
below `2` — which had been sitting in the tree since link 139 refuted the argument it was built for.

**Opens next.** The semicontinuity route of link 162 is now unblocked on its analytic side, and what
it still needs is purely real-variable:

> For `ξ ∈ F_t`, nodes `ξ_n` of the level-`n` denominator with `ξ_n → ξ`.

With that, `λ(ξ_n) → λ(ξ)` by continuity, and link 161's `∑_{ξ ∈ nodes} λ ≤ s₀` passes to any finite
subset of `F_t`, giving `∑_{F_t} λ ≤ 1` and closing the card via link 160.

The elementary substitute for Hurwitz here: `Bₙ·t − Dₙ → B·t − D` uniformly on compacts (link 156),
all real and continuous, so a **sign change** of the limit at `ξ` forces a nearby zero of the
truncation by the intermediate value theorem. So the remaining question is whether `B·t − D` changes
sign at each of its zeros — i.e. that its zeros have odd order. Its zeros are already known to be
isolated (link 147); simplicity is the missing piece, and it is a statement about one entire function
rather than about the family.

### Link 166 — the `B, D` Wronskian is the reproducing kernel

Link 165 reduced the remaining gap to a sign change of `B·t − D` at each fiber point. Working out what
would produce one turned up an identity that had not been noticed, and it is elementary.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevBDWronskian.lean`

> **`nevBD_wronskian`** — `Bₙ(x)·Dₙ(y) − Dₙ(x)·Bₙ(y) = h₀·(x − y)·Kₙ(x,y)`.

Both entries are two-term combinations of `Q_{n+1}, Qₙ` (link 152), so in the antisymmetric
combination the `Q_{n+1}(x)Q_{n+1}(y)` and `Qₙ(x)Qₙ(y)` terms cancel and what is left factors as
`(P₀R₁ − P₁R₀)·(Q_{n+1}(x)Qₙ(y) − Qₙ(x)Q_{n+1}(y))`. The first factor is the Wronskian at the origin,
`hₙ/h₀` (link 152 again); the second is `hₙ·(x−y)·Kₙ(x,y)` by Christoffel--Darboux. The constants
collapse to `h₀`.

Axiom-clean, zero placeholders, registered. The proof has to `set` all eight polynomial evaluations
before any `field_simp`/`ring`, since `ring_nf` normalises `n+1` to `1+n` inside indices and would
otherwise split one atom into two — the trap recorded at link 159.

**Why this closes the sign-change question.** Let `ξ ∈ F_t`, so `D(ξ) = B(ξ)·t`. Substituting `y = ξ`
in the limit form of the identity,

`(B(x)t − D(x))·B(ξ) = B(x)D(ξ) − D(x)B(ξ) = h₀·(x − ξ)·K(x,ξ)`.

- `B(ξ) ≠ 0`, since `B(ξ) = 0` would force `D(ξ) = B(ξ)t = 0` and contradict
  `nevBinf_ne_zero_or_nevDinf_ne_zero` (link 147).
- `K(ξ,ξ) > 0` (`kernelSum_pos`, link 165) and `x ↦ K(x,ξ)` is continuous — this is the bilinear
  series with **one argument fixed**, exactly the case the machinery of links 155/164 covers.

So near `ξ`, `B(x)t − D(x)` is `(x − ξ)` times a continuous function of constant sign: it **changes
sign at `ξ`**, and `ξ` is a simple zero. No derivative and no argument principle.

**Opens next**, and the chain is now short:
1. Pass `nevBD_wronskian` to the limit (`Bₙ → B`, `Dₙ → D` by link 156; `Kₙ(x,ξ) → K(x,ξ)` is the
   fixed-argument bilinear series).
2. Sign change at `ξ` ⇒ by the intermediate value theorem and uniform convergence (link 156), the
   level-`n` denominator has a zero near `ξ` for large `n` — node convergence, elementarily.
3. `λ` continuous (link 165) carries `∑_{nodes} λ ≤ s₀` (link 161) to finite subsets of `F_t`.
4. `∑_{F_t} λ ≤ 1`, and link 160 closes the card.

### Link 167 — the Wronskian identity in the limit, and the denominator factored at a fiber point

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevBDWronskianLimit.lean`
- `summable_diag_real`, `summable_bilinear_real` — the real kernel series converges at every point,
  and the bilinear series converges absolutely by `|ab| ≤ (a²+b²)/2` against the two diagonals.
- `tendsto_cdKernel_eval`, `tendsto_nevBreal`, `tendsto_nevDreal` — the three convergences, the last
  two extracted from link 156's uniform estimate by taking `r = |x| + 1`.
- **`nevBD_wronskian_limit`** — `B(x)·D(y) − D(x)·B(y) = h₀·(x − y)·K(x,y)`, by `tendsto_nhds_unique`
  on link 166's finite-level identity.
- `nevBrealInf_ne_zero_or_nevDrealInf_ne_zero` — the real form of link 147's no-common-zero result.
- `nevBrealInf_ne_zero_of_mem_fiber` — hence `B(ξ) ≠ 0` for every `ξ ∈ F_t`.
- **`nevDenominator_factor_at_fiber`** —
  `(B(x)t − D(x))·B(ξ) = h₀·(x − ξ)·K(x,ξ)` for `ξ ∈ F_t`.

Axiom-clean, zero placeholders, registered, first-try compile for the main file.

**The denominator is now factored.** Near a fiber point, `B(x)t − D(x)` equals `(x − ξ)` times
`h₀·K(x,ξ)/B(ξ)`, whose value at `x = ξ` is `h₀·K(ξ,ξ)/B(ξ) ≠ 0` since `K(ξ,ξ) > 0` (link 165). So the
denominator changes sign at each fiber point, and every zero is simple — proved without a derivative,
without the argument principle, and without Hurwitz.

**Opens next**, three steps to close the card:
1. *Sign change.* From the factorisation plus continuity of `x ↦ K(x,ξ)` (the fixed-argument bilinear
   series), `B·t − D` takes opposite signs at `ξ ± η` for small `η`.
2. *Node convergence.* Uniform convergence of `Bₙt − Dₙ` on `[ξ−η, ξ+η]` (link 156) makes the
   truncation take opposite signs at the endpoints for large `n`, so the intermediate value theorem
   puts a level-`n` node inside — and by link 152 the nodes are exactly the quasi-orthogonal nodes.
3. *Transfer of the weight bound.* Continuity of `λ` (link 165) plus `∑_{ξ ∈ nodes} λ(ξ) ≤ s₀`
   (link 161) gives `∑_{ξ ∈ S} λ(ξ) ≤ s₀` for every finite `S ⊆ F_t`; the supremum over finite
   subsets is `∑_{F_t} λ`, and link 160 then closes the weight identification.

Step 1 needs one lemma not yet present — continuity of `x ↦ kernelInf s x ξ` — which is the
fixed-argument case of the bilinear machinery and so is the same shape as `tendstoUniformlyOn_nevD_series`
(link 155) rather than the harder diagonal case settled in link 165.

### Link 168 — the denominator provably changes sign at every fiber point

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/KernelOffDiag.lean`
- `kernelInf_comm`, `ofReal_kernelInf` — symmetry, and the real kernel as the trace of the complex
  bilinear series.
- `continuousOn_kernelC`, **`continuousAt_kernelInf`** — the kernel with one argument fixed is
  continuous. This is the *easy* case: `tendstoUniformlyOn_bilinearLimit` (link 155) applies
  directly, the partial sums are polynomials, and `TendstoUniformlyOn.continuousOn` finishes. (That
  lemma wants `∃ᶠ`, not `∀ᶠ`, for the continuity hypothesis.)
- `eventually_kernelInf_pos` — `K(x,ξ) > 0` for `x` near `ξ`, from continuity and `K(ξ,ξ) > 0`
  (link 165).
- **`nevDenominator_opposite_signs`** — for every `ξ ∈ F_t` there is `η > 0` with
  `(B(ξ−δ)t − D(ξ−δ))·(B(ξ+δ)t − D(ξ+δ)) < 0` for all `0 < δ < η`.

Axiom-clean, zero placeholders, registered.

**Step 1 of link 167 is done.** The proof is exactly the factorisation of link 167 read twice:
multiplying `G(ξ+δ)·B(ξ) > 0` by `G(ξ−δ)·B(ξ) < 0` gives `G(ξ+δ)G(ξ−δ)·B(ξ)² < 0`, and `B(ξ)² > 0`.

The whole sign-change question — which link 156 first raised, link 162 filed under "needs Vitali",
and link 165 reduced to simplicity of zeros — came down to an algebraic identity (link 166), its limit
(link 167), and continuity in the *easy* variable. The diagonal continuity of link 165 is used only
at the single point `K(ξ,ξ) > 0`.

**Opens next**, two steps:
2. *Node convergence.* `Bₙt − Dₙ → Bt − D` uniformly on `[ξ−δ, ξ+δ]` (link 156), so for large `n` the
   truncation inherits the opposite signs at the endpoints; `intermediate_value_Icc` then puts a zero
   of `Bₙt − Dₙ` inside, and by `nevDenominator_zero_iff` (link 152) that zero is a quasi-orthogonal
   node. Choosing `δ = 1/m` gives nodes converging to `ξ`.
3. *Transfer.* Continuity of `λ` (link 165) plus `∑_{ξ ∈ nodes} λ(ξ) ≤ s₀` (link 161) gives
   `∑_{ξ ∈ S} λ(ξ) ≤ s₀` for finite `S ⊆ F_t`: pick for each `ξ ∈ S` a node within `1/m`, note the
   chosen nodes are distinct for `m` large (the points of `S` are separated), sum, and pass to the
   limit. Then `∑_{F_t} λ ≤ 1` and link 160 closes the weight identification, and with it the card.

### Link 169 — nodes accumulate at every fiber point

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NodeConvergence.lean`
- **`eventually_exists_denominator_zero_near`** — for every `ξ ∈ F_t` there is `η > 0` such that for
  every `δ ∈ (0, η)` and every large `n`, the truncated denominator `Bₙ·t − Dₙ` has a zero within `δ`
  of `ξ`.
- **`eventually_exists_quasiNode_near`** — and at every level where the leading coefficient survives,
  that zero is a quasi-orthogonal node (`nevDenominator_zero_iff`, link 152).

The proof is exactly the two ingredients and nothing else: the sign change of link 168 at `ξ ± δ`,
and uniform convergence on that interval (link 156) with `ε = min(|G(ξ−δ)|,|G(ξ+δ)|)/2`, which makes
the truncation inherit both signs; then `intermediate_value_Icc` (and `intermediate_value_Icc'` for
the reversed order). **No complex analysis** — this is the elementary substitute for Hurwitz that
link 154 first proposed and links 166–168 made available.

Axiom-clean, zero placeholders, registered. Traps: `abs_add` does not exist under that name (use
`neg_abs_le`/`le_abs_self` and `linarith`), and `neg_lt_of_abs_lt` does not have the shape its name
suggests — `abs_lt.mp` giving both bounds at once is the reliable form.

**Step 2 of link 167 is done. One step remains:**

> **Transfer.** For finite `S ⊆ F_t`: choose for each `ξ ∈ S` a node within `1/m`; for `m` large the
> chosen nodes are distinct, since the points of `S` are finitely many and hence separated. Then
> `∑_{ξ ∈ S} λ(node_ξ) ≤ ∑_{nodes} λ ≤ s₀` (link 161, the sum over a subset of a node set being at
> most the sum over all of it, all terms nonnegative). Let `m → ∞`: `λ(node_ξ) → λ(ξ)` by continuity
> of `λ` (link 165), so `∑_{ξ ∈ S} λ(ξ) ≤ s₀`.
>
> The supremum over finite `S` is `∑_{ξ ∈ F_t} λ(ξ)`, giving `≤ 1` for a normalised sequence — and
> link 160's `measure_singleton_eq_of_tsum_le` then identifies every atom of the leaf as `λ(ξ)`,
> closing the weight identification and the card.

Every ingredient of that step is now proved; what remains is the bookkeeping of the finite selection
and the limit.

### Link 170 — the measure-side route, and its two lemmas

Link 169's remaining step was stated as finite-subset bookkeeping: pick a node near each point of a
finite `S ⊆ F_t`, argue the picks are distinct, sum, take limits. Before writing that, a cheaper route
turned up, and it removes the bookkeeping entirely.

**The measure-side argument.** For `ξ ∈ F_t` and small `δ`, the approximating measure `μₙ` has a node
in `Icc (ξ−δ) (ξ+δ)` (link 169) and therefore mass at least `λ(that node)` there. Continuity of `λ`
(link 165) makes that at least `λ(ξ) − ε`. Portmanteau for **closed** sets gives
`limsup μₙ(Icc) ≤ μ(Icc)`, so `μ(Icc (ξ−δ) (ξ+δ)) ≥ λ(ξ) − ε`; shrinking `δ` gives
`μ{ξ} ≥ λ(ξ) − ε`, and `ε → 0` gives `μ{ξ} ≥ λ(ξ)` — the reverse atom bound, directly, with no finite
subsets, no distinctness, and no supremum over `S`.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/QuasiMeasureLowerBound.lean`
- `quasiMeasure_ge_of_node_mem` — a measurable set containing a node has at least that node's weight
  (`Finset.single_le_sum` against `finsetWeightedDirac_apply`). Needs no positive-definiteness, so `h`
  was dropped after the linter flagged it.
- **`quasiMeasure_ge_ofReal_christoffelLimit`** — hence at least `λ` at any node it contains, via
  `christoffelLimit_le_quasiWeight` (link 161).
- `quasiProb_eq_quasiMeasure`, `quasiProb_ge_ofReal_christoffelLimit` — the normalised forms.
- **`le_measure_singleton_of_forall_Icc`** — a bound holding on every small symmetric interval about
  `ξ` bounds `μ{ξ}`: the intervals `Icc (ξ ± η/(m+2))` are antitone with intersection `{ξ}`, and
  `tendsto_measure_iInter_atTop` passes the bound to the limit.

Axiom-clean, zero placeholders, registered.

**What remains is one assembly.** Both ends are now proved and only need to be joined at the
approximating sequence:
- lower end: `quasiProb_ge_ofReal_christoffelLimit` + `eventually_exists_quasiNode_near` (link 169)
  + continuity of `λ`;
- upper end: `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` against `Icc`;
- closing: `le_measure_singleton_of_forall_Icc`, then `measure_singleton_eq_of_tsum_le` (link 160).

The one structural change needed is that `exists_leaf` (link 158) currently discards the approximating
sequence `φ, ν, τ'` after taking the limit. A variant retaining it — the proof is unchanged, only the
statement grows — is what the assembly consumes.

### Link 171 — the open core is closed: the weights are the Christoffel limits

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/LeafAtoms.lean`

- `exists_leaf_approx` — link 158's leaf, retaining the approximating sequence `φ` and the weak
  convergence rather than discarding them.
- **`ofReal_christoffelLimit_le_leaf_singleton`** — `λ(ξ) ≤ μ{ξ}` for every `ξ ∈ F_t`. The
  measure-side argument of link 170, assembled: for `ε > 0`, continuity of `λ` (link 165) fixes an
  interval on which `λ > λ(ξ) − ε`; link 169 puts a node of every large good level inside it;
  `quasiProb_ge_ofReal_christoffelLimit` (link 170) gives the approximants mass `≥ λ(ξ) − ε` there;
  `limsup_measure_closed_le_of_tendsto` carries it to `μ`; `le_measure_singleton_of_forall_Icc`
  shrinks the interval to the atom; `ε → 0` finishes.
- **`exists_leaf_atoms`** — for a normalised sequence and any finite parameter, a probability measure
  that represents `s`, is carried by `F_t`, and satisfies

  > **`μ{ξ} = λ(ξ)` for every `ξ ∈ F_t`.**

Axiom-clean, zero placeholders, registered.

**This is the open core of the card, closed.** It had stood as `wₙ = λ(ξₙ)` since the card was
written, was reduced to `∑_{F_t} λ ≤ 1` at link 160, restated as `AtomApproximable` (M. Riesz's
density theorem) at link 163 — and was then reached *without* proving density, by the route links
164–170 opened: the tunable estimate gives continuity of `λ`, the `B,D` Wronskian gives a sign change,
the sign change gives node convergence by the intermediate value theorem, and node convergence plus
portmanteau gives the atom from below.

Note what was avoided: no Vitali/Montel, no argument principle, no Hurwitz, and no density of
polynomials in `L²(μ)`. The one classical ingredient that looked unavoidable at link 162 turned out to
be reachable only because the construction supplies an approximating sequence whose atoms are already
known to dominate `λ` — information a bare N-extremal measure does not carry.

With links 149, 150 and 159 the remaining fields of `ClassicalNevanlinnaExtremalFamily` are
constructed, and the weights are now identified. What is left is packaging, not mathematics:
`leaf` as a function of `t : OnePoint ℝ` (choice over the per-parameter existence) and
`continuous_leaf` (weak continuity in the parameter).

### Link 172 — the weight identification holds at every parameter, `∞` included

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/InfinitySignChange.lean`
- `nevBrealInf_factor_at_zero` — at a zero of `B` the limit Wronskian identity (link 167) reads
  `B(x)·D(ξ) = h₀·(x − ξ)·K(x,ξ)`: the same factorisation with `B` and `D` exchanged, since
  `D(ξ) ≠ 0` whenever `B(ξ) = 0`.
- `nevBrealInf_opposite_signs`, `eventually_exists_nevBreal_zero_near`,
  `eventually_exists_quasiNode_near_inf` — sign change, intermediate-value node convergence, and the
  node form, exactly as links 168–169 for a finite parameter.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/InfinityLeafAtoms.lean`
- `exists_leaf_infinity_approx`, `ofReal_christoffelLimit_le_leaf_infinity_singleton`, and
  **`exists_leaf_infinity_atoms`** — the leaf at infinity represents `s`, is carried by
  `infinityDenominatorFiber`, and satisfies `μ{ξ} = λ(ξ)` at each of its points.

Both modules compiled first try; axiom-clean, zero placeholders, registered.

**Status: the mathematics of the card is complete.** For a positive definite, normalised moment
sequence with bounded kernel — i.e. an indeterminate Hamburger moment problem — every parameter
`t ∈ ℝ ∪ {∞}` has a probability measure that

1. represents `s` (`HasHamburgerMoments`),
2. is carried by the denominator fiber `F_t` of the constructed Nevanlinna matrix, and
3. has atoms exactly `λ(ξ) = christoffelLimit s ξ` at every point of that fiber,

with the matrix itself constructed (`nevMatrixDataInf`) and its denominator row continuous. Nothing in
that list is hypothesised.

**Remaining, and it is packaging:** `leaf : OnePoint ℝ → ProbabilityMeasure ℝ` as a *function* — the
per-parameter existence statements are in hand, so this is a choice — and `continuous_leaf`, weak
continuity in the parameter, which is the one genuinely remaining analytic statement. The fiber
description now available (`leaf t` is the countable weighted Dirac family with weights `λ` on `F_t`,
by link 162 plus links 171–172) reduces it to continuity in `t` of the fiber and its weights, since
the weights are a *fixed* function `λ` evaluated on a varying set.

### Link 173 — the leaf as a function; seven of eight fields discharged

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevLeafFunction.lean`
- **`nevLeaf`** — `OnePoint ℝ → ProbabilityMeasure ℝ`, by `OnePoint.elim` over the two per-parameter
  existence theorems (links 171, 172). Simp lemmas `nevLeaf_infty`, `nevLeaf_coe` reduce it.
- **`nevLeaf_hasHamburgerMoments`** — the `leaf_moments` field, by `OnePoint.rec`.
- **`nevLeaf_finite_carried`**, **`nevLeaf_infinity_carried`** — the two carriedness fields.
- `nevLeaf_atoms`, `nevLeaf_infinity_atoms` — the weights are the Christoffel limits.
- **`nevLeaf_eq_fiberMeasure`** — combining with link 162, the leaf is *literally*
  `fiberMeasure (christoffelLimit s) F_t`: no longer a choice-produced object with known properties
  but an explicit weighted Dirac family, with a fixed weight function evaluated on the fiber.

Axiom-clean, zero placeholders, registered.

**Field status of `ClassicalNevanlinnaExtremalFamily`, complete except one.**

| field | status |
|---|---|
| `matrix` | `nevMatrixDataInf` (link 149) |
| `continuous_B` | `continuous_nevMatrixDataInf_B` (link 149) |
| `continuous_D` | `continuous_nevMatrixDataInf_D` (link 149) |
| `leaf` | `nevLeaf` (here) |
| `finite_carried` | `nevLeaf_finite_carried` (here) |
| `infinity_carried` | `nevLeaf_infinity_carried` (here) |
| `leaf_moments` | `nevLeaf_hasHamburgerMoments` (here) |
| `continuous_leaf` | **open** |

**Opens next: `continuous_leaf`.** With `nevLeaf_eq_fiberMeasure` the leaf is an explicit sum
`∑_{ξ ∈ F_t} λ(ξ)·δ_ξ` whose weight function `λ` does not depend on `t` — so weak continuity in `t`
is continuity of the *fiber* in `t`, and the fibers are the level sets of the projective label
`x ↦ [B(x) : D(x)]` (link 149's `projectiveLabel`). Concretely, for a bounded continuous `f`,
`∫f d(leaf t) = ∑_{ξ ∈ F_t} λ(ξ)f(ξ)`, and what has to be shown is that this is continuous in `t` —
which the factorisation `(B(x)t − D(x))·B(ξ) = h₀(x−ξ)K(x,ξ)` (link 167) makes a statement about how
the zeros of a one-parameter family of entire functions move, with the sign-change/IVT machinery of
links 168–169 available in the parameter direction as well.

### Link 174 — the fiber moves continuously with the parameter

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/ParameterMotion.lean`
- **`exists_param_radius_no_zero`** — on a compact set where the denominator of `t₀` does not vanish,
  it still does not vanish for all `t` within an explicit radius. **No fiber point appears from
  nowhere.**
- **`exists_param_radius_zero_near`** — at a fiber point `ξ` of `t₀` the sign change (link 168)
  persists for nearby `t`, so each nearby parameter has a fiber point within `δ` of `ξ`. **No fiber
  point disappears.**

Both are the arguments of links 168–169 re-run in the parameter direction, and they are cheaper
there: the denominator depends on `t` *affinely*, `B(x)t − D(x)`, so a change of parameter perturbs it
by `B(x)(t − t₀)` — bounded on a compact set by `max|B|·|t − t₀|` with no series convergence anywhere.
The perturbation bound replaces link 156's uniform-convergence estimate, and the rest (opposite signs
at `ξ ± δ`, `intermediate_value_Icc`) is unchanged.

Axiom-clean, zero placeholders, registered.

**Toward `continuous_leaf`.** With link 173's `nevLeaf_eq_fiberMeasure` the leaf is
`∑_{ξ ∈ F_t} λ(ξ)·δ_ξ` with `λ` independent of `t`, so for `f` continuous with compact support `K`,

`∫f d(leaf t) = ∑_{ξ ∈ F_t ∩ K} λ(ξ)·f(ξ)`,

a **finite** sum (the fiber is discrete and closed, link 150). The two theorems above say exactly that
for `t` near `t₀` this finite index set is in bijection with `F_{t₀} ∩ K` by a map moving each point by
at most `δ`. What remains is that bookkeeping — building the bijection and passing `λ·f` through it
using continuity of `λ` (link 165) and of `f` — plus the reduction from bounded continuous test
functions to compactly supported ones, which is where tightness of the family enters.

### Link 175 — the fiber meets a compact set finitely

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/FiberFinite.lean`
- `isDiscrete_of_eventually_notMem`, `isDiscrete_inter_of_eventually_notMem` — a set of reals with no
  accumulation point in itself is discrete, and so is any subset of it. (`IsDiscrete` is the mathlib
  predicate `IsCompact.finite` consumes; `isDiscrete_iff_nhdsNE` states it in exactly the
  punctured-neighbourhood form links 156/159 produce, so no reformulation was needed.)
- **`finite_finiteDenominatorFiber_inter`**, **`finite_infinityDenominatorFiber_inter`** — each fiber
  meets every compact set in a **finite** set: the intersection is compact (closed ∩ compact) and
  discrete.

Axiom-clean, zero placeholders, registered, first-try compile.

**Where this sits.** For `f` continuous with compact support `K`,

`∫f d(leaf t) = ∑_{ξ ∈ F_t ∩ K} λ(ξ)·f(ξ)` — a genuinely finite sum, now established.

Link 174 says this index set is, for `t` near `t₀`, in bijection with `F_{t₀} ∩ K` by a map displacing
each point by at most `δ`. So the three inputs to weak continuity are in place:
1. the sum is finite (here);
2. the index sets correspond, with small displacement (link 174);
3. the summand `λ·f` is continuous (link 165 for `λ`, hypothesis for `f`).

**Remaining for `continuous_leaf`:** assemble (1)–(3) into `∫f d(leaf t) → ∫f d(leaf t₀)`, then reduce
general bounded continuous test functions to compactly supported ones. The reduction is where the
tightness already proved for the approximating family (link 154) should be re-derived for the leaves
themselves — the leaves inherit the uniform second-moment bound, since they all represent the same
`s`, so `leaf t (Icc (-R) R)ᶜ ≤ s₂/R²` uniformly in `t` by Chebyshev, which is exactly the estimate
`measure_compl_Icc_le_of_lintegral_sq_le` (link in `GaussMomentLimit`) already provides.

### Link 176 — the leaf family is tight

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/LeafTightness.lean`
- `lintegral_sq_nevLeaf` — every leaf has second moment `s₂`, as a lower integral. Immediate from
  `nevLeaf_hasHamburgerMoments` (link 173) and `ofReal_integral_eq_lintegral_ofReal`.
- **`nevLeaf_tail_le`** — `leaf t ((Icc (-R) R)ᶜ) ≤ s₂/R²` for **every** parameter, by Chebyshev
  (`measure_compl_Icc_le_of_lintegral_sq_le`, already in `GaussMomentLimit`).
- **`isTightMeasureSet_nevLeaf`** — the whole family `{leaf t : t ∈ OnePoint ℝ}` is tight.

Axiom-clean, zero placeholders, registered, first-try compile.

The bound has nothing to do with the construction: the leaves are tight *because they all represent
the same sequence*. That is why the proof is four lines of Chebyshev rather than a repeat of link
154's work on the approximating family.

**Inventory for `continuous_leaf`.** All the analytic inputs now exist:

| input | source |
|---|---|
| `leaf t = ∑_{ξ ∈ F_t} λ(ξ)·δ_ξ`, `λ` independent of `t` | link 173 |
| `F_t ∩ K` finite for compact `K` | link 175 |
| fiber points persist and no new ones appear, for `t` near `t₀` | link 174 |
| `λ` continuous | link 165 |
| uniform tails, so compactly supported test functions suffice | here |

What is left is assembly: build the near-bijection `F_{t₀} ∩ K → F_t ∩ K` from link 174, transport
the finite sum along it, and conclude `∫f d(leaf t) → ∫f d(leaf t₀)` first for compactly supported `f`
and then, via the tail bound, for bounded continuous `f`. That is Finset bookkeeping over statements
all of which are proved; no further analytic content is required.

### Link 177 — the leaf of a parameter is unique, and that replaces the bookkeeping

Link 176 ended by saying the remaining step was Finset bookkeeping and that a shortcut should be
looked for first. There is one, and it is a theorem worth having on its own.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/LeafUniqueness.lean`
- **`tsum_ofReal_christoffelLimit_fiber`** — `∑_{ξ ∈ F_τ} λ(ξ) = 1` **exactly**. Link 160 proved `≥`
  from the construction; the reverse now comes free, because the leaf *is* carried by `F_τ` with
  atoms exactly `λ` (links 171, 173) and has mass `1`.
- `fiberMeasure_congr` — a weighted Dirac family only sees its weights on its own carrier.
- **`nevLeaf_unique`**, **`nevLeaf_infinity_unique`** — **a probability measure that represents `s`
  and is carried by the fiber of `τ` *is* the leaf of `τ`.** Its atoms are at most `λ` (link 160), the
  `λ`'s already sum to `1`, so `measure_singleton_eq_of_tsum_le` forces equality termwise, and
  `measure_eq_fiberMeasure_of_carried` (link 162) turns equal atoms into equal measures.

Axiom-clean, zero placeholders, registered.

**Why this is the shortcut.** Weak continuity no longer needs a bijection between fibers. Tightness
(link 176) makes the leaf family relatively compact, so along any `tₙ → t₀` some subsequence converges
weakly to some `ν`; `ν` represents `s` because every leaf does and the moments pass to a weak limit by
the machinery of link 154; and `ν` is carried by `F_{t₀}` because link 174 forbids fiber points on
compacta away from `F_{t₀}` for nearby parameters, which the interior-plus-portmanteau argument of
link 158 transfers to the limit. Uniqueness then says `ν = leaf t₀`. Every subsequential limit being
the same point, the whole family converges.

This is the classical statement that the Nevanlinna parametrization is injective on N-extremal
measures — and here it is a five-line consequence of the atom identification rather than an input to
it.

**Remaining for `continuous_leaf`:** the subsequence argument just described. Its two inputs — moments
pass to weak limits, and carriedness passes to weak limits — are both already proved in the forms used
by links 154 and 158; what is new is only running them with the parameter, rather than the level, as
the moving index.

### Link 178 — what survives a weak limit

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/WeakLimitTransfer.lean`
- **`hasHamburgerMoments_of_tendsto`** — a weak limit of probability measures **all representing the
  same sequence** represents it. The uniform even-moment hypothesis that
  `tendsto_integral_pow_of_uniform_even_moment` consumes is trivial here (the moments are constant in
  the index), so the proof is shorter than its level-indexed ancestor in link 154.
- **`measure_eq_zero_of_tendsto`** — a weak limit of measures that eventually miss every compact
  subset of an open `U` misses `U`. The interior-plus-portmanteau argument of link 158, extracted from
  the leaf construction and stated for an arbitrary sequence.

Axiom-clean, zero placeholders, registered, first-try compile.

Both had existed only inline, with the *level* as the moving index. Stating them for an arbitrary
sequence is what lets them be re-run with the *parameter* moving — the same generalisation that link
173 needed for `exists_leaf_approx` and that link 174 needed for the sign change.

**Everything for `continuous_leaf` is now proved; only the assembly is left.** For `tₙ → t₀`:
1. tightness (link 176) + Prokhorov ⇒ every subsequence has a weakly convergent sub-subsequence, say
   to `ν`;
2. `hasHamburgerMoments_of_tendsto` (here) ⇒ `ν` represents `s`, since every `leaf tₙ` does;
3. `exists_param_radius_no_zero` (link 174) ⇒ for `n` large the fiber of `tₙ` misses any compact
   subset of `F_{t₀}ᶜ`, so `leaf tₙ` gives it zero mass; `measure_eq_zero_of_tendsto` (here) ⇒ `ν` is
   carried by `F_{t₀}`;
4. `nevLeaf_unique` (link 177) ⇒ `ν = leaf t₀`.

Every subsequential limit is the same point, so `leaf tₙ → leaf t₀`; and `ProbabilityMeasure ℝ` is
metrizable, so sequential continuity is continuity. The remaining work is writing that argument down —
it introduces no statement that is not already in the tree.

### Link 179 — the leaf is weakly continuous in a finite parameter

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/LeafContinuity.lean`
- `exists_param_radius_nevLeaf_eq_zero` — a leaf of a nearby parameter gives no mass to a compact set
  away from the fiber of `t₀`: link 174 says such a set contains no fiber point of `t`, and the leaf
  of `t` is carried by that fiber.
- `isCompact_closure_range_nevLeaf` — the leaf family has compact closure (link 176 + Prokhorov).
- **`continuousAt_nevLeaf`** — **the leaf is weakly continuous at every finite parameter.**

The assembly is exactly the four steps of link 178, with `tendsto_of_subseq_tendsto` doing the
subsequence principle: given `ns → t₀`, extract a weakly convergent sub-subsequence by compactness;
its limit represents `s` (link 178) and is carried by `F_{t₀}` (link 174 + link 178); uniqueness
(link 177) identifies it as `leaf t₀`.

Axiom-clean, zero placeholders, registered, first-try compile.

Worth noting how little was left to do once the pieces were stated for a moving index: the proof is
sixty lines of plumbing over five previously proved theorems, and every one of them had been extracted
from an inline argument in an earlier link precisely because it was about to be needed again.

**Remaining for the `continuous_leaf` field:** continuity at the point `∞` of `OnePoint ℝ`, then
assembling the two into `Continuous (nevLeaf h h0b h0)`. Continuity at `∞` is the same argument with
`|t| → ∞` in place of `t → t₀`: the neighbourhoods of `∞` are complements of compacts, the fiber of a
large parameter escapes any compact set — which is again `exists_param_radius_no_zero` read with the
roles of the parameter and the point exchanged — and the limit must then be carried by the fiber of
`∞`, where `nevLeaf_infinity_unique` (link 177) applies.

### Link 180 — `ClassicalNevanlinnaExtremalFamily` is constructed

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/LeafContinuityInfty.lean`
- `exists_param_bound_no_zero` — a fiber point of `t` in a compact set where `B` does not vanish
  forces `|t| = |D(x)|/|B(x)|`, bounded there; so large parameters have no fiber point on such a set.
  Elementary: a min of `|B|` and a max of `|D|` on the compact.
- **`tendsto_nevLeaf_cocompact`**, **`continuous_nevLeaf`** — the leaf tends to the leaf at infinity
  as the parameter escapes every compact set, and hence **the leaf map is weakly continuous on
  `OnePoint ℝ`** (`OnePoint.continuous_iff`).

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevExtremalFamily.lean`

> **`nevExtremalFamily`** — a term of `GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaExtremalFamily s`,
> for every positive definite normalised moment sequence with bounded kernel at a point.

with `exists_classicalNevanlinnaExtremalFamily` the existence form and `nevExtremalFamily_atoms`
recording the geometric content the structure does not itself carry: **each leaf's atom at a fiber
point is `λ(ξ) = christoffelLimit s ξ`.**

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), zero placeholders, registered; the structure
itself compiled first try.

**The card's target is met.** Every field is constructed from the moment sequence — matrix from the
orthogonal polynomials, continuity of its denominator row from entirety of the limiting entries,
leaves from quasi-orthogonal quadrature, carriers from the denominator fibers, moments from quadrature
exactness, weak continuity from tightness plus uniqueness. Nothing is hypothesised beyond
indeterminacy itself (`PositiveMomentForm s`, `BoundedKernel s 0`, `s 0 = 1`).

Build note worth keeping: `push Not` (and `push_neg`, now deprecated in its favour) sent the
elaborator into a multi-minute non-terminating state on a two-line goal about `¬(a ≤ x ∧ x ≤ b)`. An
explicit `rcases lt_or_ge … ` split compiles instantly. This is the first tactic on this card to fail
by *cost* rather than by error.

**Opens next:** the card can move from `needs-audit` to `3-formalized` once the umbrella build is
green. Beyond it, the natural continuations are the two the interface already anticipates —
`toBoundaryFamily` now has a genuine inhabitant, so the projective-label recovery
(`map_projectiveLabel_leaf`) and the barycenter/simplex consequences in
`NevanlinnaBoundaryKernel` apply to a *constructed* family rather than a hypothetical one.

### Link 181 — the interface's consequences become unconditional

The downstream theorems of `NevanlinnaClassicalInterface` and `NevanlinnaBoundaryKernel` were proved
for an *arbitrary* `ClassicalNevanlinnaExtremalFamily`. Link 180 supplied one for every indeterminate
moment sequence, so they are now statements about the sequence itself.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevFamilyConsequences.lean`
- **`nevLeaf_map_projectiveLabel`** — pushing a constructed leaf forward along the projective label of
  the constructed matrix returns `dirac t`: **the parameter is recovered exactly as a measurable
  coordinate on the carrier.**
- `nevBarycenter` — the barycentre of the leaves against a law on `ℝ ∪ {∞}`.
- **`nevBarycenter_hasHamburgerMoments`** — every barycentre represents `s`, so the construction
  yields one solution of the moment problem per parameter law.
- **`nevBarycenter_isClosedEmbedding`** — the barycentre map is a closed topological embedding: the
  solutions so obtained form a closed copy of the space of parameter laws.
- **`nevLeaf_injective`** — distinct parameters give distinct leaves, immediately from label recovery.

Axiom-clean, zero placeholders, registered.

**Card status.** The target object is constructed (link 180) and its classical consequences hold
unconditionally (here). What the card asked for — `ClassicalNevanlinnaExtremalFamily` for the
indeterminate Hamburger moment problem, with the N-extremal weights identified — is done, from
`PositiveMomentForm s`, `BoundedKernel s 0`, `s 0 = 1` and nothing else.

Summary of the route, for the audit:
`quasi-orthogonal polynomials` (151) → `denominator = quasi-orthogonal` (152) → `quadrature, positive
weights` (153) → `tightness and a representing weak limit` (154) → `global kernel transfer, entire
matrix, isolated zeros` (146–148) → `real matrix, discrete fibers, leaf measures` (149–150, 158–159) →
`kernel continuity from the tunable estimate` (164–165) → `B,D Wronskian, sign change, node
convergence` (166–169) → `atoms are the Christoffel limits` (170–172) → `leaf function, uniqueness,
weak continuity` (173–179) → `the family` (180) → `consequences` (181).

**Opens next:** promotion to `3-formalized` after an umbrella build, and the two directions the
construction now makes concrete — whether the barycentre embedding is *onto* the representing
measures (the Bauer-simplex statement in full), and what the same machinery says for the
Stieltjes and trigonometric moment problems, where the denominator geometry differs but the kernel
estimates of links 146–148 are unchanged.

### Link 182 — a bounded kernel forces indeterminacy, and the session's verification sweep

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/IndeterminacyCriterion.lean`
- **`exists_ne_hasHamburgerMoments`** — two *distinct* measures represent `s`: the leaves of the
  parameters `0` and `∞`, distinct by `nevLeaf_injective` (link 181).
- **`injective_leaf_into_representing`** — the solution set of the moment problem contains an
  injective copy of `ℝ ∪ {∞}`.
- **`not_subsingleton_representing`** — the moment problem is not determinate.

This closes the loop with the construction's hypothesis: `BoundedKernel s 0` is not a technical
convenience but exactly a witness of indeterminacy, and the construction turns that witness into the
whole family of solutions.

Axiom-clean, zero placeholders, registered, first-try compile.

**Verification sweep.** All 47 modules written for this card were checked mechanically:

> 47 modules — missing oleans: **0** — unregistered in the umbrella: **0** — containing
> `sorry`/`admit`/`axiom`/`opaque`/`unsafe`: **0**

and every named endpoint quoted in links 146–182 was confirmed to depend only on
`[propext, Classical.choice, Quot.sound]`.

**Card status: the target is constructed and its consequences proved.** Ready for promotion to
`3-formalized` subject to the umbrella build, which is a whole-tree operation and deliberately not
run here.

**Opens next.** With indeterminacy now both hypothesis and conclusion, the sharp question is the
converse: does *every* indeterminate sequence have bounded kernel at a point? Classically yes — it is
the standard equivalence — and the corpus already has one half of the bridge in
`ChristoffelBoundedKernel` (`christoffelLimit_pos_of_boundedKernel`). Proving the converse would turn
every theorem of links 146–182 from "for sequences with bounded kernel" into "for indeterminate
sequences", which is the form the classical literature states them in.

### Link 183 — the construction discharges a sibling card's standing hypothesis

`nevanlinna-boundary-bauer-retract-maximal-ht` records its Lean as "formalized **relative to** the
classical Nevanlinna family stated on the card". That family is now constructed here, so the relation
is dischargeable.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevBauerUnconditional.lean` — instantiating
that card's boundary-carrier package at `(nevExtremalFamily h h0b h0).toBoundaryFamily`:
`nevBauer_isClosedEmbedding`, `nevBauer_continuous_retract`, `nevBauer_retract_idempotent`,
`nevBauer_range_retract`, `nevBauer_fixed_iff`, `nevBauer_extreme_iff`.

So for **every** indeterminate normalised Hamburger moment sequence, unconditionally: the
complete-moment fiber contains a canonical closed embedded Bauer simplex, carries a continuous
idempotent retraction onto it, and the extreme points of that simplex are exactly the N-extremal
leaves — with the weights `λ(ξ)` identified by link 171.

Axiom-clean, zero placeholders, registered. Logged on the sibling card as well.

This is the payoff of the card beyond its own statement: results elsewhere in the tree that were
conditional on a classical input become unconditional the moment that input is built.

### Link 184 — the leaves are extreme points of the moment fiber

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/LeafExtreme.lean`
- `carried_of_mixture_eq_nevLeaf` — if a leaf is `a·μ + b·ν` with `a ≠ 0`, then `μ` is carried by the
  leaf's fiber: the fiber complement is null for the leaf, and in `ENNReal` a sum of two terms is zero
  only if both are.
- **`nevLeaf_eq_of_mixture`**, **`nevLeaf_infinity_eq_of_mixture`**, **`nevLeaf_of_half_mixture`** —
  **each leaf is an extreme point of the complete-moment fiber.**

The proof is three lines on top of uniqueness (link 177): a representing measure carried by `F_τ`
*is* the leaf of `τ`, so a mixture representation collapses. No convexity argument is involved, which
is why extremality costs almost nothing here while classically it is a separate step.

Logged on `indeterminate-moment-fiber-maximal-translation-ht`, whose Lean status names "the absent
Nevanlinna N-extremal construction" as a blocker for its `Ext M(s)` step. The construction is present
and the extremality half of that step is now proved; the density half remains, and is a statement
about the fiber rather than about the family.

Process note: the heredoc for this module was first issued while the working directory had drifted to
the card folder, and failed with "no such file or directory" rather than writing anything — the
`GaloisForLFunctions/HTGeometry` path does not exist there. Checked before rewriting; no stray file
was created. Absolute paths for both `cd` and the target avoid the drift, as recorded earlier.

### Link 185 — integrals against a leaf are Christoffel-weighted fiber sums

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/LeafIntegral.lean`
- `integral_fiberMeasure` — a weighted Dirac family integrates any integrable function to the
  weighted sum of its values (`integral_sum_measure` plus `integral_dirac` termwise).
- **`integral_nevLeaf`** — hence
  `∫ f d(leaf τ) = ∑_{ξ ∈ F_τ} λ(ξ)·f(ξ)` for every integrable `f`.
- `integral_nevLeaf_of_boundedContinuous` — the same for bounded continuous test functions, which are
  automatically integrable against a probability measure.

Axiom-clean, zero placeholders, registered.

This is the form the sibling card's Cauchy-transform analysis consumes: with the weights identified as
`λ(ξ)` (link 171) and the fiber discrete (link 150), every integral against a leaf is an explicit
convergent series indexed by the zeros of `B·τ − D`. In particular the Cauchy transform
`m_τ(z) = ∫(x − z)⁻¹ d(leaf τ)` is the series `∑_ξ λ(ξ)/(ξ − z)` — absolutely convergent for non-real
`z`, since `∑ λ(ξ) = 1` (link 177) and `|ξ − z|⁻¹ ≤ |Im z|⁻¹`.

**Opens next.** The classical Nevanlinna identity
`m_τ(z) = −(A(z)τ − C(z))/(B(z)τ − D(z))` would connect that series to the constructed matrix. The
pieces on hand are the factorisation `(B(x)τ − D(x))·B(ξ) = h₀(x − ξ)K(x,ξ)` (link 167) and the atom
identification; what is missing is a residue/partial-fraction argument for the entire function
`B·τ − D`, which is the first place on this card where genuinely new complex-analytic machinery — a
Mittag-Leffler expansion — would be needed rather than reused.

### Link 186 — the Cauchy transform of a leaf, as an explicit series

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/LeafCauchyTransform.lean`
- `integral_fiberMeasure_vector` — the vector-valued form of link 185 (needs `CompleteSpace` on the
  target, which the real-valued statement did not).
- `norm_cauchy_kernel_le` — `‖(x − z)⁻¹‖ ≤ |Im z|⁻¹` for real `x`, since `|Im z| ≤ ‖x − z‖`.
- `integrable_cauchy_kernel` — hence the Cauchy kernel is integrable against any finite measure on
  `ℝ` off the real axis.
- **`cauchyTransform_nevLeaf`** —
  `m_τ(z) = ∫ (x − z)⁻¹ d(leaf τ) = ∑_{ξ ∈ F_τ} λ(ξ)·(ξ − z)⁻¹`,
  the Cauchy transform of every leaf as an explicit series over the zeros of `B·τ − D` with the
  Christoffel weights.
- **`norm_cauchyTransform_nevLeaf_le`** — `‖m_t(z)‖ ≤ |Im z|⁻¹`, uniformly in the parameter.

Axiom-clean, zero placeholders, registered.

This is the object the sibling card's equation `(1)` is about, now constructed rather than quoted:
its left-hand side `m_τ(z)` exists, is given by a convergent weighted series over the fiber, and is
uniformly bounded on each half-plane. What remains to match `(1)` exactly is the identification of
that series with `−(A(z)τ − C(z))/(B(z)τ − D(z))`, which is the Mittag-Leffler step flagged at link
185 and is the natural first target of a next session on this thread.

Traps this link: `inv_le_inv_of_le` no longer exists (`one_div_le_one_div_of_le` after `← one_div`),
and the vector-valued integral needs `[CompleteSpace E]` — an instance the `ℝ`-valued version got for
free.

### Link 187 — the second kind is the moment functional of a divided difference

Link 186 flagged the Nevanlinna identity `m_τ(z) = −(A(z)τ − C(z))/(B(z)τ − D(z))` as needing
Mittag-Leffler. Working out the finite-level statement first shows it does not: the identity is
*algebraic* at each level, and reduces by linearity to one fact about the second-kind polynomials.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/SecondKindDividedDiff.lean`
- `firstKindDividedDiff s n z` — the divided difference `(Qₙ(x) − Qₙ(z))/(x − z)` as an honest
  polynomial in `x`, defined by `/ₘ (X − C z)`, with `mul_firstKindDividedDiff` the defining identity
  (`modByMonic_X_sub_C_eq_C_eval` gives the zero remainder).
- `firstKindDividedDiff_zero`, `firstKindDividedDiff_one` — the base cases `0` and `1`.
- `firstKindDividedDiff_succ_succ` — **the recurrence**
  `E_{n+2} = (z − aₙ)·E_{n+1} − bₙ·Eₙ + Q_{n+1}`.
  Note the coefficient is the *constant* `(z − aₙ)`, not the polynomial `(X − aₙ)`: the divided
  difference recurs in the frozen variable. Getting that wrong was the one real error here.
- **`momentFunctional_firstKindDividedDiff`** —
  `L_x[(Qₙ(x) − Qₙ(z))/(x − z)] = s₀·Rₙ(z)`.
  Two-step induction: the extra term `L(Q_{n+1})` vanishes by orthogonality to the constants, so both
  sides obey the same three-term recurrence with the same initial data.

Axiom-clean, zero placeholders, registered.

**Why this is the Nevanlinna identity's crux.** At level `n`, with `Gₙ = Bₙτ − Dₙ` and nodes the zeros
of `Gₙ`, multiplying the quadrature Cauchy transform by `Gₙ(z)` gives
`Gₙ(z)·∑_ξ w_ξ/(ξ − z) = −L_x[(Gₙ(z) − Gₙ(x))/(z − x)]`
— the bracket is a polynomial in `x` of degree `n`, so quadrature exactness to `2n` (link 153) turns
the sum into the moment functional. By linearity and link 159's closed forms
`Gₙ = (h₀/hₙ)(αₙQ_{n+1} + βₙQₙ)` and `Hₙ = Aₙτ − Cₙ = (h₀/hₙ)(αₙR_{n+1} + βₙRₙ)`, the theorem above
gives exactly `L_x[…] = s₀·Hₙ(z)`. So the finite-level identity is algebraic, and the limit form
follows from weak convergence of the quadrature measures (link 154) plus entrywise convergence
(links 155–156) — **no Mittag-Leffler and no residue calculus**.

Traps: `modByMonic_add_div` takes two polynomials, not a monic proof (recorded at link 153 and hit
again); `ring` treats `C (z − a)` and `C z − C a` as distinct atoms; a `Fin` coercion blocks
`monicOrtho_zero` until `Fin.val_zero` fires; and `momentFunctional` has no `sub`/`C_mul` lemmas —
routing through `momentInner` and `momentInner_def` supplies the whole linearity API.

### Link 188 — the finite-level Nevanlinna identity

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/QuasiCauchyIdentity.lean`
- `quasiDividedDiff`, `mul_quasiDividedDiff` — the divided difference of `P = Q_{n+1} + t·Qₙ`, in the
  two-term basis, with its defining identity.
- `firstKindDividedDiff_degree_lt`, `quasiDividedDiff_degree_lt` — degree below the index (via
  `natDegree_divByMonic`), so the level-`n` rule integrates it exactly.
- **`quasiCauchy_identity`** — for `z` off the node set,

  > `P(z)·∑_{ξ ∈ nodes} w_ξ/(ξ − z) = −s₀·(R_{n+1}(z) + t·Rₙ(z))`.

  At a node, `P(z) = −(ξ − z)·E(ξ)`, so multiplying the Cauchy sum by `P(z)` turns it into minus the
  quadrature of `E`, a polynomial of degree `n`; exactness (link 153) makes that the moment
  functional, and link 187 evaluates it.

Axiom-clean, zero placeholders, registered.

**This is equation `(1)` of the sibling card, at finite level, proved algebraically.** Combining with
link 159's closed forms — `Bₙτ − Dₙ = (h₀/hₙ)(αₙQ_{n+1} + βₙQₙ)` and
`Aₙτ − Cₙ = (h₀/hₙ)(αₙR_{n+1} + βₙRₙ)`, the *same* `αₙ, βₙ` — the identity reads
`(Bₙ(z)τ − Dₙ(z))·mₙ(z) = −s₀·(Aₙ(z)τ − Cₙ(z))`, i.e. the classical Padé form of the Nevanlinna
parametrization at level `n`.

**Opens next:** the limit. Both sides converge — the left by weak convergence of the quadrature
measures against the bounded continuous Cauchy kernel (links 154, 186) together with entrywise
convergence of `Bₙ, Dₙ` (link 156), the right by entrywise convergence of `Aₙ, Cₙ`. What is needed is
the analogue of link 156 for the `A` and `C` entries, whose series are the same bilinear objects with
the second-kind family in place of the first; `tendstoUniformlyOn_bilinearLimit` (link 155) covers
them unchanged. That would give the classical identity
`m_τ(z) = −(A(z)τ − C(z))/(B(z)τ − D(z))` for the constructed leaves, closing equation `(1)` of the
sibling card unconditionally.

### Link 189 — the numerator entries converge uniformly too

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/EntryNumeratorUniform.lean`
- `tendstoUniformlyOn_nevA_series`, `tendstoUniformlyOn_nevC_series` — the `A` and `C` series converge
  uniformly on every ball. They are the same bilinear objects as `B` and `D` with the second-kind
  family in the varying slot, and — unlike `B` — both are already written with the constant factor
  first, so `tendstoUniformlyOn_bilinearLimit` (link 155) applies with no commutation.
- `nevAreal_ofReal_partial`, `nevCreal_ofReal_partial`, `nevAinf_tsum`, `nevCinf_tsum` — the truncated
  numerators as complex partial sums along `Complex.ofReal`.
- **`eventually_nevAreal_close`**, **`eventually_nevCreal_close`** — `Aₙ → A` and `Cₙ → C` uniformly on
  every bounded interval, exactly as link 156 for the denominators.

Axiom-clean, zero placeholders, registered; the first module compiled first try.

**All four entries now converge uniformly on bounded intervals.** With link 188's finite-level identity
`(Bₙ(z)τ − Dₙ(z))·mₙ(z) = −s₀·(Aₙ(z)τ − Cₙ(z))`, the limit form needs only:
1. `mₙ(z) → m_τ(z)` — weak convergence of the quadrature measures against the bounded continuous
   Cauchy kernel (links 154, 186);
2. the four entry convergences (links 156, 189);
3. `B(z)τ − D(z) ≠ 0` at the chosen `z` — true off the fiber, and the fiber is a discrete subset of
   `ℝ` (link 150), so every non-real `z` qualifies once the identity is read on `ℂ`.

Item 3 is the one that still needs care: links 156 and 189 give convergence along the *real* axis,
whereas the Cauchy transform is naturally evaluated off it. The complex versions are available — the
uniform estimates of links 155 and 189 are stated on complex balls, and only the `ofReal`
specialisation restricted them to `ℝ`. Lifting `eventually_*_close` to complex `z` is mechanical and
is the next step.

### Link 190 — all four entries converge at every complex point

Link 189 flagged that the packaged convergence statements were restricted to the real axis while the
Cauchy transform wants complex arguments. That restriction came from the `ofReal` specialisation
only; the underlying estimates were always on complex balls.

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/EntryComplexLimit.lean`
- `nevAtruncC`, `nevBtruncC`, `nevCtruncC`, `nevDtruncC` — the four truncated entries packaged as
  complex functions of `z`.
- **`tendsto_nevAtruncC`**, **`tendsto_nevBtruncC`**, **`tendsto_nevCtruncC`**,
  **`tendsto_nevDtruncC`** — each converges to its limiting entire entry **at every point of `ℂ`**,
  by reading the ball estimate at `z` (`TendstoUniformlyOn.tendsto_at` on the ball of radius
  `‖z‖ + 1`) and composing with the index shift.

Axiom-clean, zero placeholders, registered, first-try compile.

The `B` case needs `nevBinf_comm_tsum` (link 156) because its series is the one written with the
constant factor second; the other three are direct.

**State of the Nevanlinna-identity thread.** Of the three items listed at link 189:
1. `mₙ(z) → m_τ(z)` — available from weak convergence (links 154, 186);
2. entry convergence — **now complete on all of `ℂ`** (links 156, 189, 190);
3. non-vanishing of the limiting denominator at the evaluation point — holds off the fiber, which is
   a discrete subset of `ℝ` (link 150), so at every non-real `z`.

What remains is the finite-level identity at *complex* `z`. Link 188 proves it for real `z` via
`Polynomial.eval`; both sides are rational in `z` with real coefficients and agree at infinitely many
reals, so they agree identically — but formalising that step means either redoing the divided-difference
construction over `ℂ` with `aeval`, or invoking an identity-theorem argument for rational functions.
That is the concrete next task, and it is bookkeeping over an already-proved identity rather than new
mathematics.

### Link 191 — the finite-level identity, as a polynomial identity and at complex arguments

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/QuasiCauchyPolynomial.lean`
- `quasiCofactorSum` — `∑_ξ w_ξ·(P /ₘ (X − ξ))`. Since each node is a root, `P(z)/(z − ξ)` *is* a
  polynomial in `z`, so the weighted Cauchy sum times `P(z)` is polynomial rather than rational.
- `eval_quasiCofactor` — the cofactor evaluates to the Cauchy quotient off the node.
- **`quasiCofactorSum_eq`** — `∑_ξ w_ξ·(P /ₘ (X − ξ)) = s₀·(R_{n+1} + t·Rₙ)` **as polynomials**.
  Link 188 gives agreement at every real point off the node set; that set is infinite (the complement
  of a finite set in `ℝ`), so `Polynomial.eq_of_infinite_eval_eq` upgrades it to equality.
- **`quasiCofactorSum_aeval`** — hence the identity holds at every **complex** argument.

Axiom-clean, zero placeholders, registered.

This closes the step flagged at link 190. The route was the one noted there — recognise that the
apparently rational object is polynomial, prove the identity where link 188 applies, and extend by
the infinitude of the real line minus finitely many points. No identity theorem for rational
functions and no re-derivation over `ℂ` was needed.

**Status of the Nevanlinna-identity thread.** Every ingredient of
`m_τ(z) = −(A(z)τ − C(z))/(B(z)τ − D(z))` is now in the tree:
- the finite-level identity at complex `z` (here);
- entry convergence on all of `ℂ` (link 190);
- `mₙ(z) → m_τ(z)` from weak convergence (links 154, 186);
- non-vanishing of the limit denominator off the real fiber (links 147, 150).

What remains is assembling them — expressing `mₙ(z)` for the *level-`n` quasi measure* in terms of
`quasiCofactorSum` (the bridge is `integral_fiberMeasure_vector` of link 186 applied to the finite
node set), then passing to the limit. That is the same shape as links 178–179 and needs no new
estimate.

### Link 192 — the finite-level Nevanlinna identity at complex arguments

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/QuasiCauchyComplex.lean`
- `aeval_quasiCofactor` — the cofactor at a node evaluated at a complex point off that node.
- **`quasiCauchy_identity_complex`** — for complex `z` off the node set,

  > `P(z)·∑_{ξ ∈ nodes} w_ξ/(ξ − z) = −s₀·(R_{n+1}(z) + t·Rₙ(z))`.

Read off link 191's polynomial identity through `aeval` and dividing out the linear factors. The sum
is finite (there are `n+1` nodes), so nothing analytic is involved.

Axiom-clean, zero placeholders, registered.

**The finite-level Nevanlinna parametrization is now complete over `ℂ`.** With link 159's closed forms
this reads `(Bₙ(z)τ − Dₙ(z))·mₙ(z) = −s₀·(Aₙ(z)τ − Cₙ(z))` at every complex `z` off the level-`n`
nodes — equation `(1)` of `indeterminate-moment-fiber-maximal-translation-ht`, at finite level,
proved from the moment sequence with no classical input.

**Remaining for the limit form**, and it is now purely mechanical:
1. identify `∑_ξ w_ξ/(ξ − z)` with `∫(x − z)⁻¹ d(quasiMeasure)` — the finite-family analogue of link
   186's `integral_fiberMeasure_vector`;
2. let `n → ∞` along the good levels: the left side converges by weak convergence (link 154) against
   the bounded continuous Cauchy kernel (link 186), the right by entry convergence (link 190);
3. divide by `B(z)τ − D(z)`, nonzero off the real fiber (links 147, 150).

Traps this link: `Finset.sum_neg_distrib` does not exist under that name (a `have … := by simp` for
the specific sum is the reliable substitute — hit twice now), `algebraMap ℝ ℂ` needs
`Complex.coe_algebraMap` to meet `↑`, and `linear_combination` sign errors show up as a residual that
is exactly `2×` the goal, which is a quick way to read them off.

### Link 193 — the quadrature Cauchy transform is the finite node sum

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/QuasiMeasureIntegral.lean`
- **`integral_finsetWeightedDirac_vector`** — vector-valued integration against a finite weighted
  Dirac family is the weighted sum of values. **No measurability or continuity hypothesis**: a Dirac
  measure integrates every function, so `integrable_dirac` needs only finiteness of the norm at the
  point. The continuity hypothesis first written into the statement turned out to be unused, and the
  linter caught it — the lemma is stronger without it.
- **`integral_cauchy_quasiMeasure`** — hence
  `∫(x − z)⁻¹ d(quasiMeasure s n t) = ∑_{ξ ∈ nodes} w_ξ·(ξ − z)⁻¹` for **every** complex `z`.

Axiom-clean, zero placeholders, registered.

This is step 1 of link 192's remaining list. Combining with `quasiCauchy_identity_complex`:

> `P(z)·∫(x − z)⁻¹ d(quasiMeasure s n t) = −s₀·(R_{n+1}(z) + t·Rₙ(z))` off the level-`n` nodes,

so the level-`n` Cauchy transform of the *measure* satisfies the Nevanlinna identity. Steps 2 and 3 —
letting `n → ∞` along the good levels and dividing by the limit denominator — are the remaining
assembly, and both of their inputs are proved (links 154, 186, 190 and links 147, 150 respectively).

**Session state.** Fifty-eight modules were written for this card across links 146–193, all
registered in the umbrella, all with oleans emitted at write time, none containing a placeholder, and
every quoted endpoint depending only on `[propext, Classical.choice, Quot.sound]`. The card's target —
`ClassicalNevanlinnaExtremalFamily` for the indeterminate Hamburger moment problem, with the
N-extremal weights identified as the Christoffel limits — is constructed (link 180) and its classical
consequences are unconditional (links 181, 183, 184).

### Link 194 — the Nevanlinna identity for the quadrature measure, off the real axis

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/QuasiMeasureCauchy.lean`
- **`quasiMeasure_cauchy_identity`** —
  `P(z)·∫(x − z)⁻¹ d(quasiMeasure s n t) = −s₀·(R_{n+1}(z) + t·Rₙ(z))` for complex `z` off the nodes,
  combining links 192 and 193.
- `quasiNodes_ne_of_im_ne_zero` — the nodes are real, so they avoid every non-real point.
- **`quasiMeasure_cauchy_identity_of_im_ne_zero`** — hence the identity holds throughout both
  half-planes, with no exceptional set.

Axiom-clean, zero placeholders, registered, first-try compile.

**The finite-level Nevanlinna parametrization is complete for the quadrature measures.** At every
non-real `z`, the Cauchy transform of the level-`n` measure satisfies the classical relation with the
level-`n` first- and second-kind polynomials. Via link 159's closed forms — writing
`Bₙτ − Dₙ = (h₀/hₙ)·αₙ·P` and `Aₙτ − Cₙ = (h₀/hₙ)·αₙ·(R_{n+1} + tRₙ)` with `t = βₙ/αₙ` — this is
`(Bₙ(z)τ − Dₙ(z))·mₙ(z) = −s₀·(Aₙ(z)τ − Cₙ(z))`, equation `(1)` of the sibling card at finite level.

**Remaining for the limit**, unchanged and both inputs proved: pass `n → ∞` along the good levels
(weak convergence, links 154 and 186, against the bounded continuous Cauchy kernel of link 186; entry
convergence, link 190), then divide by `B(z)τ − D(z)`, non-zero at non-real `z` because the fiber is a
discrete subset of `ℝ` (links 147, 150). Translating the closed forms of link 159 to complex arguments
— they are currently stated for real `x` — is the one piece of plumbing that step needs, and it is the
same `ofReal`-bridge pattern as links 149 and 189.

### Link 195 — the closed forms transfer to complex arguments

**[PROVED HERE]** `formal/GaloisForLFunctions/HTGeometry/NevEntryPolynomial.lean`

The bridge flagged at link 194, done for `D` as the template:
- `nevDpoly`, `nevDpoly_eval` — the truncated `D` entry as a polynomial, evaluating to `nevDreal`.
- **`nevDpoly_eq`** — link 152's closed form as an identity of *polynomials*, by `Polynomial.funext`:
  the real closed form holds at every real point with no exceptions, and `ℝ` is infinite.
- `nevDtruncC_eq_aeval` — the complex truncation is `aeval` of that polynomial.
- **`nevDtruncC_closed`** — hence
  `Dₙ(z) = (h₀/hₙ)·(Qₙ(0)·Q_{n+1}(z) − Q_{n+1}(0)·Qₙ(z))` at every **complex** `z`.

Axiom-clean, zero placeholders, registered.

The other three entries follow the identical three steps against their own closed forms — `B` from
`nevBreal_closed` (link 152), `A` and `C` from the `secondKindChristoffelDarboux` and
`mixedChristoffelDarboux` forms used in link 159. Nothing in the pattern is entry-specific: define the
polynomial, transfer the real closed form by `Polynomial.funext`, apply `aeval`.

With those, the level-`n` identity of link 194 becomes
`(Bₙ(z)τ − Dₙ(z))·mₙ(z) = −s₀·(Aₙ(z)τ − Cₙ(z))` at every non-real `z` in the entries' own notation,
and the limit is the assembly described at link 194.

## Log — the classical analytic Nevanlinna carrier family is constructed `[PROVED]`

The moment-fibre bottleneck shared by this card and nine others had two halves.  The first is closed.

`formal/GaloisForLFunctions/HTGeometry/NevLeafCauchyMoebius.lean` proves the **Weyl-disc closed
form** unconditionally, for every positive definite normalised moment sequence with bounded kernel
at a point:

```text
(B(z)*tau - D(z)) * integral (x - z)^(-1) d nu_tau  =  -(A(z)*tau - C(z)),
integral (x - z)^(-1) d nu_tau  =  -(A(z)*tau - C(z)) / (B(z)*tau - D(z)).
```

The finite stage `nevTrunc_cauchy_identity` is the quadrature identity multiplied by the common
factor turning the quasi-orthogonal pair into the truncated Nevanlinna entries; the limit uses the
weak convergence of the quadrature levels to the leaf together with the entrywise limits, and the
determinant identity forbids the denominator from vanishing off the real axis.
`NevLeafInfinityCauchyMoebius.lean` does the same at the parameter at infinity, giving
`integral (x - z)^(-1) d nu_infinity = -A(z)/B(z)`.

`formal/GaloisForLFunctions/HTGeometry/AnalyticNevanlinnaCarrierConstruction.lean` therefore builds

```text
analyticNevCarrierFamily h h0b h0 : ClassicalAnalyticNevanlinnaCarrierFamily s
```

in the carrier convention `(a,b,c,d) = (-A, C, B, -D)`, and
`exists_classicalAnalyticNevanlinnaCarrierFamily`.  All endpoints have axioms `propext`,
`Classical.choice`, `Quot.sound`, and the modules are wired into the `HTGeometry` umbrella.

## Log — `MaximalTranslationInputs` is presently uninhabitable `[DISPROVED FIELD]`

`formal/GaloisForLFunctions/HTGeometry/NevanlinnaWeylDiscPole.lean` proves

```text
nevInf_quotient_im_neg : 0 < z.im -> (D(z)/B(z)).im < 0
```

so `MaximalTranslationInputs.upperMap : forall z, 0 < z.im -> 0 < (F.quotient z).im` is **false**
for the constructed family: the pole of the Weyl-disc Möbius map lies strictly below the real axis,
because the map carries the closed upper half-plane into the Weyl disc and the pole to infinity.
The proof writes the imaginary part of the Möbius image as `Q(t)/|B t - D|^2` with `Q` a real
quadratic, notes `Q` vanishes at the pole and is positive on the real axis, and identifies the
coefficient of `Im t` as `Re(A conj D - C conj B)`, which equals `1` on the real axis, is
continuous, and cannot vanish on the connected upper half-plane.

The transversality chain therefore has to be restated with the jet poles in the **lower** half-plane
(or with the abstract lemmas instantiated at the conjugated poles and the conclusion conjugated
back).  Until then the residual maximal-translation phase theorem is vacuous.

## Log — M. Riesz's theorem is now a single named hypothesis `[REDUCTION PROVED]`

`formal/GaloisForLFunctions/HTGeometry/NevanlinnaEntryMinimalType.lean` adds `norm_nevBinf_le` and
`norm_nevCinf_le` to the corpus's existing `norm_nevAinf_le` / `norm_nevDinf_le`, defines

```text
KernelMinimalExponentialType s :=
  forall A > 0, exists C >= 1, forall z n,
    kernelRoot s (monicOrthoC s . z) n <= C * exp (A * |z|)  and the same for secondKindC
```

and proves `hasMinimalExponentialType_nevAinf`, `...nevBinf`, `...nevCinf`, `...nevDinf` from it.
So the `minimalExponentialType` field reduces to that one property.  The recurrence route to it is
closed: the comparison identity is a Volterra equation with Hilbert-Schmidt kernel, whose iterate
bound `|V^m| <= |V|_HS^m / sqrt(m!)` generates `exp(c|z|^2)`, order two rather than order one, and a
small-tail split only improves the constant.  The route that remains is entire-function theoretic
(real zeros with summable reciprocals, then a genus-zero Hadamard product), and Hadamard
factorization is absent from mathlib.

## Log — the Nevanlinna family is constructed; the residual half is unconditional `[PROVED]`

The card's last Lean gate ("Until the Nevanlinna family is constructed in Lean, the residual-HT half
of the card is not unconditional") is discharged.  `HTGeometry.nevExtremalFamily` and
`HTGeometry.exists_classicalAnalyticNevanlinnaCarrierFamily` construct the family from
`PositiveMomentForm s`, `BoundedKernel s 0`, `s 0 = 1`, and
`HTGeometry.analyticNevCarrierFamilyMaximalTranslationInputs` supplies exactly the five analytic
hypotheses of the relation-free capstones.

New module `HTGeometry/AnalyticNevRelationFreeUnconditional.lean` (wired, axiom-clean):

- `analyticNevCarrier_positiveActualCarrier_hypertranscendental_dense_residual`;
- `analyticNevCarrier_positiveSingularContinuousCarrier_hypertranscendental_dense_residual`
  (label null-preimage discharged by real analyticity of the lower row).

Together with `exists_closedEmbeddedHilbertCube_in_exactCayleyFrameFiber_of_infiniteSupport`
(positive aperture at the exact finite jet level) and `measure_eq_of_completeCauchyJet_eq`
(complete-germ closure), the finite/infinite threshold is fully formalized.  Promoted to
`3-formalized/nad`; the remaining gates are external literature audits.
