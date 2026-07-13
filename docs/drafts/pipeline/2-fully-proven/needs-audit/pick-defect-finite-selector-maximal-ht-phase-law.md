# Pick defect classifies finite analytic selectors: uniqueness or residual maximal HT

- **ID:** `pick-defect-finite-selector-maximal-ht-phase-law`
- **Stage:** 2-fully-proven on paper / needs audit
- **Type:** THEOREM / EXACT FINITE-SELECTOR PHASE LAW
- **Lane:** general hypertranscendence; indeterminate moment fibers; Pick interpolation
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Parents:** `indeterminate-moment-fiber-maximal-translation-ht.md`,
  `finite-jet-aperture-complete-germ-closure-law.md`
- **Statement:** Fix any finite packet of nonreal Cauchy values and derivatives in an
  indeterminate Hamburger moment fiber, and form the reduced confluent Pick matrix of the induced
  Nevanlinna-parameter data. If that matrix is singular, the packet selects one finite-order
  canonical solution. If it is positive definite, the exact packet level is an infinite
  constraint fiber with a dense residual subset whose Cauchy transforms have differentially
  algebraically independent full complex translation families. Thus every finite analytic
  selector lies in exactly one of two phases: classical Pick singularity or maximal-HT aperture.

## Goal

The earlier finite-jet theorem proves aperture in positive barycentric charts. It does not classify
all finite analytic constraints: a boundary Pick datum can be singular and determine a unique
solution from even one value. The present theorem closes that gap.

The positive law is exact:

> **Finite analytic selection occurs precisely on the singular Pick locus. Every positive Pick
> defect carries residual maximal full-translation hypertranscendence.**

This is a theorem about constrained Herglotz/HT functions in general. RH enters only after the law
is established.

## Moment-fiber and interpolation setup

Fix an indeterminate normalized Hamburger moment sequence `s` and its Nevanlinna matrix

```text
N(z)=[[A(z),B(z)],[C(z),D(z)]],
A(z)D(z)-B(z)C(z)=1.                                      (1)
```

Every representing measure `mu in M(s)` has Cauchy transform

```text
m_mu(z)=[A(z)Phi_mu(z)+B(z)]/[C(z)Phi_mu(z)+D(z)],         (2)
```

where `Phi_mu` is a real-symmetric Pick function, with the usual projective point at infinity.
Conversely every such Pick parameter gives one measure in `M(s)`.

Fix distinct nodes `z_1,...,z_J` in the upper half-plane, depths `d_j>=1`, and a realized finite
packet

```text
D={partial_z^r m_mu(z_j):1<=j<=J, 0<=r<d_j}.              (3)
```

Let

```text
L_D={nu in M(s):partial_z^r m_nu(z_j)
                    =partial_z^r m_mu(z_j) for every (j,r)}.  (4)
```

The level `(4)` is nonempty and weakly closed. Uniform integrability is irrelevant for these
constraints because every Cauchy derivative kernel is bounded and belongs to `C_0(R)`. Hence
`L_D` is a compact metrizable Baire space.

## Passing from Cauchy jets to Pick jets `[PROVED HERE]`

Solving `(2)` for the parameter gives

```text
Phi_mu(z)=[B(z)-m_mu(z)D(z)]/[m_mu(z)C(z)-A(z)].           (5)
```

For an actual finite Pick parameter, the denominator in `(5)` is nonzero at every nonreal point;
the determinant identity gives it explicitly as a nonzero reciprocal of the denominator in `(2)`.
The projective case is handled in the opposite affine chart.

At each node, `(5)` is an analytic fractional-linear coordinate change with nonzero first
derivative. Its map on finite jets is triangular, and the coefficient of the highest derivative is
nonzero. Therefore `(3)` is equivalent to one finite confluent jet packet for `Phi_mu`.

Apply a fixed Cayley transform from the Pick half-plane to the Schur disk. The packet becomes a
finite interior Nevanlinna--Pick--Caratheodory--Fejer problem for a Schur function `S_mu`.

Delete duplicated or linearly redundant jet functionals. Let

```text
P_D                                                        (6)
```

be the resulting reduced confluent Pick matrix. Since `(3)` is realized, `P_D` is positive
semidefinite.

## Classical singular/free dichotomy `[SEARCH]`

Classical confluent Nevanlinna--Pick theory gives exactly two cases.

### Singular phase

If `P_D` is singular, the interpolation problem has one Schur-class solution. That solution is a
rational inner function of degree equal to the rank of the reduced Pick matrix. Undoing the Cayley
transform gives one rational Pick parameter `Phi_D`; undoing `(2)` gives one measure `mu_D`.
Thus

```text
L_D={mu_D}.                                                 (7)
```

In moment terminology `mu_D` is a finite-order canonical solution and is an extreme point of
`M(s)`.

### Positive-defect phase

If `P_D` is positive definite, the interpolation problem is nondegenerate. There is a rational
`J`-inner transfer matrix

```text
Theta_D(z)=[[a(z),b(z)],[c(z),d(z)]]                       (8)
```

such that all solutions are

```text
S(z)=T_(Theta_D)[omega](z)
    =[a(z)omega(z)+b(z)]/[c(z)omega(z)+d(z)],              (9)
```

with `omega` an arbitrary Schur function, subject only to the standard removable exceptional
parameters. Conversely every admissible `omega` gives a solution. The entries in `(8)` are
rational and its determinant does not vanish identically.

The singular/free dichotomy and `(8)`--`(9)` are classical inputs. No novelty is claimed for them.

## Free-parameter Cauchy-jet controllability `[PROVED HERE]`

Assume `P_D>0`. Choose a strictly interior real-symmetric Schur parameter `omega_0`. Obtain a
positive Herglotz chart by Cayley-transforming the parent positive atomic Cauchy gauges. For a
small real Banach parameter `v`, write this chart as

```text
v |-> omega_v.                                             (10)
```

At any separated finite packet of nonreal evaluation nodes, the map from `v` to all finite jets of
`omega_v` is onto as a real-linear differential. This is the parent rational-pole controllability
theorem followed by a pointwise Cayley map with nonzero derivative.

Compose successively:

```text
omega_v
 -> S_v=T_(Theta_D)[omega_v]
 -> Phi_v=Cayley^(-1)(S_v)
 -> m_v=[A Phi_v+B]/[C Phi_v+D].                           (11)
```

At a regular node, each arrow in `(11)` is fractional-linear in the current function value with
nonzero determinant. On jets of depth `r`, its derivative is triangular: the coefficient of the
incoming order-`r` jet in the outgoing order-`r` jet is the nonzero first derivative of the
fractional-linear map, while all remaining terms use lower jets. Hence the differential of `(11)`
is onto every separated finite Cauchy-jet packet.

All functions produced by `(11)` remain in the exact level `L_D`, because `(9)` is the complete
solution parametrization of the frozen interpolation data.

## Density near every point of the level `[PROVED HERE]`

Let `mu_0 in L_D`, represented by a free Schur parameter `omega_*`, and let `W` be a weak
neighborhood of `mu_0`. The Schur class is convex. For sufficiently small `epsilon>0`,

```text
omega_(epsilon,v)
 =(1-epsilon)omega_*+epsilon omega_v                       (12)
```

is a Schur parameter whose image under `(9)`--`(11)` lies in `W` for all sufficiently small `v`.
Real symmetry is preserved. If `omega_*` is an exceptional projective parameter, approximate it
first by an ordinary interior parameter; the resulting moment transforms converge locally
uniformly and hence weakly.

The differential in the `v` direction is `epsilon` times the onto differential from the previous
section, followed by the same invertible triangular jet maps. Thus every weak neighborhood in
`L_D` contains a finite-dimensional local submersion onto every prescribed separated Cauchy-jet
packet.

## Residual maximal full-translation HT `[PROVED HERE]`

If `P_D>0`, there is a dense residual subset

```text
G_D subset L_D                                             (13)
```

such that for every `nu in G_D`, every `m>=1`, and every tuple of distinct complex shifts
`h_1,...,h_m`,

```text
m_nu(z+h_1),...,m_nu(z+h_m)                               (14)
```

is differentially algebraically independent over `C(z)`.

### Proof

Fix a differential-relation support, coefficient-degree bound, and a sufficiently small compact
patch of distinct shift configurations. Choose enough high evaluation rows that all translated
nodes are regular and their free-parameter pole coordinates are separated. The controllability
of `(11)` supplies a finite-dimensional direction space whose differential spans the complete row
jet packet.

The universal direction--shift map is therefore a real submersion. The rank-defect locus for the
evaluation matrix has complex codimension greater than the complex dimension of the shift patch,
by the parent projective-incidence estimate. Whitney-stratified parametric transversality produces
arbitrarily small directions for which every rank defect is absent throughout the patch. The
density statement from `(12)` makes the escape set dense in all of `L_D`; compact-patch normal
convergence makes it open.

Intersect over the countable relation patterns and a countable compact cover of every finite
shift-configuration space. Since `L_D` is Baire, the intersection is `(13)`. A relation initially
given as an upper-end germ extends to the high evaluation rows by the meromorphic identity theorem.
Clearing rational coefficients then proves `(14)`. `QED`

## Complete-germ closure `[PROVED HERE]`

For comparison, if every derivative at one nonreal point is fixed, equality of Taylor germs gives
equality of the two Cauchy transforms on an open set. Analytic continuation and Stieltjes-transform
uniqueness give equality of the measures. Thus every complete nonreal Cauchy germ is a singleton
selector, independently of the finite Pick defect.

## Pick-defect finite-selector phase law

> **For every realized finite analytic constraint in an indeterminate Hamburger moment fiber, the
> reduced confluent Pick matrix is the exact phase coordinate. Singular Pick data select one
> finite-order canonical measure. Positive Pick defect leaves an infinite solution fiber on which
> maximal full-complex translation hypertranscendence is dense residual. Complete-germ data close
> either phase to one measure.**

This corrects the overbroad slogan “finite jets never select.” They can select, but only through a
classical singular Pick boundary. Everywhere else, finite analytic data force a maximal-HT
aperture.

## General HT consequence

The theorem gives an operational test for finite constraints on Herglotz/HT carriers:

1. convert the frozen Cauchy jets to Pick/Schur jets by `(5)`;
2. compute the reduced confluent Pick matrix;
3. if it is singular, the carrier is the unique rational-inner parameter solution;
4. if it is positive definite, maximal full-translation HT remains residual in the exact level.

Thus finite analytic rigidity is a rank defect, not a gradual accumulation of local data.

## Positive RH-carrier consequence

A finite-value or finite-derivative RH route based on an indeterminate moment carrier has only one
possible selection mechanism: it must prove that its induced Pick matrix is singular and then
identify the resulting unique finite-order canonical solution with the arithmetic source. If its
Pick matrix has positive defect, the exact source constraints still contain a residual maximal-HT
phase and do not select a carrier.

The current Xi/Hedenmalm construction does not rely on such a finite singularity. It uses the
complete pointed analytic germ to reconstruct the source trace, `XiC`, and local Bezoutian. It lies
on the complete-germ side of the law. Its remaining obligation is the global Hermitian orientation
of the reconstructed kernel, not another finite interpolation condition.

## Xi finite-Pick matrices are strictly interior under orientation `[PROVED HERE; CONDITIONAL]`

Let

```text
T(z)=continuedPrimeArchSourceRelativeTrace(z).             (15)
```

The formal orientation gate proves that `T` is anti-Pick on the centered upper half-strip exactly
when RH holds. Half-strip orientation alone does not make its disk transform inner, because it does
not supply real boundary values on both strip edges. Assume orientation, deduce RH, and instead use
the globally meromorphic centered logarithmic derivative `T_Xi=XiC'/XiC`, which agrees with `T` on
their common regular domain.

Under RH, the paired even Hadamard product gives

```text
T_Xi(z)=sum_(gamma>0) m_gamma[1/(z-gamma)+1/(z+gamma)]
```

locally normally in the upper half-plane. Hence `-T_Xi` is Herglotz there and has real boundary
values away from the real Xi divisor. Normalize it at an interior point and Cayley-transform the
domain and target. The resulting Schur function is inner, and its Clark measure is pure point on
the Cayley images of the Xi zeros. The completed Xi divisor is unconditionally infinite, so this
inner function is nonrational.

Take any finite reduced packet of its interior values and derivatives. Its confluent Pick matrix is
positive semidefinite because the oriented Xi Schur function realizes the data. It cannot be
singular: singularity would make the Schur interpolant unique and rational inner, forcing the
actual Xi Schur function to equal that rational solution. Hence

```text
orientation of the Xi source
  implies every finite reduced Xi Pick matrix is positive definite.  (16)
```

Thus the actual oriented Xi carrier lies strictly in the positive-defect phase at every finite
order. Finite Pick singularity is not a hidden route to its orientation. Any source-faithful proof
must control a cofinal family of finite Pick matrices, the complete germ, or an equivalent global
kernel sign.

Equation `(16)` is not an RH proof: its premise is the orientation condition already equivalent to
RH. Its value is route classification. It shows what the desired oriented carrier must look like
at every finite resolution and prevents a singular finite interpolant from being mistaken for the
Xi source.

## Primary interpolation sources checked

- H. Woracek, *Nevanlinna--Pick Interpolation: The Degenerated Case* proves that a nonnegative
  singular Pick matrix gives a unique rational Nevanlinna-class solution and explicitly notes the
  derivative-prescription extensions:
  `https://haraldworacek.github.io/homepage/Downloads/JournalPapers/1997/6.pdf`.
- V. Bolotnikov, *On a multi-point interpolation problem for generalized Schur functions*,
  `arXiv:0812.4564`, treats nondegenerate multipoint Nevanlinna--Pick--Caratheodory--Fejer data and
  the linear-fractional free-parameter description.
- J. A. Ball and Q. Fang, *Nevanlinna--Pick Interpolation via Graph Spaces and Krein-space
  Geometry: A Survey* records the rational resolvent-matrix/J-inner parametrization of solution
  families.

These sources support the classical interpolation half. They do not contain the residual
full-translation HT conclusion found here.

## Parent-theory and novelty attack

1. `[SEARCH]` Positivity of the confluent Pick matrix, uniqueness in the singular case, rational
   inner degree, and rational linear-fractional parametrization in the positive-defect case are
   classical Nevanlinna--Pick--Caratheodory--Fejer theory.
2. `[SEARCH]` Rational Pick parameters correspond to finite-order canonical moment solutions, and
   these are extreme.
3. `[BRIDGE]` Finite Cauchy-jet controllability and the full shift-configuration rank-defect
   transversality theorem come from the parent HT result.
4. `[PROVED HERE]` The jet coordinate changes from free Schur parameter through the interpolation
   transfer matrix and the moment Nevanlinna matrix are triangular submersions.
5. `[PROVED HERE]` Every positive-defect exact interpolation level, not merely one auxiliary chart,
   has residual maximal full-complex translation HT.
6. `[CANDIDATE RESIDUE]` Preliminary exact searches did not find the singular-Pick versus residual
   maximal-translation-HT dichotomy for finite analytic levels inside an indeterminate complete
   moment fiber.
7. `[FORMALIZED INPUT + COROLLARY]` The repository proves the Xi divisor is infinite and that
   source anti-Pick orientation is equivalent to RH. Classical singular Pick uniqueness then gives
   the conditional strict-positive-defect law `(16)` for every finite Xi packet.
8. The theorem remains `[NOVELTY UNVERIFIED]` until interpolation, moment-problem, generic-function,
   and differential-algebra specialists have audited proof and priority.

No numerical experiment and no RH assumption enter the theorem.

## Honest significance score

This materially strengthens the internal **90/100 candidate** case because it classifies every
finite analytic selector rather than only positive barycentric charts. The honest range remains
**72--94** pending specialist audit. A higher score is not justified without a source-derived
orientation mechanism, primary-source priority confirmation, and unconditional Lean formalization.

## Lean status

No Stage 3 claim is made. Formalization requires the Nevanlinna parametrization of the moment
fiber, confluent Pick matrices, the singular/free interpolation theorem, rational transfer
matrices, Schur-class compactness, triangular jet maps, parametric transversality, and the parent
full-configuration HT theorem.

Formalization audit (needs-audit pass): no bounded self-contained kernel closes a gate. Beyond the
parent moment-fiber stack, this card additionally needs the classical confluent Nevanlinna--Pick
singular/free dichotomy and its `J`-inner transfer-matrix parametrization `(8)`--`(9)` — itself a
major theory absent from mathlib. The triangular jet-coordinate submersions `(5)`, `(11)` are
elementary but inseparable from that absent interpolation surface. The one classical layer that
abstracts cleanly and is now formalized axiom-clean in-tree is the **Herglotz/Pick property of the
Cauchy transform** `(6)` — `formal/GaloisForLFunctions/StieltjesTransformPick.lean`:
`stieltjesTransform_im_nonneg` and `stieltjesTransform_im_pos` prove `Im S_μ(z) ≥ 0` (resp. `> 0` for
`μ ≠ 0`) throughout the open upper half-plane, i.e. every representing measure's Cauchy transform
`Φ_μ` is a Pick function, via the pointwise kernel positivity `Im (x−z)⁻¹ = Im z / |x−z|²`
(`cauchyKernel_im`, `cauchyKernel_im_pos`) and commuting `Im` through the Bochner integral
(`im_integral`). The confluent interpolation surface itself remains absent.

## Gates

- [x] Cauchy-jet / Pick-jet coordinate equivalence proved
- [x] redundant interpolation constraints explicitly reduced
- [x] singular Pick phase classified by classical uniqueness
- [x] positive-defect phase parametrized by a free Schur function
- [x] free-parameter to Cauchy-jet submersion proved
- [x] density near every point of the exact finite-jet level proved
- [x] residual maximal full-translation HT in the whole positive-defect level proved
- [x] complete-germ closure proved
- [x] Xi/Hedenmalm consequence scoped
- [x] conditional strict-positive-defect law for every finite oriented Xi packet proved
- [x] preliminary local and web collision search
- [ ] independent specialist proof audit
- [ ] primary-source audit for confluent singular/free theorem in exactly this normalization
- [ ] unconditional Lean formalization of the entire theorem

## Log

- 2026-07-12 -- Replaced the chart-specific finite-jet slogan by the exact reduced-Pick-matrix
  dichotomy. Proved that the positive-defect free Schur parameter transports the parent jet
  submersion through the interpolation and moment fractional-linear maps, yielding residual
  maximal full-translation HT throughout the exact finite-jet level.
