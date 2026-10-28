# Signed Arithmetic Hodge Theory

**Central question.** How can arithmetic incidence, archimedean energy and the two polar
coordinates jointly control the index of the actual Weil form under source exhaustion?

Signed arithmetic Hodge theory with source-compatible renormalization studies this question on
the original arithmetic source. Its purpose is to turn positive arithmetic sections into
quantitative control of their mixed interactions and complement. A positive section alone does
not orient the complete form. A renormalized prime spectrum alone does not recover the
archimedean term or the poles.

Namespace: `GaloisForLFunctions.SignedArithmeticHodgeTheory`.
Umbrella: `SignedArithmeticHodgeTheory.lean`.

## Motivation

Three constructions supply concrete starting points.

* Balanced logarithmic Haar sections have a full rough-Weil lower bound above a fixed lower
  index, uniformly in the upper horizon. They leave coarse directions and interactions between
  scales.
* Narrow arithmetic sections admit a bounded Weil-orthogonal projection in the complete source
  graph. Their complement contains an infinite null radical. Its nonnegativity is open; a strict
  lower bound on the whole complement is false.
* Ramanujan profiles give actual prime-matrix quasimodes with distinct renormalized energies.
  Fixed-conductor convergence leaves growing-conductor errors, a modal complement and the
  comparison with Gamma and both poles.

There is also a canonical nonnegative critical source energy. Its finiteness detects finite
off-line support; its sharp smallness threshold detects RH. Known index costs bound it from
below. An arithmetic upper bound is a separate missing result.

These are connected problems, not interchangeable criteria. This programme must produce new
estimates on their shared source and explicit interfaces between their different forms.

## Objects and language

Every comparison specifies five pieces: **source, form, domain, exhaustion and error currency**.

| Object | Mathematical content |
|---|---|
| Arithmetic source | Real compactly supported logarithmic tests, their complete source-graph closure, and explicitly embedded finite cell or class spaces |
| Signed form | The complete symmetric Weil pairing, with its prime, Gamma, mass and two-pole terms retained |
| Paid section | A source-defined subspace on which a proved coercive estimate supplies a bounded Weil projection |
| Residual | The original source minus that projection, with the induced signed form |
| Radical | Vectors pairing to zero with every source vector; these may have nonzero graph norm |
| Mixed charge | The bilinear interaction between chosen source blocks, measured in a stated norm |
| Reserve | A proved positive term available once in a joint estimate |
| Renormalization | An explicit counterterm subtraction on an identified domain, accompanied by convergence and error estimates |
| Modal source | Actual Ramanujan profiles in the prime matrix, with Gram, residual, pole and complementary errors |
| Critical energy | The canonical extended-real limit of quadratic-scale source work, including off-line/critical exterior pairs |

A morphism is a specified linear source map together with proved formulas for its mixed-form and
polar defects. Form preservation must be proved. No interface field may assume the sign, the
missing complement bound or an unproved arithmetic estimate.

“Hodge” refers to signed orthogonal decomposition, index and the arithmetic source of a sign.
It does not assert the existence of a new cohomology theory or a positive polarization.
“Source-compatible” means that the actual test functions, their poles and their mixed pairings
survive every comparison. “Renormalized” does not mean that an unpaid divergent term is discarded.

## Mechanisms and pillar theorems

### Exact residual calculus

For a proved positive section with Weil projection \(P\), write \(R=1-P\). The basic identity is

\[
 W(x,y)=W(Px,Py)+W(Rx,Ry).
\]

The programme supplies a quantitative trial-correction theorem on the actual unbounded carrier
\(K\). Let \(T_W\) be the original graph Weil operator and
\(J=\Pi_K T_W\), where \(\Pi_K\) is graph-orthogonal projection. For every source \(x\) and
every trial correction \(u\in K\),

\[
\begin{aligned}
 W(x-u)&=W(Rx)+W(Px-u),\\
 \|Px-u\|&\le2\|J(x-u)\|,\\
 W(x-u)-2\|J(x-u)\|^2
 &\le W(Rx)
 \le W(x-u)-\tfrac12\|Px-u\|^2.
\end{aligned}
\]

Equality \(W(x-u)=W(Rx)\) holds exactly when \(u=Px\). For two independent sources and trials,

\[
 |W(x-u,y-v)-W(Rx,Ry)|
 \le2\|J(x-u)\|\,\|J(y-v)\|.
\]

[TheArithmeticSchurComplementHasCertifiedErrorBounds](TheArithmeticSchurComplementHasCertifiedErrorBounds.lean)
proves these statements without a sign premise on the residual. The constants are independent
of aperture and profile count. Restricting \(T_W\) to the carrier charges only the interaction
that the correction must remove. The error estimate is quadratic in stationarity, while the
graph error is linear.

These are certified comparison tools. They do not bound stationarity on a new exhaustive
arithmetic family or prove nonnegativity of the exact complement. Coherent multiblock payment
and preservation of the radical are further parts of the residual calculus.

### Signed block payment

For a decomposition \(x=\sum_j x_j+r\), diagonal lower bounds are useful only with a simultaneous
bound for all mixed terms. The target is a source-defined matrix or operator bound whose norm
is smaller than the available diagonal reserve, with explicit treatment of the coarse residual.
Absolute-value estimates are acceptable only when their total cost is affordable.

The first substantive target is a coherent family of Haar and coarse blocks with one Gamma
allocation, both poles and an error uniform in the family size. A complete all-coefficient
nonnegative result would establish the complete Weil sign and therefore RH.

### Renormalized adjunction

For conductor \(m\), the actual mode is

\[
 v_m(n)=\frac{c_m(n)}{\sqrt{\phi(m)n}},\qquad
 E_m=\gamma+\log m+\operatorname{tameDifferent}(m).
\]

The prime matrix has trial energy \(\log N-E_m\). A source-compatible comparison must control
the Gram error, matrix residual, continuous Gamma and polar images, and the orthogonal
complement on the same growing family. Choosing an arbitrarily slow diagonal sequence from
fixed-mode limits does not establish source completeness.

### Critical-work control

The canonical energy satisfies

\[
 R^2\bigl(\mathcal W(2R)-\mathcal W(R)\bigr)
 \longrightarrow\mathcal E_{\mathrm{crit}}\in[0,\infty].
\]

The first target is an upper bound from prime or theta arithmetic retaining the exterior rows.
Finiteness would give finite off-line support. The endpoint
\(\mathcal E_{\mathrm{crit}}\le1294047/2000\) is equivalent to RH.
An index lower bound, a nonnegative pair expansion or monotone convergence supplies no such
upper bound by itself.

## Established foundations in the corpus

These are imported mathematical foundations, not new contributions of this programme.

| Foundation | Source |
|---|---|
| Complete mixed-cell transfer and source-graph projection | [ArithmeticIndexDescent](../ArithmeticIndexDescent/TheUnboundedCellCarrierHasAWeilProjection.lean) |
| High Haar full-form floor | [HaarCellEffectivity](../ArithmeticCastelnuovoSeveri/HaarCellEffectivity.lean) |
| Mean-zero Gamma payment | [GammaMeanZeroCoercivity](../ArithmeticCastelnuovoSeveri/GammaMeanZeroCoercivity.lean) |
| Actual Ramanujan prime quasimodes | [TheRamanujanPoleProfilesArePrimeQuasimodes](../RenormalizedArithmeticPotentialTheory/TheRamanujanPoleProfilesArePrimeQuasimodes.lean) |
| Prime gap on the harmonic pole hyperplane | [ThePrimeFormHasASpectralGapBelowItsPole](../RenormalizedArithmeticPotentialTheory/ThePrimeFormHasASpectralGapBelowItsPole.lean) |
| Canonical critical source energy | [TheCriticalSourceRateHasACanonicalEnergy](../ArithmeticIndexDescent/TheCriticalSourceRateHasACanonicalEnergy.lean) |
| Source synthesis beyond narrow spacing | [TheSecondOrderSynthesis](../SpacingScaleHarmonicAnalysis/TheSecondOrderSynthesis.lean) |

The trial-correction theorem is a formalized contribution of this programme. Complete signed
block payment, growing-mode transfer and arithmetic upper control of critical work remain
research targets.

## Questions and open topics

1. Which signed overlapping block families admit a uniformly paid mixed interaction without a
   diagonal Metzler gauge? What coarse complement do those families leave?
2. What is the exact variational meaning of removing an arithmetic positive section? How do
   nested section removals interact, and how is their residual radical represented?
3. Which explicit growing Ramanujan families control a useful source domain? What quantitative
   complement estimate survives the Gamma and continuous two-pole comparison?
4. Which counterterms yield convergence in a topology strong enough to preserve mixed Weil
   pairings? How do conductor, class variation and horizon constrain one another?
5. Can arithmetic gauge selection on a discrete pole hyperplane survive a faithful transfer to
   the full continuous form?
6. Which prime or theta law bounds critical energy above? Can it first exclude infinitely many
   off-line zeros without presupposing their absence?
7. Can selective localization see every possible exceptional ordinate with affordable conductor
   and inverse costs?

These questions include intermediate theorems as well as RH-strength endpoints. A proof of an
intermediate statement must state precisely which endpoint remains open.

## Traps and boundary conditions

* A null vector is not a negative direction. A graph-norm floor cannot hold on a residual that
  contains a nontrivial Weil radical.
* Ordinary mean zero, the discrete harmonic pole constraint and two continuous exponential
  moments are different conditions.
* Shared Gamma reserve cannot be spent separately on every block. Summed estimates must
  account for each source term exactly once.
* Fixed support, fixed conductor and fixed profile variation do not supply uniform growing
  families. Domain escape must be measured.
* Prime-matrix positivity and full Weil positivity concern different forms.
* Nonnegative entries in the critical pair energy do not establish positive semidefiniteness
  of its kernel.
* A sparse positive carrier can be proper. Larger horizons alone do not prove density.
* A diagonal gauge is unavailable in obstructed overlap regimes. Signed block geometry must
  address that obstruction rather than assume it away.
* Generic intersection identities and synthetic positive models do not select the actual
  arithmetic source. Equivalences and definitions cannot provide the missing sign.

## Relation to other programmes

Arithmetic Castelnuovo–Severi supplies the scaling surface and positive arithmetic sections.
Arithmetic Orientation Geometry studies signs along scaling correspondences.
Arithmetic Index Descent supplies complete source domains, projections, index capture and
critical-work costs. Renormalized Arithmetic Potential Theory supplies arithmetic finite parts,
adjunction modes and pole-gap selectivity. Spacing Scale Harmonic Analysis supplies source
synthesis and quantitative overlap estimates. Arithmetic Lorentzian Geometry identifies
constraints on positive gauge and stability mechanisms.

This programme's contribution should be the paid comparison between those objects: exact
residual optimization, coherent signed block estimates, uniform renormalized transfer and
arithmetic upper control. Existing modules remain the owners of their foundational results.

## Success and contribution criteria

A contribution must identify its actual source and prove a new estimate, sharp classification
or structural theorem needed by an estimate. It must preserve the complete relevant form,
state every growing parameter, account for mixed terms and poles, and discharge its arithmetic
inputs. Abstract helper lemmas are useful only when instantiated on the actual arithmetic
objects.

A substantive success answers part of the signed-complement, growing-mode or critical-upper-bound
questions. Full success requires the tools and source-complete forcing mechanisms demanded by
those questions; names, reformulations and conditional wrappers do not meet that standard.

Every claimed proof must be formalized in Lean without added axioms, placeholders, hidden
analytic premises or increased elaboration limits. The final statement and its dependencies,
not its title or intended application, determine what has been proved.
