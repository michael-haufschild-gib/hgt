# Arithmetic conormal socle-gauge conservation law

- **ID:** `riemann-arithmetic-conormal-socle-gauge-law`
- **Short name:** arithmetic conormal socle-gauge conservation (`ACSG`)
- **Stage:** `1-in-progress`
- **Type:** UNIVERSAL SUPPORT THEOREM + FROZEN ARITHMETIC SOURCE LAW
- **Status:** `[UNIVERSAL CONSUMER PAPER-PROVED] [COMPLETION-CLASS NO-GO LEAN-PROVED] [SOURCE LAW OPEN] [NOT RH]`
  `[NO DIVISOR-SELECTED METRIC] [NOVELTY UNVERIFIED]`
- **Lean:** none until the source comparison is constructed on paper
- **Parents:**
  - `../4-publication-ready/riemann-boundary-completeness-law/main.tex`;
  - `source-curved-prime-torus-conormal-temperedness.md`;
  - `singular-infinite-source-pointed-common-test-factorization.md`;
  - `../2-fully-proven/prime-sieve-wold-gamma-bv-relative-character.md`;
  - `../../../3-formalized/new_scientific_knowledge/other/primitive-fibre-modular-renormalization-law.md`;
  - `formal/GaloisForLFunctions/RHTower/CompleteResolutionSourceCharacterSelectionLaw.lean`;
  - `formal/GaloisForLFunctions/RHTower/Deninger/DeningerRamifiedTopConormalFiniteStageCocone.lean`.

## Result

The missing assertion is not that every modular character is unitary, and it is not the
pointwise statement that every horizontal divisor defect vanishes.  It is one source-level
conservation law: arithmetic transport must preserve a nondegenerate gauge on exact conormal
character lines.

Let

\[
 G=\mathbb Q_{>0}^{\times}=\bigoplus_{p\ {\rm prime}}\mathbb Z,
 \qquad
 A=C^*(G)=C(\widehat G),
 \tag{1}
\]

and write $u_g\in A$ for the canonical unitary attached to $g\in G$.  Let
\(\mathcal N_\Xi^{\rm src}\) be the algebraic principal-conormal cohomology of the completed
Euler--Gamma/co-Poisson source, with its centered rational-dilation action.  This module is
defined before choosing or enumerating a zero.  The existing continuation and noncensoring
theorems imply that a divisor point \(\rho\) of multiplicity \(m_\rho\) contributes a nonzero
primary jet packet on which, for every $g\in G$,

\[
 \bigl(g-g^{\rho-1/2}\bigr)^{m_\rho}=0.
 \tag{2}
\]

More sharply, the top local class $(s-\rho)^{m_\rho-1}$ is nonzero and satisfies the exact
eigenrelation

\[
 g\,(s-\rho)^{m_\rho-1}
   =g^{\rho-1/2}(s-\rho)^{m_\rho-1}.
 \tag{2a}
\]

Indeed, locally the action is multiplication by
$g^{s-1/2}=g^{\rho-1/2}\exp((s-\rho)\log g)$, and every positive power of
$(s-\rho)$ beyond degree $m_\rho-1$ vanishes.  Thus multiplicity produces a generalized
primary packet but always leaves one exact character line: its socle.  The exponent in
`(2)`--`(2a)` is the centered conormal character, not an assumed spectral normalization.

Write $T_g$ for the centered rational-dilation action on
\(\mathcal N_\Xi^{\rm src}\).  The arithmetic coefficient source supplies the Wold--Toeplitz
extension

\[
 0\longrightarrow \mathfrak J_\Gamma
 \longrightarrow \mathfrak T_\Gamma
 \longrightarrow A\longrightarrow0.
 \tag{3}
\]

Its regular anomaly is the exact polarized Gamma determinant cocycle.  Its singular anomaly is
the exact BV/co-Poisson first-trace conormal with coefficient $1-q^{-1}$.  A plain boundary
$A$-module kills both anomalies, so one candidate construction passes through a source-normal
relative Rees totalization of `(3)`.  The universal law itself does not require that realization.

### Independent arithmetic producer law

The gauge is not allowed to be chosen abstractly.  Its source-native producer is the following
singular positive-weight statement.

> **[FROZEN PRODUCER LAW -- SOURCE-POINTED REES ATOMIC WEIGHT]**
>
> The actual Wold ideal, Gamma determinant, BV first trace, and co-Poisson source point construct
> a relative Rees $*$-algebra \(\mathfrak R_{\rm src}\), a centered $G$-action $\alpha$, a
> divisor-independent equivariant conormal map
> \(j_{\rm src}:\mathcal N_\Xi^{\rm src}\to\mathfrak R_{\rm src}\), and a source-pointed
> positive weight \(\Omega_{\rm src}\) such that
>
> \[
> \Omega_{\rm src}(\alpha_g(a))=\Omega_{\rm src}(a),
> \qquad
> 0<\Omega_{\rm src}\!\left(j_{\rm src}(v)^*j_{\rm src}(v)\right)<\infty
> \tag{ASPW}
> \]
>
> for every nonzero $v$ spanning a one-dimensional $G$-submodule of
> \(\mathcal N_\Xi^{\rm src}\).  The weight may be unbounded on the ambient Rees algebra; only
> these source-conormal squares must lie in its finite domain.

`(ASPW)` is the concrete independent arithmetic law.  It is singular because every bounded
plain-boundary state erases the Gamma and BV anomalies.  It is infinite because finite Rees order
preserves the reflected flat radical.  It is source-pointed because the weight is fixed by the
arithmetic vacuum/augmentation before any divisor fibre is inspected.

Define

\[
 q_{\rm src}(x)=
 \Omega_{\rm src}\!\left(j_{\rm src}(x)^*j_{\rm src}(x)\right)^{1/2}
 \tag{3a}
\]

on the finite-weight conormal domain.  Positivity gives absolute homogeneity, equivariance plus
weight invariance gives gauge invariance, and atomic faithfulness gives character-line detection.
Thus `(ASPW)` implies the universal source law below.

> **[FROZEN SOURCE LAW -- ARITHMETIC CONORMAL SOCLE-GAUGE CONSERVATION]**
>
> The completed arithmetic source constructs, without divisor specialization, a $G$-invariant
> finite-weight domain \(\mathcal D_{\rm src}\subseteq\mathcal N_\Xi^{\rm src}\) containing the
> atomic socle locus and an absolutely homogeneous gauge
>
> \[
> q_{\rm src}:\mathcal D_{\rm src}\longrightarrow\mathbb R_{\ge0}
> \]
>
> such that centered rational dilation is gauge-conservative and the gauge detects the
> atomic character-socle locus:
>
> \[
> \boxed{
> q_{\rm src}(T_gx)=q_{\rm src}(x)
> \quad(g\in G,\ x\in\mathcal D_{\rm src}),
> \qquad
> q_{\rm src}(v)>0
> \quad\bigl(0\ne v\in
> \operatorname {Soc}^{(1)}_{G}(\mathcal N_\Xi^{\rm src})\bigr).}
> \tag{ACSG}
> \]
>
> Here \(\operatorname {Soc}^{(1)}_{G}(N)\) is the atomic socle locus: the union of zero and
> all one-dimensional \(\mathbb C[G]\)-submodules of $N$.  It is not the linear span of those
> submodules.

`(ACSG)` is the requested independent arithmetic source law.  It contains no \(\rho\), no zero
location, no Weil sign, no divisor-indexed norm, and no assertion that arbitrary modular
characters are unitary.  Its inputs must be the integral prime-valuation source, the actual Wold
ideal, the Gamma determinant anomaly, the BV first-trace anomaly, and the distinguished
co-Poisson conormal section.  Divisor points enter only after `(ACSG)`, by taking the support of
the already constructed source module.

The gauge need not satisfy a triangle inequality.  It may have a large zero locus, including
dense or maximally vertical radicals away from individual character lines.  It need not separate
sums of distinct character lines.  The law forbids one loss only: zero gauge on an exact source
character line.  This is the weakest homogeneous conservation statement that can still detect
horizontal displacement.  For RH, invariance under one fixed prime (for example $T_2$) is
already sufficient; all-$G$ invariance is the natural source-functor form.

## Universal theorem: invariant-gauge support law

**Theorem.**  Let $G$ act linearly on a complex vector space $N$.  Let $D\subseteq N$ be
$G$-invariant and closed under complex scaling, and let \(q:D\to\mathbb R_{\ge0}\) satisfy
\(q(cx)=|c|q(x)\).  Assume

\[
 q(gx)=q(x),
 \qquad
 q(v)>0\quad\text{for every nonzero }v\in D\cap\operatorname {Soc}^{(1)}_G(N).
 \tag{4}
\]

If $0\ne v\in D$ spans the character line \(gv=\lambda(g)v\), then

\[
                         |\lambda(g)|=1
 \quad\text{for every }g\in G.
 \tag{5}
\]

**Proof.**  Socle detection gives $q(v)>0$.  Absolute homogeneity and invariance give

\[
 q(v)=q(gv)=q(\lambda(g)v)=|\lambda(g)|q(v).
 \]

Cancel $q(v)$ to obtain `(5)`. \(\square\)

This theorem covers multiple zeros because every primary jet packet has the nonzero exact
eigenline `(2a)`.  Lower jets may have zero gauge.  No simplicity premise, positivity of a
scalar explicit formula, or faithfulness away from the socle is used.

### Equivalent transport realization

Suppose a source-derived map \(j:N\to H\) intertwines $G$ with isometries on a normed target and
its kernel contains no nonzero one-dimensional $G$-submodule.  Then

\[
                         q(x)=\|j(x)\|
 \tag{6}
\]

satisfies `(4)`.  Arithmetic Shilov landing, a minimal unitary Wold dilation, a positive Hodge
completion, and an isometric Rees boundary are therefore realizations of `(ACSG)`, not distinct
last-mile principles.

## Riemann consequence

Assume `(ACSG)`.  Take the nonzero top conormal class `(2a)` at a nontrivial Xi divisor point
\(\rho\).  Apply the universal theorem to

\[
                         \lambda_\rho(g)=g^{\rho-1/2}.
 \tag{7}
\]

For one rational prime $p$,

\[
 1=|\lambda_\rho(p)|=p^{\Re\rho-1/2},
\]

and therefore \(\Re\rho=1/2\).  The source-derived horizontal parameter and the faithful
Gamma/co-Poisson defect already satisfy

\[
 a_\rho=2(\Re\rho-1/2),
 \qquad
 D_\rho=0\iff a_\rho=0.
 \tag{8}
\]

Consequently

\[
 \boxed{\forall\rho,\ D_\rho=0},
 \tag{9}
\]

and the Riemann hypothesis follows by the existing horizontal-vanishing frontier theorem.

The implication is short because the corpus has already constructed and proved faithful every
reporter in `(8)`.  All new mathematical burden is `(ACSG)`.

## Why this is sharper than prime-Schwartz temperedness

Prime-Schwartz temperedness says directly that every conormal jet has polynomial growth on every
bilateral valuation lattice.  In the natural analytic quotient that statement is already
equivalent to RH.  `(ACSG)` moves one level upstream:

1. no growth condition is imposed on any divisor character;
2. no target Hilbert space, self-adjoint operator, or $C^*$-boundary is part of the theorem;
3. character unitarity is forced by a source invariant, not imposed on divisor fibres;
4. any realization is constrained by the two actual anomaly readings, so an arbitrary norm on
   the analytic quotient is forbidden;
5. no global embedding is demanded: only exact character lines must have nonzero gauge.

Thus the missing producer is **an arithmetic invariant gauge conservative on the conormal
socle**.
Temperedness, two-way contractivity, common-test positivity, and horizontal vanishing are its
different shadows.

## Corpus-wide shadow laws

`(ACSG)` explains the current positive and negative results in one statement.

1. **Wold--Poisson ancestry.**  Quotienting the Wold ideal gives the independently fixed group
   boundary $C^*(G)$.  This is where unitary prime characters live.
2. **Gamma/BV unity.**  The regular determinant and singular first trace are two readings of the
   same relative class; retaining only one does not define the comparison.
3. **Hedenmalm dense radicals.**  Haar scalarization erases point fibres.  Hence its scalar
   $L^2$ gauge cannot realize `(ACSG)`.  Dense radicals elsewhere are permitted.
4. **Maximal vertical completion.**  Product-coordinate closed relations forget every output,
   including the socle.  `(ACSG)` requires a finer topology only on the exact character lines;
   it does not demand globally informative transport.
5. **Finite-Rees no-go.**  Off-line reflected valuation sectors have exponential bilateral
   growth, so no finite-order graded gauge can induce `(ACSG)`.
6. **Gamma whitening divergence.**  Fisher whitening completes occupancy, not the primitive
   conormal.  The unnormalized anomaly must be retained before the source-normal blow-up.
7. **Sonin/Calkin and four-unit Ward consumers.**  Their quotient norms and positive forms are
   candidate gauges.  The existing constructions fail either invariance or socle detection.
8. **Krein common-test obstruction.**  Primewise reflected interval cells are indefinite.  The
   Rees comparison must cancel the negative sector globally before positive boundary
   scalarization.
9. **Hypertranscendental persistence.**  Adjoining all scalar valuation layers preserves the
   differential matroid.  `(ACSG)` asks for a source gauge rather than a finite
   differential-algebraic relation.
10. **No blanket unitarity.**  Algebraic characters of $G$ with nonunit modulus remain valid.
    They are excluded only from exact character lines detected by the arithmetic source gauge.

## Hostile audit

### 1. Is `(ACSG)` merely RH renamed?

An arbitrary gauge chosen after inspecting the Xi divisor would be exactly that.  It is
prohibited.  The law is scientifically independent only if the gauge is constructed from `(3)`
and its two fixed anomaly readings before passing to divisor support.  It must commute with prime
enlargement, source reflection, Wold renewal, and change of a noncensoring BV window.  Those
requirements are falsifiable at finite source stages.

In the actual Xi source, existence of some gauge with the conclusion of `(ACSG)` is expected to be
RH-equivalent.  The frontier advance is not a weaker logical reformulation; it is identification
of the minimal source construction whose independent proof would force RH.  No claim of an RH
proof is made until that construction, invariance, and socle detection are proved.

### 2. Why not use the plain $A$-module boundary?

Every representation factoring through $A$ kills $Q$, every Wold projection $E_p$, the
Gamma determinant defect, and the BV first-trace density.  A plain boundary map has therefore
forgotten the source evidence it is supposed to transport.  The relative Rees totalization in
the proposed Rees realization is mandatory, not decoration.  Other realizations remain possible
if they produce the same source gauge without erasing either anomaly.

### 3. Why not infer gauge conservation from algebraic exactness?

The coefficient Wold complex is already split exact.  Algebraic contraction carries no Xi
information.  `(ACSG)` can arise only after coupling that contraction to the completed co-Poisson
constraint and proving both invariance and non-erasure of exact character lines in the singular
source-normal topology.

### 4. Why not infer it from positivity or bounded CP continuation?

The corpus proves ordinary bounded CP continuation has the wrong divisor order, and the local
reflected interval kernel has a negative two-point determinant.  Any valid CP object must be a
division-free Rees correspondence on unnormalized numerator/mass data; positivity may appear
only after global anomaly cancellation.

### 5. Countermodel test

A generalized-prime source with an off-line character may reproduce functional equation,
reflection, local Gamma factors, finite Wold identities, and algebraic conormal covariance.  It
cannot satisfy `(ACSG)`: the universal theorem would force its nonunitary socle line into the
gauge radical.
Thus the law uses more than the known local package and survives the Beurling firewall.

### 6. Why is all-$G$ invariance not an overpowered hidden premise?

It is stronger than the Riemann consequence needs.  One fixed prime already gives
\(|2^{\rho-1/2}|=1\).  Therefore the minimal proof target is invariance under $T_2$ plus
nonvanishing on every $G$-character line.  The all-$G$ form is retained as the functorial law;
failure at any other generator would diagnose a defective arithmetic construction, not block the
one-prime RH implication.

## Lean-proved completion-class impossibility and corrected open cores

The earlier formulation stopped too soon at “a singular completion is required.”  The current
Lean corpus proves substantially more: ordinary closure and arbitrary operator growth are not live
escapes for the actual first-trace source.

### `[CORPUS]` Actual first-trace complete no-escape theorem

`primeFirstTraceClock_completeNoEscapeUniversality` in
`formal/GaloisForLFunctions/RHTower/PrimeFirstTraceCompleteNoEscapeUniversalityLaw.lean` proves,
unconditionally and for the literal ordinary-prime first-trace graph, all of the following at once:

1. its ordinary graph closure is exactly the full source space times the zero-vacuum response
   hyperplane;
2. every closed linear relation extending it contains that entire vertical hyperplane;
3. no closed linear extension is single-valued;
4. no arbitrary closed single-valued relation containing the graph exists;
5. no nonlinear extension has closed graph;
6. every topology-preserving realization has nonclosed graph; and
7. every complete rigging preserving the exact source and clock norms remains sequentially
   nonclosable.

Thus an `(ASPW)` comparison which first passes to an ordinary closed boundary graph is impossible:
the closure has already erased source--response provenance.  Replacing boundedness by unbounded,
essential, nonlinear, multivalued, or differently presented ordinary closure does not repair it.

The abstract source-linear strengthening is `[PAPER-PROVED]`, not yet specialized in Lean to the
infinite prime product representation: every closed relation invariant under two disjoint
multiplication representations splits blockwise.  Applied to the reflected product-Poisson sectors,
this excludes every closed untwisted source-linear off-line relation, regardless of growth.  The
remaining escapes are therefore loss or twisting of the fixed source action, nonclosedness, or
passage to the relative extension before the boundary quotient.

### `[LEAN-PROVED]` Positive survivor: the preclosure essential edge

The no-go has a nontrivial positive survivor.  In
`formal/GaloisForLFunctions/RHTower/PrimeFirstTraceEssentialNormalBoundary.lean`,
`tendsto_primeFirstTrace_anisotropicEssentialGraph` proves that after removing the already attained
first response face and rescaling source and response at their distinct natural rates,

\[
 \bigl((\log p)X_p,\;p\Pi_1^\perp Y_p\bigr)
 \longrightarrow (e_1,Se_1)=(e_1,e_2).
\tag{10a}
\]

This is a genuine nonzero source-defined relative edge.  It exists only before ordinary closure;
ordinary closure also contains `(0,e_2)` and hence forgets which source produced the response.  The
mathematical lesson is exact: the required source object is an associated-graded/Bockstein of the
failure of source-normal specialization to commute with closure, not a more rapidly growing closed
operator.

### Further `[CORPUS]` exclusions on the surviving preclosure site

Three independent Lean theorems narrow that site further.

1. `no_finiteReesOperator_sews_flat_to_nonflat` and its actual Xi-sector specializations prove that
   every finite-Rees comparison preserves the all-orders-flat radical.  Any exact reflected sewing
   has norm beyond every inverse Wold Rees power.
2. `xiGammaEulerCanonicalCrossPrimeComplexifiedCoorientedOrbit_summable_noShorting` proves that an
   orbit-universal signed Gamma cancellation with fixed separated prime-depth coefficients is
   coefficientwise zero whenever its physical amplitudes are absolutely summable.  A nontrivial
   cancellation is therefore singular beyond `ell1`, or its coefficients must couple
   nonseparably to divisor/source provenance before frequency separation.
3. `xiGammaEulerPrimitiveReflectedFiniteOffDiagonalIncidence_similarity`, together with its
   characteristic-polynomial, determinant, cyclic-trace, and triangle-holonomy corollaries, proves
   that normalized rank-one prime-depth incidence is a flat coboundary.  Finite spectral and cycle
   invariants are horizontally blind.

These results give a completion-class impossibility theorem for the current producer architecture:

\[
\boxed{
\begin{array}{c}
\text{ordinary closed boundary comparison}\;\;\text{impossible},\\
\text{finite-Rees comparison}\;\;\text{impossible},\\
\text{fixed separated-frequency }\ell^1\text{ Gamma shorting}\;\;\text{impossible},\\
\text{finite rank-one/coboundary incidence selector}\;\;\text{blind}.
\end{array}}
\tag{10b}
\]

The real producer problem consequently has three irreducible `[OPEN CORE]` clauses:

1. **Preclosure extension landing.**  Globalize the actual local edge `(10a)` over the full
   squarefree action spectrum and construct the restricted Wold--Gamma/BV source extension to
   relative Contou--Carrere/Meyer comparison before ordinary closure or divisor localization.
2. **Nonseparable singular anomaly cancellation.**  Identify the Gamma determinant and BV first
   trace as boundary values of one relative class whose cancellation is neither finite-Rees,
   rank-one coboundary, nor fixed separated-frequency `ell1` summation.
3. **Atomic positive descent.**  Construct the source-pointed invariant positive weight only after
   that relative cancellation and prove that its comparison remains finite and strictly positive
   on every exact top conormal character line, uniformly before a divisor is selected.

Clauses 1--2 construct the only completion category not excluded by `(10b)`.  Clause 3 is still the
load-bearing RH implication: it is the global atomic non-erasure theorem.  None is supplied by an
ordinary Hilbert completion, an unbounded closed operator, or the already formalized consumer law.

## Proven arithmetic half of the source law

Recent source constructions close the finite-stage half of `(ACSG)` unconditionally:

1. coherent ramified monomial sectors are only the raw sector and the top-conormal sector;
2. top-conormal power pullbacks compose strictly;
3. top-conormal embedding and residue are an adjoint isometric split pair;
4. actual rational-Witt refinements preserve that sector and form a strict cocone;
5. landing in the literal algebraic Calderón--Witt packet is injective on the admitted top sector;
6. the Gamma/co-Poisson factorial receiver kills no finite multiplicity jet;
7. the one-sided Gamma mate curvature is the actual Gamma/Calderón--Witt boundary coefficient and
   vanishes exactly at zero horizontal displacement.

Thus arithmetic source, multiplicity receiver, and exact obstruction have been constructed.  What
is not proved is passage of the finite-stage isometric gauge through the completed
Gamma/co-Poisson comparison without killing the top character line.  The finite-stage theorem
explicitly stops there; treating its coefficient-faithful landing as completed conormal
conservativity would be false.

The vectorwise erasure-or-neutrality consumer theorem is also already formalized by
`completeResolution_sourceCharacter_selection`.  The new frontier is not to prove that consumer
lemma again.  It is to remove its erasure alternative simultaneously and source-natively, without
choosing $\rho$.  In `(ACSG)` language, that means constructing one gauge whose zero locus contains
no exact conormal character line.

Exact formal evidence:

- `deningerTopConormalPowerPullback_comp` -- strict source composition;
- `inner_deningerTopConormalEmbedding` and `deningerTopConormalResidue_embedding` -- finite-stage
  isometric split top grade;
- `deningerRamifiedFiniteStageToAlgebraic_injectiveOn_admittedSector` -- coefficient-faithful
  rational-Witt landing;
- `iteratedDeriv_gammaCoPoissonIntervalCell_self_ne_zero` -- no finite multiplicity censorship;
- `deningerOneSidedFramedCurvature_two_eq_zero_iff` -- exact horizontal obstruction;
- `deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_framedCurvaturePolarization` -- the
  obstruction is the actual Gamma/Calderón--Witt boundary coefficient;
- `riemannHypothesis_of_sourceForcedHorizontalVanishing` -- zero obstruction finishes RH.

## Exact open core

Construct one source-normal gauge, not another reporter:

\[
 \boxed{
 \text{source Wold--Toeplitz extension}
 \xrightarrow{\ \text{Gamma determinant + BV first trace}\ }
 \text{relative source-normal Rees totalization}
 \xleftarrow{\ \jmath_{\rm src}\ }
 \text{completed co-Poisson conormal complex}
 \xrightarrow{\ \Omega_{\rm src}(\jmath_{\rm src}(-)^*\jmath_{\rm src}(-))^{1/2}\ }
 q_{\rm src}}
 \tag{11}
\]

and prove:

1. the two anomaly formulas are the regular and singular boundary values of one chain class;
2. the comparison exists before divisor specialization and is independent of prime exhaustion;
3. its boundary cohomology carries the centered prime action and a source-pointed positive weight;
4. the weight is invariant, finite, and strictly positive on every exact $G$-character line;
5. for each multiplicity packet it retains the top exact character line, without a
   divisor-selected norm.

Clause 4 is the load-bearing theorem.  Clauses 1--3 prevent it from being a renamed
temperedness assumption; clause 5 prevents a simple-zero truncation.  Full injectivity, global
positivity, and an all-prime Hilbert embedding are not gates: hostile review shows each is
stronger than the Riemann consequence requires and needlessly collides with the corpus's
dense-radical, Krein, and maximal-vertical no-go results.

## Gates

- [x] source law stated without divisor variables
- [x] invariant-gauge support theorem proved on paper
- [x] deduction `(ACSG) -> forall rho, D_rho=0 -> RH` proved on paper
- [x] bounded, plain-module, scalar-Hilbert, finite-Rees, and divisor-GNS shortcuts excluded
- [x] overpowered full-injectivity candidate retired
- [x] actual first-trace ordinary closed, nonlinear, topological, and exact-norm completion escapes excluded in Lean
- [x] actual source-normal preclosure edge `e_1 -> e_2` constructed in Lean
- [x] finite rank-one/coboundary and fixed separated-frequency `ell1` Gamma shorting excluded in Lean
- [ ] globalize the essential edge through the preclosure Wold--Gamma/BV relative extension
- [x] exclude every unordered scalar beyond-`ell1` Gamma-orbit cancellation in Lean
- [ ] construct a genuinely nonscalar preclosure or divisor-coupled anomaly cancellation before frequency separation
- [x] finite-stage ramified top-conormal dagger/isometry law proved
- [x] finite-stage rational-Witt top-sector landing proved coefficient-faithful
- [x] local Gamma/co-Poisson receiver proved noncensoring at every multiplicity
- [x] fixed reflected-Gaussian grade proved nonzero on every multiplicity-exact divisor copy
- [x] global resolved comparison and conservative codiagonal proved atomically non-erasing
- [ ] construct relative Rees totalization from actual source complexes
- [ ] identify Gamma determinant and BV first trace as one chain class
- [ ] construct canonical comparison `j_src` and source-pointed weight `Omega_src`
- [ ] prove weight invariance under one fixed prime action
- [ ] prove finite positive weight on every conormal character line
- [ ] prove presentation and prime-exhaustion independence
- [ ] run independent hostile mathematical review
- [ ] formalize only after the complete source proof exists
- [ ] RH

## Honest verdict

`(ACSG)` has been created and the implication to \(\forall\rho,D_\rho=0\) is complete.  `(ACSG)`
itself is not proved.  Its invariant-gauge lemma is elementary and is not a publication-level
result by itself.  Scientific progress here is the minimality theorem supplied by the hostile
reductions:

- no global injectivity is needed;
- no Hilbert space, self-adjoint operator, or scalar positivity theorem is needed;
- no control of lower multiplicity jets is needed;
- no all-prime estimate is needed;
- one source-defined gauge, one fixed prime invariance, and non-erasure of individual top
  character lines are sufficient.

The initial audit stopped at the finite-stage ingredients and the exact erasure-or-neutrality
alternative.  The source constructions summarized below supersede that audit: bare global atomic
non-erasure is now proved.  RH still does not follow, because non-erasure supplies no conserved
centered-flow amplitude.

## 2026-08-03 frontier correction: global atomic non-erasure is closed

The fixed reflected Meyer Gaussian and the adaptive reflected prime-normal comparison close the
bare non-erasure clause more strongly than the preceding audit recorded.  Put

\[
 h(q)=\mathcal M(g_{\rm ref})(q),\qquad
 R_p=J_p h,\qquad O_p=C_p h,
\]

where \(h\in\ell^2(\Xi_{\rm copy})\) is the source-derived Gaussian horizon grade,
\(J_p\) is the fixed-prime global reflected comparison, and \(C_p\) is its codiagonal.  Existing
source theorems give

\[
 h(q)\ne0,\qquad \|J_p a\|=\|a\|,\qquad
 \frac34\|a\|\le\|C_p a\|.
\]

Fiberwise,

\[
 R_p(q)=h(q)u_{p,q},\qquad
 O_p(q)=h(q)c_{p,q},qquad
 \|u_{p,q}\|=1,\quad c_{p,q}\ne0.
\]

Therefore one fixed source record simultaneously retains every multiplicity-exact divisor copy,
and the conservative observation retains every one of those fibres.  Equivalently, every
source-weighted atom \(h(q)e_q\) survives both maps.  No divisor-selected damping and no RH premise
occur.  This is the **global atomic non-erasure theorem**.

The same theorem has a sharp negative half:

\[
 h(q)\longrightarrow0\quad(q\to\infty\text{ cofinally}),
 \qquad
 \nexists c>0\;\forall q\; c\le |h(q)|.
\]

Thus atomic non-erasure and stable/invariant amplitude conservation are distinct.  The theorem
closes clause 5 of `(11)` and the non-erasure part of clause 4, but not `(ACSG)`: neither \(J_p\)
nor \(C_p\) is proved to intertwine the centered divisor character with a source action preserving
the induced norm.  Indeed the explicit centered Gaussian countertransport has uniformly bounded
source half-density capacity, while uniform capacity of its global Xi evaluation field is already
equivalent to RH.  The remaining theorem is consequently **global centered-flow capacity
conservation** (or an equivalent reflection-invariant factorization), not global atomic
non-erasure.

Formal target:

- `DeningerMeyerGlobalAtomicNonErasure.lean`;
- one source record nonzero in every fibre;
- its conservative codiagonal nonzero in every fibre and bounded below globally by `3/4`;
- every source-weighted divisor basis atom survives both transports;
- no positive uniform lower coefficient bound exists.

## 2026-08-03 three-core closure audit

The requested producer chain now has three mathematically distinct statuses.

### 1. Essential edge through the Wold--Gamma/BV preclosure

The local edge and every ordinary completion escape are closed:

- `tendsto_primeFirstTrace_anisotropicEssentialGraph` constructs the literal source/response edge
  \((e_1,e_2)\);
- `primeFirstTraceClock_completeNoEscapeUniversality` proves that ordinary graph closure, every
  closed linear extension, every closed single-valued relation, every nonlinear closed graph,
  topology-preserving realization, and every exact-norm complete rigging loses single-valued
  source coupling;
- the paper-proved prime-tail co-Poisson preclosure constructs the sharp essential boundary and
  divisor monodromy before scalar specialization.

What remains is not another completion.  It is the strict comparison morphism from the
squarefree Wold--Gamma/BV preclosure totalization to the relative determinant/Contou--Carrere--Meyer
extension, with the essential edge and literal Gamma/co-Poisson/Sonin boundary in one chain class.
No dependency-closed proof of that landing exists in the corpus or audited literature.

### 2. Beyond-`ell1` cancellation

`GammaSignedUnconditionalOrbitNoShorting.lean` closes the ordinary unordered scalar interpretation.
For the actual canonical cross-prime/depth orbit, existence of an unordered scalar sum at the one
real displacement already forces absolute physical-amplitude summability.  The existing Bohr
coefficient theorem then makes a universal modular-axis cancellation coefficientwise zero.

Thus “nonseparable and beyond `ell1`” cannot mean a scalar `HasSum` hidden in a larger carrier.
The remaining object must stay relative/distribution-valued before frequency separation, make the
relevant scalar evaluation discontinuous or undefined at preclosure level, or couple coefficients
to divisor provenance before Bohr separation.  A conditionally convergent enumeration is not a
divisor/order-independent source law.

### 3. Atomic positive descent and non-erasure

Bare divisor-independent atomic non-erasure is already unconditional:

- `reflectedGaussian_globalAtomicNonErasure` retains every multiplicity-exact divisor copy and
  gives a global `3/4` codiagonal lower modulus;
- `xiCenteredFlowConservedCapacity_eq_multiplicityMass` constructs exact source-derived covariant
  positive conservation of the complete derivative-order packet.

The remaining static assertion is sharply classified:

\[
 \texttt{XiCenteredFlowStaticCapacity}
 \quad\Longleftrightarrow\quad
 \mathrm{RH},
\]

and global triviality of the prime-tail modular countercharacter is likewise equivalent to RH.
The covariant metric uses the actual fibre character
\(e^{-(2\Re\rho-1)\tau}\); replacing it by one fixed invariant positive metric is exactly the
unproved source-forced vanishing of that character.  Therefore non-erasure, multiplicity descent,
Poisson completion, and covariant transport are no longer open cores.  The unique final premise is
source-first triviality of the horizontal modular cocycle.

### Exact surviving dependency chain

```text
strict preclosure Wold--Gamma/BV relative-extension landing       OPEN
  -> nonscalar/divisor-coupled arithmetic anomaly annihilation    OPEN
  -> atomic non-erasure + covariant multiplicity descent          LEAN-PROVED
  -> source-forced modular-cocycle triviality                      RH-EQUIVALENT
```

This audit does not claim RH.  It proves that ordinary closure, scalar unordered beyond-`ell1`
summation, missing atomic support, and missing covariant capacity are not the remaining problem.

## 2026-08-03 strict-preclosure regularization threshold

`PrimeFirstTraceEssentialEdgeSchattenThreshold.lean` now globalizes the literal normalized local
edge over every ordinary prime.  Its source and response corrections are both `ell2`, while the
source correction is not `ell1`.  The exact retained coordinate is

\[
 a_p(2)=\frac1p-\frac{p}{r_p^2}\ge\frac{3}{4p}.
\]

Therefore the first global preclosure anomaly is canonically Hilbert--Schmidt but not trace class.
This rules out an ordinary coefficient trace/Fredholm determinant at the live site and forces the
regular Wold--Gamma comparison to begin at second-regularized determinant level.  The local edge
has consequently been globalized as an actual all-prime Hilbert correction, but the operator
realization and its relative landing remain open.

The first arrow in the dependency chain is now refined to

```text
all-prime essential-edge ell2/not-ell1 source object              LEAN-PROVED
  -> diagonal/operator det2 realization                           OPEN
  -> identify det2 quadratic cocycle = Gamma regular anomaly      OPEN
  -> identify same relative class = BV singular first trace       OPEN
  -> source-to-Xi arithmetic annihilation                          OPEN
```

An invariant positive trace is not a substitute: positivity, invariance, and non-erasure on an
exact centered character line already imply its unitarity and hence reinsert the RH-bearing
premise.  Positivity can descend only after the strict `det2`/BV relative class is constructed.
