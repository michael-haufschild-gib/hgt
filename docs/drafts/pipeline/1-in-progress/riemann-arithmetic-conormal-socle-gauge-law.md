# Arithmetic conormal socle-gauge conservation law

- **ID:** `riemann-arithmetic-conormal-socle-gauge-law`
- **Short name:** arithmetic conormal socle-gauge conservation (`ACSG`)
- **Stage:** `1-in-progress`
- **Type:** UNIVERSAL SUPPORT THEOREM + FROZEN ARITHMETIC SOURCE LAW
- **Status:** `[UNIVERSAL CONSUMER PAPER-PROVED] [SOURCE LAW OPEN] [NOT RH]`
  `[NO DIVISOR-SELECTED METRIC] [NOVELTY UNVERIFIED]`
- **Lean:** none until the source comparison is constructed on paper
- **Parents:**
  - `../4-publication-ready/riemann-boundary-completeness-law/main.tex`;
  - `source-curved-prime-torus-conormal-temperedness.md`;
  - `singular-infinite-source-pointed-common-test-factorization.md`;
  - `../2-fully-proven/prime-sieve-wold-gamma-bv-relative-character.md`;
  - `../2-fully-proven/new_scientific_knowledge/other/primitive-fibre-modular-renormalization-law.md`;
  - `formal/GaloisForLFunctions/RHTower/CompleteResolutionSourceCharacterSelectionLaw.lean`;
  - `formal/GaloisForLFunctions/RHTower/DeningerRamifiedTopConormalFiniteStageCocone.lean`.

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
- [x] finite-stage ramified top-conormal dagger/isometry law proved
- [x] finite-stage rational-Witt top-sector landing proved coefficient-faithful
- [x] local Gamma/co-Poisson receiver proved noncensoring at every multiplicity
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

Current corpus proves every finite-stage ingredient and the exact erasure-or-neutrality
alternative.  It does not prove global atomic non-erasure.  Any claim that RH now follows
unconditionally would therefore be false.  Next legitimate theorem is not another RH
equivalence: it is construction of the singular source-normal gauge and proof that no exact
conormal character line lies in its zero locus.

## 2026-08-03 frontier correction: global atomic non-erasure is closed

The fixed reflected Meyer Gaussian and the adaptive reflected prime-normal comparison close the
bare non-erasure clause more strongly than the preceding audit recorded.  Put

\[
 h(q)=\mathcal M(g_{\rm ref})(q),\qquad
 R_p=J_p h,\qquad O_p=C_p h,
\]

where (h\in\ell^2(\Xi_{\rm copy})) is the source-derived Gaussian horizon grade,
(J_p) is the fixed-prime global reflected comparison, and (C_p) is its codiagonal.  Existing
source theorems give

\[
 h(q)\ne0,qquad \|J_p a\|=\|a\|,qquad
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
source-weighted atom (h(q)e_q) survives both maps.  No divisor-selected damping and no RH premise
occur.  This is the **global atomic non-erasure theorem**.

The same theorem has a sharp negative half:

\[
 h(q)\longrightarrow0\quad(q\to\infty\text{ cofinally}),
 \qquad
 \nexists c>0\;\forall q\; c\le |h(q)|.
\]

Thus atomic non-erasure and stable/invariant amplitude conservation are distinct.  The theorem
closes clause 5 of `(11)` and the non-erasure part of clause 4, but not `(ACSG)`: neither (J_p)
nor (C_p) is proved to intertwine the centered divisor character with a source action preserving
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
