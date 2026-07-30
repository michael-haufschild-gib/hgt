# Polarized irregular source-purity law

- **ID:** `polarized-irregular-source-purity-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / RH-BEARING SOURCE CONJECTURE
- **Source:** whole-corpus synthesis of Wold/BV boundary volume, multiple-Gamma scheme change,
  Hellinger--Rees reflection fracture, Poisson/co-Poisson source reflection, and enhanced-boundary
  no-go results
- **Statement:** A reflected renormalization gauge is bi-moderate exactly where its leading odd
  irregular charge is purely imaginary.  For the ordinary-prime Wold--Gamma source this charge is
  \(2(s-\tfrac12)\), so a faithful polarized irregular landing of every Xi conormal implies RH.

## Goal

Replace the vague requirement “find a third completion” by one source theorem with the exact
capabilities forced by the corpus:

1. retain essential exponential/Stokes data rather than quotienting it to zero;
2. retain every Xi divisor conormal and multiplicity jet;
3. carry a Hermitian polarization, not functional-equation duality alone;
4. permit unitary essential oscillation but exclude essential real norm growth;
5. be constructed from the ordinary-prime Euler--Gamma/co-Poisson source before choosing a zero.

The target is not a regular-singular completion.  Such a category would also delete the critical
oscillatory factors \(\exp(2it/a)\).  The required object is polarized and irregular.

## What the corpus is saying

The repeated obstructions have one common interpretation.

```text
finite prime stages:
  every gauge and point fibre exists, but no infinite boundary purity;

bare all-prime L2:
  restores covariance, but point conormals dissolve into continuous spectrum;

determinant or scalar completion:
  retains regular holonomy, but deletes the divergent first trace;

normalized boundary states:
  retain a weak atomic endpoint, but normalization amplifies the tail and destroys strong control;

Hellinger--Rees boundary:
  retains finite-grade, half-normal, and all-orders-flat sectors, but lacks source polarization;

multiple-Gamma scheme change:
  computes the deleted first trace as an actual irregular exponential gauge;

wild/enhanced completion:
  can retain the essential gauge, but arithmetic source landing and polarization remain open.
```

Thus critical line is not merely a symmetry axis or positivity locus.  It is the **Hermitian-pure
locus of the reflection-odd irregular renormalization charge**.

## Theorem: reflected renormalization-anomaly cone

`[PROVED HERE]`

Let \(b_\lambda>1\) tend to \(+\infty\).  Fix \(t\) and suppose a family of scheme-change
counterterms satisfies
\[
 C_\lambda(t)
 =
 b_\lambda Q(t)+R_\lambda(t),\qquad
 |\operatorname{Re}R_\lambda(t)|
 \leq A_t\log b_\lambda+B_t.                                \tag{1}
\]
Put
\[
 G_\lambda(t)=\exp C_\lambda(t).                            \tag{2}
\]
Call \(G(t)\) polynomially moderate if
\[
 |G_\lambda(t)|\leq K_tb_\lambda^{N_t}                      \tag{3}
\]
eventually, and **bi-moderate** if both \(G(t)\) and \(G(t)^{-1}\) satisfy `(3)`.
Then
\[
 \boxed{\quad
 G(t)\text{ is bi-moderate}
 \quad\Longleftrightarrow\quad
 \operatorname{Re}Q(t)=0.
 \quad}                                                     \tag{4}
\]

More precisely, \(G(t)\) is moderate for
\(\operatorname{Re}Q(t)\leq0\), its inverse is moderate for
\(\operatorname{Re}Q(t)\geq0\), and the two conditions meet exactly on `(4)`.

### Proof

Taking real logarithms in `(2)` gives
\[
 \log|G_\lambda(t)|
 =
 b_\lambda\operatorname{Re}Q(t)+O(\log b_\lambda).          \tag{5}
\]
If \(\operatorname{Re}Q(t)>0\), the linear term in \(b_\lambda\) dominates every
\(N\log b_\lambda\), so `(3)` fails.  If \(\operatorname{Re}Q(t)<0\), the same argument applied
to \(G^{-1}\) makes inverse moderation fail.  If the real part is zero, `(1)` bounds both
\(\log|G|\) and \(-\log|G|\) by \(O(\log b_\lambda)\), proving bi-moderation.

Now let two finite-source presentations satisfy
\[
 F_{\lambda,h}(t)
 =
 \exp C_\lambda(t)\,F_{\lambda,g}(t).                       \tag{6}
\]
Their reflected quotients
\[
 \Pi_{\lambda,j}(t)
 =
 \frac{F_{\lambda,j}(t)}{F_{\lambda,j}(-t)}
\]
obey
\[
 \frac{\Pi_{\lambda,h}(t)}{\Pi_{\lambda,g}(t)}
 =
 \exp\!\left(C_\lambda(t)-C_\lambda(-t)\right).             \tag{7}
\]
Therefore only the odd counterterm
\[
 Q_{\rm odd}^{\rm pol}(t)=Q(t)-Q(-t)                       \tag{8}
\]
survives reflection polarization, and the bi-moderate locus is
\[
 \operatorname{Re}\!\left(Q(t)-Q(-t)\right)=0.             \tag{9}
\]

## New corollaries

### 1. Even counterterms cannot locate a reflection axis

Every even renormalization term cancels identically in `(7)`.  Hence an RH mechanism based on
genus-two determinants, squared intensities, or another reflection-even regularization must retain
an independent odd extension class.  This explains why the corpus repeatedly recovers exact
completed values while losing orientation.

### 2. Scheme-independent divisors are insufficient

The exponential in `(6)` never vanishes.  Thus every scheme has the same zero divisor even when
the transition gauge has essential real growth.  Zero-set invariance therefore supplies no
purity.  The load-bearing object is the **metrized conormal line**: at a common zero its leading
jet is multiplied by \(\exp C_\lambda(t)\), and `(4)` decides whether that jet survives
bi-moderately.

This separates two statements that previous routes conflated:

```text
divisor support survives scheme change: automatic;
Hermitian conormal survives scheme change: critical-line selector.
```

### 3. First trace is the unique hyperplane selector

If the first divergent odd term has degree \(d\), the primary purity locus is
\[
 \operatorname{Re}(\beta t^d)=0.                            \tag{10}
\]
For \(d>1\), this is generally a union of rays or curved branches.  A nonzero linear first-trace
charge gives one real hyperplane.  Thus the ordinary-prime Wold first trace is not a dispensable
counterterm: its degree-one character is what can select one critical line.

### 4. Infinite rank alone changes nothing

Let \(a_\lambda=b_\lambda^{-1}\).  The all-orders-flat radical
\[
 {\mathfrak F}_\infty(a;E)
 =
 \{v:\|v_\lambda\|=o(a_\lambda^N)\text{ for every }N\}
\]
is preserved by every operator family with
\[
 \|R_\lambda\|_{\rm op}=O(a_\lambda^{-K})
\]
for one finite \(K\), in arbitrary dimension.  This is paper- and Lean-proved in
`RHTower.reesAllOrdersFlat_apply_reesOperatorGradeAtMost`.

Consequently an infinite completion crosses the Hellinger reflection fracture only by an
essentially singular operator norm, by ceasing to be a bounded/closable operator correspondence,
or by losing the source conormal.  “Infinite-dimensional” is not a mechanism.

## Exact ordinary-prime specialization

For primes below \(x\), let
\[
 a_x=\prod_{p\leq x}(1-p^{-1}),\qquad b_x=a_x^{-1}.          \tag{11}
\]
The corpus proves unconditionally:

1. \(a_x>0\) and \(a_x\to0\);
2. the first prime-occupation trace is exactly \(b_x\);
3. changing the finite occupation product from genus zero to genus one gives
   \[
   F_{x,1}(t)=\exp(t/a_x)F_{x,0}(t);
   \]
4. on reflected quotients,
   \[
   \Pi_{x,1}(t)=\exp(2t/a_x)\Pi_{x,0}(t).                   \tag{12}
   \]

These identities are Lean-proved in
`GaloisForLFunctions.PrimeWoldGammaGlobalBoundaryVolume`.
Apply `(4)` to `(12)` with \(Q(t)=2t\):
\[
 \boxed{\quad
 \exp(2t/a_x)\text{ is bi-moderate in norm}
 \quad\Longleftrightarrow\quad
 \operatorname{Re}t=0.
 \quad}                                                     \tag{13}
\]
For the centered zeta coordinate
\[
 t=s-\tfrac12,
\]
equation `(13)` is exactly
\[
 \operatorname{Re}s=\tfrac12.                              \tag{14}
\]

The Hellinger--Rees theorem is a second, nonlinear shadow of the same boundary split: one
reflected radial packet is all-orders flat while the other has finite half-normal order.  The
finite-Rees operator theorem proves that no moderate source equivalence can sew them off `(14)`.

## Theorem: vacuum--anomaly reciprocity

`[PROVED HERE]`

The exact common object behind the Wold, Hellinger, and Gamma formulas is one unnormalized
occupation vector.

Let \(S\) be any finite set and \(0<q_i<1\) for \(i\in S\).  On
\(\ell^2(\mathbb N^S)\), define
\[
 u_q(\nu)=\prod_{i\in S}q_i^{\nu_i/2},\qquad
 a(q)=\prod_{i\in S}(1-q_i).                               \tag{14a}
\]
Then
\[
 \|u_q\|^2
 =
 \sum_{\nu\in\mathbb N^S}\prod_iq_i^{\nu_i}
 =
 \prod_i(1-q_i)^{-1}
 =
 a(q)^{-1}.                                                \tag{14b}
\]
Put \(\widehat u_q=a(q)^{1/2}u_q\).  This is a unit vector, and its normalized vacuum
probability is
\[
 |\langle\delta_0,\widehat u_q\rangle|^2=a(q).             \tag{14c}
\]
Consequently
\[
 \boxed{\quad
 |\langle\delta_0,\widehat u_q\rangle|^2\,
 \|u_q\|^2=1.
 \quad}                                                     \tag{14d}
\]

For the multiple-Gamma occupation product, the exact genus-zero/genus-one scheme change is
\[
 F_1(t)
 =
 \exp\!\left(t\sum_\nu\prod_iq_i^{\nu_i}\right)F_0(t)
 =
 \exp\!\left(t\|u_q\|^2\right)F_0(t).                      \tag{14e}
\]
Its reflected quotient therefore changes by
\[
 \exp\!\left(2t\|u_q\|^2\right)
 =
 \exp\!\left(
   \frac{2t}{|\langle\delta_0,\widehat u_q\rangle|^2}
 \right).                                                  \tag{14f}
\]

### Proof

Finite Fubini and the geometric series give `(14b)`.  Equations `(14c)`--`(14d)` follow because
the vacuum coordinate of \(u_q\) is one.  The exact multiple-Gamma scheme-change theorem says
that raising genus from zero to one adds \(t\) times the first occupation moment; `(14b)` identifies
that moment with \(\|u_q\|^2\), proving `(14e)`--`(14f)`.

For \(q_p=p^{-1}\), `(14a)`--`(14f)` become
\[
 \|u_S\|^2=Z_S(1)=a_S^{-1},\qquad
 |\langle\delta_0,\widehat u_S\rangle|=\sqrt{a_S},\qquad
 G_S^{\rm pol}(t)=e^{2t/a_S}.                              \tag{14g}
\]

This is the sought exact reinterpretation:

```text
Wold boundary volume a_S
  = normalized occupation-vacuum probability;

Hellinger half-density sqrt(a_S)
  = normalized vacuum amplitude;

Gamma first-trace anomaly a_S^(-1)
  = squared norm of the unnormalized occupation vector;

irregular reflected gauge exp(2t/a_S)
  = exponential of centered charge times that lost squared norm.
```

Normalization/projectivization keeps \(\widehat u_S\) but deletes \(\|u_S\|^2\).  Scalar
determinant regularization keeps the regular genus-one function but deletes the same first moment.
The deleted quantities are not two defects: `(14d)` proves they are reciprocal records of one
occupation line.

Therefore the minimal third completion is not merely a new Hilbert space.  It is the
**projective occupation direction together with its norm/determinant torsor**.  In boundary
language it must retain simultaneously
\[
 \left(\widehat u_S,\sqrt{a_S},a_S^{-1}\right),             \tag{14h}
\]
with the algebraic relation `(14d)`, rather than choose one normalized shadow.

The scalar identities used in `(14g)` are already Lean-proved as
`finitePrimeOccupationFirstMoment_eq_inv_woldBoundaryVolume` and
`finitePrimeGenusOnePolarizedPhase_eq_irregularGauge_mul`.  The Hilbert-vector packaging
`(14a)`--`(14f)` is paper-proved here but is not yet separately formalized.

## Polarized irregular type

Write the leading irregular type of `(12)` as
\[
 \phi_t(a)=\frac{2t}{a}.                                    \tag{15}
\]
Irregular duality and Hermitian conjugation act by
\[
 {\mathbb D}:\phi\longmapsto-\phi,\qquad
 {\mathbb C}:\phi\longmapsto\overline{\phi}.                \tag{16}
\]
A Hermitian polarization of the reflected conormal identifies these two operations at leading
irregular order.  Hence
\[
 -\phi_t=\overline{\phi_t}\pmod{O(\log a^{-1})}.             \tag{17}
\]
Multiplying `(17)` by \(a/2\) and taking the boundary limit gives
\[
 -t=\bar t
 \quad\Longleftrightarrow\quad
 \operatorname{Re}t=0.                                     \tag{18}
\]

This is why the correct completion is wild rather than regular singular.  At \(t=i\tau\), the
factor \(\exp(2i\tau/a)\) remains essentially singular as a holomorphic function, but has unit
norm and is allowed by the polarization.  For \(\operatorname{Re}t\neq0\), one of the two
reflected norms has essential growth.

## RH-bearing source conjecture

> **[CONJECTURE -- XI WOLD-POLARIZED IRREGULAR LANDING.]**
> The ordinary-integer Poisson comb, with its unique-factorization Wold/BV prime polarization and
> completed Gamma/co-Poisson Mellin realization, constructs before divisor specialization a
> Hausdorff enhanced irregular object over the boundary \(a\to0\) such that:
>
> 1. it retains the occupation direction, vacuum half-density, and determinant norm record in
>    `(14h)`, and its reflection-odd irregular type is the exact source gauge `(15)`;
> 2. Poisson reflection is the Hermitian polarization duality `(16)`;
> 3. Meyer's source quotient \(M_\zeta\) and every Xi principal conormal jet land faithfully;
> 4. the landing is strict for the irregular/Rees filtration and preserves integral
>    multiplicity;
> 5. after factoring the unitary irregular type, reflection and its inverse have finite Rees
>    operator norm.

This is the exact proposed universal law in the zeta source.  It is source-pure: all structure is
defined before a zero is selected.  It is also honestly RH-bearing: the corpus does not yet prove
clauses 2--5 simultaneously.

## Conditional RH theorem

`[DEPENDENCY-CLOSED GIVEN THE SOURCE CONJECTURE]`

Assume `XI WOLD-POLARIZED IRREGULAR LANDING`, and let \(\rho\) be any nontrivial Xi zero.  By
faithful conormal landing, its nonzero top multiplicity jet has centered irregular type
\[
 \phi_{\rho-1/2}(a)=\frac{2(\rho-1/2)}a.
\]
Polarization gives `(17)`, hence
\[
 -(\rho-\tfrac12)=\overline{\rho-\tfrac12}.
\]
Taking real parts yields
\[
 \operatorname{Re}\rho=\tfrac12.
\]
The argument applies to every nontrivial zero and preserves the top jet, so it proves RH without
assuming simplicity.

## Why this is not a renamed classic route

- Hilbert--Pólya asks for a self-adjoint operator whose eigenvalues encode zeros.  Here point
  fibres may be distributional and the invariant is their wild irregular type.
- de Branges/Weil positivity asks for a global sign.  Here the selector is Hermitian purity of an
  exact source renormalization anomaly.
- Functional equation gives duality \(\phi\mapsto-\phi\) but no Hermitian identification with
  \(\bar\phi\).
- Hypertranscendence guarantees that finite source presentations cannot collapse to a finite
  differential model; it does not itself construct the polarization.
- Wild Hodge theory supplies parent categories with exponential factors, Stokes data, conjugation,
  and polarization.  It does not construct the ordinary-prime Wold object or land Xi conormals.

## Hostile audit

1. **No claim of RH is made.**  Source landing/polarization is open and load-bearing.
2. **Regular singularity would be false as target.**  It excludes the unitary essential phases
   required at nonzero critical height.
3. **Divisor invariance is automatic and useless alone.**  Exponential scheme changes preserve
   every zero.
4. **Functional equation is insufficient.**  It supplies `(16)`'s first map, not the
   polarization equating it to conjugation.
5. **A chosen metric is circular.**  Hermitian structure must descend from the Poisson/Wold
   source before divisor specialization.
6. **Finite or infinite Hilbert vocabulary is insufficient.**  The precise requirement is a
   finite-Rees bound on the polarized operator norm after removal of the unitary irregular type.
7. **Generalized-prime countermodels remain falsifiers.**  They must be excluded by the literal
   ordinary-integer Poisson comb, Wold boundary volume, and source conormal landing, not by FE,
   positivity, entire completion, or HT alone.
8. **Wild-Hodge parent theory is not arithmetic landing.**  Invoking a polarizable wild twistor
   category without constructing the zeta object inside it would be theatre.

## Literature boundary

Parent literature already provides the abstract wild categories:

- Mochizuki, *Wild Harmonic Bundles and Wild Pure Twistor D-modules*,
  https://arxiv.org/abs/0803.1344;
- Sabbah, *Wild twistor D-modules*, https://arxiv.org/abs/0803.0287;
- D'Agnolo--Kashiwara, *On the irregular Riemann--Hilbert correspondence*,
  https://arxiv.org/abs/2408.04260;
- Hohl, *Kashiwara conjugation and the enhanced Riemann--Hilbert correspondence*,
  https://arxiv.org/abs/2307.15608;
- Sabbah, *Irregular Hodge theory*, https://arxiv.org/abs/1511.00176.

These sources cover enhanced exponential decompositions, irregular/Stokes data, conjugation,
polarization, and strict irregular Hodge filtrations.  They do not state the ordinary-prime
first-trace identity `(12)`, identify its charge with the centered zeta character, construct a
Wold-polarized Xi conormal landing, or derive RH from its Hermitian purity.  Exact-conjunction
novelty is therefore provisional; the asymptotic theorem `(4)` itself is elementary and not
claimed as standalone novelty.

## Proof program

1. Construct the finite-prime polarized irregular triple from the already formalized projective
   prime Fourier clock, the norm/vacuum torsor `(14h)`, and genus-zero/genus-one Gamma transition.
2. Prove uniform polarizability of its cofinal enhanced limit.  The estimate must control the
   Hermitian operator norm after factoring \(\exp(2it/a_x)\); scalar determinant convergence is
   insufficient.
3. Construct the source map from the pre-divisor integer-comb/co-Poisson incidence complex, or
   Meyer's \(M_\zeta\), into that enhanced limit.
4. Prove nonvanishing and strictness on every top Xi multiplicity jet.
5. Apply `(18)` and formalize the dependency-closed RH theorem in Lean.

The next non-immediate obstacle is Step 2: a cofinal wild harmonic/polarized estimate for the
literal ordinary-prime finite-stage triples.  Step 3 must be developed alongside it so the metric
cannot be fitted after inspecting zeros.

## Gates

- [x] 0 → 1: source-pure object, exact anomaly, RH consumer, and falsifiers stated
- [x] exact Wold boundary volume and reciprocal first trace Lean-proved
- [x] exact genus scheme-change irregular gauge Lean-proved
- [x] reflected bi-moderate critical-line selector Lean-proved
- [x] general finite-Rees operator-radical law paper- and Lean-proved
- [x] universal vacuum--anomaly reciprocity theorem paper-proved
- [x] reflected renormalization-anomaly theorem paper-proved
- [x] preliminary internal and external parent audit
- [x] construct finite-prime polarized irregular triples on actual `ell²` occupation carriers
- [ ] prove uniform cofinal polarization after unitary irregular factorization
- [ ] land the pre-divisor Xi conormal and all multiplicity jets
- [ ] prove strict Hermitian irregular purity
- [ ] dependency-closed RH proof
- [ ] unconditional Lean formalization of RH

## Log

- 2026-07-30 — Reinterpreted Wold boundary volume, Hellinger--Rees fracture, and multiple-Gamma
  scheme change as one reflection-odd irregular renormalization charge.  Proved the general
  bi-moderation locus `(4)`--`(9)`, isolated divisor/conormal distinction, rejected an
  over-strong regular-singular target, and froze `XI WOLD-POLARIZED IRREGULAR LANDING` as the exact
  RH-bearing source theorem.
- 2026-07-30 — Proved vacuum--anomaly reciprocity `(14a)`--`(14f)`: Wold boundary probability,
  Hellinger half-density, occupation-vector norm, Gamma first trace, and reflected irregular gauge
  are reciprocal records of one finite-source occupation line.  This identifies the missing
  completion as a projective direction plus its norm/determinant torsor.
- 2026-07-30 — Formalized vacuum--anomaly reciprocity in
  `formal/GaloisForLFunctions/HTGeometry/OccupationVacuumAnomalyReciprocity.lean`.
  `HTGeometry.finiteOccupation_vacuum_mul_mass` proves for every finite complex nome family in
  the open unit polydisc that vacuum amplitude times raw occupation mass is exactly one.  The same
  module now constructs the raw and normalized finite occupation half-densities as actual `ell²`
  vectors and proves their norm and vacuum-amplitude identities.
- 2026-07-30 — Formalized the complete finite-prime specialization in
  `formal/GaloisForLFunctions/RHTower/FinitePrimePolarizedIrregularTriple.lean`.
  `finitePrimePolarizedIrregularTriple_exact` proves simultaneously that the normalized
  occupation direction has squared norm one, its squared vacuum amplitude is the Wold boundary
  volume, the raw squared norm is the reciprocal boundary volume, and the reflected genus-one
  Gamma phase is the genus-zero phase multiplied by the exponential of centered charge times that
  raw squared norm.  Both modules pass direct Lean checking; the generic module also passes its
  targeted module build.  This closes finite-stage Step 1 only.  Cofinal polarization and
  source-defined Xi conormal landing remain open.
