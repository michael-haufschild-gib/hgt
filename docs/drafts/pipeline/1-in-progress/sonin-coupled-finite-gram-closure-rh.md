# Coupled all-prime Sonin finite Gram closure implies RH

- **ID:** sonin-coupled-finite-gram-closure-rh
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** top-down Lean-corpus synthesis
- **Statement:** Finite-block value closure of the normalized prime--Gamma Hankel matrix inside the coupled all-prime Sonin Gram family forces RH.

## Formal status

`[PROVED IN LEAN, CONDITIONAL]` The following chains are now formalized:

```text
coupled trace-moment convergence
  -> coupled finite Gram convergence
    -> coupled finite Gram closure
      -> integer-polynomial prime--Gamma trace-Hankel positivity
        -> RH
```

and

```text
coupled finite Gram convergence
  -> coupled finite Gram closure
    -> integer-polynomial prime--Gamma trace-Hankel positivity
      -> RH
```

and its shorter closure form

```text
coupled finite Gram closure -> RH.
```

The absolute normalization has now been removed.  Lean also proves the strictly weaker
projective chain

```text
positive rescaled coupled trace-moment convergence
  -> positive rescaled coupled Gram convergence
    -> projective finite Gram closure
      -> integer-polynomial prime--Gamma trace-Hankel positivity
        -> RH.
```

One positive scalar is shared by the whole finite block but may vary with the aperture and
cutoff.  Thus the analytic problem concerns the shape of the moment vector, not its degree-zero
normalization.

Lean now removes even that scalar sequence from the hypothesis.  The direct normalized-shape
chain is

```text
nonzero coupled all-prime source column C_a
  <-> strictly positive zeroth coupled energy
  + normalized coupled moment-ratio convergence for 1 <= k < 2N-1
    -> canonical projective scaling by m_0 / S_0(a)
      -> projective finite-moment coupling
        -> RH.
```

The degree-zero coordinate is an exact identity under the canonical scale, rather than a limit.
Lean also proves the exact non-degeneracy interface

```text
Re Tr(C_a† C_a) > 0 <-> C_a != 0.
```

Thus no independent sign estimate remains at degree zero.  Its input is the concrete positive
statement that the source-built all-prime column is nonzero.

`[SOURCE-FORMALIZED, UNVERIFIED]` The Kraus/Stinespring direct-sum reading localizes this remaining
nondegeneracy input exactly:

```text
C_a != 0
  <-> exists one prime-power channel alpha with R_{a,alpha} != 0.
```

The logarithmic Euler coefficient of every retained channel is nonzero, so weighted and
unweighted residual nondegeneracy are equivalent.  A constructor now turns one concrete residual
witness directly into `SoninCoupledNondegenerateAperture`.  The infinite all-prime column can no
longer hide or cancel a nonzero local channel; the open nondegeneracy problem is one-channel
operator nonvanishing.  The general master-effect identity `C†C = 0 <-> C = 0` also makes the same
local witness equivalent to nonvanishing of the coupled positive energy and to strict positivity
of its zeroth trace moment.

The finite approximants are whole Gram matrices of the Hilbert--Schmidt coordinate vectors of
`C_a (C_a† C_a)^n`.  Thus one aperture schedule at cutoff `N` couples all `N^2` matrix entries and
all coefficient tests simultaneously.  This is strictly more coherent than a separately chosen
scalar approximation for each polynomial.  Lean also identifies every encoded matrix entry
exactly with the coordinate-free Hilbert--Schmidt pairing of its two coupled power columns, so the
`ℓ²` realization has introduced no surrogate moment sequence.  More sharply, Lean proves the
exact Hankel collapse

```text
⟨C_a T_a^m, C_a T_a^n⟩_HS = Tr(T_a^(m+n+1)),   T_a = C_a† C_a.
```

Consequently, the apparent `N^2`-entry problem requires only the first `2N-1` coupled trace
moments along one aperture schedule.  Lean now also proves the exact degree-zero value relation

```text
Tr(C_a† C_a) = soninAllPrimeEnergyMoment(a, 0).
```

Thus the coupled and block-diagonal routes share the same scalar energy normalization.  Coupling
first changes the sequence at the second trace moment, where mixed prime-power words survive.
That change is now exact in Lean:

```text
Re Tr((C_a† C_a)^2)
  = Re soninAllPrimeEnergyMoment(a, 1) + mixedSecondInvariant(a),

mixedSecondInvariant(a)
  = sum_(alpha != beta) ||A_alpha A_beta†||_HS^2 >= 0.
```

Lean proves the load-bearing identification

```text
soninAllPrimeEnergyMoment(a, 1) = diagonalSecondMoment(a),
```

by realizing the old block-diagonal output energy, computing its exact diagonal blocks, and using
trace cyclicity.  The common-source coupling therefore raises the old second moment by an explicit
nonnegative off-diagonal prime-power interaction; it is not a relabelling of the old direct sum.
Moreover, every individual coupled trace moment is unconditionally real and nonnegative.  Even
indices are Hilbert--Schmidt norm squares of coupled power columns, and odd indices are
Hilbert--Schmidt norm squares of powers of `C_a† C_a`.  Hence no isolated moment sign can carry the
RH content: it lies in the simultaneous finite Hankel relations.

## Goal

Replace the block-diagonal Sonin moment curve, which deletes mixed prime words, by the canonical
coupled column operator.  Its energy is positive and its Gram entries retain every cross-prime
overlap.  Prove the scale-free source-pure chain

```text
finite prime--Gamma Hankel blocks
  lie in the closure of positively rescaled coupled Sonin Gram blocks
    -> every integer-polynomial prime--Gamma Hankel value is nonnegative
      -> RH.
```

The closure premise is a static value relation between two explicit source objects.  It contains
no Xi zero location, real-rootedness, anti-Herglotz sign, limiting divisor measure, or rectangular
subpower estimate.

## Named open core

`[OPEN CORE]` For every cutoff `N`, construct a positive aperture sequence `a_{N,j}>0` whose
coupled all-prime source columns `C_{a_{N,j}}` are nonzero—equivalently, at every selected
aperture exhibit one prime-power residual `R_{a_{N,j},alpha} != 0`—and for which

```text
Tr((C_a† C_a)^(k+1)) / Tr(C_a† C_a)
  -> normalizedPrimeArchMoment(k) / normalizedPrimeArchMoment(0),
  1 ≤ k < 2N-1.
```

Equivalently, prove that every finite normalized prime--Gamma moment-Hankel block is a cluster
point of the positively rescaled positive-aperture Gram blocks of the coupled Sonin column
operator.  Lean constructs the scale canonically as
`normalizedPrimeArchMoment(0) / Tr(C_a† C_a)` and proves that `k=0` then matches identically.
Thus neither an external scale sequence nor a degree-zero convergence assertion remains.  The
first nontrivial projective coordinate is the old degree-one moment plus the already formalized
nonnegative mixed second invariant, the sum of all off-diagonal prime-power cross-overlap
energies.  Exact unscaled convergence and explicit projective-scale convergence remain valid
stronger routes but are no longer the preferred open core.

### Prime-power identity-response route

`[SOURCE-FORMALIZED, UNVERIFIED]` Let

```text
L_a(D) = (1-Q_a) D Q_a - (1-Q_a^0) D Q_a^0,
Q_a^0 = 1-P_a-F_a.
```

Every dilation residual is exactly `L_a(D_p)`.  At the identity observable the actual projection
has zero boundary response, while the formal complement has the exact defect

```text
L_a(1) = P_a F_a + F_a P_a != 0.
```

The nonvanishing is source-pure: for self-adjoint idempotents the anticommutator vanishes exactly
when the transition channel `F_a P_a` vanishes, but the existing Shannon area law gives
`||F_a P_a||_HS^2 = 4 a^2 > 0`.  Hence `Q_a^0` is not idempotent at any positive aperture.
The generic `HTGeometry` sharpness law now records this without Sonin-specific algebra:

```text
IsIdempotentElem(1-P-Q) <-> QP = 0.
```

The response also has the single-correction factorization

```text
L_a(D) = (1-Q_a) D (Q_a-Q_a^0) - (Q_a-Q_a^0) D Q_a^0,
```

which replaces the two duplicated expansions previously used by the residual norm and
Hilbert--Schmidt estimates.

This does not by itself prove a prime-power residual nonzero.  The sharply named missing lemma is
an operator-tomography statement: the prime-power symmetric dilation observables must determine
the identity value of the continuous linear response `L_a`.  Any such theorem immediately forces
one local residual witness and discharges source nondegeneracy through the criterion above.
Slepian--Pollak time--frequency concentration supplies the physical cutoff geometry
([DOI 10.1002/j.1538-7305.1961.tb03976.x](https://doi.org/10.1002/j.1538-7305.1961.tb03976.x));
Kraus/Stinespring supplies the channel/effect reading.

`[ROUTE RETIRED]` Operator-norm tomography cannot supply the missing lemma.  The formal response
map is norm-continuous, but every finite prime-power dilation sum is a trigonometric polynomial
with only nonzero prime-log frequencies.  Its invariant Bohr mean is zero, whereas the identity
has Bohr mean one.  Since the Bohr mean is bounded in the uniform norm, the identity is not in the
operator-norm/uniform closed span of those observables.  This is the same zero-frequency
separation already proved for bounded prime screens in
`prime-screen-bounded-observable-almost-periodicity.md`; norm continuity therefore does not turn
the nonzero identity response into a prime-power witness.

`[CONJECTURE]` A surviving tomography theorem would have to use a weaker strong- or weak-operator
topology on controlled spectral packets, prove that the prime-power symmetric dilation
observables determine the identity there, and prove the required packetwise continuity of
`L_a`.  The current corpus contains no such Sonin operator-topology interface.  No completeness
claim is promoted without those three proofs.

## Non-redressing audit

- The premise is defined before the Xi divisor is selected.
- Each approximating block is unconditionally a Gram matrix of explicit prime-power residuals.
- The coupled operator retains mixed prime words erased by the earlier direct-sum assembly.
- The premise is stronger than the resulting Hankel sign and is not defined as a positivity cone.
- `[CONJECTURE]` The coupled family has a source asymptotic matching the prime--Gamma blocks.
- `[NOVELTY UNVERIFIED]` No scientific novelty claim is made for the conditional transfer theorem.

## Gates

- [x] 0 -> 1 in-progress: source-pure finite-block closure and exact target identified
- [ ] 1 -> 2 fully-proven: prove the analytic coupled-source closure
- [ ] 2 -> 3 formalized: unconditional closure theorem and RH capstone
- [ ] 3 -> 4 publication-ready: standalone proof and literature audit

## Approach

1. Use the coordinate form of the canonical all-prime column `C_a`.
2. Form `T_a=C_a^*C_a` and the Hilbert--Schmidt Gram vectors `C_a T_a^n`.
3. Prove every finite coefficient quadratic form of their Gram block is a squared
   Hilbert--Schmidt norm.
4. Pull this closed nonnegative half-space through finite-block closure.
5. Allow one positive global scale per finite block; homogeneity preserves every source quadratic
   sign while eliminating absolute energy normalization.
6. Prove one concrete prime-power residual channel is nonzero at every selected aperture.  The
   exact direct-sum criterion then proves the source column and its zeroth trace energy are
   nonzero; normalize every source moment by that energy, and use the canonical target/source
   zeroth-moment quotient to reconstruct the projective scale.
7. Identify the target quadratic form with the existing prime--Gamma trace-Hankel value and use
   the countable criterion for RH.

The formal theorem surface is
`RHTower/SoninCoupledPrimeArchGramTransfer.lean`.  The remaining open core is not hidden by that
surface: it is exactly the analytic construction of the positive-aperture schedules in
`SoninCoupledPrimeArchFiniteMomentCoupling`; the Hankel identity then gives
`SoninCoupledPrimeArchFiniteGramCoupling`, and hence the matrix closure in
`SoninCoupledPrimeArchFiniteGramClosure`.  The preferred weaker interfaces are
`SoninCoupledPrimeArchProjectiveFiniteMomentCoupling` and
`SoninCoupledPrimeArchProjectiveFiniteGramClosure`; the preferred explicit aperture-only interface
is `SoninCoupledPrimeArchMomentRatioCoupling`.  Theorems
`soninAllPrimeCoupledTraceMoment_zero_eq_column_hsNormSq` and
`soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero` identify its degree-zero premise
with ordinary nonvanishing of the explicit source column.  The source-only declarations
`soninAllPrimeColumnCoordinateOperator_ne_zero_iff_exists_primePowerResidual_ne_zero` and
`soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_exists_primePowerResidual_ne_zero`, together with
`soninCoupledNondegenerateApertureOfPrimePowerResidual`, reduce that premise further to one local
residual witness; they remain uncompiled under the current no-build constraint.

## Log

- 2026-07-13 — created after rejecting arbitrary theta autocorrelation factorization as a
  spectral-square restatement and rejecting global Pólya convexity by the forced concavity at the
  center of every nonconstant smooth even decreasing density.
- 2026-07-13 — formalized the conditional finite-matrix closure and sequential-coupling chains to
  RH.  The proof uses only unconditional Hilbert--Schmidt Gram positivity, closedness of each finite
  real quadratic half-space, the exact prime--Gamma/Xi centered-moment identity, and the existing
  countable integer-polynomial criterion.
- 2026-07-13 — proved the exact coupled Hankel identity.  This reduces the analytic target from
  `N^2` generic matrix entries to `2N-1` trace moments while retaining all mixed prime words.
- 2026-07-13 — proved the degree-zero equality with the old residual energy and the exact
  degree-one split into the diagonal contribution plus the nonnegative mixed overlap invariant.
- 2026-07-13 — proved every individual coupled trace moment is a Hilbert--Schmidt norm square and
  proved the diagonal degree-one contribution is exactly the older block-diagonal Sonin moment.
- 2026-07-13 — weakened exact moment matching to projective matching by allowing one positive
  scale per finite source block; this removes the absolute degree-zero normalization condition.
- 2026-07-13 — eliminated the auxiliary projective scale sequence from the explicit theorem
  interface.  Strict positivity of the zeroth coupled energy supplies the canonical scale
  `normalizedPrimeArchMoment(0) / S_0(a)`; Lean proves degree-zero matching identically, so the
  remaining aperture-only hypothesis is convergence of normalized moment ratios in degrees
  `1 <= k < 2N-1`.
- 2026-07-13 — discharged the apparent degree-zero sign input to concrete source non-degeneracy:
  Lean proves `Re S_0(a) > 0` exactly when the coupled all-prime column `C_a` is nonzero.  The open
  core is now column nonvanishing plus finite normalized moment-ratio convergence.

## Per-test canonical scalar weakening

`[PROVED IN LEAN]` Simultaneous finite-block convergence is not required by the countable
integer-polynomial criterion.  Let

```text
S_0(a) = Re Tr(C_a† C_a),
λ_can(a) = normalizedPrimeArchMoment(0) / S_0(a),
Q_a(P) = λ_can(a) · c(P)^T G_a c(P),
```

where `C_a` is the coupled all-prime Sonin column, `G_a` is its coupled moment Gram block at the
finite coefficient support of `P`, and `C_a ≠ 0`.  Lean proves the strictly weaker chain

```text
for every P ∈ ℤ[X], independently,
  primeArchSourceTraceHankel(P) ∈ closure {Q_a(P) : a > 0 and C_a ≠ 0}
    -> prime--Gamma integer-polynomial Hankel positivity
      -> RH.
```

A sequential interface allows a different nondegenerate aperture schedule for every `P`.  It asks
for convergence of one real scalar per test, not `2N-1` normalized moments along one common
cutoff schedule.  The normalizing scale is forced by `a`; allowing an arbitrary positive scale
per polynomial was rejected because any single strictly positive source value would then generate
the whole positive ray and the premise would collapse to the target sign criterion.

`[OPEN CORE]` Prove this canonical per-test value relation directly from the coupled
prime-power/Gamma source formulas.  This is now the weakest live coupled-Sonin interface.  It may
be attacked polynomial by polynomial and retains the mixed-prime words absent from the older
block-diagonal per-test Sonin locus.

The formal declarations are
`SoninCoupledPrimeArchPerTestNormalizedValueClosure`,
`SoninCoupledPrimeArchPerTestNormalizedValueCoupling`, and the two RH capstones with the same name
suffix in `RHTower/SoninCoupledPrimeArchGramTransfer.lean`.

- 2026-07-13 — reduced the simultaneous normalized moment-ratio problem to a canonical scalar
  value-closure problem for each integer polynomial separately.  Exact module build and axiom
  audit passed; the capstones use only `propext`, `Classical.choice`, and `Quot.sound`.

### Exact source-norm form of the scalar target

`[PROVED IN LEAN]` If `P` has real coefficient vector `c(P)` and

```text
V_a(P) = Σ_j c_j(P) · C_a (C_a† C_a)^j,
```

viewed in the Hilbert--Schmidt coordinate space, then

```text
c(P)^T G_a c(P) = ‖V_a(P)‖²,
normalizedValue_a(P)
  = normalizedPrimeArchMoment(0) / Re S_0(a) · ‖V_a(P)‖².
```

Thus the new open core is an equality/cluster relation between the prime--Gamma polynomial value
and a canonically normalized squared norm of one explicit polynomial in the common-source energy
operator.  No matrix surrogate remains in the analytic target.

- 2026-07-13 — exposed the canonical per-test value as the exact squared norm of the polynomial
  coupled power-column vector; the exact module build passed.

### Verification checkpoint

`[PROVED IN LEAN]` The exact source-norm identities and both per-test RH capstones build in the
project target.  Axiom inspection reports only `propext`, `Classical.choice`, and `Quot.sound` for
all four declarations.  The repository formal lint gate passes with no proof-debt findings.

The fresh-corpus comparison found no stronger automatic producer.  Positive moment measures,
Stieltjes--Pick transforms, Hedenmalm one-Cauchy signs, Lee--Yang localizations, and far-right
moving Hankel anchors become RH-bearing only after an orientation, representation, convergence,
or zero-winding input is supplied.  None currently implies the canonical coupled source-norm
cluster relation.  The open core therefore remains the polynomial-by-polynomial source comparison,
not construction of another positive carrier.

- 2026-07-13 — exact target build, axiom audit, formal lint, and generated-index refresh passed;
  fresh-corpus alternatives were rejected when their producer premise was RH-equivalent or belonged
  to an already active route.

## One-sided variational reduction

`[PROVED IN LEAN]` Exact cluster matching is stronger than the positivity transfer uses.  Define

```text
G_a(P) = normalizedPrimeArchMoment(0) / Re S_0(a) * ||V_a(P)||^2,
Q(P)   = Re primeArchSourceTraceHankel(P).
```

Every `G_a(P)` is nonnegative.  Therefore the following one-sided relation already suffices:

```text
for every P in Z[X] and every epsilon > 0,
  there exists a > 0 with C_a != 0 and G_a(P) <= Q(P) + epsilon.
```

Indeed, if `Q(P) < 0`, choose `epsilon = -Q(P)/2`.  The displayed inequality would place the
nonnegative value `G_a(P)` strictly below zero.  Hence every `Q(P)` is nonnegative, and the existing
countable prime--Gamma Hankel criterion gives RH.

This is strictly weaker as a theorem interface than equality or cluster convergence: it asks only
that

```text
inf_{a > 0, C_a != 0} G_a(P) <= Q(P)
```

in epsilon form, separately for each integer polynomial.  No common aperture schedule, lower
approximation, moment convergence, or finite-block convergence remains.  Lean also proves that the
previous value-closure hypothesis implies this variational hypothesis.

`[OPEN CORE]` Prove the one-sided variational comparison directly from the coupled prime-power and
Gamma source formulas.  The useful target is now an upper-bound construction, not an asymptotic
identification: for a fixed polynomial `P`, choose an aperture whose canonically normalized Sonin
polynomial energy is no larger than the completed prime--Gamma quadratic value, up to arbitrary
positive error.

The formal declarations are
`SoninCoupledPrimeArchPerTestVariationalUpperBound`,
`soninCoupledPrimeArchPerTestVariationalUpperBound_of_valueClosure`,
`primeArchSourceTraceHankelIntNonnegative_of_soninCoupledPerTestVariationalUpperBound`, and
`riemannHypothesis_of_soninCoupledPrimeArchPerTestVariationalUpperBound` in
`RHTower/SoninCoupledPrimeArchGramTransfer.lean`.

The same sweep retired three tempting substitutions.  The fixed semilocal trace normalization is
false by the proved bounded-response versus growing-log-scale obstruction.  Gamma-damped Cauchy
packet energy is a genuine positive domain repair but is not the completed Gamma Hankel kernel.
The two-point first-divided numerical sector is a reflected-zero sign test and hence only a
re-expression of the orientation conclusion.

- 2026-07-13 — replaced exact per-test value closure by the one-sided variational upper comparison;
  the exact Lean module build passed.

### Shifted-sector restriction of the open comparison

`[PROVED ON PAPER]` The card
`prime-arch-shifted-sector-circle-valuation-cone.md` removes an explicit family of tests from the
one-sided comparison.  Write every nonzero integer polynomial canonically as `P=X^v q`, with
`q(0)=b_0!=0`.  The endpoint radius and one-eighty-fourth reciprocal-square sector prove directly
that

```text
v <= 5 and
224*sum_(n>=1)b_n^2 <= (1960-13*(2v+1)^2)*b_0^2
  -> Q(P)>=0.
```

Let `R_sector` be the complementary integer-polynomial family.  It is enough to prove the
variational upper comparison only for `P in R_sector`: nonnegativity of the Sonin value excludes a
negative `Q(P)` there, while the displayed source theorem handles every omitted test.  Thus the
live target is strictly smaller than `SoninCoupledPrimeArchPerTestVariationalUpperBound` and retains
the same non-sign source interface.

`[OPEN CORE]` Prove the aperture Rayleigh upper bound only on `R_sector`.  High-valuation tests and
low-valuation polynomials whose post-valuation coefficient tail dominates their leading
coefficient remain.  No comparison theorem is required inside the discharged sector cones.

### Quotient-free Rayleigh form

`[PROVED IN LEAN]` The variational comparison is equivalent to the cross-multiplied inequality

```text
normalizedPrimeArchMoment(0) * ||V_a(P)||^2
  <= (Q(P) + epsilon) * Re S_0(a).
```

The nondegeneracy condition `C_a != 0` makes `Re S_0(a) > 0`, so division by the zeroth energy
recovers the normalized formulation exactly.  This is the preferred analytic target: it is a
finite-polynomial Rayleigh upper bound between two explicit coupled-source squared energies and
contains no quotient or limiting equality.  Lean exposes it as
`SoninCoupledPrimeArchPerTestRayleighUpperBound` and proves both its equivalence with the
variational interface and its direct RH capstone.

### Variational verification checkpoint

`[PROVED IN LEAN]` The exact module build, project-module build, axiom inspection, formal lint, and
generated-index refresh pass for the variational and Rayleigh capstones.  Axiom inspection reports
only `propext`, `Classical.choice`, and `Quot.sound`.
