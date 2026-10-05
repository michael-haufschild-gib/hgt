# Mixed spectral formation, atomic retention, continuous escape, and closed-range law

- **ID:** ULF-OISM-6
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** ULF-OISM-4 and ULF-OISM-5
- **Statement:** For every separable unitary phase representation, Hilbert--Schmidt Cesaro formation
  retains exactly the equal-eigenvalue atomic blocks and erases every mixed or continuous block.
  For a positive trace-class packet, trace-norm formation converges exactly when the packet has zero
  continuous spectral mass; otherwise the continuous mass is an exact lower bound for the missing
  trace-norm convergence.  The conjugation transgression has closed Hilbert--Schmidt range exactly
  when the unitary has finite spectrum.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [ROUTE-INDEPENDENT]
  [COMPLETE MIXED-SPECTRUM CLASSIFICATION] [ATOMIC RETENTION]
  [CONTINUOUS TRACE ESCAPE] [CLOSED-RANGE IFF FINITE SPECTRUM]
  [FUNCTIONAL-EQUATION NEUTRAL] [LEAN-PROVED] [NOT RH]

## 1. Purpose

ULF-OISM-4 proves the pure-point resonance law.  ULF-OISM-5 proves the atomless escape law.  A
source representation need not be purely one or the other.  The correct invariant is the atomic
and continuous spectral decomposition of the unitary phase action.

This card closes that dichotomy.  It gives one complete formation law for arbitrary spectral type
and identifies the escaped trace exactly.

## 2. Spectral decomposition

Let `H` be a separable complex Hilbert space and let `U:H->H` be unitary.  For each unit-circle
eigenvalue `lambda`, let

```text
H_lambda=ker(U-lambda),
P_lambda=orthogonal projection onto H_lambda.
```

Separability makes the set `A(U)` of eigenvalues countable.  Define

```text
H_at = orthogonal direct sum_(lambda in A(U)) H_lambda,
P_at = sum_lambda P_lambda,
H_c  = H_at^perp,
P_c  = 1-P_at.
```

The restriction of `U` to `H_c` has no eigenvectors.

On the Hilbert space `S_2(H)` define

```text
alpha(T)=U* T U,
delta(T)=T-alpha(T).
```

Define the atomic pinching

\[
 \boxed{
 \Pi_{\rm at}(T)=\sum_{\lambda\in A(U)}P_\lambda T P_\lambda.}
\tag{MSF.1}
\]

For `T in S_2`, the sum converges in Hilbert--Schmidt norm because its terms are orthogonal
compressions.  For positive trace-class `T`, it also converges in trace norm.

## 3. Fixed Hilbert--Schmidt geometry

### Lemma 3.1 -- a compact commuting operator vanishes on the continuous subspace

If a compact operator `K:H_c->H_c` commutes with `U|H_c`, then `K=0`.

#### Proof

Commutation with the normal operator `U` implies commutation with its adjoint.  Hence `K*K` is a
positive compact operator commuting with `U|H_c`.  If `K!=0`, then `K*K` has a positive eigenvalue
whose eigenspace `E` is nonzero and finite dimensional.  Commutation makes `E` invariant under
`U`.  A unitary on a nonzero finite-dimensional complex space has an eigenvector.  This would give
an eigenvector of `U` in `H_c`, contradicting the definition of the continuous subspace. QED.

### Theorem 3.2 -- fixed ideal equals atomic equal-phase blocks

\[
 \boxed{
 \ker\delta
  =\left\{\bigoplus_{\lambda\in A(U)}T_\lambda:
        T_\lambda\in S_2(H_\lambda),\ 
        \sum_\lambda\|T_\lambda\|_2^2<\infty\right\}.}
\tag{MSF.2}
\]

The orthogonal projection of `S_2(H)` onto this fixed space is exactly `Pi_at`.

#### Proof

If `T` commutes with `U`, then it commutes with every spectral projection of `U`.  Thus it preserves
`H_at`, `H_c`, and every eigenspace `H_lambda`; all cross blocks vanish.  Its restriction to `H_c`
is Hilbert--Schmidt, hence compact, and Lemma 3.1 makes it zero.  The remaining restrictions are the
equal-eigenvalue blocks displayed in `(MSF.2)`.

Conversely, every such block sum commutes with `U`.  Orthogonality of the blocks gives the stated
Hilbert--Schmidt summability and identifies `(MSF.1)` as the orthogonal projection. QED.

### Corollary 3.3 -- complete Hilbert--Schmidt formation law

For

\[
 M_N(T)=\frac1N\sum_{n=0}^{N-1}U^{-n}TU^n,
\tag{MSF.3}
\]

the mean ergodic theorem and Theorem 3.2 give

\[
 \boxed{
 M_N(T)\longrightarrow\Pi_{\rm at}(T)
 \quad\text{in }S_2.}
\tag{MSF.4}
\]

The pure-point theorem ULF-OISM-4 is the case `P_at=1`.  The atomless theorem ULF-OISM-5 is the
case `P_at=0`.

## 4. Exact escaped trace mass

Let `T>=0` be trace class.  Define its atomic and continuous masses

\[
 m_{\rm at}(T)=\operatorname{tr}(TP_{\rm at}),
 \qquad
 m_c(T)=\operatorname{tr}(TP_c).
\tag{MSF.5}
\]

They are nonnegative and add to `tr(T)`.

### Theorem 4.1 -- atomic trace retained by the Hilbert--Schmidt limit

\[
 \boxed{
 \operatorname{tr}\Pi_{\rm at}(T)=m_{\rm at}(T),
 \qquad
 \operatorname{tr}M_N(T)=\operatorname{tr}T.}
\tag{MSF.6}
\]

Therefore

\[
 \boxed{
 \operatorname{tr}\bigl(M_N(T)-\Pi_{\rm at}(T)\bigr)=m_c(T).}
\tag{MSF.7}
\]

#### Proof

The positive blocks `P_lambda T P_lambda` have total trace at most `tr(T)`, so their sum converges
in trace class.  Countable trace additivity gives

\[
 \operatorname{tr}\Pi_{\rm at}(T)
 =\sum_\lambda\operatorname{tr}(P_\lambda T P_\lambda)
 =\operatorname{tr}(TP_{\rm at}).
\]

Unitary conjugation preserves trace, hence so does its Cesaro average.  Subtraction proves
`(MSF.7)`. QED.

### Corollary 4.2 -- quantitative ideal mismatch

For every `N`,

\[
 \boxed{
 \|M_N(T)-\Pi_{\rm at}(T)\|_1\ge m_c(T).}
\tag{MSF.8}
\]

Indeed, the trace norm dominates the absolute value of the trace.  Thus continuous spectral mass
is not merely “lost” in the Hilbert--Schmidt limit; it is the exact conserved charge obstructing
trace-norm convergence.

## 5. Trace-norm convergence classification

### Theorem 5.1 -- trace formation converges if and only if continuous mass vanishes

For positive trace-class `T`,

\[
 \boxed{
 M_N(T)\longrightarrow\Pi_{\rm at}(T)\text{ in }S_1
 \iff m_c(T)=0.}
\tag{MSF.9}
\]

#### Proof: necessity

If `M_N(T)` converges in trace norm, then it converges in Hilbert--Schmidt norm to the same limit.
Equation `(MSF.4)` makes that limit `Pi_at(T)`.  Trace continuity and `(MSF.6)` then give

```text
tr(T)=tr(Pi_at(T))=m_at(T),
```

so `m_c(T)=0`.  Equivalently, `(MSF.8)` already forbids convergence when `m_c(T)>0`.

#### Proof: sufficiency

If `m_c(T)=0`, then

\[
 \|T^{1/2}P_c\|_2^2=\operatorname{tr}(P_cTP_c)=0.
\]

Hence `T^(1/2)P_c=0`, and positivity gives

```text
T=P_at T P_at.
```

Choose finite subsets `F` of `A(U)` increasing to all eigenvalues and put

```text
P_F=sum_(lambda in F)P_lambda,
T_F=P_F T P_F.
```

Strong convergence `P_F->P_at` and trace-class compactness give `||T-T_F||_1->0`.  For fixed
finite `F`, only finitely many phase ratios occur, so geometric averaging gives

\[
 M_N(T_F)\longrightarrow\sum_{\lambda\in F}P_\lambda T_FP_\lambda
 \quad\text{in }S_1.
\]

Both Cesaro averaging and atomic pinching are trace-norm contractions.  Approximate `T` by `T_F`,
apply the finite result, and let `F` increase.  This proves `(MSF.9)`. QED.

### Corollary 5.2 -- spectral type is operationally recoverable from ideal convergence

For positive packets, the scalar

```text
m_c(T)
```

is exactly the obstruction to promoting Hilbert--Schmidt formation convergence to trace-norm
formation convergence.  It can be recovered as

\[
 \boxed{
 m_c(T)=\operatorname{tr}T-\operatorname{tr}\Pi_{\rm at}(T).}
\tag{MSF.10}
\]

Thus the ideal mismatch carries spectral-type information erased by the `S_2` limit itself.

## 6. Closed-range classification for arbitrary unitary spectrum

### Theorem 6.1 -- global transgression is proper exactly for finite spectrum

\[
 \boxed{
 \operatorname{ran}(1-\operatorname{Ad}_U)\text{ is closed on }S_2(H)
 \iff \sigma(U)\text{ is finite}.}
\tag{MSF.11}
\]

#### Proof: finite spectrum

If

```text
sigma(U)={lambda_1,...,lambda_r},
```

then

```text
S_2(H)=orthogonal direct sum_(i,j) P_i S_2(H) P_j.
```

On the `(i,j)` block, `delta` is scalar multiplication by

```text
1-conj(lambda_i)lambda_j.
```

It vanishes on equal phases and is bounded below on all other blocks by the minimum of a finite
nonempty set of positive numbers.  Hence it has closed range.

#### Proof: infinite spectrum

An infinite compact subset of the unit circle contains distinct pairs

```text
lambda_n,mu_n in sigma(U),      |lambda_n-mu_n|->0.
```

Choose disjoint spectral arcs `A_n,B_n` around these points, with diameters tending to zero and
nonzero spectral projections.  Take unit vectors

```text
x_n in E_U(A_n)H,      y_n in E_U(B_n)H,
```

and let `R_n=|x_n><y_n|`.  Then `||R_n||_2=1`.  Since the arcs are disjoint, `R_n` is orthogonal to
the fixed Hilbert--Schmidt space: a commuting operator has no block from `B_n` to `A_n`.

Spectral localization gives

```text
||U x_n-lambda_n x_n|| -> 0,
||U y_n-mu_n y_n||     -> 0.
```

The rank-one norm identity then yields

```text
||delta(R_n)||_2
 <= |1-conj(lambda_n)mu_n| + o(1) -> 0.
```

Thus `delta` has no positive lower bound on the orthogonal complement of its kernel.  The Hilbert
closed-range theorem implies that its range is not closed. QED.

### Corollary 6.2 -- spectral richness forces global ill-conditioning

Every finite spectral aperture has a bounded inverse on its off-resonant blocks.  If the full
spectrum is infinite, the best inverse norms over increasing apertures diverge.  This holds for
pure point, singular continuous, absolutely continuous, and mixed spectrum alike.

Hence closed-range failure is caused by infinite spectral richness, not specifically by
atomlessness.  Atomlessness decides the survivor and trace escape; infinitude decides global
transgression properness.

## 7. Functional-equation neutrality

Replacing `U` by `U*` conjugates every spectral value and leaves every spectral projection
unchanged.  Therefore it preserves:

1. `H_at`, `H_c`, `P_at`, and `P_c`;
2. the pinching `Pi_at`;
3. atomic and continuous trace masses;
4. the trace-norm convergence criterion `(MSF.9)`;
5. finiteness of the spectrum;
6. closedness of the transgression range.

The functional equation is again information-neutral: it reverses phase orientation without
changing the mixed-spectral formation geometry.  A common exact-recovery lift preserves the same
information distinctions.

## 8. Field laws and leverage

The mixed theorem yields a complete spectral formation table.

| source spectral feature | formed `S_2` law | formed `S_1` law |
|---|---|---|
| finite atomic spectrum | closed transgression; atomic pinching | trace-norm convergence |
| infinite pure point | nonclosed transgression; atomic pinching | trace-norm convergence |
| atomless continuous | dense nonclosed transgression; zero limit | no convergence for nonzero state |
| mixed atomic/continuous | nonclosed transgression; atomic pinching | convergence iff continuous mass zero |

This separates three quantities that the corpus often merges:

1. **phase cardinality** controls transgression properness;
2. **spectral type** controls the surviving fixed ideal;
3. **packet spectral mass** controls trace-class convergence.

The theorem provides unconditional leverage on any route obstruction realized by a unitary phase
packet: once its source spectral type and packet mass are known, all three global questions are
settled without further route-specific estimates.

## 9. Hostile boundaries

1. **No RH conclusion.** The source still must construct its unitary phase representation before
   zero specialization.
2. **Positive packets only in Theorem 5.1.** For general trace-class operators, zero continuous
   diagonal trace does not control cross blocks.
3. **Separability matters.** It makes the point spectrum countable and the block sum manageable.
4. **`S_2` is load-bearing.** Conjugation is unitary there, enabling exact mean-ergodic projection.
5. **Classical ingredients.** Spectral decomposition, compact commutant arguments, mean ergodicity,
   and trace ideals are classical.  The field contribution is their exact formation classification
   and use as a universal source test.
6. **Finite spectrum is stronger than pure point.** Infinite pure point retains all trace mass but
   still has nonclosed transgression.
7. **No claim that spectral type causes HT.** A separate source theorem must connect differential
   independence to spectral richness.

Corpus search found recurrence theorems for countable pure-point packets, spectral-type moment
fibers, finite pinching, and route-specific dephasing.  None found states `(MSF.2)`, `(MSF.9)`, and
`(MSF.11)` as one mixed-spectrum formation classification.

## 10. Lean status

Fully formalized, unconditionally: see the Lean certificate below.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.UnitaryAtomicDecomposition`, `GaloisForLFunctions.HTGeometry.MixedSpectralFormation`, `GaloisForLFunctions.HTGeometry.MixedSpectralTraceEscape`, `GaloisForLFunctions.HTGeometry.UnitarySpectrumClosedRange`, `GaloisForLFunctions.HTGeometry.UnitaryInversionNeutrality`, `GaloisForLFunctions.HTGeometry.MixedSpectralPositivityBoundary`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.UnitaryAtomicDecomposition` (eigenspaces, countable point spectrum,
atomic/continuous subspaces, compact commutant on `H_c`, adapted Hilbert basis),
`GaloisForLFunctions.HTGeometry.MixedSpectralFormation` (fixed Hilbert–Schmidt geometry, atomic pinching,
mean-ergodic formation law), `GaloisForLFunctions.HTGeometry.MixedSpectralTraceEscape` (masses, retention,
trace-norm classification), `GaloisForLFunctions.HTGeometry.UnitarySpectrumClosedRange` (approximate point
spectrum of a unitary, closed-range law, spectral formation table),
`GaloisForLFunctions.HTGeometry.UnitaryInversionNeutrality` (`U ↦ U*`) and
`GaloisForLFunctions.HTGeometry.MixedSpectralPositivityBoundary` (the positivity boundary of Theorem 5.1).
Corpus inputs: `hsConj`, `hsCesaro`, `hsColumns`, `columnOperator`, `columnConj`, `HasNoEigenvectors`,
`HasApproxEigenvectors`, `eq_zero_of_isCompactOperator_of_comm`, `eq_zero_of_hsConj_eq`, `hsConj_rankOne`,
`rankOne_smul_unimodular` (ULF-OISM-5); `cesaroCoeff`, `tendsto_cesaroCoeff`, `conj_mul_eq_one_iff`,
`exists_ne_norm_sub_lt_of_infinite` (ULF-OISM-4); `orthoAverage`, `traceNorm_orthoAverage`,
`hsCesaro_rankOne_eq_orthoAverage`, `adjoint_unitaryCLM`, `isPositive_hsConj`, `opTrace_hsConj`
(ULF-OISM-5); `hasTransverseLowerBound_iff_isClosed_range`, `RHTower.traceClassRoot`,
`RHTower.rectTraceNorm_comp_le_hsNorm_mul_hsNorm_unrestricted`, `RHTower.traceNorm_eq_re_opTrace_of_isPositive`,
`RHTower.norm_opTrace_le_traceNorm`, `RHTower.traceNorm_comp_left_le`, `RHTower.traceNorm_eq_zero_iff`,
`memSchattenClass_one_sum`, `lpReindex`, `lpDiag`, `memSchattenClass_one_rankOne`, `opTrace_rankOne`,
`starProjection_congr`, `ext_hilbertBasis`; mathlib mean ergodic theorem, continuous functional calculus,
`spectrum.nonempty`, `OrthogonalFamily.norm_sum`, polarization `inner_eq_sum_norm_sq_div_four`.

| Claim | Lean declaration |
|-|-|
| §2 `H_λ = ker(U - λ)`, `P_λ`, `A(U)` countable (separable `H`), eigenvalues unimodular, eigenspaces orthogonal | `unitaryEigenspace`, `mem_unitaryEigenspace`, `eigenproj`, `unitaryPointSpectrum`, `countable_unitaryPointSpectrum`, `norm_eq_one_of_mem_pointSpectrum`, `unitaryEigenspace_isOrtho` |
| §2 `H_at`, `P_at`, `H_c = H_atᗮ`, `P_c`; `P_at + P_c = 1`; `U∣H_c` has no eigenvectors | `atomicSubspace`, `atomproj`, `continuousSubspace`, `contproj`, `atomproj_add_contproj`, `continuousRestrict`, `hasNoEigenvectors_continuousRestrict` |
| §2 adapted Hilbert basis (eigenbases of every `H_λ` and a basis of `H_c`) | `adaptedVec`, `orthonormal_adaptedVec`, `adaptedVec_dense`, `adaptedBasis`, `eigenprojection_adaptedVec`, `continuousProjection_adaptedVec` |
| (MSF.1) `Π_at(T) = ∑_λ P_λ T P_λ`, Hilbert–Schmidt convergence of the block sums | `atomicPinch`, `atomicPinch_apply`, `isHilbertSchmidt_atomicPinch`, `atomicPinch_sub_sum_apply`, `tendsto_hsNorm_atomicPinch_sub_sum` |
| (MSF.1) trace-norm convergence of the block sums for positive trace-class `T` | `tendsto_traceNorm_atomicPinch_sub_sum`, `atomicPinch_sub_aperture_eq`, `aperture_tail_traceClass`, `inner_aperture_tail_adaptedVec` |
| Lemma 3.1 compact operator commuting with `U∣H_c` vanishes | `eq_zero_of_compact_comm_continuousRestrict`, `compact_comm_apply_continuous_eq_zero`, `compact_comm_continuousProjection` |
| Theorem 3.2, (MSF.2) fixed ideal = equal-eigenvalue blocks (kills and avoids `H_c`, commutes with every `P_λ`) | `hsConj_eq_iff`, `commute_eigenprojection`, `commute_mapsTo_eigenspace`, `hsConj_atomicPinch`, `atomicPinch_eq_self_of_fixed` |
| Theorem 3.2 `Π_at` is the orthogonal projection onto `ker δ` | `inner_sub_atomicPinch_fixed`, `fixedColumns`, `atomicPinch_eq_starProjection` |
| Corollary 3.3, (MSF.3)–(MSF.4) `M_N(T) → Π_at(T)` in `S₂` | `hsCesaro`, `tendsto_hsNorm_hsCesaro_sub_atomicPinch` |
| (MSF.5) `m_at(T) = tr(T P_at)`, `m_c(T) = tr(T P_c)`, nonnegative, sum `tr T` | `atomicMass`, `continuousMass`, `atomicMass_eq_tsum`, `continuousMass_eq_tsum`, `atomicMass_nonneg`, `continuousMass_nonneg`, `atomicMass_add_continuousMass` |
| Theorem 4.1, (MSF.6) `Π_at(T)` positive trace class with `tr Π_at(T) = m_at(T)`; `tr M_N(T) = tr T` | `isPositive_atomicPinch`, `summable_atomicDiag`, `atomicPinch_traceClass`, `memSchattenClass_one_hsCesaro`, `opTrace_hsCesaro` |
| (MSF.7) `tr(M_N(T) - Π_at(T)) = m_c(T)` | `opTrace_hsCesaro_sub_atomicPinch` |
| Corollary 4.2, (MSF.8) `‖M_N(T) - Π_at(T)‖₁ ≥ m_c(T)` | `norm_continuousMass_le_traceNorm` |
| Theorem 5.1, (MSF.9) `M_N(T) → Π_at(T)` in `S₁` iff `m_c(T) = 0` (positive trace-class `T`) | `tendsto_traceNorm_iff_continuousMass_eq_zero` |
| Theorem 5.1 necessity | `continuousMass_eq_zero_of_tendsto` |
| Theorem 5.1 sufficiency: `T^{1/2} P_c = 0`; truncation `‖T - Q_F T Q_F‖₁ → 0`; finite apertures converge (phase-ratio Cesàro coefficients); `Π_at` tail | `sqrtOp_adaptedVec_inr`, `tendsto_hsNormSq_sqrtOp_tail`, `traceNorm_sub_aperture_le`, `hsConj_block`, `hsCesaro_block`, `atomicPinch_aperture`, `tendsto_traceNorm_aperture`, `traceNorm_atomicPinch_sub_aperture`, `tendsto_traceNorm_of_continuousMass_eq_zero` |
| Corollary 5.2, (MSF.10) `m_c(T) = tr T - tr Π_at(T)` | `continuousMass_eq_sub` |
| Theorem 6.1, (MSF.11) `ran(1 - Ad_U)` closed on `S₂(H)` iff `σ(U)` finite (any Hilbert basis column model) | `isClosed_range_columnTransgression_iff_finite_spectrum` |
| Theorem 6.1: closed range = transverse lower bound on `ker δᗮ` = operators with `Π_at = 0`; basis-independent column inner product | `isClosed_range_columnTransgression_iff`, `inner_hsColumns_eq`, `inner_hsColumns_fixed`, `hsColumns_mem_ker_orthogonal`, `atomicPinch_columnOperator_eq_zero` |
| Theorem 6.1, finite spectrum: `σ(U)` finite iff `A(U)` finite and `H_c = 0` (spectral indicators by continuous functional calculus; off `A(U)`, `z - U` bounded below) | `spectrum_finite_iff`, `continuousSubspace_eq_bot_of_finite`, `spectrum_subset_pointSpectrum`, `mem_spectrum_of_mem_pointSpectrum`, `isStarNormal_unitaryCLM`, `not_mem_spectrum_of_boundedBelow` |
| Theorem 6.1, finite spectrum: on the block `(λ, μ)` `δ` is the scalar `1 - λ̄μ`, bounded below by the minimal gap | `exists_lowerBound_iff`, `aperture_column_lowerBound`, `aperture_lowerBound`, `norm_sum_eigenproj_sq`, `le_norm_sum_eigenproj`, `symm_eq_sum_eigenproj`, `norm_mul_conj_sub_one`, `apertureProj_eq_one` |
| Theorem 6.1, infinite spectrum: close distinct eigenvalues `∣x⟩⟨y∣`, or approximate eigenvectors in `H_c ≠ 0` (spectral values of a unitary are unimodular approximate eigenvalues); witnesses orthogonal to the fixed space with `‖δ R‖₂ → 0` | `exists_almostFixed_rankOne`, `hsConj_rankOne_eigen`, `hsNorm_transgression_rankOne_eigen`, `atomicPinch_rankOne_eigen`, `atomicPinch_rankOne_continuous`, `hsNorm_transgression_rankOne_le`, `norm_eq_one_of_mem_spectrum`, `exists_approxEigen_of_mem_spectrum`, `hasApproxEigenvectors_of_nontrivial` |
| Corollary 6.2 every finite aperture has a bounded inverse on its off-resonant blocks | `exists_apertureInverse`, `exists_separation_of_finset` |
| Corollary 6.2 infinite spectrum forces global ill-conditioning, for every spectral type | `spectrum_infinite_iff_almostFixed` |
| Corollary 6.2 best inverse norms over increasing eigenvalue apertures diverge | `aperture_inverse_diverges` |
| §7 `U ↦ U*` conjugates eigenvalues, `H_λ(U*) = H_{λ̄}(U)` | `unitaryEigenspace_symm`, `mem_unitaryPointSpectrum_symm`, `eigenproj_symm` |
| §7 (1) `H_at`, `H_c`, `P_at`, `P_c` unchanged | `atomicSubspace_symm`, `continuousSubspace_symm`, `atomproj_symm`, `contproj_symm` |
| §7 (2) pinching unchanged (common fixed space) | `hsConj_symm_eq_iff`, `atomicPinch_symm` |
| §7 (3) masses unchanged | `atomicMass_symm`, `continuousMass_symm` |
| §7 (4) criterion (MSF.9) unchanged | `tendsto_traceNorm_symm_iff` |
| §7 (5) finiteness of the spectrum unchanged | `unitaryPointSpectrum_finite_symm_iff`, `spectrum_finite_symm_iff` |
| §7 (6) closedness of the transgression range unchanged | `isClosed_range_columnTransgression_symm_iff` |
| §8 table: finite atomic / infinite pure point (`H_c = 0`): trace-norm convergence; closed iff finite | `continuousMass_eq_zero_of_bot`, `tendsto_traceNorm_of_continuousSubspace_eq_bot`, `isClosed_range_columnTransgression_iff_finite_spectrum` |
| §8 table: atomless continuous: zero `S₂` limit, all trace escapes, no `S₁` convergence for nonzero states, dense nonclosed transgression | `atomicPinch_eq_zero_of_hasNoEigenvectors`, `continuousMass_eq_opTrace_of_hasNoEigenvectors`, `not_tendsto_traceNorm_of_hasNoEigenvectors`, `dense_range_columnTransgression`, `isClosed_range_columnTransgression_iff_finite_spectrum` |
| §8 table: mixed spectrum: atomic pinching, convergence iff continuous mass zero | `tendsto_hsNorm_hsCesaro_sub_atomicPinch`, `tendsto_traceNorm_iff_continuousMass_eq_zero` |
| §9 (2) positivity is necessary in Theorem 5.1: a self-adjoint trace-class packet with zero continuous mass and `‖M_N(T) - Π_at(T)‖₁ ≥ 1` | `sheetShiftUnitary`, `hasNoEigenvectors_sheetShiftUnitary`, `sheetPacket`, `continuousMass_sheetPacket`, `atomicPinch_sheetPacket`, `hsCesaro_sheetPacket`, `sheetPacket_formation_traceNorm`, `exists_traceClass_continuousMass_zero_not_tendsto` |
| §9 (6) infinite pure point retains all trace mass but has nonclosed transgression | `tendsto_traceNorm_of_continuousSubspace_eq_bot`, `isClosed_range_columnTransgression_iff_finite_spectrum`, `spectrum_finite_iff` |

`S₂(H)` is modelled as the column Hilbert space `ℓ²(ι; H)` of an arbitrary Hilbert basis; the closed-range
law holds for every basis.  Separability is used only for the countability of `A(U)`.  §1 carries no Lean
obligation; §9 items (1), (3), (4), (5), (7) are scope remarks.

## Log

- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
