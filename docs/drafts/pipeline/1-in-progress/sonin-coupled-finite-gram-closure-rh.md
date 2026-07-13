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
coupled all-prime source columns `C_{a_{N,j}}` are nonzero and for which

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
6. Prove the concrete source column is nonzero, equivalently that its zeroth trace energy is
   strictly positive, and normalize every source moment by that energy; the canonical
   target/source zeroth-moment quotient reconstructs the projective scale.
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
with ordinary nonvanishing of the explicit source column.

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
