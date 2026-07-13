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
  = diagonalSecondMoment(a) + mixedSecondInvariant(a),

mixedSecondInvariant(a)
  = sum_(alpha != beta) ||A_alpha A_beta†||_HS^2 >= 0.
```

The common-source coupling therefore raises the second moment by an explicit nonnegative
off-diagonal prime-power interaction; it is not a relabelling of the old direct sum.

## Goal

Replace the block-diagonal Sonin moment curve, which deletes mixed prime words, by the canonical
coupled column operator.  Its energy is positive and its Gram entries retain every cross-prime
overlap.  Prove the source-pure chain

```text
finite prime--Gamma Hankel blocks
  lie in the closure of coupled positive-aperture Sonin Gram blocks
    -> every integer-polynomial prime--Gamma Hankel value is nonnegative
      -> RH.
```

The closure premise is a static value relation between two explicit source objects.  It contains
no Xi zero location, real-rootedness, anti-Herglotz sign, limiting divisor measure, or rectangular
subpower estimate.

## Named open core

`[OPEN CORE]` For every cutoff `N`, construct one positive-aperture sequence `a_{N,j}` such that

```text
Tr((C_a† C_a)^(k+1)) -> normalizedPrimeArchMoment(k),   0 ≤ k < 2N-1.
```

Equivalently, prove that every finite normalized prime--Gamma moment-Hankel block is a cluster
point of the positive-aperture Gram blocks of the coupled Sonin column operator.  The first new
coordinate beyond the block-diagonal model is the already formalized nonnegative mixed second
invariant, the sum of all off-diagonal prime-power cross-overlap energies.  The `k=0` convergence
condition is exactly the old scalar Sonin-energy condition, not an additional coupled hypothesis;
its convergence to `normalizedPrimeArchMoment(0)` remains analytic rather than formal.

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
5. Identify the target quadratic form with the existing prime--Gamma trace-Hankel value and use
   the countable criterion for RH.

The formal theorem surface is
`RHTower/SoninCoupledPrimeArchGramTransfer.lean`.  The remaining open core is not hidden by that
surface: it is exactly the analytic construction of the positive-aperture schedules in
`SoninCoupledPrimeArchFiniteMomentCoupling`; the Hankel identity then gives
`SoninCoupledPrimeArchFiniteGramCoupling`, and hence the matrix closure in
`SoninCoupledPrimeArchFiniteGramClosure`.

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
