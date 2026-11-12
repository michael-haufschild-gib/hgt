# The critical power comb does not converge

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** A82; the excluded parameter `a=1/2`.
- **Statement:** `¬ PowerCombTailConverges (1/2)`.
- **Lean status:** Complete chain written; first eight supports through the actual Dirichlet symbol verified; remaining modules unverified.

## Finite parts and forced drift

The critical archimedean jet is
`1/(√t(1+√t)) + 1/(√t(1+t))`, a decreasing function on `(0,1]`.
Its mesh error is at most `4/√N`; the row error is at most
`5/(2(N+1))+4/√(N+1)`. Harmonic weighting makes this error summable,
so the archimedean comb has a finite part after removing `rowLimit H_N`.

The centered Euler remainder and co-Poisson floor estimate give
`|prefix(a,X)-X^(1-a)/(1-a)-ζ(a)| ≤ C_a X^-a` for `0<a<1`, `X≥1`.
Thus subtracting `Re ζ(1/2)/t` from the critical reference profile leaves
an integrable `O(t^-1/2)` profile with convergent meshes. The removed
mesh is exactly `Re ζ(1/2) H_N`.

The first-degree remainder tends to `2 pole(1/2) Re ζ(1/2)`.
Consequently critical comb convergence is equivalent to convergence of
`contacts(N)-C H_N`, where `C=rowLimit/2-Re ζ(1/2)`.
Central ξ symmetry and the Gamma row formula identify
`C=-ζ′/ζ(1/2)-ζ(1/2)`: harmonic subtraction removes the actual real pole.

## Pole obstruction

Convergence of the harmonic remainder gives a holomorphic transform on
`Re s>0` and zero residues at nonzero boundary frequencies. Restoring
`Cζ(s+1)` preserves these properties. Its actual symbol is
`ζ(s+1)(-ζ′/ζ(s+1/2)-ζ(s+1/2))`.

Every zero with `Re ρ≥1/2` supplies a nonzero interior or boundary
residue: its multiplier `ζ(ρ+1/2)` lies in the zero-free closed outer
half-plane. Unconditional zero existence and reflection supply such a
zero; a separate Hardy theorem is unnecessary.

## Lean chain

- `CriticalPowerTailJetMesh`, `CriticalPowerTailArchimedeanFinitePart`.
- `PowerTailPrefixQuantitativeFinitePart`, `CriticalPowerTailReferenceFinitePart`.
- `CriticalPowerCombConvergencePaysHarmonicContacts`.
- `CriticalPowerContactCoefficientIsTheRealResidue`.
- `CriticalPowerContactMellin`, `CriticalPowerContactDirichletSymbol`,
  `CriticalPowerContactContinuation`.
- `TheCriticalPowerCombDoesNotConverge`.

## Positive survivor

The quantitative finite parts, exact harmonic decomposition, and forced
real coefficient survive ordinary divergence. `CriticalPowerCombGrowthDetectsRH`
also writes the exact classification: for every `σ≥0`, the critical
contacts, harmonically centered contacts, and literal critical comb have
strict growth threshold `σ` iff `XiZeroHalfPlaneBound σ`. In particular,
they have every positive power bound iff RH. Weighted inversion is valid
at exponent zero; harmonic subtraction and the convergent elementary
remainder preserve every nonnegative threshold. This extends the existing
strictly subcritical growth law to its previously excluded endpoint.
This positive classification remains unverified.
A stronger candidate is
[critical Abel integrability iff RH](critical-power-comb-abel-integrability-detects-rh.md),
with finite Abel limit read from the removable real contact symbol.
The equivalence and finite-limit proof are written but unverified.
This route is not retired.

`CriticalPowerTailJetMesh` passed Lean: critical mesh error ≤4/√N and
row error ≤5/(2(N+1))+4/√(N+1).
`CriticalPowerTailArchimedeanFinitePart` passed Lean: harmonic row errors
are summable and the critical archimedean logarithmic finite part exists.
`PowerTailPrefixQuantitativeFinitePart` passed Lean: the power-prefix
finite-part error is O(X^-a) at every real cutoff X≥1, for 0<a<1.
`CriticalPowerTailReferenceFinitePart` passed Lean: subtracting Re ζ(1/2)/t
leaves an integrable profile with convergent meshes and exact harmonic subtraction.
`CriticalPowerCombConvergencePaysHarmonicContacts` passed Lean: critical
comb convergence iff harmonically centered contact convergence, with the
explicit affine logarithmic contact asymptotic.
`CriticalPowerContactCoefficientIsTheRealResidue` passed Lean: C=B(0).
`CriticalPowerContactMellin` passed Lean: the restored transform is holomorphic
on Re s>0 and has vanishing nonreal boundary residues under comb convergence.
`CriticalPowerContactDirichletSymbol` passed Lean: the restored transform
equals the actual contact Dirichlet symbol on its initial half-plane.
Remaining endpoint chain unverified.
