# cusp-spectrum-radius-law — state and plan

Card: docs/drafts/pipeline/2-fully-proven/cusp-spectrum-radius-law.md

## Closed unconditionally

**Boundary law, degree 1, any conductor** — two routes, both via a functional
equation whose RIGHT side is a convergent series dominated by its first exponent:
1. ζ, any real shift α: `HurwitzZetaRightAsymptotics` → `ZetaTwistShiftDecomposition`
   → `ZetaTwistCuspRadius` → `ZetaTwistGapGeometry`.
   Capstone `hadamardLimsup_zetaTwistShift_eq_infDist` = `1/(2π·infDist α (Sing\{α}))`.
2. Any periodic Φ : ZMod N → ℂ, Φ ≠ 0: `PeriodicLSeriesRightAsymptotics` →
   `ZModLFunctionCuspRadius`. `hadamardLimsup_zmodShift` = `N/(2π n₀)`;
   `hadamardLimsup_zmodShift_of_dft_one` = `N/(2π)` (card's Dirichlet row).

**Step 3 in degree 2** — `RHTower/ZetaSquareCuspRadius.lean`:
`hadamardLimsup_zetaSquareShift : limsup |ζ(s₀-k/2)²/k!|^{1/k} = 1/(4π)`,
needing `∀ k:ℕ, s₀ ≠ k/2`. NO Stirling: `(m!)²/(2m)! = 1/C(2m,m)` and
`4^m/(2m) ≤ C(2m,m) ≤ 4^m` is a polynomial envelope.
New infrastructure (reusable for any degree d):
- `HTGeometry/ScaledRootGrowth.lean` — exponent `1/(a m + b)` versions of the
  whole root-growth engine. Key trick: `u^{1/(am+b)} = (u^{1/m})^{m/(am+b)}` and
  `m/(am+b) → 1/a`, then continuity of rpow at (1, 1/a).
- `HTGeometry/ParityLimsupSplit.lean` — `atTop = map(2·) atTop ⊔ map(2·+1) atTop`,
  `hadamardLimsup_eq_parity_sup`, `limsup_ofReal_eq`.
- `HTGeometry/CentralBinomialRoot.lean` — `centralQuot`, its bounds and root.

**Interior law, any degree** — `HTGeometry/NonnegThetaCuspGrowth.lean` +
`CuspGapUnconditionalInstances.lean` (non-negative coefficient families).
CAVEAT: base height is *chosen* to be Δ, so it is the interior shadow.

**K–P for ζ** — `RHTower/ZetaStandardTwistDichotomy.lean`,
`differentiable_expZeta_iff`, straight from mathlib's `expZeta`.

## What is left

Only degree `d > 1` in the *general* boundary law: it needs the class member's
own Hurwitz-type formula, i.e. the Selberg class `S^♯` + Kaczorowski–Perelli.
The corpus has NO Selberg-class layer (the `Selberg*` modules are the sieve).
Model the structure on `RHTower/SelfDualDirichletRealZeros.lean`'s
`SelfDualPrimitiveDirichletDatum`. The scaled/parity engine above is already in
place for whatever degree such a formula would produce.
