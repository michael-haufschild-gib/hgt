# Suzuki 2012 Appendix Regularity — Literature Parity

- **ID:** SUZUKI-2012-APPENDIX-REGULARITY
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** Suzuki (2012), Appendix, Lemmas `lem_ad1` and `lem_ad2`
- **Statement:** Formalize the literal extended Fredholm solution's exact `C¹` regularity in the
  physical variable and aperture, then formalize the resulting first-order system without added
  analytic hypotheses.

## Goal

Reach theorem-for-theorem Lean parity with the regularity input used by Suzuki's canonical-system
derivation. This is literature closure, not an RH proof and not a novel source theorem. It is
non-circular only if moving arithmetic cusps, aperture endpoints, and resolvent dependence are all
derived from the literal kernel and the already-proved signed-resolvent invertibility.

## Gates

- [x] 0 → 1 in-progress: source statement fixed; exact cusp loci identified; attack is source-pure
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact source claims

1. `lem_ad1`: for `omega > 1`, `a > 1`, and either sign, the extended solution is `C¹` in
   `x ≥ 0` away from `x = n / a`.
2. `lem_ad2`: for fixed `x > 0`, the extended solution is continuous in `a > 1` and `C¹` away
   from `a = n / x` and `a = sqrt n`.
3. Equations (406)--(413): differentiated integral equations and the coupled first-order system.

## Closed Lean layer

- `SuzukiCanonicalKernelDifferentiability.lean`: literal beta-tail, `g_omega`, and arithmetic
  kernel `C¹` away from exact cusps.
- `SuzukiCanonicalLogKernelW1One.lean`: exact logarithmic `W^{1,1}` atom/fixed-sum/truncation FTC.
- `SuzukiCanonicalLogConvolution.lean`: reflected-profile substitution and the stronger theorem
  that pairing the literal moving-cusp kernel with any continuous compact profile is `C¹` at every
  positive physical point.
- `SuzukiCanonicalHankelLemmaAd1.lean`: closed universal theorem `suzuki_lemma_ad1`, targeted build
  green; axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
- `SuzukiCanonicalHankelApertureContinuity.lean` and
  `SuzukiCanonicalHankelLemmaAd2Continuity.lean`: literal fixed-window/global bridge and exact
  continuity half of `lem_ad2`, including pointwise continuity of the extended global solution.
- `SuzukiCanonicalHankelL1Smoothing.lean`: bounded literal Hankel smoothing map `L¹ → L²`,
  exact a.e. integral formula, and compatibility with the existing compressed `L²` operator.
- `SuzukiCanonicalHankelL1Resolvent.lean`: exact Woodbury factorization and explicit two-sided
  inverse of the signed fixed-window resolvent on `L¹`, derived solely from the proved `L²`
  inverse. Targeted build green; axiom audit contains only `propext`, `Classical.choice`, and
  `Quot.sound`.
- `SuzukiCanonicalHankelApertureDerivative.lean`: exact moving-endpoint theorem for the literal
  smoothed cutoff. For every continuous profile `f`, the `L²` derivative of `a ↦ H(P_a f)` is
  the rank-one endpoint row `f(a) h_ω(·a)`. This corrects the false intermediate idea that
  `a ↦ P_a f` itself differentiates in `L¹`; its derivative is a Dirac mass. Targeted build green;
  axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
- `SuzukiCanonicalL1Translation.lean`: exact strongly continuous measure-preserving translation
  action on `L¹(ℝ)`, using mathlib's joint `Lp.compMeasurePreserving` continuity theorem.

## Current open core: `lem_ad2` differentiability

The continuity half and exact smoothed moving-cutoff derivative are closed. Remaining seam is the
literal boundary-source derivative in `L¹`: prove the translation-differentiation theorem for the
already-formalized logarithmic `W^{1,1}` kernel, transport it to the fixed physical window, then
differentiate the resolvent equation. Suzuki's printed Fredholm-minor proof suppresses this
topology change. Derivative fields are generally only `L¹` at arithmetic cusps when merely
`omega > 1`; an `L²` shortcut would silently strengthen the theorem and is forbidden.

## Approach

Work on one fixed larger physical window `B` around an aperture `a0`.

1. Realize the aperture-`b` equation on the fixed window using the literal `B`-kernel followed by
   cutoff/restriction to `[0,b]`.
2. Use the already-proved strict `L²(0,B)` contraction to obtain a uniform signed resolvent. Derive
   `L¹` resolvent solvability by the smoothing factorization: the kernel sends `L¹` to continuous
   functions and hence to `L²`; solve the smoothed equation in `L²`, then use the exact algebraic
   resolvent identity.
3. Prove aperture continuity first by a difference equation and shrinking-strip estimates.
4. Prove the boundary-source difference quotients in `L¹` from the exact logarithmic FTC and the
   strongly continuous `L¹` translation action. Do **not** differentiate the raw cutoff in `L¹`:
   its derivative is measure-valued. Use the proved smoothed endpoint law
   `d/da [H(P_a f)] = f(a) h_ω(·a)` instead.
5. Recover fixed-`x` derivatives from the literal global equation. Exclude exactly `a = n/x` for
   the boundary source and `a = sqrt n` for endpoint evaluation—no larger exceptional set.
6. Only after `lem_ad2` is closed, differentiate equation (405), justify integration by parts from
   the proved `W^{1,1}` layer, and formalize (406)--(413).

## Theatre checks

- Do not introduce a premise asserting aperture continuity/differentiability of the solution,
  Fredholm minor, determinant, resolvent, or inverse family.
- Do not replace literal `h_omega` by a smooth proxy.
- Do not claim `L²` differentiability at the source threshold `omega > 1`; the cusp derivative is
  only guaranteed in `L¹`.
- A generic inverse-function theorem counts only after the fixed-window operator and inverse are
  constructed from Suzuki's proved compression, not assumed.

## Log

- 2026-08-13 — Card created. `lem_ad1` closed and axiom-audited in Lean. `lem_ad2` is the next exact
  literature gap; fixed-window `L¹`/`L²` resolvent attack selected.
- 2026-08-13 — Closed exact aperture continuity and the fixed-window `L¹` smoothing/resolvent
  infrastructure. The Woodbury inverse is two-sided, targeted-build verified, and axiom-clean.
  Remaining work is genuine `lem_ad2` `C¹`: prove source and cutoff difference quotients in `L¹`,
  pass them through this inverse, then recover the exact exceptional set `{n/x, sqrt n}`.
- 2026-08-13 — Corrected topology after a proof-failure audit: raw cutoff quotients do not converge
  in `L¹` (Dirac endpoint). Proved the exact theorem actually needed after smoothing,
  `d/da [H(P_a f)] = f(a) h_ω(·a)`, and added strong `L¹` translation infrastructure. This
  isolates one remaining analytic theorem rather than hiding it: translation differentiation of
  Suzuki's literal logarithmic `W^{1,1}` source.
- 2026-08-13 — Closed that analytic theorem without a sharp auxiliary cutoff.
  `SuzukiCanonicalL1TranslationGenerator.lean` proves the strong Sobolev translation generator
  from an exact FTC identity. `SuzukiCanonicalLogSourceL1Derivative.lean` constructs a compact
  smooth extension agreeing exactly with the literal source below any horizon and proves its
  global `W^{1,1}`/FTC/translation derivative across the countable cusp set.
  `SuzukiCanonicalHankelBoundarySourceDerivative.lean` constructs the bounded physical pullback
  `Q_B : L¹(ℝ) → L¹(0,B)`, proves `‖Q_B F‖₁ ≤ B ‖F‖₁`, identifies the localized extension with the
  literal fixed-window boundary row, and proves its unconditional strong `L¹` aperture derivative
  for every `0 < a < B`. Direct `lake env lean` checks pass; targeted builds pass for modules whose
  `.olean` files were required. Open core is now resolvent differentiation plus exact exceptional
  set recovery, not source differentiation.
- 2026-08-13 — Closed fixed-window resolvent differentiation and pointwise transport.
  `SuzukiCanonicalHankelLemmaAd2Derivative.lean` proves a uniform explicit `L¹` inverse bound,
  strong parameter continuity of the inverse without operator-norm continuity, the exact moving
  resolvent difference identity, and unconditional strong `L¹` differentiability of the literal
  Fredholm solution for every `0<a<B`. `SuzukiCanonicalHankelLemmaAd2Pointwise.lean` constructs the
  literal `L¹→C[0,B]` output, proves the moving endpoint/product rule, and obtains pointwise
  aperture differentiability on Suzuki's printed regular locus. The Banach-space theorem is
  strictly sharper at this stage: it requires no `a=sqrt(n)` exclusion. Direct Lean checks pass;
  the single missing derivative-module `.olean` was built successfully. Remaining exact parity
  obligation is the word **continuously** in `lem_ad2`: prove continuity of the derivative field
  on `{a>1} \ {n/x,sqrt(n)}`, then close equations (406)--(413).
