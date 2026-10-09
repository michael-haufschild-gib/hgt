# Finite coefficient blocks suffice for log-shift separation

- **ID:** weil-finite-block-minorant-separation
- **Stage:** 3-formalized
- **Type:** PREMISE REDUCTION / exact finite observation identity
- **Source:** the functional definition and the support/quantitative separation
  theorems in `RHTower/WeilFullConeMinorantRigidity.lean` and its imports.
- **Write scope:** new `formal/GaloisForLFunctions/RHTower/WeilFiniteBlockMinorantSeparation.lean`,
  its RHTower umbrella import, this card, generated index and session memory.
  Preserve the already verified minorant module.
- **Source policy:** Lean corpus only. No external papers, web searches or numerical experiments.

## Proved statements

For an integer window k, put N(k)=floor(exp(2k)), B(k)=exp(4k).
Complete an arbitrary coefficient sequence lam by retaining it through B(k) and
using Lambda afterward. Denote this completion by C_k(lam).
Let P_k(lam) be the finite complex vector of actual full Weil probe values at
`logShiftRiemannDifference k (log m)`, indexed by `m in Icc 2 N(k)`.

1. Unconditional exact identity: `P_k(C_k(lam)) = P_k(lam)` for every k and lam.
2. For every q:N and t:R, there is K:N such that every integer k>=K satisfies:

```
{lam : N -> R |
  (forall n, 2<=n AND n<=exp(4k) imply lam(n)<=Lambda(n)) AND
  exp(t)<=(Lambda(q+2)-lam(q+2))/sqrt(q+2)}
  is a subset of
{lam : N -> R |
  exists m, 2<=m AND m<=exp(2k) AND
  Re(full Weil probe value at k,m) <= -exp(t)*riemannAutocorr(0)/25}.
```

The cutoff is uniform over all sequences in the displayed class. The coefficients
beyond the finite block have no sign, size, growth, summability or positivity
restriction. No assertion that Lambda passes the probes is required.

3. Positive consequence: uniformly beyond a cutoff, if the finite probe panel is
   nonnegative and the prescribed coefficient deficit is present, some coefficient
   between 2 and exp(4k) must strictly exceed Lambda. Thus a deficit cannot be
   compensated solely by an arbitrary remote tail.

## Paper proof [CLOSED BY SOURCE AUDIT]

For an eligible m, c=log(m) lies in [0,2k]. The source identity expresses the
autocorrelation probe at y as `2 K_k(y)-K_k(y+c)-K_k(y-c)`.
The source theorem `truncatedRiemannAutocorr_eq_zero` kills K_k(z) whenever
`2k<=|z|`. If `4k<=|y|`, the triangle inequalities
`|y|<=|y+c|+c` and `|y|<=|y-c|+c` give this bound for all three arguments.
Thus the probe vanishes at both signed logarithms of every n>exp(4k).

The actual `weilFullFunctional` definition depends on lam only through its
coefficient series. Below the cutoff the two coefficient sequences agree;
above it the kernel factor is zero; below n=2 the coefficient factor is zero.
Consequently every summand is identical, hence the complete complex functional
and the finite panel are identical. This uses equality of series terms, not
a rearrangement or an unproved convergence hypothesis.

Take the uniform global-minorant separation cutoff from
`exists_uniform_logShift_minorant_separation`. Enlarge it by the natural ceiling
of `log(q+2)/4`, ensuring q+2<=exp(4k) in every admitted window.
For a sequence satisfying the finite block condition, C_k(lam) is a global
minorant and retains the prescribed coefficient deficit. Apply the global
separator to this completion. The exact panel identity transfers its negative
probe value back to the original arbitrary-tail sequence.

For the positive consequence, absence of such a finite-block excess is precisely
the finite minorant condition. Target 2 then supplies a strictly negative probe,
contradicting nonnegativity of the finite panel. Strictness follows from
exp(t)>0 and riemannAutocorr(0)>0, both already proved in the corpus.

## Corpus novelty audit

- Ran the documented lexical research command for `"weilFullFunctional" "support"`
  with `--module RHTower --per-module 0 --no-refresh --json`. One declaration hit:
  `weilFullFunctional_transl_sub_eq` in `WeilConeWindowRigidity.lean`.
  Candidate-lemma and source-argument sections were empty; the lexical result
  provides no semantic-coverage certification.
- Exhaustive RHTower search found 41 uses/declarations relating the functional
  to congruence, support or sums. The existing `weilFullFunctional_congr` assumes
  agreement at every coefficient n>=2; it does not isolate this finite block.
- Read the actual functional definition, global congruence proof, translated
  window identity, truncated-autocorrelation support theorem, log-shift kernel
  identity and current uniform-separation signature.
- The translated window identity and its adjacent rigidity receiver assume
  support/large-translation conditions and global full positivity. They do not
  eliminate arbitrary tails from these finite log-shift probes.
- The proposed advance is exact finite-panel invariance and replacing the global
  minorant condition by a finite coefficient block. No external novelty claim.

## Limits

The bound exp(4k) is a sufficient common cutoff, not a sharp support claim.
No full Weil positivity or RH follows from the finite certificate. All existing
global-minorant results remain unchanged.

## Work log

- [x] Revalidate current source and read the active objective.
- [x] Corpus search and nearest-result comparison.
- [x] Close the paper proof from actual source identities.
- [x] Verify APIs in this toolchain using a /tmp probe.
- [x] Formalize finite completion, finite panel, exact identity, local separator and excess localization.
- [x] Direct leaf audit, axiom audit, umbrella wiring, index and authoritative lint.

**[FORMALIZED]** All three theorems and both definitions pass the final direct
leaf and axiom audits. The leaf is warning-free, indexed and wired. Repository
lint fails on eleven unrelated umbrella-reachability errors, listed below.

## Implementation checkpoint

The new leaf defines `weilLogShiftWindowCompletion` and `weilLogShiftWindowPanel`.
It proves `weilLogShiftWindowPanel_completion`,
`exists_uniform_finiteBlock_logShift_separation` and
`exists_uniform_finiteBlock_excess_of_deficit`.
The existing global-minorant source was not modified. The new module is imported
immediately after it in the RHTower umbrella.

The API probe caught an unavailable `abs_add` name; both triangle bounds instead
use the corpus's verified `abs_sub`. Polymorphic scratch probes were instantiated
at concrete types. The first leaf check required opening the source's `Zeta23`
namespace and annotating finite-block coefficient indices as naturals. The next
check passed. All five initial axiom lists were exactly
`[propext, Classical.choice, Quot.sound]`, and the printed signatures contain only
the intended data parameters and unconditional statements.
No heartbeat limit was raised. Owned scratch files use `/tmp/hgt-weil-local*`.

## Final verification

- `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilFiniteBlockMinorantSeparation.olean GaloisForLFunctions/RHTower/WeilFiniteBlockMinorantSeparation.lean`
  passed with exit 0 and no diagnostics after the tactic-style cleanup.
- The final `/tmp` import, signature and axiom audit passed for all five new
  declarations. Every axiom list is exactly `[propext, Classical.choice, Quot.sound]`.
  Printed signatures confirm the intended finite panel and coefficient block,
  with no extra proof arguments or implicit scientific hypotheses.
- `scripts/formal_tools.py index` passed after the final source edit. All two
  definitions and three theorems appear in the generated API index.
- The RHTower umbrella imports the new module exactly once. No full or umbrella
  build was run; only one owned Lean process ran at any time.
- Scoped `git diff --check` passed. No heartbeat override, proof debt, numerical
  experiment, external source, commit or push was introduced.
- `scripts/formal_tools.py lint` exited 1 solely for these unrelated unreachable
  owned modules:

```
RHTower.ChronologicalBudgetGapLaw
RHTower.ThetaCuspRatioKineticLeading.JetHeads
RHTower.ThetaCuspRatioKineticLeading.KineticCoefficients
RHTower.ThetaCuspRatioKineticLeading.MinorLeading
RHTower.ThetaCuspRatioKineticLeading.ReflectionHeads
HTGeometry.ApertureConeCalculus
HTGeometry.ApertureConeWinding
HTGeometry.ApertureLogTranslation
HTGeometry.ApertureOpenHistoryIdeal
HTGeometry.BoundaryCoronaCStarAlgebra
HTGeometry.PaperFourierLLogL.Weak.Cover
```

These modules were not edited for this task. The global lint gate is not reported
as passing. The former global-minorant theorem remains intact; the new result
applies it to a finite-block completion and transfers exact probe values back.

All nine owned `/tmp/hgt-weil-local*` files were removed after every owned job
exited and the evidence above was recorded. Absence of matching files was verified.
