# Positive one-coordinate completion of finite log-shift panels

- **ID:** weil-finite-panel-positive-completion
- **Stage:** 3-formalized
- **Type:** EXACT BOUNDARY / constructive finite-observation limitation
- **Write scope:** `formal/GaloisForLFunctions/RHTower/WeilFinitePanelPositiveCompletion.lean`,
  its umbrella import, this card, generated index and memory.
- **Source policy:** Lean corpus only; no external papers, numerical experiments or heartbeat increases.

## Exact theorem

For every integer window k>=1, choose N=floor(exp(2k))+1. Then
exp(2k)<N<2exp(2k). For every coefficient sequence and every real target height,
increasing only coefficient N by a sufficiently large positive amount raises
every entry of the finite log-shift panel above that height. All coefficients
at indices <=exp(2k), including any prescribed deficit there, remain unchanged.

This identifies a precise limitation of each finite panel while preserving
the verified quantitative excess-mass requirement from the predecessor card.
The positive survivor is constructive one-coordinate completion, not merely a
negative claim about finite observations.

## Original proof obligations [CLOSED]

1. Audit exact strict support of the truncated autocorrelation. Proposed law:
   `0 < K_L(y) iff |y| < 2L`, valid for all real L,y. Use positivity at t=y/2
   of the continuous nonnegative compactly supported integrand; check actual
   smooth cutoff positivity rather than assume it.
2. For exp(2k)<N<2exp(2k) and 2<=m<=exp(2k), the paired kernel at log N equals
   `-2 K_k(log N-log m)<0`. Its other two autocorrelation terms vanish.
3. Use the verified finite affine panel-difference formula to show that a
   positive change a at N raises probe m by `2a K_k(log N-log m)/sqrt(N)`.
4. Each slope is strictly positive and there are finitely many probes; choose
   one positive amplitude exceeding all required height ratios.
5. Export an unconditional quantified completion theorem with no RH, full-cone
   positivity, summability or coefficient growth premise. Record the exact
   preserved coefficient block and the positive slope law.

## Corpus audit / work log

- [x] Read active objective; previous turn produced verified excess-mass bounds.
- [x] Initial documented lexical strict-positivity query returned no hits;
  broadened to all truncated-autocorrelation declarations and inspected all 11.
- [x] Exhaustive source text searches located cutoff definitions, zero-boundary
  theorem, and continuous compact-support integral-positivity proof pattern.
- [x] Audit strict cutoff positivity and nearest constructive-completion results.
- [x] Close paper proof before writing Lean implementation.
- [x] Verify APIs in scratch, implement, run leaf/axiom audits, wire and index.
- [x] Authoritative lint and final status recorded.
- [x] Memory updated; all owned jobs terminal; all 13 owned scratch files removed
  and absence verified.

**[PAPER PROVED; LEAN VERIFIED]** Seven theorems and one definition passed the
final leaf and axiom audits. Existing mass-bound module remains unchanged.

## Closed paper proof

The actual cutoff is `smoothTransition(L-u)*smoothTransition(L+u)`.
Mathlib's `Real.smoothTransition.pos_of_pos` and the existing cutoff zero law
give strict positivity exactly on `|u|<L`. Since `riemannKernelReal` is strictly
positive everywhere, the truncated real kernel has the same positivity set.
For `|y|<2L`, both truncated factors are positive at t=y/2. Their product is
continuous, nonnegative, compactly supported, and nonzero there, so its integral
is strictly positive. For `2L<=|y|`, the existing exact zero law applies.

Write E=exp(2k). For k>=1, E>2, and N=floor(E)+1 satisfies
`E<N<=E+1<2E<E^2=exp(4k)`. Thus N lies inside the visible coefficient block
and outside the preserved block. For each panel index m,
`0<log(N)-log(m)<2k`; meanwhile `log(N)>2k` and `log(N)+log(m)>2k`.
The paired-kernel identity therefore reduces to `-2K_k(log(N)-log(m))<0`.

The predecessor's finite affine identity reduces a single coefficient increase
a at N to the positive real gain a*s_m, where
`s_m=2K_k(log(N)-log(m))/sqrt(N)>0`. For the arbitrary original panel P and target
r, choose

`a = 1 + sum_m max((r-Re(P_m))/s_m,0)`.

Every summand is nonnegative, so a>0 and a is strictly larger than each required
ratio. Hence every updated real probe exceeds r. Only coefficient N changes;
all indices <=E remain exactly as prescribed. No sign, tail, convergence,
positivity or RH premise is needed for the starting coefficient sequence.

## Nearest-result audit

All 11 indexed truncated-autocorrelation declarations were inspected; none states
the strict support equivalence. The broad Weil/completion query had 193 results;
its first ranked page was inspected, with no claim of exhaustive semantic
coverage. An exhaustive focused text search of the Weil sources supplied the
nearest constructive results. `bounded_coherent_completion` repairs a finite
family of polar tests and controls archimedean cost; `ExposingRayRealization.repair`
constructs test mixtures with prescribed integer atom trace. Neither gives the
one-coefficient positive direction of this finite log-shift panel. Full-cone
completion rigidity concerns positivity on all tests. This theorem concerns
one window, and its amplitude depends on that window. No external novelty claim.

## Verified positive survivor and exact limitation

`exists_weilLogShiftWindowPanel_positive_completion` is unconditional in k, the
starting coefficient sequence and the real target height. The implementation
uses window k+1 to cover all positive integer windows. Its explicit positive
spike is at `weilLogShiftLiftIndex k=floor(exp(2(k+1)))+1`; every coefficient at
an index <=exp(2(k+1)) is unchanged. All coefficients except the spike index are
unchanged by the displayed construction. Every updated real panel entry is
strictly above the requested height.

This is a constructive completion theorem, not merely a failed separation claim.
The independent positive statements are exact cutoff/kernel/autocorrelation
support, exact spike location, and exact complex affine gain. Finite panel
positivity alone cannot reject arbitrary prescribed coefficients in its earlier
index block. The prior visible excess-mass bound remains a necessary condition.
No assertion about positivity on the full Weil cone or simultaneous completion
at infinitely many windows is made here.

## Final verification evidence

- Final direct leaf command from `formal` exited 0, with no diagnostics:
  `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/WeilFinitePanelPositiveCompletion.olean GaloisForLFunctions/RHTower/WeilFinitePanelPositiveCompletion.lean`.
- Separate `/tmp` import/signature/axiom audit with `lake --old env lean` exited 0.
  All eight declarations have exactly `[propext, Classical.choice, Quot.sound]`:
  `bulkCutoff_pos_iff`, `truncatedRiemannKernelReal_pos_iff`,
  `truncatedRiemannAutocorr_pos_iff`, `weilLogShiftLiftIndex`,
  `weilLogShiftLiftIndex_bounds`, `weilLogShiftLiftIndex_kernel`,
  `weilLogShiftWindowPanel_singleSpike`, and
  `exists_weilLogShiftWindowPanel_positive_completion`.
- Exported signatures were inspected: strict support holds for all real L,y,
  including nonpositive L; the gain identity permits any real amplitude; the
  completion supplies a strictly positive amplitude for arbitrary lam and r.
- `scripts/formal_tools.py index` exited 0; all eight declarations have API rows.
- `RHTower.lean` imports the leaf exactly once immediately after
  `WeilFiniteBlockExcessMass`. No full or umbrella build was run.
- Scoped `git diff --check` passed. No heartbeat setting was added.
- `scripts/formal_tools.py lint` exited 1. Its only errors were these 17 unrelated
  modules unreachable from their theorem-area umbrellas:
  RHTower's `ChronologicalMobiusSubsetSums`, `XiRealRootedApproxEigenLimitRH`,
  `XiRealRootedEigenGaussianGrowthRH`; HTGeometry's `ApertureConeCalculus`,
  `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
  `BoundaryCoronaCStarAlgebra`, `PaperFourierLLogL.Compress.Context`,
  `PaperFourierLLogL.Compress.Projection`, `PaperFourierLLogL.Compress.Select`,
  `PaperFourierLLogL.Compress.ThinChoice`, `PaperFourierLLogL.Dyadic.Node`,
  `PaperFourierLLogL.Dyadic.Snap`, `PaperFourierLLogL.Fourier.Good`,
  `PaperFourierLLogL.Thermal.Ginibre`, and `PaperFourierLLogL.Thermal.Order`.
  These files were not edited here. Repository lint is not claimed green.

## Possible next conjecture [UNPROVED]

A later positive spike may preserve positivity of every earlier panel: outside
the earlier exp(2j) block, the central autocorrelation term vanishes and the
remaining paired terms are nonpositive. If this exact monotonicity and local
finiteness can be proved, recursive positive spikes might complete all windows
beyond one cutoff simultaneously while preserving any prescribed finite prefix.
This stronger claim has not been searched or formalized. It needs a new paper
and corpus audit, especially the passage from finite stages to an infinite
coefficient sequence. The current finite-window theorem does not imply it without
those additional arguments.
