# Mass-shifted strict-frontier curvature renewal (2026-08-12)

## Result
New unconditional Lean module `formal/GaloisForLFunctions/RHTower/XiShiftedHankelStrictFrontierCurvatureRenewal.lean` proves actual canonical terminal-frontier schedule carries adaptive arithmetic source prices.

Capstones:
- `xiShiftedHigherBlockFailureSet_mono`
- `xiShiftedHigherBlockTerminalFrontier_mono_of_le`
- `exists_sourceAdaptive_frontierCertificate_of_strict_step`
- `exists_occupied_xiShiftedHigherBlockTerminalFrontier_gt_of_not_riemannHypothesis`
- `exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis`
- closed `riemannHypothesis_or_cofinal_sourceAdaptive_frontierCertificates`

Strict step assumptions `F_n.Nonempty` and `tau_n<tau_(n+1)` make `y=tau_(n+1)` a singular PSD face with positive head. Its null vector has nonzero terminal coordinate; parity-complete flat-face theorem yields k>=n+2 and x with `0 < -Q_y(x)` and `y+(-Q_y(x))/W(x) <= tau_k`.

Under false RH, for every A choose y=|A|+1. Fixed-shift all-block criterion gives non-PSD H_N(y), hence H_(N+2)(y) not PD, y∈F_N, and A<y<=tau_N. Therefore occupied frontiers are unbounded. Nested failure sets plus finite adjacent-step extraction give cofinal strict rungs, each source-priced as above. Closed dichotomy is RH or cofinal priced strict renewals.

## Conjecture/failure audit
- Hard-edge compactness does NOT give uniform positive renewal quotient: transverse coupling can vanish at aperture boundary.
- Cofinal positive prices do NOT by themselves imply divergent sum.
- Bounded producer region, absence of actual-schedule admission, and infinite plateau escape are now closed.

## Higher principle / open core
Curvature-renewal/free-flight decomposition: every strict rung contains priced Lipschitz persistence plus possibly unpriced positive-chamber free flight. Under false RH, rungs/frontiers are cofinal. Exact remaining burden is a renewal-efficiency theorem: priced fraction of cofinal frontier travel cannot vanish, equivalently free-flight slack cannot dominate known parabolic recession.

## Documentation
- report equations (9.3.611)-(9.3.614) in `docs/reports/mass-shifted-spectral-trace-route.md`
- Stage3 card `docs/drafts/pipeline/3-formalized/mass-shifted-strict-frontier-curvature-renewal.md`
- umbrella import in `formal/GaloisForLFunctions/RHTower.lean`

## Verification
Direct `lake env lean` passed; targeted `lake build GaloisForLFunctions.RHTower.XiShiftedHankelStrictFrontierCurvatureRenewal` passed. All new theorem axiom audits report only `propext`, `Classical.choice`, `Quot.sound`. No computations. Corpus lint fails pre-existing unreachable modules only; new module is reachable.