# TG native first-jet shell scale law — completed component

User cleared the broader research goal and asked to finish started code. Completed exactly three leaves and stopped; do not resume the old goal without a new request.

Files: `formal/GaloisForLFunctions/BiScaleUncertainty/PositiveDiagonalCovariance.lean`, `formal/GaloisForLFunctions/RHTower/BurnolFirstJetDampingShell.lean`, `formal/GaloisForLFunctions/RHTower/BurnolFirstJetShellScaleLaw.lean`. Exactly one direct import each in BSU/RHTower umbrellas. Card: `docs/drafts/pipeline/3-formalized/tg-native-first-jet-shell-scale-law-2026-10-18.md`.

For original bounded first-jet synthesis S, columns have norm squared 1/(4 k p^k). Native weights d_t=exp(-2t k log p). For c>=1 and t>0, Q=S diag(d_t-d_ct) S* is positive trace class and equals the difference of original native damped covariances: square-root weighted synthesis is exactly burnolWeightedShift(t) composed with S. All prime depths and physical mixed entries retained. Re Tr Q=[eulerLogMoment(1+2t)-eulerLogMoment(1+2ct)]/4=log(c)/4+[R(1+2t)-R(1+2ct)]/4. Trace tends to log(c)/4; Q tends strongly to zero. For c>1 its trace norm cannot tend to zero. For c=2 trace eventually lies strictly in (0,1), with literal source normalization.

Scope: does NOT identify Q with formationCubicDefect, pay the Gamma/co-Poisson residual, prove the central Gaussian sign, or prove RH. TG remains open; no route retired. No external novelty/priority audit.

Validation: all three canonical leaf compilations exit 0, empty logs; scratch API probe exit 0; separate scratch audit checks all 42 public declarations, only propext/Classical.choice/Quot.sound. Source hashes rechecked; no prohibited declarations. Scoped diff check passes. Global formal lint exit 1 for eight unrelated unreachable BSU/BVI modules, listed in card and /tmp/hgt-tg-formal-lint.log. Global diff check also flags an unrelated trailing blank line in BVI README. No full umbrella build, commits or pushes. Evidence: /tmp/hgt-tg-shell-audit-manifest.json and /tmp/hgt-tg-shell-source-sha256.txt. All owned jobs terminal.

Rotation preference: 27 live routes plus 18 candidates; do not repeatedly concentrate on one route. Recent sequence RW → TH → MSC → RB → SZ → BVI → HCF audit → JAS → PA → RFHM → EGC → TG. No new route investigation authorized by this finishing request. See `mem:rh/egc-source-ray-scale-separation-2026-10-18` for preceding component.
