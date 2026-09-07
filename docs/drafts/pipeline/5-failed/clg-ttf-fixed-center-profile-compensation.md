# CLG/TTF: fixed center-profile compensation

**Status:** paper proof and Lean theorem closed. This excludes the stated separable correction,
not CLG/TTF or center-dependent corrections. RH remains unproved.

**Attempt:** extend the successful finite-rank center compensation to a whole reflected density
using one displacement profile, independent of the center. With the literal source `Φ`, set

```
P_x(t)=Φ(x+t)Φ(x-t),
G(x)=3Φ(x)²+2xΦ(x)Φ'(x),
g(x)=G(x)/Φ(x)²=3+2x(log Φ)'(x),
K_x(t)=P_x(t)+G(x)C(t),       C(0)=0.
```

The proposed all-order certificate requires `K_x` positive definite for every `x≥0`.
This in particular requires `|K_x(t)|≤K_x(0)=Φ(x)²` for every real displacement.
The corpus already proves `0<P_x(t)≤Φ(x)²` by logarithmic concavity.
Consequently the necessary two-point bound gives the exact quantitative restriction

```
|g(x)| |C(t)| ≤ 2.                                         (1)
```

Indeed, `|G(x)C(t)|=|K_x(t)-P_x(t)|≤2Φ(x)²`, and the source square is strictly positive.
For `g(x)<0`, the sharper interval is

```
(P_x(t)/Φ(x)²-1)/(-g(x)) ≤ C(t)
  ≤ (P_x(t)/Φ(x)²+1)/(-g(x)).                              (2)
```

Strict logarithmic concavity and evenness give `(log Φ)'(1)<0` and
`(log Φ)'(x)≤(log Φ)'(1)` for `x≥1`. Hence
`g(x)≤3+2x(log Φ)'(1)→-∞`. Letting the center grow in (1) forces `C(t)=0` for
every displacement. No nonzero fixed profile can satisfy even this necessary two-point
condition. This proof needs no tail expansion, numerical evidence, or RH assumption.

**Positive survivor:** bound (1), and interval (2), remain necessary for a center-dependent
profile `C_x(t)`. Its displacement values must shrink along the tail at least as prescribed
by `1/|g(x)|`. The result supplies a quantitative compatibility condition for an entire
corrected kernel; it does not assert that a family meeting that condition exists.

**Scope:** the existing rank-three and rank-four compensation theorems change a final moment
in a finite matrix. They do not construct a displacement profile with these global two-point
bounds. Their validity is unaffected. Nor does the argument exclude a purely formal moment
sequence without a proved kernel realization. The actual aperture-dependent flux derivative
is a different coefficient from `G`; no assertion about that coefficient is obtained merely
by its lower bound by `G`.

**Next mathematical action:** any all-order compensation proof must retain its center and
displacement dependence, or prove the integrated form directly. Choosing more constants for
successive finite determinants does not establish the rejected fixed-profile certificate.

## Lean evidence

Module: `GaloisForLFunctions.RHTower.ThetaCuspFixedCenterCorrectionRigidity`.
It imports only the existing `ThetaCuspKernelLogConcavity`, expressing the correction directly
in the literal source and its logarithm. Its four theorems prove unbounded negative normalized
coefficient, interval (2), bound (1), and fixed-profile rigidity. No extra analytic or sign
assumption enters the source estimates; the rigidity theorem quantifies over profiles satisfying
the displayed mass and two-point conditions.

The scratch file passed `lake env lean`. After a no-build preflight identified only the new
leaf as stale, the final audit
`lake --old --log-level=error build GaloisForLFunctions.RHTower.ThetaCuspFixedCenterCorrectionRigidity`
built that leaf in 5.5 seconds. All four new theorem axiom audits passed using only
`propext`, `Classical.choice`, and `Quot.sound`. The umbrella import is wired.

The initial audit used an unnecessarily broad import and started rebuilding stale dependencies
in parallel. It was terminated together with its child processes; one dependency had finished.
Narrowing the import removed that dependency rebuild. No umbrella build or numerical experiment
was used.

Generated indexes were refreshed. Scoped whitespace checks passed. Repository-wide formal lint
reported one separate concurrent-work issue: the newly added `WindowCarrierOscillation` module
was not yet reachable from its umbrella. The new correction-rigidity module is wired; its direct
check, leaf build, and axiom audit passed.
