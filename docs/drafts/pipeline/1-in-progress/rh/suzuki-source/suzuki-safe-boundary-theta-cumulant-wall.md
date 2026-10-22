# Suzuki safe wall as a boundary-theta skewness budget

- **ID:** SR-63
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` · Route G / `SUZUKI-SOURCE-SELECTION-AND-TRANSFER`
- **Statement:** Suzuki's safe-shift minor is exactly one third-cumulant inequality for the
  probability law proportional to `exp(x) thetaCuspFullSource(x) dx`.

## Goal

Move the first nonlinear Suzuki target gate from reciprocal Xi-zero coordinates to one literal
theta-source law at the Euler-half-plane boundary `s = 3/2`.  This does not construct the cofinal
two-angle producer.  It removes one necessary target wall only if the final skewness inequality is
proved unconditionally.

## Gates

- [x] 0 → 1 in-progress: exact well-posed source law and attack identified
- [ ] 1 → 2 fully-proven: skewness inequality proved with no open premise
- [x] Partial Lean closure: boundary integrability, source-jet/cumulant bridge, all finite raw
      Hankel blocks, and exact cumulant sign chamber are formalized unconditionally
- [ ] 3 → 4 publication-ready: theorem, proof, certificate, and specialist novelty audit integrated

## Exact conjecture

Put

```text
Z = integral_R exp(x) Phi(x) dx,
Phi = thetaCuspFullSource,
P(dx) = Z⁻¹ exp(x) Phi(x) dx.
```

Let

```text
mu     = E_P[X],
v      = E_P[(X-mu)^2],
kappa3 = E_P[(X-mu)^3].
```

For the safe-shift reciprocal moments

```text
A = Re M_0(1),   B = Re M_1(1),   C = Re M_2(1),
```

the expected exact bridge is

```text
A = mu,
B = (mu-v)/2,
C = (kappa3-3v+3mu)/8,

8(AC-B^2) = mu*kappa3 + (mu-v)(mu+2v).                 (SR-63.1)
```

The existing strict first-defect estimate gives `mu-v = 2B > 0`.  Therefore the surviving hard
source theorem is the sharp one-point skewness budget

```text
SUZUKI-SAFE-TILT-SKEWNESS-BUDGET:
  -mu*kappa3 <= (mu-v)(mu+2v).                          (SR-63.2)
```

Strict inequality would give the strict Suzuki safe wall.  A reverse strict inequality would kill
this target gate and force any surviving two-angle producer to avoid the current Xi second-jet
calibration.

## Paper derivation already checked

Let `L(t) = log xi(1/2+t)` on the real Euler side and write
`mu(t)=L'(t)`.  Existing unconditional Xi jet identities give, at `t=1`,

```text
v = mu'(1) = A-2B,
kappa3 = mu''(1) = -6B+8C.
```

Solving for `B,C` and expanding proves (SR-63.1).  What remains is not algebra:

1. complete the theta Fourier--Laplace moment law at the boundary `|Im w|=1`;
2. identify the normalized boundary raw moments with `mu,v,kappa3`;
3. prove or falsify (SR-63.2) from theta-specific structure.

Lean now supplies boundary integrability by an explicit Gaussian-atom argument, identifies all
three normalized boundary cumulants with the Xi jets, and proves `(SR-63.1)`. It also proves
`mu>0`, `v>0`, `kappa3<0`, `v<mu`, and strict positivity of every finite raw-moment Hankel block.
The only remaining step is to prove or falsify `(SR-63.2)` from theta-specific structure. Generic
moment positivity does not imply this nonlinear cumulant inequality.

## Anti-theatre checks

- Renaming derivatives of `log xi` as cumulants is not progress.  Literal boundary integrals are
  required.
- Generic log-concavity, positivity, self-adjointness, or moment Cauchy--Schwarz do not imply
  (SR-63.2); the existing positive-resolvent countermodels remain applicable.
- `AC-B^2 >= 0` may not be assumed through reciprocal concavity, Hankel positivity, RH, or an
  abstract moment representation.
- Even a proof of (SR-63.2) does not close Route G: cofinal source selection, two-angle
  meromorphic normality, nondegeneration, and Xi/Hermite--Biehler identification remain.

## Novelty status

The boundary-theta cumulant calibration is now an internal formal theorem in
`SuzukiSafeBoundaryThetaCumulantWall.lean`. Classical Fourier--Laplace representations and
complete-monotonicity results for Xi are prior infrastructure, often RH-conditional when derived
from real-zero product geometry. External priority for the exact Suzuki-specific identity and the
still-open skewness wall remains under specialist audit.

## Log

- 2026-08-01 — exact cumulant bridge derived; boundary source completion and skewness sign opened.
