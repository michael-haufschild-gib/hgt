# BAG full positive Mellin lines

- **Stage:** 3-formalized

For every pair a,b>0 and every planar Schwartz function f, the pullback
exp(-a*u-b*v)*f(exp(-u),exp(-v)) is Schwartz. No boundary vanishing is needed.
Let delta=min(a,b)>0 and choose an integer m>max(a,b)+delta. In each coordinate,
exp(-a*u+delta*abs(u)) <= (1+norm(node u))^m. Multiplication controls all four
quadrants by Schwartz decay of degree2m. The inequality
norm(u)^k <= k!/delta^k * exp(delta*(abs(u0)+abs(u1))) supplies every polynomial
weight. The derivative is the same pullback applied to the Schwartz gradient
(-a*f-x*d_x f,-b*f-y*d_y f); induction proves all derivative decay.

Fourier inversion of this full logarithmic Schwartz profile gives two-variable
Mellin inversion on real parts(a,b), with absolute vertical integrability.
All mixed dependence is retained. The line domain is encoded by positive-real
subtypes in Lean. Scratch71545 empty PASS; production audit pending.

For a,b>1 this profile can pair the full rational cone via the already proved
absolute HasSum, retaining both numerator cofactors and both label exclusions.
That physical pairing is being formalized next. Moving-line identities alone
do not prove uniform frequency-tail control or signed physical saving.

Final01ap: production86634 (positive lines) and4433 (actual pairing) empty
PASS. Axiom62726 all17 public declarations standard3 only. Index87535 passed;
API17/17 and both umbrella imports once. Lint67343:27 unrelated unreachable
modules,174warnings; no finding in these leaves, global NOT clean.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.HTGeometry.PositiveQuadrantMellinLines` | `quadrantLogSchwartz_apply`, `norm_quadrantMellinKernel`, `quadrantMellin_inversion`, `continuous_quadrantMellinKernel`, `integrable_quadrantMellin_inversion` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
