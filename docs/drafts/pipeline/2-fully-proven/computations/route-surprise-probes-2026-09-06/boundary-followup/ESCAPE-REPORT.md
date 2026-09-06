# Positive curvature does not protect the enlarged source class

**Status:** B1 is rejected by independently validated numerical counterfactuals. Ten exact algebraic theorems are formalized separately. The literal theta inequality and RH remain open. This investigation is paused while research tests producers that do not rely on positivity.

## Result

B1 asserted that the basic source gates and positive lower-transport curvature force nonnegative complete compensation for positive tails supported on `[3,infinity)`, with the actual theta tail mass at the left endpoint. An escaping atom defeats that implication even when the actual conditional first moment is also preserved.

Take left scale `A0=6`, displacement `t=.52`, homotopy parameter `lambda=0`, and remote node `g=10^12`. Let `tau` be the actual higher-tail Laplace mass at this endpoint, approximately `3.0459959489440221e-7`, and let `m` be its actual conditional first moment, approximately `3.04444444444690394`. Replace the conditional distribution by atoms at `3,g`, with weights `1-epsilon,epsilon`, where `epsilon=(m-3)/(g-3)`.

The complete source calculation gives:

| Quantity | Value |
|---|---:|
| Complete third compensation | `-2.78417339182079615e-12` |
| Lower-transport second derivative | `+2.47035184368656555e-10` |
| Normalized curvature | `4.79455514` |
| Required critical curvature | `316.0684483` |
| Replacement conditional second moment | about `4.4444444456e10` |
| Actual conditional second moment | about `9.2864197531` |

All B1 gates hold numerically. Independent differentiation of the original compensation and the analytic jet formula agrees to relative errors about `3.5e-82` and `1.7e-142` at 90 and 150 digits. Doubling the actual theta mass/mean cutoff from 40 to 80 preserves the displayed results. These checks support rejecting the hunch; they are not interval certificates or Lean proofs of the numerical signs. No zero data or RH assumption enters the computation.

Continuation in `g` brackets a compensation sign change near `1.5207523539e10` and a curvature sign change near `3.9240613709e14`. Thus the failure is not confined to an unresolved near-zero numerical boundary. Uniqueness of these crossings is not asserted. Parameters and results are in `escape-validation.json` and `escape-profile.json`.

## Mathematical interpretation and exact residue

Unit positive mass, a fixed support gap, and a fixed first moment permit unbounded second moments. An exact family has nodes `3,4+z^2` and weight `w=(c^2/(1+c^2))/(1+z^2)` at the second node. Its first moment is `3+c^2/(1+c^2)` and its second moment is `9+(c^2/(1+c^2))(7+z^2)`. Lean proves both identities, weight bounds, and an unconditional existence theorem with fixed mean `16/5` and second moment above any prescribed real ceiling.

The same module proves the exact affine response of the complete compensation to a formal left-endpoint curvature increment, retaining both mixed coefficients. This explains which information a mass/mean description omits. A finite atom intervention also changes other endpoint jets, so the formal single-jet perturbation is not asserted to be the entire numerical deformation.

These results exclude the tested enlarged-class explanation. They neither falsify the literal theta source inequality nor prove that every positivity or spectral route must fail. The actual arithmetic tail has additional restrictions not preserved here.

## Domain correction

The structural theorem requires **left** scale `A(u-t)>=6`, not merely center scale `A(u)>=6`. In the earlier boundary batch, 270 of 450 curvature specifications satisfy the actual structural condition; all 372 bracketed curvature roots belong to that domain. The slope batch has 162 structural specifications and 162 admissible roots, with smallest observed reserve ratio about `3.12e8`. The smaller ratio about 82,158 belongs to the extended domain with left scale `pi`. `domain-audit.json` preserves this classification; its extra displayed ratio digits are not a precision claim.

## Reproduction and formal audit

Run `interior_attack.py`, `escape_continuation.py`, `verify_escape.py`, and `escape_profile.py` on the authorized Runpod under `/root/rh-route-surprise-20260906/boundary-followup`, with the parent helpers available. The bounded interior search selected remote atoms at its search cap; continuation then exposed the failure, and an independent simple witness replaced the optimizer output. Commands used 120-second caps, at most eight processes and one BLAS thread each; completed batches took seconds. Scripts and results are downloaded here.

`ThetaCuspC5SpectralMomentTransport.lean` passed scratch and source `lake env lean` checks and its named-module final build. Its ten theorem axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into `RHTower.lean`; no umbrella build was run. No numerical result is a Lean premise. The parent report records repository lint separately.
