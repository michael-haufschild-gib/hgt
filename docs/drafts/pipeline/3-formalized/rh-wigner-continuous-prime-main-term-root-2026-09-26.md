# Exact continuous prime main term of the critical Wigner kernel

- **ID:** rh-wigner-continuous-prime-main-term-root-2026-09-26
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), derived component / [BRIDGE]
- **Source:** `../1-in-progress/rh-full-source-sign-root-2026-09-26.md`, S8
- **Statement:** The continuous prime pairing of the literal critical Wigner pair kernel equals a negative decaying hyperbolic-secant power, for every real displacement.

## Goal and limits

Remove the continuous prime main term exactly before attacking the signed
arithmetic remainder in the mixed Mobius packet. This theorem neither
bounds that remainder nor proves source positivity or RH. It is not a
replacement for the full source-sign target.

## Gates

- [x] Well-posed and tied to the existing literal kernel.
- [x] Dependency-closed paper proof below.
- [x] Scratch and production source checks pass, default limits.
- [x] Named leaf build passes.
- [x] Final public-axiom audit: standard axioms only.
- [ ] Global formal lint: blocked by two unrelated unwired modules listed below.

## Exact statement

Let `C(t)=thetaCuspWignerPairKernel (1/2) t` and
`c=(2*pi)^(-1/2)*Gamma(5/2)/2`. Then

`integral_(v>0) exp(v/2)*(C(t+v)+C(t-v)) dv = -c*cosh(t)^(-5/2)`.

The public Lean theorem is
`RHTower.thetaCuspWignerPairKernel_continuousPrimeMainTerm` in
`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspWignerPrimeMainTerm.lean`.
The leaf is wired once in `formal/GaloisForLFunctions/RHTower.lean`.

## Complete paper proof [PROVED HERE]

Set `f(x)=cosh(x)^(-5/2)`, `d=f'`, and
`k=35/4*cosh(x)^(-9/2)-6*f(x)`. Differentiation gives
`d'=f/4-k`. The existing exact Helmholtz identity gives `C=c*k`.

From `abs(sinh x)<=cosh x`, `cosh x>=1`, and
`exp x<=2*cosh x`, obtain

- `0<f(x)<=4*exp(-2*x)`;
- `abs(d(x))<=5/2*f(x)`;
- `abs(k(x))<=15*f(x)`.

Thus `exp(v/2)*abs(k(t+v))` is bounded by a constant depending on t
times `exp(-3*v/2)`. This proves absolute integrability on `v>0`.
The same bound for f and d shows
`B(t,v)=exp(v/2)*(d(t+v)-f(t+v)/2)` tends to zero at infinity.
Its derivative in v is `-exp(v/2)*k(t+v)`. The improper fundamental
theorem therefore gives

`integral_(v>0) exp(v/2)*k(t+v) dv = d(t)-f(t)/2`.

Since f and k are even and d is odd, replacing t by -t gives

`integral_(v>0) exp(v/2)*k(t-v) dv = -d(t)-f(t)/2`.

Both integrals are absolutely convergent. Add them, obtaining `-f(t)`,
and multiply by c. Every analytic and algebraic step above is present
in the Lean proof.

## Novelty and whole-route audit

The existing `ThetaCuspWignerPairHelmholtzForm` supplies the differential
identity, not the exponential improper integral. Corpus deep/method
searches were used for the main-term and signed-error mechanisms. No
claim of literature priority is made. The proposed signed Stieltjes
error decomposition remains paper-only, and no remainder sign is proved.

Existing `CCMActualHeadCoherentQuantileGammaProducer` and
`CCMActualHeadCoherentQuantileGammaPhaseSquare` already combine the
arithmetic vectors before estimating; they leave the same source-sign
inequality. Recasting the present remainder in that framework is not a
new positivity result.

## Verification

- `/tmp/rh-s8-mainterm.lean`: exit 0; both theorem axiom reports standard only.
- Production source direct Lean check: exit 0, no diagnostics.
- Named leaf build: exit 0; no new-leaf warnings; existing dependency diagnostics replayed.
- Final public audit: exit 0; only `propext`, `Classical.choice`, `Quot.sound`.
- Global formal lint: exit 1 only for unrelated unwired `CircleSeamModulusMargin`
  and `XiZeroFreeDiscSeamModulusMargin`; no own-leaf or stale-index error.
- Audit logs: `/tmp/rh-s8-mainterm-build.log`, `/tmp/rh-s8-final-axioms.log`,
  `/tmp/rh-s8-lint.log`.
- No git, numerical mathematical experiment, or proof-limit override.
