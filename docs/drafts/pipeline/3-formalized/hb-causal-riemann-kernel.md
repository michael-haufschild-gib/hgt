# HB: characteristic kernel for the original BM wave

Status: 15 public theorems formalized. The integrated full-angular Green action and physical extinction remain unproved.

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCausalRiemannKernel`.

The construction addresses the unknown causal pulse horizon value in [the source contact reduction](../1-in-progress/hb-causal-onset-contact-cancellation.md). Its [full-angular circle-kernel application](../1-in-progress/hb-causal-horizon-circle-kernel.md) gives an analytical source-only response formula; the corresponding angular and integral admission theorem is not supplied by this module.

## Proved kernel

For `z>0`, the explicit function

```
P_nu(z) = ((z+1)/2)^nu * 2F1(-nu,-nu;1;(z-1)/(z+1))
```

uses a Gauss argument strictly inside the unit disk. Lean differentiates both the prefactor and the series, proves the displayed first and second jets are actual derivatives, and proves

```
(z²-1)P_nu''(z)+2z P_nu'(z)-nu(nu+1)P_nu(z)=0,
P_nu(1)=1.
```

No restriction on the complex degree is needed. With

```
Z(h,x,y)=[cosh(h)+sinh(x)sinh(y)]/[cosh(x)cosh(y)],
R_chi(h,x,y)=P_(-1/2+i chi)(Z(h,x,y)),
```

the exact coordinate derivatives satisfy

```
Z_h²-Z_x²=(Z²-1)/cosh(x)²,
Z_hh-Z_xx=2Z/cosh(x)².
```

Every point in the forward cone has `Z>=1`. Applying the chain rule to actual derivatives gives the original BM equation, for every complex angular frequency `chi`:

```
partial_h² R_chi-partial_x² R_chi
  +(1/4+chi²)/cosh(x)² * R_chi = 0.
```

The theorem is `D4BMCausalKernel.bmRiemannKernel_wave`. Its `CausalPoint` argument carries only the geometric inequality `|x-y|<=h`.

The characteristic value is one. The constructed causal image kernel is

```
G_D=(1/2)[1_(h>=|x-y|)R_chi(h,x,y)
          -1_(h>=|x+y|)R_chi(h,x,-y)].
```

Lean proves it vanishes before the source time and at the original AdS boundary `x=0`. The latter theorem retains both support indicators; no endpoint value is assigned independently of the kernel.

These statements do not yet prove the distributional source identity across the characteristic, differentiation of the forced Green integral, its full angular circle-mean realization, or equality with the corpus's admitted causal response. They provide the explicit kernel and its necessary differential and boundary identities for that next source-level proof.

## Verification

The scratch proof passed `lake env lean`. The exact leaf passed `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCausalRiemannKernel` in an isolated audit using existing dependency caches: one new module, 10 seconds, three Lake jobs. No dependency or umbrella build was run. All 15 new public theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The installed source and artifacts match the audited copies byte for byte. The module is imported by `RHTower.lean`.

`python3 scripts/formal_tools.py lint` passed. Generated catalogs were refreshed; the additional freshness check reported stale catalogs while other corpus work was changing the shared tree. No proof-debt or wiring error was reported. That repository-wide freshness check is not recorded as passing.
