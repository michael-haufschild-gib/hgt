# QNM-conserved reflected-pair response no-go

## RH chain closed

Stationary reflected-pair response → nontrivial BM cancellation → shared Ward zero →
HB / FZZ-P / RBH / PW-B → RH.

The producer premise at the first arrow is impossible for every finite-packet bilinear kernel
satisfying QNM-generator conservation.

## Formal result

`hbXiPeierlsQNMConservedNontrivialReflectedPairResponseProducerRouteKilled` is unconditional.
QNM-generator conservation implies spectral-fibre locality. Off the critical wall, a Xi copy and
its functional-equation reflection occupy different fibres, so the reflected coefficient is zero.
On the wall, the literal BM polarized source amplitude is zero. Therefore the complete
source–kernel–radial reflected-pair response charge vanishes for every Xi copy.

This excludes the corpus's division-free cross-pair compensator whenever it is required to arise
from stationary QNM-conserved packet dynamics.

## Forced survivor

A nonzero reflected-pair producer must break QNM time conservation or cease to be a finite-packet
bilinear-kernel response.

## Novelty and verification

Corpus deep search found no prior theorem combining QNM-generator conservation with the Xi
functional-equation pair and BM source extinction. Literature audit through August 2026 found
general QNM conserved-current/orthogonality results, but no such Xi/RH reflected-pair no-go; see
[Green et al., arXiv:2210.15935](https://arxiv.org/abs/2210.15935).

Verified with:

```text
lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMQNMConservedReflectedPairResponseNoGo.lean
```

Result: exit 0 in 19.96 seconds. No `lake build` was run.
