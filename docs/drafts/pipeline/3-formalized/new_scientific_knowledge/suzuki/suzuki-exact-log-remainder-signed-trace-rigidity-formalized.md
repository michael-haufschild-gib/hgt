# Exact log remainder signed trace rigidity

- **ID:** `suzuki-exact-log-remainder-signed-trace-rigidity`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-exact-log-remainder-signed-trace-rigidity.md`
- **Child card:** `./suzuki-weak-signed-half-log-trace.md` (same conclusion, weak hypotheses)
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/LogNormalEquationTrace.lean`,
  `formal/GaloisForLFunctions/HTGeometry/GammaTransportKernel.lean`,
  `formal/GaloisForLFunctions/HTGeometry/PenalizedMaximum.lean`,
  `formal/GaloisForLFunctions/HTGeometry/HalfLogCesaroAverage.lean`

## Formal content

The card's normal form `(1)` — the whole-line transport operator written with the *half-line*
remainder `(2)` plus the boundary term `q(L) F(L)` — is proved as

```text
gammaTransport_eq_halfLine_add_boundary :
  gammaTransport (zeroExtend F) L
    = (integral_{s>0} forwardDifference  (zeroExtend F) L s * k s
       + integral_{0<s<=L} backwardDifference (zeroExtend F) L s * k s)
      + (-log (1 - exp (-L))) * zeroExtend F L
```

for `L > 0`, with `zeroExtend F` continuous, Lipschitz and bounded. Its ingredients:

| Card | Lean |
|---|---|
| `(2)` the two one-sided remainders | `forwardDifference`, `backwardDifference`, `secondDifference_eq_add` |
| each remainder converges separately | `abs_forwardDifference_mul_kernel_le_near`/`_far`, `abs_backwardDifference_mul_kernel_le_near`/`_far`, `integrableOn_forwardDifference_kernel`, `integrableOn_backwardDifference_kernel` |
| the split into halves | `gammaTransport_eq_add` |
| `q(L) = integral_L^infinity k` | `integral_Ioi_gammaTransportKernel` |
| the boundary term | `integral_backwardDifference_split`, `integral_Ioi_gammaTransportKernel_reflect` |
| `(1)` itself | `gammaTransport_eq_halfLine_add_boundary` |
| `(3)` the trace exists | `tendsto_halfLogTrace_mollified` |

The separate convergence of the two one-sided remainders is the substantive point: the Lipschitz
bound cancels the kernel's simple pole on either side alone, so `(2)` is not merely a formal
rearrangement of a conditionally convergent integral.

Given `(1)`, the card's hypotheses are those of the child card, and its conclusion `(3)` is the
child's `(4)`, proved by `tendsto_halfLogTrace_mollified`.

No `sorry`, `axiom`, `opaque`, `unsafe`, RH premise, or numerical computation occurs. Every cited
declaration audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

As for the child card, the Lean development proves the trace for the mollified profile; the final
limit interchange in the mollification parameter is not formalized.
