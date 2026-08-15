# CCM third-grade subcubic completeness

- **ID:** `ccm-guinand-weil-third-grade-subcubic-completeness`
- **Stage:** 3-formalized
- **Route:** CCM-FU
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [CORPUS-NEW] [NO EXACT EXTERNAL COLLISION FOUND]`
- **RH used:** no
- **Computation used:** no
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilThirdGradeSubcubicCompleteness.lean`

## Claim

For every real `alpha<3`, positive wall `b`, and constant `C`, the tail estimate

```text
|E(h)| <= C h^alpha  for h>b                             (C73.1)
```

forces

```text
E(H)/H^3 -> 0,
integral_b^infinity |96 E(h)/h^4| dh < infinity.         (C73.2)
```

Hence the completed-error flux and completed third-grade window have explicit finite limits, and
C72 gives RH. In particular a quadratic bound is sufficient. Contrapositively, if RH fails then,
for every `alpha<3`, every positive wall, and every `C`, some later height satisfies

```text
C h^alpha < |E(h)|.                                      (C73.3)
```

## Proof and significance

The endpoint majorant is `C H^{-(3-alpha)}`. The bulk majorant is
`96 C h^{alpha-4}`, integrable exactly when `alpha-4<-1`. Both conditions meet at the same strict
threshold `alpha<3`, revealing a grade--growth duality rather than a special quadratic trick.

C73 gives a concrete replacement target for vague cofinal orientation: any source theorem placing
the literal completed error below a fixed subcubic envelope closes CCM-FU. It also proves that such
a theorem cannot be unconditional unless it proves RH; under non-RH, subcubic escape is forced.

## Prior and novelty audit

Schoenfeld's classical RH-conditional bound for `psi(x)-x` is a neighboring result, but direct
absolute Volterra integration loses one logarithmic grade and does not state C73's completed-error
flux theorem. Suzuki and 2026 Guinand--Weil searches found no real-exponent third-grade threshold
or escape law matching `(C73.1)--(C73.3)`.

## Lean audit

Direct Lean check passes. Scratch axiom audit of all capstones reports only `propext`,
`Classical.choice`, and `Quot.sound`; targeted module audit is pending final verification.
