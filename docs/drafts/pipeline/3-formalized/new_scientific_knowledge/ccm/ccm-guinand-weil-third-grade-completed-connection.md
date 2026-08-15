# CCM Guinand--Weil completed third-grade connection

- **ID:** `ccm-guinand-weil-third-grade-completed-connection`
- **Stage:** 3-formalized
- **Route:** CCM-FU
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [CORPUS-NEW] [NO EXACT EXTERNAL COLLISION FOUND]`
- **RH used:** no
- **Computation used:** no
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilThirdGradeCompletedConnection.lean`

## Claim

The prime-entry cubic jet forces the continuous weight `F(h)=32/h^3`. For every `0<b<=H`, exact
finite Stieltjes integration by parts gives

```text
prime3(b,H)-polar3(b,H)
 = 32 E(b)/b^3 - 32 E(H)/H^3
   - integral_b^H 96 E(h)/h^4 dh,                        (C70.1)
```

where `E=criticalMellinCompletedError`. Adding the literal Gamma channel gives the completed
third-grade rate. Its Gamma tail is absolutely integrable, hence

```text
completed third-grade converges
  iff completed-error cubic flux converges.              (C70.2)
```

## Proof and significance

Finite prime staircase and continuous polar source are integrated by parts on the same positive
wall. Their exponential-size main terms cancel before taking any limit. The remaining Gamma
density is exponentially decaying after inverse-cubic weighting.

C70 kills arbitrary cofinal normalization: the local cubic incidence uniquely fixes the global
grade. It also isolates one honest obstruction—endpoint/flux behavior of `E`—with no separate
prime, polar, or Gamma ambiguity.

## Novelty audit

Internal search found no prior exact shifted Stieltjes law at the forced cubic grade. External
search found classical Guinand--Weil/screw formulas but no formula matching `(C70.1)` or its exact
cofinal obstruction classification.

## Lean audit

Direct Lean check and targeted module build pass. Capstones use only standard Lean axioms.
