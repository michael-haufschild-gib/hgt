# CCM prime-entry third jet / Suzuki wall-field weld

- **ID:** `ccm-guinand-weil-prime-entry-wall-field-weld`
- **Stage:** 3-formalized
- **Route:** CCM-FU
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [CORPUS-NEW] [NO EXACT EXTERNAL COLLISION FOUND]`
- **RH used:** no
- **Computation used:** no
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMGuinandWeilPrimeEntryWallFieldWeld.lean`

## Claim

For `k=p^(e+1)`, entry aperture `a_k=log(k)/2`, Suzuki wall field `W_k(t)`, and CCM cubic
prime-entry rate `q_k`, Lean proves the phase-complete identity

```text
q_k exp(i t log k) = (4/a_k^3) W_k(t)^2.                 (C69.1)
```

At zero height,

```text
q_k = 4 |W_k(0)|^2/a_k^3 > 0.                            (C69.2)
```

Consequently the complete cubic Loewner matrix is the universal third-jet matrix scaled by
normalized Suzuki wall-field energy, and on every centered packet its quadratic form is

```text
8 pi^2 |W_k(0)|^2/a_k^3 * (first clock moment)^2.        (C69.3)
```

## Proof and significance

Von Mangoldt critical mass is exactly the square of Suzuki's bare wall amplitude. The forced
conversion `log(k)=2a_k` turns `32/log(k)^3` into `4/a_k^3`; Suzuki's far-hinge square identity
retains the full spectral phase. Thus C67's agreement in jet order was not analogy: both objects
are the same atomic source in symmetric-square coordinates.

This closes the local CCM--Suzuki bridge. Remaining obstruction is global completion of all
prime, polar, and Gamma channels, not atomic calibration.

## Novelty audit

Internal search found no earlier phase-complete square identity or matrix consequence. External
collision search checked Suzuki's 2022 screw-function papers and 2026 screw/Weil paper; they supply
the screw and wall-side context but no exact inverse-cubic CCM symmetric-square weld was found.

## Lean audit

Direct Lean check and targeted module build pass. Principal theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.
