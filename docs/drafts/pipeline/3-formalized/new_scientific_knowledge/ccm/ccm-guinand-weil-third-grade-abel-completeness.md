# CCM third-grade cubic Abel completeness

- **ID:** `ccm-guinand-weil-third-grade-abel-completeness`
- **Stage:** 3-formalized
- **Route:** CCM-FU
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [CORPUS-NEW] [NO EXACT EXTERNAL COLLISION FOUND]`
- **RH used:** no
- **Computation used:** no
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMGuinandWeilThirdGradeAbelCompleteness.lean`

## Claim

Let `A_b(H)` be the cumulative literal prime-minus-polar third-grade source beyond positive wall
`b`, and Abel-damp it in logarithmic height. Three spectral derivatives cancel the inverse-cubic
grade exactly:

```text
(d/du)^3 Abel(A_b)(u)
 = 32 * [polar tail(u) - active prime L-series(u)].       (C72.1)
```

Finite prime head and compact polar head form an entire wall term, so the singular part of the
full critical Mellin defect is base-wall invariant. If `A_b` is uniformly bounded, `(C72.1)` gives
an analytic continuation of the regularized critical Mellin defect to `Re(s)>-1/2`; the identity
theorem and Xi logarithmic-derivative transport then exclude every upper-half-plane Xi zero.
Consequently

```text
bounded A_b                         -> RH,
completed third-grade convergence  -> RH.                (C72.2)
```

If RH fails, `A_b` exceeds every finite bound beyond every positive wall and no completed
third-grade rate can converge to a finite limit.

## Proof and significance

The proof constructs the actual atomic Dirichlet coefficients, literal polar Laplace channel,
all-order derivative identities, entire wall heads, half-plane analytic extension, and Xi
upper-half-plane exclusion. No abstract surrogate source is substituted.

C72 changes route diagnosis. Cofinal convergence is not a routine estimate waiting after the
geometry: it is already RH-complete. The higher principle is that source grade is a spectral
primitive order. Three derivatives return the undamped critical Mellin defect, while wall choice
changes only an entire head.

## Novelty audit

External search checked Suzuki screw-function papers, 2026 screw/Weil work, and finite
Guinand--Weil truncation work. No cubic Abel cancellation, entire wall-head decomposition, or
bounded-cumulative-source RH criterion matching C72 was found.

## Lean audit

Direct Lean check passes. Principal capstones depend only on `propext`, `Classical.choice`, and
`Quot.sound`.
