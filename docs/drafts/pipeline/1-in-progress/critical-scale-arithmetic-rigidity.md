# Arithmetic rigidity at critical scale

- **ID:** critical-scale-arithmetic-rigidity
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-3110/astra.md`, section 6
- **Statement:** Develop source-specific joint successor–dilation rigidity and relative signed-energy estimates at growing arithmetic scales.
- **Disposition:** Paused at user request. Existing Lean drafts and direct audits are complete; no further research authorized.

## Goal

Construct the arithmetic tools needed to control mixed complete-Weil interactions, conductor escape, literal Chebyshev near bands, signed prime surplus, producer precision, arithmetic conjugation, and integer-index resolution. The full goal includes answering the source questions, not merely formalizing their equivalent criteria.

## Mathematical foundation

Prime-dilation packet energy has exact weights `log m + tameDifferent m`. Complete conductor energies and joint shell–pole cancellation are available. The missing input is their source-specific relative control at growing scales, including mixed interactions and boundary terms.

## First research problem

Determine the strongest unconditional rigidity and mixed-energy consequences of the exact prime-dilation identity. Search existing polarization, kernel, confinement, and finite-horizon results before selecting a new theorem. Use the actual Ramanujan packet source; do not assume the desired coercivity.

## Programme requirements

- Own folder and sibling umbrella: `CriticalScaleArithmeticRigidity`.
- Foundational README explains objects, mechanisms, traps, questions, corpus interfaces, and contribution criteria.
- Every new mathematical result receives a dependency-closed Lean proof and a direct foreground audit.
- No computational experiments, full builds, raised proof limits, or unproved analytic inputs.
- Maintain the complete eight-question scope in the README. Mark a question answered only by the corresponding source theorem.

## Open input

No relative complete-form estimate at an RH-complete schedule, near-band power saving, or signed prime-surplus bound is asserted. These remain objectives, not premises.

The packet and prime-generator results have not improved the complete-Weil positivity range, a zero-free strip, or the critical-line census. Their extension to the full signed form is unproved.
