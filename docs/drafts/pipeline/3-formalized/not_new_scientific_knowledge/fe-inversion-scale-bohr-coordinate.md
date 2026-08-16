# FE inversion-scale Bohr coordinate

- **ID:** fe-inversion-scale-bohr-coordinate
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `universal-prime-side-orthogonality.md` section 3
- **Statement:** In the Bohr coordinate `x_p = p^{-s}`, the functional-equation involution `s |-> 1-s`
  sends `x_p` to `p^{-1} * x_p^{-1}`.

## Goal
This banks the exact coordinate identity behind the abelian case's archimedean-twist claim. It does not
formalize torus representation categories, compact-form uniqueness, the general Satake quantifier, Weil
positivity, or RH.

## Paper Proof
For a positive real base `p`, write `x_p = p^{-s}`. Under the FE map `s |-> 1-s`,

`x_p` becomes `p^{-(1-s)}`.

Since `-(1-s) = s-1`, the complex-power subtraction law gives
`p^{s-1} = p^s * p^{-1}`. Also `p^s = (p^{-s})^{-1}` for nonzero `p`. Therefore

`p^{-(1-s)} = p^{-1} * (p^{-s})^{-1}`.

## Gates
- [x] 0 -> 1  in-progress: FE coordinate identity extracted from the abelian orthogonality argument.
- [x] 1 -> 2  fully-proven: paper proof above by complex-power subtraction and inversion for a positive base.
- [x] 2 -> 3  formalized: Lean theorem `cpow_inversion_scale` in
  `formal/GaloisForLFunctions/Core.lean`; scratch `#check`/`#print axioms`, `lake build`, and
  `scripts/check_axioms.sh` pass.
- [ ] 3 -> 4  publication-ready: cite as the coordinate certificate for the abelian FE twist in the seam
  exposition.

## Log
- 2026-06-19 - Leaner split this exact coordinate identity from
  `universal-prime-side-orthogonality` section 3. The parent card remains in `2-fully-proven` because the
  torus-representation wrapper, compact-form uniqueness, general Satake quantifier, Weil positivity, and RH
  are not fully Lean-formalized.
