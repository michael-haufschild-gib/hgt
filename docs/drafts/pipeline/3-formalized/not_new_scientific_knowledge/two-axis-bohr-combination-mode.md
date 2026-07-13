# Two-axis Bohr combination mode

- **ID:** two-axis-bohr-combination-mode
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/archimedean-generator-axis-mode.md`
- **Statement:** The product of two nonzero Bohr axis modes at distinct axes is the corresponding two-axis
  combination mode, and its exponent support is exactly those two axes.

## Goal
This banks the exact finite algebra behind the generator-axis-mode statement that combination modes arise
from the ring product. It does not formalize the analytic `partial_s` operator, infinite torus generator
domains, the digamma residue, or the C5-localization synthesis.

## Paper Proof
Let `p` and `q` be distinct axes, and let `a,b` be nonzero integers. The two-axis exponent vector is

`a delta_p + b delta_q`.

At any axis `r`, its coefficient is `a` if `r=p`, `b` if `r=q`, and `0` otherwise. Since `p != q` and
`a,b` are nonzero, its finite support is exactly `{p,q}`.

For Bohr characters `e_m(x)=product_i x_i^(m_i)`, the already finite product law gives

`e_{m+n}(x)=e_m(x)e_n(x)`.

Taking `m=a delta_p` and `n=b delta_q` gives

`e_{a delta_p + b delta_q}(x)=e_{a delta_p}(x)e_{b delta_q}(x)`.

Thus multiplying two distinct nonzero axis modes produces a genuine two-axis combination mode.

## Gates
- [x] 0 -> 1  in-progress: two-axis support/product lemma extracted from the generator-axis-mode card.
- [x] 1 -> 2  fully-proven: paper proof above by coordinate evaluation and finite Bohr-character
  multiplicativity.
- [x] 2 -> 3  formalized: Lean theorems `twoAxisMode_support_eq`,
  `bohrCharacter_twoAxis_product`, and `twoAxisMode_ne_zero` in
  `formal/GaloisForLFunctions/HTGeometry/BohrGenerators.lean`; scratch `#check` / `#print axioms`, `lake build`, and
  `scripts/check_axioms.sh` pass.
- [ ] 3 -> 4  publication-ready: cite as the finite combination-mode certificate in the generator-level
  C5-localization note.

## Log
- 2026-06-19 - Leaner split this exact finite lemma from `archimedean-generator-axis-mode`. The parent card
  remains in `2-fully-proven` because the analytic generator, infinite torus/generator language, digamma
  residue, and structural C5-localization claims are not fully Lean-formalized.
