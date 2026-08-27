# FZZ polynomial-incidence maximal-minor classification (2026-08-27)

Formalized `GaloisForLFunctions.RHTower.FZZCigarPuncturePolynomialIncidenceMinorClassification` and wired it into `RHTower.lean`.

For arbitrary rectangular `A : Matrix (Fin R) (Fin N) (Polynomial ℂ)`, define a dark mode at `z` as a nonzero vector in `ker A(z)`. Proved exact equivalence:

1. `A` has a dark mode at every positive real `XiC` zero;
2. every column-maximal minor polynomial of `A` is identically zero;
3. `A(z)` has a dark mode for every `z : ℂ`.

Forward direction: each dark mode roots every maximal minor; a Hardy packet of `natDegree(minor)+1` rules out any nonzero minor. Converse: all evaluated maximal minors vanish, so rectangular `mulVec` is noninjective at every energy by corpus theorem `matrix_mulVec_injective_iff_exists_submatrix_det_ne_zero`.

Interpretation: finite fixed polynomial FZZ/puncture incidence systems cannot select the Xi zero set. Xi-completeness collapses to universal all-energy darkness. Selective survivors must be infinite-dimensional, non-polynomial, moving-domain, or otherwise escape finite fixed polynomial incidence.

Direct check and targeted build passed. Six principal theorems audited with only `propext`, `Classical.choice`, `Quot.sound`. Card: `docs/drafts/pipeline/3-formalized/fzz-puncture-polynomial-incidence-minor-classification.md`. Frontier map remained read-only.