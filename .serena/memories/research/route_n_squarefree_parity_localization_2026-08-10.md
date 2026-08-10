# Route N C17: squarefree parity localization

Date: 2026-08-10

## Formal module

`formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnSquarefreeParityLocalization.lean`
umbrella-wired in `RHTower.lean`.

Direct compile and explicit olean generation pass. Axiom audit uses only `propext`, `Classical.choice`, `Quot.sound`.

## Exact new bridge

For source dyadic split `k=e+2j`, squarefree parity probability has odds exactly `q`.

With Route N critical/twisted channel masses:
- `q0=p^-1`;
- `qt=p^(-1-2|t|)`.

Then:
- parity odds ratio `qt/q0=p^(-2|t|)` is exactly transverse modular cocycle;
- parity odds displacement `qt-q0=sign(t) Q_t(p)` is exactly signed Route N Krein charge;
- paired-depth residual odds ratio is cocycle squared;
- paired-depth residual difference `p^(-2-4|t|)-p^-2` is summable for every `t`;
- parity odds displacement is summable iff `t=0`.

## Scientific consequence

Nonsummable all-prime Route N modular class is entirely on source-canonical squarefree parity digit. Higher dyadic Wold tower is regular/ell1 correction. Corpus already has dyadic Wold/Boolean coupling; do not treat generic Boolean--Wold totalization as open.

Remaining Route N producer is narrowed to:

`squarefree singular source -> exceptional Gamma/Mellin/Cartier reporter -> every Xi principal conormal and multiplicity jet`

constructed before divisor evaluation, preserving parity modular marginal under Xi specialization, with no scalar Boolean entropy renormalization.

Docs updated:
- Route N card through C17, equations N.33-N.34.
- frontier Route N table/dossier open core corrected.
