# Matched wall-light third-jet transmutation

## Status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.CCMActualHeadMatchedWallLightThirdJetTransmutation`.
This identifies a positive source connection but does not yet prove its occurrence in the full
Robin--Gamma--holonomy trace or prove RH.

## New knowledge

Let `n = p^(e+1)`, let `M_n` be the matched polar oriented first moment, and let `q_n` be the
Guinand--Weil/Suzuki prime-entry third-jet scale. Lean proves the exact atomwise seam

\[
Q''_{p,e}(0)=D_nq_n,
\qquad
D_n=\frac{\pi}{8}\log(n)^4M_n>0.
\]

The factor `D_n` is forced by matching the already-formalized coefficients; it is not a fitted
observer parameter. This sharpens the prior qualitative observation that both channels first
appear at quadratic spectral order: matched wall-light contact is literally a positive diagonal
dressing of the corpus CCM/Suzuki third-jet connection.

For every finite prime/depth packet, Lean preserves labels and proves that its wall-light
connection is the corresponding sum of dressed literal prime-entry third-jet matrices. On the
zero-sum coefficient sector its quadratic form is exactly

\[
2\pi^2\Big(\sum_{(p,e)}Q''_{p,e}(0)\Big)
\Big(\sum_i \tau_i v_i\Big)^2.
\]

It is therefore positive semidefinite unconditionally, and strictly positive whenever the packet
is nonempty and the first centered clock moment is visible.

## Frontier consequence

The matched polar orientation channel and causal Gamma/Guinand--Weil cubic channel are no longer
separate analogies. They are the same universal Loewner direction after a source-defined positive
change of density. Remaining task is occurrence: transport this exact dressed connection into the
actual Robin--Gamma--holonomy rectangular trace while retaining the separate scalar center reserve,
then control the residual Schur debt uniformly.

## Lean audit

- direct leaf check: passed;
- exact module build: passed;
- umbrella import: wired, not built;
- capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
