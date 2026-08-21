# Matched CCM wall-light quadratic jet

## Status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.CCMActualHeadMatchedWallLightQuadraticJet`.
This proves a new local source law; it does not yet identify that law with the actual
Robin--Gamma--holonomy trace or prove RH.

## New knowledge

For every prime-power wall `n = p^(e+1)`, define the oriented source coupling

\[
Q_{p,e}(\xi)=
(\|\ell_+(2\pi\xi;p,e)\|^2-\|\ell_-(2\pi\xi;p,e)\|^2)S_n(\xi),
\]

where `S_n` is the odd matched prime--polar sine profile. Lean proves exact derivative laws for
both factors and differentiation under the defining interval integral for `S_n`. At spectral
center,

\[
Q_{p,e}(0)=Q'_{p,e}(0)=0,
\qquad
Q''_{p,e}(0)=
2w_n(2\pi\log n)M_n>0,
\]

where `w_n` is critical Mellin mass and `M_n` is the strictly positive oriented first moment of
the matched polar cell.

Thus the oriented source channel is invisible to value-level and first-jet tests at center but
survives as strict positive quadratic contact. The earlier pointwise center obstruction was not
evidence that source incidence disappears; it was evidence that the relevant observable lives
one derivative grade higher.

## Frontier consequence

Any proposed scalar pointwise domination of raw negative light still fails. A viable actual-trace
transport may instead recover negative-light orientation through a second spectral jet, while a
separate scalar channel carries center reserve. Corpus causal-Gamma modules also expose a
quadratic spectral factor through a third boundary jet, making an exact coefficient match a
concrete next conjecture. That cross-module identification is not claimed here and must be proved
or sharply ruled out in Lean.

## Lean audit

- direct leaf check: passed;
- exact module build: passed;
- umbrella import: wired, not built;
- capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
