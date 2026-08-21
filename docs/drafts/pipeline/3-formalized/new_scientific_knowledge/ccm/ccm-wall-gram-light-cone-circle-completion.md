# CCM wall-Gram light-cone circle completion

## Status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.CCMActualHeadWallGramLightConeCircleCompletion`.
This classifies information lost by the scalar actual-head wall Gram; it does not yet provide the
global orientation lift or prove RH.

## New knowledge

For one prime-power wall, write `w` for critical Mellin mass, `C` for the reflected Mellin-wall
chord energy used by the actual-head wall-Gram producer, and `B` for literal positive-minus-negative
Suzuki light energy. Lean proves

\[
\left(w-\frac C2\right)+iB
=G(t,-t),
\]

where `G(t,-t)` is the full anti-diagonal critical wall Gram. Thus the actual scalar chord is its
cosine coordinate and wall-light incidence is exactly its missing sine coordinate.

The two coordinates obey the exact circle and discriminant laws

\[
\left(w-\frac C2\right)^2+B^2=w^2,
\qquad
B^2=C\left(w-\frac C4\right).
\]

Consequently scalar chord data determine orientation magnitude but not orientation sign. Negative
light is one sheet of this double cover:

\[
(2\|\ell_-\|^2-w)^2=C\left(w-\frac C4\right).
\]

This is sharper than the center no-go. The actual wall-Gram producer does not lack critical mass or
positive Gram geometry; it loses one binary phase sheet when the full anti-diagonal Gram is
projected to chord energy.

## Frontier consequence

Any successful Robin--Gamma--holonomy comparison must supply a coherent global lift of this local
two-sheet cover. Pointwise scalar estimates cannot choose the sheet. The previously formalized
positive quadratic/third-jet dressing supplies local orientation stiffness, suggesting that
holonomy should be tested as the sheet-selection connection while scalar Gamma reserve pays the
center mass.

## Lean audit

- direct leaf check: passed;
- exact module build: passed;
- umbrella import: wired, not built;
- capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
