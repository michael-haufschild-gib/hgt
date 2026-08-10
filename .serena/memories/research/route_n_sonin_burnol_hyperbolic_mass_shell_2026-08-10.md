# Route N C24-C25: flat/nonmetric Sonin-Burnol mass shell (2026-08-10)

Route N is terminalized; these are positive survivors and no-go refinements, not RH.

New Lean modules, umbrella-wired:
- `RHTower/HedenmalmGammaSewnSoninHermitianNonmetricity.lean`
- `RHTower/HedenmalmGammaSewnBurnolHolonomyMassShell.lean`

Let `D_t(p)=1-p^(-2|t|)` and `A_t(p)=p^(2|t|)`. Define Hermitian nonmetricity
`M_t(p)=D_t(p)^2/(1-D_t(p))`.

C24 proves:
- `M>=0`, `M=0 iff t=0`, and `M(-t)=M(t)`.
- `M=A+A^-1-2`.
- On the right half-strip, the reciprocal Sonin-character squared amplitudes sum to `2+M`.
- At every actual strict-right zeta zero and every aperture level, literal forward/inverse co-Poisson edge-image energy is `(2+M)||y_j||^2`.
- For initial aperture `<1`, `y_0` is nonzero, hence paired-edge energy is strictly greater than `2||y_0||^2`.

This kills the mixed-curvature pivot: `GammaCoPoissonSoninQuadrantFlatness.lean` already proves the two-path connection is flat on the entire quotient. Flatness and Hermitian metric compatibility are independent; off-line obstruction is nonmetricity, not curvature. Reflection preserves M.

C25 connects Route R. At prime dilation ratio and any actual strict-right zeta zero, normalized Burnol holonomy is
`H=A-A^-1=D(2-D)/(1-D)` and satisfies exact hyperbolic mass shell
`H^2=M(M+4)`.
Thus Route N positive fracture and Route R signed Burnol holonomy are trace/orientation coordinates of one reciprocal transport, not independent RH pressures. Reflection reverses H and preserves M.

Verification:
- direct `lake env lean` passed for both modules;
- explicit oleans generated;
- focused axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`.

Docs updated:
- failed Route N card with C24-C25 `(N.50)`-`(N.53)`;
- frontier map Route N dossier;
- literature exchange Route N verdict.

Research consequence: any viable producer must enter before reciprocal determinant-one transport, via independent source incidence/current structure. Do not combine Route N and Route R reporters as if two inequalities.