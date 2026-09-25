# Direct finite-part challenge: frozen after discovery

Discovery exposed one complete-matrix determinant candidate at `rho = 0.880795460232595309035783338060080245984264806920089923751085 + 0.634145625801657837777746285670772699883161431185172620706643 i`. This protocol was frozen before any direct-integral value was computed.

Question: does that candidate survive evaluation from the literal first-subtracted integral, bypassing both hypergeometric continuation and endpoint binomial series?

Independent object: for each branch/reader, compute `F(0)/(w+1) + integral_0^1 z^w(F(z)-F(0)) dz` after the endpoint-smoothing substitution `z=u^4`, then divide by `2 B(3,w+1)`. No hypergeometric function or endpoint series is called.

Experiments: independent complex root refinements at 70, 110 and 150 digits; direct matrix and source-mixture residuals; 48-point local argument contour at 80 digits; nonzero shifted anchor; comparison against frozen discovery matrix. Root and contour computations run in separate processes, at most 14 workers.

Falsifier: failure to converge to the frozen root, a determinant residual above `10^(-0.55*dps)`, non-unit local winding, or matrix-entry disagreement above `10^(-0.5*dps)`. Failure rejects the candidate. Agreement validates a numerical zero, not a certified enclosure.

Interpretation remains factor-level. Full angular source, onset, causal corrections, contact terms, SS/SV/VV action and every spacetime face are absent from this object and remain unknown. No spectral control is called a Xi zero. One 570-second guard; preserve partial output; no scan enlargement.

Scientific-method mechanics: change representation, attack candidate as artifact, perturb via contour/anchor, mix precision and source amplitudes, retain positive null-mixture classification if candidate survives.
