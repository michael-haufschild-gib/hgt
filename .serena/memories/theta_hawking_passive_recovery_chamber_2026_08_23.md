# Theta-Hawking passive recovery chamber (2026-08-23)

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBackreactionRecoveryChamberEndpoint.lean`; integrated into `RHTower.lean` and `docs/reports/endpoints.md`.

## Audit verdict
- Exact max-determinant/maximum-entropy selection of `r*=Kxy*Kyz/Kyy` is Dempster covariance selection / Gaussian Markov recovery (literature bridge), not new.
- Strong subadditivity gives nonnegative conditional mutual information, not Markov/Petz saturation. Generic Hawking entropy does not select `r*`.
- Bianchi–Smerlak (arXiv:1404.0602) permits and for nontrivial unitary conformal vacua requires negative energy phases. Existing theta QEI already proves a negative central pulse and controls only renormalized sampled flux.
- Kumar–Reyes–Wintergerst (arXiv:2310.03483) supplies genuine dynamical moving-mirror backreaction but no tripartite covariance completion selection.

## New unconditional survivor
For `B=Kyy>0`, existing exact identity
`D(r*)-D(r)=B(r*-r)^2` yields:
1. Complete passive chamber:
   `D(r)>=0 iff B(r*-r)^2 <= D(r*)`.
2. `r*` uniquely maximizes determinant.
3. If raw `D(raw)<0` and repaired `D(s)>=0`, then
   `(s-r*)^2 < (raw-r*)^2`.
4. Repair direction is strictly oriented:
   `0 < (s-raw)*(r*-raw)`.
Thus any passive repair, not only exact max-entropy completion, forces directed remote-shell mixing toward the Markov center.

Affine repair `R_strength(raw)=raw+strength*(r*-raw)` has:
- composition `strength1+strength2-strength1*strength2`;
- exact determinant gain `B*strength*(2-strength)*(r*-raw)^2`;
- strict gain for `0<strength<=1` away from center.

Specialized to coefficient-faithful selective Hawking gain and actual causal Hardy stimulated scattering. For any offcritical orbit and sufficiently large rapidity, every passive repair strictly contracts and is oriented toward `r*`.

## Verification
15 new declarations compile and use only `propext`, `Classical.choice`, `Quot.sound`. No forbidden declarations. Lint reaches umbrella integration but fails on unrelated pre-existing unreachable modules. Temp files removed; no git used.

## Remaining open core
Derive a chamber-entering contraction globally from actual nonlinear theta-mirror anomaly/backreaction dynamics. Exact max-entropy selection is unnecessary. The required physical theorem is weaker and sharper: backreaction must reduce conditional-correlation defect enough to cross passive boundary in every tilted sector.