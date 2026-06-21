# Penrose R19 — observed-volume covariance sign

NODE: relativistic light-cone averaging; the observed volume element is perturbed and affects averages.

Transfer:
- Trace: `X_sigma(t)=log(1+|zeta'(sigma+it)/zeta(sigma+it)|)`.
- Observable: robust `O=robust(X)`.
- Observed-volume perturbation: local differential variation of `O`, primarily gradient and curvature.
- Compare coordinate mean, observed weighted mean `sum(WO)/sum(W)`, and reversed volume weight.

Step 9 reverse-weight evidence:
- `sigma=.3`, `[100,170]`:
  - true `bias+ +0.139`, `bias- -0.148`
  - finite `-0.125`, `+0.140`
  - random `-0.077`, `+0.084`
- `sigma=.5`, `[100,170]`:
  - true `+0.329`, `-0.381`
  - finite `-0.199`, `+0.208`
  - random `-0.077`, `+0.086`
- `sigma=.7`, `[100,170]`:
  - true `+0.097`, `-0.111`
  - finite `-0.206`, `+0.218`
  - random `-0.080`, `+0.087`
- Right strip, `sigma=1.2`, `[100,170]`:
  - true `-0.138`, `+0.169`
  - finite `-0.130`, `+0.145`

Step 11 missing-lemma check:
- Candidate lemma: value-gradient observed-volume covariance sign.
- `sigma=.3`, `[100,170]`:
  - true grad/curv/top30 bias `+0.502 / +0.771 / +0.569`
  - finite `-0.244 / -0.599 / -0.292`
  - random `-0.190 / -0.447 / -0.287`
- `sigma=.5`, `[100,170]`:
  - true `+0.208 / +0.866 / +0.776`
  - finite `-0.364 / -0.515 / -0.603`
  - random `-0.248 / -0.479 / -0.304`
- `sigma=.7`, `[100,170]`:
  - true `+0.270 / +0.287 / +0.507`
  - finite `-0.439 / -0.560 / -0.689`
  - random `-0.233 / -0.418 / -0.209`
- `sigma=1.2`, `[100,170]`:
  - true `-0.443 / -0.477 / -0.475`
  - finite `-0.409 / -0.516 / -0.466`

Verdict:
- Counted as non-promptable experimental finding.
- Posted to `#research` id `761`.
- Interpretation: in the analytic critical strip, true `zeta'/zeta` places high values on high-gradient/high-curvature observed-volume regions; finite/random controls put high gradients mostly away from high values. In the right strip true and finite share the finite-Euler sign.
