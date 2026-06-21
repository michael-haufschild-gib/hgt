# Penrose R20 — phase-space caustic wrong-momentum result

NODE: resolve caustic surfaces in phase space, not only their projections.

Transfer:
- Projection coordinate: `O(t)=robust(log(1+|zeta'/zeta|))`.
- Momentum coordinate: phase of a log-derivative trace.
- Invariant: signed lifted area `int O dP`, compared to circular phase shifts.

Step 9:
- True analytic phase lift has a large critical-strip signed area.
- Finite-prime momentum lift does not resolve true projected caustics.

Key values:
- `sigma=.5`, `[100,170]`:
  - true self area `+2.3487`, shift z `18.92`
  - true amplitude + finite momentum area `-0.7874`, z `-0.54`
- `sigma=.5`, `[500,570]`:
  - true self area `+2.3301`, z `11.41`
  - true amplitude + finite momentum area `-0.7721`, z `-0.55`
- `sigma=.3`, `[100,170]`:
  - true self area `+0.3278`, z `11.11`
  - true amplitude + finite momentum area `-0.1971`, z `-0.38`
- `sigma=.3`, `[500,570]`:
  - true self area `+0.2646`, z `12.41`
  - true amplitude + finite momentum area `-0.1541`, z `-0.28`

Step 11 fake-proof cutoff sweep:
- Fake proof: finite-prime phase should become the right momentum as cutoff grows.
- `sigma=.5`, `[100,170]`: true area `+2.2848`; finite cutoffs:
  - `P=5`: `-0.5785`
  - `P=11`: `-0.5740`
  - `P=23`: `-0.6118`
  - `P=47`: `-0.9364`
  - `P=97`: `-1.1085`
- `sigma=.5`, `[500,570]`: true area `+2.1933`; finite cutoffs:
  - `P=5`: `-0.4696`
  - `P=11`: `-0.6188`
  - `P=23`: `-0.7311`
  - `P=47`: `-0.9331`
  - `P=97`: `-1.0559`
- `sigma=.3` also stays opposite-signed across cutoffs.

Verdict:
- Counted as non-promptable experimental finding.
- Posted to `#research` id `762`.
- Interpretation: finite-prime phase is the wrong momentum coordinate for true critical-strip projected caustics; the true analytic phase-space lift has a stable signed area that finite Euler phase fails to approximate in the tested critical windows.
