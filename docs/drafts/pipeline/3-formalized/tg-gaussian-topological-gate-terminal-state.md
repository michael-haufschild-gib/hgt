# TG — Terminal state: twelve RH forms, shift no-go, unconditional baseline

- **ID:** TG-CAP-2
- **Stage:** 3-formalized
- **Type:** CAPSTONE (Lean)
- **Statement:** (a) 12-way TFAE: RH; central budget; eventual negativity; explicit −1/10+32√y;
  Gaussian Chebyshev; sign abscissa ½; spectral Bohr form; anchored cubic sub-unit gate; Route-P capacity
  law; ∫₀^U G² ≤ K(U+1); ∫₀^U G² ≤ K_ε e^{εU}; differenced budget of ζ(s)/ζ(s+½).
  (b) Unconditional: |G(u)| ≤ C exp(u/4 − u·η_VK(u)/2); for every 0<a<½ the Eisenstein ζ(s−a)ζ(s+a)
  central budget fails.

## Lean
`RHTower/GaussianTopologicalGateTerminalState.lean`, wired after GaussianCentralGapZeroFreeRegionBudget.
`riemannHypothesis_tfae_gaussianTopologicalGateExtended`, `gaussianTopologicalGate_terminalState`.
Axioms [propext, Classical.choice, Quot.sound].

## Reading
TG reading side, shift-algebra no-go and unconditional producer baseline are formally closed.
Producer ladder: exponent 1/4 (VK, proved) → < 1/4 (zero-free strip, open) → 0 (RH).
Walls blocking producers (corpus catalogue): 1 (√x one-sided counting), 5 (no Frobenius), 6 (Gaussian
positivity = PD pole form, dominant), 9 (temperedness, now formal in TG).
