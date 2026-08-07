# Suzuki causal-depth rectangular Carathéodory growth — formalization certificate

- **Stage:** 3 — formalized in Lean 4
- **Paper theorem:**
  `./suzuki-causal-depth-rectangular-caratheodory-growth.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiCausalDepthRectangularCaratheodoryGrowth.lean`
- **Umbrella import:**
  `formal/GaloisForLFunctions/RHTower/RiemannHypothesisSOTA2026.lean`
- **Scientific status:** `[LEAN-PROVED] [SOURCE-SPECIFIC] [NOVELTY UNVERIFIED] [NOT RH]`
- **RH used:** no
- **Computation used:** no

## Formal theorem surface

Module proves unconditionally:

- `causalDepthRadialRealPart_strictAntiOn`: for `0<c<1` and every real `s<=1`,
  `(1-x)^2(1-cx^2s)/(1-2cx^2s+c^2x^4)` is strictly decreasing on `(0,1)`; Lean strengthens
  original phase-interval statement because no lower bound on `s` is needed;
- source radius, aperture disk coordinate, and base amplitude have exact required strict signs;
- `suzukiCriticalApertureDepthFusedDemodulatedAtom_eq_radial`: causal depth resolvent has exact
  positive-amplitude radial normal form after forced half-prime-log phase removal;
- `re_suzukiCriticalApertureDepthFusedDemodulatedAtom_strictMono`: demodulated real part strictly
  increases with observer aperture at every real height;
- `re_suzukiCriticalApertureDepthFusedAtom_rectangle_demodulated_pos`: every positive fixed-width
  causal observer rectangle has strictly positive demodulated real part;
- `xiGammaEulerHeightBoundaryFeature_critical_depth_zero_eq_amplitude_mul_star_phase`: demodulator
  is exactly actual unstarred depth-zero Gamma--Euler boundary coordinate up to positive amplitude;
- `re_xiGammaEulerHeightBoundaryFeature_mul_fusedAtom_rectangle_pos`: literal Gamma--Euler
  boundary pairing with each causal aperture rectangle has strictly positive real part.

## Scope and surviving frontier

This closes primewise fixed-width source sign and source origin of conjugate phase.  It does not
prove concrete restricted-Weil/Robin rectangular trace contains this bilinear block, identify
cross-prime Gamma/marked-halfgap/holonomy Schur remainder, prove uniform Ward-defect lower bound,
or prove RH.

## Verification

- direct `lake env lean` source check passed with no module-local warnings;
- targeted `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` passed `9479/9479`;
- six capstone axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden declaration scan is clean;
- repository lint reaches module and remains red only on 21 unrelated unreachable modules.
