# Theta-cusp Hawking KMS Friedrichs mixing endpoint (2026-08-23)

New module: formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingKMSFriedrichsMixingEndpoint.lean
Umbrella import: formal/GaloisForLFunctions/RHTower.lean

Correct interpretation:
- Exponential tilt removes/gauges growth rate; it is not a KMS centralizer statement because real oscillation frequency remains.
- Exact tilted moving-mirror Born shell density is J_a(omega)=omega^4 normSq(XiC(omega+a i))/(48 pi^2).
- Unsquared normalized shell form factor is omega^2 XiC(omega+a i)/(4 sqrt(3) pi); its reflected tilt -a is exact complex conjugate.
- Hawking beta_H=2pi/kappa Araki-Woods lift has down weight J/(1-q), up weight qJ/(1-q), q=exp(-beta_H omega), with exact detailed balance.
- Total width Gamma=2pi(down+up) is nonnegative and Gamma=0 iff XiC(omega+a i)=0 for omega>0.
- Real-counterterm-renormalized Friedrichs on-shell determinant is -i Gamma/2. Its zero is the embedded dressed mode criterion. Positive width removes that resonance-sector point spectrum.
- The property that every positive-frequency nonzero-tilt sector mixes is Lean-proved equivalent to RH:
  RHTower.riemannHypothesis_iff_thetaCuspHawkingKMSFriedrichsResonanceMixing.
- Hawking/KMS supplies the genuine thermal dilation and exact coefficients, but not strict positivity. Strict mixing remains RH-equivalent; generic KMS, passivity, centralizer arguments do not prove it.
- Purely imaginary centered Xi zeros are excluded using XiC_ne_zero_of_imaginary, so positive frequency sectors cover the full off-line divisor up to evenness.

Verification:
- lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingKMSFriedrichsMixingEndpoint.lean: PASS.
- targeted lake build module: PASS.
- #print axioms on capstone, determinant-zero, width-zero theorems: only propext, Classical.choice, Quot.sound.
- no sorry/admit/axiom/opaque/unsafe in new module.

Prior related memory: `mem:research/theta_cusp_hawking_tilted_backreaction_gauge_endpoint_2026_08_23`. That module's algebra is valid, but its centralizer language is physically misleading; prefer this KMS/Friedrichs endpoint.