# Theta-cusp Hartle–Hawking double-KMS endpoint (2026-08-23)

[MISSION] Construct a source-faithful Hawking horizon model whose genuine state structure forces Xi resonance charge to vanish.

[FALSIFIED] Ordinary Tomita modular conjugation J does not transport one natural-cone state vector to another. Relative state transport uses the relative Tomita operator and generally unbounded Δ_{ψ|φ}^{1/2}. Therefore the prior bounded J-shadow premise is not supplied by Tomita–Takesaki/Bisognano–Wichmann theory. `ThetaCuspHawkingTomitaAcceleratedTypeEndpoint.lean` now labels this physical producer falsified while retaining its valid mathematical no-go.

[LITERATURE] Higuchi–Lima, arXiv:2107.10271: Hartle–Hawking state is equivalent to a pure, wedge-reflection-invariant double KMS state, regular on a bifurcate Killing horizon, reducing to thermal state at Hawking temperature in both static regions. Araki 1976 defines relative entropy via relative modular operator. Maldacena hep-th/0106112 uses two CFT copies and an entangled state for eternal black hole.

[PAPER-PROVED] For physical horizon charge c and prime p, source laws have geometric ratios q_V=p^{-(1-2c)} and q_P=p^{-(1+2c)}. Xi strip gives both in (0,1). A primewise type-I pure double has one ordered squared-Schmidt spectrum for its two reduced geometric KMS states. Equality of vacuum Schmidt mass gives 1-q_V=1-q_P, hence q_V=q_P. Strict injectivity of x↦p^x for p>1 gives c=0. Conversely c=0 makes marginals identical and provides common spectrum. This is exact at one prime.

[LEAN-PROVED] New file `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingHartleHawkingDoubleKMSEndpoint.lean` proves:
- horizon charge lies in (-1/2,1/2);
- visible and partner KMS ratios lie in (0,1);
- `thetaCuspHawkingPrimeKMSRatio_eq_iff_horizonCharge_zero`;
- `thetaCuspHawkingPrimeDoubleKMSPurification_iff_horizonCharge_zero`;
- positive-charge no-purification theorem;
- `thetaCuspHawkingHartleHawkingDoubleKMSCompletable_iff_riemannHypothesis`.
Imported by `formal/GaloisForLFunctions/RHTower.lean`.

[OPEN CORE] Quantize existing theta conformal-anomaly/backreaction system and prove its two wedge restrictions are exactly the source-prescribed prime-valuation geometric laws. General Hawking thermality does not identify arbitrary arithmetic measures with wedge reductions. Sharp AQFT wedge algebras are type III; current theorem is explicitly primewise type-I cutoff/oscillator localization.

[VERIFICATION] Exact new module and corrected Tomita module compile. `#print axioms` for key ratio, purification, and RH endpoint shows only `propext`, `Classical.choice`, `Quot.sound`. `scripts/formal_tools.py lint` passed (large-file warnings only).