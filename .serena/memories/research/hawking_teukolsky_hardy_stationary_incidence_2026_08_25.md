Mission: source-specific Hawking–Teukolsky dynamics selecting critical line or forcing tilted-sector mixing.

New exact results:
1. Birmingham–Mokhtari d=4 stationary boundary Jost is nonzero at every Xi divisor. At omega=0 the two reciprocal-Gamma arguments have imaginary parts ±Re(z)/4; Xi spectral points have nonzero real part, so neither argument lies on Gamma's nonpositive-integer pole lattice. Added five declarations to `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyBackreactionReturnDeterminant.lean`, capstone `d4GravitationalHypergeometricBoundaryJost_stationary_xi_ne_zero`.
2. Causal incidence is now physical rather than a fictitious complex-mode amplitude. For every upper theta resonance, Xi canonical-product exhaustiveness chooses a multiplicity copy q at same centered point. Its Szegő kernel is a finite-energy causal Hardy wavepacket with nonzero node evaluation. Multiplying exact BM gravitational Green channel by that evaluation preserves the simple QNM pole. New file `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskyHardyWavepacketIncidence.lean`, theorem `exists_d4BMGravitationalHardyWavepacketSimplePole`; imported by RHTower umbrella.
3. Paper theorem (not Lean formalized): on complete finite-area hyperbolic horizon, a smooth L2 TT metric variation h whose Laplacian variation commutes with spectral resolution must vanish. TT gives principal symbol b=h^{ij}xi_i xi_j; commutator zero gives geodesic-flow invariance; finite-volume hyperbolic ergodicity makes b constant on unit cotangent; tracefree forces h=0. Thus every nonzero Teichmüller horizon deformation mixes angular sectors.
4. Static tensor mode: in d=4 every TT horizon mode is Teichmüller type. KI static radial equation integrates r^2 f H'=C. Horizon regularity kills logarithmic C branch; fixed conformal boundary kills constant. If boundary moduli float, constant survives and item 3 forces mixing.
5. Resulting linear horizon-memory classification: fixed-boundary stationary kernel modulo gauge is mass only; floating boundary gives mass plus Teichmüller tangent, and every nonzero tangent mixes sectors. Nonexceptional scalar/vector zero modes are excluded by stationary Jost; scalar k=0 is mass; K=-1 has no exceptional rotation.

Verification:
- Targeted Lean compile passed for modified backreaction module and new incidence module.
- Axiom prints for six new declarations: only propext, Classical.choice, Quot.sound.
- `scripts/formal_tools.py lint` has no new failure; sole remaining failure is unrelated pre-existing unreachable `HTGeometry.SecondOrderConstraintDescent`.
- /tmp scratch files removed. No git, no broad builds.

Remaining irreducible dynamics:
Derive retarded second-order Einstein/Teukolsky asymptotic decomposition for a physical Hardy wavepacket:
return = nonnegative absorbed-mass memory + TT boundary-modulus memory + transient local/QNM/continuum tail.
Existing delayed theorem handles finite local/Jordan terms and finite-energy BM continuum. New stationary theorem excludes same-sector zero-mode memory; fixed boundary excludes TT, while floating TT forces mixing. Need prove full reduced source lies in this decomposition, including cusp threshold/direct contour terms. This would rule out exact negative AIME counterterm at late delay without generic KMS/passivity and close cubic producer.
