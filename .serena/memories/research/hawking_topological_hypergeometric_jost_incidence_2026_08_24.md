# Hawking topological-black-hole hypergeometric Jost incidence (2026-08-24)

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTopologicalBlackHoleHypergeometricJostIncidence.lean` and imported it from `formal/GaloisForLFunctions/RHTower.lean`.

Source-faithful radial object from Aros–Martínez–Troncoso–Zanelli (hep-th/0211024), 4D massless topological AdS black hole, conformal scalar:
- `a = 3/4 - I*(omega-xi)/2`
- `b = 3/4 - I*(omega+xi)/2`
- `c = 1-I*omega`
- normalized Evans/Jost determinant `D = 1/(Gamma(a)Gamma(b))`
- literal forbidden-boundary coefficient `B = Gamma(c)Gamma(1/2)D`
- retarded Green proxy `1/B`.

Unconditional formal results:
- exact QNM branches give `a=-n` and `b=-n`;
- each branch factor has a simple Jost zero and reciprocal Green simple pole;
- at every actual Xi divisor, `XiC_ne_zero_of_imaginary` rules out cross-branch and `Gamma(c)` collisions;
- full physical boundary coefficient has simple zeros at both exact QNM descendants;
- physical retarded Green has simple poles at both;
- scalar full Jost and physical boundary coefficient are theta-shadow invariant;
- branch-resolved chiral quotient is inverted by shadow;
- completed Eisenstein EKG angular vertex is bright on both sheets.

Interpretation/no-go:
Xi divisor is angular resonance; its radial descendants are Jost zeros and Green poles. Exact scalar EKG scattering forces both shadow-related sectors and cannot select canonical split. Generic KMS/passivity remains insufficient. Remaining RH-bearing producer is specifically a nonlinear chiral Teukolsky/helicity return determinant and phase-sensitive Einstein-backreaction optical law. Birmingham–Mokhtari (hep-th/0609028) supports exact hypergeometric gravitational extension, but that nonlinear chiral selector is not proved.

Verification:
- targeted module compile passed;
- targeted olean passed;
- all 46 new lemmas/theorems axiom-audited: only `[propext, Classical.choice, Quot.sound]`;
- scratch files removed;
- no git used;
- static `scripts/formal_tools.py lint` remains red only on unrelated pre-existing umbrella omissions (one RHTower module and several HTGeometry modules), not this module.
