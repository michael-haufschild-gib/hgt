# Route N C26-C27: squarefree Fisher affine conormal residue

## Formal results
New umbrella-wired modules:
- formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnSquarefreeFisherConormalResidue.lean
- formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnSquarefreeFisherAffineResidueBridge.lean

For any Re(sigma)>1, epsilon != 0, and affine coordinate rho=sigma+u epsilon in the strict-right strip:
1. Moving squarefree overlap B(u)=Z_sq(sigma+u epsilon)/Z_sq(sigma) has analytic order equal to Xi at rho.
2. At an actual Xi zero of multiplicity m=k+1, pointed division-free Fisher numerator F=2(B'+epsilon A_sq(sigma)B) has exact order m-1.
3. No analytic local q can satisfy F=Bq. This disproves the old live source-card divisibility gate at every simple or multiple strict-right zero.
4. Normalized conormal residue is exact: lim_(v->u,v!=u) (v-u)F(v)/B(v)=2m.
5. Centered scaling by -(rho-1/2)/2 makes this residue exactly the exceptional Xi affine-current residue -(rho-1/2)m.
6. Its real part is strictly negative for every strict-right zero.

Unconditional closed certificates:
- RHTower.routeNSquarefreeFisherConormal_law
- RHTower.routeNSquarefreeFisherAffineResidue_law

Direct Lean, explicit oleans, and focused #print axioms audit passed. Headline theorems depend only on propext, Classical.choice, Quot.sound.

## Research interpretation
Derivative does not land in overlap ideal; it lands in one-dimensional conormal quotient. Fisher conormal, exceptional normal cone, and position-times-multiplicity current are one conserved oriented source incidence. This is the independent pre-divisor coordinate missing from Route N reflection-even reporters, but it records rather than removes divisor.

Correct live target:
- split forced residue line from analytic regular remainder on charged multiplication graph;
- control regular remainder through completed Ward/Gamma/Sonin transport;
- prove from pre-divisor Euler-Gamma-Stokes structure a sign/annihilation law excluding negative horizontal affine residue.

Do not retry literal Fisher numerator divisibility; it is mathematically impossible.

Updated:
- failed Route N card with (N.54)-(N.56);
- rh-current-frontier-map Route N dossier;
- rh-route-literature-exchange;
- mobius-incidence-curvature-gamma-sonin-pole-divisor-transfer-rh live gates.

Targeted primary search located generic Burnol co-Poisson, zeta log-derivative statistics, and Fisher/log-derivative geometry but not exact squarefree-source/Xi affine-residue synthesis. Generic order-drop/residue is not claimed new; only exact synthesis is provisional local delta.

Related memories: `mem:research/route_n_sonin_burnol_hyperbolic_mass_shell_2026-08-10`, `mem:research/route_n_xi_kadison_receiver_nogo_2026-08-10`.