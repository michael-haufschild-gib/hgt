P-G206 constructed/formalized Route P nonlocal precompression shorting.

Lean:
- formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaWardPrecompressionShorting.lean
- wired in formal/GaloisForLFunctions/RHTower.lean; umbrella intentionally not built.
- exact leaf build passed [12991/12991].
- axioms only propext, Classical.choice, Quot.sound.
- formal lint sees module reachable; remaining lint failures are unrelated concurrent HTGeometry BrickCover/Cube/GeneralPosition/Separator modules.

Core construction:
1. Define all-cell, pre-selection clock
  E_x(pe)=c_J*gammaSewnMobiusJuliaNormalizedPrimeLog x pe.prime.
2. Define skew global exterior coupling before finite packet selection
  J_x,u(i,j)=sqrt(2)*a_u(i)*a_u(j)*(E_x(i)-E_x(j)),
where a_u is literal xiGammaEulerPrimitiveDescentTestAmplitude. Thus prime labels/depths and both coefficients remain.
3. Select depth-zero primes 2,3 only afterward and normalize by literal pair mass M. Let C=J/M.
4. Lean proves C^2 equals finite-aperture two-prime Ward energy W_x exactly.
5. Physical precompression block is defined with literal Ward corner, not fitted square:
  B=[[W_x,C],[C,1]].
Environment pivot 1 equals normalized pair source mass sum_i w_i. B is PSD rank one, det B=0, and Schur short W_x-C^2=0.
6. As x->0+, E_x->c_J log p, so W_x tends P-G205 literal two-prime source-state Ward energy, which is positive for every u. Therefore eventually short(B)=0 < compressed corner W_x. This is exact, demonstrable failure of compression monotonicity.

Heavy-conjecture failures:
- Abstractly adjoining a copy/square root of Ward current was rejected as tautology.
- Covariant Pluecker inverse incidence alone lacks Gamma-Julia coefficient identity.
- Surviving source is normalized environment coordinate of canonical Gamma-sewn Julia lift; it exists before scalar recombination and before prime selection.

External classification:
- Anderson-Trapp shorting/Schur formula and Julia defect operators are classical.
- No checked external source gives this arithmetic reciprocal-promotion/Gamma-Julia coefficient identity or Xi landing. Novelty externally unverified.

Honest open core:
Coupling, nonlocal cancellation, and order of operations are closed. Still need completed Gamma/polar source theorem transporting this exact Julia environment short to coefficient- and multiplicity-faithful Xi divisor/spectrum. Current block does not identify Xi or prove RH. Direct scalar/det2 welding and compression-monotone budget remain dead.

Card:
docs/drafts/pipeline/3-formalized/new_scientific_knowledge/gamma/route-p-julia-ward-precompression-shorting.md