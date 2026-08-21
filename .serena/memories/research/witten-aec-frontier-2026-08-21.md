# Witten asymptotic-expansion conjecture: audited frontier (2026-08-21)

Target fixed as the SU(2) WRT asymptotic expansion for every closed 3-manifold: for h=1/n -> 0, the WRT invariant is a finite sum over flat SU(2) connection phases exp(-CS(rho)/(2*pi*i*h)), each times h^d_rho (d_rho in 1/2 Z) and a formal half-power series. Current precise formulation: Campbell Wheeler, SIGMA 21 (2025), Conj. 1.2, https://www.maths.tcd.ie/EMIS/journals/SIGMA/2025/004/sigma25-004.pdf pp. 2–3.

External frontier:
- Witten, Commun. Math. Phys. 121 (1989), DOI 10.1007/BF01217730: Chern–Simons origin.
- Andersen, arXiv:1104.5576: AEC proved for finite-order mapping tori by Lefschetz–Riemann–Roch, with polynomial phase terms by flat-moduli components.
- Andersen–Jorgensen, arXiv:1206.2552: torus-bundle instances.
- Wong–Yang, arXiv:2003.10053: figure-eight Dehn-filling class.
- Andersen et al., arXiv:2510.10678: Seifert integral homology spheres.
- Murakami, arXiv:2508.21710: negative-definite plumbed 3-manifolds.
- Wheeler 2025 pp. 13 states WAE proved for some hyperbolic families but open in general; its proposed vector-valued resurgent refinement includes complex SL2(C) sectors and Stokes data. Earlier scalar Gukov–Manolescu radial-limit formulation has a counterexample for 4_1(-1,2).

Internal Lean frontier:
- Exact rg finds no WRT / Reshetikhin / Turaev declaration; only unrelated InnerRegularWRT.
- HTGeometry/AsymptoticExpansionAlgebra.lean formalizes continuous integer-power Poincare expansions at 0+, not the required discrete half-power multi-phase WAE.
- RHTower/FiniteExponentialPencilMeanSquare.lean already formally proves finite unit-phase mode extraction/noncancellation: not_tendsto_finiteExponentialPencil_zero_of_fiberCoefficient.
- Existing Chern–Simons sources are finite abstract homotopy/abelian models, not an SU(2) WRT TQFT or 3-manifold invariant.

Hostile loops:
1. Reduce all closed 3-manifolds to negative-definite plumbings: FALSE. This does not cover general hyperbolic manifolds; surgery is not a closure theorem for all-order WAE.
2. Identify WRT with a scalar radial GPPV/Zhat limit and deduce WAE: FALSE. Wheeler’s 4_1(-1,2) counterexample kills the scalar radial-limit bridge.
3. Use a full vector-valued resurgent Stokes system to project complex flat sectors to arithmetic SU(2) WRT asymptotics: REDISCOVERED/OPEN. This is Wheeler’s existing refinement, not a new theorem.

Exact [OPEN CORE]: an unconditional all-closed-3-manifold construction connecting SU(2) WRT surgery/TQFT to a finite, Borel-resurgent gluing formula with an arithmetic Stokes projection; this would imply WAE. No paper proof, local Lean model, or literature theorem closes it.

Do not duplicate finite phase-separation Lean infrastructure.

Lean progress after the audit:
- Added and wired `formal/GaloisForLFunctions/HTGeometry/WittenAsymptoticExpansion.lean`.
- The module defines exact finite phase-polynomial level formulas and proves (i) identically zero remainder to every inverse-power order and (ii) polynomial growth for unit phases. This formalizes the final analytic implication used by known exact phase-polynomial cases; it does not define WRT or claim an instance of the full conjecture.
- Verified source with `lake env lean GaloisForLFunctions/HTGeometry/WittenAsymptoticExpansion.lean`; built exact target with `lake build GaloisForLFunctions.HTGeometry.WittenAsymptoticExpansion`; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Project non-build lint reaches this module through the umbrella but exits nonzero on four pre-existing unreachable owned modules: BorelWeil.BottCombinatorics, HilbertIrreducibility.DividedDifference, HilbertIrreducibility.RationalInterpolation, and PoincareHopf.ManifoldIndex. Do not overwrite user-modified generated index files to repair unrelated lint state.