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

Lean progress after that record:
- Added HTGeometry/AbelianChernSimonsAsymptotics.lean: finite cyclic linking-sector U(1) Chern--Simons sum, exact degree-zero phase expansion, all-order zero remainder, level-periodicity by torsion order, and uniform bound.
- Added HTGeometry/FiniteOrderMappingTorusWRT.lean: Andersen 2011 Remark 1.1's published SU(2) calibration formula Z_k(T^2_{-Id}) = k + 1, encoded as an exact one-phase degree-one formula. It proves unboundedness, excludes every degree-zero unit-phase exact presentation, and proves a nonzero aggregated leading fiber.
- Added HTGeometry/WittenPhasePolynomialRigidity.lean: if every equal-phase fiber has zero aggregate linear coefficient, a degree-one exact phase polynomial collapses to degree zero. This is a formal leading-packet uniqueness mechanism, not a generic duplicate of existing mean-square noncancellation.
- Added HTGeometry/SU2TorusModularData.lean: for r >= 2, odd 2r-th-root Fourier packets underlying SU(2) torus sine columns satisfy exact Hermitian orthogonality <P_a,P_b> = if a=b then 4r else 0; each is nonzero and the r-1 packets are linearly independent. This is direct non-abelian modular-data progress toward the S^2 charge-conjugation/trace bridge.
- All four modules are direct HTGeometry umbrella imports. Target-only builds succeeded for WittenPhasePolynomialRigidity, FiniteOrderMappingTorusWRT, and SU2TorusModularData; #print axioms for new theorems reports only propext, Classical.choice, Quot.sound. No custom axioms/sorry/admit/opaque/unsafe in the added modules.
- Current next exact Lean kernel: turn the odd packet basis into the normalized SU(2) torus S operator, prove S^2 = charge conjugation, then derive the mapping-torus trace from genuine modular data rather than a named formula.
- New direct advance: SU2TorusModularData now defines packet synthesis from label coordinates and dual Fourier analysis. It proves the synthesis Hermitian form is exactly scaled by 4r, injective, and analysis∘synthesis=id. This is a verified finite SU(2) torus state-space embedding. Remaining: construct the ambient odd-subspace self-identification / normalized endomorphism and prove S^2=charge conjugation.

2026-08-21 advance: corpus search `finite cyclic Fourier transform inversion odd subspace root unity` located Mathlib `ZMod.dft_dft` and existing `RHTower/FieldOneFiniteCyclicFourierParseval.lean`, avoiding a duplicate Fourier inversion proof. `HTGeometry/SU2TorusModularData.lean` now imports `Mathlib.Analysis.Fourier.ZMod`, defines the Weyl-odd submodule of functions on `ZMod (2*r)`, proves DFT preserves it, proves `su2TorusWeylOddFourier_sq`: Fourier square is `-(2*r)•id` on this carrier, and defines the exact normalized operator `su2TorusWeylS`. The closed theorem `su2TorusWeylS_sq` proves `S²=id` for `r≥2`, via `i/sqrt(2r)`. Target-only build `lake build GaloisForLFunctions.HTGeometry.SU2TorusModularData` passed; axiom audit of both new square theorems lists only propext, Classical.choice, Quot.sound. This is genuine finite SU2 torus modular data, still not Reshetikhin–Turaev surgery/TQFT or all-manifold WAE.

$1 The coordinate map is now upgraded to `su2TorusWeylOddPositiveCoordinatesEquiv`, so the finite state model is an explicit linear equivalence, not merely a matching finrank.