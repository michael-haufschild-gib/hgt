# Route P cubic rank--coarea dissipation quantum

- **ID:** `CUBIC-RANK-COAREA-DISSIPATION-QUANTUM`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** completed-Xi cubic irregular-microlocal Riemann--Hilbert route
- **Statement:** Rank-magnitude-preserving contracted/unit cubic Xi landings dissipate at least the common-rank square times the sum of inverse local cover--branch complexities.

## Goal

Extract a source-independent quantitative obstruction from actual completed-Xi irregular-Stokes
landings.  Direct coefficient-faithful source incidence is RH-equivalent in the current corpus, so
the theorem must use only intrinsic landing data and must not assume the missing arithmetic bridge.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, hostile attack and Door passport complete
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: targeted Lean theorem and new-declaration axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact theorem

Fix coefficient-generated local Puiseux data `d_a` at the nonempty marked-point family
`a : Fin (p+1)`.  Write `N_a` for local common-cover degree, `m_a` for local branch count, and
`B_a(x)` for unit-Rees canonical block coarea.  Let `x_0` and `x_1` be contracted and unit cubic Xi
Malgrange landings with the same squared common physical rank.  Set

`T_j = sum_a terminalEnergy_a(x_j)` and `r_j = commonRank(x_j)`.

Then

`0 < r_1^2 * sum_a 1 / (N_a m_a) <= T_0 - T_1`.

The exact moving-landing balance also gives

`T_0 - T_1 = sum_a B_a(x_1)`.

No existence of either landing, no relation between their charge coordinates, and no arithmetic
source-to-landing map is asserted.

## Approach

Use all canonical pendant Stokes cuts rather than one chosen branch per orbit.  Their injectivity
retains full branchwise squared charge.  Finite Cauchy--Schwarz converts that branch energy into a
common-rank floor.  Sum the resulting inverse cover--branch floors over every marked point, then
identify total block coarea with terminal dissipation through the existing moving-landing law.

## Dependency-closed proof `[PROVED HERE]`

Fix one local datum with cover degree `N`, branch count `m`, orbit charge `x`, lifted branch charge
`y_b = x_(orbit(b))`, physical rank `r = sum_b y_b`, and block energy `B`.

1. Coefficient-generated threshold geometry supplies one pendant edge `P(b)` per branch.  Its cut
   length is exactly `1/N`, and its cut coordinate is exactly `y_b`.
2. `P` is injective: if `P(b)=P(c)`, evaluate both cut-side functions at `b`.  Pendant singleton
   laws give `1` on the first side and, when `b != c`, `0` on the second.
3. Every block-energy summand is nonnegative.  Restriction to the distinct pendant edges yields
   `(1/N) * sum_b y_b^2 <= B`.
4. Since `N>0`, multiplication by `N` gives `sum_b y_b^2 <= N B`.
5. Finite Cauchy--Schwarz gives `r^2 <= m * sum_b y_b^2`.  Therefore
   `r^2 <= N m B`.
6. For a cubic Xi landing, the common rank is nonzero.  Compatibility identifies it with every
   local physical rank.  Hence every local branch count is positive: if `m=0`, the defining branch
   sum for local physical rank is zero.  Cover degrees are positive by construction.
7. Divide the local inequality by positive `N m`:
   `r^2 / (N m) <= B`.  Apply this to `x_1` at every marked point and sum:
   `r_1^2 * sum_a 1/(N_a m_a) <= sum_a B_a(x_1)`.
8. Every reciprocal is positive, the marked-point type is nonempty, and `r_1 != 0`; therefore the
   left side is strictly positive.
9. Rank-magnitude preservation and the exact moving-landing balance give
   `T_0 - T_1 = sum_a B_a(x_1)`.  Substitution proves the conjecture.

All dependencies are already proved coefficient-generated landing laws or elementary finite-sum
inequalities.  No open source-incidence statement occurs.

## Hostile audit

- **Circular route killed.** A direct coefficient-faithful source-to-`compatibleCharges` landing
  would repackage RH.  Corpus classifications include
  `ccmRationalAdelicPrimeFixedXiStokesComparisonsCoefficientFaithful_iff_riemannHypothesis`,
  `xiPrimeWardExteriorCoefficientFaithfulSourceSubquantum_iff_riemannHypothesis`, and
  `primeDepthBVWoldXiSourcePolarizationStokesFlat_iff_riemannHypothesis`.
- **No hidden transport premise.** `x_0` and `x_1` are independent members of explicit landing
  fibres.  Only equality of their squared common ranks is used.
- **No vacuity disguised as existence.** Result is a necessary law on the landing-pair subtype.  It
  does not prove that a completed-Xi arithmetic source produces such a pair.
- **Rediscovery boundary.** Pendant restriction and finite Cauchy--Schwarz are standard
  finite-dimensional mechanisms.  They are not claimed as new mathematics in isolation.
- **Surviving application.** Cumulative completed-Xi bound eliminates terminal-coordinate
  distribution and quantifies unavoidable dissipation solely by physical rank and intrinsic local
  irregular complexity.  Corpus search found no branch-count rank floor or cumulative
  cover--branch dissipation quantum.

## Literature audit

Primary irregular-RH sources audited: Mochizuki, *Wild Harmonic Bundles and Wild Pure Twistor
D-modules* (arXiv:0803.1344); Mochizuki, *Good Wild Harmonic Bundles and Good Filtered Higgs
Bundles* (arXiv:1902.08298); Bolibruch--Malek--Mitschi, *On the generalized Riemann--Hilbert problem
with irregular singularities* (arXiv:math/0410483).  Connes--Consani, *The Scaling Hamiltonian*
(arXiv:1910.14368), was also checked for arithmetic trace/positivity overlap.  These sources provide
wild harmonic/twistor structures, ramified Stokes data, generalized RH existence, and scaling-site
positivity frameworks.  Audit found no completed-Xi cumulative rank--coarea dissipation law.
Absence is an audit inference, not a universal priority claim.

## No-go closure

- **Exact killing theorem/mechanism:** exact coefficient-faithful global source landing is already
  classified as equivalent to RH in three independent corpus formulations.
- **Strongest positive survivor:** intrinsic rank-only cumulative dissipation quantum
  `r_1^2 * sum_a 1/(N_a m_a) <= T_0-T_1`, with strict positive left side.
- **New insight:** each marked point must independently pay for the same fused physical-rank
  channel; global dissipation accumulates all inverse local cover--branch capacities rather than
  selecting one favourable point or assuming terminal-coordinate control.
- **Status:** paper proof dependency-closed and exact theorem formalized in Lean.  Application-level
  novelty survives preliminary corpus/literature attack; local finite-dimensional lemma is
  standard.

## Lean formalization

Implemented in
`formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicRankCoareaDissipationQuantum.lean`.
Public declarations:

- `routePPrimitiveGammaJuliaStokesCubicUnitLanding_cumulativeRankCoareaQuantum_pos_le_blockEnergy`;
- `routePPrimitiveGammaJuliaStokesCubicRankMagnitudePreservingMovingLanding_rankCoarea_dissipationQuantum`.

All pendant-edge, branch-count, and division lemmas remain private.  Targeted module check passed.
Both public declarations depend exactly on `[propext, Classical.choice, Quot.sound]`; no project
axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration was introduced.  Temporary scratch and
dependency `.olean` files were removed.  No umbrella build was run.

## Log

- 2026-08-25 -- direct coefficient-faithful source bridge killed as circular.
- 2026-08-25 -- stronger rank-only cumulative survivor conjectured and paper proof closed.
- 2026-08-25 -- promoted to fully proven after hostile dependency and circularity audit.
- 2026-08-25 -- formalized; targeted module check and new-declaration axiom audit passed.
