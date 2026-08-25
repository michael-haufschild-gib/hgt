# Route P cubic cover-weighted terminal dissipation

- **ID:** `CUBIC-COVER-WEIGHTED-TERMINAL-DISSIPATION`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** completed-Xi cubic irregular-Stokes route
- **Statement:** Unit Rees activation pays at least the inverse-cover-weighted terminal energy; rank-magnitude-preserving moving landings contract terminal energy by that explicit amount.

## Goal

Extract a quantitative completed-Xi consequence from coefficient-generated irregular microlocal
Riemann--Hilbert data.  This is an application theorem about the cubic Xi landing problem, not a
new abstract Stokes foundation or a source-incidence assumption.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: Lean theorem, targeted module check, new-declaration axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact theorem

Fix coefficient-generated local Puiseux data `d_a` with positive cover degrees `N_a`.  For a unit
Rees cubic Xi landing `x_1`, write

- `T_1 = sum_a terminalEnergy_a(x_1)`;
- `B_1 = sum_a blockEnergy_a(x_1)`;
- `W_1 = sum_a (1 / N_a) terminalEnergy_a(x_1)`.

Then

`0 < W_1 <= B_1`.

For arbitrary contracted and unit landings `x_0,x_1`, with `A` the positive magnitude of the
unique global rank coefficient and `r_j` their common physical ranks,

`T_1 + W_1 + A r_0^2 <= T_0 + A r_1^2`.

If rank magnitude is preserved, then

`T_1 + W_1 <= T_0`.

Thus the terminal-energy drop is not merely positive: it is at least the explicit
inverse-cover-weighted terminal energy visible after unit Rees activation.

## Dependency-closed proof `[PROVED HERE]`

1. At each marked point, coefficient thresholds provide one pendant edge `P(b)` for every Puiseux
   branch `b`.  Its length is exactly `1/N`, and its cut side is the singleton indicator of `b`.
2. `P` is injective.  If `P(b)=P(c)`, evaluate their equal cut sides at `b`; the pendant laws give
   `1 = 1` only when `b=c`, and `1=0` otherwise.
3. Orbit surjectivity supplies a section `s` from orbit labels to branches.  It is injective because
   `orbit(s(i))=i`.  Hence `P compose s` selects distinct block-energy summands.
4. Every block-energy summand is nonnegative.  Restricting the full edge sum to the selected
   pendant edges gives
   `(1/N) sum_i x_i^2 <= blockEnergy(x)`,
   because the pendant coordinate sum at `P(s(i))` equals the lifted charge
   `x(orbit(s(i)))=x_i`.
5. Sum this local inequality over all marked points to obtain `W_1 <= B_1`.
6. A cubic Xi landing charge is globally nonzero.  Some local terminal energy is therefore
   positive; every `1/N_a` is positive.  Hence `0<W_1`.
7. Existing arbitrary-moving-pair balance is
   `T_0 + A r_1^2 = T_1 + B_1 + A r_0^2`.
   Substitute `W_1<=B_1` to get the universal inequality.  If `r_0^2=r_1^2`, cancel the rank
   terms and obtain `T_1+W_1<=T_0`.

## Hostile audit

- No landing-pair existence is asserted.
- No equality, isometry, or source map between the two charges is assumed.
- Rank preservation is used only for the final corollary; the weighted coarea floor and universal
  rank--terminal inequality hold without it.
- Cover positivity and pendant faithfulness come from coefficient-generated Puiseux data already
  present in the completed-Xi landing type.
- Result remains a necessary transport law, not RH and not the missing coefficient-faithful
  source-to-charge construction.

## Novelty audit

Corpus search found positivity, exact moving-pair balance, and rank-preserving strict dissipation,
but no inverse-cover quantitative floor.  Primary irregular-RH literature supplies Stokes
filtrations, ramified formal data, deformation data, and functoriality, but the audit found no
completed-Xi cover-weighted energy law: Mochizuki, *The Stokes Structure of a Good Meromorphic
Flat Bundle* (2011); Mochizuki, *Wild Harmonic Bundles* (Asterisque 340, 2011); Doucot,
*A Topological Algorithm for the Fourier Transform of Stokes Data at Infinity* (2025);
Bolibruch--Malek--Mitschi, *On the Generalized Riemann--Hilbert Problem with Irregular
Singularities* (2006).  Absence is an audit inference, not a universal priority claim.

## Lean formalization

Implemented in
`formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicCoverWeightedTerminalDissipation.lean`.
Public declarations:

- `routePPrimitiveGammaJuliaStokesCubicUnitLanding_coverWeightedTerminalEnergy_pos_le_blockEnergy`;
- `routePPrimitiveGammaJuliaStokesCubicMovingLanding_coverWeighted_rankTerminal_exchange`;
- `routePPrimitiveGammaJuliaStokesCubicRankMagnitudePreservingMovingLanding_coverWeightedTerminalEnergy_contraction`.

Pendant-edge selection and finite-sum domination remain private.  Targeted module check passed.
Each new public declaration depends exactly on `[propext, Classical.choice, Quot.sound]`; no
project axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration was introduced.

## Log

- 2026-08-25 -- conjectured after moving-charge balance; corpus and primary-literature audit found
  no existing statement.
- 2026-08-25 -- hostile audit passed; dependency-closed paper proof completed.
- 2026-08-25 -- formalized in Lean; targeted module check passed.
