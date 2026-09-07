# CCM-FU: oriented initial balancing with arbitrary one-prime extension

- **Stage:** 3-formalized
- **Type:** positive source construction; paper and Lean proofs closed
- **Parent:** [adaptive prime ceiling](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Boundary:** one additional prime may be interleaved anywhere; repeated smaller-prime mergers remain open.

## Exact theorem

At every sufficiently large cutoff M=4N, active late primes admit a selected block L whose retained head lies in `[0,sqrt(M)]`. Its head square is at most M and `Q_L<=V_empty+M`. For every R subset L, both `Q_R<=Q_empty` and `Q_(R union {q})<=Q_R` hold for every unprocessed prime q<M. These state bounds cover every ordering of L together with any one additional prime, including insertion anywhere inside the selected block. They do not assert closure after two such additional primes or the complete SD1 bound.

## Source proof

Every original fibre has Möbius parity: `(-1)^card(R) F_empty(R)>=0`. This follows termwise from squarefree Möbius coefficients and the proved unsigned-channel positivity. Late-prime consumption leaves every nonempty fibre unchanged except for removed singleton fibres, so it preserves their parity. If the retained head is nonnegative too, every paired product for any next prime is nonpositive; the exact merger identity therefore contracts complete energy.

For a nonnegative target h covered by nonnegative weights bounded by a, stop below h with residual in `[0,a]`. This can also be obtained from the existing crossing selector applied to target `h-a` when h>a, or by choosing the empty set when h<=a. Every intermediate subset leaves a nonnegative head. The exact nonempty-energy law yields `Q_L<=V_empty+a^2`. Actual late coefficients are at most sqrt(M), and their complete mass eventually covers the initial head along 4N, with no signed-energy premise.

## Iteration boundary

The previously formal theorem `mobiusDivisorSelectionFibre_twentyOne_three_gt` gives `F_(21,{2})({3})>0.04`, violating the original singleton's odd parity after one smaller-prime merger. Thus contraction alone does not preserve the conditions for the next contraction. A complete growing schedule must control the changed signs or prove a restoration mechanism. This source construction leaves PE4, PE4G, PE4C, SD1 and RH open.

## Lean certificate and verification

`RHTower.MobiusDivisorOrientedPrimeExtension` contains seven new public theorems:

- `exists_mass_cover_below_with_bounded_residual` proves finite selection below the target.
- `mobiusDivisorSelectionFibre_empty_parity_nonneg` and `mobiusDivisorSelectionFibre_late_parity_nonneg` prove original and retained nonempty source orientation.
- `mobiusDivisorSelectionEnergy_insert_le_of_parity_nonneg` and `mobiusDivisorSelectionEnergy_insert_le_after_late_primes` prove contraction from that orientation.
- `exists_mobiusDivisorInitialOrientedPrimeExtension` constructs the block from explicit available source mass.
- `eventually_exists_mobiusDivisorInitialOrientedPrimeExtension` discharges availability from actual arithmetic and gives the unconditional capstone along cutoffs 4N.

The complete scratch proof and exact new-leaf `lake env lean` check passed. The leaf is wired once into `RHTower.lean`; no umbrella, dependency or full build was run. All seven new declarations were axiom-audited once and depend only on `propext`, `Classical.choice` and `Quot.sound`. No numerical premise or proof placeholder is used.

The global `scripts/formal_tools.py lint` invocation reports five unrelated concurrent modules missing umbrella wiring: RHTower's `ThetaCuspTwoAtomExponentialAdmission` and `ThetaCuspTwoAtomOddProfiles`, and HTGeometry's `TwoAtomOddAlgebra`, `TwoAtomOddHighReserve` and `TwoAtomOddLowerReserve`. It reports no error for the new CCM-FU leaf. Its exact Lean verification is complete; this invocation does not establish a passing global lint gate.
